-- Prove2me | solution 1 for ModularCurve.periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d7bcddb5-8ff0-5932-af9f-0d12268c0d86

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped MatrixGroups ModularForm Topology
open UpperHalfPlane CongruenceSubgroup CohCarrier ModularCurve ModularCurve.Period Filter

namespace DiamondPeriod

theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma M ≤ GammaH M H := by
  intro A hA
  rw [mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

scoped instance GammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)

theorem hasDerivAt_moebius (s : SL(2, ℤ)) (z : ℂ) (hz : ((s 1 0 : ℤ) : ℂ) * z + ((s 1 1 : ℤ) : ℂ) ≠ 0) :
    HasDerivAt (fun w : ℂ => (((s 0 0 : ℤ) : ℂ) * w + ((s 0 1 : ℤ) : ℂ)) / (((s 1 0 : ℤ) : ℂ) * w + ((s 1 1 : ℤ) : ℂ)))
      (1 / (((s 1 0 : ℤ) : ℂ) * z + ((s 1 1 : ℤ) : ℂ)) ^ 2) z := by
  have hnum : HasDerivAt (fun w : ℂ => ((s 0 0 : ℤ) : ℂ) * w + ((s 0 1 : ℤ) : ℂ)) ((s 0 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((s 0 0 : ℤ) : ℂ)).add_const ((s 0 1 : ℤ) : ℂ)
  have hden : HasDerivAt (fun w : ℂ => ((s 1 0 : ℤ) : ℂ) * w + ((s 1 1 : ℤ) : ℂ)) ((s 1 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((s 1 0 : ℤ) : ℂ)).add_const ((s 1 1 : ℤ) : ℂ)
  have h := hnum.div hden hz
  have hdet : ((s 0 0 : ℤ) : ℂ) * ((s 1 1 : ℤ) : ℂ) - ((s 0 1 : ℤ) : ℂ) * ((s 1 0 : ℤ) : ℂ) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe s
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  convert h using 1
  all_goals try rfl
  rw [one_div, eq_div_iff (pow_ne_zero 2 hz), inv_mul_cancel₀ (pow_ne_zero 2 hz)]
  linear_combination -hdet

end DiamondPeriod
p2m_reactivate "P2MW.S_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash.DiamondPeriod"

open DiamondPeriod in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (σ : CongruenceSubgroup.Gamma0 M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ⇑f ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) :
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      CohCarrier.diamondRaw M H ℂ σ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f) := by
  obtain ⟨F, hFd, hF0, hFeq, hFcusp⟩ := exists_hasEquivariantPrimitiveOf (GammaH M H) f
  set s : SL(2, ℤ) := (σ : SL(2, ℤ)) with hs
  obtain ⟨L, hL⟩ := hFcusp s

  have hconj : ∀ (γ : ↥(GammaH M H)) (z : ℍ),
      s • ((γ : SL(2, ℤ)) • z) = ((conjHom M H σ γ : ↥(GammaH M H)) : SL(2, ℤ)) • (s • z) := by
    intro γ z
    rw [← mul_smul, ← mul_smul]
    congr 1
    show s * (γ : SL(2, ℤ)) = (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ * s
    rw [hs, inv_mul_cancel_right]

  set G : ℍ → ℂ := fun w => F (s • w) - L with hG
  have hGeq : IsEquivariantPrimitive (GammaH M H) G := by
    intro γ
    obtain ⟨c, hc⟩ := hFeq (conjHom M H σ γ)
    refine ⟨c, fun z => ?_⟩
    simp only [hG]
    rw [hconj γ z, sub_sub_sub_cancel_right]
    exact hc (s • z)
  have hG0 : Tendsto G atImInfty (𝓝 0) := by
    have := hL.sub_const L
    rwa [sub_self] at this
  have hGcusp : ∀ δ : SL(2, ℤ), ∃ L' : ℂ, Tendsto (fun w : ℍ => G (δ • w)) atImInfty (𝓝 L') := by
    intro δ
    obtain ⟨L', hL'⟩ := hFcusp (s * δ)
    refine ⟨L' - L, ?_⟩
    have : (fun w : ℍ => G (δ • w)) = fun w => F ((s * δ) • w) - L := by
      ext w; simp only [hG, mul_smul]
    rw [this]
    exact hL'.sub_const L
  have hGd : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ := by
    intro τ

    have hden : ∀ z : ℂ, 0 < z.im → ((s 1 0 : ℤ) : ℂ) * z + ((s 1 1 : ℤ) : ℂ) ≠ 0 := by
      intro z hz h0
      have := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
        Complex.zero_im] at this

      have h10 : ((s 1 0 : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hz.ne'
      have h11 : ((s 1 1 : ℤ) : ℂ) = 0 := by
        have := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,
          Complex.zero_re] at this
        have h10' : ((s 1 0 : ℤ) : ℝ) * z.re = 0 := by rw [h10, zero_mul]
        rw [h10', zero_add] at this
        exact_mod_cast this
      have hdet := Matrix.SpecialLinearGroup.det_coe s
      rw [Matrix.det_fin_two] at hdet
      have h10z : (s 1 0 : ℤ) = 0 := by exact_mod_cast h10
      have h11z : (s 1 1 : ℤ) = 0 := by exact_mod_cast h11
      rw [h10z, h11z, mul_zero, mul_zero, sub_zero] at hdet
      exact zero_ne_one hdet
    have hdenom : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) s))
        (τ : ℂ) = ((s 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((s 1 1 : ℤ) : ℂ) := by
      simp [UpperHalfPlane.denom]
    have hval : g τ = f (s • τ) * (1 / (((s 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((s 1 1 : ℤ) : ℂ)) ^ 2) := by
      have := congrFun hg τ
      rw [this]
      show (⇑f ∣[(2 : ℤ)] s) τ = _
      rw [ModularForm.SL_slash_apply, hdenom, zpow_neg, zpow_two, one_div, pow_two]
    rw [hval]

    set moeb : ℂ → ℂ := fun w =>
      (((s 0 0 : ℤ) : ℂ) * w + ((s 0 1 : ℤ) : ℂ)) / (((s 1 0 : ℤ) : ℂ) * w + ((s 1 1 : ℤ) : ℂ)) with hmoeb
    have hmoeb_eq : ∀ z : ℂ, 0 < z.im → ((s • ofComplex z : ℍ) : ℂ) = moeb z := by
      intro z hz
      rw [coe_specialLinearGroup_apply, ofComplex_apply_of_im_pos hz]
      simp [hmoeb]
    have hev : (G ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] (fun z : ℂ => (F ∘ ofComplex) (moeb z) - L) := by
      have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds τ.2] with z hz
      simp only [Function.comp_apply, hG]
      rw [← hmoeb_eq z hz, ofComplex_apply]
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    have h1 : HasDerivAt (F ∘ ofComplex) (f (s • τ)) (moeb (τ : ℂ)) := by
      have := hFd (s • τ)
      rwa [show ((s • τ : ℍ) : ℂ) = moeb (τ : ℂ) from by
        rw [← hmoeb_eq (τ : ℂ) τ.2, ofComplex_apply]] at this
    have h2 := hasDerivAt_moebius s (τ : ℂ) (hden _ τ.2)
    exact (h1.comp (τ : ℂ) h2).sub_const L

  refine AddMonoidHom.ext fun x => ?_
  induction x using Additive.rec with
  | ofMul γ =>
  show periodMapOf (GammaH M H) g (Additive.ofMul γ) =
    periodMapOf (GammaH M H) f (Additive.ofMul (conjHom M H σ γ))
  rw [periodMapOf_apply_eq_periodOf, periodMapOf_apply_eq_periodOf,
    periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf _ g ⟨hGd, hG0, hGeq, hGcusp⟩,
    periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf _ f ⟨hFd, hF0, hFeq, hFcusp⟩]
  obtain ⟨c, hc⟩ := hFeq (conjHom M H σ γ)
  simp only [hG]
  rw [hconj γ, sub_sub_sub_cancel_right, hc (s • UpperHalfPlane.I), ← hc UpperHalfPlane.I]

end S_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
end P2MW
export P2MW.S_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash (solution)
