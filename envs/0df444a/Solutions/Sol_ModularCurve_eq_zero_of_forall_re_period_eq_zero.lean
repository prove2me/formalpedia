-- Prove2me | solution 1 for ModularCurve.eq_zero_of_forall_re_period_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bdad91d2-b494-51bb-9e6a-1e379f0dd0a7

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodMapBundled
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_forall_re_period_eq_zero

open scoped MatrixGroups Real Manifold ModularForm
open UpperHalfPlane Filter Topology Complex Function Metric

namespace ModularCurve
p2m_export "ModularCurve" "period HasEquivariantPrimitive exists_hasEquivariantPrimitive period_apply_eq_sub_of_hasEquivariantPrimitive"
namespace PeriodRealInjectivity
p2m_open "ModularCurve"

open ModularCurve.Period

local notation "𝕢" => Function.Periodic.qParam

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1
  all_goals try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem hasDerivAt_comp_smul {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (γ • ofComplex z)) ((g ∣[(2:ℤ)] γ) τ) ↑τ := by
  have hfun : (fun z : ℂ => G (γ • ofComplex z))
      = (G ∘ ofComplex) ∘ (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) (g (γ • τ))
      ((fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (γ • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasDerivAt_smul_ofComplex γ τ)
  rw [← hfun] at hcomp
  convert hcomp using 1
  all_goals try rfl
  exact ModularForm.SL_slash_apply (g : ℍ → ℂ) γ τ

theorem tendsto_vadd_atImInfty (x : ℝ) :
    Tendsto (fun z : ℍ => x +ᵥ z) atImInfty atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  exact tendsto_comap.congr fun z => (vadd_im x z).symm

theorem const_eq_zero_of_tendsto_sub {α : Type*} {l : Filter α} [l.NeBot]
    {g h : α → ℂ} {L c : ℂ} (hg : Tendsto g l (𝓝 L)) (hh : Tendsto h l (𝓝 L))
    (hc : ∀ a, g a - h a = c) : c = 0 := by
  have hsub : Tendsto (fun a => g a - h a) l (𝓝 (L - L)) := hg.sub hh
  rw [sub_self] at hsub
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun a => (hc a).symm) hsub

theorem apply_smul_T_zpow_smul {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : IsEquivariantPrimitive Γ F) (δ : SL(2, ℤ)) {L : ℂ}
    (hlim : Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) (n : ℤ)
    (hγ : δ * ModularGroup.T ^ n * δ⁻¹ ∈ Γ) (w : ℍ) :
    F (δ • (ModularGroup.T ^ n • w)) = F (δ • w) := by
  have hkey : ∀ w : ℍ, (δ * ModularGroup.T ^ n * δ⁻¹ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w)
      = δ • (ModularGroup.T ^ n • w) := by
    intro w
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  have hc' : ∀ w : ℍ, F (δ • (ModularGroup.T ^ n • w)) - F (δ • w) = hF.period ⟨_, hγ⟩ := by
    intro w
    rw [← hkey]
    exact hF.sub_eq_period ⟨_, hγ⟩ (δ • w)
  have hc0 : hF.period ⟨_, hγ⟩ = 0 := by
    refine const_eq_zero_of_tendsto_sub
      (g := fun w : ℍ => F (δ • (ModularGroup.T ^ n • w)))
      (h := fun w : ℍ => F (δ • w)) (L := L) ?_ hlim hc'
    have hfun : (fun w : ℍ => F (δ • (ModularGroup.T ^ n • w)))
        = (fun w : ℍ => F (δ • w)) ∘ fun w : ℍ => ((n : ℤ) : ℝ) +ᵥ w := by
      funext w
      simp only [Function.comp_apply, UpperHalfPlane.modular_T_zpow_smul]
    rw [hfun]
    exact hlim.comp (tendsto_vadd_atImInfty ((n : ℤ) : ℝ))
  have := hc' w
  rwa [hc0, sub_eq_zero] at this

theorem conj_T_zpow_mem_Gamma0 (N : ℕ) (δ : SL(2, ℤ)) :
    δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  have hTmem : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have hconj : δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (CongruenceSubgroup.Gamma_normal N).conj_mem _ hTmem δ
  exact CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hconj).2.2.1

section Main

variable {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} {F : ℍ → ℂ}

local notation "Γ" => CongruenceSubgroup.Gamma0 N

noncomputable def K (F : ℍ → ℂ) (ρ : SL(2, ℤ)) : ℍ → ℂ := fun w => cexp (F (ρ⁻¹ • w))

omit [NeZero N] in
theorem K_periodic (hF : ModularCurve.HasEquivariantPrimitive N f F) (ρ : SL(2, ℤ)) :
    Periodic (K F ρ ∘ ofComplex) (N : ℝ) := by
  obtain ⟨L, hL⟩ := hF.2.2.2 ρ⁻¹
  intro z
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + (N : ℝ)).im := by simpa using hz
    simp only [Function.comp_apply, K]
    rw [ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hz]
    have hT : (⟨z + (N : ℝ), hz'⟩ : ℍ) = ModularGroup.T ^ (N : ℤ) • (⟨z, hz⟩ : ℍ) := by
      rw [UpperHalfPlane.modular_T_zpow_smul]
      ext1
      simp [UpperHalfPlane.coe_vadd, add_comm]
    rw [hT, apply_smul_T_zpow_smul hF.2.2.1 ρ⁻¹ hL (N : ℤ) (by
      simpa using conj_T_zpow_mem_Gamma0 N ρ⁻¹)]
  · have hz : z.im ≤ 0 := not_lt.mp hz
    have hz' : (z + (N : ℝ)).im ≤ 0 := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_eq_of_im_nonpos hz' hz]

omit [NeZero N] in
theorem K_mdifferentiable (hF : ModularCurve.HasEquivariantPrimitive N f F) (ρ : SL(2, ℤ)) :
    MDiff (K F ρ) := by
  intro τ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have h1 : DifferentiableAt ℂ (fun z : ℂ => F (ρ⁻¹ • ofComplex z)) ↑τ :=
    (hasDerivAt_comp_smul hF.1 ρ⁻¹ τ).differentiableAt
  exact h1.cexp

omit [NeZero N] in
theorem K_tendsto (hF : ModularCurve.HasEquivariantPrimitive N f F) (ρ : SL(2, ℤ)) :
    ∃ M : ℂ, Tendsto (K F ρ) atImInfty (𝓝 M) := by
  obtain ⟨L, hL⟩ := hF.2.2.2 ρ⁻¹
  exact ⟨cexp L, hL.cexp⟩

omit [NeZero N] in
theorem K_bounded (hF : ModularCurve.HasEquivariantPrimitive N f F) (ρ : SL(2, ℤ)) :
    IsBoundedAtImInfty (K F ρ) := by
  obtain ⟨M, hM⟩ := K_tendsto hF ρ
  have := hM.isBigO_one ℝ
  exact this

noncomputable def Φ (N : ℕ) (F : ℍ → ℂ) (ρ : SL(2, ℤ)) : ℂ → ℂ :=
  UpperHalfPlane.cuspFunction (N : ℝ) (K F ρ)

theorem hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

theorem Φ_differentiableOn (hF : ModularCurve.HasEquivariantPrimitive N f F) (ρ : SL(2, ℤ)) :
    DifferentiableOn ℂ (Φ N F ρ) (ball 0 1) :=
  differentiableOn_cuspFunction_ball hNpos (K_periodic hF ρ) (K_mdifferentiable hF ρ)
    (K_bounded hF ρ)

theorem Φ_qParam (hF : ModularCurve.HasEquivariantPrimitive N f F) (ρ : SL(2, ℤ)) (w : ℍ) :
    Φ N F ρ (𝕢 (N : ℝ) ↑w) = cexp (F (ρ⁻¹ • w)) :=
  UpperHalfPlane.eq_cuspFunction w (hNpos (N := N)).ne' (K_periodic hF ρ)

omit [NeZero N] in
theorem qParam_mem_ball (w : ℍ) : 𝕢 (N : ℝ) ↑w ∈ ball (0 : ℂ) 1 ∨ (N : ℝ) ≤ 0 := by
  by_cases hN : (0 : ℝ) < N
  · left
    rw [mem_ball_zero_iff, Function.Periodic.norm_qParam]
    have him : (0:ℝ) < Complex.im ↑w := w.2
    calc Real.exp (-2 * π * Complex.im ↑w / N) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by
            apply div_neg_of_neg_of_pos _ hN
            nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero
  · right; exact not_lt.mp hN

theorem qParam_mem_ball' (w : ℍ) : 𝕢 (N : ℝ) ↑w ∈ ball (0 : ℂ) 1 := by
  rcases qParam_mem_ball (N := N) w with h | h
  · exact h
  · exact absurd hNpos (not_lt.mpr h)

theorem qParam_mem_closedBall {w : ℍ} (hw : 1 / 2 ≤ w.im) :
    𝕢 (N : ℝ) ↑w ∈ closedBall (0 : ℂ) (Real.exp (-π / N)) := by
  rw [mem_closedBall_zero_iff, Function.Periodic.norm_qParam, Real.exp_le_exp, UpperHalfPlane.coe_im]
  rw [div_le_div_iff_of_pos_right hNpos]
  nlinarith [Real.pi_pos]

theorem re_apply_smul (hF : ModularCurve.HasEquivariantPrimitive N f F)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, (ModularCurve.period N γ f).re = 0)
    (γ : CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    (F ((γ : SL(2, ℤ)) • z)).re = (F z).re := by
  have h1 := hF.2.2.1.sub_eq_period γ z
  have h2 : hF.2.2.1.period γ = ModularCurve.period N γ f := by
    rw [ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive N f hF γ]
    rfl
  have h3 : (F ((γ : SL(2, ℤ)) • z) - F z).re = 0 := by rw [h1, h2, h γ]
  rw [Complex.sub_re, sub_eq_zero] at h3
  exact h3

theorem norm_exp_apply_smul (hF : ModularCurve.HasEquivariantPrimitive N f F)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, (ModularCurve.period N γ f).re = 0)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    ‖cexp (F (γ • z))‖ = ‖cexp (F z)‖ := by
  rw [Complex.norm_exp, Complex.norm_exp, ← re_apply_smul hF h ⟨γ, hγ⟩ z]

theorem exp_F_const (hF : ModularCurve.HasEquivariantPrimitive N f F)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, (ModularCurve.period N γ f).re = 0) :
    ∃ c : ℂ, ∀ z : ℍ, cexp (F z) = c := by
  classical
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  set r : ℝ := Real.exp (-π / N) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hNpos

  have hmax : ∀ j : SL(2, ℤ) ⧸ Γ, ∃ q ∈ closedBall (0 : ℂ) r,
      IsMaxOn (norm ∘ Φ N F j.out) (closedBall (0 : ℂ) r) q := fun j =>
    (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn (nonempty_closedBall.mpr hr0)
      (((Φ_differentiableOn hF j.out).continuousOn.mono (closedBall_subset_ball hr1)).norm)
  choose q hq hqmax using hmax
  set m : SL(2, ℤ) ⧸ Γ → ℝ := fun j => ‖Φ N F j.out (q j)‖ with hm
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ m ⟨(1 : SL(2, ℤ)), Finset.mem_univ _⟩
  set B : ℝ := m j₀ with hB

  have hbound : ∀ z : ℍ, ‖cexp (F z)‖ ≤ B := by
    intro z
    obtain ⟨g, hg⟩ := ModularGroup.exists_one_half_le_im_smul z
    obtain ⟨g0, hg0⟩ := QuotientGroup.mk_out_eq_mul Γ g
    set j : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk g with hj
    have h1 : ‖cexp (F z)‖ = ‖Φ N F j.out (𝕢 (N : ℝ) ↑(g • z))‖ := by
      rw [Φ_qParam hF, hg0, mul_inv_rev, mul_smul, inv_smul_smul]
      exact (norm_exp_apply_smul hF h (inv_mem g0.2) z).symm
    rw [h1]
    exact (hqmax j (qParam_mem_closedBall hg)).trans (hj₀ j (Finset.mem_univ _))

  set ρ₀ : SL(2, ℤ) := j₀.out with hρ₀
  have hΦd : DifferentiableOn ℂ (Φ N F ρ₀) (ball 0 1) := Φ_differentiableOn hF ρ₀
  have hnonzero : ∀ p ∈ ball (0 : ℂ) 1, p ≠ 0 → ‖Φ N F ρ₀ p‖ ≤ B := by
    intro p hp hp0
    have him : 0 < (Function.Periodic.invQParam (N : ℝ) p).im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one hNpos (mem_ball_zero_iff.mp hp) hp0
    have : Φ N F ρ₀ p = cexp (F (ρ₀⁻¹ • ⟨_, him⟩)) := by
      rw [Φ, UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hp0,
        Function.comp_apply, K, ofComplex_apply_of_im_pos him]
    rw [this]
    exact hbound _
  have hall : ∀ p ∈ ball (0 : ℂ) 1, ‖Φ N F ρ₀ p‖ ≤ B := by
    intro p hp
    rcases eq_or_ne p 0 with rfl | hp0
    · have hcont : ContinuousAt (Φ N F ρ₀) 0 :=
        (hΦd.differentiableAt (ball_mem_nhds 0 one_pos)).continuousAt
      have ht : Tendsto (fun p => ‖Φ N F ρ₀ p‖) (𝓝[≠] 0) (𝓝 ‖Φ N F ρ₀ 0‖) :=
        (hcont.tendsto.mono_left nhdsWithin_le_nhds).norm
      refine le_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) one_pos)] with p hp0 hp1
      exact hnonzero p hp1 hp0
    · exact hnonzero p hp hp0
  have hq₀ball : q j₀ ∈ ball (0 : ℂ) 1 := closedBall_subset_ball hr1 (hq j₀)
  have hismax : IsMaxOn (norm ∘ Φ N F ρ₀) (ball 0 1) (q j₀) := by
    intro p hp
    exact hall p hp
  have hconst := Complex.eq_const_of_exists_max hΦd hq₀ball hismax

  refine ⟨Φ N F ρ₀ (q j₀), fun z => ?_⟩
  have h1 : cexp (F z) = Φ N F ρ₀ (𝕢 (N : ℝ) ↑(ρ₀ • z)) := by
    rw [Φ_qParam hF, inv_smul_smul]
  rw [h1]
  exact hconst (qParam_mem_ball' _)

theorem apply_eq_zero (hF : ModularCurve.HasEquivariantPrimitive N f F)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, (ModularCurve.period N γ f).re = 0) (τ : ℍ) :
    f τ = 0 := by
  obtain ⟨c, hc⟩ := exp_F_const hF h
  have h1 : HasDerivAt (fun z : ℂ => cexp ((F ∘ ofComplex) z)) (cexp ((F ∘ ofComplex) ↑τ) * f τ) ↑τ :=
    (hF.1 τ).cexp
  have h2 : HasDerivAt (fun z : ℂ => cexp ((F ∘ ofComplex) z)) 0 ↑τ := by
    refine (hasDerivAt_const (↑τ : ℂ) c).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz]
    exact hc _
  have h3 := h1.unique h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (Complex.exp_ne_zero _)
  · exact h4

end Main

theorem main (N : ℕ) [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, (ModularCurve.period N γ f).re = 0) : f = 0 := by
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitive N f
  exact DFunLike.ext f 0 fun τ => by simpa using apply_eq_zero hF h τ

end ModularCurve.PeriodRealInjectivity

theorem solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, (ModularCurve.period N γ f).re = 0) : f = 0 :=
  ModularCurve.PeriodRealInjectivity.main N f h

end S_ModularCurve_eq_zero_of_forall_re_period_eq_zero
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_forall_re_period_eq_zero (solution)
