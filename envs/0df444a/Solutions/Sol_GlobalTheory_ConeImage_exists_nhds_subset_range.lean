-- Prove2me | solution 1 for GlobalTheory.ConeImage.exists_nhds_subset_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:41:20.322082+00:00
-- url     : https://prove2.me/submissions/eab02da4-b1e2-49b1-a847-1cd009d1653c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
import Theorems.Thm_GlobalTheory_ConeImage_exists_continuous_slope
import Theorems.Thm_P2M_GlobalTheory_ConeImage_map_eval__3b0ac179800a
import Theorems.Thm_P2M_GlobalTheory_ConeImage_map_eval___93a91e452ef8
import Theorems.Thm_GlobalTheory_ConeImage_derivation_eq_zero
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage
namespace GlobalTheory.ConeImage
theorem _root_.solution {d : ℕ} {A W : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (hd : d ≤ Module.finrank ℂ W)
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q : MvPolynomial (Fin d) ℂ) (hp : p.eval₂ j.toRingHom a = 0)
    (hpq : Polynomial.C q ∈ Ideal.span {p, p.derivative})
    (hb : ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a)
    (Φ : W → A →ₐ[ℂ] ℂ) (hΦ : ∀ b, Differentiable ℂ fun w => Φ w b) (w₀ : W)
    (hq : Φ w₀ (j q) ≠ 0) (himm : ∀ ξ, (∀ b, fderiv ℂ (fun w => Φ w b) w₀ ξ = 0) → ξ = 0) :
    ∃ U ∈ 𝓝 (⇑(Φ w₀) : A → ℂ), ∀ φ : A →ₐ[ℂ] ℂ, ⇑φ ∈ U → ∃ w, φ = Φ w := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hp' : Φ w₀ (p.derivative.eval₂ j.toRingHom a) ≠ 0 := by
    intro h
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hpq
    have := congrArg (fun r => Φ w₀ (Polynomial.eval₂ j.toRingHom a r)) hαβ
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hp, map_add, map_mul, h,
      Polynomial.eval₂_C, mul_zero, map_zero, add_zero] at this
    exact hq this.symm
  let u : W → Fin d → ℂ := fun w i => Φ w (j (MvPolynomial.X i))
  have hu : Differentiable ℂ u := differentiable_pi.mpr fun i => hΦ _
  have hus : HasStrictFDerivAt u (fderiv ℂ u w₀) w₀ :=
    (GlobalTheory.SCV.analyticOnNhd_of_differentiable hu Set.univ w₀ trivial).hasStrictFDerivAt
  have hinj : Function.Injective (fderiv ℂ u w₀) := by
    rw [injective_iff_map_eq_zero]
    intro ξ hξ
    refine himm ξ fun b => derivation_eq_zero j a p q hp hb (Φ w₀) hq hp'
      (fun b => fderiv ℂ (fun w => Φ w b) w₀ ξ) ?_ ?_ ?_ ?_ b
    · intro x y
      simp only [map_add]
      rw [fderiv_fun_add (hΦ x w₀) (hΦ y w₀)]; rfl
    · intro x y
      simp only [map_mul]
      rw [fderiv_fun_mul (hΦ x w₀) (hΦ y w₀)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    · intro c
      simp
    · intro i
      have := congrFun hξ i
      rw [fderiv_pi (fun i => hΦ _ w₀)] at this
      exact this
  have hsurj : (fderiv ℂ u w₀).range = ⊤ := by
    have h1 := LinearMap.finrank_range_of_inj (f := (fderiv ℂ u w₀ : W →ₗ[ℂ] (Fin d → ℂ))) hinj
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    rw [Module.finrank_fin_fun]
    exact hd.trans h1.ge
  have hmap := hus.map_nhds_eq_of_surj hsurj
  obtain ⟨k, hk, hk'⟩ := exists_continuous_slope p
  have hk0 : k (u w₀, Φ w₀ a, Φ w₀ a) ≠ 0 := by
    rw [(hk' _ _ (Φ w₀ a)).2, ← map_eval₂']; exact hp'
  have hev : ∀ᶠ x in 𝓝 (u w₀, Φ w₀ a, Φ w₀ a), k x ≠ 0 := hk.continuousAt.eventually_ne hk0
  obtain ⟨U₁, hU₁, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨V₁, hV₁, V₂, hV₂, hVV⟩ := mem_nhds_prod_iff.mp hV
  have hW : (fun w => Φ w a) ⁻¹' V₂ ∈ 𝓝 w₀ := (hΦ a).continuous.continuousAt hV₂
  have hU₂ : u '' ((fun w => Φ w a) ⁻¹' V₂) ∈ 𝓝 (u w₀) := hmap ▸ image_mem_map hW
  have c1 : Continuous fun (x : A → ℂ) (i : Fin d) => x (j (MvPolynomial.X i)) := by fun_prop
  have c2 : Continuous fun (x : A → ℂ) => x a := by fun_prop
  have c3 : Continuous fun (x : A → ℂ) => x (j q) := by fun_prop
  refine ⟨_, inter_mem (inter_mem (c1.continuousAt (inter_mem hU₁ hU₂)) (c2.continuousAt hV₁))
    (c3.continuousAt.eventually_ne hq), ?_⟩
  rintro φ ⟨⟨⟨h1, w, hw, h2⟩, h3⟩, h4⟩
  refine ⟨w, ?_⟩
  have h2' : (fun i => φ (j (MvPolynomial.X i))) = u w := h2.symm
  have hk1 : k (u w, φ a, Φ w a) ≠ 0 :=
    hUV (Set.mk_mem_prod (h2' ▸ h1) (hVV (Set.mk_mem_prod h3 hw)))
  have e1 := map_eval₂' j φ a p
  have e2 := map_eval₂' j (Φ w) a p
  rw [hp, map_zero] at e1 e2
  rw [h2'] at e1
  have ha : Φ w a = φ a := by
    have := (hk' (u w) (φ a) (Φ w a)).1
    rw [← e1, ← e2, sub_zero] at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this.symm).resolve_right hk1)
  ext b
  obtain ⟨r, hr⟩ := hb b
  have f1 := map_eval₂' j φ a r
  have f2 := map_eval₂' j (Φ w) a r
  rw [← hr, map_mul] at f1 f2
  have hqq : Φ w (j q) = φ (j q) := by rw [map_eval₂, map_eval₂ j φ, h2']
  rw [h2'] at f1
  rw [ha, hqq] at f2
  exact mul_left_cancel₀ (h4 : φ (j q) ≠ 0) (f1.trans f2.symm)
end GlobalTheory.ConeImage
