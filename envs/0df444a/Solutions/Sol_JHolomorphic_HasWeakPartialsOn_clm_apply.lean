-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.clm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:57:42.902299+00:00
-- url     : https://prove2.me/submissions/e8211cac-f9c0-43bb-9d59-06a5402527f5

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Theorems.Thm_JHolomorphic_contDiff_mul_of_tsupport_subset
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_integral_contDiff_one



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Weak Leibniz rule: if `w` has weak partials `wₛ`, `wₜ` on an open set `U` and `A` is a `C¹`
family of linear maps on `U`, then `z ↦ A(z) w(z)` has weak partials
`(∂ₛA) w + A wₛ` and `(∂ₜA) w + A wₜ` on `U`. -/
theorem HasWeakPartialsOn.clm_apply_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set ℂ} (hU : IsOpen U) {A : ℂ → E →L[ℝ] F} (hA : ContDiffOn ℝ 1 A U)
    {w ws wt : ℂ → E} (hw : HasWeakPartialsOn U w ws wt)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn w K ∧ IntegrableOn ws K ∧ IntegrableOn wt K) :
    HasWeakPartialsOn U (fun z => A z (w z)) (fun z => fderiv ℝ A z 1 (w z) + A z (ws z))
      (fun z => fderiv ℝ A z Complex.I (w z) + A z (wt z)) := by
  have hiw : ∀ K ⊆ U, IsCompact K → IntegrableOn w K := fun K hKU hK => (hint K hKU hK).1
  -- coordinates of `A` in a basis of `E →L[ℝ] F`
  let b := Module.finBasis ℝ (E →L[ℝ] F)
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ (E →L[ℝ] F)) → (E →L[ℝ] F) →L[ℝ] ℝ,
      ∀ k L, c k L = b.repr L k :=
    ⟨fun k => LinearMap.toContinuousLinearMap (b.coord k), fun k L => by simp⟩
  have hexp : ∀ L : E →L[ℝ] F, ∀ x : E, L x = ∑ k, c k L • b k x := by
    intro L x
    calc L x = (∑ k, b.repr L k • b k) x := by rw [b.sum_repr]
      _ = ∑ k, c k L • b k x := by
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hc]
  obtain ⟨a, ha_def⟩ : ∃ a : Fin (Module.finrank ℝ (E →L[ℝ] F)) → ℂ → ℝ,
      ∀ k, a k = fun z => c k (A z) := ⟨fun k z => c k (A z), fun k => rfl⟩
  have ha : ∀ k, ContDiffOn ℝ 1 (a k) U := fun k => by
    rw [ha_def k]; exact (c k).contDiff.comp_contDiffOn hA
  have hda : ∀ k, ∀ z ∈ U, ∀ v : ℂ, fderiv ℝ (a k) z v = c k (fderiv ℝ A z v) := by
    intro k z hz v
    have hAd : DifferentiableAt ℝ A z :=
      (hA.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
    rw [ha_def k, show (fun z => c k (A z)) = c k ∘ A from rfl,
      ((c k).hasFDerivAt.comp z hAd.hasFDerivAt).fderiv]
    rfl
  have key : ∀ (v : ℂ) (wv : ℂ → E), (∀ K ⊆ U, IsCompact K → IntegrableOn wv K) →
      (∀ ψ : ℂ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∫ z, fderiv ℝ ψ z v • w z = -∫ z, ψ z • wv z) →
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ z, fderiv ℝ φ z v • A z (w z) = -∫ z, φ z • (fderiv ℝ A z v (w z) + A z (wv z)) := by
    intro v wv hiwv hH φ hφ hφc hφU
    obtain ⟨hdφ, hdφc, hdφU⟩ := fderiv_apply_isTestFunction hφ hφc hφU v
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
    have hφU0 : ∀ z, z ∉ U → φ z = 0 := fun z hz =>
      Function.notMem_support.mp fun h' => hz (hφU (subset_tsupport _ h'))
    have hdφU0 : ∀ z, z ∉ U → fderiv ℝ φ z v = 0 := fun z hz => by
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h' => hz (hφU h'))]; simp
    -- the test functions `φ aₖ`
    obtain ⟨ψ, hψ_def⟩ : ∃ ψ : Fin (Module.finrank ℝ (E →L[ℝ] F)) → ℂ → ℝ,
        ∀ k, ψ k = fun z => φ z * a k z := ⟨fun k z => φ z * a k z, fun k => rfl⟩
    have hψ : ∀ k, ContDiff ℝ 1 (ψ k) := fun k => by
      rw [hψ_def k]; exact contDiff_mul_of_tsupport_subset hU (n := 1) hφ1 hφU (ha k)
    have hψU : ∀ k, tsupport (ψ k) ⊆ U := fun k => by
      rw [hψ_def k]; exact tsupport_mul_subset_left.trans hφU
    have hψc : ∀ k, HasCompactSupport (ψ k) := fun k => by
      rw [hψ_def k]; exact hφc.mul_right
    have hdψ : ∀ k z, fderiv ℝ (ψ k) z v =
        fderiv ℝ φ z v * a k z + φ z * fderiv ℝ (a k) z v := by
      intro k z
      by_cases hz : z ∈ U
      · have hd1 : DifferentiableAt ℝ φ z := hφ1.differentiable one_ne_zero z
        have hd2 : DifferentiableAt ℝ (a k) z :=
          ((ha k).differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
        rw [hψ_def k, show (fun z => φ z * a k z) = φ * a k from rfl, fderiv_mul hd1 hd2]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      · rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h' => hz (hψU k h')), hφU0 z hz,
          hdφU0 z hz]
        simp
    -- continuity on `U` of the coefficients
    have hac : ∀ k, ContinuousOn (a k) U := fun k => (ha k).continuousOn
    have hdac : ∀ k, ContinuousOn (fun z => fderiv ℝ (a k) z v) U := fun k =>
      ((ha k).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    -- integrability of the pieces
    have i1 : ∀ k, Integrable (fun z => (fderiv ℝ φ z v * a k z) • w z) := fun k =>
      integrable_smul_of_integrableOn_compact hiw (hdφ.continuous.continuousOn.mul (hac k))
        hdφc.mul_right (tsupport_mul_subset_left.trans hdφU)
    have i2 : ∀ k, Integrable (fun z => (φ z * fderiv ℝ (a k) z v) • w z) := fun k =>
      integrable_smul_of_integrableOn_compact hiw (hφ.continuous.continuousOn.mul (hdac k))
        hφc.mul_right (tsupport_mul_subset_left.trans hφU)
    have i3 : ∀ k, Integrable (fun z => ψ k z • wv z) := fun k =>
      integrable_smul_of_integrableOn_compact hiwv (hψ k).continuous.continuousOn (hψc k)
        (hψU k)
    have i23 : ∀ k, Integrable
        (fun z => (φ z * fderiv ℝ (a k) z v) • w z + ψ k z • wv z) := fun k =>
      (i2 k).add (i3 k)
    -- one coordinate at a time
    have hk : ∀ k, ∫ z, (fderiv ℝ φ z v * a k z) • w z =
        -((∫ z, (φ z * fderiv ℝ (a k) z v) • w z) + ∫ z, ψ k z • wv z) := by
      intro k
      have e := hH (ψ k) (hψ k) (hψc k) (hψU k)
      simp_rw [hdψ k, add_smul] at e
      rw [integral_add (i1 k) (i2 k)] at e
      rw [eq_neg_iff_add_eq_zero] at e ⊢
      rw [← add_assoc]
      exact e
    -- pointwise expansions
    have hL : ∀ z, fderiv ℝ φ z v • A z (w z) =
        ∑ k, b k ((fderiv ℝ φ z v * a k z) • w z) := by
      intro z
      rw [hexp (A z) (w z), Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, smul_smul, ha_def k]
    have hR : ∀ z, φ z • (fderiv ℝ A z v (w z) + A z (wv z)) =
        ∑ k, b k ((φ z * fderiv ℝ (a k) z v) • w z + ψ k z • wv z) := by
      intro z
      by_cases hz : z ∈ U
      · rw [hexp (fderiv ℝ A z v) (w z), hexp (A z) (wv z), ← Finset.sum_add_distrib,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_add, map_smul, map_smul, hda k z hz v, smul_add, smul_smul, smul_smul,
          hψ_def k, ha_def k]
      · simp [hφU0 z hz, hψ_def]
    calc ∫ z, fderiv ℝ φ z v • A z (w z)
        = ∑ k, b k (∫ z, (fderiv ℝ φ z v * a k z) • w z) := by
          simp_rw [hL]
          rw [integral_finset_sum _ fun k _ => (b k).integrable_comp (i1 k)]
          exact Finset.sum_congr rfl fun k _ => (b k).integral_comp_comm (i1 k)
      _ = -∑ k, b k (∫ z, (φ z * fderiv ℝ (a k) z v) • w z + ψ k z • wv z) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hk k, map_neg, integral_add (i2 k) (i3 k)]
      _ = -∫ z, φ z • (fderiv ℝ A z v (w z) + A z (wv z)) := by
          simp_rw [hR]
          rw [integral_finset_sum _ fun k _ => (b k).integrable_comp (i23 k)]
          congr 1
          exact (Finset.sum_congr rfl fun k _ => (b k).integral_comp_comm (i23 k)).symm
  have hHw := HasWeakPartialsOn.integral_contDiff_one hU hw hint
  intro φ hφ hφc hφU
  exact ⟨key 1 ws (fun K hKU hK => (hint K hKU hK).2.1)
      (fun ψ h1 h2 h3 => (hHw ψ h1 h2 h3).1) φ hφ hφc hφU,
    key Complex.I wt (fun K hKU hK => (hint K hKU hK).2.2)
      (fun ψ h1 h2 h3 => (hHw ψ h1 h2 h3).2) φ hφ hφc hφU⟩

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set ℂ} (hU : IsOpen U) {A : ℂ → E →L[ℝ] F} (hA : ContDiffOn ℝ 1 A U)
    {w ws wt : ℂ → E} (hw : HasWeakPartialsOn U w ws wt)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn w K ∧ IntegrableOn ws K ∧ IntegrableOn wt K) :
    HasWeakPartialsOn U (fun z => A z (w z)) (fun z => fderiv ℝ A z 1 (w z) + A z (ws z))
      (fun z => fderiv ℝ A z Complex.I (w z) + A z (wt z)) :=
  HasWeakPartialsOn.clm_apply_aux hU hA hw hint
