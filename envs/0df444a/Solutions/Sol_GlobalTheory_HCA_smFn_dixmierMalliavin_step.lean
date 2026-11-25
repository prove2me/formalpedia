-- Prove2me | solution 1 for GlobalTheory.HCA.smFn_dixmierMalliavin_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:58.0553+00:00
-- url     : https://prove2.me/submissions/9082ac79-e152-417f-bafd-15c29116fab5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalContDiffExpLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalTsumReplicateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStep
import Theorems.Thm_GlobalTheory_T_boundedDerivFunctional_contDiff_expLine
import Theorems.Thm_GlobalTheory_T_boundedDerivFunctional_tsum_replicate
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_exists_dixmierMalliavin_line
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
noncomputable section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic Set
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ (i : Fin d) (ε : ℝ), 0 < ε → ∃ (Λ' : List (Fin d) → (G → ℂ) → ℂ) (u v : ℝ → ℂ), SmFn h b μ S K Λ' ∧ ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ v ∧ tsupport u ⊆ Set.Icc (-ε) ε ∧ tsupport v ⊆ Set.Icc (-ε) ε ∧ ∀ f ∈ S, Λ [] f = (∫ t, u t * Λ' [] fun y => f (h.expG (t • b i) * y)) + ∫ t, v t * Λ [] fun y => f (h.expG (t • b i) * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hcont hinv K hK Λ hΛ i ε hε
  obtain ⟨M, hM0, hMb, hser⟩ := GlobalTheory.T.boundedDerivFunctional_tsum_replicate 𝔸 G 𝔤 h d b μ hμ S hcont hinv K hK Λ hΛ i
  obtain ⟨c, u, v, hu, hv, hus, hvs, hc, hid⟩ := exists_dixmierMalliavin_line M hε
  refine ⟨fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f, u, v,
    hser c hc, hu, hv, hus, hvs, fun f hf => ?_⟩
  have hmem : ∀ t : ℝ, (fun y => f (h.expG (t • b i) * y)) ∈ S := fun t => hinv f hf _
  set F : ℝ → ℂ := fun t => Λ [] fun y => f (h.expG (t • b i) * y) with hFdef
  obtain ⟨hF, hD'⟩ := GlobalTheory.T.boundedDerivFunctional_contDiff_expLine 𝔸 G 𝔤 h d b μ hμ S hcont hinv K hK Λ hΛ [] i f hf
  have hD : ∀ p t, iteratedDeriv p F t = Λ (List.replicate p i) fun y => f (h.expG (t • b i) * y) := by
    intro p t; rw [hD' p t, List.append_nil]

  have hfc : Continuous f := hcont f hf
  have hjc : Continuous fun q : ℝ × G => f (h.expG (q.1 • b i) * q.2) :=
    hfc.comp ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hjc.continuousOn
  set B : ℝ := max C 0 * μ.real K with hB
  have hB0 : 0 ≤ B := mul_nonneg (le_max_right _ _) measureReal_nonneg
  have hKint : ∀ t ∈ Icc (-ε) ε, (∫ x in K, ‖f (h.expG (t • b i) * x)‖ ∂μ) ≤ B := by
    intro t ht
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := K) (C := max C 0)
      (f := fun x => ‖f (h.expG (t • b i) * x)‖) hK.measure_lt_top (fun x hx => by
        rw [norm_norm]; exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _))
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at this
    exact this
  have hDb : ∀ p, ∀ t ∈ Icc (-ε) ε, ‖iteratedDeriv p F t‖ ≤ M p * B := by
    intro p t ht
    rw [hD]
    exact (hMb p _ (hmem t)).trans (mul_le_mul_of_nonneg_left (hKint t ht) (hM0 p))

  set a : ℂ := ((B + 1 : ℝ) : ℂ)⁻¹ with ha
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  have ha0 : a ≠ 0 := inv_ne_zero (by exact_mod_cast hB1.ne')
  have hFa : ContDiff ℝ ∞ fun t => a * F t := contDiff_const.mul hF
  have hDa : ∀ p t, iteratedDeriv p (fun t => a * F t) t = a * iteratedDeriv p F t := by
    intro p t
    exact iteratedDeriv_const_mul a (hF.contDiffAt.of_le (by exact_mod_cast le_top))
  have key := hid (fun t => a * F t) hFa (fun p t ht => by
    rw [hDa, norm_mul, ha, norm_inv, Complex.norm_real, Real.norm_of_nonneg hB1.le]
    rw [inv_mul_le_iff₀ hB1]
    calc ‖iteratedDeriv p F t‖ ≤ M p * B := hDb p t ht
      _ ≤ (B + 1) * M p := by nlinarith [hM0 p])
  simp_rw [hDa] at key
  have e1 : ∀ p, (c p : ℂ) * ∫ t, a * iteratedDeriv p F t * u t = a * ((c p : ℂ) * ∫ t, iteratedDeriv p F t * u t) := by
    intro p
    simp_rw [mul_assoc a, integral_const_mul]; ring
  have e2 : ∫ t, a * F t * v t = a * ∫ t, F t * v t := by
    rw [← integral_const_mul a]; simp_rw [mul_assoc]
  simp_rw [e1] at key
  rw [e2, tsum_mul_left, ← mul_add] at key
  have key' := mul_left_cancel₀ ha0 key
  have hF0 : F 0 = Λ [] f := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero]; simp only [one_mul]
  rw [← hF0, key']
  congr 1
  · have hugc : HasCompactSupport u := isCompact_Icc.of_isClosed_subset (isClosed_tsupport u) hus
    have hcD : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * u t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcD p).mul hu.continuous).integrable_of_hasCompactSupport hugc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * (B * ‖u t‖) := by
      intro p t
      by_cases ht : t ∈ tsupport u
      · simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have := hDb p t (hus ht)
        calc |c p| * (‖iteratedDeriv p F t‖ * ‖u t‖) ≤ |c p| * ((M p * B) * ‖u t‖) := by gcongr
          _ = |c p| * M p * (B * ‖u t‖) := by ring
      · have hu0 : u t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp only [T, hu0, mul_zero, norm_zero, le_refl]
    have hgi : Integrable (fun t => B * ‖u t‖) :=
      (hu.continuous.integrable_of_hasCompactSupport hugc).norm.const_mul _
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, B * ‖u t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e3 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * u t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e3]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    simp only [T, hD, List.nil_append]
    rw [← tsum_mul_left]
    congr 1
    funext p
    ring
  · congr 1; funext t; rw [mul_comm]
end GlobalTheory.HCA
