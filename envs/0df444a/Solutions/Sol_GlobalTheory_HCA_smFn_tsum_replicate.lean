-- Prove2me | solution 1 for GlobalTheory.HCA.smFn_tsum_replicate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:23:49.811861+00:00
-- url     : https://prove2.me/submissions/522e3cd9-f3a9-4831-abe2-cdd8f2e9ef0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalTsumReplicate
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_add_smul
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
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
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ i, ∃ M : ℕ → ℝ, (∀ p, 0 ≤ M p) ∧ (∀ p, ∀ f ∈ S, ‖Λ (List.replicate p i) f‖ ≤ M p * ∫ x in K, ‖f x‖ ∂μ) ∧ ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) → SmFn h b μ S K fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hSc hSL K hK Λ hΛ i
  classical
  haveI := hμ
  choose C0 hC0 using hΛ.bdd
  let C : List (Fin d) → ℝ := fun l => max 0 (C0 l)
  have hC0' : ∀ l, 0 ≤ C l := fun l => le_max_left _ _
  have hC : ∀ l, ∀ f ∈ S, ‖Λ l f‖ ≤ C l * ∫ x in K, ‖f x‖ ∂μ := by
    intro l f hf
    have hI : 0 ≤ ∫ x in K, ‖f x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    exact (hC0 l f hf).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hI)
  let D : ℕ → ℕ → ℝ := fun p k =>
    C (((Encodable.decode k : Option (List (Fin d))).getD []) ++ List.replicate p i)
  let M : ℕ → ℝ := fun p => C (List.replicate p i) + ∑ k ∈ Finset.range (p + 1), D p k
  have hD0 : ∀ p k, 0 ≤ D p k := fun p k => hC0' _
  have hM0 : ∀ p, 0 ≤ M p := fun p => add_nonneg (hC0' _) (Finset.sum_nonneg fun k _ => hD0 p k)
  have hMl : ∀ l : List (Fin d), ∀ p, Encodable.encode l ≤ p → C (l ++ List.replicate p i) ≤ M p := by
    intro l p hp
    have h1 : D p (Encodable.encode l) ≤ ∑ k ∈ Finset.range (p + 1), D p k :=
      Finset.single_le_sum (f := D p) (fun k _ => hD0 p k) (Finset.mem_range.2 (Nat.lt_succ_of_le hp))
    have h2 : D p (Encodable.encode l) = C (l ++ List.replicate p i) := by
      simp only [D, Encodable.encodek, Option.getD_some]
    have h3 := hC0' (List.replicate p i)
    simp only [M]
    linarith
  refine ⟨M, hM0, ?_, ?_⟩
  · intro p f hf
    refine (hC _ f hf).trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => norm_nonneg _))
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hD0 p k)
  intro c hc
  have hsum : ∀ l, Summable (fun p => |c p| * C (l ++ List.replicate p i)) := by
    intro l
    refine Summable.of_norm_bounded_eventually_nat hc ?_
    filter_upwards [Filter.eventually_ge_atTop (Encodable.encode l)] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hC0' _))]
    exact mul_le_mul_of_nonneg_left (hMl l p hp) (abs_nonneg _)
  have hterm : ∀ l, ∀ f ∈ S, ∀ p, ‖(c p : ℂ) * Λ (l ++ List.replicate p i) f‖ ≤
      |c p| * C (l ++ List.replicate p i) * ∫ x in K, ‖f x‖ ∂μ := by
    intro l f hf p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC _ f hf) (abs_nonneg _)
  have hsumm : ∀ l, ∀ f ∈ S, Summable (fun p => (c p : ℂ) * Λ (l ++ List.replicate p i) f) :=
    fun l f hf => Summable.of_norm_bounded ((hsum l).mul_right _) (hterm l f hf)
  have hexp0 : h.expG 0 = 1 := by
    apply Subtype.ext; apply Units.ext; simp
  refine ⟨?_, ?_, ?_⟩
  · intro l f hf f' hf' a
    have e : ∀ p, (c p : ℂ) * Λ (l ++ List.replicate p i) (a • f + f') =
        a * ((c p : ℂ) * Λ (l ++ List.replicate p i) f) + (c p : ℂ) * Λ (l ++ List.replicate p i) f' := by
      intro p; rw [hΛ.lin _ f hf f' hf' a]; ring
    simp_rw [e]
    rw [Summable.tsum_add ((hsumm l f hf).mul_left a) (hsumm l f' hf'), tsum_mul_left]
  · intro l
    refine ⟨∑' p, |c p| * C (l ++ List.replicate p i), fun f hf => ?_⟩
    rw [← tsum_mul_right]
    exact tsum_of_norm_bounded ((hsum l).mul_right _).hasSum (hterm l f hf)
  · intro l j f hf
    have hft : ∀ t : ℝ, (fun y => f (h.expG (t • b j) * y)) ∈ S := fun t => hSL f hf _
    have hcont : Continuous fun q : ℝ × G => f (h.expG (q.1 • b j) * q.2) :=
      (hSc f hf).comp ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_snd)
    obtain ⟨A, hA⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
      hcont.continuousOn
    have hB : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∫ x in K, ‖f (h.expG (t • b j) * x)‖ ∂μ ≤ max 0 A * μ.real K := by
      intro t ht
      have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (C := max 0 A)
        (f := fun x => ‖f (h.expG (t • b j) * x)‖) hK.measure_lt_top (fun x hx => by
          rw [norm_norm]; exact (hA (t, x) ⟨ht, hx⟩).trans (le_max_right _ _))
      exact (Real.le_norm_self _).trans h1
    have hderiv : ∀ (m : List (Fin d)) (t : ℝ), HasDerivAt (fun s : ℝ => Λ m fun y => f (h.expG (s • b j) * y))
        (Λ (j :: m) fun y => f (h.expG (t • b j) * y)) t := by
      intro m t
      have h0 := hΛ.der m j _ (hft t)
      have e1 : (fun s : ℝ => Λ m fun y => f (h.expG (t • b j) * (h.expG (s • b j) * y))) =
          fun s => Λ m fun y => f (h.expG ((t + s) • b j) * y) := by
        funext s; congr 1; funext y; rw [h.expG_add_smul, mul_assoc]
      rw [e1] at h0
      have h1 : HasDerivAt (fun s : ℝ => Λ m fun y => f (h.expG ((t + s) • b j) * y))
          (Λ (j :: m) fun y => f (h.expG (t • b j) * y)) (t - t) := by rw [sub_self]; exact h0
      have h2 := h1.comp_sub_const t t
      have e2 : ∀ u : ℝ, t + (u - t) = u := fun u => by ring
      simp only [e2] at h2
      exact h2
    have key := hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
      (g := fun p s => (c p : ℂ) * Λ (l ++ List.replicate p i) fun y => f (h.expG (s • b j) * y))
      (g' := fun p s => (c p : ℂ) * Λ (j :: (l ++ List.replicate p i)) fun y => f (h.expG (s • b j) * y))
      (u := fun p => |c p| * C ((j :: l) ++ List.replicate p i) * (max 0 A * μ.real K))
      ((hsum (j :: l)).mul_right _) isOpen_Ioo isPreconnected_Ioo
      (fun p s _ => (hderiv _ s).const_mul _)
      (fun p s hs => (hterm (j :: l) _ (hft s) p).trans
        (mul_le_mul_of_nonneg_left (hB s (Set.Ioo_subset_Icc_self hs)) (mul_nonneg (abs_nonneg _) (hC0' _))))
      (by norm_num) (hsumm l _ (hft 0)) (by norm_num)
    simp only [zero_smul, hexp0, one_mul] at key
    exact key
end GlobalTheory.HCA
