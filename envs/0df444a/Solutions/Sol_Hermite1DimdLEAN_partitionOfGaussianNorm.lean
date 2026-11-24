-- Prove2me | solution 1 for Hermite1DimdLEAN.partitionOfGaussianNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:21.548597+00:00
-- url     : https://prove2.me/submissions/04423b37-6937-43e9-a8db-8e1e8222dd63

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma measurableSet_productAnnulus
    {d : ℕ} (j : MultiIndex d) :
    MeasurableSet (productAnnulus j) := by
  classical
  have h :
      MeasurableSet (⋂ q : Fin d, {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1}) := by
    refine MeasurableSet.iInter (f := fun q : Fin d => {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ <
        (j q : ℝ) + 1}) ?_
    intro q
    have hge : MeasurableSet {z : CSpace d | (j q : ℝ) ≤ ‖z q‖} :=
      measurableSet_le measurable_const (measurable_norm.comp (continuous_apply q).measurable)
    have hlt : MeasurableSet {z : CSpace d | ‖z q‖ < (j q : ℝ) + 1} :=
      measurableSet_lt (measurable_norm.comp (continuous_apply q).measurable) measurable_const
    simpa [Set.ofPred_and] using hge.inter hlt
  simpa [productAnnulus, Set.ofPred_forall] using h
private lemma productAnnulus_eq_of_mem
    {d : ℕ} {j ℓ : MultiIndex d} {z : CSpace d}
    (hj : z ∈ productAnnulus j) (hℓ : z ∈ productAnnulus ℓ) :
    j = ℓ := by
  funext q
  rcases hj q with ⟨hj_lower, hj_upper⟩
  rcases hℓ q with ⟨hℓ_lower, hℓ_upper⟩
  have h1 : j q < ℓ q + 1 := by exact_mod_cast lt_of_le_of_lt hj_lower hℓ_upper
  have h2 : ℓ q < j q + 1 := by exact_mod_cast lt_of_le_of_lt hℓ_lower hj_upper
  omega
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (F : CSpace d → ℂ)
    (hF : Integrable (fun z : CSpace d => ‖F z‖ ^ 2) (gaussianMeasure d)) :
    gaussianL2NormSq F = ∑' j : MultiIndex d, annulusMass j F := by
  /-
  Scaffolding guidance:
  later files only need the partition formula, not an explicit derivation.
  Keep it annulus-facing and do not force downstream code to reopen Tonelli.
  -/
  have hmeas : ∀ j : MultiIndex d, MeasurableSet (productAnnulus j) := measurableSet_productAnnulus
  have hdisj : Pairwise (fun j k : MultiIndex d => Disjoint (productAnnulus j) (productAnnulus k))
      := by
    intro j k hjk
    rw [Set.disjoint_iff]
    intro z hz
    exact hjk (productAnnulus_eq_of_mem hz.1 hz.2)
  have hcover : (⋃ j : MultiIndex d, productAnnulus j) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨fun q => Nat.floor ‖z q‖, fun q => ⟨?_, ?_⟩⟩
    · exact_mod_cast Nat.floor_le (show 0 ≤ ‖z q‖ by positivity)
    · exact_mod_cast Nat.lt_floor_add_one ‖z q‖
  have hfi :
      IntegrableOn (fun z : CSpace d => ‖F z‖ ^ 2)
        (⋃ j : MultiIndex d, productAnnulus j) (gaussianMeasure d) := by simpa [hcover] using hF
  calc
    gaussianL2NormSq F
        = ∫ z in ⋃ j : MultiIndex d, productAnnulus j, ‖F z‖ ^ 2 ∂ gaussianMeasure d := by
            simp [gaussianL2NormSq, hcover]
    _ = ∑' j : MultiIndex d, ∫ z in productAnnulus j, ‖F z‖ ^ 2 ∂ gaussianMeasure d := by
          simpa [hcover] using
            MeasureTheory.integral_iUnion
              (f := fun z : CSpace d => ‖F z‖ ^ 2) hmeas hdisj hfi
    _ = ∑' j : MultiIndex d, annulusMass j F := by
          congr with j
          simpa [annulusMass, Set.indicator] using
            (MeasureTheory.integral_indicator
              (μ := gaussianMeasure d)
              (f := fun z : CSpace d => ‖F z‖ ^ 2)
              (hs := hmeas j)).symm
end Hermite1DimdLEAN
