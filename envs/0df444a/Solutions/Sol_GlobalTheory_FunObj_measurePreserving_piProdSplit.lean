-- Prove2me | solution 1 for GlobalTheory.FunObj.measurePreserving_piProdSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:52:47.220944+00:00
-- url     : https://prove2.me/submissions/ec75b9dc-6345-4f4b-8cc2-88accf0c3e1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {ι : Type*} [Fintype ι] {α β γ : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
  [∀ i, MeasurableSpace (γ i)]
namespace GlobalTheory.FunObj
theorem _root_.solution (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] : MeasurePreserving (piProdSplit α β) (.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (piProdSplit α β).measurable
  map_eq := by
    refine (Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply, show piProdSplit α β ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
          (Set.univ.pi fun i ↦ s i ×ˢ t i) by
          ext; simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi, forall_and]; rfl]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]
end GlobalTheory.FunObj
