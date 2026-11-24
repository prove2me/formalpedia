-- Prove2me | solution 1 for GlobalTheory.exists_finite_intermediateField_range_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:41:32.590382+00:00
-- url     : https://prove2.me/submissions/12420efe-8b04-47f4-a9dc-ab910c97599c

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsContinuousExtensionAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] (τ : E →+* PadicAlgCl l) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x, τ x ∈ K := by
  let b := Module.finBasis ℚ E
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range (fun i => τ (b i))), ?_, ?_⟩
  · apply IntermediateField.finiteDimensional_adjoin
    intro x _
    exact (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  · intro x
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
end GlobalTheory
