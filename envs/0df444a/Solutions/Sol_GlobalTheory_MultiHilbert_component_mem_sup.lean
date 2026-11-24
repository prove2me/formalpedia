-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.component_mem_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:25.378706+00:00
-- url     : https://prove2.me/submissions/9bab5cc0-2cf8-4608-b93d-23a686f44dc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_component_mem_span_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)
namespace GlobalTheory.MultiHilbert
theorem _root_.solution {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n, weightedHomogeneousComponent w n F ∈ I) (i : σ) :
    ∀ F ∈ I ⊔ Ideal.span {X i}, ∀ n,
      weightedHomogeneousComponent w n F ∈ I ⊔ Ideal.span {X i} := by
  intro F hF n
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hF
  rw [map_add]
  refine Submodule.add_mem_sup (hI a ha n) ?_
  rw [← Set.image_singleton] at hb ⊢
  exact component_mem_span_X w _ n hb
end GlobalTheory.MultiHilbert
