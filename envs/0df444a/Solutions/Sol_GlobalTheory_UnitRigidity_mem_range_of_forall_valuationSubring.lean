-- Prove2me | solution 1 for GlobalTheory.UnitRigidity.mem_range_of_forall_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:36:45.836163+00:00
-- url     : https://prove2.me/submissions/b2d06585-f945-406f-a277-571d6a77fcc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.UnitRigidity
namespace GlobalTheory.UnitRigidity
theorem _root_.solution {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    (x : L) (h : ∀ O : ValuationSubring L, (∀ k, algebraMap K L k ∈ O) → x ∈ O) :
    x ∈ Set.range (algebraMap K L) := by
  have h1 : x ∈ (integralClosure (Subring.closure (Set.range (algebraMap K L))) L).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    exact fun V => h V.1 fun k => V.2 ⟨k, rfl⟩
  have e : Subring.closure (Set.range (algebraMap K L)) = (algebraMap K L).range :=
    Subring.closure_eq (algebraMap K L).range
  rw [e] at h1
  have h2 : IsIntegral (algebraMap K L).range x := h1
  have h3 : IsIntegral K x := by
    obtain ⟨p, hp, hpx⟩ := h2
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (algebraMap K L).rangeRestrict_surjective p) hp
    refine ⟨q, hqm, ?_⟩
    rw [← hq, Polynomial.eval₂_map] at hpx
    exact hpx
  exact minpoly.mem_range_of_degree_eq_one K x
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h3))
end GlobalTheory.UnitRigidity
