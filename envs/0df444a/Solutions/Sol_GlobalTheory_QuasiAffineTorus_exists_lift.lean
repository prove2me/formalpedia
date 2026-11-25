-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:48:21.890789+00:00
-- url     : https://prove2.me/submissions/8fe24641-268d-478b-ac2f-270437a85cba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
import Theorems.Thm_GlobalTheory_ReducedSubgroup_range_subset_of_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.QuasiAffineTorus
open RationalPoint
variable {k : Type} [Field k]
variable [IsAlgClosed k]
namespace GlobalTheory.QuasiAffineTorus
theorem _root_.solution {T N G : Over (Sp k)} [LocallyOfFiniteType T.hom] [IsReduced T.left]
    [IsReduced N.left] (ν : N ⟶ G) [IsClosedImmersion ν.left] (g : T ⟶ G)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ T, Set.range (x ≫ g).left ⊆ Set.range ν.left) :
    ∃ l : T ⟶ N, l ≫ ν = g := by
  have h1 := ReducedSubgroup.range_subset_of_points g ν.left.isClosedEmbedding.isClosed_range h
  have h2 : ν.left.ker ≤ g.left.ker := by
    refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U a ha => ?_
    rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
    intro t ht
    obtain ⟨n, hn⟩ := h1 ⟨t, rfl⟩
    have h3 : n ∈ ν.left ⁻¹ᵁ G.left.basicOpen a := by
      change ν.left n ∈ G.left.basicOpen a
      rw [hn]
      exact ht
    rw [Scheme.preimage_basicOpen, show ν.left.app U a = 0 from ν.left.ideal_ker_le U ha,
      Scheme.basicOpen_zero] at h3
    exact h3
  have h3 := IsClosedImmersion.lift_fac ν.left g.left h2
  refine ⟨Over.homMk (IsClosedImmersion.lift ν.left g.left h2) ?_, ?_⟩
  · rw [← Over.w ν, ← Category.assoc, h3, Over.w]
  · ext1
    exact h3
end GlobalTheory.QuasiAffineTorus
