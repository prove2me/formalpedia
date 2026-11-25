-- Prove2me | solution 1 for GlobalTheory.SS.Ord.prime_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:43.696863+00:00
-- url     : https://prove2.me/submissions/60789c55-5c20-4e86-8069-4a2fd55673f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_DvrModel_mem_range_special
import Theorems.Thm_GlobalTheory_DvrModel_prime_res
import Theorems.Thm_GlobalTheory_isIntegral_of_smooth_field


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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R}
omit [IsFractionRing R K]
namespace GlobalTheory.SS.Ord
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty) : Prime (cst M U π) := by
  have := M.smooth
  obtain ⟨x, hx, hs⟩ := h
  have hp := IsPullback.of_hasPullback M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have hr : Set.range (pullback.fst M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) = M.sp :=
    Set.ext fun x => DvrModel.mem_range_special hp x
  have hc : _root_.IsConnected (Set.univ : Set ↑(pullback M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) := by
    have hi := (pullback.fst M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).isClosedEmbedding.isInducing
    refine ⟨?_, hi.isPreconnected_image.1 ?_⟩
    · obtain ⟨y, -⟩ := hr.ge hs
      exact ⟨y, trivial⟩
    · rw [Set.image_univ, hr]; exact hM.isConnected.isPreconnected
  have := connectedSpace_iff_univ.2 hc
  have := isIntegral_of_smooth_field (pullback.snd M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  exact DvrModel.prime_res hπ hp hU hx hs
end GlobalTheory.SS.Ord
