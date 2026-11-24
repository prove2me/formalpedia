-- Prove2me | solution 1 for GlobalTheory.KS.square_fibre_affine_opens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:02.687839+00:00
-- url     : https://prove2.me/submissions/997552cc-598f-4e64-bf67-ac72e1e8f1d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSquareOfIsGrpPullback
import Theorems.Thm_GlobalTheory_KS_exists_square_of_isGrpPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap x₀) m → (∃ m₂ : (P₀.A ⊗ P₀.A).left ⟶ (P.A ⊗ P.A).left, IsSquare m m₂ ∧ m₂ ≫ (fst P.A P.A * snd P.A P.A).left = (fst P₀.A P₀.A * snd P₀.A P₀.A).left ≫ m ∧ m₂ ≫ (P.A ⊗ P.A).hom = (P₀.A ⊗ P₀.A).hom ≫ spMap x₀) ∧ IsSeparated P₀.A.hom ∧ IsPullback (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left P₀.A.hom P₀.A.hom ∧ (∀ W : P.A.left.Opens, IsAffineOpen W → IsAffineOpen (m ⁻¹ᵁ W)) ∧ ∀ W W' : P.A.left.Opens, IsAffineOpen W → IsAffineOpen W' → IsAffineOpen (W ⊓ W') := by
  intro K _ P₀ R _ x₀ P m h
  have hp₀ : IsProper P₀.A.hom := P₀.isAb.proper
  have hp : IsProper P.A.hom := P.isAb.proper
  refine ⟨exists_square_of_isGrpPullback _ _ _ _ h, inferInstance,
    IsPullback.of_hasPullback _ _, fun W hW => ?_, fun W W' hW hW' => ?_⟩
  · have : IsAffineHom m :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) h.1.flip inferInstance
    exact hW.preimage m
  · have : IsSeparated (terminal.from P.A.left) := by
      rw [← terminal.comp_from P.A.hom]; infer_instance
    exact hW.inf hW'
end GlobalTheory.KS
