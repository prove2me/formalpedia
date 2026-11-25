-- Prove2me | solution 1 for GlobalTheory.SmoothLocusAdd.IsSumAt.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:47:47.648459+00:00
-- url     : https://prove2.me/submissions/f402ac20-40fa-477b-9023-22eaecc61bde

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
import Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_triples
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
open GlobalTheory GlobalTheory.SmoothLocusAdd
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
namespace GlobalTheory.SmoothLocusAdd
namespace IsSumAt
theorem _root_.solution {k : Type} [Field k] {a b c c' : Spec (.of k) ⟶ scheme W}
    (hab : a ≫ toSpec W = b ≫ toSpec W) (h : IsSumAt W a b c) (h' : IsSumAt W a b c') :
    c = c' := by
  obtain ⟨ρ, P, Q, hP, hQ, eP, eQ⟩ := exists_triples W a b hab
  obtain ⟨_, e⟩ := h ρ P Q hP hQ eP eQ
  obtain ⟨_, e'⟩ := h' ρ P Q hP hQ eP eQ
  exact e.trans e'.symm
end IsSumAt
end GlobalTheory.SmoothLocusAdd
