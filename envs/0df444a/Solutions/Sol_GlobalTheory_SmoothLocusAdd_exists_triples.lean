-- Prove2me | solution 1 for GlobalTheory.SmoothLocusAdd.exists_triples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:25:11.618111+00:00
-- url     : https://prove2.me/submissions/4252e3ef-2b55-4766-b538-5d736251b644

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
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
theorem _root_.solution {k : Type} [Field k] (a b : Spec (.of k) ⟶ scheme W)
    (hab : a ≫ toSpec W = b ≫ toSpec W) :
    ∃ (ρ : R →+* k) (P Q : Fin 3 → k) (hP : IsUnimodularSol (W.map ρ) P)
      (hQ : IsUnimodularSol (W.map ρ) Q), a = ptHom W ρ P hP ∧ b = ptHom W ρ Q hQ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec W)
  obtain ⟨P, hP, eP⟩ := exists_eq_ptHom W φ.hom a hφ.symm
  obtain ⟨Q, hQ, eQ⟩ := exists_eq_ptHom W φ.hom b (hab.symm.trans hφ.symm)
  exact ⟨φ.hom, P, Q, hP, hQ, eP, eQ⟩
end GlobalTheory.SmoothLocusAdd
