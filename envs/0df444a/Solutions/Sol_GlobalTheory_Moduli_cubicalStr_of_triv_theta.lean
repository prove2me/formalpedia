-- Prove2me | solution 1 for GlobalTheory.Moduli.cubicalStr_of_triv_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:27.10513+00:00
-- url     : https://prove2.me/submissions/0707051f-02c6-43b5-91da-df0ceec7987b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubicalStrOfTrivTheta
import Theorems.Thm_GlobalTheory_AbLaw_Cube_exists_normalised


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.Moduli
namespace GlobalTheory.Moduli
theorem _root_.solution : Out.Laws → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.Rigidified A M → Triv (Theta A M) → ∃ L : RigLB A, L.L = M ∧ Nonempty (CubicalStr A L) := by
  intro hL S A _ _ hA M hM hR hT
  obtain ⟨t, ht⟩ := hT
  obtain ⟨r, hr⟩ := hR
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised hM t ht
  exact ⟨⟨M, r, hM, hr⟩, rfl, ⟨GlobalTheory.AbLaw.Cube.cubicalOfNormalised
    (by cases hL; assumption) hA ⟨M, r, hM, hr⟩ t' ht' hn⟩⟩
end GlobalTheory.Moduli
