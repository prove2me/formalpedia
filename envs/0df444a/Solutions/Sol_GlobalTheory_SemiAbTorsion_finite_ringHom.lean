-- Prove2me | solution 1 for GlobalTheory.SemiAbTorsion.finite_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:42:54.615531+00:00
-- url     : https://prove2.me/submissions/5a85c660-f29a-47bc-8528-ce7149768bd7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde

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
open GlobalTheory
open GlobalTheory.SemiAbTorsion
namespace GlobalTheory.SemiAbTorsion
theorem _root_.solution (A F : Type) [CommRing A] [CommRing F] [Finite F]
    [Algebra.FiniteType ℤ A] : Finite (A →+* F) := by
  obtain ⟨S, hS⟩ := (inferInstance : Algebra.FiniteType ℤ A).out
  refine Finite.of_injective (fun (φ : A →+* F) (s : S) => φ s.1) fun a b h => ?_
  have : a.toIntAlgHom = b.toIntAlgHom :=
    AlgHom.ext_of_adjoin_eq_top hS fun s hs => congrFun h ⟨s, hs⟩
  ext x
  exact DFunLike.congr_fun this x
end GlobalTheory.SemiAbTorsion
