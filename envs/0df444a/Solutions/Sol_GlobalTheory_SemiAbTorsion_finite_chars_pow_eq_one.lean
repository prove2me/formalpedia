-- Prove2me | solution 1 for GlobalTheory.SemiAbTorsion.finite_chars_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:49.174898+00:00
-- url     : https://prove2.me/submissions/6d695a61-1090-4d7d-b332-48d6d7835fb4

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
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (R : Type)
    [CommRing R] [IsDomain R] {n : ℕ} (hn : 1 ≤ n) :
    Finite {t : Multiplicative X →* Rˣ // t ^ n = 1} := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : AddGroup.FG X := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨S, hS⟩ := (Group.fg_def.mp (inferInstance : Group.FG (Multiplicative X)))
  let g : {t : Multiplicative X →* Rˣ // t ^ n = 1} → (S → rootsOfUnity n R) := fun t s =>
    ⟨t.1 s.1, (mem_rootsOfUnity _ _).2 (by simpa using DFunLike.congr_fun t.2 s.1)⟩
  refine Finite.of_injective g fun a b h => Subtype.ext ?_
  refine MonoidHom.eq_of_eqOn_dense hS fun s hs => ?_
  exact congrArg Subtype.val (congrFun h ⟨s, hs⟩)
end GlobalTheory.SemiAbTorsion
