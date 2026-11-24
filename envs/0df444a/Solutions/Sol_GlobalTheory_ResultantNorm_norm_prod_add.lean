-- Prove2me | solution 1 for GlobalTheory.ResultantNorm.norm_prod_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:36.311068+00:00
-- url     : https://prove2.me/submissions/83d39820-5cad-449d-bc3b-de4787ec8562

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.ResultantNorm
open Polynomial Filter Topology
variable {K Ω : Type} [NontriviallyNormedField K] [NormedField Ω] [NormedAlgebra K Ω]
namespace GlobalTheory.ResultantNorm
theorem _root_.solution [DecidableEq Ω] (a : Multiset Ω) (g : Ω → Ω) (t : K) :
    ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖t‖ ^ a.countP (fun x => g x = 0) *
        ‖((a.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons x a ih =>
    by_cases hx : g x = 0
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih,
        Multiset.countP_cons_of_pos _ (by exact hx), Multiset.filter_cons_of_neg _ (by simpa using hx), hx,
        zero_add, norm_algebraMap']
      ring
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih,
        Multiset.countP_cons_of_neg _ (by exact hx), Multiset.filter_cons_of_pos _ (by exact hx),
        Multiset.map_cons, Multiset.prod_cons, norm_mul]
      ring
end GlobalTheory.ResultantNorm
