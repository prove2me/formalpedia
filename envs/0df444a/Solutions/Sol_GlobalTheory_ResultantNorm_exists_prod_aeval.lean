-- Prove2me | solution 1 for GlobalTheory.ResultantNorm.exists_prod_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:35.510503+00:00
-- url     : https://prove2.me/submissions/0ca81037-c723-45e3-afe8-d74b082ff945

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
namespace GlobalTheory.ResultantNorm
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (a : Multiset Ω)
    (P : K[X]) (hP : P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod) (F : K[X]) :
    ∃ u : K, algebraMap K Ω u = (a.map fun x => aeval x F).prod := by
  have hs : (P.map (algebraMap K Ω)).Splits := by
    rw [hP]; exact Splits.multisetProd (by
      intro f hf; obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hf; exact Splits.X_sub_C x)
  have hm : (P.map (algebraMap K Ω)).Monic := by
    rw [hP]; exact monic_multisetProd_X_sub_C a
  have hr : (P.map (algebraMap K Ω)).roots = a := by
    rw [hP]; exact roots_multiset_prod_X_sub_C a
  refine ⟨resultant P F (P.map (algebraMap K Ω)).natDegree F.natDegree, ?_⟩
  rw [← resultant_map_map, resultant_eq_prod_eval _ _ _ natDegree_map_le hs, hm.leadingCoeff,
    one_pow, _root_.one_mul, hr]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  rw [eval_map_algebraMap]
end GlobalTheory.ResultantNorm
