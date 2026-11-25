-- Prove2me | solution 1 for GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:35.534848+00:00
-- url     : https://prove2.me/submissions/fdef7693-20db-4223-9caf-18e8f7312778

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernelStatement
import Theorems.Thm_GlobalTheory_mapDeg_eq_pow_mul_card_ker


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
open GlobalTheory.ZV
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A), IsMonHom α → IsFinite α.left → Finite {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1} ∧ ∃ e : ℕ, MapDeg α.left (ringExpChar K ^ e * Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1}) := by
  first | exact @GlobalTheory.mapDeg_eq_pow_mul_card_ker | exact GlobalTheory.mapDeg_eq_pow_mul_card_ker | (intros; apply GlobalTheory.mapDeg_eq_pow_mul_card_ker <;> assumption)
end _root_.GlobalTheory.T
