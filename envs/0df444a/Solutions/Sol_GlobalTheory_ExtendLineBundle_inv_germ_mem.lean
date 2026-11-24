-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.inv_germ_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:46.461945+00:00
-- url     : https://prove2.me/submissions/03f2da84-0e17-43c2-92ae-0131ee30326b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_algebraMap_germ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {U : X.Opens} (a : Γ(X, U)) (h : genericPoint X ∈ U) {y : X}
    (hy : y ∈ X.basicOpen a) :
    X.presheaf.germ U _ h a ≠ 0 ∧ (X.presheaf.germ U _ h a)⁻¹ ∈ localSubring y := by
  have hyU := X.basicOpen_le a hy
  obtain ⟨b, hb⟩ := ((X.mem_basicOpen a y hyU).1 hy).exists_right_inv
  have e := congrArg (algebraMap (X.presheaf.stalk y) X.functionField) hb
  rw [map_mul, map_one, algebraMap_germ hyU h] at e
  exact ⟨left_ne_zero_of_mul_eq_one e, b, eq_inv_of_mul_eq_one_right e⟩
end GlobalTheory.ExtendLineBundle
