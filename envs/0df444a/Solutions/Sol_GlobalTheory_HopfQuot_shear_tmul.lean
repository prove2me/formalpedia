-- Prove2me | solution 1 for GlobalTheory.HopfQuot.shear_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:17.120383+00:00
-- url     : https://prove2.me/submissions/c6e1f22f-c7f8-40d5-9bf4-59c3aaf27ac8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]
namespace GlobalTheory.HopfQuot
theorem _root_.solution (x y : Λ) : shear R Λ (x ⊗ₜ y) = x • Coalgebra.comul (R := R) y := by
  simp [shear, Algebra.smul_def, Algebra.ofId_apply]
end GlobalTheory.HopfQuot
