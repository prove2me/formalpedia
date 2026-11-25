-- Prove2me | solution 1 for GlobalTheory.DualCokernel.d_d_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:50.220244+00:00
-- url     : https://prove2.me/submissions/8ec5e09d-5697-4611-8768-fe7100cf8bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
namespace GlobalTheory.DualCokernel
theorem _root_.solution (i j k : ℕ) (x : C.X i) : (C.d j k).hom ((C.d i j).hom x) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, C.d_comp_d]
  rfl
end GlobalTheory.DualCokernel
