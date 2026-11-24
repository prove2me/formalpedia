-- Prove2me | solution 1 for GlobalTheory.exact_lTensor_iff_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:04.389795+00:00
-- url     : https://prove2.me/submissions/4f406832-f349-49bd-8d4f-a15e6b74332a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
namespace GlobalTheory
theorem _root_.solution (k L : Type*) [CommRing k] [CommRing L] [Algebra R k]
    [Algebra R L] [Algebra k L] [IsScalarTower R k L] [Module.FaithfullyFlat k L]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔ Exact (f.lTensor k) (g.lTensor k) := by
  have h1 := Module.FaithfullyFlat.lTensor_exact_iff_exact k L (f.baseChange k) (g.baseChange k)
  have h2 : Exact (AlgebraTensorModule.lTensor k L f) (AlgebraTensorModule.lTensor k L g) ↔
      Exact ((f.baseChange k).lTensor L) ((g.baseChange k).lTensor L) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R k k L A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R k k L B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R k k L C)
      (by ext; simp) (by ext; simp)
  exact h2.trans h1
end GlobalTheory
