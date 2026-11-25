-- Prove2me | solution 1 for GlobalTheory.DualCokernel.extZero_coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:02.617011+00:00
-- url     : https://prove2.me/submissions/d53379b5-d237-4129-903f-b502752dd527

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
variable [IsLocalRing R]
namespace GlobalTheory.DualCokernel
theorem _root_.solution {X F : Type} [AddCommGroup X] [Module R X] [AddCommGroup F] [Module R F]
    {Y : Type} [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] F) (q : F →ₗ[R] Y) (hf : Injective f)
    (hq : Surjective q) (hex : Exact f q) (n : ℕ) (hX : ExtZero (R := R) X (n + 1))
    (hF : ExtZero (R := R) F n) : ExtZero (R := R) Y n := by
  have hS : (ModuleCat.shortComplexOfCompEqZero f q hex.linearMap_comp_eq_zero).ShortExact :=
    ModuleCat.shortComplex_shortExact _ hex hf hq
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x rfl (@Subsingleton.elim _ hX _ _)
  rw [@Subsingleton.elim _ hF y 0]
  exact Ext.zero_comp _ _ _ _ _
end GlobalTheory.DualCokernel
