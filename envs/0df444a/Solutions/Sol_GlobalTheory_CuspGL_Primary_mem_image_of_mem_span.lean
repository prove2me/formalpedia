-- Prove2me | solution 1 for GlobalTheory.CuspGL.Primary.mem_image_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:04.286303+00:00
-- url     : https://prove2.me/submissions/965bb530-4a61-444a-8dd2-7293eb20bd56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEq
import Theorems.Thm_GlobalTheory_CuspGL_Primary_aeval_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.Primary
namespace GlobalTheory.CuspGL.Primary
theorem _root_.solution {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V)
    (f : F[X]) {t : ℕ} (π : V →ₗ[F] (Fin t → AdjoinRoot f)) (hπ : ∀ v, π (g v) = AdjoinRoot.root f • π v)
    (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (y : Fin t → AdjoinRoot f)
    (hy : y ∈ Submodule.span (AdjoinRoot f) (π '' W)) : ∃ w ∈ W, π w = y := by
  have key : ∀ (p : F[X]) (v : V), π (aeval g p v) = AdjoinRoot.mk f p • π v := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      intro v
      rw [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, algebraMap_smul]
      simp
    | add p q hp hq => intro v; simp [hp, hq, add_smul]
    | monomial n a h =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, aeval_X, h, hπ, map_mul (AdjoinRoot.mk f) _ X,
        AdjoinRoot.mk_X, smul_smul]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, W.zero_mem, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    exact ⟨w + w', W.add_mem hw hw', map_add _ _ _⟩
  | smul k x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective k
    exact ⟨_, aeval_mem g W hW p w hw, key p w⟩
end GlobalTheory.CuspGL.Primary
