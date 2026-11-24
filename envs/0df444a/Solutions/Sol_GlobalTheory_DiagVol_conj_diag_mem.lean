-- Prove2me | solution 1 for GlobalTheory.DiagVol.conj_diag_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:40:43.670925+00:00
-- url     : https://prove2.me/submissions/4e5f1779-a30a-4e06-8b9e-2eca959b5163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagRowUnipotentMemPeriodUnipotentIntegralGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInverseUnipotentVolumeConjDiagonalEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.DiagVol
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.DiagVol
theorem _root_.solution {F : Type} [Field F] (d : n ⊕ Fin c → Fˣ) {x : GL (n ⊕ Fin c) F} (hx : x ∈ symN F n c) :
    diagGL d * x * (diagGL d)⁻¹ ∈ symN F n c := by
  have key : ∀ p, ∀ y ∈ N F n c p, diagGL d * y * (diagGL d)⁻¹ ∈ N F n c p := by
    intro p y hy
    rw [Model.mem_N_iff] at hy ⊢
    intro r s h
    have e : ((diagGL d)⁻¹).val = Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F) := rfl
    rw [Units.val_mul, Units.val_mul, e, diagGL_val, Matrix.mul_diagonal, Matrix.diagonal_mul, hy r s h]
    by_cases hrs : r = s
    · subst hrs; simp
    · simp [Matrix.one_apply_ne hrs]
  have h : symN F n c ≤ (symN F n c).comap (MulAut.conj (diagGL d)).toMonoidHom :=
    sup_le (fun v hv => Subgroup.mem_sup_left (by simpa using key _ v hv))
      fun v hv => Subgroup.mem_sup_right (by simpa using key _ v hv)
  simpa using h hx
end GlobalTheory.DiagVol
