-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.qminor_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:18.425829+00:00
-- url     : https://prove2.me/submissions/fcbf98d7-84c6-4f4d-8135-5a2bb9c4d584

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_qminor_swap_adjacent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
open Formalism.REAL
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution {n t : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a : Fin t → Fin n) (u : ℂ) (τ : Equiv.Perm (Fin t)) (b : Fin t → Fin n) :
    qminor E a (b ∘ τ) u = (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) • qminor E a b u := by
  cases t with
  | zero =>
    rw [Subsingleton.elim τ 1]; simp
  | succ m =>
    have hτ : τ ∈ Submonoid.closure
        (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hτ using Submonoid.closure_induction generalizing b with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
      rw [qminor_swap_adjacent E hE]
      simp [Equiv.Perm.sign_swap hne]
    | one => simp
    | mul x y _ _ hx hy =>
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy, hx, smul_smul]
      simp [mul_comm]
end GlobalTheory.QuantumMinorAdjacentSwap
