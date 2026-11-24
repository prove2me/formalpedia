-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.qminor_swap_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:07:13.053643+00:00
-- url     : https://prove2.me/submissions/2c240643-ca49-47c2-afdf-68995f597a80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_prod_ofFn_adjacent
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_two_rel
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_eq_zero_of_eq_neg

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
theorem _root_.solution {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) (i : Fin m) :
    qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u = - qminor E a b u := by
  rw [← add_eq_zero_iff_eq_neg]
  set s := Equiv.swap i.castSucc i.succ with hs
  let G : Equiv.Perm (Fin (m + 1)) → A := fun σ =>
    (List.ofFn fun k : Fin (m + 1) => Tm E (u - (k : ℂ)) (a (σ k)) (b (s k))).prod +
    (List.ofFn fun k : Fin (m + 1) => Tm E (u - (k : ℂ)) (a (σ k)) (b k)).prod
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  have hG : ∀ σ, G σ = G (σ * s) := by
    intro σ
    apply prod_ofFn_adjacent m i
    · intro k h1 h2
      simp [hs, Equiv.swap_apply_of_ne_of_ne h1 h2]
    · have hu : u - ((i.castSucc : ℕ) : ℂ) = (u - ((i.succ : ℕ) : ℂ)) + 1 := by
        simp only [Fin.val_castSucc, Fin.val_succ]; push_cast; ring
      simp only [hs, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, hu]
      exact two_rel E hE _ _ _ _ _
  have h1 : qminor E a (b ∘ s) u + qminor E a b u =
      ∑ σ : Equiv.Perm (Fin (m + 1)), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) * G σ := by
    simp only [qminor, G, mul_add, Finset.sum_add_distrib, Function.comp]
  rw [h1]
  apply eq_zero_of_eq_neg
  rw [← Finset.sum_neg_distrib]
  refine (Equiv.sum_comp (Equiv.mulRight s) _).symm.trans (Finset.sum_congr rfl fun σ _ => ?_)
  simp only [Equiv.coe_mulRight, ← hG]
  simp [hs, Equiv.Perm.sign_swap hne]
end GlobalTheory.QuantumMinorAdjacentSwap
