-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.eq_of_prod_bottomRows_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:24:42.225983+00:00
-- url     : https://prove2.me/submissions/bf1d61eb-1748-4a01-a024-03d8e51d4db7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_prod_bottomRows_eq_prodFrom
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_prodFrom_eq_mul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_prodFrom_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_prodFrom_of_le
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {t t' : Fin n → Fˣ}
    (h : ∀ k : Fin n, ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) =
      ∏ a : Fin (k.val + 1), (t' (bottomRows k a) : F)) : t = t' := by
  have hall : ∀ s, prodFrom t s = prodFrom (F := F) t' s := by
    intro s
    by_cases hs : s < n
    · have := h ⟨n - 1 - s, by omega⟩
      rw [prod_bottomRows_eq_prodFrom, prod_bottomRows_eq_prodFrom] at this
      have e : n - (n - 1 - s + 1) = s := by omega
      simpa only [e] using this
    · rw [prodFrom_of_le t (by omega), prodFrom_of_le t' (by omega)]
  funext x
  have h1 := prodFrom_eq_mul (F := F) t x
  have h2 := prodFrom_eq_mul (F := F) t' x
  rw [hall, h2, hall (x.val + 1)] at h1
  exact Units.ext (mul_right_cancel₀ (prodFrom_ne_zero t' _) h1.symm)
end GroundTheory.Automorphic.Whittaker
