-- Prove2me | solution 1 for GlobalTheory.GoodCorank.exists_good_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:00:49.575795+00:00
-- url     : https://prove2.me/submissions/eb56bbe2-ba12-46e6-901e-4a37f289c61c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorank
import Theorems.Thm_GlobalTheory_GoodCorank_exists_sat_ker
import Theorems.Thm_GlobalTheory_GoodCorank_good_of_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GoodCorank
variable {C : Type} [Field C] {V : VF C}
variable {d : ℕ} {I J : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.GoodCorank
theorem _root_.solution (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J]
    [DecidableEq I] (G : Cart V d I J) (a : ZMod d) :
    ∃ (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C), (∀ ν, G.Good a (w ν) (x ν)) ∧
      (∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0) ∧ IsSat V w ∧
      (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a).card ≤
        N + (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1).card := by
  have hex : ∀ b c : I, ∃ r : C, r ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b) := fun b c =>
    IsAlgClosed.exists_pow_nat_eq _ V.l_prime.pos
  choose r hr using hex
  obtain ⟨N, w, hs, hP, hφ, hN⟩ := exists_sat_ker (V := V)
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a) r
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1)
  have hp : ∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0 := fun ν c hc => hP ν c (by simpa using hc)
  have hx : ∀ ν, ∃ x, G.Good a (w ν) x := fun ν =>
    good_of_ker G r hr (hs.1 ν) (hp ν) fun b hb => hφ ν b (by simpa using hb)
  choose x hx using hx
  exact ⟨N, w, x, hx, hp, hs, hN⟩
end GlobalTheory.GoodCorank
