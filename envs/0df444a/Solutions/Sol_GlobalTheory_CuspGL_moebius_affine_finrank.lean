-- Prove2me | solution 1 for GlobalTheory.CuspGL.moebius_affine_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:02:56.720368+00:00
-- url     : https://prove2.me/submissions/aae916bf-94c3-4839-83ac-569c5e6d75bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspaces
import Theorems.Thm_GlobalTheory_CuspGL_finsum_le_oneValue_finrank
import Theorems.Thm_GlobalTheory_CuspGL_eq_of_finsum_le_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (G : Submodule K U → ℂ) (c₀ c : ℂ) (hU : 0 < Module.finrank K U)
    (hG : ∀ A : Submodule K U, ∑ᶠ B : {B : Submodule K U // B ≤ A}, G B.1 =
      c₀ + c * (Module.finrank K A : ℂ)) :
    G ⊤ = c * ∏ i ∈ Finset.Ico 1 (Module.finrank K U), (1 - (Nat.card K : ℂ) ^ i) := by
  classical
  haveI : Finite U := Module.finite_of_finite K
  have key := eq_of_finsum_le_eq G
    (fun B => (if B = ⊥ then c₀ else 0) + c * oneValue (Nat.card K) (Module.finrank K B)) (fun A => by
      haveI : Fintype {B : Submodule K U // B ≤ A} := Fintype.ofFinite _
      rw [hG A, ← finsum_le_oneValue_finrank K U A, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_eq_single (⟨⊥, bot_le⟩ : {B : Submodule K U // B ≤ A})]
      · simp
      · intro B _ hB
        exact if_neg fun e => hB (Subtype.ext e)
      · intro h
        exact absurd (Finset.mem_univ _) h) ⊤
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos hU
  rw [key, if_neg top_ne_bot, zero_add, finrank_top, oneValue, if_neg hU.ne']
end GlobalTheory.CuspGL
