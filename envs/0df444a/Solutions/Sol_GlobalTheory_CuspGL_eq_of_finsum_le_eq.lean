-- Prove2me | solution 1 for GlobalTheory.CuspGL.eq_of_finsum_le_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:06:53.810784+00:00
-- url     : https://prove2.me/submissions/d580273e-7177-41fa-844f-37bbf1f509e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspaces

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
theorem _root_.solution {α : Type} [PartialOrder α] [Finite α] (G H : α → ℂ)
    (h : ∀ A : α, ∑ᶠ B : {B : α // B ≤ A}, G B.1 = ∑ᶠ B : {B : α // B ≤ A}, H B.1) (A : α) :
    G A = H A := by
  classical
  induction A using WellFoundedLT.induction with
  | ind A ih =>
    haveI : Fintype {B : α // B ≤ A} := Fintype.ofFinite _
    have h1 := h A
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨A, le_rfl⟩ : {B : α // B ≤ A})),
      ← Finset.add_sum_erase _ (fun B : {B : α // B ≤ A} => H B.1)
        (Finset.mem_univ (⟨A, le_rfl⟩ : {B : α // B ≤ A}))] at h1
    have h2 : ∑ B ∈ Finset.univ.erase (⟨A, le_rfl⟩ : {B : α // B ≤ A}), G B.1 =
        ∑ B ∈ Finset.univ.erase (⟨A, le_rfl⟩ : {B : α // B ≤ A}), H B.1 := by
      refine Finset.sum_congr rfl fun B hB => ih B.1 (lt_of_le_of_ne B.2 fun e => ?_)
      exact (Finset.mem_erase.1 hB).1 (Subtype.ext e)
    rw [h2] at h1
    exact add_right_cancel h1
end GlobalTheory.CuspGL
