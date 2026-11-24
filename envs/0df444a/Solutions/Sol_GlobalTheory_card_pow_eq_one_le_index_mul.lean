-- Prove2me | solution 1 for GlobalTheory.card_pow_eq_one_le_index_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:53.742801+00:00
-- url     : https://prove2.me/submissions/92705f41-1ac3-4de9-936a-deb3153c708a

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
private lemma card_pow_eq_one_le_of_isCyclic {α : Type*} [Group α] [Finite α] [IsCyclic α] {n : ℕ}
    (hn : 0 < n) : Nat.card {a : α // a ^ n = 1} ≤ n := by
  classical
  let _ := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert IsCyclic.card_pow_eq_one_le (α := α) hn
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G)
    [IsCyclic H] {d : ℕ} (hd : 0 < d) : Nat.card {x : G // x ^ d = 1} ≤ H.index * d := by
  classical

  set K : Subgroup G := (powMonoidHom d : G →* G).ker with hKdef
  have hK : Nat.card {x : G // x ^ d = 1} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp [hKdef]))
  have hsplit := (H.subgroupOf K).card_mul_index
  have hidx : (H.subgroupOf K).index ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.relIndex_dvd_index_of_normal (H := H) (K := K))
  have hsmall : Nat.card (H.subgroupOf K) ≤ d := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : H.subgroupOf K => (⟨⟨(x.1 : G), Subgroup.mem_subgroupOf.mp x.2⟩, ?_⟩ :
        {h : H // h ^ d = 1})) ?_) (card_pow_eq_one_le_of_isCyclic hd)
    · apply Subtype.ext
      have hx : (x.1 : G) ^ d = 1 := x.1.2
      simpa using hx
    · intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg (fun z : {h : H // h ^ d = 1} => ((z.1 : H) : G)) hxy
  rw [hK, ← hsplit]
  calc Nat.card (H.subgroupOf K) * (H.subgroupOf K).index ≤ d * H.index :=
        Nat.mul_le_mul hsmall hidx
    _ = H.index * d := Nat.mul_comm _ _
end GlobalTheory
