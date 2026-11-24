-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.exists_iInf_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:29:55.092433+00:00
-- url     : https://prove2.me/submissions/cf9bd947-2408-4c7c-b958-1237b6aa0b6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
import Theorems.Thm_GlobalTheory_CoeffSubring_pow_mem_level
import Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_sub_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_level_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}
namespace GlobalTheory.CoeffSubring
theorem _root_.solution [IsAdicComplete (maximalIdeal S) S] (h0 : (p : S) ∈ maximalIdeal S)
    (hs : ∀ n s, ∃ t ∈ level p L n, s - t ∈ maximalIdeal S) (s : S) :
    ∃ a ∈ ⨅ n, level p L n, s - a ∈ maximalIdeal S := by
  choose F hF hF' using fun n (t : level p L n) => exists_level_succ h0 hs n t.2
  let u : ∀ n, level p L n := fun n =>
    Nat.rec (motive := fun n => level p L n) ⟨s, by simpa using pow_mem_level (p := p) (L := L) 0 s⟩
      (fun n t => ⟨F n t, hF n t⟩) n
  have hu : ∀ n : ℕ, (u n).1 - (u (n + 1)).1 ∈ maximalIdeal S ^ (n + 1) :=
    fun n => hF' n (u n)
  have hc : AdicCompletion.IsAdicCauchy (maximalIdeal S) S fun n => (u n).1 := by
    rw [AdicCompletion.isAdicCauchy_iff]
    exact fun n => SModEq.sub_mem.2 (by simpa using Ideal.pow_le_pow_right n.le_succ (hu n))
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' (I := maximalIdeal S) (fun n => (u n).1) hc
  have ha' : ∀ n, a - (u n).1 ∈ maximalIdeal S ^ (n + 1) := fun n => by
    have h1 : (u (n + 1)).1 - a ∈ maximalIdeal S ^ (n + 1) := by
      simpa using SModEq.sub_mem.1 (ha (n + 1))
    have := neg_mem (add_mem (hu n) h1)
    convert this using 1
    ring
  refine ⟨a, Subring.mem_iInf.2 fun n => mem_level_of_sub_mem (u n).2 (ha' n), ?_⟩
  have : a - s ∈ maximalIdeal S ^ (0 + 1) := ha' 0
  simpa using neg_mem this
end GlobalTheory.CoeffSubring
