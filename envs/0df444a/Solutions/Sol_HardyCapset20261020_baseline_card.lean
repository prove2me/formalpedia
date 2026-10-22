-- Prove2me | solution 1 for HardyCapset20261020.baseline_card
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T13:47:18.300826+00:00
-- url     : https://prove2.me/submissions/91cfe64e-e383-466b-a4ae-4aac11ee1b74

import Definitions.Def_HardyCapsetModel20261020
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain
import Mathlib.Tactic.NormNum
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option autoImplicit false

open HardyCapset20261020

theorem decode_injective_on_range (q r : ℕ) (hq : q < 6561) (hr : r < 6561)
    (h : decode q = decode r) : q = r := by
  have h0 := congrArg (fun p : Point => (p 0).val) h
  have h1 := congrArg (fun p : Point => (p 1).val) h
  have h2 := congrArg (fun p : Point => (p 2).val) h
  have h3 := congrArg (fun p : Point => (p 3).val) h
  have h4 := congrArg (fun p : Point => (p 4).val) h
  have h5 := congrArg (fun p : Point => (p 5).val) h
  have h6 := congrArg (fun p : Point => (p 6).val) h
  have h7 := congrArg (fun p : Point => (p 7).val) h
  norm_num [decode, ZMod.val_natCast] at h0 h1 h2 h3 h4 h5 h6 h7
  omega

theorem ids_nodup : baselineIds.Nodup := by
  have hs : List.IsChain (· < ·) baselineIds := by decide
  have hp : List.Pairwise (· < ·) baselineIds := List.isChain_iff_pairwise.mp hs
  exact hp.imp (fun h => Nat.ne_of_lt h)
theorem ids_range : baselineIds.all (fun q => q < 6561) = true := by decide

theorem solution : baseline.card = 512 := by
  have hrange : ∀ q ∈ baselineIds, q < 6561 := by
    simpa using (List.all_eq_true.mp ids_range)
  have hn : (baselineIds.map decode).Nodup := ids_nodup.map_on (by
    intro q hq r hr he
    exact decode_injective_on_range q r (hrange q hq) (hrange r hr) he)
  rw [baseline, List.toFinset_card_of_nodup hn, List.length_map]
  decide

#print axioms solution
