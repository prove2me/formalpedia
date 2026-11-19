-- Prove2me | solution 1 for Kyprianou.Ch01.extendedClockInverseBeforeHorizon
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:04:38.2542+00:00
-- url     : https://prove2.me/submissions/56cdc0b5-3249-43ad-a1c6-55df7dc7fdae

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ENNReal.Basic
set_option autoImplicit false

theorem solution
    (J : NNReal → ENNReal) (hmono : Monotone J)
    (t horizon : NNReal) (ht : t < horizon)
    (hstrict : ∀ s : NNReal, t < s → s < horizon → J t < J s) :
    sInf {s : NNReal | J t < J s} = t := by
  obtain ⟨m, hm1, hm2⟩ := exists_between ht
  have hne : ({s : NNReal | J t < J s} : Set NNReal).Nonempty := ⟨m, hstrict m hm1 hm2⟩
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    rcases lt_or_ge a horizon with h | h
    · exact csInf_le (OrderBot.bddBelow {s : NNReal | J t < J s}) (show a ∈ {s : NNReal | J t < J s} from hstrict a ha h)
    · exact le_trans (csInf_le (OrderBot.bddBelow {s : NNReal | J t < J s}) (show m ∈ {s : NNReal | J t < J s} from hstrict m hm1 hm2)) (le_trans hm2.le h)
  · apply le_csInf hne
    intro s hs
    by_contra hlt0
    have hlt := not_le.mp hlt0
    exact absurd (hmono hlt.le) (not_le.mpr hs)
