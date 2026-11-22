-- Prove2me | solution 1 for KadatchJenkins.crcWordN_of_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:01:54.102542+00:00
-- url     : https://prove2.me/submissions/d4680ef1-05a2-4a57-9cf0-31c4d73f346a

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial
namespace KadatchJenkins

theorem crcWordN_of_le (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N : ℕ) (hDW : P.natDegree ≤ W)
    (m v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) (hm : m.degree < (W : WithBot ℕ)) :
    crcWordN P W N m v = ((v * X ^ (W - P.natDegree) + m) * X ^ ((N - 1) * W + P.natDegree)) % P := by
  unfold crcWordN
  congr 1
  obtain ⟨e, rfl⟩ : ∃ e, W = e + P.natDegree := ⟨W - P.natDegree, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

end KadatchJenkins

theorem solution (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N : ℕ) (hDW : P.natDegree ≤ W)
    (m v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) (hm : m.degree < (W : WithBot ℕ)) :
    KadatchJenkins.crcWordN P W N m v = ((v * X ^ (W - P.natDegree) + m) * X ^ ((N - 1) * W + P.natDegree)) % P :=
  KadatchJenkins.crcWordN_of_le P hP W N hDW m v hv hm
