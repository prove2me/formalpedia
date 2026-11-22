-- Prove2me | solution 1 for KadatchJenkins.crc0_word_of_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:03:06.775389+00:00
-- url     : https://prove2.me/submissions/73449df7-cfe7-4002-b31e-87511e345981

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial
namespace KadatchJenkins

theorem AuxC0_polydeg (M : Message) : M.poly.degree < (M.length : WithBot ℕ) := by
  rw [← Polynomial.mem_degreeLT]
  unfold Message.poly
  refine Submodule.sum_mem _ (fun k _ => ?_)
  rw [Polynomial.mem_degreeLT]
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  have := k.2
  exact_mod_cast (by omega : M.length - 1 - (k : ℕ) < M.length)

theorem crc0_word_of_le (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W : ℕ) (hDW : P.natDegree ≤ W)
    (M : Message) (hM : M.length = W) (v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) :
    crc0 P M v = ((v * X ^ (W - P.natDegree) + M.poly) * X ^ P.natDegree) % P ∧
      (v * X ^ (W - P.natDegree) + M.poly).degree < (W : WithBot ℕ) := by
  refine ⟨?_, ?_⟩
  · unfold crc0
    congr 1
    obtain ⟨e, rfl⟩ : ∃ e, W = e + P.natDegree := ⟨W - P.natDegree, by omega⟩
    rw [hM, Nat.add_sub_cancel]
    ring
  · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (degree_mul_le _ _) ?_
      refine lt_of_le_of_lt (add_le_add_right (degree_X_pow_le _) _) ?_
      have hW : (W : WithBot ℕ) = (P.natDegree : WithBot ℕ) + ((W - P.natDegree : ℕ) : WithBot ℕ) := by
        exact_mod_cast (by omega : W = P.natDegree + (W - P.natDegree))
      rw [hW]
      exact WithBot.add_lt_add_right (WithBot.coe_ne_bot) hv
    · have := AuxC0_polydeg M; rw [hM] at this; exact this

end KadatchJenkins

theorem solution (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W : ℕ) (hDW : P.natDegree ≤ W)
    (M : KadatchJenkins.Message) (hM : M.length = W) (v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) :
    KadatchJenkins.crc0 P M v = ((v * X ^ (W - P.natDegree) + M.poly) * X ^ P.natDegree) % P ∧
      (v * X ^ (W - P.natDegree) + M.poly).degree < (W : WithBot ℕ) :=
  KadatchJenkins.crc0_word_of_le P hP W hDW M hM v hv
