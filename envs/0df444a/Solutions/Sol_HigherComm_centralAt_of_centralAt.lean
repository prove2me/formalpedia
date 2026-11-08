-- Prove2me | solution 1 for HigherComm.centralAt_of_centralAt
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T07:32:21.886233+00:00
-- url     : https://prove2.me/submissions/8674c561-3bea-4b7a-9b6a-ea77aad10508

import Definitions.Def_HigherComm_defs
import Theorems.Thm_HigherComm_shift_rotation

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language

namespace HigherComm

theorem coc_main {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M] {n k : ℕ}
    (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (δ : Congruence (L := L) M)
    (l : Fin (k + 2)) (hl : CentralAt T l δ) (i : Fin (k + 2)) : CentralAt T i δ := by
  by_cases hil : i = l
  · subst hil; exact hl
  obtain ⟨R, hR⟩ := shift_rotation m hm T i l hil
  intro h hh hS
  obtain ⟨hmem, -, h2, h3⟩ := hR h hh
  have hL : LineRel δ h i (Function.update (fun _ => true) l false) :=
    hS _ ⟨l, Ne.symm hil, by simp⟩
  exact (h3 δ hL).mpr (fun e => hl _ (hmem e) (h2 δ hS e))

end HigherComm

theorem solution {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M] {n k : ℕ}
    (m : Fin (n + 1) → L.Term (Fin 4)) (hm : HigherComm.IsDayTerms M m)
    (T : Fin (k + 2) → HigherComm.Congruence (L := L) M) (δ : HigherComm.Congruence (L := L) M)
    (l : Fin (k + 2)) (hl : HigherComm.CentralAt T l δ) (i : Fin (k + 2)) :
    HigherComm.CentralAt T i δ :=
  HigherComm.coc_main m hm T δ l hl i
