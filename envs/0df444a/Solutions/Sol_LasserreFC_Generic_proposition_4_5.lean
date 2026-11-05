-- Prove2me | solution 1 for LasserreFC.Generic.proposition_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:45:14.317167+00:00
-- url     : https://prove2.me/submissions/312299ba-a62b-4633-9ea8-c27ea9321f6e

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting
import Definitions.Def_LasserreFC_Generic_Cond43
import Theorems.Thm_LasserreFC_Generic_proposition_4_4
import Theorems.Thm_LasserreFC_Generic_lemma_4_6
import Theorems.Thm_LasserreFC_Generic_kkt_first_order

open MvPolynomial LasserreFC.Generic in
theorem solution {n m1 m2 : ℕ} (hm1 : m1 ≤ n) (P : POP n m1 m2) (d0 : ℕ)
    (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) (hadm : P.Admissible d0 d d')
    (hC : Cond43 P d0 d d') :
    ∀ u ∈ P.K, IsLocalMinOn (fun x => eval x P.f) P.K u → OptCond P u := by
  intro u hu hmin
  obtain ⟨ha, hb, hc, hd⟩ := hC
  -- CQC: Proposition 4.4 ii) only involves `h` and `g`; apply it with objective `0`.
  let P' : POP n m1 m2 := ⟨0, P.h, P.g⟩
  have hadm' : P'.Admissible d0 d d' := ⟨by simp [P'], hadm.2.1, hadm.2.2⟩
  have hcq : CQC P u := by
    have h13 : grad P'.f u = ∑ i, (0 : Fin m1 → ℝ) i • grad (P'.h i) u +
        ∑ j, (0 : Fin m2 → ℝ) j • grad (P'.g j) u := by
      funext k; simp [P', grad]
    exact (proposition_4_4 hm1 P' d0 d d' hadm' u hu 0 0 h13 (fun j => by simp)).2.1 ha hb
  obtain ⟨lam, mu, hkkt⟩ := kkt_first_order P u hu hmin hcq
  have h44 := proposition_4_4 hm1 P d0 d d' hadm u hu lam mu hkkt.1 hkkt.2.1
  refine ⟨hcq, lam, mu, hkkt, ?_, ?_⟩
  · intro j
    have hg := hu.2 j
    by_cases hj : eval u (P.g j) = 0
    · have hmu := (h44.2.2.1 ha hc).2 j hj
      have := hkkt.2.2 j
      rw [hj]
      exact lt_of_le_of_ne (by simpa using this) (Ne.symm (by simpa using hmu))
    · have := hkkt.2.2 j
      have : 0 < eval u (P.g j) := lt_of_le_of_ne hg (Ne.symm hj)
      linarith [hkkt.2.2 j]
  · exact (lemma_4_6 P u hu hmin lam mu hkkt hcq).mpr (h44.2.2.2 ha hd)
