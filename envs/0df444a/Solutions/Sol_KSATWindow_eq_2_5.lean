-- Prove2me | solution 1 for KSATWindow.eq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:48:40.657204+00:00
-- url     : https://prove2.me/submissions/1492e47e-471f-4f4e-8fae-21fd23428651

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_KSATWindow_Forcing
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

open KSATWindow in
theorem solution (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    ∀ j : ℕ, 1 ≤ j → j ≤ k → rho n j S = killRatio n (forcedCount S) j := by
  intro j _ _
  obtain ⟨a₀, ha₀⟩ := hS
  have hnum : (Finset.univ.filter fun c : Clause n j => Kills S c).card
      = (forcedCount S).choose j := by
    rw [← Fintype.card_subtype, Fintype.card_congr (killingEquiv (k := j) ha₀),
      Fintype.card_subtype]
    have : (Finset.univ.filter fun s : Finset (Fin n) => s ⊆ frozen S ∧ s.card = j)
        = Finset.powersetCard j (frozen S) := by
      ext s
      simp [Finset.mem_powersetCard]
    rw [this, Finset.card_powersetCard]
    rfl
  have hden : Fintype.card (Clause n j) = n.choose j * 2 ^ j := by
    have e : Fintype.card (Clause n j)
        = Fintype.card ((s : {s : Finset (Fin n) // s.card = j}) × (s.1 → Bool)) :=
      Fintype.card_congr (Equiv.refl _)
    rw [e, Fintype.card_sigma]
    have h2 : ∀ s : {s : Finset (Fin n) // s.card = j}, Fintype.card (s.1 → Bool) = 2 ^ j :=
      fun s => by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, s.2]
    rw [Finset.sum_congr rfl fun s _ => h2 s, Finset.sum_const, Finset.card_univ,
      Fintype.card_finset_len, Fintype.card_fin, smul_eq_mul]
  unfold rho killRatio
  rw [hnum, hden]
  push_cast
  ring
