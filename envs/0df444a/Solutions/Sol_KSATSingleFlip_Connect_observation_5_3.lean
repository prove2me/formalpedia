-- Prove2me | solution 1 for KSATSingleFlip.Connect.observation_5_3
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:39:15.109208+00:00
-- url     : https://prove2.me/submissions/81370ff1-493f-4081-98e9-05c1c30a1e24

import Definitions.Def_KSATSingleFlip_Connect_Model

open scoped Classical BigOperators
open KSATSingleFlip.Connect

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (Φ : GFormula V) (σ τ : V → Bool) (U : Finset V)
    (hτ : FSat τ Φ) :
    ∀ C ∈ Φ, vbl C ⊆ U → ∀ v ∈ U ∩ disagree σ τ,
      satSet σ C = {v} → ∃ w ∈ U ∩ disagree σ τ, w ≠ v ∧ w ∈ vbl C := by
  intro C hC hsub v hv hforced
  obtain ⟨w, hw⟩ := hτ C hC
  have hwvbl : w ∈ vbl C := by simp [vbl, hw]
  have hvdiff : σ v ≠ τ v := by simpa [disagree] using (Finset.mem_inter.mp hv).2
  have hwne : w ≠ v := by
    intro h
    subst w
    have htrue : C v = some (σ v) := by
      have : v ∈ satSet σ C := by rw [hforced]; simp
      simpa [satSet] using this
    exact hvdiff (Option.some.inj (htrue.symm.trans hw))
  have hwdiff : σ w ≠ τ w := by
    intro h
    have hwsat : w ∈ satSet σ C := by simp [satSet, hw, h]
    rw [hforced] at hwsat
    exact hwne (Finset.mem_singleton.mp hwsat)
  exact ⟨w, by simp [disagree, hsub hwvbl, hwdiff], hwne, hwvbl⟩


#print axioms solution
