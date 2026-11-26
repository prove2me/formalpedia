-- Prove2me | solution 1 for Kyprianou.Ch05.unkilledPassageFinite_iff_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:16:34.213842+00:00
-- url     : https://prove2.me/submissions/26407e70-3251-4667-9888-cfe5fd130f5f

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Classical
theorem solution
    {Omega : Type} (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal) (hDeath : ∀ w, death w = ⊤)
    (x : Real) (w : Omega) (hMono : Monotone (fun t : NNReal => Y t w)) :
    PassageFinite Y death x w ↔ ∃ n : ℕ, 0 < n ∧ x < Y (n : NNReal) w := by
  unfold PassageFinite strictUpcrossing
  simp only [hDeath, WithTop.coe_lt_top, true_and]
  constructor
  · intro h
    have hne : {t : NNReal | 0 < t ∧ x < Y t w}.Nonempty := by
      by_contra hn
      rw [Set.not_nonempty_iff_eq_empty.mp hn, Set.image_empty, sInf_empty] at h
      exact h rfl
    obtain ⟨t, ht, hyt⟩ := hne
    obtain ⟨n, hn⟩ := exists_nat_ge t
    refine ⟨n, ?_, hyt.trans_le (hMono hn)⟩
    by_contra hzero
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hzero
    simp [hn0] at hn
    exact (ne_of_gt ht) hn
  · rintro ⟨n, hn, hy⟩ h
    have hmem : ((n : NNReal) : WithTop NNReal) ∈
        (fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ x < Y t w} :=
      ⟨(n : NNReal), ⟨by exact_mod_cast hn, hy⟩, rfl⟩
    have hle := sInf_le hmem
    rw [h] at hle
    exact (WithTop.not_top_le_coe _ hle)
