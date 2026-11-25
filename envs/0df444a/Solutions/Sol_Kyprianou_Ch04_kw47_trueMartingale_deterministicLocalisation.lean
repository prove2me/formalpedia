-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_trueMartingale_deterministicLocalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:19:46.159292+00:00
-- url     : https://prove2.me/submissions/df858486-2ecd-4472-a4d4-bae398bd6410

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → Real) (hM : Martingale M F P) :
    ∃ stop : Nat → Omega → NNReal,
      (∀ (n : Nat) (t : NNReal), MeasurableSet[(F t)]
        {omega : Omega | stop n omega ≤ t}) ∧
      (∀ᵐ omega : Omega ∂P,
        Tendsto (fun n : Nat => (stop n omega : WithTop NNReal)) atTop (nhds ⊤)) ∧
      (∀ n : Nat, Martingale (fun t omega => M (min t (stop n omega)) omega) F P) := by 
  refine ⟨fun n _ => (n : NNReal), ?_, ?_, ?_⟩
  · intro n t
    by_cases h : (n : NNReal) ≤ t <;> simp [h]
  · apply Filter.Eventually.of_forall
    intro w
    apply tendsto_order.2
    refine ⟨?_, fun a ha => (not_top_lt ha).elim⟩
    intro a ha
    obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt ha)
    obtain ⟨n, hn⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop n] with k hk
    exact_mod_cast hn.trans_le (Nat.cast_le.mpr hk : (n : NNReal) ≤ k)
  · intro n
    refine ⟨?_, ?_⟩
    · intro t
      exact (hM.stronglyAdapted (min t (n : NNReal))).mono (F.mono (min_le_left _ _))
    · intro i j hij
      change P[M (min j (n : NNReal)) | F i] =ᵐ[P] M (min i (n : NNReal))
      by_cases hi : i ≤ (n : NNReal)
      · rw [min_eq_left hi]
        exact hM.condExp_ae_eq (le_min hij hi)
      · have hn : (n : NNReal) ≤ i := le_of_not_ge hi
        rw [min_eq_right hn, min_eq_right (hn.trans hij)]
        rw [condExp_of_stronglyMeasurable (F.le i)
          ((hM.stronglyAdapted (n : NNReal)).mono (F.mono hn)) (hM.integrable _)]
