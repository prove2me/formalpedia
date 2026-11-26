-- Prove2me | solution 1 for ManyServerQED.Scheduling.continuous_adapted_capped_exit_localization
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:54:34.095824+00:00
-- url     : https://prove2.me/submissions/4ef9e014-5ede-4159-93ae-5e49e16491ee

import Mathlib

open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal

set_option maxHeartbeats 500000 in
theorem solution
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (F : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → E) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (T : ℝ≥0) (r : ℝ) :
    ∃ τ : ℕ → Ω → ℝ≥0,
      (∀ (R : ℕ) (a : ℝ≥0), MeasurableSet[F a] {ω | τ R ω < a}) ∧
      (∀ R ω, τ R ω ≤ T) ∧
      (∀ ω, Monotone (fun R => τ R ω)) ∧
      (∀ ω, ∀ᶠ R in atTop, τ R ω = T) ∧
      (∀ R ω t, t < τ R ω → ‖X t ω‖ ≤ r+R) ∧
      (∀ (R : ℕ) ω, ‖X 0 ω‖ ≤ r+R → ‖X (τ R ω) ω‖ ≤ r+R) := by
  classical
  let S (R : ℕ) (ω : Ω) : Set ℝ≥0 := {T} ∪ {t | t ≤ T ∧ r+R < ‖X t ω‖}
  let τ (R : ℕ) (ω : Ω) := sInf (S R ω)
  have hB (R : ℕ) (ω : Ω) : BddBelow (S R ω) := ⟨0,fun _ _ => zero_le⟩
  have hT (R : ℕ) (ω : Ω) : T ∈ S R ω := Or.inl rfl
  have hE (R : ℕ) (ω : Ω) : (S R ω).Nonempty := ⟨T,hT R ω⟩
  have hτle (R : ℕ) (ω : Ω) : τ R ω ≤ T := csInf_le (hB R ω) (hT R ω)
  have hpre (R : ℕ) (ω : Ω) (t : ℝ≥0) (ht : t < τ R ω) : ‖X t ω‖ ≤ r+R := by
    by_contra! hh
    exact (not_le_of_gt ht) (csInf_le (hB R ω) (Or.inr ⟨ht.le.trans (hτle R ω),hh⟩))
  refine ⟨τ,?_,hτle,?_,?_,hpre,?_⟩
  · intro R a
    obtain ⟨D,hDc,hDense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
    have he : {ω | τ R ω < a} =
        (if T < a then univ else ∅) ∪ ⋃ q ∈ D, if q < a ∧ q < T then
          {ω | r+R < ‖X q ω‖} else ∅ := by
      ext ω
      rcases lt_or_ge T a with hTa | hTa
      · simp [hTa,(hτle R ω).trans_lt hTa]
      simp only [not_lt_of_ge hTa, if_false, empty_union, mem_iUnion, mem_preimage, mem_Iio]
      constructor
      · intro hω
        obtain ⟨t,ht,hta⟩ := (csInf_lt_iff (hB R ω) (hE R ω)).1 hω
        rcases ht with ht | ⟨ht,hx⟩
        · exact False.elim (not_lt_of_ge hTa (show T < a from ht ▸ hta))
        have htT := hta.trans_le hTa
        let U := Iio a ∩ Iio T ∩ {t | r+R < ‖X t ω‖}
        have hU : IsOpen U :=
          (isOpen_Iio.inter isOpen_Iio).inter (isOpen_lt continuous_const (hc ω).norm)
        obtain ⟨q,hqU,hqD⟩ := hDense.inter_open_nonempty U hU ⟨t,⟨⟨hta,htT⟩,hx⟩⟩
        change (q < a ∧ q < T) ∧ r+R < ‖X q ω‖ at hqU
        exact ⟨q,hqD,by simp only [if_pos hqU.1,mem_setOf_eq]; exact hqU.2⟩
      · rintro ⟨q,_,hq⟩
        split_ifs at hq with h
        · exact (csInf_le (hB R ω) (Or.inr ⟨h.2.le,hq⟩)).trans_lt h.1
        · exact False.elim hq
    rw [he]
    apply MeasurableSet.union
    · split_ifs <;> simp
    · apply MeasurableSet.biUnion hDc
      intro q hq
      split_ifs with hq'
      · have h := (hm q).mono (F.mono hq'.1.le) le_rfl
        letI : MeasurableSpace Ω := F a
        exact measurableSet_lt measurable_const h.norm
      · exact @MeasurableSet.empty Ω (F a)
  · intro ω i j hij
    apply csInf_le_csInf (hB i ω) (hE j ω)
    intro u hu
    rcases hu with hu | ⟨h1,h2⟩
    · exact Or.inl hu
    · have hcast : (i:ℝ) ≤ j := by exact_mod_cast hij
      exact Or.inr ⟨h1,(add_le_add_right hcast r).trans_lt h2⟩
  · intro ω
    obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc ω).continuousOn
      (s := Icc (0:ℝ≥0) T)
    obtain ⟨N,hN⟩ := exists_nat_ge (A-r)
    filter_upwards [eventually_ge_atTop N] with R hR
    have hRA : A ≤ r+R := by
      have hrN : (N:ℝ) ≤ R := by exact_mod_cast hR
      linarith
    have hSet : S R ω = {T} := by
      ext u
      constructor
      · rintro (hu | h)
        · exact hu
        · exact False.elim (not_lt_of_ge ((hA u ⟨zero_le,h.1⟩).trans hRA) h.2)
      · exact Or.inl
    simp [τ,hSet]
  · intro R ω h0
    by_cases hτ0 : τ R ω = 0
    · simpa [hτ0] using h0
    have hC : IsClosed {t : ℝ≥0 | ‖X t ω‖ ≤ r+R} :=
      isClosed_le (hc ω).norm continuous_const
    have hSub : Iio (τ R ω) ⊆ {t : ℝ≥0 | ‖X t ω‖ ≤ r+R} := hpre R ω
    have hcl := closure_minimal hSub hC
    exact hcl (by rw [closure_Iio' ⟨0, pos_iff_ne_zero.mpr hτ0⟩]; exact self_mem_Iic)
