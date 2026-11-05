-- Prove2me | solution 1 for JSQHalfinWhitt.Tightness.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:07:29.161797+00:00
-- url     : https://prove2.me/submissions/de9a7440-ccd9-45e7-b71c-6a9c03f5da34

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_JSQHalfinWhitt_Tightness_Model

namespace JSQHalfinWhitt.Tightness

open scoped Classical

section Abstract

variable {S ι : Type*}

/-- Abstract basic adjoint relation for a chain with finitely many transitions out of each state
and bounded total rate. -/
theorem bar_abstract (π : S → ℝ) (hπ0 : ∀ q, 0 ≤ π q)
    (T : S → Finset ι) (r : S → ι → ℝ) (y : S → ι → S) (hr : ∀ q t, 0 ≤ r q t)
    (M : ℝ) (hM : ∀ q, ∑ t ∈ T q, r q t ≤ M)
    (G : (S → ℝ) → S → ℝ)
    (hG : ∀ f q, G f q = ∑ t ∈ T q, r q t * (f (y q t) - f q))
    (hbal : ∀ q', Summable (fun q => π q * G (indicatorState q') q) ∧
      ∑' q, π q * G (indicatorState q') q = 0)
    (f : S → ℝ) (hf : Summable fun q => π q * |f q|) :
    Summable (fun q => π q * G f q) ∧ ∑' q, π q * G f q = 0 := by
  set R : S → ℝ := fun q => ∑ t ∈ T q, r q t with hRdef
  set A : (S → ℝ) → S → ℝ := fun h q => ∑ t ∈ T q, r q t * h (y q t) with hAdef
  have hR0 : ∀ q, 0 ≤ R q := fun q => Finset.sum_nonneg (fun t _ => hr q t)
  have hG' : ∀ h q, G h q = A h q - R q * h q := by
    intro h q
    rw [hG, hAdef, hRdef]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  -- inflow
  have hind : ∀ q' q, π q * A (indicatorState q') q =
      π q * G (indicatorState q') q + (if q = q' then π q' * R q' else 0) := by
    intro q' q
    rw [hG']
    by_cases h : q = q'
    · subst h; simp [indicatorState]; ring
    · simp [indicatorState, h]
  have hinflow : ∀ q', Summable (fun q => π q * A (indicatorState q') q) ∧
      ∑' q, π q * A (indicatorState q') q = π q' * R q' := by
    intro q'
    have h1 := (hbal q').1
    have h2 : Summable (fun q => if q = q' then π q' * R q' else 0) :=
      summable_of_ne_finset_zero (s := {q'}) (fun b hb => by
        simp at hb; simp [hb])
    refine ⟨?_, ?_⟩
    · simp_rw [hind]; exact h1.add h2
    · simp_rw [hind]
      rw [h1.tsum_add h2, (hbal q').2, tsum_ite_eq]; ring
  have hAnn : ∀ q' q, 0 ≤ A (indicatorState q') q := by
    intro q' q
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (hr q t) (by
      unfold indicatorState; split_ifs <;> norm_num))
  -- per-q finite sum
  have hfin : ∀ (h : S → ℝ) q, HasSum (fun q' => h q' * (π q * A (indicatorState q') q))
      (π q * A h q) := by
    intro h q
    have : ∀ q', h q' * (π q * A (indicatorState q') q) =
        ∑ t ∈ T q, (if q' = y q t then π q * r q t * h (y q t) else 0) := by
      intro q'
      simp only [hAdef, indicatorState, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      by_cases hh : q' = y q t
      · subst hh; simp; ring
      · have : y q t ≠ q' := fun e => hh e.symm
        simp [hh, this]
    simp_rw [this]
    have : π q * A h q = ∑ t ∈ T q, π q * r q t * h (y q t) := by
      simp only [hAdef, Finset.mul_sum]; refine Finset.sum_congr rfl (fun t _ => by ring)
    rw [this]
    exact hasSum_sum (fun t _ => hasSum_ite_eq (y q t) (π q * r q t * h (y q t)))
  -- key identity for nonnegative h
  have hkey : ∀ h : S → ℝ, (∀ q, 0 ≤ h q) → Summable (fun q => π q * h q) →
      Summable (fun q => π q * A h q) ∧ Summable (fun q => π q * R q * h q) ∧
      ∑' q, π q * A h q = ∑' q, π q * R q * h q := by
    intro h hh0 hhs
    have hRh : Summable (fun q => π q * R q * h q) := by
      refine Summable.of_nonneg_of_le (fun q => mul_nonneg (mul_nonneg (hπ0 q) (hR0 q)) (hh0 q))
        (fun q => ?_) (hhs.mul_left M)
      have : π q * R q * h q = R q * (π q * h q) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hM q) (mul_nonneg (hπ0 q) (hh0 q))
    set F : S × S → ℝ := fun p => h p.1 * (π p.2 * A (indicatorState p.1) p.2) with hF
    have hF0 : 0 ≤ F := fun p => mul_nonneg (hh0 _) (mul_nonneg (hπ0 _) (hAnn _ _))
    have hrow : ∀ q', HasSum (fun q => F (q', q)) (h q' * (π q' * R q')) := by
      intro q'
      have := ((hinflow q').1.hasSum).mul_left (h q')
      rw [(hinflow q').2] at this
      exact this
    have hFs : Summable F := by
      rw [summable_prod_of_nonneg hF0]
      refine ⟨fun q' => (hrow q').summable, ?_⟩
      simp_rw [(hrow _).tsum_eq]
      refine hRh.congr (fun q => by ring)
    have hFs' : Summable (F ∘ Prod.swap) := hFs.prod_symm
    have hcol : Summable (fun q => π q * A h q) := by
      have := hFs'.prod
      refine this.congr (fun q => ?_)
      exact (hfin h q).tsum_eq
    refine ⟨hcol, hRh, ?_⟩
    have hc := hFs.tsum_comm (f := fun q' q => F (q', q))
    have e1 : ∀ q, ∑' q', F (q', q) = π q * A h q := fun q => (hfin h q).tsum_eq
    have e2 : ∀ q', ∑' q, F (q', q) = π q' * R q' * h q' := fun q' => by
      rw [(hrow q').tsum_eq]; ring
    simp only [e1, e2] at hc
    exact hc
  -- signed f
  set fp : S → ℝ := fun q => max (f q) 0
  set fm : S → ℝ := fun q => max (-f q) 0
  have hfp0 : ∀ q, 0 ≤ fp q := fun q => le_max_right _ _
  have hfm0 : ∀ q, 0 ≤ fm q := fun q => le_max_right _ _
  have hfpm : ∀ q, f q = fp q - fm q := by
    intro q; simp only [fp, fm]
    rcases le_total 0 (f q) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hfps : Summable (fun q => π q * fp q) := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (hπ0 q) (hfp0 q)) (fun q => ?_) hf
    refine mul_le_mul_of_nonneg_left ?_ (hπ0 q)
    simp only [fp]; exact max_le (le_abs_self _) (abs_nonneg _)
  have hfms : Summable (fun q => π q * fm q) := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (hπ0 q) (hfm0 q)) (fun q => ?_) hf
    refine mul_le_mul_of_nonneg_left ?_ (hπ0 q)
    simp only [fm]; exact max_le (neg_le_abs _) (abs_nonneg _)
  obtain ⟨p1, p2, p3⟩ := hkey fp hfp0 hfps
  obtain ⟨m1, m2, m3⟩ := hkey fm hfm0 hfms
  have hGf : ∀ q, π q * G f q =
      (π q * A fp q - π q * R q * fp q) - (π q * A fm q - π q * R q * fm q) := by
    intro q
    rw [hG']
    have : A f q = A fp q - A fm q := by
      simp only [hAdef, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [hfpm (y q t)]; ring
    rw [this, hfpm q]; ring
  simp_rw [hGf]
  refine ⟨(p1.sub p2).sub (m1.sub m2), ?_⟩
  rw [(p1.sub p2).tsum_sub (m1.sub m2), p1.tsum_sub p2, m1.tsum_sub m2, p3, m3]
  ring

end Abstract

section JSQ

variable {n : ℕ}

/-- an index beyond which all coordinates vanish -/
noncomputable def cut (q : State n) : ℕ := Classical.choose q.2.2.2 + 1

lemma cut_spec (q : State n) : ∀ i, cut q ≤ i + 1 → q.1 i = 0 := by
  intro i hi
  exact Classical.choose_spec q.2.2.2 i (by unfold cut at hi; omega)

lemma not_arrives_of_ge (hn : 1 ≤ n) (q : State n) (i : ℕ) (hi : cut q ≤ i) :
    ¬ ArrivesAt q i := by
  rintro ⟨h1, _⟩
  have := h1 (cut q - 1) (by unfold cut at hi ⊢; omega)
  rw [cut_spec q (cut q - 1) (by unfold cut; omega)] at this
  omega

lemma dep_rate_zero (q : State n) (i : ℕ) (hi : cut q ≤ i) :
    ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) = 0 := by
  rw [cut_spec q i (by omega), cut_spec q (i + 1) (by omega)]; simp

lemma dep_rate_nonneg (q : State n) (i : ℕ) : 0 ≤ ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) := by
  have := q.2.2.1 (Nat.le_succ i)
  have : ((q.1 (i+1) : ℕ) : ℝ) ≤ (q.1 i : ℝ) := by exact_mod_cast this
  linarith

lemma arrives_unique (q : State n) (i j : ℕ) (hi : ArrivesAt q i) (hj : ArrivesAt q j) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hj.1 i h; have := hi.2; omega
  · exact h
  · have := hi.1 j h; have := hj.2; omega

lemma sum_arr_le (q : State n) (c : ℝ) (hc : 0 ≤ c) (s : Finset ℕ) :
    ∑ i ∈ s, (if ArrivesAt q i then c else 0) ≤ c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have : (s.filter (fun i => ArrivesAt q i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact arrives_unique q a b ha.2 hb.2
  have : ((s.filter (fun i => ArrivesAt q i)).card : ℝ) ≤ 1 := by exact_mod_cast this
  nlinarith

lemma sum_dep_eq (q : State n) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) = q.1 0 - q.1 N := by
  rw [Finset.sum_range_sub']

/-- rates of the JSQ chain as a finite family indexed by `ℕ ⊕ ℕ` -/
noncomputable def rate (lam : ℝ) (q : State n) : ℕ ⊕ ℕ → ℝ :=
  Sum.elim (fun i => if ArrivesAt q i then (n : ℝ) * lam else 0)
    (fun i => (q.1 i : ℝ) - (q.1 (i + 1) : ℝ))

noncomputable def target (q : State n) : ℕ ⊕ ℕ → State n :=
  Sum.elim (fun i => up q i) (fun i => down q i)

lemma genQ_eq_finsum (hn : 1 ≤ n) (lam : ℝ) (f : State n → ℝ) (q : State n) :
    genQ n lam f q = ∑ t ∈ (Finset.range (cut q)).disjSum (Finset.range (cut q)),
      rate lam q t * (f (target q t) - f q) := by
  rw [Finset.sum_disjSum, genQ]
  congr 1
  · rw [tsum_eq_sum (s := Finset.range (cut q))]
    · rfl
    · intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      simp [not_arrives_of_ge hn q i hi]
  · rw [tsum_eq_sum (s := Finset.range (cut q))]
    · rfl
    · intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [dep_rate_zero q i hi]; simp

theorem lemma_1_proof (n : ℕ) (lam : ℝ) (hn : 1 ≤ n) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : State n → ℝ) (hπ : IsStationaryDist (genQ n lam) π)
    (f : State n → ℝ) (hf : Summable (fun q => π q * |f q|)) :
    Summable (fun q => π q * genQ n lam f q) ∧ expect π (genQ n lam f) = 0 := by
  have hr : ∀ (q : State n) t, 0 ≤ rate lam q t := by
    intro q t
    cases t with
    | inl i => simp only [rate, Sum.elim_inl]; split_ifs <;> positivity
    | inr i => simp only [rate, Sum.elim_inr]; exact dep_rate_nonneg q i
  have hM : ∀ q : State n, ∑ t ∈ (Finset.range (cut q)).disjSum (Finset.range (cut q)), rate lam q t ≤
      (n : ℝ) * lam + n := by
    intro q
    rw [Finset.sum_disjSum]
    simp only [rate, Sum.elim_inl, Sum.elim_inr]
    have h1 := sum_arr_le q ((n : ℝ) * lam) (by positivity) (Finset.range (cut q))
    rw [sum_dep_eq]
    have h2 : ((q.1 0 : ℕ) : ℝ) ≤ n := by exact_mod_cast q.2.1 0
    have h3 : (0 : ℝ) ≤ (q.1 (cut q) : ℝ) := by positivity
    linarith
  exact bar_abstract π hπ.1 (fun q => (Finset.range (cut q)).disjSum (Finset.range (cut q)))
    (rate lam) target hr _ hM (genQ n lam) (fun f q => genQ_eq_finsum hn lam f q) hπ.2.2.2 f hf

end JSQ

end JSQHalfinWhitt.Tightness

open JSQHalfinWhitt.Tightness in
theorem solution (n : ℕ) (lam : ℝ) (hn : 1 ≤ n) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : State n → ℝ) (hπ : IsStationaryDist (genQ n lam) π)
    (f : State n → ℝ) (hf : Summable (fun q => π q * |f q|)) :
    Summable (fun q => π q * genQ n lam f q) ∧ expect π (genQ n lam f) = 0 :=
  lemma_1_proof n lam hn hlam0 hlam1 π hπ f hf
