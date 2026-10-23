-- Prove2me | solution 1 for MarketInterference.FluidLimit.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T20:37:07.644512+00:00
-- url     : https://prove2.me/submissions/6271ced7-2c43-46b4-8108-2ec717fda7a8

import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidLimit_PoissonCounts

namespace MarketInterference.FluidLimit.Mk1

open MeasureTheory ProbabilityTheory Filter Topology Real
open MarketInterference.FluidBias MarketInterference.FluidLimit

/-! ### Deterministic LP facts -/

section LP

variable {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]

lemma obj_bound (N : Network nd ns I E) (τ : ℝ)
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ τ * N.k e) :
    |obj N x| ≤ ∑ e, |N.v e| * (τ * N.k e) := by
  unfold obj
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  rw [abs_mul, abs_of_nonneg (hx e).1]
  exact mul_le_mul_of_nonneg_left (hx e).2 (abs_nonneg _)

lemma Phi_bound (N : Network nd ns I E)
    {τ : ℝ} (hτ : 0 ≤ τ) (d : Fin nd → ℝ) (s : Fin ns → ℝ) :
    |Phi N τ d s| ≤ ∑ e, |N.v e| * (τ * N.k e) := by
  have hB : 0 ≤ ∑ e, |N.v e| * (τ * N.k e) :=
    Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (mul_nonneg hτ (N.k_nonneg e))
  unfold Phi
  set S := obj N '' {x | Feasible N τ d s x}
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h, Real.sSup_empty]; simpa using hB
  · have hb : ∀ y ∈ S, |y| ≤ ∑ e, |N.v e| * (τ * N.k e) := by
      rintro y ⟨x, hx, rfl⟩
      exact obj_bound N τ x hx.1
    have hbdd : BddAbove S := ⟨_, fun y hy => (abs_le.1 (hb y hy)).2⟩
    rw [abs_le]
    constructor
    · obtain ⟨y, hy⟩ := h
      exact (abs_le.1 (hb y hy)).1.trans (le_csSup hbdd hy)
    · exact csSup_le h fun y hy => (abs_le.1 (hb y hy)).2

lemma bdd (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ) :
    BddAbove (obj N '' {x | Feasible N τ d s x}) := by
  refine ⟨∑ e, |N.v e| * (τ * N.k e), ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact (abs_le.1 (obj_bound N τ x hx.1)).2

lemma feas_zero (N : Network nd ns I E) {τ : ℝ} (hτ : 0 ≤ τ) {d : Fin nd → ℝ}
    {s : Fin ns → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∀ j, 0 ≤ s j) :
    Feasible N τ d s (fun _ => 0) := by
  refine ⟨fun e => ⟨le_rfl, mul_nonneg hτ (N.k_nonneg e)⟩, fun i => ?_, fun j => ?_, fun u => ?_⟩
  · simpa using hd i
  · simpa using hs j
  · simp

lemma ne (N : Network nd ns I E) {τ : ℝ} (hτ : 0 ≤ τ) {d : Fin nd → ℝ}
    {s : Fin ns → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∀ j, 0 ≤ s j) :
    (obj N '' {x | Feasible N τ d s x}).Nonempty :=
  ⟨_, _, feas_zero N hτ hd hs, rfl⟩

lemma feas_scale (N : Network nd ns I E) {τ τ' c : ℝ} (hc : 0 ≤ c) (h : c * τ ≤ τ')
    {d : Fin nd → ℝ} {s : Fin ns → ℝ} {x : E → ℝ} (hx : Feasible N τ d s x) :
    Feasible N τ' (fun i => c * d i) (fun j => c * s j) (fun e => c * x e) := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  refine ⟨fun e => ⟨mul_nonneg hc (h1 e).1, ?_⟩, fun i => ?_, fun j => ?_, fun u => ?_⟩
  · calc c * x e ≤ c * (τ * N.k e) := mul_le_mul_of_nonneg_left (h1 e).2 hc
      _ = (c * τ) * N.k e := by ring
      _ ≤ τ' * N.k e := mul_le_mul_of_nonneg_right h (N.k_nonneg e)
  · rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h2 i) hc
  · rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h3 j) hc
  · rw [← Finset.mul_sum, ← Finset.mul_sum, h4 u]

lemma obj_scale (N : Network nd ns I E) (c : ℝ) (x : E → ℝ) :
    obj N (fun e => c * x e) = c * obj N x := by
  unfold obj
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

lemma Phi_scale (N : Network nd ns I E) {τ τ' c : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ)
    (h : c * τ ≤ τ') {d : Fin nd → ℝ} {s : Fin ns → ℝ} (hd : ∀ i, 0 ≤ d i)
    (hs : ∀ j, 0 ≤ s j) :
    c * Phi N τ d s ≤ Phi N τ' (fun i => c * d i) (fun j => c * s j) := by
  unfold Phi
  rw [← le_div_iff₀' hc]
  refine csSup_le (ne N hτ hd hs) ?_
  rintro y ⟨x, hx, rfl⟩
  rw [le_div_iff₀' hc, ← obj_scale]
  exact le_csSup (bdd N _ _ _) ⟨_, feas_scale N hc.le h hx, rfl⟩

lemma Phi_mono (N : Network nd ns I E) {τ : ℝ} (hτ : 0 ≤ τ) {d d' : Fin nd → ℝ}
    {s s' : Fin ns → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∀ j, 0 ≤ s j)
    (hdd : ∀ i, d i ≤ d' i) (hss : ∀ j, s j ≤ s' j) :
    Phi N τ d s ≤ Phi N τ d' s' := by
  unfold Phi
  refine csSup_le (ne N hτ hd hs) ?_
  rintro y ⟨x, hx, rfl⟩
  refine le_csSup (bdd N _ _ _) ⟨x, ?_, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hx
  exact ⟨h1, fun i => (h2 i).trans (hdd i), fun j => (h3 j).trans (hss j), h4⟩

end LP

/-! ### Poisson concentration -/

noncomputable def pw (m : ℝ) (k : ℕ) : ℝ := exp (-m) * m ^ k / (k.factorial : ℝ)

lemma pw_succ (m : ℝ) (k : ℕ) : pw m (k + 1) * ((k : ℝ) + 1) = m * pw m k := by
  unfold pw
  rw [Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma hasSum_pw (r : NNReal) : HasSum (fun n => pw r n) 1 := hasSum_one_poissonMeasure r

lemma hasSum_pw1 (r : NNReal) : HasSum (fun n : ℕ => pw r n * n) r := by
  have key : (fun n : ℕ => r * pw r n) = fun n : ℕ => pw r (n + 1) * ((n + 1 : ℕ) : ℝ) := by
    funext n; push_cast; exact (pw_succ r n).symm
  have h := (hasSum_pw r).mul_left (r : ℝ)
  rw [mul_one, key] at h
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa using h

lemma hasSum_pw2 (r : NNReal) :
    HasSum (fun n : ℕ => pw r n * ((n : ℝ) * ((n : ℝ) - 1))) ((r : ℝ) ^ 2) := by
  have key : (fun n : ℕ => r * (pw r n * n)) =
      fun n : ℕ => pw r (n + 1) * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)) := by
    funext n
    have h1 := pw_succ r n
    push_cast
    rw [show (n : ℝ) + 1 - 1 = n by ring, ← mul_assoc, ← h1]; ring
  have h := (hasSum_pw1 r).mul_left (r : ℝ)
  rw [key, ← sq] at h
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa using h

lemma hasSum_var (r : NNReal) :
    HasSum (fun n : ℕ => pw r n * ((n : ℝ) - r) ^ 2) r := by
  have h := ((hasSum_pw2 r).add ((hasSum_pw1 r).mul_left (1 - 2 * (r : ℝ)))).add
    ((hasSum_pw r).mul_left ((r : ℝ) ^ 2))
  have key : (fun n : ℕ => pw r n * ((n : ℝ) * ((n : ℝ) - 1)) + (1 - 2 * (r : ℝ)) * (pw r n * n)
      + (r : ℝ) ^ 2 * pw r n) = fun n : ℕ => pw r n * ((n : ℝ) - r) ^ 2 := by
    funext n; ring
  have e : (r : ℝ) ^ 2 + (1 - 2 * (r : ℝ)) * r + (r : ℝ) ^ 2 * 1 = r := by ring
  rw [key, e] at h
  exact h

lemma integrable_var (r : NNReal) : Integrable (fun n : ℕ => ((n : ℝ) - r) ^ 2) Po(r) := by
  rw [integrable_poissonMeasure_iff]
  refine (hasSum_var r).summable.congr fun n => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  rfl

lemma integral_var (r : NNReal) : ∫ n : ℕ, ((n : ℝ) - r) ^ 2 ∂Po(r) = r := by
  rw [integral_poissonMeasure]
  exact (hasSum_var r).tsum_eq

lemma pois_bad (r : NNReal) {ε : ℝ} (hε : 0 < ε) :
    Po(r).real {n : ℕ | ¬((1 - ε) * r ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + ε) * r)} ≤
      1 / (ε ^ 2 * r) := by
  have hnn : 0 ≤ᵐ[Po(r)] (fun n : ℕ => ((n : ℝ) - r) ^ 2) :=
    Eventually.of_forall fun n => sq_nonneg _
  rcases eq_or_lt_of_le r.2 with h0 | hpos
  · -- r = 0
    have hr : (r : ℝ) = 0 := h0.symm
    have hM := mul_meas_ge_le_integral_of_nonneg hnn (integrable_var r) 1
    rw [integral_var, one_mul] at hM
    have hsub : {n : ℕ | ¬((1 - ε) * r ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + ε) * r)} ⊆
        {n : ℕ | (1 : ℝ) ≤ ((n : ℝ) - r) ^ 2} := by
      intro n hn
      simp only [Set.mem_setOf_eq] at hn ⊢
      rw [hr] at hn ⊢
      have : n ≠ 0 := by
        rintro rfl; simp at hn
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 this
      nlinarith
    have h0' : 1 / (ε ^ 2 * (r : ℝ)) = 0 := by rw [hr]; simp
    rw [h0']
    exact (measureReal_mono hsub).trans (hM.trans hr.le)
  · have hr : (0 : ℝ) < r := hpos
    have hM := mul_meas_ge_le_integral_of_nonneg hnn (integrable_var r) (ε ^ 2 * r ^ 2)
    rw [integral_var] at hM
    have hsub : {n : ℕ | ¬((1 - ε) * r ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + ε) * r)} ⊆
        {n : ℕ | ε ^ 2 * (r : ℝ) ^ 2 ≤ ((n : ℝ) - r) ^ 2} := by
      intro n hn
      simp only [Set.mem_setOf_eq, not_and_or, not_le] at hn ⊢
      have he : 0 < ε * r := mul_pos hε hr
      rcases hn with h | h
      · nlinarith
      · nlinarith
    have hpos2 : 0 < ε ^ 2 * (r : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ (by positivity)]
    have := (mul_le_mul_of_nonneg_left (measureReal_mono hsub (μ := Po(r)))
      hpos2.le).trans hM
    nlinarith

/-! ### Main argument -/

section Main

variable {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]

lemma law_fst (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ : ℝ) (i : Fin nd) (A : Set ℕ) :
    (fluidLaw lam pi τ).real {z | z.1 i ∈ A} = Po(Real.toNNReal (lam i * τ)).real A := by
  unfold fluidLaw
  have h := (measurePreserving_eval (μ := fun i => poissonMeasure (Real.toNNReal (lam i * τ))) i).comp
    (measurePreserving_fst (μ := Measure.pi fun i => poissonMeasure (Real.toNNReal (lam i * τ)))
      (ν := Measure.pi fun j => poissonMeasure (Real.toNNReal (pi j * τ))))
  exact h.measureReal_preimage (MeasurableSet.of_discrete).nullMeasurableSet

lemma law_snd (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ : ℝ) (j : Fin ns) (A : Set ℕ) :
    (fluidLaw lam pi τ).real {z | z.2 j ∈ A} = Po(Real.toNNReal (pi j * τ)).real A := by
  unfold fluidLaw
  have h := (measurePreserving_eval (μ := fun j => poissonMeasure (Real.toNNReal (pi j * τ))) j).comp
    (measurePreserving_snd (μ := Measure.pi fun i => poissonMeasure (Real.toNNReal (lam i * τ)))
      (ν := Measure.pi fun j => poissonMeasure (Real.toNNReal (pi j * τ))))
  exact h.measureReal_preimage (MeasurableSet.of_discrete).nullMeasurableSet

instance fluidLaw_prob (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ : ℝ) :
    IsProbabilityMeasure (fluidLaw lam pi τ) := by
  unfold fluidLaw; infer_instance

/-- coordinatewise good event -/
def G (ε m : ℝ) : Set ℕ := {n : ℕ | (1 - ε) * m ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + ε) * m}

def good (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (ε t : ℝ) : Set ((Fin nd → ℕ) × (Fin ns → ℕ)) :=
  {z | (∀ i, z.1 i ∈ G ε (lam i * t)) ∧ ∀ j, z.2 j ∈ G ε (pi j * t)}

lemma bad_bound (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (hlam : 0 ≤ lam) (hpi : 0 ≤ pi)
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    (fluidLaw lam pi t).real (good lam pi ε t)ᶜ ≤
      (∑ i, 1 / (ε ^ 2 * lam i) + ∑ j, 1 / (ε ^ 2 * pi j)) / t := by
  have hsub : (good lam pi ε t)ᶜ ⊆ (⋃ i, {z : (Fin nd → ℕ) × (Fin ns → ℕ) | z.1 i ∈ (G ε (lam i * t))ᶜ}) ∪
      ⋃ j, {z : (Fin nd → ℕ) × (Fin ns → ℕ) | z.2 j ∈ (G ε (pi j * t))ᶜ} := by
    intro z hz
    simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_forall] at hz
    rcases hz with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact Or.inl (Set.mem_iUnion.2 ⟨i, hi⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, hj⟩)
  have hD : ∀ i, (fluidLaw lam pi t).real {z | z.1 i ∈ (G ε (lam i * t))ᶜ} ≤
      1 / (ε ^ 2 * lam i) / t := by
    intro i
    rw [law_fst]
    have hm : 0 ≤ lam i * t := mul_nonneg (hlam i) ht
    have := pois_bad (Real.toNNReal (lam i * t)) hε
    rw [Real.coe_toNNReal _ hm] at this
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · rfl
    · rw [div_div, mul_assoc]
  have hS : ∀ j, (fluidLaw lam pi t).real {z | z.2 j ∈ (G ε (pi j * t))ᶜ} ≤
      1 / (ε ^ 2 * pi j) / t := by
    intro j
    rw [law_snd]
    have hm : 0 ≤ pi j * t := mul_nonneg (hpi j) ht
    have := pois_bad (Real.toNNReal (pi j * t)) hε
    rw [Real.coe_toNNReal _ hm] at this
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · rfl
    · rw [div_div, mul_assoc]
  calc (fluidLaw lam pi t).real (good lam pi ε t)ᶜ
      ≤ (fluidLaw lam pi t).real ((⋃ i, {z : (Fin nd → ℕ) × (Fin ns → ℕ) | z.1 i ∈ (G ε (lam i * t))ᶜ}) ∪
      ⋃ j, {z : (Fin nd → ℕ) × (Fin ns → ℕ) | z.2 j ∈ (G ε (pi j * t))ᶜ}) := measureReal_mono hsub
    _ ≤ ∑ i, (fluidLaw lam pi t).real {z | z.1 i ∈ (G ε (lam i * t))ᶜ} +
        ∑ j, (fluidLaw lam pi t).real {z | z.2 j ∈ (G ε (pi j * t))ᶜ} :=
      (measureReal_union_le _ _).trans
        (add_le_add (measureReal_iUnion_fintype_le _) (measureReal_iUnion_fintype_le _))
    _ ≤ ∑ i, 1 / (ε ^ 2 * lam i) / t + ∑ j, 1 / (ε ^ 2 * pi j) / t :=
      add_le_add (Finset.sum_le_sum fun i _ => hD i) (Finset.sum_le_sum fun j _ => hS j)
    _ = _ := by rw [add_div, Finset.sum_div, Finset.sum_div]

lemma sum_eq (N : Network nd ns I E) (τ : ℝ) :
    ∑ e, |N.v e| * (τ * N.k e) = τ * ∑ e, |N.v e| * N.k e := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring

lemma pt (N : Network nd ns I E) (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (hlam : 0 ≤ lam)
    (hpi : 0 ≤ pi) {ε t : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (ht : 0 < t)
    (z : (Fin nd → ℕ) × (Fin ns → ℕ)) (hz : z ∈ good lam pi ε t) :
    |(1 / t) * Phi N t (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ)) - Phi N 1 lam pi| ≤
      ε * ∑ e, |N.v e| * N.k e := by
  obtain ⟨hzD, hzS⟩ := hz
  set Φ := Phi N 1 lam pi
  set P := Phi N t (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ))
  have hΦ := Phi_bound N zero_le_one lam pi
  rw [sum_eq, one_mul] at hΦ
  have hl : ∀ i, 0 ≤ lam i := hlam
  have hp : ∀ j, 0 ≤ pi j := hpi
  have hc : 0 < (1 - ε) * t := mul_pos (by linarith) ht
  have L1 := Phi_scale N (τ := 1) (τ' := t) hc zero_le_one (by nlinarith) hl hp
  have L2 : Phi N t (fun i => (1 - ε) * t * lam i) (fun j => (1 - ε) * t * pi j) ≤ P :=
    Phi_mono N ht.le (fun i => mul_nonneg hc.le (hl i)) (fun j => mul_nonneg hc.le (hp j))
      (fun i => by have := (hzD i).1; linarith) (fun j => by have := (hzS j).1; linarith)
  have hc' : 0 < 1 / ((1 + ε) * t) := by positivity
  have U1 := Phi_scale N (c := 1 / ((1 + ε) * t)) (τ := t) (τ' := 1) hc' ht.le
    (by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; nlinarith)
    (d := fun i => (1 + ε) * t * lam i) (s := fun j => (1 + ε) * t * pi j)
    (fun i => by have := hl i; positivity) (fun j => by have := hp j; positivity)
  have e1 : (fun i => 1 / ((1 + ε) * t) * ((1 + ε) * t * lam i)) = lam := by
    funext i; field_simp
  have e2 : (fun j => 1 / ((1 + ε) * t) * ((1 + ε) * t * pi j)) = pi := by
    funext j; field_simp
  rw [e1, e2] at U1
  have U2 : P ≤ Phi N t (fun i => (1 + ε) * t * lam i) (fun j => (1 + ε) * t * pi j) :=
    Phi_mono N ht.le (fun i => Nat.cast_nonneg _) (fun j => Nat.cast_nonneg _)
      (fun i => by have := (hzD i).2; linarith) (fun j => by have := (hzS j).2; linarith)
  have hlo : (1 - ε) * Φ ≤ (1 / t) * P := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ ht]; nlinarith
  have hhi : (1 / t) * P ≤ (1 + ε) * Φ := by
    have h3 : 1 / ((1 + ε) * t) * P ≤ Φ :=
      (mul_le_mul_of_nonneg_left U2 hc'.le).trans U1
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ ht]
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)] at h3
    nlinarith
  have hΦ0 : Φ ≤ ∑ e, |N.v e| * N.k e := (abs_le.1 hΦ).2
  rw [abs_le]; constructor <;> nlinarith

lemma integrable_bdd {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (μ : Measure α) [IsFiniteMeasure μ] (g : α → ℝ) (C : ℝ) (h : ∀ z, |g z| ≤ C) :
    Integrable g μ :=
  Integrable.of_bound (measurable_of_countable g).aestronglyMeasurable C
    (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using h z)

lemma key_est (N : Network nd ns I E) (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (hlam : 0 ≤ lam)
    (hpi : 0 ≤ pi) {ε t : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (ht : 0 < t) :
    |(∫ z, (1 / t) * Phi N t (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ)) ∂(fluidLaw lam pi t))
      - Phi N 1 lam pi| ≤ ε * ∑ e, |N.v e| * N.k e +
        2 * (∑ e, |N.v e| * N.k e) * (fluidLaw lam pi t).real (good lam pi ε t)ᶜ := by
  set M := ∑ e, |N.v e| * N.k e
  set μ := fluidLaw lam pi t
  have hprob : IsProbabilityMeasure μ := by
    simp only [μ, fluidLaw]; infer_instance
  set f := fun z : (Fin nd → ℕ) × (Fin ns → ℕ) =>
    (1 / t) * Phi N t (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ))
  have hM : 0 ≤ M := Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (N.k_nonneg e)
  have hf : ∀ z, |f z| ≤ M := by
    intro z
    have := Phi_bound N ht.le (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ))
    rw [sum_eq] at this
    simp only [f, abs_mul, abs_of_pos (one_div_pos.2 ht)]
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ ht]; linarith
  have hΦ := Phi_bound N zero_le_one lam pi
  rw [sum_eq, one_mul] at hΦ
  have hpt : ∀ z, |f z - Phi N 1 lam pi| ≤ ε * M + 2 * M * (good lam pi ε t)ᶜ.indicator 1 z := by
    intro z
    by_cases hz : z ∈ good lam pi ε t
    · have := pt N lam pi hlam hpi hε hε1 ht z hz
      rw [Set.indicator_of_notMem (by simpa using hz)]
      simp only [mul_zero, add_zero]
      exact this
    · rw [Set.indicator_of_mem (by simpa using hz)]
      have h1 := hf z
      have : |f z - Phi N 1 lam pi| ≤ |f z| + |Phi N 1 lam pi| := abs_sub _ _
      simp only [Pi.one_apply, mul_one]
      nlinarith
  have hfi : Integrable f μ := integrable_bdd μ f M hf
  have hci : Integrable (fun _ : (Fin nd → ℕ) × (Fin ns → ℕ) => Phi N 1 lam pi) μ :=
    integrable_const _
  have hIi : Integrable ((good lam pi ε t)ᶜ.indicator (1 : (Fin nd → ℕ) × (Fin ns → ℕ) → ℝ)) μ :=
    integrable_bdd μ _ 1 fun z => by
      by_cases hz : z ∈ (good lam pi ε t)ᶜ
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz]
  have e1 : (∫ z, f z ∂μ) - Phi N 1 lam pi = ∫ z, (f z - Phi N 1 lam pi) ∂μ := by
    rw [integral_sub hfi hci, integral_const, probReal_univ, one_smul]
  have e2 : ∫ z, (ε * M + 2 * M * (good lam pi ε t)ᶜ.indicator 1 z) ∂μ =
      ε * M + 2 * M * μ.real (good lam pi ε t)ᶜ := by
    rw [integral_add (integrable_const _) (hIi.const_mul _), integral_const, probReal_univ,
      one_smul, integral_const_mul, integral_indicator_one (MeasurableSet.of_discrete)]
  show |(∫ z, f z ∂μ) - Phi N 1 lam pi| ≤ _
  rw [e1, ← e2]
  exact (abs_integral_le_integral_abs).trans (integral_mono (hfi.sub hci).abs
    ((integrable_const _).add (hIi.const_mul _)) hpt)

theorem main (N : Network nd ns I E) (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (hlam : 0 ≤ lam)
    (hpi : 0 ≤ pi) :
    Tendsto (fun τ : ℕ => ∫ z, (1 / (τ : ℝ)) * Phi N τ (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ))
        ∂(fluidLaw lam pi τ)) atTop (𝓝 (Phi N 1 lam pi)) := by
  set M := ∑ e, |N.v e| * N.k e
  have hM : 0 ≤ M := Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (N.k_nonneg e)
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε := min (1 / 2) (η / (2 * (M + 1))) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hεM : ε * M < η / 2 := by
    have : ε ≤ η / (2 * (M + 1)) := min_le_right _ _
    calc ε * M ≤ η / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right this hM
      _ < η / 2 := by
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  set C := ∑ i, 1 / (ε ^ 2 * lam i) + ∑ j, 1 / (ε ^ 2 * pi j)
  have hT := (tendsto_const_div_atTop_nhds_zero_nat (2 * M * C)).eventually
    (gt_mem_nhds (half_pos hη))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hT.and (eventually_ge_atTop 1))
  refine ⟨N0, fun τ hτ => ?_⟩
  obtain ⟨h1, h2⟩ := hN0 τ hτ
  have ht : (0 : ℝ) < τ := by exact_mod_cast h2
  rw [Real.dist_eq]
  have hk := key_est N lam pi hlam hpi hε hε1 ht
  have hb := bad_bound lam pi hlam hpi hε ht.le
  have : 2 * M * (fluidLaw lam pi τ).real (good lam pi ε τ)ᶜ ≤ 2 * M * C / τ := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  linarith

end Main

end MarketInterference.FluidLimit.Mk1

namespace MarketInterference.FluidLimit

open MeasureTheory Filter Topology

theorem theorem_1 {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (hlam : 0 ≤ lam) (hpi : 0 ≤ pi) :
    Tendsto (fun τ : ℕ => ∫ z, (1 / (τ : ℝ)) * MarketInterference.FluidBias.Phi N τ (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ))
        ∂(fluidLaw lam pi τ)) atTop (𝓝 (MarketInterference.FluidBias.Phi N 1 lam pi)) :=
  Mk1.main N lam pi hlam hpi

end MarketInterference.FluidLimit


-- Platform entry point: restates the target verbatim.
namespace MarketInterference.FluidLimit

open MeasureTheory Filter Topology

/-- Theorem 1, display (7) (arXiv:2205.02274v4, p. 12): along integer densities `τ → ∞`,
`E[(1/τ) Φ_τ(D^{τ,λ}, S^τ)] → Φ(λ, π)`, where `D^{τ,λ}_i ∼ Poisson(λ_i τ)` and `S^τ_j ∼ Poisson(π_j τ)`
are independent. -/
theorem _root_.solution {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (hlam : 0 ≤ lam) (hpi : 0 ≤ pi) :
    Tendsto (fun τ : ℕ => ∫ z, (1 / (τ : ℝ)) * MarketInterference.FluidBias.Phi N τ (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ))
        ∂(fluidLaw lam pi τ)) atTop (𝓝 (MarketInterference.FluidBias.Phi N 1 lam pi)) := by
  apply @MarketInterference.FluidLimit.theorem_1 <;> assumption

end MarketInterference.FluidLimit
