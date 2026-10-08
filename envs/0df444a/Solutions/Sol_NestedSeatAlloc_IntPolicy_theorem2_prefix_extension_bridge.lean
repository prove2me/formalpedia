-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem2_prefix_extension_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:38:27.766042+00:00
-- url     : https://prove2.me/submissions/97c06056-e593-40df-bcd6-11666db9aa1a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

set_option autoImplicit false

namespace B7892142

open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory

lemma revenue_prefix_irrel (f x : ℕ → ℝ) :
    ∀ (k : ℕ) (p q : ℕ → ℝ), (∀ i, i < k → p i = q i) →
      ∀ s, revenue f p x k s = revenue f q x k s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p q hpq s
    match k, ih, hpq with
    | 0, _, _ => simp [revenue]
    | 1, _, _ => simp [revenue]
    | m + 2, ih, hpq =>
      have hp : p (m + 1) = q (m + 1) := hpq (m + 1) (by omega)
      have hrec : ∀ t, revenue f p x (m + 1) t = revenue f q x (m + 1) t :=
        ih (m + 1) (by omega) p q (fun i hi => hpq i (by omega))
      simp only [revenue, hp, hrec]

lemma clampU_zero {s a b : ℝ} (hb : 0 ≤ b) (hs : s ≤ a) : min (max (s - a) 0) b = 0 := by
  rw [max_eq_right (by linarith), min_eq_left hb]

lemma clampU_mid {s a b : ℝ} (h1 : a ≤ s) (h2 : s ≤ a + b) : min (max (s - a) 0) b = s - a := by
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]

lemma clampU_hi {s a b : ℝ} (hb : 0 ≤ b) (h : a + b ≤ s) : min (max (s - a) 0) b = b := by
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]

lemma clampU_mono {s t a b : ℝ} (hb : 0 ≤ b) (hst : s ≤ t) :
    min (max (s - a) 0) b ≤ min (max (t - a) 0) b ∧
    min (max (t - a) 0) b - min (max (s - a) 0) b ≤ t - s := by
  simp only [min_def, max_def]
  split_ifs <;> constructor <;> linarith

lemma rev_step (f p x : ℕ → ℝ) (k : ℕ) (hx : 0 ≤ x (k + 2)) (s : ℝ) :
    revenue f p x (k + 2) s = f (k + 2) * min (max (s - p (k + 1)) 0) (x (k + 2))
      + revenue f p x (k + 1) (s - min (max (s - p (k + 1)) 0) (x (k + 2))) := by
  rw [revenue]
  split_ifs with h1 h2
  · rw [clampU_zero hx h1.le]; simp
  · rw [clampU_mid (not_lt.mp h1) h2.le, sub_sub_cancel]; ring
  · rw [clampU_hi hx (not_lt.mp h2)]; ring

lemma rev_zero (f p x : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hx : ∀ i, 0 ≤ x i) :
    ∀ k, revenue f p x k 0 = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [revenue]
    | 1, _ =>
      simp only [revenue]
      split_ifs with h
      · ring
      · have : x 1 = 0 := le_antisymm (not_lt.mp h) (hx 1)
        rw [this]; ring
    | k + 2, ih =>
      rw [rev_step f p x k (hx _), clampU_zero (hx _) (by simpa using hp (k + 1))]
      simp [ih (k + 1) (by omega)]

lemma rev_lip (f p x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (hf : ∀ i, 1 ≤ i → 0 ≤ f i ∧ f i ≤ f 1) :
    ∀ k s t, s ≤ t → revenue f p x k s ≤ revenue f p x k t ∧
      revenue f p x k t - revenue f p x k s ≤ f 1 * (t - s) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s t hst
    have hf1 := (hf 1 le_rfl).1
    have hts : 0 ≤ f 1 * (t - s) := mul_nonneg hf1 (by linarith)
    match k, ih with
    | 0, _ =>
      simp only [revenue, le_refl, sub_self, true_and]
      exact hts
    | 1, _ =>
      simp only [revenue]
      split_ifs with h1 h2 h2
      · constructor <;> nlinarith
      · constructor <;> nlinarith [mul_nonneg hf1 (by linarith : (0:ℝ) ≤ x 1 - s),
          mul_nonneg hf1 (by linarith : (0:ℝ) ≤ t - x 1)]
      · exfalso; linarith
      · constructor <;> nlinarith
    | k + 2, ih =>
      rw [rev_step f p x k (hx _) s, rev_step f p x k (hx _) t]
      obtain ⟨hu1, hu2⟩ := clampU_mono (a := p (k + 1)) (hx (k + 2)) hst
      set us := min (max (s - p (k + 1)) 0) (x (k + 2))
      set ut := min (max (t - p (k + 1)) 0) (x (k + 2))
      obtain ⟨hg1, hg2⟩ := ih (k + 1) (by omega) (s - us) (t - ut) (by linarith)
      obtain ⟨hfa, hfb⟩ := hf (k + 2) (by omega)
      have e1 : f (k + 2) * us ≤ f (k + 2) * ut := mul_le_mul_of_nonneg_left hu1 hfa
      have e2 : f (k + 2) * (ut - us) ≤ f 1 * (ut - us) :=
        mul_le_mul_of_nonneg_right hfb (by linarith)
      have e3 : f 1 * (t - ut - (s - us)) + f 1 * (ut - us) = f 1 * (t - s) := by ring
      constructor <;> nlinarith

lemma rev_eventually_const (f p x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ k, ∃ T, ∀ s, T ≤ s → revenue f p x k s = revenue f p x k T := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => exact ⟨0, fun s _ => by simp [revenue]⟩
    | 1, _ =>
      refine ⟨x 1, fun s hs => ?_⟩
      simp only [revenue]
      rw [if_neg (not_lt.mpr hs), if_neg (lt_irrefl _)]
    | k + 2, ih =>
      obtain ⟨T, hT⟩ := ih (k + 1) (by omega)
      refine ⟨max (p (k + 1) + x (k + 2)) (T + x (k + 2)), fun s hs => ?_⟩
      have h1 := le_max_left (p (k + 1) + x (k + 2)) (T + x (k + 2))
      have h2 := le_max_right (p (k + 1) + x (k + 2)) (T + x (k + 2))
      set M := max (p (k + 1) + x (k + 2)) (T + x (k + 2))
      have c1 : min (max (s - p (k + 1)) 0) (x (k + 2)) = x (k + 2) :=
        clampU_hi (hx _) (by linarith)
      have c2 : min (max (M - p (k + 1)) 0) (x (k + 2)) = x (k + 2) :=
        clampU_hi (hx _) (by linarith)
      rw [rev_step f p x k (hx _) s, rev_step f p x k (hx _) M, c1, c2,
        hT (s - x (k + 2)) (by linarith), hT (M - x (k + 2)) (by linarith)]

lemma rev_affine (f p x : ℕ → ℝ) (hxn : ∀ i, ∃ n : ℕ, x i = n) (hpn : ∀ i, ∃ n : ℕ, p i = n) :
    ∀ k (m : ℤ) (s : ℝ), (m : ℝ) ≤ s → s ≤ m + 1 →
      revenue f p x k s = revenue f p x k m
        + (s - m) * (revenue f p x k (m + 1) - revenue f p x k m) := by
  have hx : ∀ i, 0 ≤ x i := fun i => by
    obtain ⟨n, hn⟩ := hxn i
    rw [hn]; positivity
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m s hs1 hs2
    match k, ih with
    | 0, _ => simp [revenue]
    | 1, _ =>
      obtain ⟨a, ha⟩ := hxn 1
      simp only [revenue]
      rcases le_or_gt ((m : ℤ) + 1) (a : ℤ) with h | h
      · have h' : (m : ℝ) + 1 ≤ a := by exact_mod_cast h
        have key : ∀ t : ℝ, t ≤ x 1 → (if t < x 1 then f 1 * t else f 1 * x 1) = f 1 * t := by
          intro t ht
          split_ifs with h0
          · rfl
          · rw [le_antisymm ht (not_lt.mp h0)]
        rw [key s (by rw [ha]; linarith), key (m : ℝ) (by rw [ha]; linarith),
          key ((m : ℝ) + 1) (by rw [ha]; linarith)]
        ring
      · have h' : (a : ℝ) ≤ m := by
          have : (a : ℤ) ≤ m := by omega
          exact_mod_cast this
        have key : ∀ t : ℝ, x 1 ≤ t → (if t < x 1 then f 1 * t else f 1 * x 1) = f 1 * x 1 := by
          intro t ht
          rw [if_neg (not_lt.mpr ht)]
        rw [key s (by rw [ha]; linarith), key (m : ℝ) (by rw [ha]; linarith),
          key ((m : ℝ) + 1) (by rw [ha]; linarith)]
        ring
    | k + 2, ih =>
      obtain ⟨a, ha⟩ := hpn (k + 1)
      obtain ⟨b, hb⟩ := hxn (k + 2)
      have hb0 : (0 : ℝ) ≤ x (k + 2) := hx _
      have hstep := rev_step f p x k hb0
      rw [hstep s, hstep (m : ℝ), hstep ((m : ℝ) + 1)]
      rcases le_or_gt ((m : ℤ) + 1) (a : ℤ) with h | h
      · have h' : (m : ℝ) + 1 ≤ p (k + 1) := by rw [ha]; exact_mod_cast h
        rw [clampU_zero hb0 (by linarith : s ≤ p (k + 1)),
          clampU_zero hb0 (by linarith : (m : ℝ) ≤ p (k + 1)), clampU_zero hb0 h']
        simp only [mul_zero, zero_add, sub_zero]
        exact ih (k + 1) (by omega) m s hs1 hs2
      · have hma : p (k + 1) ≤ (m : ℝ) := by
          rw [ha]
          have : (a : ℤ) ≤ m := by omega
          exact_mod_cast this
        rcases le_or_gt ((m : ℤ) + 1) ((a : ℤ) + b) with h2 | h2
        · have h2' : (m : ℝ) + 1 ≤ p (k + 1) + x (k + 2) := by
            rw [ha, hb]; exact_mod_cast h2
          rw [clampU_mid (by linarith : p (k + 1) ≤ s) (by linarith : s ≤ p (k + 1) + x (k + 2)),
            clampU_mid hma (by linarith : (m : ℝ) ≤ p (k + 1) + x (k + 2)),
            clampU_mid (by linarith : p (k + 1) ≤ (m : ℝ) + 1) h2']
          simp only [sub_sub_cancel]
          ring
        · have h2' : p (k + 1) + x (k + 2) ≤ (m : ℝ) := by
            rw [ha, hb]
            have : (a : ℤ) + b ≤ m := by omega
            exact_mod_cast this
          rw [clampU_hi hb0 (by linarith : p (k + 1) + x (k + 2) ≤ s), clampU_hi hb0 h2',
            clampU_hi hb0 (by linarith : p (k + 1) + x (k + 2) ≤ (m : ℝ) + 1)]
          have e1 : (((m - b : ℤ)) : ℝ) = (m : ℝ) - x (k + 2) := by rw [hb]; push_cast; ring
          have := ih (k + 1) (by omega) (m - b) (s - x (k + 2)) (by rw [e1]; linarith)
            (by rw [e1]; linarith)
          rw [this, e1]
          have e2 : (m : ℝ) + 1 - x (k + 2) = (m : ℝ) - x (k + 2) + 1 := by ring
          rw [e2]; ring

lemma rev_meas {Ω : Type*} [MeasurableSpace Ω] (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => revenue f p (fun i => X i ω) k (s ω)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hs
    match k, ih with
    | 0, _ => simp only [revenue]; exact measurable_const
    | 1, _ =>
      simp only [revenue]
      exact Measurable.ite (measurableSet_lt hs (hX 1)) (measurable_const.mul hs)
        (measurable_const.mul (hX 1))
    | k + 2, ih =>
      simp only [revenue]
      refine Measurable.ite (measurableSet_lt hs measurable_const) (ih (k + 1) (by omega) s hs) ?_
      refine Measurable.ite (measurableSet_lt hs (measurable_const.add (hX (k + 2)))) ?_ ?_
      · exact ((hs.sub measurable_const).mul measurable_const).add
          (ih (k + 1) (by omega) (fun _ => p (k + 1)) measurable_const)
      · exact ((hX (k + 2)).mul measurable_const).add
          (ih (k + 1) (by omega) (fun ω => s ω - X (k + 2) ω) (hs.sub (hX (k + 2))))

theorem exists_subdiff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (f q : ℕ → ℝ) (K : ℕ)
    (hX : ∀ i, Measurable (X i)) (hint : ∀ i ω, ∃ n : ℕ, X i ω = n)
    (hqn : ∀ i, ∃ n : ℕ, q i = n) (hf : ∀ i, 1 ≤ i → 0 ≤ f i ∧ f i ≤ f 1)
    (c : ℝ) (hc : 0 < c) :
    ∃ n : ℕ, InSubdiff (expRevenue P X f q K) n c := by
  have hx0 : ∀ i ω, 0 ≤ X i ω := fun i ω => by
    obtain ⟨n, hn⟩ := hint i ω
    rw [hn]; positivity
  have hq0 : ∀ i, 0 ≤ q i := fun i => by
    obtain ⟨n, hn⟩ := hqn i
    rw [hn]; positivity
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, E = expRevenue P X f q K := ⟨_, rfl⟩
  rw [← hE]
  have hEs : ∀ s, E s = ∫ ω, revenue f q (fun i => X i ω) K s ∂P := fun s => by
    rw [hE]; rfl
  have hmeasR : ∀ s : ℝ, Measurable (fun ω => revenue f q (fun i => X i ω) K s) :=
    fun s => rev_meas f q X hX K (fun _ => s) measurable_const
  have hint_s : ∀ s : ℝ, 0 ≤ s → Integrable (fun ω => revenue f q (fun i => X i ω) K s) P := by
    intro s hs
    refine Integrable.mono' (integrable_const (f 1 * s)) (hmeasR s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := rev_lip f q (fun i => X i ω) (fun i => hx0 i ω) hf K 0 s hs
    have h0 := rev_zero f q (fun i => X i ω) hq0 (fun i => hx0 i ω) K
    rw [h0] at h1
    have : 0 ≤ f 1 * s := mul_nonneg (hf 1 le_rfl).1 hs
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h1.1, h1.2]
  have hgaff : ∀ m : ℕ, ∀ s, (m : ℝ) ≤ s → s ≤ m + 1 →
      E s = E m + (s - m) * (E (m + 1) - E m) := by
    intro m s h1 h2
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have e : ∀ ω, revenue f q (fun i => X i ω) K s = revenue f q (fun i => X i ω) K m
        + (s - m) * (revenue f q (fun i => X i ω) K (m + 1) - revenue f q (fun i => X i ω) K m) := by
      intro ω
      have := rev_affine f q (fun i => X i ω) (fun i => hint i ω) hqn K (m : ℤ) s
        (by exact_mod_cast h1) (by exact_mod_cast h2)
      push_cast at this
      exact this
    have hA := hint_s m hm0
    have hB := hint_s (m + 1) (by linarith)
    have hC : Integrable (fun ω => (s - m) * (revenue f q (fun i => X i ω) K (m + 1)
        - revenue f q (fun i => X i ω) K m)) P := (hB.sub hA).const_mul _
    rw [hEs s, hEs m, hEs (m + 1), integral_congr_ae (Filter.Eventually.of_forall e),
      integral_add hA hC, integral_const_mul, integral_sub hB hA]
  have hright : ∀ m : ℕ, HasDerivWithinAt E (E (m + 1) - E m) (Set.Ici (m : ℝ)) m := by
    intro m
    have hlin : HasDerivWithinAt (fun s => E m + (s - m) * (E (m + 1) - E m))
        (E (m + 1) - E m) (Set.Ici (m : ℝ)) m := by
      have := (((hasDerivAt_id (m : ℝ)).sub_const (m : ℝ)).mul_const (E (m + 1) - E m)).const_add
        (E m)
      simpa using this.hasDerivWithinAt
    refine hlin.congr_of_eventuallyEq ?_ (by simp)
    filter_upwards [Icc_mem_nhdsGE (show (m : ℝ) < m + 1 by linarith)] with s hs
    exact hgaff m s hs.1 hs.2
  have hleft : ∀ m : ℕ, HasDerivWithinAt E (E (m + 1) - E m) (Set.Iic ((m : ℝ) + 1)) ((m : ℝ) + 1) := by
    intro m
    have hlin : HasDerivWithinAt (fun s => E m + (s - m) * (E (m + 1) - E m))
        (E (m + 1) - E m) (Set.Iic ((m : ℝ) + 1)) ((m : ℝ) + 1) := by
      have := (((hasDerivAt_id ((m : ℝ) + 1)).sub_const (m : ℝ)).mul_const
        (E (m + 1) - E m)).const_add (E m)
      simpa using this.hasDerivWithinAt
    refine hlin.congr_of_eventuallyEq ?_ (by ring)
    filter_upwards [Icc_mem_nhdsLE (show (m : ℝ) < m + 1 by linarith)] with s hs
    exact hgaff m s hs.1 hs.2
  have hlim : Filter.Tendsto (fun m : ℕ => E ((m : ℝ) + 1) - E m) Filter.atTop (nhds 0) := by
    have hEq : ∀ m : ℕ, E ((m : ℝ) + 1) - E m =
        ∫ ω, (revenue f q (fun i => X i ω) K ((m : ℝ) + 1) - revenue f q (fun i => X i ω) K m) ∂P :=
      fun m => by
        rw [hEs, hEs, integral_sub (hint_s _ (by positivity)) (hint_s _ (by positivity))]
    have hT := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun (m : ℕ) ω => revenue f q (fun i => X i ω) K ((m : ℝ) + 1)
        - revenue f q (fun i => X i ω) K m)
      (f := fun _ => (0 : ℝ)) (fun _ => f 1)
      (fun m => ((hmeasR _).sub (hmeasR _)).aestronglyMeasurable) (integrable_const _)
      (fun m => Filter.Eventually.of_forall fun ω => by
        have h1 := rev_lip f q (fun i => X i ω) (fun i => hx0 i ω) hf K (m : ℝ) ((m : ℝ) + 1)
          (by linarith)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [h1.1, h1.2])
      (Filter.Eventually.of_forall fun ω => by
        obtain ⟨T, hT⟩ := rev_eventually_const f q (fun i => X i ω) (fun i => hx0 i ω) K
        refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
        filter_upwards [Filter.eventually_ge_atTop ⌈T⌉₊] with m hm
        have hTm : T ≤ (m : ℝ) := Nat.ceil_le.mp hm
        rw [hT _ (by linarith), hT _ hTm, sub_self])
    simp only [integral_zero] at hT
    simpa only [hEq] using hT
  have hev : ∀ᶠ m : ℕ in Filter.atTop, E ((m : ℝ) + 1) - E m < c := hlim (Iio_mem_nhds hc)
  obtain ⟨m, hm⟩ := hev.exists
  have hex : ∃ m : ℕ, E ((m : ℝ) + 1) - E m ≤ c := ⟨m, hm.le⟩
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, E ((n : ℝ) + 1) - E n ≤ c ∧
      (n = 0 ∨ ∃ n', n = n' + 1 ∧ c < E ((n' : ℝ) + 1) - E n') := by
    classical
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exact Or.inl h
    · refine Or.inr ⟨Nat.find hex - 1, by omega, ?_⟩
      have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      exact not_le.mp this
  refine ⟨n, ⟨_, hright n, hn1⟩, ?_⟩
  rcases hn2 with h0 | ⟨n', rfl, hlt⟩
  · left; rw [h0]; simp
  · right
    refine ⟨_, ?_, hlt.le⟩
    push_cast
    exact hleft n'

end B7892142

open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (k : ℕ) (p : ℕ → ℕ)
    (hM : IsSeatModel P X f) (hint : ∀ i ω, ∃ n : ℕ, X i ω = n)
    (hpos : ∀ i, 1 ≤ i → 0 < f i) (hk : 1 ≤ k)
    (hclbi : IsCLBI (expRevenue P X f (fun j => (p j : ℝ)) k))
    (h20 : ∀ j, 1 ≤ j → j ≤ k →
      InSubdiff (expRevenue P X f (fun i => (p i : ℝ)) j) (p j) (f (j + 1))) :
    ∃ n : ℕ, ∀ j, 1 ≤ j → j ≤ k + 1 →
      InSubdiff (expRevenue P X f (fun i =>
        if i = k + 1 then (n : ℝ) else (p i : ℝ)) j)
        (if j = k + 1 then n else p j) (f (j + 1)) := by
  have := hM.isProb
  have hfanti : ∀ i, 1 ≤ i → f i ≤ f 1 := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (hM.fare_strictAnti n hn).le.trans ih
  have hf : ∀ i, 1 ≤ i → 0 ≤ f i ∧ f i ≤ f 1 := fun i hi => ⟨(hpos i hi).le, hfanti i hi⟩
  obtain ⟨n, hn⟩ := B7892142.exists_subdiff P X f (fun j => (p j : ℝ)) (k + 1) hM.meas hint
    (fun i => ⟨p i, rfl⟩) hf (f (k + 2)) (hpos (k + 2) (by omega))
  refine ⟨n, fun j hj1 hj2 => ?_⟩
  have hloc : expRevenue P X f (fun i => if i = k + 1 then (n : ℝ) else (p i : ℝ)) j
      = expRevenue P X f (fun i => (p i : ℝ)) j := by
    funext s
    unfold expRevenue
    congr 1
    funext ω
    exact B7892142.revenue_prefix_irrel f (fun i => X i ω) j _ _
      (fun i hi => by simp [show i ≠ k + 1 by omega]) s
  rw [hloc]
  rcases Nat.lt_or_ge j (k + 1) with h | h
  · have hne : j ≠ k + 1 := by omega
    simp only [hne, if_false]
    exact h20 j hj1 (by omega)
  · have hjk : j = k + 1 := by omega
    subst hjk
    simp only [if_true]
    exact hn
