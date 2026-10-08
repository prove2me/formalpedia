-- Prove2me | solution 1 for KingmanSubadditive.Continuous.oscillation_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:50:57.563983+00:00
-- url     : https://prove2.me/submissions/a327c336-0615-4d3a-b89e-29b3e949ce88

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process



namespace KingmanSubadditive.Continuous

open MeasureTheory Filter Topology

variable {S : Type*} [MeasurableSpace S]

lemma ofReal_abs_le_osc
    (x : ℝ → ℝ → S → ℝ) (I : Set ℝ) (ω : S)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s < t) (hsI : s ∈ I) (htI : t ∈ I) :
    ENNReal.ofReal (|x s t ω|) ≤ oscillation x I ω := by
  unfold oscillation
  exact le_iSup₂ (f := fun (p : TimePair) (_ : p.1.1 ∈ I ∧ p.1.2 ∈ I) =>
    ENNReal.ofReal (|x p.1.1 p.1.2 ω|)) (⟨(s, t), hs, hst⟩ : TimePair) ⟨hsI, htI⟩

lemma measurable_procMap (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    Measurable (fun ω : S => fun p : TimePair => x (p.1.1 + τ) (p.1.2 + τ) ω) := by
  refine measurable_pi_iff.2 fun p => ?_
  exact hproc.1 _ _ (by linarith [p.2.1]) (by linarith [p.2.2])

lemma measurable_procMap0 (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x) :
    Measurable (fun ω : S => fun p : TimePair => x p.1.1 p.1.2 ω) := by
  refine measurable_pi_iff.2 fun p => ?_
  exact hproc.1 _ _ p.2.1 p.2.2

/-- law transfer for a single coordinate under a nonnegative time shift. -/
lemma shift_coord (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (s t τ : ℝ) (hs : 0 ≤ s) (hst : s < t) (hτ : 0 ≤ τ) :
    (Integrable (x (s + τ) (t + τ)) P ↔ Integrable (x s t) P) ∧
    ∫ ω, x (s + τ) (t + τ) ω ∂P = ∫ ω, x s t ω ∂P := by
  have hmap := hproc.2.2.1 τ hτ
  have hev : Measurable (fun f : TimePair → ℝ => f (⟨(s, t), hs, hst⟩ : TimePair)) :=
    measurable_pi_apply _
  have h1 := measurable_procMap P x hproc τ hτ
  have h0 := measurable_procMap0 P x hproc
  constructor
  · have A := integrable_map_measure (μ := P)
      (f := fun ω : S => fun p : TimePair => x (p.1.1 + τ) (p.1.2 + τ) ω)
      hev.aestronglyMeasurable h1.aemeasurable
    have B := integrable_map_measure (μ := P)
      (f := fun ω : S => fun p : TimePair => x p.1.1 p.1.2 ω)
      hev.aestronglyMeasurable h0.aemeasurable
    rw [hmap] at A
    exact A.symm.trans B
  · have A := integral_map (μ := P)
      (φ := fun ω : S => fun p : TimePair => x (p.1.1 + τ) (p.1.2 + τ) ω)
      h1.aemeasurable hev.aestronglyMeasurable
    have B := integral_map (μ := P)
      (φ := fun ω : S => fun p : TimePair => x p.1.1 p.1.2 ω)
      h0.aemeasurable hev.aestronglyMeasurable
    rw [hmap] at A
    exact A.symm.trans B

/-- the shifted process as a map into the path space -/
def Xsh (x : ℝ → ℝ → S → ℝ) (τ : ℝ) (ω : S) : TimePair → ℝ :=
  fun p => x (p.1.1 + τ) (p.1.2 + τ) ω

def X0 (x : ℝ → ℝ → S → ℝ) (ω : S) : TimePair → ℝ :=
  fun p => x p.1.1 p.1.2 ω

lemma measurable_Xsh (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (τ : ℝ) (hτ : 0 ≤ τ) : Measurable (Xsh x τ) := by
  refine measurable_pi_iff.2 fun p => ?_
  exact hproc.1 _ _ (by linarith [p.2.1]) (by linarith [p.2.2])

lemma measurable_X0 (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x) :
    Measurable (X0 x) := by
  refine measurable_pi_iff.2 fun p => ?_
  exact hproc.1 _ _ p.2.1 p.2.2

lemma map_Xsh (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (τ : ℝ) (hτ : 0 ≤ τ) : Measure.map (Xsh x τ) P = Measure.map (X0 x) P :=
  hproc.2.2.1 τ hτ

lemma lintegral_Xsh (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (τ : ℝ) (hτ : 0 ≤ τ) (G : (TimePair → ℝ) → ENNReal) (hG : Measurable G) :
    ∫⁻ ω, G (Xsh x τ ω) ∂P = ∫⁻ ω, G (X0 x ω) ∂P := by
  rw [← lintegral_map hG (measurable_Xsh P x hproc τ hτ), map_Xsh P x hproc τ hτ,
    lintegral_map hG (measurable_X0 P x hproc)]

lemma measure_Xsh (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (τ : ℝ) (hτ : 0 ≤ τ) (A : Set (TimePair → ℝ)) (hA : MeasurableSet A) :
    P (Xsh x τ ⁻¹' A) = P (X0 x ⁻¹' A) := by
  rw [← Measure.map_apply (measurable_Xsh P x hproc τ hτ) hA, map_Xsh P x hproc τ hτ,
    Measure.map_apply (measurable_X0 P x hproc) hA]

/-- integer left shifts of the separating set -/
def Dsh (D : Set TimePair) : Set TimePair :=
  {r | ∃ p ∈ D, ∃ m : ℕ, p.1.1 = r.1.1 + m ∧ p.1.2 = r.1.2 + m}

lemma Dsh_countable {D : Set TimePair} (hD : D.Countable) : (Dsh D).Countable := by
  have : Dsh D ⊆ ⋃ p ∈ D, ⋃ m : ℕ, {r : TimePair | (r : ℝ × ℝ) = (p.1.1 - m, p.1.2 - m)} := by
    intro r hr
    obtain ⟨p, hp, m, h1, h2⟩ := hr
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨p, hp, m, ?_⟩
    ext <;> simp <;> linarith
  refine Set.Countable.mono this ?_
  refine hD.biUnion fun p _ => Set.countable_iUnion fun m => ?_
  apply Set.Subsingleton.countable
  intro r hr r' hr'
  simp only [Set.mem_setOf_eq] at hr hr'
  exact Subtype.ext (hr.trans hr'.symm)

lemma mem_Dsh_self {D : Set TimePair} {p : TimePair} (hp : p ∈ D) : p ∈ Dsh D :=
  ⟨p, hp, 0, by simp, by simp⟩

def Jset (c h : ℝ) (l : ℕ) : Set ℝ := Set.Ioo (c + l * h - h) (c + l * h + 2 * h)

def Qidx (D : Set TimePair) (c h : ℝ) (l : ℕ) : Type :=
  {q : TimePair // q ∈ Dsh D ∧ q.1.1 ∈ Jset c h l ∧ q.1.2 ∈ Jset c h l}

lemma Qidx_countable {D : Set TimePair} (hD : D.Countable) (c h : ℝ) (l : ℕ) :
    Countable (Qidx D c h l) :=
  ((Dsh_countable hD).mono (fun q (hq : q ∈ Dsh D ∧ _) => hq.1)).to_subtype

noncomputable def Zf (D : Set TimePair) (c h : ℝ) (l : ℕ) (f : TimePair → ℝ) : ENNReal :=
  ⨆ q : Qidx D c h l, ENNReal.ofReal |f q.1|

noncomputable def Tf (D : Set TimePair) (c h : ℝ) (K : ℕ) (f : TimePair → ℝ) : ENNReal :=
  ∑ l ∈ Finset.range K, Zf D c h l f

noncomputable def Psi (D : Set TimePair) (c h : ℝ) (K : ℕ) (hc : 0 ≤ c)
    (f : TimePair → ℝ) : ENNReal :=
  ENNReal.ofReal |f ⟨(c, c + 1), hc, by linarith⟩| + 9 * Tf D c h K f

lemma measurable_eval_abs (g : TimePair) :
    Measurable (fun f : TimePair → ℝ => ENNReal.ofReal |f g|) := by
  have h : Measurable (fun f : TimePair → ℝ => f g) := measurable_pi_apply g
  exact (continuous_abs.measurable.comp h).ennreal_ofReal

lemma measurable_Zf {D : Set TimePair} (hD : D.Countable) (c h : ℝ) (l : ℕ) :
    Measurable (Zf D c h l) := by
  have := Qidx_countable hD c h l
  exact Measurable.iSup fun q => measurable_eval_abs q.1

lemma measurable_Tf {D : Set TimePair} (hD : D.Countable) (c h : ℝ) (K : ℕ) :
    Measurable (Tf D c h K) :=
  Finset.measurable_sum _ fun l _ => measurable_Zf hD c h l

lemma measurable_Psi {D : Set TimePair} (hD : D.Countable) (c h : ℝ) (K : ℕ) (hc : 0 ≤ c) :
    Measurable (Psi D c h K hc) :=
  (measurable_eval_abs _).add ((measurable_Tf hD c h K).const_mul 9)

/-- shifted-back version of `Zf`, used to compare with the oscillation on `[a,b]` -/
noncomputable def Zback (D : Set TimePair) (c h : ℝ) (l : ℕ) (τ : ℝ)
    (hτ : τ ≤ c + l * h - h) (f : TimePair → ℝ) : ENNReal :=
  ⨆ q : Qidx D c h l, ENNReal.ofReal
    |f ⟨(q.1.1.1 - τ, q.1.1.2 - τ), by linarith [q.2.2.1.1], by linarith [q.1.2.2]⟩|

lemma measurable_Zback {D : Set TimePair} (hD : D.Countable) (c h : ℝ) (l : ℕ) (τ : ℝ)
    (hτ : τ ≤ c + l * h - h) : Measurable (Zback D c h l τ hτ) := by
  have := Qidx_countable hD c h l
  exact Measurable.iSup fun q => measurable_eval_abs _

lemma Zback_Xsh (D : Set TimePair) (c h : ℝ) (l : ℕ) (τ : ℝ)
    (hτ : τ ≤ c + l * h - h) (x : ℝ → ℝ → S → ℝ) (ω : S) :
    Zback D c h l τ hτ (Xsh x τ ω) = Zf D c h l (X0 x ω) := by
  unfold Zback Zf Xsh X0
  simp only [sub_add_cancel]

/-- Borel–Cantelli tail sum for a nonnegative `ℝ≥0∞`-valued variable with finite integral -/
lemma tsum_measure_gt_lt_top (P : Measure S) [IsProbabilityMeasure P]
    (Y : S → ENNReal) (hY : Measurable Y) (hfin : ∫⁻ ω, Y ω ∂P < ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∑' n : ℕ, P {ω | ENNReal.ofReal (ε * n) < Y ω} < ⊤ := by
  letI : MeasureSpace S := ⟨P⟩
  haveI : IsProbabilityMeasure (volume : Measure S) := inferInstanceAs (IsProbabilityMeasure P)
  set X : S → ℝ := fun ω => (Y ω).toReal / ε with hX
  have hint : Integrable X volume := by
    have := integrable_toReal_of_lintegral_ne_top hY.aemeasurable hfin.ne
    exact this.div_const ε
  have hnn : 0 ≤ X := fun ω => by
    simp only [hX, Pi.zero_apply]
    exact div_nonneg ENNReal.toReal_nonneg hε.le
  have htop : (volume : Measure S) {ω | Y ω = ⊤} = 0 :=
    measure_eq_top_of_lintegral_ne_top hY.aemeasurable hfin.ne
  have hsub : ∀ n : ℕ, {ω | ENNReal.ofReal (ε * n) < Y ω} ⊆
      {ω | X ω ∈ Set.Ioi (n : ℝ)} ∪ {ω | Y ω = ⊤} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_cases ht : Y ω = ⊤
    · exact Or.inr ht
    · left
      simp only [Set.mem_setOf_eq, Set.mem_Ioi, hX]
      rw [lt_div_iff₀ hε]
      have h1 : ENNReal.ofReal (ε * n) < ENNReal.ofReal (Y ω).toReal := by
        rwa [ENNReal.ofReal_toReal ht]
      have h2 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 h1
      linarith
  calc ∑' n : ℕ, P {ω | ENNReal.ofReal (ε * n) < Y ω}
      ≤ ∑' n : ℕ, (volume {ω | X ω ∈ Set.Ioi (n : ℝ)} + volume {ω | Y ω = ⊤}) :=
        ENNReal.tsum_le_tsum fun n => (measure_mono (hsub n)).trans (measure_union_le _ _)
    _ = ∑' n : ℕ, volume {ω | X ω ∈ Set.Ioi (n : ℝ)} := by simp [htop]
    _ < ⊤ := ProbabilityTheory.tsum_prob_mem_Ioi_lt_top hint hnn


/-! ### chain lemmas -/

/-- `x` extended by `0` to non-strict pairs -/
noncomputable def xt (x : ℝ → ℝ → S → ℝ) (s t : ℝ) (ω : S) : ℝ :=
  if s < t then x s t ω else 0

lemma xt_of_lt (x : ℝ → ℝ → S → ℝ) {s t : ℝ} (ω : S) (h : s < t) : xt x s t ω = x s t ω :=
  if_pos h

lemma xt_sub (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (s t u : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (htu : t ≤ u) (ω : S) :
    xt x s u ω ≤ xt x s t ω + xt x t u ω := by
  rcases hst.lt_or_eq with h1 | rfl
  · rcases htu.lt_or_eq with h2 | rfl
    · rw [xt_of_lt x ω h1, xt_of_lt x ω h2, xt_of_lt x ω (h1.trans h2)]
      exact hproc.2.1 s t u hs h1 h2 ω
    · simp [xt]
  · simp [xt]

lemma xt_chain (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (e : ℕ → ℝ) (he0 : 0 ≤ e 0) (hmono : Monotone e) (ω : S) (i : ℕ) :
    ∀ j, i ≤ j → xt x (e i) (e j) ω ≤ ∑ l ∈ Finset.Ico i j, xt x (e l) (e (l + 1)) ω := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => simp [xt]
  | succ j hij ih =>
    rw [Finset.sum_Ico_succ_top hij]
    have := xt_sub P x hproc (e i) (e j) (e (j + 1)) (he0.trans (hmono (Nat.zero_le i)))
      (hmono hij) (hmono (Nat.le_succ j)) ω
    linarith

lemma ofReal_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

lemma ofReal_abs_le_add (v : ℝ) :
    ENNReal.ofReal |v| ≤ ENNReal.ofReal v + ENNReal.ofReal (-v) := by
  rcases le_or_gt 0 v with h | h
  · rw [abs_of_nonneg h]; exact le_self_add
  · rw [abs_of_neg h]; exact le_add_self

/-- the location index of `s ∈ [n, n+1]` on the grid of mesh `h = 1/K` -/
noncomputable def idx (n h : ℝ) (K : ℕ) (s : ℝ) : ℕ := min ⌊(s - n) / h⌋₊ (K - 1)

lemma idx_lt (n h : ℝ) (K : ℕ) (hK : 1 ≤ K) (s : ℝ) : idx n h K s < K := by
  unfold idx; have := min_le_right ⌊(s - n) / h⌋₊ (K - 1); omega

lemma idx_mono (n h : ℝ) (K : ℕ) (hh : 0 < h) {s t : ℝ} (hst : s ≤ t) :
    idx n h K s ≤ idx n h K t := by
  unfold idx
  apply min_le_min_right
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ hh.le
  linarith

lemma idx_le (n h : ℝ) (K : ℕ) (hh : 0 < h) (s : ℝ) (hs : n ≤ s) :
    n + (idx n h K s : ℝ) * h ≤ s := by
  have h1 : ((idx n h K s : ℕ) : ℝ) ≤ (⌊(s - n) / h⌋₊ : ℝ) := by
    exact_mod_cast min_le_left _ _
  have h2 : (⌊(s - n) / h⌋₊ : ℝ) ≤ (s - n) / h := Nat.floor_le (div_nonneg (by linarith) hh.le)
  have h3 : ((idx n h K s : ℕ) : ℝ) * h ≤ s - n := by
    rw [← le_div_iff₀ hh]; exact h1.trans h2
  linarith

lemma le_idx (n h : ℝ) (K : ℕ) (hK : 1 ≤ K) (hh : 0 < h) (hKh : (K : ℝ) * h = 1)
    (s : ℝ) (hs : s ≤ n + 1) :
    s ≤ n + ((idx n h K s : ℝ) + 1) * h := by
  unfold idx
  rcases le_or_gt ⌊(s - n) / h⌋₊ (K - 1) with hle | hlt
  · rw [min_eq_left hle]
    have h2 : (s - n) / h < ⌊(s - n) / h⌋₊ + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hh] at h2
    linarith
  · rw [min_eq_right hlt.le]
    have : ((K - 1 : ℕ) : ℝ) + 1 = K := by
      rw [Nat.cast_sub hK]; push_cast; ring
    rw [this, hKh]; linarith

lemma mem_Jset_of_between (n h : ℝ) (hh : 0 < h) (i : ℕ) (s : ℝ)
    (h1 : n + i * h ≤ s) (h2 : s ≤ n + (i + 1) * h) : s ∈ Jset n h i := by
  unfold Jset
  constructor <;> nlinarith

lemma Zf_le_Tf (D : Set TimePair) (c h : ℝ) (K : ℕ) (l : ℕ) (hl : l < K)
    (f : TimePair → ℝ) : Zf D c h l f ≤ Tf D c h K f :=
  Finset.single_le_sum (f := fun l => Zf D c h l f) (fun _ _ => zero_le)
    (Finset.mem_range.2 hl)

lemma sum_Zf_le_Tf (D : Set TimePair) (c h : ℝ) (K : ℕ) (i j : ℕ) (hj : j ≤ K)
    (f : TimePair → ℝ) : ∑ l ∈ Finset.Ico i j, Zf D c h l f ≤ Tf D c h K f := by
  apply Finset.sum_le_sum_of_subset
  intro l hl
  simp only [Finset.mem_Ico] at hl
  simp only [Finset.mem_range]; omega

/-- the key separability bound: a real pair inside the open window is bounded by the
countable supremum over the shifted-back separating set. -/
lemma ofReal_abs_le_Zf (x : ℝ → ℝ → S → ℝ) (D : Set TimePair) (N : Set S)
    (hsepN : ∀ ω : S, ω ∉ N → ∀ p : TimePair,
      ∃ q : ℕ → TimePair, (∀ n, q n ∈ D) ∧ Tendsto q atTop (𝓝 p) ∧
        Tendsto (fun n => x (q n).1.1 (q n).1.2 ω) atTop (𝓝 (x p.1.1 p.1.2 ω)))
    (c h : ℝ) (hh : 0 < h) (hch : h ≤ c) (m : ℕ) (l : ℕ) (ω : S) (hω : ω ∉ N)
    (u v : ℝ) (hu : u ∈ Jset (c + m) h l) (hv : v ∈ Jset (c + m) h l) (huv : u < v) :
    ENNReal.ofReal |x u v ω| ≤ Zf D c h l (Xsh x m ω) := by
  have hu' : c + m + l * h - h < u ∧ u < c + m + l * h + 2 * h := hu
  have hv' : c + m + l * h - h < v ∧ v < c + m + l * h + 2 * h := hv
  have hl0 : (0 : ℝ) ≤ l * h := mul_nonneg (Nat.cast_nonneg l) hh.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hu0 : 0 ≤ u := by linarith
  obtain ⟨q, hqD, hqlim, hxlim⟩ := hsepN ω hω ⟨(u, v), hu0, huv⟩
  have h1 : Tendsto (fun j => (q j).1.1) atTop (𝓝 u) :=
    ((continuous_fst.comp continuous_subtype_val).tendsto _).comp hqlim
  have h2 : Tendsto (fun j => (q j).1.2) atTop (𝓝 v) :=
    ((continuous_snd.comp continuous_subtype_val).tendsto _).comp hqlim
  have e1 : ∀ᶠ j in atTop, (q j).1.1 ∈ Set.Ioo (c + m + l * h - h) (c + m + l * h + 2 * h) :=
    h1.eventually (Ioo_mem_nhds hu'.1 hu'.2)
  have e2 : ∀ᶠ j in atTop, (q j).1.2 ∈ Set.Ioo (c + m + l * h - h) (c + m + l * h + 2 * h) :=
    h2.eventually (Ioo_mem_nhds hv'.1 hv'.2)
  have hlim : Tendsto (fun j => ENNReal.ofReal |x (q j).1.1 (q j).1.2 ω|) atTop
      (𝓝 (ENNReal.ofReal |x u v ω|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp hxlim)
  refine le_of_tendsto hlim ?_
  filter_upwards [e1, e2] with j hj1 hj2
  have hj1' : c + m + l * h - h < (q j).1.1 ∧ (q j).1.1 < c + m + l * h + 2 * h := hj1
  have hj2' : c + m + l * h - h < (q j).1.2 ∧ (q j).1.2 < c + m + l * h + 2 * h := hj2
  have hq0 : 0 ≤ (q j).1.1 - m := by linarith
  have hqlt : (q j).1.1 - m < (q j).1.2 - m := by linarith [(q j).2.2]
  let r : TimePair := ⟨((q j).1.1 - m, (q j).1.2 - m), hq0, hqlt⟩
  have hr : r ∈ Dsh D ∧ r.1.1 ∈ Jset c h l ∧ r.1.2 ∈ Jset c h l := by
    refine ⟨⟨q j, hqD j, m, by simp [r], by simp [r]⟩, ?_, ?_⟩
    · show c + l * h - h < (q j).1.1 - m ∧ (q j).1.1 - m < c + l * h + 2 * h
      constructor <;> linarith
    · show c + l * h - h < (q j).1.2 - m ∧ (q j).1.2 - m < c + l * h + 2 * h
      constructor <;> linarith
  have := le_iSup (fun q : Qidx D c h l => ENNReal.ofReal |Xsh x m ω q.1|) ⟨r, hr⟩
  simpa [Xsh, r, Zf] using this

lemma ofReal_xt_le_Zf (x : ℝ → ℝ → S → ℝ) (D : Set TimePair) (N : Set S)
    (hsepN : ∀ ω : S, ω ∉ N → ∀ p : TimePair,
      ∃ q : ℕ → TimePair, (∀ n, q n ∈ D) ∧ Tendsto q atTop (𝓝 p) ∧
        Tendsto (fun n => x (q n).1.1 (q n).1.2 ω) atTop (𝓝 (x p.1.1 p.1.2 ω)))
    (c h : ℝ) (hh : 0 < h) (hch : h ≤ c) (m : ℕ) (l : ℕ) (ω : S) (hω : ω ∉ N)
    (u v : ℝ) (hu : u ∈ Jset (c + m) h l) (hv : v ∈ Jset (c + m) h l) :
    ENNReal.ofReal (xt x u v ω) ≤ Zf D c h l (Xsh x m ω) := by
  by_cases huv : u < v
  · rw [xt_of_lt x ω huv]
    exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
      (ofReal_abs_le_Zf x D N hsepN c h hh hch m l ω hω u v hu hv huv)
  · simp [xt, huv]

/-- upper chain bound -/
lemma ofReal_xt_le_three (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (D : Set TimePair) (N : Set S)
    (hsepN : ∀ ω : S, ω ∉ N → ∀ p : TimePair,
      ∃ q : ℕ → TimePair, (∀ n, q n ∈ D) ∧ Tendsto q atTop (𝓝 p) ∧
        Tendsto (fun n => x (q n).1.1 (q n).1.2 ω) atTop (𝓝 (x p.1.1 p.1.2 ω)))
    (c h : ℝ) (K : ℕ) (hK : 1 ≤ K) (hh : 0 < h) (hKh : (K : ℝ) * h = 1) (hch : h ≤ c)
    (m : ℕ) (ω : S) (hω : ω ∉ N)
    (s t : ℝ) (hs : c + m ≤ s) (hst : s ≤ t) (ht : t ≤ c + m + 1) :
    ENNReal.ofReal (xt x s t ω) ≤ 3 * Tf D c h K (Xsh x m ω) := by
  set n : ℝ := c + m with hn
  set f := Xsh x m ω with hf
  have hn0 : 0 ≤ n := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hij : idx n h K s ≤ idx n h K t := idx_mono n h K hh hst
  have hiK : idx n h K s < K := idx_lt n h K hK s
  have hjK : idx n h K t < K := idx_lt n h K hK t
  have hs1 : n + idx n h K s * h ≤ s := idx_le n h K hh s hs
  have hs2 : s ≤ n + (idx n h K s + 1) * h := le_idx n h K hK hh hKh s (by linarith)
  have ht1 : n + idx n h K t * h ≤ t := idx_le n h K hh t (by linarith)
  have ht2 : t ≤ n + (idx n h K t + 1) * h := le_idx n h K hK hh hKh t ht
  generalize hi : idx n h K s = i at hij hiK hs1 hs2
  generalize hj : idx n h K t = j at hij hjK ht1 ht2
  have hT3 : Tf D c h K f ≤ 3 * Tf D c h K f :=
    le_mul_of_one_le_left zero_le (by norm_num)
  have hsJ : s ∈ Jset n h i := mem_Jset_of_between n h hh i s hs1 hs2
  have htJ : t ∈ Jset n h j := mem_Jset_of_between n h hh j t ht1 ht2
  rcases hij.lt_or_eq with hlt | heq
  · -- chain through the grid points e l = n + l h
    set e : ℕ → ℝ := fun l => n + l * h with he
    have hmono : Monotone e := by
      intro l l' hll'
      simp only [he]
      have : (l : ℝ) ≤ l' := by exact_mod_cast hll'
      nlinarith
    have he0 : 0 ≤ e 0 := by simp [he, hn0]
    have hsE : s ≤ e (i + 1) := by simp only [he]; push_cast; linarith
    have hEt : e j ≤ t := ht1
    have hE1 : e (i + 1) ≤ e j := hmono hlt
    have hA := xt_sub P x hproc s (e (i + 1)) t (by linarith) hsE (hE1.trans hEt) ω
    have hB := xt_sub P x hproc (e (i + 1)) (e j) t (he0.trans (hmono (Nat.zero_le _)))
      hE1 hEt ω
    have hC := xt_chain P x hproc e he0 hmono ω (i + 1) j hlt
    have hreal : xt x s t ω ≤ xt x s (e (i + 1)) ω +
        (∑ l ∈ Finset.Ico (i + 1) j, xt x (e l) (e (l + 1)) ω) + xt x (e j) t ω := by
      linarith
    have hgrid : ∀ l, e l ∈ Jset n h l ∧ e (l + 1) ∈ Jset n h l := by
      intro l
      constructor
      · exact mem_Jset_of_between n h hh l (e l) le_rfl (by simp only [he]; nlinarith)
      · exact mem_Jset_of_between n h hh l (e (l + 1)) (by simp only [he]; push_cast; nlinarith)
          (by simp only [he]; push_cast; linarith)
    have hEi : e (i + 1) ∈ Jset n h i :=
      mem_Jset_of_between n h hh i (e (i + 1)) (by simp only [he]; push_cast; nlinarith)
        (by simp only [he]; push_cast; linarith)
    have hEj : e j ∈ Jset n h j :=
      mem_Jset_of_between n h hh j (e j) le_rfl (by simp only [he]; nlinarith)
    calc ENNReal.ofReal (xt x s t ω)
        ≤ ENNReal.ofReal (xt x s (e (i + 1)) ω +
            (∑ l ∈ Finset.Ico (i + 1) j, xt x (e l) (e (l + 1)) ω) + xt x (e j) t ω) :=
          ENNReal.ofReal_le_ofReal hreal
      _ ≤ ENNReal.ofReal (xt x s (e (i + 1)) ω) +
            ENNReal.ofReal (∑ l ∈ Finset.Ico (i + 1) j, xt x (e l) (e (l + 1)) ω) +
            ENNReal.ofReal (xt x (e j) t ω) :=
          ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
      _ ≤ Zf D c h i f + (∑ l ∈ Finset.Ico (i + 1) j, Zf D c h l f) + Zf D c h j f := by
          gcongr
          · exact ofReal_xt_le_Zf x D N hsepN c h hh hch m i ω hω s _ hsJ hEi
          · refine (ofReal_sum_le' _ _).trans (Finset.sum_le_sum fun l _ => ?_)
            exact ofReal_xt_le_Zf x D N hsepN c h hh hch m l ω hω _ _ (hgrid l).1 (hgrid l).2
          · exact ofReal_xt_le_Zf x D N hsepN c h hh hch m j ω hω _ _ hEj htJ
      _ ≤ Tf D c h K f + Tf D c h K f + Tf D c h K f := by
          gcongr
          · exact Zf_le_Tf D c h K i hiK f
          · exact sum_Zf_le_Tf D c h K (i + 1) j hjK.le f
          · exact Zf_le_Tf D c h K j hjK f
      _ = 3 * Tf D c h K f := by ring
  · subst heq
    calc ENNReal.ofReal (xt x s t ω) ≤ Zf D c h i f :=
          ofReal_xt_le_Zf x D N hsepN c h hh hch m i ω hω s t hsJ htJ
      _ ≤ Tf D c h K f := Zf_le_Tf D c h K i hiK f
      _ ≤ 3 * Tf D c h K f := hT3

/-- the pointwise oscillation bound -/
lemma osc_le_Psi (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (D : Set TimePair) (N : Set S)
    (hsepN : ∀ ω : S, ω ∉ N → ∀ p : TimePair,
      ∃ q : ℕ → TimePair, (∀ n, q n ∈ D) ∧ Tendsto q atTop (𝓝 p) ∧
        Tendsto (fun n => x (q n).1.1 (q n).1.2 ω) atTop (𝓝 (x p.1.1 p.1.2 ω)))
    (c h : ℝ) (K : ℕ) (hK : 1 ≤ K) (hh : 0 < h) (hKh : (K : ℝ) * h = 1) (hch : h ≤ c)
    (hc : 0 ≤ c) (m : ℕ) (ω : S) (hω : ω ∉ N) :
    oscillation x (Set.Icc (c + m) (c + m + 1)) ω ≤ Psi D c h K hc (Xsh x m ω) := by
  set n : ℝ := c + m with hn
  set f := Xsh x m ω with hf
  have hn0 : 0 ≤ n := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hPsi : Psi D c h K hc f = ENNReal.ofReal |x n (n + 1) ω| + 9 * Tf D c h K f := by
    simp only [Psi, hf, Xsh, hn]
    congr 3
    ring
  rw [hPsi]
  unfold oscillation
  refine iSup₂_le fun p hp => ?_
  have hp1 : n ≤ p.1.1 ∧ p.1.1 ≤ n + 1 := hp.1
  have hp2 : n ≤ p.1.2 ∧ p.1.2 ≤ n + 1 := hp.2
  have hlt := p.2.2
  have hup := ofReal_xt_le_three P x hproc D N hsepN c h K hK hh hKh hch m ω hω
    p.1.1 p.1.2 hp1.1 hlt.le hp2.2
  have h1 := ofReal_xt_le_three P x hproc D N hsepN c h K hK hh hKh hch m ω hω
    n p.1.1 le_rfl hp1.1 hp1.2
  have h2 := ofReal_xt_le_three P x hproc D N hsepN c h K hK hh hKh hch m ω hω
    p.1.2 (n + 1) hp2.1 hp2.2 le_rfl
  have hA := xt_sub P x hproc n p.1.1 (n + 1) hn0 hp1.1 hp1.2 ω
  have hB := xt_sub P x hproc p.1.1 p.1.2 (n + 1) (hn0.trans hp1.1) hlt.le hp2.2 ω
  have hxt : xt x n (n + 1) ω = x n (n + 1) ω := xt_of_lt x ω (by linarith)
  have hxt2 : xt x p.1.1 p.1.2 ω = x p.1.1 p.1.2 ω := xt_of_lt x ω hlt
  have hlow : -(x p.1.1 p.1.2 ω) ≤ xt x n p.1.1 ω + xt x p.1.2 (n + 1) ω + |x n (n + 1) ω| := by
    rw [hxt] at hA; rw [hxt2] at hB
    have := neg_abs_le (x n (n + 1) ω)
    linarith
  calc ENNReal.ofReal |x p.1.1 p.1.2 ω|
      ≤ ENNReal.ofReal (x p.1.1 p.1.2 ω) + ENNReal.ofReal (-(x p.1.1 p.1.2 ω)) :=
        ofReal_abs_le_add _
    _ ≤ 3 * Tf D c h K f + (ENNReal.ofReal (xt x n p.1.1 ω) +
          ENNReal.ofReal (xt x p.1.2 (n + 1) ω) + ENNReal.ofReal |x n (n + 1) ω|) := by
        gcongr
        · rw [← hxt2]; exact hup
        · exact (ENNReal.ofReal_le_ofReal hlow).trans
            (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl))
    _ ≤ 3 * Tf D c h K f + (3 * Tf D c h K f + 3 * Tf D c h K f +
          ENNReal.ofReal |x n (n + 1) ω|) := by gcongr
    _ = ENNReal.ofReal |x n (n + 1) ω| + 9 * Tf D c h K f := by ring


theorem oscillation_vanishes_core (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (hsep : IsSeparable P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    (∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω /
        (n : ENNReal)) atTop (𝓝 0)) ∧
    Tendsto (fun n : ℕ =>
      ∫⁻ ω, oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω /
        (n : ENNReal) ∂P) atTop (𝓝 0) := by
  obtain ⟨D, N, hD, -, hNmeas, hN0, hsepN⟩ := hsep
  obtain ⟨hoscm, hoscfin⟩ := hosc
  -- constants
  have hδpos : 0 < b - a := by linarith
  set a' := a + (b - a) / 4 with ha'
  set K : ℕ := ⌈6 / (b - a)⌉₊ + 1 with hKdef
  have hK : 1 ≤ K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set h : ℝ := 1 / K with hhdef
  have hh : 0 < h := by positivity
  have hKh : (K : ℝ) * h = 1 := by rw [hhdef]; field_simp
  have hh1 : h ≤ 1 := by rw [hhdef, div_le_one hKpos]; exact_mod_cast hK
  have hK6 : 6 / (b - a) ≤ K := by
    have := Nat.le_ceil (6 / (b - a))
    rw [hKdef]; push_cast; linarith
  have h3h : 3 * h ≤ (b - a) / 2 := by
    rw [div_le_iff₀ hδpos] at hK6
    rw [hhdef, show 3 * (1 / (K : ℝ)) = 3 / K by ring, div_le_iff₀ hKpos]
    nlinarith
  set c₀ : ℕ := ⌈a'⌉₊ + 1 with hc₀
  set c : ℝ := (c₀ : ℝ) with hcdef
  have hc1 : a' + 1 ≤ c := by
    have := Nat.le_ceil a'
    rw [hcdef, hc₀]; push_cast; linarith
  have ha'0 : 0 ≤ a' := by linarith
  have hc : 0 ≤ c := by linarith
  have hch : h ≤ c := by linarith
  -- the reference variable
  set Y₀ : S → ENNReal := fun ω => Psi D c h K hc (X0 x ω) with hY₀
  have hY₀m : Measurable Y₀ :=
    (measurable_Psi hD c h K hc).comp (measurable_X0 P x hproc)
  -- its integral is finite
  have hfin : ∫⁻ ω, Y₀ ω ∂P < ⊤ := by
    have hint : Integrable (x c (c + 1)) P := by
      have := (shift_coord P x hproc 0 1 c le_rfl one_pos hc).1.2 (hproc.2.2.2.1 1 one_pos)
      rwa [zero_add, add_comm 1 c] at this
    have hmeas1 : Measurable fun ω =>
        ENNReal.ofReal |X0 x ω ⟨(c, c + 1), hc, by linarith⟩| :=
      (measurable_eval_abs _).comp (measurable_X0 P x hproc)
    have h1 : ∫⁻ ω, ENNReal.ofReal |X0 x ω ⟨(c, c + 1), hc, by linarith⟩| ∂P < ⊤ := by
      have := hint.hasFiniteIntegral
      unfold HasFiniteIntegral at this
      change ∫⁻ ω, ENNReal.ofReal |x c (c + 1) ω| ∂P < ⊤
      simpa [← ofReal_norm, Real.norm_eq_abs] using this
    have h2 : ∀ l ∈ Finset.range K, ∫⁻ ω, Zf D c h l (X0 x ω) ∂P < ⊤ := by
      intro l hl
      have hlK : l < K := Finset.mem_range.1 hl
      have hlh : (l : ℝ) * h ≤ 1 - h := by
        have : (l : ℝ) + 1 ≤ K := by exact_mod_cast hlK
        nlinarith
      have hl0 : (0 : ℝ) ≤ l * h := by positivity
      have hτ0 : 0 ≤ c + l * h - h - a' := by linarith
      have hτle : c + l * h - h - a' ≤ c + l * h - h := by linarith
      have hZ : ∫⁻ ω, Zf D c h l (X0 x ω) ∂P =
          ∫⁻ ω, Zback D c h l (c + l * h - h - a') hτle (X0 x ω) ∂P := by
        rw [← lintegral_Xsh P x hproc _ hτ0 _ (measurable_Zback hD c h l _ hτle)]
        simp_rw [Zback_Xsh]
      rw [hZ]
      refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hoscfin
      unfold Zback
      refine iSup_le fun q => ?_
      have hq1 : c + l * h - h < q.1.1.1 ∧ q.1.1.1 < c + l * h + 2 * h := q.2.2.1
      have hq2 : c + l * h - h < q.1.1.2 ∧ q.1.1.2 < c + l * h + 2 * h := q.2.2.2
      exact ofReal_abs_le_osc x _ ω _ _ (by linarith) (by linarith [q.1.2.2])
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    have hmeasZ : ∀ l, Measurable fun ω => Zf D c h l (X0 x ω) := fun l =>
      (measurable_Zf hD c h l).comp (measurable_X0 P x hproc)
    have hcalc : ∫⁻ ω, Y₀ ω ∂P =
        ∫⁻ ω, ENNReal.ofReal |X0 x ω ⟨(c, c + 1), hc, by linarith⟩| ∂P +
          9 * ∑ l ∈ Finset.range K, ∫⁻ ω, Zf D c h l (X0 x ω) ∂P := by
      simp only [hY₀, Psi, Tf]
      rw [lintegral_add_left hmeas1,
        lintegral_const_mul _ (Finset.measurable_sum _ fun l _ => hmeasZ l),
        lintegral_finsetSum _ fun l _ => hmeasZ l]
    rw [hcalc]
    refine ENNReal.add_lt_top.2 ⟨h1, ENNReal.mul_lt_top (by simp) ?_⟩
    exact ENNReal.sum_lt_top.2 h2
  -- the shifted variables
  set Y : ℕ → S → ENNReal := fun m ω => Psi D c h K hc (Xsh x m ω) with hYdef
  have hYm : ∀ m, Measurable (Y m) := fun m =>
    (measurable_Psi hD c h K hc).comp (measurable_Xsh P x hproc m (Nat.cast_nonneg m))
  have hYint : ∀ m, ∫⁻ ω, Y m ω ∂P = ∫⁻ ω, Y₀ ω ∂P := fun m =>
    lintegral_Xsh P x hproc m (Nat.cast_nonneg m) _ (measurable_Psi hD c h K hc)
  have hYmeasure : ∀ m (r : ENNReal), P {ω | r < Y m ω} = P {ω | r < Y₀ ω} := fun m r =>
    measure_Xsh P x hproc m (Nat.cast_nonneg m) {f | r < Psi D c h K hc f}
      (measurableSet_lt measurable_const (measurable_Psi hD c h K hc))
  -- pointwise bound
  have hbound : ∀ ω, ω ∉ N → ∀ n : ℕ, c₀ ≤ n →
      oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω ≤ Y (n - c₀) ω := by
    intro ω hω n hn
    have hcast : (n : ℝ) = c + ((n - c₀ : ℕ) : ℝ) := by
      rw [hcdef, Nat.cast_sub hn]; ring
    rw [hcast]
    exact osc_le_Psi P x hproc D N hsepN c h K hK hh hKh hch hc (n - c₀) ω hω
  have haeN : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]; simpa using hN0
  have hBC : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      ¬ (ENNReal.ofReal ((1 / ((j : ℝ) + 1)) * n) < Y (n - c₀) ω) := by
    intro j
    have hε : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hsum := tsum_measure_gt_lt_top P Y₀ hY₀m hfin _ hε
    have : ∑' n : ℕ, P {ω | ENNReal.ofReal ((1 / ((j : ℝ) + 1)) * n) < Y (n - c₀) ω} < ⊤ := by
      simp_rw [hYmeasure]; exact hsum
    exact ae_eventually_notMem this.ne
  have hae : ∀ᵐ ω ∂P, ω ∉ N ∧ ∀ j : ℕ, ∀ᶠ n : ℕ in atTop,
      ¬ (ENNReal.ofReal ((1 / ((j : ℝ) + 1)) * n) < Y (n - c₀) ω) :=
    haeN.and (ae_all_iff.2 hBC)
  constructor
  · filter_upwards [hae] with ω hω
    obtain ⟨hωN, hωj⟩ := hω
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · exact Eventually.of_forall fun _ => le_top
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hεr
    filter_upwards [hωj j, eventually_ge_atTop c₀, eventually_ge_atTop 1] with n hn hnc hn1
    have hn' := not_lt.1 hn
    have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hntop : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
    calc oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω / n ≤ Y (n - c₀) ω / n :=
          ENNReal.div_le_div_right (hbound ω hωN n hnc) _
      _ ≤ ENNReal.ofReal ((1 / ((j : ℝ) + 1)) * n) / n := ENNReal.div_le_div_right hn' _
      _ = ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.mul_div_cancel_right hn0 hntop]
      _ ≤ ε := by rw [ENNReal.ofReal_le_iff_le_toReal hεtop]; exact hj.le
  · have hup : ∀ n : ℕ, c₀ ≤ n →
        ∫⁻ ω, oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω / n ∂P ≤
          (∫⁻ ω, Y₀ ω ∂P) * (n : ENNReal)⁻¹ := by
      intro n hn
      calc ∫⁻ ω, oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω / n ∂P
          ≤ ∫⁻ ω, Y (n - c₀) ω / n ∂P := by
            apply lintegral_mono_ae
            filter_upwards [haeN] with ω hω
            exact ENNReal.div_le_div_right (hbound ω hω n hn) _
        _ = (∫⁻ ω, Y (n - c₀) ω ∂P) * (n : ENNReal)⁻¹ := by
            simp_rw [div_eq_mul_inv]; exact lintegral_mul_const _ (hYm _)
        _ = _ := by rw [hYint]
    have hlim : Tendsto (fun n : ℕ => (∫⁻ ω, Y₀ ω ∂P) * (n : ENNReal)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ∫⁻ ω, Y₀ ω ∂P)
        ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hfin.ne)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => zero_le) ?_
    filter_upwards [eventually_ge_atTop c₀] with n hn
    exact hup n hn

end KingmanSubadditive.Continuous

open KingmanSubadditive.Continuous
open MeasureTheory Filter Topology

theorem solution {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (hsep : IsSeparable P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    (∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω /
        (n : ENNReal)) atTop (𝓝 0)) ∧
    Tendsto (fun n : ℕ =>
      ∫⁻ ω, oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω /
        (n : ENNReal) ∂P) atTop (𝓝 0) := by
  exact oscillation_vanishes_core P x hproc hsep a b ha hab hosc
