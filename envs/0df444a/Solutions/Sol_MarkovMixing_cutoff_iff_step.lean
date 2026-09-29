-- Prove2me | solution 1 for MarkovMixing.cutoff_iff_step
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T20:27:56.551545+00:00
-- url     : https://prove2.me/submissions/f2818133-687e-4fee-810f-cd2ca8279a3f

import Definitions.Def_mm_cutoff
import Theorems.Thm_MarkovMixing_tv_eq_half_l1
import Theorems.Thm_MarkovMixing_convergence_theorem
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open scoped BigOperators
open MarkovMixing

namespace CutStep

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

lemma pow_row_sum {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x : V), ∑ y, (P ^ t) x y = 1 := by
  intro t
  induction t with
  | zero => intro x; simp [Matrix.one_apply]
  | succ t ih =>
    intro x
    have : ∀ y : V, (P ^ (t + 1)) x y = ∑ z, (P ^ t) x z * P z y := by
      intro y; rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_comm]
    have e : ∀ z : V, ∑ y, (P ^ t) x z * P z y = (P ^ t) x z := by
      intro z; rw [← Finset.mul_sum, hP.2 z, mul_one]
    rw [Finset.sum_congr rfl (fun z _ => e z), ih x]

lemma rowDist_isDist {P : Matrix V V ℝ} (hP : IsStochastic P) (t : ℕ) (x : V) :
    IsDist (rowDist P t x) :=
  ⟨fun y => pow_entry_nonneg hP t x y, pow_row_sum hP t x⟩

lemma tvDist_nonneg (μ ν : V → ℝ) : 0 ≤ tvDist μ ν := by
  have hb : BddAbove (Set.range fun B : Finset V => |∑ x ∈ B, μ x - ∑ x ∈ B, ν x|) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have := le_ciSup hb (∅ : Finset V)
  simp only [Finset.sum_empty, sub_zero, abs_zero] at this
  exact this

lemma le_tvDist (μ ν : V → ℝ) (A : Finset V) :
    |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ tvDist μ ν := by
  have hb : BddAbove (Set.range fun B : Finset V => |∑ x ∈ B, μ x - ∑ x ∈ B, ν x|) :=
    Set.Finite.bddAbove (Set.finite_range _)
  exact le_ciSup hb A

lemma tvDist_le_one {μ ν : V → ℝ} (hμ : IsDist μ) (hν : IsDist ν) :
    tvDist μ ν ≤ 1 := by
  rw [(MarkovMixing.tv_eq_half_l1 μ ν hμ hν).1]
  have h : ∑ x, |μ x - ν x| ≤ ∑ x, (μ x + ν x) := by
    refine Finset.sum_le_sum fun x _ => ?_
    rcases abs_cases (μ x - ν x) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; linarith [hν.1 x]
    · rw [he]; linarith [hμ.1 x]
  rw [Finset.sum_add_distrib, hμ.2, hν.2] at h
  linarith

/-- The one-step contraction of the `ℓ¹` distance under a stochastic matrix. -/
lemma tvDist_step {P : Matrix V V ℝ} (hP : IsStochastic P) {π : V → ℝ}
    (hπ : IsStationary P π) (t : ℕ) (x : V) :
    tvDist (rowDist P (t + 1) x) π ≤ tvDist (rowDist P t x) π := by
  have hd1 := rowDist_isDist hP (t + 1) x
  have hd2 := rowDist_isDist hP t x
  rw [(MarkovMixing.tv_eq_half_l1 _ _ hd1 hπ.1).1,
    (MarkovMixing.tv_eq_half_l1 _ _ hd2 hπ.1).1]
  have hcol : ∀ y : V, ∑ z, π z * P z y = π y := fun y => congrFun hπ.2 y
  have hstep : ∀ y : V, |(P ^ (t + 1)) x y - π y| ≤ ∑ z, |(P ^ t) x z - π z| * P z y := by
    intro y
    have e1 : (P ^ (t + 1)) x y = ∑ z, (P ^ t) x z * P z y := by
      rw [pow_succ, Matrix.mul_apply]
    have e2 : (P ^ (t + 1)) x y - π y = ∑ z, ((P ^ t) x z - π z) * P z y := by
      rw [e1, ← hcol y, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [e2]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun z _ => ?_
    rw [abs_mul, abs_of_nonneg (hP.1 z y)]
  have hsum : ∑ y, |(P ^ (t + 1)) x y - π y| ≤ ∑ z, |(P ^ t) x z - π z| := by
    refine le_trans (Finset.sum_le_sum fun y _ => hstep y) ?_
    rw [Finset.sum_comm]
    refine le_of_eq (Finset.sum_congr rfl fun z _ => ?_)
    rw [← Finset.mul_sum, hP.2 z, mul_one]
  have hgoal : ∑ y, |rowDist P (t + 1) x y - π y| ≤ ∑ y, |rowDist P t x y - π y| := hsum
  show 2⁻¹ * ∑ y, |rowDist P (t + 1) x y - π y| ≤ 2⁻¹ * ∑ y, |rowDist P t x y - π y|
  linarith

lemma le_distStationary (P : Matrix V V ℝ) (π : V → ℝ) (t : ℕ) (x : V) :
    tvDist (rowDist P t x) π ≤ distStationary P π t := by
  have hb : BddAbove (Set.range fun y : V => tvDist (rowDist P t y) π) :=
    Set.Finite.bddAbove (Set.finite_range _)
  exact le_ciSup hb x

lemma distStationary_le [Nonempty V] {P : Matrix V V ℝ} {π : V → ℝ} {t : ℕ} {c : ℝ}
    (h : ∀ x : V, tvDist (rowDist P t x) π ≤ c) : distStationary P π t ≤ c :=
  ciSup_le h

lemma distStationary_nonneg [Nonempty V] (P : Matrix V V ℝ) (π : V → ℝ) (t : ℕ) :
    0 ≤ distStationary P π t :=
  le_trans (tvDist_nonneg _ _) (le_distStationary P π t (Classical.arbitrary V))

lemma distStationary_le_one [Nonempty V] {P : Matrix V V ℝ} (hP : IsStochastic P)
    {π : V → ℝ} (hπ : IsStationary P π) (t : ℕ) : distStationary P π t ≤ 1 :=
  distStationary_le fun x => tvDist_le_one (rowDist_isDist hP t x) hπ.1

lemma distStationary_succ_le [Nonempty V] {P : Matrix V V ℝ} (hP : IsStochastic P)
    {π : V → ℝ} (hπ : IsStationary P π) (t : ℕ) :
    distStationary P π (t + 1) ≤ distStationary P π t :=
  distStationary_le fun x =>
    le_trans (tvDist_step hP hπ t x) (le_distStationary P π t x)

/-- `d(t)` is non-increasing. -/
lemma distStationary_anti [Nonempty V] {P : Matrix V V ℝ} (hP : IsStochastic P)
    {π : V → ℝ} (hπ : IsStationary P π) {s t : ℕ} (hst : s ≤ t) :
    distStationary P π t ≤ distStationary P π s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction k with
  | zero => simp
  | succ k ih =>
    have he : s + (k + 1) = (s + k) + 1 := by ring
    rw [he]
    exact le_trans (distStationary_succ_le hP hπ (s + k)) ih

/-- Under irreducibility and aperiodicity the chain really does come within
`ε` of stationarity, so `mixingTime` is not the junk value of an empty
infimum. -/
lemma target_nonempty [Nonempty V] {P : Matrix V V ℝ} (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (hap : Aperiodic P) {π : V → ℝ}
    (hπ : IsStationary P π) {ε : ℝ} (hε : 0 < ε) :
    {t : ℕ | distStationary P π t ≤ ε}.Nonempty := by
  obtain ⟨α, hα, C, hC, hbd⟩ :=
    MarkovMixing.convergence_theorem P hP hirr hap π hπ
  obtain ⟨t, ht⟩ : ∃ t : ℕ, C * α ^ t < ε := by
    have hlim : Filter.Tendsto (fun t : ℕ => C * α ^ t) Filter.atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hα.1) hα.2
      simpa using this.const_mul C
    have := (Metric.tendsto_nhds.mp hlim) ε hε
    obtain ⟨t, ht⟩ := this.exists
    refine ⟨t, ?_⟩
    have : |C * α ^ t| < ε := by simpa [Real.dist_eq] using ht
    exact lt_of_abs_lt this
  exact ⟨t, le_trans (hbd t) ht.le⟩

lemma mixingTime_spec [Nonempty V] {P : Matrix V V ℝ} (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (hap : Aperiodic P) {π : V → ℝ}
    (hπ : IsStationary P π) {ε : ℝ} (hε : 0 < ε) :
    distStationary P π (mixingTime P π ε) ≤ ε :=
  Nat.sInf_mem (target_nonempty hP hirr hap hπ hε)

lemma mixingTime_le {P : Matrix V V ℝ} {π : V → ℝ} {ε : ℝ} {t : ℕ}
    (h : distStationary P π t ≤ ε) : mixingTime P π ε ≤ t :=
  Nat.sInf_le h

/-- Past the mixing time the distance stays below the target. -/
lemma dist_le_of_mixingTime_le [Nonempty V] {P : Matrix V V ℝ} (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (hap : Aperiodic P) {π : V → ℝ}
    (hπ : IsStationary P π) {ε : ℝ} (hε : 0 < ε) {t : ℕ} (ht : mixingTime P π ε ≤ t) :
    distStationary P π t ≤ ε :=
  le_trans (distStationary_anti hP hπ ht) (mixingTime_spec hP hirr hap hπ hε)

/-- `t_mix(ε)` is antitone in `ε`. -/
lemma mixingTime_anti [Nonempty V] {P : Matrix V V ℝ} (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (hap : Aperiodic P) {π : V → ℝ}
    (hπ : IsStationary P π) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    mixingTime P π b ≤ mixingTime P π a :=
  mixingTime_le (le_trans (mixingTime_spec hP hirr hap hπ ha) hab)

end CutStep

open CutStep

theorem solution {V : ℕ → Type*} [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)] [∀ n, Nonempty (V n)]
    (P : ∀ n, Matrix (V n) (V n) ℝ) (π : ∀ n, V n → ℝ)
    (hP : ∀ n, MarkovMixing.IsStochastic (P n))
    (hirr : ∀ n, MarkovMixing.Irreducible (P n))
    (hap : ∀ n, MarkovMixing.Aperiodic (P n))
    (hπ : ∀ n, MarkovMixing.IsStationary (P n) (π n)) :
    MarkovMixing.HasCutoff P π ↔
      ∀ c : ℝ, 0 < c →
        (c < 1 → Filter.Tendsto
          (fun n => MarkovMixing.distStationary (P n) (π n)
            ⌊c * MarkovMixing.tMix (P n) (π n)⌋₊) Filter.atTop (nhds 1)) ∧
        (1 < c → Filter.Tendsto
          (fun n => MarkovMixing.distStationary (P n) (π n)
            ⌊c * MarkovMixing.tMix (P n) (π n)⌋₊) Filter.atTop (nhds 0)) := by
  classical
  -- abbreviations
  set D : ∀ n : ℕ, ℕ → ℝ := fun n t => MarkovMixing.distStationary (P n) (π n) t with hD
  set M : ℕ → ℝ → ℕ := fun n e => MarkovMixing.mixingTime (P n) (π n) e with hM
  set T : ℕ → ℕ := fun n => MarkovMixing.tMix (P n) (π n) with hT
  have hTM : ∀ n, T n = M n (1 / 4) := fun n => rfl
  have hspec : ∀ (n : ℕ) (e : ℝ), 0 < e → D n (M n e) ≤ e := fun n e he =>
    mixingTime_spec (hP n) (hirr n) (hap n) (hπ n) he
  have hmono : ∀ (n s t : ℕ), s ≤ t → D n t ≤ D n s := fun n _ _ hst =>
    distStationary_anti (hP n) (hπ n) hst
  have hle1 : ∀ (n t : ℕ), D n t ≤ 1 := fun n t =>
    distStationary_le_one (hP n) (hπ n) t
  have hnn : ∀ (n t : ℕ), 0 ≤ D n t := fun n t =>
    distStationary_nonneg (P n) (π n) t
  have hMle : ∀ (n : ℕ) (e : ℝ) (t : ℕ), D n t ≤ e → M n e ≤ t := fun n e t h =>
    mixingTime_le h
  have hDle : ∀ (n : ℕ) (e : ℝ), 0 < e → ∀ t : ℕ, M n e ≤ t → D n t ≤ e :=
    fun n e he t ht => le_trans (hmono n _ _ ht) (hspec n e he)
  have hanti : ∀ (n : ℕ) (a b : ℝ), 0 < a → a ≤ b → M n b ≤ M n a :=
    fun n a b ha hab => hMle n b (M n a) (le_trans (hspec n a ha) hab)
  constructor
  · -- cutoff implies the step profile
    intro hcut
    have hratio : ∀ e : ℝ, 0 < e → e < 1 → ∀ δ : ℝ, 0 < δ →
        ∀ᶠ n in Filter.atTop, |(M n e : ℝ) / (M n (1 - e) : ℝ) - 1| < δ := by
      intro e he he1 δ hδ
      have := Metric.tendsto_nhds.mp (hcut e he he1) δ hδ
      simpa [Real.dist_eq] using this
    have hBne : ∀ e : ℝ, 0 < e → e < 1 → ∀ᶠ n in Filter.atTop, 1 ≤ M n (1 - e) := by
      intro e he he1
      filter_upwards [hratio e he he1 1 one_pos] with n hn
      rcases Nat.eq_zero_or_pos (M n (1 - e)) with h0 | hpos
      · rw [h0] at hn
        norm_num at hn
      · exact hpos
    intro c hc
    refine ⟨?_, ?_⟩
    · -- `c < 1`: the distance is eventually near `1`
      intro hc1
      rw [Metric.tendsto_nhds]
      intro δ hδ
      set d0 : ℝ := min δ (1 / 4) with hd0def
      have hd0pos : 0 < d0 := lt_min hδ (by norm_num)
      have hd0le : d0 ≤ 1 / 4 := min_le_right _ _
      have hd0δ : d0 ≤ δ := min_le_left _ _
      have hd0lt1 : d0 < 1 := by linarith
      set γ : ℝ := (1 / c - 1) / 2 with hγdef
      have hcinv : 1 < 1 / c := by
        rw [lt_div_iff₀ hc]; linarith
      have hγpos : 0 < γ := by rw [hγdef]; linarith
      have hkey : (1 + γ) * c ≤ 1 := by
        have h1 : 1 + γ < 1 / c := by rw [hγdef]; linarith
        have := (mul_lt_mul_of_pos_right h1 hc)
        rw [div_mul_cancel₀ 1 (ne_of_gt hc)] at this
        linarith
      filter_upwards [hratio d0 hd0pos hd0lt1 γ hγpos, hBne d0 hd0pos hd0lt1] with n hn hB
      have hBpos : (0 : ℝ) < (M n (1 - d0) : ℝ) := by exact_mod_cast hB
      have hAB : (M n d0 : ℝ) < (1 + γ) * (M n (1 - d0) : ℝ) := by
        have h1 : (M n d0 : ℝ) / (M n (1 - d0) : ℝ) < 1 + γ := by
          have := abs_lt.mp hn
          linarith [this.2]
        rw [div_lt_iff₀ hBpos] at h1
        linarith
      have hTA : (T n : ℝ) ≤ (M n d0 : ℝ) := by
        have : T n ≤ M n d0 := by
          rw [hTM n]
          exact hanti n d0 (1 / 4) hd0pos hd0le
        exact_mod_cast this
      have hTnn : (0 : ℝ) ≤ (T n : ℝ) := Nat.cast_nonneg _
      have hlt : c * (T n : ℝ) < (M n (1 - d0) : ℝ) := by
        have h1 : (1 + γ) * (c * (T n : ℝ)) ≤ (T n : ℝ) := by
          have := mul_le_mul_of_nonneg_right hkey hTnn
          nlinarith [hTnn]
        nlinarith [hAB, hTA, hγpos]
      have hfl : (⌊c * (T n : ℝ)⌋₊ : ℝ) ≤ c * (T n : ℝ) :=
        Nat.floor_le (by positivity)
      have hflB : ⌊c * (T n : ℝ)⌋₊ < M n (1 - d0) := by
        have : (⌊c * (T n : ℝ)⌋₊ : ℝ) < (M n (1 - d0) : ℝ) := by linarith
        exact_mod_cast this
      have hDgt : 1 - d0 < D n ⌊c * (T n : ℝ)⌋₊ := by
        by_contra hcon
        push_neg at hcon
        exact absurd (hMle n (1 - d0) _ hcon) (by omega)
      rw [Real.dist_eq]
      have := hle1 n ⌊c * (T n : ℝ)⌋₊
      rw [abs_of_nonpos (by linarith)]
      linarith
    · -- `c > 1`: the distance is eventually near `0`
      intro hc1
      rw [Metric.tendsto_nhds]
      intro δ hδ
      set d0 : ℝ := min (δ / 2) (1 / 4) with hd0def
      have hd0pos : 0 < d0 := lt_min (by linarith) (by norm_num)
      have hd0le : d0 ≤ 1 / 4 := min_le_right _ _
      have hd0δ : d0 ≤ δ / 2 := min_le_left _ _
      have hd0lt1 : d0 < 1 := by linarith
      filter_upwards [hratio d0 hd0pos hd0lt1 (c - 1) (by linarith),
        hBne d0 hd0pos hd0lt1] with n hn hB
      have hBpos : (0 : ℝ) < (M n (1 - d0) : ℝ) := by exact_mod_cast hB
      have hAB : (M n d0 : ℝ) < c * (M n (1 - d0) : ℝ) := by
        have h1 : (M n d0 : ℝ) / (M n (1 - d0) : ℝ) < c := by
          have := abs_lt.mp hn
          linarith [this.2]
        rw [div_lt_iff₀ hBpos] at h1
        linarith
      have hBT : (M n (1 - d0) : ℝ) ≤ (T n : ℝ) := by
        have : M n (1 - d0) ≤ T n := by
          rw [hTM n]
          exact hanti n (1 / 4) (1 - d0) (by norm_num) (by linarith)
        exact_mod_cast this
      have hAT : (M n d0 : ℝ) ≤ c * (T n : ℝ) := by
        nlinarith [hAB, hBT, hc]
      have hfl : M n d0 ≤ ⌊c * (T n : ℝ)⌋₊ := Nat.le_floor hAT
      have hDle2 : D n ⌊c * (T n : ℝ)⌋₊ ≤ d0 := hDle n d0 hd0pos _ hfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn n _)]
      linarith
  · -- the step profile implies cutoff
    intro hstep ε hε hε1
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set γ : ℝ := min (1 / 2) (δ / 8) with hγdef
    have hγ0 : 0 < γ := lt_min (by norm_num) (by linarith)
    have hγ2 : γ ≤ 1 / 2 := min_le_left _ _
    have hγd : γ ≤ δ / 8 := min_le_right _ _
    set m : ℝ := min ε (1 - ε) with hmdef
    have hm0 : 0 < m := lt_min hε (by linarith)
    have hmε : m ≤ ε := min_le_left _ _
    have hmε' : m ≤ 1 - ε := min_le_right _ _
    set MM : ℝ := max ε (1 - ε) with hMMdef
    have hMM1 : MM < 1 := max_lt hε1 (by linarith)
    have hMMε : ε ≤ MM := le_max_left _ _
    have hMMε' : 1 - ε ≤ MM := le_max_right _ _
    have hup := (hstep (1 + γ) (by linarith)).2 (by linarith)
    have hdown := (hstep (1 - γ) (by linarith)).1 (by linarith)
    have hev1 : ∀ᶠ n in Filter.atTop,
        D n ⌊(1 + γ) * (T n : ℝ)⌋₊ < m := by
      have := Metric.tendsto_nhds.mp hup m hm0
      filter_upwards [this] with n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn n _)] at hn
      exact hn
    have hev2 : ∀ᶠ n in Filter.atTop,
        MM < D n ⌊(1 - γ) * (T n : ℝ)⌋₊ := by
      have := Metric.tendsto_nhds.mp hdown (1 - MM) (by linarith)
      filter_upwards [this] with n hn
      rw [Real.dist_eq] at hn
      have := hle1 n ⌊(1 - γ) * (T n : ℝ)⌋₊
      rw [abs_of_nonpos (by linarith)] at hn
      linarith
    filter_upwards [hev1, hev2] with n h1 h2
    set F : ℕ := ⌊(1 + γ) * (T n : ℝ)⌋₊ with hF
    set G : ℕ := ⌊(1 - γ) * (T n : ℝ)⌋₊ with hG
    have hTnn : (0 : ℝ) ≤ (T n : ℝ) := Nat.cast_nonneg _
    have hAF : M n ε ≤ F := hMle n ε F (by linarith [hmε])
    have hBF : M n (1 - ε) ≤ F := hMle n (1 - ε) F (by linarith [hmε'])
    have hGA : G < M n ε := by
      by_contra hcon
      push_neg at hcon
      exact absurd (hDle n ε hε G hcon) (by linarith [hMMε])
    have hGB : G < M n (1 - ε) := by
      by_contra hcon
      push_neg at hcon
      exact absurd (hDle n (1 - ε) (by linarith) G hcon) (by linarith [hMMε'])
    -- turn the integer comparisons into real bounds
    have hFle : (F : ℝ) ≤ (1 + γ) * (T n : ℝ) := Nat.floor_le (by positivity)
    have hGlt : (1 - γ) * (T n : ℝ) < (G : ℝ) + 1 := Nat.lt_floor_add_one _
    have hAup : (M n ε : ℝ) ≤ (1 + γ) * (T n : ℝ) := by
      have : (M n ε : ℝ) ≤ (F : ℝ) := by exact_mod_cast hAF
      linarith
    have hBup : (M n (1 - ε) : ℝ) ≤ (1 + γ) * (T n : ℝ) := by
      have : (M n (1 - ε) : ℝ) ≤ (F : ℝ) := by exact_mod_cast hBF
      linarith
    have hAlow : (1 - γ) * (T n : ℝ) < (M n ε : ℝ) := by
      have : (G : ℝ) + 1 ≤ (M n ε : ℝ) := by exact_mod_cast hGA
      linarith
    have hBlow : (1 - γ) * (T n : ℝ) < (M n (1 - ε) : ℝ) := by
      have : (G : ℝ) + 1 ≤ (M n (1 - ε) : ℝ) := by exact_mod_cast hGB
      linarith
    have hTpos : (0 : ℝ) < (T n : ℝ) := by
      rcases eq_or_lt_of_le hTnn with h | h
      · exfalso
        have hB0 : (M n (1 - ε) : ℝ) ≤ 0 := by rw [← h] at hBup; linarith
        have : (1 - γ) * (T n : ℝ) < 0 := lt_of_lt_of_le hBlow hB0
        rw [← h] at this
        linarith
      · exact h
    have hBpos : (0 : ℝ) < (M n (1 - ε) : ℝ) := by
      have : (0 : ℝ) < (1 - γ) * (T n : ℝ) := by
        have : (0:ℝ) < 1 - γ := by linarith
        positivity
      linarith
    rw [Real.dist_eq]
    rw [abs_lt]
    constructor
    · -- lower bound
      have h3 : (1 - γ) * (T n : ℝ) < (M n ε : ℝ) := hAlow
      have h4 : (M n (1 - ε) : ℝ) ≤ (1 + γ) * (T n : ℝ) := hBup
      have h5 : ((1 - γ) / (1 + γ)) < (M n ε : ℝ) / (M n (1 - ε) : ℝ) := by
        rw [div_lt_div_iff₀ (by linarith) hBpos]
        nlinarith [hTpos, hγ0]
      have h6 : 1 - δ < (1 - γ) / (1 + γ) := by
        rw [lt_div_iff₀ (by linarith)]
        nlinarith [hγ0, hγd, hδ]
      linarith
    · -- upper bound
      have h5 : (M n ε : ℝ) / (M n (1 - ε) : ℝ) < (1 + γ) / (1 - γ) := by
        rw [div_lt_div_iff₀ hBpos (by linarith)]
        nlinarith [hTpos, hγ0, hAup, hBlow]
      have h6 : (1 + γ) / (1 - γ) < 1 + δ := by
        rw [div_lt_iff₀ (by linarith)]
        nlinarith [hγ0, hγd, hδ, hγ2]
      linarith
