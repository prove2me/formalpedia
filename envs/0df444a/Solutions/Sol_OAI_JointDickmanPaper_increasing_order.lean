-- Prove2me | solution 1 for OAI.JointDickmanPaper.increasing_order
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-17T18:53:47.825606+00:00
-- url     : https://prove2.me/submissions/79046b74-0027-4025-a5bd-72f7520023a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_JointDickman
import Theorems.Thm_OAI_JointDickmanPaper_joint_law

namespace JDCor

open Filter OAI.JointDickman OAI.Erdos970.NumberTheoryLean
open scoped Topology

/-! ## The delay construction of `ρ` -/

lemma step_succ_apply (σ : ℝ) (n : ℕ) (u : ℝ) :
    DelayConstruction.stepApprox σ (n + 1) u =
      1 + σ * ∫ t in (1 : ℝ)..max 1 u,
        DelayConstruction.kernel (DelayConstruction.stepApprox σ n) t := rfl

lemma step_succ_eq (σ : ℝ) : ∀ n : ℕ, ∀ u : ℝ, u ≤ n →
    DelayConstruction.stepApprox σ (n + 1) u = DelayConstruction.stepApprox σ n u := by
  intro n
  induction n with
  | zero =>
    intro u hu
    have : max 1 u = 1 := max_eq_left (by push_cast at hu; linarith)
    rw [step_succ_apply, this, intervalIntegral.integral_same]
    simp [DelayConstruction.stepApprox]
  | succ k ih =>
    intro u hu
    rw [step_succ_apply σ (k + 1) u, step_succ_apply σ k u]
    congr 2
    apply intervalIntegral.integral_congr
    intro t ht
    have h1 : (1 : ℝ) ≤ max 1 u := le_max_left _ _
    rw [Set.uIcc_of_le h1] at ht
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hmax : max 1 u ≤ (k : ℝ) + 1 := max_le (by linarith) (by push_cast at hu; linarith)
    simp only [DelayConstruction.kernel]
    rw [ih (t - 1) (by linarith [ht.2])]

lemma step_eq_of_le (σ : ℝ) (n : ℕ) (u : ℝ) (hu : u ≤ n) : ∀ m, n ≤ m →
    DelayConstruction.stepApprox σ m u = DelayConstruction.stepApprox σ n u := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [step_succ_eq σ m u (le_trans hu (by exact_mod_cast hnm)), ih]

lemma rho_eq (n : ℕ) (u : ℝ) (hu : u ≤ n) :
    Dickman.rho u = DelayConstruction.stepApprox (-1) n u := by
  show DelayConstruction.stepApprox (-1) ⌈u⌉₊ u = _
  exact (step_eq_of_le (-1) ⌈u⌉₊ u (Nat.le_ceil u) n (Nat.ceil_le.2 hu)).symm

lemma kernel_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (DelayConstruction.kernel f) := by
  unfold DelayConstruction.kernel
  exact (hf.comp (continuous_id.sub continuous_const)).div (continuous_const.max continuous_id)
    (fun t => (lt_of_lt_of_le one_pos (le_max_left 1 t)).ne')

lemma step_continuous (σ : ℝ) : ∀ n, Continuous (DelayConstruction.stepApprox σ n) := by
  intro n
  induction n with
  | zero => exact continuous_const
  | succ k ih =>
    have hk := kernel_continuous _ ih
    have hprim : Continuous (fun x => ∫ t in (1 : ℝ)..x,
        DelayConstruction.kernel (DelayConstruction.stepApprox σ k) t) :=
      intervalIntegral.continuous_primitive (fun a b => hk.intervalIntegrable a b) 1
    have : DelayConstruction.stepApprox σ (k + 1) = fun u => 1 + σ * ∫ t in (1 : ℝ)..max 1 u,
        DelayConstruction.kernel (DelayConstruction.stepApprox σ k) t := by
      funext u; exact step_succ_apply σ k u
    rw [this]
    exact continuous_const.add (continuous_const.mul (hprim.comp (continuous_const.max continuous_id)))

lemma rho_continuous : Continuous Dickman.rho := by
  rw [continuous_iff_continuousAt]
  intro u
  obtain ⟨n, hn⟩ := exists_nat_gt u
  have h : DelayConstruction.stepApprox (-1) n =ᶠ[𝓝 u] Dickman.rho := by
    filter_upwards [Iio_mem_nhds hn] with x hx
    exact (rho_eq n x (le_of_lt hx)).symm
  exact (step_continuous (-1) n).continuousAt.congr h

lemma rho_of_le_one (u : ℝ) (hu : u ≤ 1) : Dickman.rho u = 1 := by
  rw [rho_eq 1 u (by simpa using hu)]
  show DelayConstruction.stepApprox (-1) (0 + 1) u = 1
  rw [step_succ_apply, max_eq_left hu, intervalIntegral.integral_same]
  ring

/-- If `ρ ≥ η` on `[0, u - 1]` then the delay equation forces `ρ(u) ≤ 1 - η log u`. -/
lemma rho_le_of_lower (η u : ℝ) (hu : 1 ≤ u)
    (h : ∀ t, 0 ≤ t → t ≤ u - 1 → η ≤ Dickman.rho t) :
    Dickman.rho u ≤ 1 - η * Real.log u := by
  set n := ⌈u⌉₊
  have hn : u ≤ (n : ℝ) := Nat.le_ceil u
  rw [rho_eq (n + 1) u (by push_cast; linarith), step_succ_apply, max_eq_right hu]
  have hk : ∀ t ∈ Set.Icc (1 : ℝ) u,
      η / t ≤ DelayConstruction.kernel (DelayConstruction.stepApprox (-1) n) t := by
    intro t ht
    simp only [DelayConstruction.kernel]
    rw [max_eq_right ht.1, ← rho_eq n (t - 1) (by linarith [ht.2])]
    exact div_le_div_of_nonneg_right (h (t - 1) (by linarith [ht.1]) (by linarith [ht.2]))
      (by linarith [ht.1])
  have hint1 : IntervalIntegrable (fun t : ℝ => η / t) MeasureTheory.volume 1 u := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hu] at hx
    exact (lt_of_lt_of_le one_pos hx.1).ne'
  have hint2 := (kernel_continuous _ (step_continuous (-1) n)).intervalIntegrable
    (μ := MeasureTheory.volume) 1 u
  have hmono := intervalIntegral.integral_mono_on hu hint1 hint2 hk
  have h1 : ∫ t in (1 : ℝ)..u, η / t = η * Real.log u := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by linarith), div_one]
  linarith

/-! ## Counting -/

def J (a b : ℝ) : ℕ → Prop := fun n =>
  (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧ ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b

noncomputable def F (a : ℝ) : ℝ := Dickman.rho (1 / a)

lemma joint (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (realDensity (J a b)) atTop (𝓝 (F a * F b)) :=
  OAI.JointDickmanPaper.joint_law a b ha ha1 hb hb1

lemma count_congr {P Q : ℕ → Prop} (h : ∀ n, P n ↔ Q n) (N : ℕ) :
    empiricalCount P N = empiricalCount Q N := by
  have : P = Q := funext fun n => propext (h n)
  subst this; rfl

lemma count_mono {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) (N : ℕ) :
    empiricalCount P N ≤ empiricalCount Q N := by
  classical
  unfold empiricalCount
  exact Finset.card_le_card (Finset.monotone_filter_right _ (fun n _ => h n))

lemma count_ie (A X Y : ℕ → Prop) (N : ℕ) :
    empiricalCount A N + empiricalCount (fun n => A n ∧ X n ∧ Y n) N =
      empiricalCount (fun n => A n ∧ X n) N + empiricalCount (fun n => A n ∧ Y n) N +
        empiricalCount (fun n => A n ∧ ¬ X n ∧ ¬ Y n) N := by
  classical
  unfold empiricalCount
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hA : A n <;> by_cases hX : X n <;> by_cases hY : Y n <;> simp [hA, hX, hY]

lemma sum_count_le (K : ℕ) (E : ℕ → ℕ → Prop) (P : ℕ → Prop)
    (hdisj : ∀ i j n, i < K → j < K → i ≠ j → E i n → E j n → False)
    (hsub : ∀ i n, E i n → P n) (N : ℕ) :
    ∑ i ∈ Finset.range K, empiricalCount (E i) N ≤ empiricalCount P N := by
  classical
  unfold empiricalCount
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n _
  by_cases h : ∃ i ∈ Finset.range K, E i n
  · obtain ⟨i0, hi0, hE⟩ := h
    rw [Finset.sum_eq_single i0]
    · simp [hE, hsub i0 n hE]
    · intro j hj hji
      have : ¬ E j n := fun hEj =>
        hdisj j i0 n (Finset.mem_range.1 hj) (Finset.mem_range.1 hi0) hji hEj hE
      simp [this]
    · intro h; exact absurd hi0 h
  · push Not at h
    rw [Finset.sum_eq_zero]
    · exact Nat.zero_le _
    · intro i hi; simp [h i hi]

lemma count_add_le (P Q : ℕ → Prop) (h : ∀ n, P n → Q n → False) (N : ℕ) :
    empiricalCount P N + empiricalCount Q N ≤ N := by
  have := sum_count_le 2 (fun i => if i = 0 then P else Q) (fun _ => True)
    (by
      intro i j n hi hj hij hEi hEj
      interval_cases i <;> interval_cases j <;> simp_all)
    (fun _ _ _ => trivial) N
  simp [Finset.sum_range_succ] at this
  calc _ ≤ empiricalCount (fun _ => True) N := this
    _ ≤ N := by
      classical
      unfold empiricalCount
      simp

lemma density_nonneg (P : ℕ → Prop) {X : ℝ} (hX : 0 ≤ X) : 0 ≤ realDensity P X :=
  div_nonneg (Nat.cast_nonneg _) hX

lemma density_mono {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) {X : ℝ} (hX : 0 ≤ X) :
    realDensity P X ≤ realDensity Q X :=
  div_le_div_of_nonneg_right (by exact_mod_cast count_mono h _) hX

lemma rpow_mono_nat (n : ℕ) {a a' : ℝ} (ha : 0 < a) (h : a ≤ a') :
    (n : ℝ) ^ a ≤ (n : ℝ) ^ a' := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow ha.ne', Real.zero_rpow (by linarith : a' ≠ 0)]
  · exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) h

/-- The rectangle `n^a < P⁺(n) ≤ n^a'`, `n^b < P⁺(n+1) ≤ n^c`. -/
def Cell (a a' b c : ℝ) : ℕ → Prop := fun n =>
  J a' c n ∧ ¬ ((n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a) ∧ ¬ (((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b)

lemma cell_count (a a' b c : ℝ) (ha : 0 < a) (haa : a ≤ a') (hb : 0 < b) (hbc : b ≤ c) (N : ℕ) :
    (empiricalCount (Cell a a' b c) N : ℝ) =
      empiricalCount (J a' c) N - empiricalCount (J a c) N - empiricalCount (J a' b) N +
        empiricalCount (J a b) N := by
  have h := count_ie (J a' c) (fun n => (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a)
    (fun n => ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b) N
  have e1 : empiricalCount (fun n => J a' c n ∧ (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a) N =
      empiricalCount (J a c) N := count_congr (fun n =>
        ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans (rpow_mono_nat n ha haa), h.2⟩, h.1⟩⟩) N
  have e2 : empiricalCount (fun n => J a' c n ∧ ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b) N =
      empiricalCount (J a' b) N := count_congr (fun n =>
        ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans (rpow_mono_nat n hb hbc)⟩, h.2⟩⟩) N
  have e3 : empiricalCount (fun n => J a' c n ∧ (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧
      ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b) N = empiricalCount (J a b) N :=
    count_congr (fun n =>
      ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨⟨h.1.trans (rpow_mono_nat n ha haa),
        h.2.trans (rpow_mono_nat n hb hbc)⟩, h.1, h.2⟩⟩) N
  have e4 : empiricalCount (Cell a a' b c) N = empiricalCount (fun n => J a' c n ∧
      ¬ (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧ ¬ ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b) N := rfl
  rw [e1, e2, e3, ← e4] at h
  have h' : ((empiricalCount (J a' c) N + empiricalCount (J a b) N : ℕ) : ℝ) =
      ((empiricalCount (J a c) N + empiricalCount (J a' b) N +
        empiricalCount (Cell a a' b c) N : ℕ) : ℝ) := by rw [h]
  push_cast at h'
  linarith

lemma cell_tendsto (a a' b c : ℝ) (ha : 0 < a) (haa : a ≤ a') (ha' : a' < 1) (hb : 0 < b)
    (hbc : b ≤ c) (hc : c < 1) :
    Tendsto (realDensity (Cell a a' b c)) atTop (𝓝 ((F a' - F a) * (F c - F b))) := by
  have hfun : realDensity (Cell a a' b c) = fun X => realDensity (J a' c) X -
      realDensity (J a c) X - realDensity (J a' b) X + realDensity (J a b) X := by
    funext X
    unfold realDensity
    rw [cell_count a a' b c ha haa hb hbc]
    ring
  rw [hfun]
  have := (((joint a' c (by linarith) ha' (by linarith) hc).sub
    (joint a c ha (by linarith) (by linarith) hc)).sub
    (joint a' b (by linarith) ha' hb (by linarith))).add
    (joint a b ha (by linarith) hb (by linarith))
  convert this using 2
  ring

/-! ## Properties of `F a = ρ(1/a)` -/

lemma F_continuousAt (a : ℝ) (ha : a ≠ 0) : ContinuousAt F a := by
  show ContinuousAt (fun x => Dickman.rho (1 / x)) a
  exact ContinuousAt.comp (g := Dickman.rho) rho_continuous.continuousAt
    (continuousAt_const.div continuousAt_id ha)

lemma F_near_one (η : ℝ) (hη : 0 < η) (lo : ℝ) (hlo : lo < 1) :
    ∃ a, lo < a ∧ 0 < a ∧ a < 1 ∧ 1 - η < F a := by
  have hF1 : F 1 = 1 := by simp [F, rho_of_le_one]
  have ht : Tendsto F (𝓝[<] 1) (𝓝 1) := by
    have := (F_continuousAt 1 one_ne_zero).tendsto
    rw [hF1] at this
    exact this.mono_left nhdsWithin_le_nhds
  have e1 : ∀ᶠ a in 𝓝[<] (1 : ℝ), 1 - η < F a := ht.eventually (lt_mem_nhds (by linarith))
  have e2 : ∀ᶠ a in 𝓝[<] (1 : ℝ), max lo 0 < a :=
    (eventually_gt_nhds (max_lt hlo one_pos)).filter_mono nhdsWithin_le_nhds
  have e3 : ∀ᶠ a in 𝓝[<] (1 : ℝ), a < 1 := self_mem_nhdsWithin
  obtain ⟨a, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  exact ⟨a, lt_of_le_of_lt (le_max_left _ _) h2, lt_of_le_of_lt (le_max_right _ _) h2, h3, h1⟩

lemma F_nonneg (a : ℝ) (ha : 0 < a) (ha1 : a < 1) : 0 ≤ F a := by
  obtain ⟨b, -, hb, hb1, hFb⟩ := F_near_one (1 / 2) (by norm_num) 0 (by norm_num)
  have : 0 ≤ F a * F b := ge_of_tendsto (joint a b ha ha1 hb hb1)
    ((eventually_ge_atTop 0).mono fun X hX => density_nonneg _ hX)
  by_contra h
  push Not at h
  nlinarith

lemma F_mono (a a' : ℝ) (ha : 0 < a) (haa : a ≤ a') (ha' : a' < 1) : F a ≤ F a' := by
  obtain ⟨b, -, hb, hb1, hFb⟩ := F_near_one (1 / 2) (by norm_num) 0 (by norm_num)
  have : F a * F b ≤ F a' * F b :=
    le_of_tendsto_of_tendsto (joint a b ha (by linarith) hb hb1)
      (joint a' b (by linarith) ha' hb hb1)
      ((eventually_ge_atTop 0).mono fun X hX =>
        density_mono (fun n h => ⟨h.1.trans (rpow_mono_nat n ha haa), h.2⟩) hX)
  by_contra h
  push Not at h
  nlinarith

lemma F_small (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ a, 0 < a ∧ a < 1 ∧ F a < η := by
  by_contra hcon
  push Not at hcon
  set u := Real.exp (2 / η) with hu_def
  have hu : 1 < u := by
    have h0 : (0 : ℝ) < 2 / η := by positivity
    have := Real.add_one_lt_exp h0.ne'
    linarith
  have hlow : ∀ t, 0 ≤ t → t ≤ u - 1 → η ≤ Dickman.rho t := by
    intro t ht0 ht
    rcases le_or_gt t 1 with h | h
    · rw [rho_of_le_one t h]; exact hη1
    · have := hcon (1 / t) (by positivity) (by rw [div_lt_one (by linarith)]; exact h)
      simpa [F, one_div, inv_inv] using this
  have h1 := rho_le_of_lower η u hu.le hlow
  have hlog : Real.log u = 2 / η := Real.log_exp _
  have h2 : 0 ≤ Dickman.rho u := by
    have := F_nonneg (1 / u) (by positivity) (by rw [div_lt_one (by linarith)]; exact hu)
    simpa [F, one_div, inv_inv] using this
  rw [hlog] at h1
  have : η * (2 / η) = 2 := by field_simp
  linarith

lemma sum_K_sub (K : ℕ) : ∑ i ∈ Finset.range K, ((K : ℝ) - (i + 1)) = K * (K - 1) / 2 := by
  have gauss : ∀ m : ℕ, ∑ i ∈ Finset.range m, ((i : ℝ) + 1) = m * (m + 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, gauss]
  ring

/-- A grid in `(0,1)` along which `F` has equal increments carrying almost all of the mass. -/
lemma grid (ε : ℝ) (hε : 0 < ε) : ∃ (K : ℕ) (a : ℕ → ℝ),
    (∀ i, i ≤ K → 0 < a i ∧ a i < 1) ∧ (∀ i j, i ≤ j → j ≤ K → a i ≤ a j) ∧
    1 / 2 - ε < ∑ i ∈ Finset.range K, (F (a (i + 1)) - F (a i)) * (F (a K) - F (a (i + 1))) := by
  set η := min (ε / 4) (1 / 4) with hη_def
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  obtain ⟨lo, hlo0, hlo1, hFlo⟩ := F_small η hη (by linarith)
  obtain ⟨hi, hlohi, hhi0, hhi1, hFhi⟩ := F_near_one η hη lo hlo1
  set m := F lo
  set M := F hi
  set D := M - m with hD_def
  have hD : 1 - 2 * η < D := by linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
  have hKpos : (0 : ℝ) < K := lt_trans (by positivity) hK
  set y : ℕ → ℝ := fun i => m + i * D / K with hy_def
  have hcont : ContinuousOn F (Set.Icc lo hi) := fun x hx =>
    (F_continuousAt x (lt_of_lt_of_le hlo0 hx.1).ne').continuousWithinAt
  have hivt := intermediate_value_Icc hlohi.le hcont
  have hex : ∀ i, ∃ x, i ≤ K → x ∈ Set.Icc lo hi ∧ F x = y i := by
    intro i
    by_cases hi : i ≤ K
    · have hiK : (i : ℝ) ≤ K := by exact_mod_cast hi
      have hyi : y i ∈ Set.Icc m M := by
        constructor
        · simp only [hy_def]
          have : 0 ≤ (i : ℝ) * D / K := by
            apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hKpos.le
          linarith
        · simp only [hy_def]
          have : (i : ℝ) * D / K ≤ D := by
            rw [div_le_iff₀ hKpos]; nlinarith
          linarith
      obtain ⟨x, hx, hFx⟩ := hivt hyi
      exact ⟨x, fun _ => ⟨hx, hFx⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose a ha using hex
  have hpos : ∀ i, i ≤ K → 0 < a i ∧ a i < 1 := fun i hi =>
    ⟨lt_of_lt_of_le hlo0 (ha i hi).1.1, lt_of_le_of_lt (ha i hi).1.2 hhi1⟩
  refine ⟨K, a, hpos, ?_, ?_⟩
  · intro i j hij hjK
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · by_contra hcon
      push Not at hcon
      have h1 := F_mono (a j) (a i) (hpos j hjK).1 hcon.le (hpos i (hij.trans hjK)).2
      rw [(ha j hjK).2, (ha i (hij.trans hjK)).2] at h1
      simp only [hy_def] at h1
      have hlt' : (i : ℝ) < j := by exact_mod_cast hlt
      have : (i : ℝ) * D / K < j * D / K := by
        apply div_lt_div_of_pos_right _ hKpos
        nlinarith
      linarith
  · have hsum : ∑ i ∈ Finset.range K, (F (a (i + 1)) - F (a i)) * (F (a K) - F (a (i + 1))) =
        ∑ i ∈ Finset.range K, (D / K) ^ 2 * ((K : ℝ) - (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiK : i + 1 ≤ K := Finset.mem_range.1 hi
      rw [(ha (i + 1) hiK).2, (ha i (by omega)).2, (ha K le_rfl).2]
      simp only [hy_def]
      push_cast
      field_simp
      ring
    rw [hsum, ← Finset.mul_sum, sum_K_sub]
    -- (D/K)^2 * (K (K-1)/2) = D^2 (1 - 1/K) / 2
    have hform : (D / K) ^ 2 * (K * (K - 1) / 2) = D ^ 2 * (1 - 1 / K) / 2 := by
      field_simp
    rw [hform]
    have ht : 1 / (K : ℝ) < ε := by
      rw [div_lt_iff₀ hKpos]
      rw [div_lt_iff₀ hε] at hK
      linarith
    have ht0 : 0 < 1 / (K : ℝ) := by positivity
    have hD0 : 1 / 2 ≤ D := by linarith
    rcases le_or_gt 1 ε with hε1 | hε1
    · have : 0 ≤ D ^ 2 * (1 - 1 / K) / 2 := by
        apply div_nonneg _ (by norm_num)
        apply mul_nonneg (sq_nonneg _)
        have : 1 / (K : ℝ) ≤ 1 := by
          rw [div_le_one hKpos]
          have : (1 : ℝ) ≤ K := by
            rcases Nat.eq_zero_or_pos K with h | h
            · simp [h] at hKpos
            · exact_mod_cast h
          exact this
        linarith
      linarith
    · have hD2 : 1 - ε ≤ D ^ 2 := by nlinarith
      have h1t : 1 - ε < 1 - 1 / (K : ℝ) := by linarith
      have : (1 - ε) * (1 - ε) < D ^ 2 * (1 - 1 / K) := by
        calc (1 - ε) * (1 - ε) < (1 - ε) * (1 - 1 / K) := by
              apply mul_lt_mul_of_pos_left h1t (by linarith)
          _ ≤ D ^ 2 * (1 - 1 / K) := by
              apply mul_le_mul_of_nonneg_right hD2 (by linarith)
      nlinarith

/-! ## The two orderings -/

def Inc : ℕ → Prop := fun n => n.maxPrimeFac < (n + 1).maxPrimeFac
def Dec : ℕ → Prop := fun n => (n + 1).maxPrimeFac < n.maxPrimeFac

lemma sum_density_le (K : ℕ) (E : ℕ → ℕ → Prop) (P : ℕ → Prop)
    (hdisj : ∀ i j n, i < K → j < K → i ≠ j → E i n → E j n → False)
    (hsub : ∀ i n, E i n → P n) {X : ℝ} (hX : 0 ≤ X) :
    ∑ i ∈ Finset.range K, realDensity (E i) X ≤ realDensity P X := by
  unfold realDensity
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hX
  exact_mod_cast sum_count_le K E P hdisj hsub ⌊X⌋₊

lemma core (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X in atTop, 1 / 2 - ε < realDensity Inc X ∧ 1 / 2 - ε < realDensity Dec X := by
  obtain ⟨K, a, hpos, hmono, hS⟩ := grid ε hε
  set S := ∑ i ∈ Finset.range K, (F (a (i + 1)) - F (a i)) * (F (a K) - F (a (i + 1)))
  have hE : Tendsto (fun X => ∑ i ∈ Finset.range K,
      realDensity (Cell (a i) (a (i + 1)) (a (i + 1)) (a K)) X) atTop (𝓝 S) := by
    apply tendsto_finsetSum
    intro i hi
    have hiK : i + 1 ≤ K := Finset.mem_range.1 hi
    exact cell_tendsto _ _ _ _ (hpos i (by omega)).1 (hmono i (i + 1) (by omega) hiK)
      (hpos (i + 1) hiK).2 (hpos (i + 1) hiK).1 (hmono (i + 1) K hiK le_rfl) (hpos K le_rfl).2
  have hE' : Tendsto (fun X => ∑ i ∈ Finset.range K,
      realDensity (Cell (a (i + 1)) (a K) (a i) (a (i + 1))) X) atTop (𝓝 S) := by
    have : Tendsto (fun X => ∑ i ∈ Finset.range K,
        realDensity (Cell (a (i + 1)) (a K) (a i) (a (i + 1))) X) atTop
        (𝓝 (∑ i ∈ Finset.range K, (F (a K) - F (a (i + 1))) * (F (a (i + 1)) - F (a i)))) := by
      apply tendsto_finsetSum
      intro i hi
      have hiK : i + 1 ≤ K := Finset.mem_range.1 hi
      exact cell_tendsto _ _ _ _ (hpos (i + 1) hiK).1 (hmono (i + 1) K hiK le_rfl)
        (hpos K le_rfl).2 (hpos i (by omega)).1 (hmono i (i + 1) (by omega) hiK)
        (hpos (i + 1) hiK).2
    have heq : ∑ i ∈ Finset.range K, (F (a K) - F (a (i + 1))) * (F (a (i + 1)) - F (a i)) = S :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rwa [heq] at this
  -- cells for the increasing ordering are disjoint and contained in `Inc`
  have hdisjI : ∀ i j n, i < K → j < K → i ≠ j →
      Cell (a i) (a (i + 1)) (a (i + 1)) (a K) n →
      Cell (a j) (a (j + 1)) (a (j + 1)) (a K) n → False := by
    intro i j n hi hj hij h1 h2
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2.2.1 (h1.1.1.trans (rpow_mono_nat n (hpos (i + 1) (by omega)).1
        (hmono (i + 1) j (by omega) (by omega))))
    · exact h1.2.1 (h2.1.1.trans (rpow_mono_nat n (hpos (j + 1) (by omega)).1
        (hmono (j + 1) i (by omega) (by omega))))
  have hsubI : ∀ i n, Cell (a i) (a (i + 1)) (a (i + 1)) (a K) n → Inc n := by
    intro i n h
    have : (n.maxPrimeFac : ℝ) < ((n + 1).maxPrimeFac : ℝ) :=
      lt_of_le_of_lt h.1.1 (not_le.1 h.2.2)
    exact_mod_cast this
  have hdisjD : ∀ i j n, i < K → j < K → i ≠ j →
      Cell (a (i + 1)) (a K) (a i) (a (i + 1)) n →
      Cell (a (j + 1)) (a K) (a j) (a (j + 1)) n → False := by
    intro i j n hi hj hij h1 h2
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2.2.2 (h1.1.2.trans (rpow_mono_nat n (hpos (i + 1) (by omega)).1
        (hmono (i + 1) j (by omega) (by omega))))
    · exact h1.2.2 (h2.1.2.trans (rpow_mono_nat n (hpos (j + 1) (by omega)).1
        (hmono (j + 1) i (by omega) (by omega))))
  have hsubD : ∀ i n, Cell (a (i + 1)) (a K) (a i) (a (i + 1)) n → Dec n := by
    intro i n h
    have : ((n + 1).maxPrimeFac : ℝ) < (n.maxPrimeFac : ℝ) :=
      lt_of_le_of_lt h.1.2 (not_le.1 h.2.1)
    exact_mod_cast this
  filter_upwards [hE.eventually (lt_mem_nhds hS), hE'.eventually (lt_mem_nhds hS),
    eventually_ge_atTop 0] with X h1 h2 hX
  exact ⟨lt_of_lt_of_le h1 (sum_density_le K _ Inc hdisjI hsubI hX),
    lt_of_lt_of_le h2 (sum_density_le K _ Dec hdisjD hsubD hX)⟩

lemma density_inc_add_dec_le {X : ℝ} (hX : 0 < X) :
    realDensity Inc X + realDensity Dec X ≤ 1 := by
  unfold realDensity
  rw [← add_div, div_le_one hX]
  have := count_add_le Inc Dec (fun n h1 h2 => lt_asymm h1 h2) ⌊X⌋₊
  calc ((empiricalCount Inc ⌊X⌋₊ : ℝ) + empiricalCount Dec ⌊X⌋₊) ≤ (⌊X⌋₊ : ℝ) := by
        exact_mod_cast this
    _ ≤ X := Nat.floor_le hX.le

theorem orderings :
    Tendsto (realDensity Inc) atTop (𝓝 (1 / 2)) ∧
      Tendsto (realDensity Dec) atTop (𝓝 (1 / 2)) := by
  constructor
  · rw [tendsto_order]
    refine ⟨fun l hl => ?_, fun u hu => ?_⟩
    · filter_upwards [core (1 / 2 - l) (by linarith)] with X hX
      linarith [hX.1]
    · filter_upwards [core (u - 1 / 2) (by linarith), eventually_gt_atTop 0] with X hX hX0
      linarith [hX.2, density_inc_add_dec_le hX0]
  · rw [tendsto_order]
    refine ⟨fun l hl => ?_, fun u hu => ?_⟩
    · filter_upwards [core (1 / 2 - l) (by linarith)] with X hX
      linarith [hX.2]
    · filter_upwards [core (u - 1 / 2) (by linarith), eventually_gt_atTop 0] with X hX hX0
      linarith [hX.1, density_inc_add_dec_le hX0]

end JDCor

open Filter OAI.JointDickman in
open scoped Topology in
theorem solution :
    Tendsto (realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac))
      atTop (𝓝 (1 / 2)) :=
  JDCor.orderings.1

#print axioms solution
