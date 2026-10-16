-- Prove2me | solution 1 for LeastSquaresTD.Absorbing.lstd_converges_absorbing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T00:47:45.678998+00:00
-- url     : https://prove2.me/submissions/3ff8a7d1-b3c2-4fcb-a796-85de0e1feeee

import Mathlib
import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

set_option autoImplicit false

section

set_option autoImplicit false

open MeasureTheory Filter Topology Finset

namespace M1

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- cylinder weight -/
noncomputable def wt (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (xs : Fin (n + 1) → X) : ℝ :=
  ν (xs 0) * ∏ i : Fin n, P (xs i.castSucc) (xs i.succ)

/-- path increment sum -/
def pathS (h : X → X → ℝ) (n : ℕ) (xs : Fin (n + 1) → X) : ℝ :=
  ∑ k : Fin n, h (xs k.castSucc) (xs k.succ)

lemma wt_snoc (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (xs : Fin (n + 1) → X) (y : X) :
    wt P ν (n + 1) (Fin.snoc xs y : Fin (n + 2) → X) = wt P ν n xs * P (xs (Fin.last n)) y := by
  unfold wt
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc xs y : Fin (n + 2) → X) 0 = xs 0 := by
    simp
  rw [h0]
  have h1 : ∀ i : Fin n, P ((Fin.snoc xs y : Fin (n + 2) → X) i.castSucc.castSucc)
      ((Fin.snoc xs y : Fin (n + 2) → X) i.castSucc.succ) = P (xs i.castSucc) (xs i.succ) := by
    intro i
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  have h2 : P ((Fin.snoc xs y : Fin (n + 2) → X) (Fin.last n).castSucc)
      ((Fin.snoc xs y : Fin (n + 2) → X) (Fin.last n).succ) = P (xs (Fin.last n)) y := by
    rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  simp only [h1, h2]
  ring

lemma sum_snoc {M : Type*} [AddCommMonoid M] (n : ℕ) (F : (Fin (n + 2) → X) → M) :
    ∑ xs : Fin (n + 2) → X, F xs =
      ∑ xs : Fin (n + 1) → X, ∑ y : X, F (Fin.snoc xs y) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => X)).sum_comp]
  rw [Fintype.sum_prod_type_right]
  rfl

lemma pathS_snoc (h : X → X → ℝ) (n : ℕ) (xs : Fin (n + 1) → X) (y : X) :
    pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X) = pathS h n xs + h (xs (Fin.last n)) y := by
  unfold pathS
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

/-- expectation over paths -/
noncomputable def EE (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (G : (Fin (n + 1) → X) → ℝ) : ℝ :=
  ∑ xs : Fin (n + 1) → X, wt P ν n xs * G xs

lemma EE_succ (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (F : (Fin (n + 2) → X) → ℝ) :
    EE P ν (n + 1) F = ∑ xs : Fin (n + 1) → X, wt P ν n xs *
      ∑ y : X, P (xs (Fin.last n)) y * F (Fin.snoc xs y) := by
  unfold EE
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun xs _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [wt_snoc]; ring

lemma wt_nonneg (P : Matrix X X ℝ) (ν : X → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hν : ∀ x, 0 ≤ ν x)
    (n : ℕ) (xs : Fin (n + 1) → X) : 0 ≤ wt P ν n xs :=
  mul_nonneg (hν _) (Finset.prod_nonneg fun i _ => hP _ _)

lemma EE_mono (P : Matrix X X ℝ) (ν : X → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hν : ∀ x, 0 ≤ ν x)
    (n : ℕ) {F G : (Fin (n + 1) → X) → ℝ} (hFG : ∀ xs, F xs ≤ G xs) :
    EE P ν n F ≤ EE P ν n G :=
  Finset.sum_le_sum fun xs _ => mul_le_mul_of_nonneg_left (hFG xs) (wt_nonneg P ν hP hν n xs)

lemma EE_one (P : Matrix X X ℝ) (ν : X → ℝ) (hrow : ∀ x, ∑ y, P x y = 1)
    (hν1 : ∑ x, ν x = 1) (n : ℕ) : EE P ν n (fun _ => 1) = 1 := by
  induction n with
  | zero =>
    unfold EE wt
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [← hν1]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) _ _ (fun x => by simp)
  | succ n ih =>
    rw [EE_succ]
    simp only [mul_one, hrow]
    simpa [EE] using ih

lemma EE_const (P : Matrix X X ℝ) (ν : X → ℝ) (hrow : ∀ x, ∑ y, P x y = 1)
    (hν1 : ∑ x, ν x = 1) (n : ℕ) (c : ℝ) : EE P ν n (fun _ => c) = c := by
  have := EE_one P ν hrow hν1 n
  unfold EE at this ⊢
  simp only [← Finset.sum_mul, mul_comm _ c, ← Finset.mul_sum] at this ⊢
  have h1 : ∑ i : Fin (n + 1) → X, wt P ν n i = 1 := by simpa using this
  rw [h1, mul_one]

lemma EE_add (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (F G : (Fin (n + 1) → X) → ℝ) :
    EE P ν n (fun xs => F xs + G xs) = EE P ν n F + EE P ν n G := by
  unfold EE; simp [mul_add, Finset.sum_add_distrib]

lemma EE_smul (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (c : ℝ) (F : (Fin (n + 1) → X) → ℝ) :
    EE P ν n (fun xs => c * F xs) = c * EE P ν n F := by
  unfold EE; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun xs _ => ?_; ring

/-- moment of the increment kernel -/
noncomputable def aj (P : Matrix X X ℝ) (h : X → X → ℝ) (j : ℕ) (x : X) : ℝ :=
  ∑ y, P x y * h x y ^ j

lemma aj_abs_le (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (h : X → X → ℝ) (B : ℝ) (hB : ∀ x y, |h x y| ≤ B) (j : ℕ) (x : X) :
    |aj P h j x| ≤ B ^ j := by
  unfold aj
  calc |∑ y, P x y * h x y ^ j| ≤ ∑ y, |P x y * h x y ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, P x y * B ^ j := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (hP x y), abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hB x y) j) (hP x y)
    _ = B ^ j := by rw [← Finset.sum_mul, hrow, one_mul]

lemma inner2 (P : Matrix X X ℝ) (hrow : ∀ x, ∑ y, P x y = 1) (h : X → X → ℝ)
    (hh : ∀ x, ∑ y, P x y * h x y = 0) (x : X) (s : ℝ) :
    ∑ y, P x y * (s + h x y) ^ 2 = s ^ 2 + aj P h 2 x := by
  have : ∀ y, P x y * (s + h x y) ^ 2 =
      s ^ 2 * P x y + 2 * s * (P x y * h x y) + P x y * h x y ^ 2 := fun y => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hrow, hh, aj]
  ring

lemma inner4 (P : Matrix X X ℝ) (hrow : ∀ x, ∑ y, P x y = 1) (h : X → X → ℝ)
    (hh : ∀ x, ∑ y, P x y * h x y = 0) (x : X) (s : ℝ) :
    ∑ y, P x y * (s + h x y) ^ 4 =
      s ^ 4 + 6 * s ^ 2 * aj P h 2 x + 4 * s * aj P h 3 x + aj P h 4 x := by
  have : ∀ y, P x y * (s + h x y) ^ 4 =
      s ^ 4 * P x y + 4 * s ^ 3 * (P x y * h x y) + 6 * s ^ 2 * (P x y * h x y ^ 2)
        + 4 * s * (P x y * h x y ^ 3) + P x y * h x y ^ 4 := fun y => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hrow, hh, aj]
  ring

lemma pathS_abs_le (h : X → X → ℝ) (B : ℝ) (hB : ∀ x y, |h x y| ≤ B) (n : ℕ)
    (xs : Fin (n + 1) → X) : |pathS h n xs| ≤ n * B := by
  unfold pathS
  calc |∑ k : Fin n, h (xs k.castSucc) (xs k.succ)|
      ≤ ∑ k : Fin n, |h (xs k.castSucc) (xs k.succ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, B := Finset.sum_le_sum fun k _ => hB _ _
    _ = n * B := by simp

lemma moment2 (P : Matrix X X ℝ) (ν : X → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (h : X → X → ℝ)
    (hh : ∀ x, ∑ y, P x y * h x y = 0) (B : ℝ) (hB : ∀ x y, |h x y| ≤ B) (n : ℕ) :
    EE P ν n (fun xs => pathS h n xs ^ 2) ≤ n * B ^ 2 := by
  induction n with
  | zero => simp [EE, pathS]
  | succ n ih =>
    rw [EE_succ]
    have e : ∀ xs : Fin (n + 1) → X, ∑ y, P (xs (Fin.last n)) y *
        (pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X)) ^ 2 =
        pathS h n xs ^ 2 + aj P h 2 (xs (Fin.last n)) := fun xs => by
      simp only [pathS_snoc]
      exact inner2 P hrow h hh _ _
    have : ∑ xs : Fin (n + 1) → X, wt P ν n xs * ∑ y, P (xs (Fin.last n)) y *
        (pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X)) ^ 2 =
        EE P ν n (fun xs => pathS h n xs ^ 2 + aj P h 2 (xs (Fin.last n))) := by
      unfold EE; exact Finset.sum_congr rfl fun xs _ => by rw [e]
    rw [this]
    have hle : EE P ν n (fun xs => pathS h n xs ^ 2 + aj P h 2 (xs (Fin.last n))) ≤
        EE P ν n (fun xs => pathS h n xs ^ 2 + B ^ 2) :=
      EE_mono P ν hP hν n fun xs => by
        have := aj_abs_le P hP hrow h B hB 2 (xs (Fin.last n))
        linarith [(abs_le.mp this).2]
    have hR : EE P ν n (fun xs => pathS h n xs ^ 2 + B ^ 2) =
        EE P ν n (fun xs => pathS h n xs ^ 2) + B ^ 2 := by
      rw [EE_add, EE_const P ν hrow hν1]
    rw [hR] at hle
    push_cast
    nlinarith [hle, ih]

lemma moment4 (P : Matrix X X ℝ) (ν : X → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (h : X → X → ℝ)
    (hh : ∀ x, ∑ y, P x y * h x y = 0) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x y, |h x y| ≤ B) (n : ℕ) :
    EE P ν n (fun xs => pathS h n xs ^ 4) ≤ 10 * B ^ 4 * (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp [EE, pathS]
  | succ n ih =>
    rw [EE_succ]
    have e : ∀ xs : Fin (n + 1) → X, ∑ y, P (xs (Fin.last n)) y *
        (pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X)) ^ 4 =
        pathS h n xs ^ 4 + 6 * pathS h n xs ^ 2 * aj P h 2 (xs (Fin.last n))
          + 4 * pathS h n xs * aj P h 3 (xs (Fin.last n)) + aj P h 4 (xs (Fin.last n)) :=
      fun xs => by
        simp only [pathS_snoc]
        exact inner4 P hrow h hh _ _
    have : ∑ xs : Fin (n + 1) → X, wt P ν n xs * ∑ y, P (xs (Fin.last n)) y *
        (pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X)) ^ 4 =
        EE P ν n (fun xs => pathS h n xs ^ 4 + 6 * pathS h n xs ^ 2 * aj P h 2 (xs (Fin.last n))
          + 4 * pathS h n xs * aj P h 3 (xs (Fin.last n)) + aj P h 4 (xs (Fin.last n))) := by
      unfold EE; exact Finset.sum_congr rfl fun xs _ => by rw [e]
    rw [this]
    have hle : EE P ν n (fun xs => pathS h n xs ^ 4 + 6 * pathS h n xs ^ 2 * aj P h 2 (xs (Fin.last n))
          + 4 * pathS h n xs * aj P h 3 (xs (Fin.last n)) + aj P h 4 (xs (Fin.last n))) ≤
        EE P ν n (fun xs => (pathS h n xs ^ 4 + (6 * B ^ 2) * pathS h n xs ^ 2)
          + (4 * n * B ^ 4 + B ^ 4)) := by
      refine EE_mono P ν hP hν n fun xs => ?_
      have a2 := (abs_le.mp (aj_abs_le P hP hrow h B hB 2 (xs (Fin.last n)))).2
      have a4 := (abs_le.mp (aj_abs_le P hP hrow h B hB 4 (xs (Fin.last n)))).2
      have a3 := aj_abs_le P hP hrow h B hB 3 (xs (Fin.last n))
      have hs := pathS_abs_le h B hB n xs
      have hm : |pathS h n xs * aj P h 3 (xs (Fin.last n))| ≤ n * B * B ^ 3 := by
        rw [abs_mul]
        exact mul_le_mul hs a3 (abs_nonneg _) (by positivity)
      have hm' := (abs_le.mp hm).2
      have hsq : 0 ≤ pathS h n xs ^ 2 := sq_nonneg _
      have h6 : 6 * pathS h n xs ^ 2 * aj P h 2 (xs (Fin.last n)) ≤ 6 * B ^ 2 * pathS h n xs ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left a2 hsq]
      nlinarith [h6, hm', a4]
    have hR : EE P ν n (fun xs => (pathS h n xs ^ 4 + (6 * B ^ 2) * pathS h n xs ^ 2)
          + (4 * n * B ^ 4 + B ^ 4)) = EE P ν n (fun xs => pathS h n xs ^ 4)
          + (6 * B ^ 2) * EE P ν n (fun xs => pathS h n xs ^ 2) + (4 * n * B ^ 4 + B ^ 4) := by
      rw [EE_add, EE_add, EE_smul, EE_const P ν hrow hν1]
    rw [hR] at hle
    have h2 := moment2 P ν hP hrow hν hν1 h hh B hB n
    have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
    have hB4 : 0 ≤ B ^ 4 := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith [hle, ih, mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 6 * B ^ 2),
      mul_nonneg hn hB4]

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

lemma cyl_meas (Z : ℕ → Ω → X) (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (n : ℕ) (xs : Fin (n + 1) → X) : MeasurableSet {ω | ∀ i : Fin (n + 1), Z i ω = xs i} := by
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => hmeas _ _

lemma measurable_path (Z : ℕ → Ω → X) (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (n : ℕ) {β : Type*} [MeasurableSpace β] (G : (Fin (n + 1) → X) → β) :
    Measurable (fun ω => G (fun i : Fin (n + 1) => Z i ω)) := by
  letI : MeasurableSpace (Fin (n + 1) → X) := ⊤
  have hW : Measurable (fun ω => (fun i : Fin (n + 1) => Z i ω)) := by
    refine measurable_to_countable' fun xs => ?_
    have : (fun ω => (fun i : Fin (n + 1) => Z i ω)) ⁻¹' {xs} =
        {ω | ∀ i : Fin (n + 1), Z i ω = xs i} := by
      ext ω; simp [funext_iff]
    rw [this]; exact cyl_meas Z hmeas n xs
  exact (measurable_from_top (f := G)).comp hW

lemma lintegral_path (μ : Measure Ω) (Z : ℕ → Ω → X)
    (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (n : ℕ) (G : (Fin (n + 1) → X) → ENNReal) :
    ∫⁻ ω, G (fun i : Fin (n + 1) => Z i ω) ∂μ =
      ∑ xs : Fin (n + 1) → X, G xs * μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} := by
  have key : ∀ ω, G (fun i : Fin (n + 1) => Z i ω) =
      ∑ xs : Fin (n + 1) → X,
        ({ω | ∀ i : Fin (n + 1), Z i ω = xs i}).indicator (fun _ => G xs) ω := by
    intro ω
    rw [Finset.sum_eq_single (fun i : Fin (n + 1) => Z i ω)]
    · simp [Set.indicator]
    · intro xs _ hne
      have : ω ∉ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} := by
        intro hω
        apply hne
        funext i
        exact (hω i).symm
      simp [Set.indicator_of_notMem this]
    · simp
  simp_rw [key]
  rw [lintegral_finset_sum]
  · refine Finset.sum_congr rfl fun xs _ => ?_
    rw [lintegral_indicator_const (cyl_meas Z hmeas n xs)]
  · intro xs _
    exact measurable_const.indicator (cyl_meas Z hmeas n xs)

end Meas

lemma pathS_eq_range {Ω : Type*} (Z : ℕ → Ω → X) (h : X → X → ℝ) (t : ℕ) (ω : Ω) :
    pathS h t (fun i : Fin (t + 1) => Z i ω) = ∑ k ∈ Finset.range t, h (Z k ω) (Z (k + 1) ω) := by
  unfold pathS
  have := Fin.sum_univ_eq_sum_range (fun k => h (Z k ω) (Z (k + 1) ω)) t
  rw [← this]
  simp

theorem markov_mds_slln {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (ν : X → ℝ) (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (Z : ℕ → Ω → X) (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (hlaw : ∀ (n : ℕ) (xs : Fin (n + 1) → X),
      μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} =
        ENNReal.ofReal (ν (xs 0) * ∏ i : Fin n, P (xs i.castSucc) (xs i.succ)))
    (h : X → X → ℝ) (hh : ∀ x, ∑ y, P x y * h x y = 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℕ => (1 / (t : ℝ)) * ∑ k ∈ Finset.range t, h (Z k ω) (Z (k + 1) ω))
      atTop (𝓝 0) := by
  set B : ℝ := ∑ x, ∑ y, |h x y| with hBdef
  have hB : ∀ x y, |h x y| ≤ B := fun x y =>
    (Finset.single_le_sum (f := fun y => |h x y|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ y)).trans
      (Finset.single_le_sum (f := fun x => ∑ y, |h x y|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ x))
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  let f : ℕ → Ω → ENNReal := fun t ω =>
    ENNReal.ofReal ((pathS h t (fun i : Fin (t + 1) => Z i ω) / t) ^ 4)
  have hfm : ∀ t, Measurable (f t) := fun t =>
    measurable_path Z hmeas t (fun xs => ENNReal.ofReal ((pathS h t xs / t) ^ 4))
  have hint : ∀ t, ∫⁻ ω, f t ω ∂μ ≤ ENNReal.ofReal (10 * B ^ 4 / (t : ℝ) ^ 2) := by
    intro t
    have := lintegral_path μ Z hmeas t (fun xs => ENNReal.ofReal ((pathS h t xs / t) ^ 4))
    show ∫⁻ ω, ENNReal.ofReal ((pathS h t (fun i : Fin (t + 1) => Z i ω) / t) ^ 4) ∂μ ≤ _
    rw [this]
    simp_rw [hlaw]
    have hw : ∀ xs : Fin (t + 1) → X, ν (xs 0) * ∏ i : Fin t, P (xs i.castSucc) (xs i.succ)
        = wt P ν t xs := fun _ => rfl
    simp_rw [hw]
    calc ∑ xs : Fin (t + 1) → X, ENNReal.ofReal ((pathS h t xs / t) ^ 4) *
          ENNReal.ofReal (wt P ν t xs)
        = ∑ xs : Fin (t + 1) → X, ENNReal.ofReal ((pathS h t xs / t) ^ 4 * wt P ν t xs) :=
          Finset.sum_congr rfl fun xs _ => (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (∑ xs : Fin (t + 1) → X, (pathS h t xs / t) ^ 4 * wt P ν t xs) :=
          (ENNReal.ofReal_sum_of_nonneg fun xs _ =>
            mul_nonneg (by positivity) (wt_nonneg P ν hP hν t xs)).symm
      _ ≤ ENNReal.ofReal (10 * B ^ 4 / (t : ℝ) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          have e1 : ∑ xs : Fin (t + 1) → X, (pathS h t xs / t) ^ 4 * wt P ν t xs =
              EE P ν t (fun xs => (1 / (t : ℝ) ^ 4) * pathS h t xs ^ 4) := by
            unfold EE
            refine Finset.sum_congr rfl fun xs _ => ?_
            rw [div_pow]; ring
          rw [e1, EE_smul]
          rcases Nat.eq_zero_or_pos t with rfl | ht
          · simp
          · have m4 := moment4 P ν hP hrow hν hν1 h hh B hB0 hB t
            have htpos : (0 : ℝ) < t := by exact_mod_cast ht
            calc 1 / (t : ℝ) ^ 4 * EE P ν t (fun xs => pathS h t xs ^ 4)
                ≤ 1 / (t : ℝ) ^ 4 * (10 * B ^ 4 * (t : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left m4 (by positivity)
              _ = 10 * B ^ 4 / (t : ℝ) ^ 2 := by field_simp
  have hsumm : Summable (fun t : ℕ => 10 * B ^ 4 / (t : ℝ) ^ 2) :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (10 * B ^ 4)).congr
      fun t => by rw [mul_one_div]
  have hsum : ∑' t, ∫⁻ ω, f t ω ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' t : ℕ, ENNReal.ofReal (10 * B ^ 4 / (t : ℝ) ^ 2)) ?_
      (ENNReal.tsum_le_tsum hint)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity) hsumm]
    exact ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ ω ∂μ, ∑' t, f t ω < ⊤ := by
    have hm : Measurable (fun ω => ∑' t, f t ω) := Measurable.ennreal_tsum hfm
    have hl : ∫⁻ ω, ∑' t, f t ω ∂μ ≠ ⊤ := by
      rw [lintegral_tsum (fun t => (hfm t).aemeasurable)]; exact hsum
    exact ae_lt_top hm hl
  filter_upwards [hlt] with ω hω
  have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h1 : Tendsto (fun t : ℕ => (pathS h t (fun i : Fin (t + 1) => Z i ω) / t) ^ 4)
      atTop (𝓝 0) := by
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    rw [ENNReal.toReal_zero] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp, f]
    exact ENNReal.toReal_ofReal (by positivity)
  have h3 : Tendsto (fun t : ℕ => pathS h t (fun i : Fin (t + 1) => Z i ω) / t) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at h1 ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h1 (ε ^ 4) (by positivity)
    refine ⟨N, fun t ht => ?_⟩
    have h4 := hN t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h4
    rw [Real.dist_eq, sub_zero]
    by_contra hcon
    push_neg at hcon
    have h5 : ε ^ 4 ≤ |pathS h t (fun i : Fin (t + 1) => Z i ω) / t| ^ 4 :=
      pow_le_pow_left₀ hε.le hcon 4
    rw [Even.pow_abs (by decide)] at h5
    linarith
  refine h3.congr fun t => ?_
  rw [pathS_eq_range]
  ring

end M1

end

section

set_option autoImplicit false

open Matrix Finset

namespace M1

variable {X : Type*} [Fintype X] [DecidableEq X]

lemma pow_entry_nonneg (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y) (n : ℕ) (x y : X) :
    0 ≤ (P ^ n) x y := by
  induction n generalizing x y with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (hP _ _) (ih _ _)

lemma vecMul_pow_eq (P : Matrix X X ℝ) (π : X → ℝ) (h : Matrix.vecMul π P = π) (n : ℕ) :
    Matrix.vecMul π (P ^ n) = π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, h]

/-- A2: stationary distribution exists. -/
theorem exists_stationary_of_stochastic [Nonempty X]
    (P : Matrix X X ℝ) (hnn : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) :
    ∃ π : X → ℝ, (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1 ∧ Matrix.vecMul π P = π := by
  -- a nonzero left fixed vector
  have hdet : (Pᵀ - 1 : Matrix X X ℝ).det = 0 := by
    rw [← Matrix.det_transpose, Matrix.transpose_sub, Matrix.transpose_transpose,
      Matrix.transpose_one]
    obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun _ => 1, fun h => ?_, ?_⟩
    · have := congrFun h x₀; simp at this
    · ext x
      simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, hrow x, Matrix.one_apply]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hvP : Matrix.vecMul v P = v := by
    have : Pᵀ *ᵥ v = v := by
      have := hv
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    rw [← Matrix.mulVec_transpose]; exact this
  set u : X → ℝ := fun x => |v x| with hu
  have hge : ∀ y, u y ≤ Matrix.vecMul u P y := by
    intro y
    have h1 : v y = ∑ x, v x * P x y := by
      have := congrFun hvP y
      rw [Matrix.vecMul, dotProduct] at this
      exact this.symm
    calc u y = |∑ x, v x * P x y| := by rw [hu]; simp only; rw [← h1]
      _ ≤ ∑ x, |v x * P x y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, u x * P x y := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [abs_mul, abs_of_nonneg (hnn x y)]
      _ = Matrix.vecMul u P y := by rw [Matrix.vecMul, dotProduct]
  have hsum_eq : ∑ y, Matrix.vecMul u P y = ∑ x, u x := by
    simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, hrow, mul_one]
  have heq : ∀ y, Matrix.vecMul u P y = u y := by
    have h0 : ∑ y, (Matrix.vecMul u P y - u y) = 0 := by
      rw [Finset.sum_sub_distrib, hsum_eq, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sub_nonneg.mpr (hge y))).mp h0
    intro y
    have := this y (Finset.mem_univ y)
    linarith
  have hupos : 0 < ∑ x, u x := by
    obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hv0 (funext hcon)
    refine lt_of_lt_of_le (abs_pos.mpr hx) ?_
    exact Finset.single_le_sum (f := u) (fun _ _ => abs_nonneg _) (Finset.mem_univ x)
  set s : ℝ := ∑ x, u x with hs_def
  refine ⟨fun x => u x / s, fun x => div_nonneg (abs_nonneg _) hupos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, ← hs_def, div_self hupos.ne']
  · ext y
    simp only [Matrix.vecMul, dotProduct] at heq ⊢
    rw [show (∑ x, u x / s * P x y) = (∑ x, u x * P x y) / s by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun x _ => by ring]
    rw [heq y]

/-- A3 -/
theorem stationary_pos_of_irreducible
    (P : Matrix X X ℝ) (hnn : ∀ x y, 0 ≤ P x y)
    (hirr : ∀ x y : X, ∃ n : ℕ, 0 < (P ^ n) x y) (π : X → ℝ) (hπnn : ∀ x, 0 ≤ π x)
    (hπsum : ∑ x, π x = 1) (hπP : Matrix.vecMul π P = π) : ∀ x, 0 < π x := by
  intro x
  by_contra hcon
  have hx : π x = 0 := le_antisymm (not_lt.mp hcon) (hπnn x)
  have hall : ∀ y, π y = 0 := by
    intro y
    obtain ⟨n, hn⟩ := hirr y x
    have h1 := congrFun (vecMul_pow_eq P π hπP n) x
    rw [Matrix.vecMul, dotProduct, hx] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => mul_nonneg (hπnn z) (pow_entry_nonneg P hnn n z x))).mp h1 y (Finset.mem_univ y)
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hn.ne'
  have : ∑ x, π x = 0 := Finset.sum_eq_zero fun y _ => hall y
  linarith

end M1

end

section

set_option autoImplicit false

open Matrix Finset

namespace M1A

open LeastSquaresTD.Absorbing

variable {X : Type*} [Fintype X] [DecidableEq X]

lemma pent_nonneg (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y) (n : ℕ) (x y : X) :
    0 ≤ (P ^ n) x y := by
  induction n generalizing x y with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (hP _ _) (ih _ _)

lemma abs_row_zero (C : Chain X) {x : X} (hx : C.P x x = 1) {z : X} (hz : z ≠ x) :
    C.P x z = 0 := by
  have h := C.row_sum x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hx] at h
  have h0 : ∑ y ∈ Finset.univ.erase x, C.P x y = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => C.nonneg x y)).mp h0 z
    (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩)

lemma restart_nonneg (C : Chain X) (S : X → ℝ) (hS : ∀ x, 0 ≤ S x) (x y : X) :
    0 ≤ C.restartKernel S x y := by
  unfold Chain.restartKernel
  split_ifs
  · exact hS y
  · exact C.nonneg x y

lemma restart_row (C : Chain X) (S : X → ℝ) (hS1 : ∑ x, S x = 1) (x : X) :
    ∑ y, C.restartKernel S x y = 1 := by
  unfold Chain.restartKernel
  by_cases h : C.P x x = 1
  · simp [h, hS1]
  · simp [h, C.row_sum x]

theorem restart_irreducible (C : Chain X) (S : X → ℝ)
    (habs : C.IsAbsorbing) (hS_nonneg : ∀ x, 0 ≤ S x) (hS_sum : ∑ x, S x = 1)
    (haccess : C.AllAccessible S) :
    ∀ x y : X, ∃ n : ℕ, 0 < (C.restartKernel S ^ n) x y := by
  set Q := C.restartKernel S with hQ
  have hQnn : ∀ x y, 0 ≤ Q x y := restart_nonneg C S hS_nonneg
  have trans : ∀ x y z, (∃ n, 0 < (Q ^ n) x y) → (∃ n, 0 < (Q ^ n) y z) →
      ∃ n, 0 < (Q ^ n) x z := by
    rintro x y z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    rw [pow_add, Matrix.mul_apply]
    calc (0 : ℝ) < (Q ^ n) x y * (Q ^ m) y z := mul_pos hn hm
      _ ≤ ∑ w, (Q ^ n) x w * (Q ^ m) w z :=
        Finset.single_le_sum (f := fun w => (Q ^ n) x w * (Q ^ m) w z)
          (fun w _ => mul_nonneg (pent_nonneg Q hQnn n _ _) (pent_nonneg Q hQnn m _ _))
          (Finset.mem_univ y)
  have step : ∀ x y, 0 < Q x y → ∃ n, 0 < (Q ^ n) x y := fun x y h => ⟨1, by simpa using h⟩
  have hP2R : ∀ n x y, 0 < (C.P ^ n) x y → ∃ k, 0 < (Q ^ k) x y := by
    intro n
    induction n with
    | zero =>
      intro x y h
      have : x = y := by
        by_contra hne
        simp [Matrix.one_apply, hne] at h
      subst this
      exact ⟨0, by simp⟩
    | succ n ih =>
      intro x y h
      rw [pow_succ', Matrix.mul_apply] at h
      obtain ⟨z, _, hz⟩ := Finset.exists_lt_of_sum_lt
        (s := Finset.univ) (f := fun _ => (0 : ℝ))
        (g := fun z => C.P x z * (C.P ^ n) z y) (by simpa using h)
      have hz' : 0 < C.P x z * (C.P ^ n) z y := hz
      have hPxz : 0 < C.P x z := by
        by_contra hc
        have : C.P x z * (C.P ^ n) z y ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) (pent_nonneg C.P C.nonneg n z y)
        linarith
      have hPzy : 0 < (C.P ^ n) z y := by
        by_contra hc
        have : C.P x z * (C.P ^ n) z y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (C.nonneg x z) (not_lt.mp hc)
        linarith
      by_cases hx : C.P x x = 1
      · have hzx : z = x := by
          by_contra hne
          rw [abs_row_zero C hx hne] at hPxz
          exact lt_irrefl _ hPxz
        subst hzx
        exact ih _ _ hPzy
      · have hQxz : 0 < Q x z := by
          simp only [hQ, Chain.restartKernel, if_neg hx]; exact hPxz
        exact trans x z y (step x z hQxz) (ih z y hPzy)
  intro x y
  obtain ⟨n, a, ha, hna⟩ := habs x
  obtain ⟨s, k, hs, hky⟩ := haccess y
  have hxa := hP2R n x a hna
  have has : ∃ n, 0 < (Q ^ n) a s := step a s (by
    simp only [hQ, Chain.restartKernel, if_pos ha]; exact hs)
  have hsy := hP2R k s y hky
  obtain ⟨j, hj⟩ := trans x a y hxa (trans a s y has hsy)
  exact ⟨j, hj⟩

end M1A

end

section

set_option autoImplicit false

open Matrix Finset

namespace M1A4

open LeastSquaresTD.Absorbing

variable {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}

theorem restart_lstd_identities (C C' : Chain X)
    (S : X → ℝ) (hC' : C'.P = C.restartKernel S) (R : X → X → ℝ) (φ : X → Fin m → ℝ)
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0) (γ : ℝ) (π : X → ℝ) :
    limitMatrix C' φ γ π = limitMatrix C φ γ π ∧
      limitVector C' R φ π = limitVector C R φ π ∧
      ∀ (z : ℕ → X) (n : ℕ), chainLstdTheta R φ γ z n = lstdTheta C R φ γ z n := by
  have hPeq : ∀ x, C.P x x ≠ 1 → ∀ y, C'.P x y = C.P x y := by
    intro x hx y
    simp [hC', Chain.restartKernel, hx]
  refine ⟨?_, ?_, ?_⟩
  · have key : Matrix.transpose (Matrix.of φ) * Matrix.diagonal π * (1 - γ • C'.P) =
        Matrix.transpose (Matrix.of φ) * Matrix.diagonal π * (1 - γ • C.P) := by
      ext i y
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hAD : (Matrix.transpose (Matrix.of φ) * Matrix.diagonal π) i x = φ x i * π x := by
        simp [Matrix.mul_diagonal]
      rw [hAD]
      by_cases hx : C.P x x = 1
      · have h0 : φ x i = 0 := by rw [hφabs x hx]; rfl
        rw [h0]; simp
      · simp only [Matrix.sub_apply, Matrix.smul_apply, hPeq x hx y]
    unfold limitMatrix
    rw [key]
  · have hrb : ∀ x, C.P x x ≠ 1 → C'.rbar R x = C.rbar R x := by
      intro x hx
      unfold Chain.rbar
      exact Finset.sum_congr rfl fun y _ => by rw [hPeq x hx y]
    unfold limitVector
    have hD : ∀ r : X → ℝ, Matrix.mulVec (Matrix.diagonal π) r = fun x => π x * r x := fun r => by
      ext x; simp [Matrix.mulVec_diagonal]
    rw [hD, hD]
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : C.P x x = 1
    · have h0 : φ x i = 0 := by rw [hφabs x hx]; rfl
      rw [h0]; simp
    · rw [hrb x hx]
  · intro z n
    unfold chainLstdTheta lstdTheta chainLstdA lstdA chainLstdB lstdB
    have hA : ∑ k ∈ (Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1),
        Matrix.vecMulVec (φ (z k)) (φ (z k) - γ • φ (z (k + 1))) =
        ∑ k ∈ Finset.range n, Matrix.vecMulVec (φ (z k)) (φ (z k) - γ • φ (z (k + 1))) := by
      refine Finset.sum_filter_of_ne fun k _ hk => ?_
      by_contra hc
      apply hk
      rw [hφabs _ hc]
      ext i j; simp [Matrix.vecMulVec]
    have hB : ∑ k ∈ (Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1),
        R (z k) (z (k + 1)) • φ (z k) = ∑ k ∈ Finset.range n, R (z k) (z (k + 1)) • φ (z k) := by
      refine Finset.sum_filter_of_ne fun k _ hk => ?_
      by_contra hc
      apply hk
      rw [hφabs _ hc, smul_zero]
    rw [hA, hB]

end M1A4

end

section

set_option autoImplicit false

open Matrix Finset Module

namespace M1P

variable {X : Type*} [Fintype X] [DecidableEq X]

lemma pent_nonneg (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y) (n : ℕ) (x y : X) :
    0 ≤ (P ^ n) x y := by
  induction n generalizing x y with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (hP _ _) (ih _ _)

/-- harmonic functions of an irreducible stochastic matrix are constant -/
lemma harmonic_const [Nonempty X] (P : Matrix X X ℝ) (hnn : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hirr : ∀ x y : X, ∃ n : ℕ, 0 < (P ^ n) x y)
    (g : X → ℝ) (hg : P *ᵥ g = g) (x y : X) : g x = g y := by
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  have hmax : ∀ z, g z ≤ g x₀ := fun z => hx₀ z (Finset.mem_univ z)
  -- from a max point, positive-probability successors are max points
  have step : ∀ a, g a = g x₀ → ∀ b, 0 < P a b → g b = g x₀ := by
    intro a ha b hb
    have h1 : ∑ z, P a z * g z = g a := by
      have := congrFun hg a
      simpa [Matrix.mulVec, dotProduct] using this
    have h2 : ∑ z, P a z * (g x₀ - g z) = 0 := by
      have : ∑ z, P a z * (g x₀ - g z) = g x₀ * ∑ z, P a z - ∑ z, P a z * g z := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [this, hrow, h1, ha]; ring
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => mul_nonneg (hnn a z) (sub_nonneg.mpr (hmax z)))).mp h2 b (Finset.mem_univ b)
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hb.ne'
    · linarith
  have reach : ∀ n a b, g a = g x₀ → 0 < (P ^ n) a b → g b = g x₀ := by
    intro n
    induction n with
    | zero =>
      intro a b ha h
      have : a = b := by
        by_contra hne
        simp [Matrix.one_apply, hne] at h
      subst this; exact ha
    | succ n ih =>
      intro a b ha h
      rw [pow_succ', Matrix.mul_apply] at h
      obtain ⟨z, _, hz⟩ := Finset.exists_lt_of_sum_lt
        (s := Finset.univ) (f := fun _ => (0 : ℝ))
        (g := fun z => P a z * (P ^ n) z b) (by simpa using h)
      have hz' : 0 < P a z * (P ^ n) z b := hz
      have hPaz : 0 < P a z := by
        by_contra hc
        have : P a z * (P ^ n) z b ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) (pent_nonneg P hnn n z b)
        linarith
      have hPzb : 0 < (P ^ n) z b := by
        by_contra hc
        have : P a z * (P ^ n) z b ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (hnn a z) (not_lt.mp hc)
        linarith
      exact ih z b (step a ha z hPaz) hPzb
  have hall : ∀ b, g b = g x₀ := by
    intro b
    obtain ⟨n, hn⟩ := hirr x₀ b
    exact reach n x₀ b rfl hn
  rw [hall x, hall y]

/-- Poisson equation -/
theorem poisson_solvable [Nonempty X] (P : Matrix X X ℝ) (hnn : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hirr : ∀ x y : X, ∃ n : ℕ, 0 < (P ^ n) x y)
    (π : X → ℝ) (hπsum : ∑ x, π x = 1) (hπP : Matrix.vecMul π P = π)
    (f : X → ℝ) (hf : ∑ x, π x * f x = 0) :
    ∃ g : X → ℝ, ∀ x, g x - (P *ᵥ g) x = f x := by
  let T : (X → ℝ) →ₗ[ℝ] (X → ℝ) := Matrix.mulVecLin (1 - P)
  let ell : (X → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun g => ∑ x, π x * g x
      map_add' := fun a b => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring }
  have hcard : finrank ℝ (X → ℝ) = Fintype.card X := Module.finrank_fintype_fun_eq_card ℝ
  -- kernel of T
  have hkerT : LinearMap.ker T = ℝ ∙ (fun _ : X => (1 : ℝ)) := by
    ext g
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro hg
      have hg' : P *ᵥ g = g := by
        have : (1 - P) *ᵥ g = 0 := hg
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
        exact this.symm
      obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
      refine ⟨g x₀, ?_⟩
      ext y
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact harmonic_const P hnn hrow hirr g hg' x₀ y
    · rintro ⟨c, rfl⟩
      show (1 - P) *ᵥ (c • fun _ : X => (1 : ℝ)) = 0
      have hP1 : P *ᵥ (fun _ : X => (1 : ℝ)) = fun _ => 1 := by
        ext x; simp [Matrix.mulVec, dotProduct, hrow x]
      rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec, hP1, sub_self, smul_zero]
  have hfinT : finrank ℝ (LinearMap.ker T) = 1 := by
    rw [hkerT]; exact finrank_span_singleton (fun h => by
      obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
      have := congrFun h x₀; simp at this)
  have hrankT := LinearMap.finrank_range_add_finrank_ker T
  -- range ell = top
  have hrange_ell : LinearMap.range ell = ⊤ := by
    have : ∃ x, π x ≠ 0 := by
      by_contra hc; push_neg at hc
      have : ∑ x, π x = 0 := Finset.sum_eq_zero fun x _ => hc x
      linarith
    obtain ⟨x, hx⟩ := this
    rw [eq_top_iff]
    intro c _
    refine ⟨fun y => if y = x then c / π x else 0, ?_⟩
    show ∑ y, π y * (if y = x then c / π x else 0) = c
    simp [hx] <;> field_simp
  have hrank_ell := LinearMap.finrank_range_add_finrank_ker ell
  rw [hrange_ell, finrank_top, finrank_self] at hrank_ell
  have hle : LinearMap.range T ≤ LinearMap.ker ell := by
    rintro _ ⟨g, rfl⟩
    show ∑ x, π x * ((1 - P) *ᵥ g) x = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have : ∑ x, π x * (P *ᵥ g) x = ∑ x, π x * g x := by
      have h1 : Matrix.vecMul π P ⬝ᵥ g = π ⬝ᵥ (P *ᵥ g) := (Matrix.dotProduct_mulVec π P g).symm
      rw [hπP] at h1
      simpa [dotProduct] using h1.symm
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, this, sub_self]
  have heq : LinearMap.range T = LinearMap.ker ell :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hfmem : f ∈ LinearMap.ker ell := by
    rw [LinearMap.mem_ker]; exact hf
  rw [← heq] at hfmem
  obtain ⟨g, hg⟩ := hfmem
  refine ⟨g, fun x => ?_⟩
  have := congrFun hg x
  have e : (1 - P) *ᵥ g = fun x => g x - (P *ᵥ g) x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  simp only [T, Matrix.mulVecLin_apply, e] at this
  exact this

end M1P

end

section

set_option autoImplicit false

open MeasureTheory Filter Topology Finset Matrix

namespace M1F

variable {X : Type*} [Fintype X] [DecidableEq X]

def vc (z : ℕ → X) (x : X) (t : ℕ) : ℕ := ((Finset.range t).filter (fun k => z k = x)).card

def pc (z : ℕ → X) (x y : X) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun k => z k = x ∧ z (k + 1) = y)).card

theorem visit_freq [Nonempty X] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Matrix X X ℝ) (hnn : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hirr : ∀ x y : X, ∃ n : ℕ, 0 < (P ^ n) x y)
    (π : X → ℝ) (hπsum : ∑ x, π x = 1) (hπP : Matrix.vecMul π P = π)
    (ν : X → ℝ) (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (Z : ℕ → Ω → X) (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (hlaw : ∀ (n : ℕ) (xs : Fin (n + 1) → X),
      μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} =
        ENNReal.ofReal (ν (xs 0) * ∏ i : Fin n, P (xs i.castSucc) (xs i.succ))) :
    ∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => (vc (fun k => Z k ω) x t : ℝ) / t) atTop (𝓝 (π x)) := by
  rw [ae_all_iff]
  intro x
  set f : X → ℝ := fun z => (if z = x then 1 else 0) - π x with hfdef
  have hf : ∑ z, π z * f z = 0 := by
    simp only [hfdef, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_mul, hπsum]
    ring
  obtain ⟨g, hg⟩ := M1P.poisson_solvable P hnn hrow hirr π hπsum hπP f hf
  set h : X → X → ℝ := fun u v => g v - (P *ᵥ g) u with hh_def
  have hh : ∀ u, ∑ y, P u y * h u y = 0 := by
    intro u
    simp only [hh_def, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul]
    simp only [Matrix.mulVec, dotProduct]
    ring
  have M := M1.markov_mds_slln μ P hnn hrow ν hν hν1 Z hmeas hlaw h hh
  filter_upwards [M] with ω hω
  set G : ℝ := ∑ y, |g y| with hG
  have hgb : ∀ z, |g z| ≤ G := fun z =>
    Finset.single_le_sum (f := fun y => |g y|) (fun _ _ => abs_nonneg _) (Finset.mem_univ z)
  have hsum : ∀ t : ℕ, ∑ k ∈ Finset.range t, f (Z k ω) =
      ∑ k ∈ Finset.range t, h (Z k ω) (Z (k + 1) ω) + (g (Z 0 ω) - g (Z t ω)) := by
    intro t
    have e : ∀ k, f (Z k ω) = h (Z k ω) (Z (k + 1) ω) + (g (Z k ω) - g (Z (k + 1) ω)) := by
      intro k
      have := hg (Z k ω)
      simp only [hh_def]
      linarith
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib,
      Finset.sum_range_sub' (fun k => g (Z k ω)) t]
  have hcount : ∀ t : ℕ, ∑ k ∈ Finset.range t, f (Z k ω) =
      (vc (fun k => Z k ω) x t : ℝ) - t * π x := by
    intro t
    simp only [hfdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      vc, Finset.sum_boole]
  have hrem : Tendsto (fun t : ℕ => (g (Z 0 ω) - g (Z t ω)) / t) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun t => ?_) (tendsto_const_div_atTop_nhds_zero_nat (2 * G))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg t)
    calc |g (Z 0 ω) - g (Z t ω)| ≤ |g (Z 0 ω)| + |g (Z t ω)| := abs_sub _ _
      _ ≤ 2 * G := by linarith [hgb (Z 0 ω), hgb (Z t ω)]
  have hcomb : Tendsto (fun t : ℕ => (1 / (t : ℝ)) *
      ∑ k ∈ Finset.range t, h (Z k ω) (Z (k + 1) ω) + (g (Z 0 ω) - g (Z t ω)) / t)
      atTop (𝓝 0) := by simpa using hω.add hrem
  have hfin : Tendsto (fun t : ℕ => (vc (fun k => Z k ω) x t : ℝ) / t - π x) atTop (𝓝 0) := by
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    have := hsum t
    rw [hcount t] at this
    field_simp
    linarith
  simpa using hfin.add_const (π x)

theorem pair_freq [Nonempty X] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Matrix X X ℝ) (hnn : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hirr : ∀ x y : X, ∃ n : ℕ, 0 < (P ^ n) x y)
    (π : X → ℝ) (hπsum : ∑ x, π x = 1) (hπP : Matrix.vecMul π P = π)
    (ν : X → ℝ) (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (Z : ℕ → Ω → X) (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (hlaw : ∀ (n : ℕ) (xs : Fin (n + 1) → X),
      μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} =
        ENNReal.ofReal (ν (xs 0) * ∏ i : Fin n, P (xs i.castSucc) (xs i.succ))) :
    ∀ᵐ ω ∂μ, ∀ x y : X,
      Tendsto (fun t : ℕ => (pc (fun k => Z k ω) x y t : ℝ) / t) atTop (𝓝 (π x * P x y)) := by
  have hV := visit_freq μ P hnn hrow hirr π hπsum hπP ν hν hν1 Z hmeas hlaw
  have hall : ∀ x y : X, ∀ᵐ ω ∂μ,
      Tendsto (fun t : ℕ => (pc (fun k => Z k ω) x y t : ℝ) / t) atTop (𝓝 (π x * P x y)) := by
    intro x y
    set h : X → X → ℝ := fun u v =>
      (if u = x ∧ v = y then 1 else 0) - (if u = x then P x y else 0) with hh_def
    have hh : ∀ u, ∑ w, P u w * h u w = 0 := by
      intro u
      simp only [hh_def, mul_sub, Finset.sum_sub_distrib]
      by_cases hu : u = x
      · subst hu
        simp only [if_true, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ]
        rw [← Finset.sum_mul, hrow]
        ring
      · simp [hu]
    have M := M1.markov_mds_slln μ P hnn hrow ν hν hν1 Z hmeas hlaw h hh
    filter_upwards [M, hV] with ω hω hVω
    have hid : ∀ t : ℕ, ∑ k ∈ Finset.range t, h (Z k ω) (Z (k + 1) ω) =
        (pc (fun k => Z k ω) x y t : ℝ) - P x y * (vc (fun k => Z k ω) x t : ℝ) := by
      intro t
      simp only [hh_def, Finset.sum_sub_distrib, Finset.sum_boole, pc, vc]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      ring
    have hfin : Tendsto (fun t : ℕ => (1 / (t : ℝ)) *
        ∑ k ∈ Finset.range t, h (Z k ω) (Z (k + 1) ω) + P x y * ((vc (fun k => Z k ω) x t : ℝ) / t))
        atTop (𝓝 (π x * P x y)) := by
      have := hω.add ((hVω x).const_mul (P x y))
      simpa [mul_comm] using this
    refine hfin.congr fun t => ?_
    rw [hid t]
    ring
  exact ae_all_iff.mpr fun x => ae_all_iff.mpr (hall x)

end M1F

end

section

set_option autoImplicit false

open MeasureTheory Filter Topology Matrix

namespace M1L

open LeastSquaresTD.Absorbing

def pcL {X : Type*} [DecidableEq X] (z : ℕ → X) (x y : X) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun k => z k = x ∧ z (k + 1) = y)).card

lemma sum_pairs {X : Type*} [Fintype X] [DecidableEq X] {M : Type*} [AddCommMonoid M]
    [Module ℝ M] (z : ℕ → X) (t : ℕ) (f : X → X → M) :
    ∑ k ∈ Finset.range t, f (z k) (z (k + 1)) =
      ∑ x, ∑ y, (pcL z x y t : ℝ) • f x y := by
  have h : ∀ x y, (pcL z x y t : ℝ) • f x y =
      ∑ k ∈ Finset.range t, if z k = x ∧ z (k + 1) = y then f x y else 0 := by
    intro x y
    rw [pcL, Finset.card_filter, Nat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have inner : ∀ k, ∑ x, ∑ y, (if z k = x ∧ z (k + 1) = y then f x y else 0) =
      f (z k) (z (k + 1)) := by
    intro k
    simp only [ite_and]
    rw [Finset.sum_eq_single (z k)]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  simp_rw [h]
  calc ∑ k ∈ Finset.range t, f (z k) (z (k + 1))
      = ∑ k ∈ Finset.range t, ∑ x, ∑ y,
          (if z k = x ∧ z (k + 1) = y then f x y else 0) :=
        Finset.sum_congr rfl fun k _ => (inner k).symm
    _ = ∑ x, ∑ k ∈ Finset.range t, ∑ y,
          (if z k = x ∧ z (k + 1) = y then f x y else 0) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_comm

lemma scale_helper {X : Type*} [Fintype X] {M : Type*} [AddCommGroup M] [Module ℝ M]
    (t : ℕ) (ht : (t : ℝ) ≠ 0) (F : X → X → M) (c : X → X → ℝ) :
    ∑ x, ∑ y, c x y • F x y = (t : ℝ) • ∑ x, ∑ y, (c x y / t) • F x y := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]; congr 1; field_simp

lemma inv_smul_real {m : ℕ} (c : ℝ) (hc : c ≠ 0) (A : Matrix (Fin m) (Fin m) ℝ) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases hA : IsUnit A.det
  · simpa [Units.smul_def] using Matrix.inv_smul' A (Units.mk0 c hc) hA
  · have h2 : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul]
      intro h
      exact hA ((IsUnit.mul_iff.mp h).2)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hA, Matrix.nonsing_inv_apply_not_isUnit _ h2,
      smul_zero]

theorem path_lstd {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}
    (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ) (z : ℕ → X)
    (hfreq : ∀ x y : X,
      Tendsto (fun t : ℕ => (pcL z x y t : ℝ) / t) atTop (𝓝 (π x * C.P x y)))
    (hM : IsUnit (limitMatrix C φ γ π)) :
    Tendsto (fun n => chainLstdTheta R φ γ z n) atTop
      (𝓝 ((limitMatrix C φ γ π)⁻¹ *ᵥ limitVector C R φ π)) := by
  set V : X → X → Matrix (Fin m) (Fin m) ℝ :=
    fun x y => Matrix.vecMulVec (φ x) (φ x - γ • φ y) with hV
  set W : X → X → (Fin m → ℝ) := fun x y => R x y • φ x with hW
  set Ab : ℕ → Matrix (Fin m) (Fin m) ℝ :=
    fun t => ∑ x, ∑ y, ((pcL z x y t : ℝ) / t) • V x y with hAb
  set Bb : ℕ → (Fin m → ℝ) :=
    fun t => ∑ x, ∑ y, ((pcL z x y t : ℝ) / t) • W x y with hBb
  have hA : ∀ t : ℕ, t ≠ 0 → chainLstdA φ γ z t = (t : ℝ) • Ab t := by
    intro t ht
    have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have e : chainLstdA φ γ z t = ∑ k ∈ Finset.range t, V (z k) (z (k + 1)) := rfl
    rw [e, sum_pairs z t V]
    exact scale_helper t htr V (fun x y => (pcL z x y t : ℝ))
  have hB : ∀ t : ℕ, t ≠ 0 → chainLstdB R φ z t = (t : ℝ) • Bb t := by
    intro t ht
    have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have e : chainLstdB R φ z t = ∑ k ∈ Finset.range t, W (z k) (z (k + 1)) := rfl
    rw [e, sum_pairs z t W]
    exact scale_helper t htr W (fun x y => (pcL z x y t : ℝ))
  have hMeq : limitMatrix C φ γ π = ∑ x, ∑ y, (π x * C.P x y) • V x y := by
    ext i j
    simp only [limitMatrix, hV, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.transpose_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e1 : ∀ y, φ x i * π x * ((if x = y then 1 else 0) - γ * C.P x y) * φ y j =
        (if x = y then φ x i * π x * φ y j else 0) - γ * (φ x i * π x * C.P x y * φ y j) := by
      intro y; split_ifs <;> ring
    have e2 : ∀ y, π x * C.P x y * (φ x i * (φ x j - γ * φ y j)) =
        C.P x y * (π x * φ x i * φ x j) - γ * (φ x i * π x * C.P x y * φ y j) := by
      intro y; ring
    simp only [e1, e2, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, C.row_sum,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hVeq : limitVector C R φ π = ∑ x, ∑ y, (π x * C.P x y) • W x y := by
    ext i
    simp only [limitVector, hW, Chain.rbar, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.of_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have tA : Tendsto Ab atTop (𝓝 (limitMatrix C φ γ π)) := by
    rw [hMeq]
    refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => ?_
    exact (hfreq x y).smul_const _
  have tB : Tendsto Bb atTop (𝓝 (limitVector C R φ π)) := by
    rw [hVeq]
    refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => ?_
    exact (hfreq x y).smul_const _
  have hdet : (limitMatrix C φ γ π).det ≠ 0 := by
    rw [Matrix.isUnit_iff_isUnit_det] at hM
    exact hM.ne_zero
  have hinv : ContinuousAt Inv.inv (limitMatrix C φ γ π) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have tI := hinv.tendsto.comp tA
  have hc : Continuous fun p : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => p.1 *ᵥ p.2 :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  have hlim := (hc.tendsto _).comp (tI.prodMk_nhds tB)
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with t ht
  have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  simp only [Function.comp, chainLstdTheta]
  rw [hA t ht, hB t ht, inv_smul_real _ htr, Matrix.smul_mulVec, Matrix.mulVec_smul,
    smul_smul, inv_mul_cancel₀ htr, one_smul]

end M1L

end

section

set_option autoImplicit false

open Matrix Finset

namespace M1V

open LeastSquaresTD.Absorbing

variable {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}

lemma pent_nonneg (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y) (n : ℕ) (x y : X) :
    0 ≤ (P ^ n) x y := by
  induction n generalizing x y with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (hP _ _) (ih _ _)

lemma abs_row_zero (C : Chain X) {x : X} (hx : C.P x x = 1) {z : X} (hz : z ≠ x) :
    C.P x z = 0 := by
  have h := C.row_sum x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hx] at h
  have h0 : ∑ y ∈ Finset.univ.erase x, C.P x y = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => C.nonneg x y)).mp h0 z
    (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩)

lemma pow_rowsum (C : Chain X) (k : ℕ) (x : X) : ∑ y, (C.P ^ k) x y = 1 := by
  induction k generalizing x with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    simp only [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact C.row_sum x

lemma abs_pow_mulVec (C : Chain X) {x : X} (hx : C.P x x = 1) (k : ℕ) (w : X → ℝ) :
    ((C.P ^ k) *ᵥ w) x = w x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    set u := (C.P ^ k) *ᵥ w with hu
    have : (C.P *ᵥ u) x = ∑ y, C.P x y * u y := rfl
    rw [this]
    have e : ∀ y, C.P x y * u y = if y = x then u x else 0 := by
      intro y
      by_cases hy : y = x
      · subst hy; simp [hx]
      · simp [hy, abs_row_zero C hx hy]
    simp_rw [e]
    simp [ih]

/-- indicator of the non-absorbing states -/
noncomputable def indN (C : Chain X) : X → ℝ := fun x => if C.P x x = 1 then 0 else 1

lemma indN_nonneg (C : Chain X) (x : X) : 0 ≤ indN C x := by
  unfold indN; split_ifs <;> norm_num

lemma indN_le_one (C : Chain X) (x : X) : indN C x ≤ 1 := by
  unfold indN; split_ifs <;> norm_num

noncomputable def sN (C : Chain X) (k : ℕ) (x : X) : ℝ := ((C.P ^ k) *ᵥ indN C) x

lemma mulVec_pow_mono (C : Chain X) (k : ℕ) {u v : X → ℝ} (huv : ∀ y, u y ≤ v y) (x : X) :
    ((C.P ^ k) *ᵥ u) x ≤ ((C.P ^ k) *ᵥ v) x :=
  Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (huv y) (pent_nonneg C.P C.nonneg k x y)

lemma sN_nonneg (C : Chain X) (k : ℕ) (x : X) : 0 ≤ sN C k x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (pent_nonneg C.P C.nonneg k x y) (indN_nonneg C y)

lemma sN_le_one (C : Chain X) (k : ℕ) (x : X) : sN C k x ≤ 1 := by
  have := mulVec_pow_mono C k (u := indN C) (v := fun _ => 1) (fun y => indN_le_one C y) x
  refine this.trans (le_of_eq ?_)
  simp [Matrix.mulVec, dotProduct, pow_rowsum]

lemma sN_abs (C : Chain X) {x : X} (hx : C.P x x = 1) (k : ℕ) : sN C k x = 0 := by
  unfold sN
  rw [abs_pow_mulVec C hx]
  simp [indN, hx]

lemma P_ind_le (C : Chain X) (y : X) : (C.P *ᵥ indN C) y ≤ indN C y := by
  by_cases hy : C.P y y = 1
  · have := abs_pow_mulVec C hy 1 (indN C)
    rw [pow_one] at this
    exact le_of_eq this
  · have h1 : (C.P *ᵥ indN C) y ≤ ∑ z, C.P y z * 1 :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (indN_le_one C z) (C.nonneg y z)
    simp only [mul_one, C.row_sum] at h1
    simpa [indN, hy] using h1

lemma sN_succ_le (C : Chain X) (k : ℕ) (x : X) : sN C (k + 1) x ≤ sN C k x := by
  unfold sN
  rw [pow_succ, ← Matrix.mulVec_mulVec]
  exact mulVec_pow_mono C k (fun y => P_ind_le C y) x

lemma sN_anti (C : Chain X) (x : X) : Antitone (fun k => sN C k x) :=
  antitone_nat_of_succ_le fun k => sN_succ_le C k x

lemma contraction [Nonempty X] (C : Chain X) (habs : C.IsAbsorbing) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ x, sN C n0 x ≤ r := by
  have h1 : ∀ x, ∃ n, sN C n x < 1 := by
    intro x
    by_cases hx : C.P x x = 1
    · exact ⟨0, by rw [sN_abs C hx]; norm_num⟩
    · obtain ⟨n, y, hy, hpos⟩ := habs x
      refine ⟨n, ?_⟩
      have hge : (C.P ^ n) x y ≤ ∑ z, (C.P ^ n) x z * (1 - indN C z) := by
        calc (C.P ^ n) x y = (C.P ^ n) x y * (1 - indN C y) := by simp [indN, hy]
          _ ≤ _ := Finset.single_le_sum (f := fun z => (C.P ^ n) x z * (1 - indN C z))
              (fun z _ => mul_nonneg (pent_nonneg C.P C.nonneg n x z)
                (sub_nonneg.mpr (indN_le_one C z))) (Finset.mem_univ y)
      have hs : sN C n x = ∑ z, (C.P ^ n) x z * indN C z := rfl
      have hsum : ∑ z, (C.P ^ n) x z * (1 - indN C z) = 1 - sN C n x := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, pow_rowsum, hs]
      linarith
  choose n hn using h1
  set N0 : ℕ := Finset.univ.sup n with hN0
  have hle : ∀ x, sN C (N0 + 1) x < 1 := fun x =>
    lt_of_le_of_lt (sN_anti C x (by have := Finset.le_sup (f := n) (Finset.mem_univ x); omega))
      (hn x)
  obtain ⟨xs, -, hxs⟩ := Finset.exists_max_image Finset.univ (fun x => sN C (N0 + 1) x)
    Finset.univ_nonempty
  exact ⟨N0 + 1, Nat.succ_pos _, sN C (N0 + 1) xs, sN_nonneg C _ _, hle xs,
    fun x => hxs x (Finset.mem_univ x)⟩

lemma sN_pow_le (C : Chain X) (n0 : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hs : ∀ x, sN C n0 x ≤ r) :
    ∀ (a : ℕ) (x : X), sN C (a * n0) x ≤ r ^ a := by
  intro a
  induction a with
  | zero => intro x; simpa [sN] using indN_le_one C x
  | succ a ih =>
    intro x
    have e : sN C ((a + 1) * n0) x = ((C.P ^ n0) *ᵥ ((C.P ^ (a * n0)) *ᵥ indN C)) x := by
      unfold sN
      rw [Matrix.mulVec_mulVec, ← pow_add]
      congr 3
      ring
    rw [e]
    have hb : ∀ y, ((C.P ^ (a * n0)) *ᵥ indN C) y ≤ (r ^ a • indN C) y := by
      intro y
      by_cases hy : C.P y y = 1
      · have := sN_abs C hy (a * n0)
        simp only [sN] at this
        simp [this, indN, hy]
      · have := ih y
        simp only [sN] at this
        simpa [indN, hy] using this
    refine (mulVec_pow_mono C n0 hb x).trans ?_
    rw [Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc r ^ a * ((C.P ^ n0) *ᵥ indN C) x ≤ r ^ a * r :=
          mul_le_mul_of_nonneg_left (hs x) (pow_nonneg hr0 a)
      _ = r ^ (a + 1) := by ring

lemma sN_bound (C : Chain X) (n0 : ℕ) (hn0 : 0 < n0) (r : ℝ) (hr0 : 0 ≤ r)
    (hs : ∀ x, sN C n0 x ≤ r) (k : ℕ) (x : X) : sN C k x ≤ r ^ (k / n0) :=
  (sN_anti C x (Nat.div_mul_le_self k n0)).trans (sN_pow_le C n0 r hr0 hs (k / n0) x)

lemma summable_geom_div (n0 : ℕ) (hn0 : 0 < n0) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun k : ℕ => r ^ (k / n0)) := by
  set g : ℕ → ℝ := fun k => r ^ (k / n0) with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => pow_nonneg hr0 _
  have hg1 : ∀ k, g k ≤ 1 := fun k => pow_le_one₀ hr0 hr.le
  have hshift : ∀ k, g (n0 + k) = r * g k := by
    intro k
    simp only [hg]
    rw [Nat.add_comm n0 k, Nat.add_div_right k hn0, pow_succ]
    ring
  refine summable_of_sum_range_le (c := n0 / (1 - r)) hg0 fun K => ?_
  have h1 : ∑ i ∈ range (n0 + K), g i = ∑ i ∈ range n0, g i + ∑ i ∈ range K, g (n0 + i) :=
    Finset.sum_range_add g n0 K
  have h2 : ∑ i ∈ range n0, g i ≤ n0 := by
    calc ∑ i ∈ range n0, g i ≤ ∑ i ∈ range n0, (1 : ℝ) := Finset.sum_le_sum fun i _ => hg1 i
      _ = n0 := by simp
  have h3 : ∑ i ∈ range K, g (n0 + i) = r * ∑ i ∈ range K, g i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hshift i
  have h4 : ∑ i ∈ range K, g i ≤ ∑ i ∈ range (n0 + K), g i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => hg0 i)
  have h5 : (1 - r) * ∑ i ∈ range (n0 + K), g i ≤ n0 := by
    have hS : 0 ≤ ∑ i ∈ range K, g i := Finset.sum_nonneg fun i _ => hg0 i
    nlinarith [h1, h2, h3, h4, mul_le_mul_of_nonneg_left h4 hr0]
  have h6 : ∑ i ∈ range K, g i ≤ n0 / (1 - r) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [h4, h5, hr0]
  exact h6

lemma rbar_abs (C : Chain X) (R : X → X → ℝ) (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    {x : X} (hx : C.P x x = 1) : C.rbar R x = 0 := by
  unfold Chain.rbar
  rw [Finset.sum_eq_single x]
  · rw [hRabs x x hx hx]; ring
  · intro y _ hy; rw [abs_row_zero C hx hy]; ring
  · simp

lemma summable_terms [Nonempty X] (C : Chain X) (R : X → X → ℝ) (γ : ℝ)
    (habs : C.IsAbsorbing) (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (x : X) :
    Summable (fun k : ℕ => γ ^ k * ((C.P ^ k) *ᵥ C.rbar R) x) := by
  obtain ⟨n0, hn0, r, hr0, hr1, hs⟩ := contraction C habs
  set M0 : ℝ := ∑ y, |C.rbar R y| with hM0def
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hrb : ∀ y, |C.rbar R y| ≤ M0 * indN C y := by
    intro y
    by_cases hy : C.P y y = 1
    · simp [indN, hy, rbar_abs C R hRabs hy]
    · simp only [indN, hy, if_false, mul_one]
      exact Finset.single_le_sum (f := fun y => |C.rbar R y|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ y)
  refine Summable.of_norm_bounded (g := fun k => M0 * r ^ (k / n0))
    ((summable_geom_div n0 hn0 r hr0 hr1).mul_left M0) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hγ0]
  have h1 : |((C.P ^ k) *ᵥ C.rbar R) x| ≤ M0 * sN C k x := by
    calc |∑ y, (C.P ^ k) x y * C.rbar R y| ≤ ∑ y, |(C.P ^ k) x y * C.rbar R y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, (C.P ^ k) x y * (M0 * indN C y) := Finset.sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_nonneg (pent_nonneg C.P C.nonneg k x y)]
          exact mul_le_mul_of_nonneg_left (hrb y) (pent_nonneg C.P C.nonneg k x y)
      _ = M0 * sN C k x := by
          unfold sN
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
  have h2 := sN_bound C n0 hn0 r hr0 hs k x
  calc γ ^ k * |((C.P ^ k) *ᵥ C.rbar R) x| ≤ 1 * (M0 * sN C k x) :=
        mul_le_mul (pow_le_one₀ hγ0 hγ1) h1 (abs_nonneg _) zero_le_one
    _ ≤ M0 * r ^ (k / n0) := by rw [one_mul]; exact mul_le_mul_of_nonneg_left h2 hM0

lemma value_identity [Nonempty X] (C : Chain X) (R : X → X → ℝ) (γ : ℝ)
    (habs : C.IsAbsorbing) (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (x : X) :
    C.rbar R x = C.value R γ x - γ * ∑ y, C.P x y * C.value R γ y := by
  have hs := summable_terms C R γ habs hRabs hγ0 hγ1
  set a : ℕ → X → ℝ := fun k y => γ ^ k * ((C.P ^ k) *ᵥ C.rbar R) y with ha
  have e1 : ∑ y, C.P x y * C.value R γ y =
      ∑' k, γ ^ k * ((C.P ^ (k + 1)) *ᵥ C.rbar R) x := by
    have h1 : ∀ y, C.P x y * C.value R γ y = ∑' k, C.P x y * a k y := fun y => by
      unfold Chain.value; rw [tsum_mul_left]
    simp_rw [h1]
    rw [← Summable.tsum_finsetSum (fun y _ => (hs y).mul_left (C.P x y))]
    refine tsum_congr fun k => ?_
    try simp only [ha]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have e2 : C.value R γ x = a 0 x + ∑' k, a (k + 1) x := (hs x).tsum_eq_zero_add
  have e3 : γ * ∑' k, γ ^ k * ((C.P ^ (k + 1)) *ᵥ C.rbar R) x = ∑' k, a (k + 1) x := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    simp only [ha]; ring
  have e4 : a 0 x = C.rbar R x := by simp [ha]
  rw [e1, e3]
  linarith

lemma exists_theta (C : Chain X) (φ : X → Fin m → ℝ)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0) (v : X → ℝ) (hv : ∀ x, C.P x x = 1 → v x = 0) :
    ∃ θ : Fin m → ℝ, ∀ x, v x = ∑ i, φ x i * θ i := by
  let e : C.Nonabsorbing ≃ Fin m := Fintype.equivFinOfCardEq hm.symm
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j => φ (e.symm i).val j
  have hA : LinearIndependent ℝ (fun i => A i) := hli.comp e.symm e.symm.injective
  have hU : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp hA
  let target : Fin m → ℝ := fun i => v (e.symm i).val
  obtain ⟨θ', hθ'⟩ : ∃ θ' : Fin m → ℝ, θ' = A⁻¹ *ᵥ target := ⟨_, rfl⟩
  refine ⟨θ', fun x => ?_⟩
  by_cases hx : C.P x x = 1
  · rw [hv x hx, hφabs x hx]; simp
  · have key : A *ᵥ θ' = target := by
      rw [hθ', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det A).mp hU), Matrix.one_mulVec]
    have := congrFun key (e ⟨x, hx⟩)
    have he : e.symm (e ⟨x, hx⟩) = ⟨x, hx⟩ := e.symm_apply_apply _
    simp only [Matrix.mulVec, dotProduct, A, target, he] at this
    exact this.symm

theorem value_consistency [Nonempty X] (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ) (γ : ℝ)
    (habs : C.IsAbsorbing) (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k *
        (Matrix.mulVec (C.P ^ k) (C.rbar R)) x)) ∧
      (∀ x, C.value R γ x = ∑ i, φ x i * θstar i) ∧
      C.rbar R = Matrix.mulVec (1 - γ • C.P)
        (Matrix.mulVec (Matrix.of φ) θstar) := by
  have hv : ∀ x, C.P x x = 1 → C.value R γ x = 0 := by
    intro x hx
    unfold Chain.value
    have : ∀ k : ℕ, γ ^ k * ((C.P ^ k) *ᵥ C.rbar R) x = 0 := fun k => by
      rw [abs_pow_mulVec C hx, rbar_abs C R hRabs hx, mul_zero]
    simp [this]
  obtain ⟨θ, hθ⟩ := exists_theta C φ hm hli hφabs (C.value R γ) hv
  refine ⟨θ, summable_terms C R γ habs hRabs hγ0 hγ1, hθ, ?_⟩
  have hΦ : Matrix.mulVec (Matrix.of φ) θ = C.value R γ := by
    ext x
    simp [Matrix.mulVec, dotProduct, hθ x]
  rw [hΦ]
  ext x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [value_identity C R γ habs hRabs hγ0 hγ1 x]
  simp [Matrix.mulVec, dotProduct]

end M1V

end

section

set_option autoImplicit false

namespace LSTD8601

open LeastSquaresTD.Absorbing

/-- Maximum-principle step: if `u` vanishes on absorbing states and satisfies
`u x = γ ∑ P x y u y` on non-absorbing states, then `u = 0`. -/
theorem u_eq_zero {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (γ : ℝ) (u : X → ℝ)
    (habs : C.IsAbsorbing) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (huabs : ∀ x, C.P x x = 1 → u x = 0)
    (hfix : ∀ x, C.P x x ≠ 1 → u x = γ * ∑ y, C.P x y * u y) :
    ∀ x, u x = 0 := by
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image Finset.univ (fun x => |u x|)
    Finset.univ_nonempty
  set M := |u x0| with hM
  have hle : ∀ x, |u x| ≤ M := fun x => hx0 x (Finset.mem_univ _)
  by_contra hne
  push Not at hne
  obtain ⟨x1, hx1⟩ := hne
  have hMpos : 0 < M := lt_of_lt_of_le (abs_pos.mpr hx1) (hle x1)
  -- closure: from a state attaining the max, every successor attains it
  have hclos : ∀ x, |u x| = M → ∀ y, 0 < C.P x y → |u y| = M := by
    intro x hx y hy
    have hxna : C.P x x ≠ 1 := by
      intro h; rw [huabs x h, abs_zero] at hx; linarith
    have hux := hfix x hxna
    have h1 : M ≤ γ * ∑ y, C.P x y * |u y| := by
      rw [← hx, hux, abs_mul, abs_of_nonneg hγ0]
      apply mul_le_mul_of_nonneg_left _ hγ0
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [abs_mul, abs_of_nonneg (C.nonneg x z)]
    have hs0 : 0 ≤ ∑ y, C.P x y * |u y| :=
      Finset.sum_nonneg (fun z _ => mul_nonneg (C.nonneg x z) (abs_nonneg _))
    have h2 : M ≤ ∑ y, C.P x y * |u y| := by
      have : γ * ∑ y, C.P x y * |u y| ≤ ∑ y, C.P x y * |u y| := by
        nlinarith
      linarith
    have h3 : ∑ y, C.P x y * (M - |u y|) = 0 := by
      have hsum : ∑ y, C.P x y * (M - |u y|) = M - ∑ y, C.P x y * |u y| := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, C.row_sum x, one_mul]
      have h4 : 0 ≤ ∑ y, C.P x y * (M - |u y|) :=
        Finset.sum_nonneg (fun z _ => mul_nonneg (C.nonneg x z) (by linarith [hle z]))
      linarith
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => mul_nonneg (C.nonneg x z) (by linarith [hle z]))).mp h3 y (Finset.mem_univ _)
    rcases mul_eq_zero.mp h5 with h | h
    · linarith
    · linarith
  have hx0M : |u x0| = M := rfl
  have hreach : ∀ n y, |u y| ≠ M → (C.P ^ n) x0 y = 0 := by
    intro n
    induction n with
    | zero =>
      intro y hy
      have : x0 ≠ y := by rintro rfl; exact hy hx0M
      simp [Matrix.one_apply_ne this]
    | succ n ih =>
      intro y hy
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun z _ => ?_)
      by_cases hz : |u z| = M
      · have : C.P z y = 0 := by
          rcases (C.nonneg z y).lt_or_eq with h | h
          · exact absurd (hclos z hz y h) hy
          · exact h.symm
        rw [this, mul_zero]
      · rw [ih z hz, zero_mul]
  obtain ⟨n, y, hyy, hpos⟩ := habs x0
  have hyM : |u y| = M := by
    by_contra h; rw [hreach n y h] at hpos; exact lt_irrefl _ hpos
  rw [huabs y hyy, abs_zero] at hyM
  linarith

end LSTD8601

open LeastSquaresTD.Absorbing Matrix in
theorem lmi_main {m : ℕ}
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ)
    (habs : C.IsAbsorbing) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hπ : ∀ x : C.Nonabsorbing, 0 < π x.val) :
    IsUnit (limitMatrix C φ γ π) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  suffices H : ∀ w, limitMatrix C φ γ π *ᵥ w = 0 → w = 0 by
    intro a b hab
    have := H (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
    exact sub_eq_zero.mp this
  intro w hw
  set u : X → ℝ := fun x => φ x ⬝ᵥ w with hu_def
  have hu : Matrix.of φ *ᵥ w = u := rfl
  set z : X → ℝ := Matrix.diagonal π *ᵥ ((1 - γ • C.P) *ᵥ u) with hz_def
  have hw' : (Matrix.of φ)ᵀ *ᵥ z = 0 := by
    rw [← hw, hz_def, ← hu]
    simp only [limitMatrix, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hsum : ∑ x, z x • φ x = 0 := by
    ext i
    have := congrFun hw' i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  have hsumN : ∑ x : C.Nonabsorbing, z x.val • φ x.val = 0 := by
    rw [← hsum]
    rw [← Finset.sum_filter_of_ne (p := fun x => C.P x x ≠ 1)]
    · exact (Finset.sum_subtype (Finset.univ.filter (fun x => C.P x x ≠ 1))
        (by simp) (fun x => z x • φ x)).symm
    · intro x _ hx hxx
      apply hx
      rw [hφabs x hxx, smul_zero]
  have hzN := Fintype.linearIndependent_iff.mp hli (fun x => z x.val) hsumN
  have hQ : ∀ x, ((1 - γ • C.P) *ᵥ u) x = u x - γ * ∑ y, C.P x y * u y := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
  have hfix : ∀ x, C.P x x ≠ 1 → u x = γ * ∑ y, C.P x y * u y := by
    intro x hx
    have h0 : z x = 0 := hzN ⟨x, hx⟩
    rw [hz_def, Matrix.mulVec_diagonal, hQ] at h0
    have hp : π x ≠ 0 := (hπ ⟨x, hx⟩).ne'
    have := (mul_eq_zero.mp h0).resolve_left hp
    linarith
  have huabs : ∀ x, C.P x x = 1 → u x = 0 := by
    intro x hx
    simp [hu_def, hφabs x hx]
  have hu0 := LSTD8601.u_eq_zero C γ u habs hγ0 hγ1 huabs hfix
  let e : C.Nonabsorbing ≃ Fin m := Fintype.equivFinOfCardEq hm.symm
  let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i => φ (e.symm i).val
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli.comp e.symm e.symm.injective
  apply Matrix.mulVec_injective_iff_isUnit.mpr hA
  rw [Matrix.mulVec_zero]
  funext i
  exact hu0 (e.symm i).val


end


set_option autoImplicit false

open MeasureTheory Filter Topology LeastSquaresTD.Absorbing in
theorem solution {m : ℕ}
    {X Ω : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Chain X) (S : X → ℝ) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (γ : ℝ) (Z : ℕ → Ω → X)
    (habs : C.IsAbsorbing) (hS_nonneg : ∀ x, 0 ≤ S x)
    (hS_sum : ∑ x, S x = 1) (haccess : C.AllAccessible S)
    (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hlaw : HasRestartLaw C S μ Z) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k *
        (Matrix.mulVec (C.P ^ k) (C.rbar R)) x)) ∧
      (∀ x, C.value R γ x = ∑ i, φ x i * θstar i) ∧
      (∀ᵐ ω ∂μ, Tendsto
        (fun n => lstdTheta C R φ γ (fun k => Z k ω) n)
        atTop (𝓝 θstar)) := by
  obtain ⟨θ, hsum, hval, hr⟩ := M1V.value_consistency C R φ γ habs hRabs hm hli hφabs hγ0 hγ1
  have hirr := M1A.restart_irreducible C S habs hS_nonneg hS_sum haccess
  have hnn : ∀ x y, 0 ≤ C.restartKernel S x y := M1A.restart_nonneg C S hS_nonneg
  have hrow : ∀ x, ∑ y, C.restartKernel S x y = 1 := M1A.restart_row C S hS_sum
  obtain ⟨π, hπnn, hπsum, hπP⟩ := M1.exists_stationary_of_stochastic (C.restartKernel S) hnn hrow
  have hπpos := M1.stationary_pos_of_irreducible (C.restartKernel S) hnn hirr π hπnn hπsum hπP
  let C' : Chain X := ⟨C.restartKernel S, hnn, hrow⟩
  have hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x} :=
    fun n x => hlaw.1 n (measurableSet_singleton x)
  have hfreq := M1F.pair_freq μ (C.restartKernel S) hnn hrow hirr π hπsum hπP S hS_nonneg
    hS_sum Z hmeas hlaw.2
  obtain ⟨hMeq, hveq, hest⟩ := M1A4.restart_lstd_identities C C' S rfl R φ hφabs γ π
  have hunit : IsUnit (limitMatrix C' φ γ π) := by
    rw [hMeq]
    exact lmi_main C φ γ π habs hγ0 hγ1 hm hli hφabs (fun x => hπpos x.val)
  have hv : limitVector C R φ π = Matrix.mulVec (limitMatrix C φ γ π) θ := by
    unfold limitVector limitMatrix
    rw [hr]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hU : IsUnit (limitMatrix C φ γ π) := hMeq ▸ hunit
  have hid : Matrix.mulVec (limitMatrix C φ γ π)⁻¹ (limitVector C R φ π) = θ := by
    rw [hv, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
  refine ⟨θ, hsum, hval, ?_⟩
  filter_upwards [hfreq] with ω hω
  have hlim := M1L.path_lstd C' R φ γ π (fun k => Z k ω) (fun x y => hω x y) hunit
  rw [hMeq, hveq, hid] at hlim
  have hfun : (fun n => chainLstdTheta R φ γ (fun k => Z k ω) n) =
      fun n => lstdTheta C R φ γ (fun k => Z k ω) n := funext fun n => hest _ n
  rwa [hfun] at hlim
