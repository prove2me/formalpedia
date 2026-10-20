-- Prove2me | solution 1 for LeastSquaresTD.Ergodic.lemma5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T21:23:34.523755+00:00
-- url     : https://prove2.me/submissions/8ad08354-915a-45e8-a0bb-651245b03a49

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD

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


set_option autoImplicit false

open MeasureTheory Filter Topology Matrix

namespace L5E

open LeastSquaresTD.Ergodic

theorem pair_freq_of_visits {X : Type*} [Fintype X] [DecidableEq X]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Matrix X X ℝ) (hnn : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (π : X → ℝ) (ν : X → ℝ) (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (Z : ℕ → Ω → X) (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (hlaw : ∀ (n : ℕ) (xs : Fin (n + 1) → X),
      μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} =
        ENNReal.ofReal (ν (xs 0) * ∏ i : Fin n, P (xs i.castSucc) (xs i.succ)))
    (hV : ∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => (visitCount (fun k => Z k ω) x t : ℝ) / t) atTop (𝓝 (π x))) :
    ∀ᵐ ω ∂μ, ∀ x y : X,
      Tendsto (fun t : ℕ => (pairCount (fun k => Z k ω) x y t : ℝ) / t) atTop
        (𝓝 (π x * P x y)) := by
  have hall : ∀ x y : X, ∀ᵐ ω ∂μ,
      Tendsto (fun t : ℕ => (pairCount (fun k => Z k ω) x y t : ℝ) / t) atTop
        (𝓝 (π x * P x y)) := by
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
        (pairCount (fun k => Z k ω) x y t : ℝ) -
          P x y * (visitCount (fun k => Z k ω) x t : ℝ) := by
      intro t
      simp only [hh_def, Finset.sum_sub_distrib, Finset.sum_boole, pairCount, visitCount]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      ring
    have hfin : Tendsto (fun t : ℕ => (1 / (t : ℝ)) *
        ∑ k ∈ Finset.range t, h (Z k ω) (Z (k + 1) ω) +
          P x y * ((visitCount (fun k => Z k ω) x t : ℝ) / t))
        atTop (𝓝 (π x * P x y)) := by
      have := hω.add ((hVω x).const_mul (P x y))
      simpa [mul_comm] using this
    refine hfin.congr fun t => ?_
    rw [hid t]
    ring
  exact ae_all_iff.mpr fun x => ae_all_iff.mpr (hall x)

lemma sum_pairs {X : Type*} [Fintype X] [DecidableEq X] {M : Type*} [AddCommMonoid M]
    [Module ℝ M] (z : ℕ → X) (t : ℕ) (f : X → X → M) :
    ∑ k ∈ Finset.range t, f (z k) (z (k + 1)) =
      ∑ x, ∑ y, (pairCount z x y t : ℝ) • f x y := by
  have h : ∀ x y, (pairCount z x y t : ℝ) • f x y =
      ∑ k ∈ Finset.range t, if z k = x ∧ z (k + 1) = y then f x y else 0 := by
    intro x y
    rw [pairCount, Finset.card_filter, Nat.cast_sum, Finset.sum_smul]
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

lemma scale_pairs {X : Type*} [Fintype X] {M : Type*} [AddCommGroup M] [Module ℝ M]
    (t : ℕ) (F : X → X → M) (c : X → X → ℝ) :
    (1 / (t : ℝ)) • ∑ x, ∑ y, c x y • F x y = ∑ x, ∑ y, (c x y / t) • F x y := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]; congr 1; ring

theorem path_lstd {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}
    (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ) (z : ℕ → X)
    (hfreq : ∀ x y : X,
      Tendsto (fun t : ℕ => (pairCount z x y t : ℝ) / t) atTop (𝓝 (π x * C.P x y)))
    (hM : IsUnit (lemma5Matrix C φ π γ)) :
    Tendsto (fun t : ℕ => lstdTheta φ R γ t z) atTop
      (𝓝 ((lemma5Matrix C φ π γ)⁻¹ *ᵥ lemma5Vector C R φ π)) := by
  set V : X → X → Matrix (Fin m) (Fin m) ℝ :=
    fun x y => Matrix.vecMulVec (φ x) (φ x - γ • φ y) with hV
  set W : X → X → (Fin m → ℝ) := fun x y => R x y • φ x with hW
  set Ab : ℕ → Matrix (Fin m) (Fin m) ℝ :=
    fun t => ∑ x, ∑ y, ((pairCount z x y t : ℝ) / t) • V x y with hAb
  set Bb : ℕ → (Fin m → ℝ) :=
    fun t => ∑ x, ∑ y, ((pairCount z x y t : ℝ) / t) • W x y with hBb
  have hA : ∀ t : ℕ, lstdA φ γ t z = Ab t := by
    intro t
    have e : lstdA φ γ t z = (1 / (t : ℝ)) • ∑ k ∈ Finset.range t, V (z k) (z (k + 1)) := rfl
    rw [e, sum_pairs z t V]
    exact scale_pairs t V (fun x y => (pairCount z x y t : ℝ))
  have hB : ∀ t : ℕ, lstdB φ R t z = Bb t := by
    intro t
    have e : lstdB φ R t z = (1 / (t : ℝ)) • ∑ k ∈ Finset.range t, W (z k) (z (k + 1)) := rfl
    rw [e, sum_pairs z t W]
    exact scale_pairs t W (fun x y => (pairCount z x y t : ℝ))
  have hMeq : lemma5Matrix C φ π γ = ∑ x, ∑ y, (π x * C.P x y) • V x y := by
    ext i j
    simp only [lemma5Matrix, featureMatrix, hV, Matrix.mul_apply, Matrix.diagonal_apply,
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
  have hVeq : lemma5Vector C R φ π = ∑ x, ∑ y, (π x * C.P x y) • W x y := by
    ext i
    simp only [lemma5Vector, featureMatrix, hW, Chain.rbar, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.of_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have tA : Tendsto Ab atTop (𝓝 (lemma5Matrix C φ π γ)) := by
    rw [hMeq]
    refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => ?_
    exact (hfreq x y).smul_const _
  have tB : Tendsto Bb atTop (𝓝 (lemma5Vector C R φ π)) := by
    rw [hVeq]
    refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => ?_
    exact (hfreq x y).smul_const _
  have hdet : (lemma5Matrix C φ π γ).det ≠ 0 := by
    rw [Matrix.isUnit_iff_isUnit_det] at hM
    exact hM.ne_zero
  have hinv : ContinuousAt Inv.inv (lemma5Matrix C φ π γ) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have tI := hinv.tendsto.comp tA
  have hc : Continuous fun p : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => p.1 *ᵥ p.2 :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  have hlim := (hc.tendsto _).comp (tI.prodMk_nhds tB)
  refine hlim.congr fun t => ?_
  simp only [Function.comp, lstdTheta, hA t, hB t]

end L5E

open MeasureTheory Matrix Filter Topology LeastSquaresTD.Ergodic in
theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (R : X → X → ℝ) {m : ℕ} (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : X → ℝ) (hν : IsProbVec ν) (Z : ℕ → Ω → X) (hZ : IsMarkovLaw μ C ν Z)
    (h2 : ∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => visitCount (fun k => Z k ω) x t) atTop atTop)
    (h3 : ∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => (visitCount (fun k => Z k ω) x t : ℝ) / t) atTop (𝓝 (π x)))
    (h4 : IsUnit (lemma5Matrix C φ π γ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℕ => lstdTheta φ R γ t (fun k => Z k ω)) atTop
      (𝓝 ((lemma5Matrix C φ π γ)⁻¹ *ᵥ lemma5Vector C R φ π)) := by
  have hF := L5E.pair_freq_of_visits μ C.P C.nonneg C.row_sum π ν hν.1 hν.2 Z hZ.1 hZ.2 h3
  filter_upwards [hF] with ω hω
  exact L5E.path_lstd C R φ γ π _ hω h4
