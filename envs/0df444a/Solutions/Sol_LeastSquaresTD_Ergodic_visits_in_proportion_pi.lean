-- Prove2me | solution 1 for LeastSquaresTD.Ergodic.visits_in_proportion_pi
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T21:56:34.050971+00:00
-- url     : https://prove2.me/submissions/6fc44081-42a0-4ef1-9ed5-ec4878a1f5e5

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


set_option autoImplicit false

open MeasureTheory Matrix Filter Topology LeastSquaresTD.Ergodic in
theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (hC : C.IsErgodic) (π : X → ℝ) (hπ : C.IsStationary π)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : X → ℝ) (hν : IsProbVec ν) (Z : ℕ → Ω → X) (hZ : IsMarkovLaw μ C ν Z) :
    (∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => visitCount (fun k => Z k ω) x t) atTop atTop) ∧
    (∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => (visitCount (fun k => Z k ω) x t : ℝ) / t) atTop (𝓝 (π x))) := by
  have hV : ∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => (visitCount (fun k => Z k ω) x t : ℝ) / t) atTop (𝓝 (π x)) :=
    M1F.visit_freq μ C.P C.nonneg C.row_sum hC π hπ.2.1 hπ.2.2 ν hν.1 hν.2 Z hZ.1 hZ.2
  have hpos : ∀ x, 0 < π x :=
    M1.stationary_pos_of_irreducible C.P C.nonneg hC π hπ.1 hπ.2.1 hπ.2.2
  refine ⟨?_, hV⟩
  filter_upwards [hV] with ω hω x
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  have hmul := (hω x).pos_mul_atTop (hpos x) tendsto_natCast_atTop_atTop
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htpos : (t : ℝ) ≠ 0 := by positivity
  field_simp
