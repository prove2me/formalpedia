-- Prove2me | solution 1 for MomentComparison.baseThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:44.846337+00:00
-- url     : https://prove2.me/submissions/ff909b52-f769-4229-a64f-32cea8a4703e

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_RealHypercontractivity
public import Theorems.Thm_MomentComparison_constant_of_hasDegreeLE_zero
public import Theorems.Thm_MomentComparison_cubeAverage_cons
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeAverage_const_mul
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty


section
public section
open scoped BigOperators
namespace MomentComparison
private theorem average_nonneg {n : ℕ} {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeAverage f :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) (by positivity)
private theorem average_cauchy_schwarz {n : ℕ} (f g : Cube n → ℝ) :
    cubeAverage (fun x => f x * g x) ^ 2 ≤
      cubeAverage (fun x => f x ^ 2) * cubeAverage (fun x => g x ^ 2) := by
  unfold cubeAverage
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  rw [div_pow, div_mul_div_comm, ← pow_two]
  exact div_le_div_of_nonneg_right h (by positivity)
private theorem degree_evenPart {n d : ℕ} {f : Cube (n + 1) → ℝ}
    (hf : HasDegreeLE f d) : HasDegreeLE (evenPart f) d := by
  intro s hs
  have h := hf (s.map (Fin.succEmb n)) (by simpa using hs)
  rw [cubeAverage_cons] at h
  simp only [Finset.prod_map, Fin.coe_succEmb, Fin.cons_succ] at h
  unfold cubeAverage evenPart at *
  convert h using 1
  rw [← add_div, div_right_comm, ← Finset.sum_add_distrib]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring
private theorem degree_oddPart {n d : ℕ} {f : Cube (n + 1) → ℝ}
    (hf : HasDegreeLE f (d + 1)) : HasDegreeLE (oddPart f) d := by
  intro s hs
  have hz : (0 : Fin (n + 1)) ∉ s.map (Fin.succEmb n) := by simp
  have h := hf (insert 0 (s.map (Fin.succEmb n))) (by simpa [Finset.card_insert_of_notMem hz] using Nat.succ_lt_succ hs)
  rw [cubeAverage_cons] at h
  simp only [Finset.prod_insert hz, Finset.prod_map, Fin.coe_succEmb, Fin.cons_succ,
    Fin.cons_zero, ite_true, Bool.false_eq_true, ite_false, one_mul, neg_one_mul] at h
  unfold cubeAverage oddPart at *
  convert h using 1
  rw [← add_div, div_right_comm, ← Finset.sum_add_distrib]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring
private theorem average_add {n : ℕ} (f g : Cube n → ℝ) :
    cubeAverage (fun x => f x + g x) = cubeAverage f + cubeAverage g := by
  simp [cubeAverage, Finset.sum_add_distrib, add_div]
private theorem evenMoment_two {n : ℕ} (f : Cube (n + 1) → ℝ) :
    cubeAverage (fun x => f x ^ 2) =
      cubeAverage (fun x => evenPart f x ^ 2) + cubeAverage (fun x => oddPart f x ^ 2) := by
  rw [cubeAverage_cons, ← average_add, div_eq_inv_mul, ← cubeAverage_const_mul, ← average_add]
  congr 1
  funext x
  unfold evenPart oddPart
  ring
private theorem evenMoment_four {n : ℕ} (f : Cube (n + 1) → ℝ) :
    cubeAverage (fun x => f x ^ 4) =
      cubeAverage (fun x => evenPart f x ^ 4) +
      6 * cubeAverage (fun x => evenPart f x ^ 2 * oddPart f x ^ 2) +
      cubeAverage (fun x => oddPart f x ^ 4) := by
  rw [cubeAverage_cons, ← average_add, div_eq_inv_mul, ← cubeAverage_const_mul,
    ← cubeAverage_const_mul, ← average_add, ← average_add]
  congr 1
  funext x
  unfold evenPart oddPart
  ring
private theorem fourthMoment_of_constant {n : ℕ} (a : ℝ) :
    cubeAverage (fun _ : Cube n => a ^ 4) = cubeAverage (fun _ : Cube n => a ^ 2) ^ 2 := by
  simp only [cubeAverage_const]
  ring
private theorem fourthMoment_split {n d : ℕ} (f : Cube (n + 1) → ℝ)
    (he : cubeAverage (fun x => evenPart f x ^ 4) ≤
      ((3 : ℝ) ^ (d + 1) * cubeAverage (fun x => evenPart f x ^ 2)) ^ 2)
    (ho : cubeAverage (fun x => oddPart f x ^ 4) ≤
      ((3 : ℝ) ^ d * cubeAverage (fun x => oddPart f x ^ 2)) ^ 2) :
    cubeAverage (fun x => f x ^ 4) ≤
      ((3 : ℝ) ^ (d + 1) * cubeAverage (fun x => f x ^ 2)) ^ 2 := by
  let A := (3 : ℝ) ^ (d + 1) * cubeAverage (fun x => evenPart f x ^ 2)
  let B := (3 : ℝ) ^ d * cubeAverage (fun x => oddPart f x ^ 2)
  have hA : 0 ≤ A := mul_nonneg (by positivity) (average_nonneg fun _ => sq_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (by positivity) (average_nonneg fun _ => sq_nonneg _)
  have he₀ := average_nonneg (f := fun x => evenPart f x ^ 4) (fun _ => by positivity)
  have hAB : cubeAverage (fun x => evenPart f x ^ 2 * oddPart f x ^ 2) ≤ A * B := by
    have hc := average_cauchy_schwarz (fun x => evenPart f x ^ 2) (fun x => oddPart f x ^ 2)
    simp only [← pow_mul] at hc
    change _ ≤ cubeAverage (fun x => evenPart f x ^ 4) *
      cubeAverage (fun x => oddPart f x ^ 4) at hc
    have h := hc.trans (mul_le_mul he ho
      (average_nonneg fun _ => by positivity) (sq_nonneg A))
    rw [← mul_pow] at h
    exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hA hB) h
  rw [evenMoment_four, evenMoment_two, mul_add]
  calc
    _ ≤ A ^ 2 + 6 * (A * B) + B ^ 2 := by linarith only [he, ho, hAB]
    _ ≤ (A + 3 * B) ^ 2 := by nlinarith only [sq_nonneg B]
    _ = _ := by simp [A, B, pow_succ]; ring
private theorem fourthMoment_bound
    {n d : ℕ} {f : Cube n → ℝ} (hf : HasDegreeLE f d) :
    cubeAverage (fun x => f x ^ 4) ≤ ((3 : ℝ) ^ d * cubeAverage (fun x => f x ^ 2)) ^ 2 := by
  induction n generalizing d with
  | zero =>
    let x₀ : Cube 0 := fun i => Fin.elim0 i
    have h : f = fun _ => f x₀ := funext fun x => congrArg f (Subsingleton.elim x x₀)
    rw [h, fourthMoment_of_constant]
    have hd : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    have hnonneg := average_nonneg (f := fun _ : Cube 0 => f x₀ ^ 2) (fun _ => sq_nonneg _)
    gcongr
    simpa using mul_le_mul_of_nonneg_right hd hnonneg
  | succ n ih =>
    cases d with
    | zero =>
      obtain ⟨a, ha⟩ := constant_of_hasDegreeLE_zero hf
      rw [show f = fun _ => a from funext ha, fourthMoment_of_constant]
      simp
    | succ d =>
      exact fourthMoment_split f (ih (degree_evenPart hf)) (ih (degree_oddPart hf))
private theorem normComparison_of_fourthMoment {n : ℕ} (f : Cube n → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hfour : cubeAverage (fun x => f x ^ 4) ≤ (K * cubeAverage (fun x => f x ^ 2)) ^ 2) :
    Real.sqrt (cubeAverage (fun x => f x ^ 2)) ≤ K * cubeAverage (fun x => |f x|) := by
  let A := cubeAverage (fun x => |f x|)
  let B := cubeAverage (fun x => f x ^ 2)
  let M := cubeAverage (fun x => |f x| ^ 3)
  let D := cubeAverage (fun x => f x ^ 4)
  have hA : 0 ≤ A := average_nonneg fun _ => abs_nonneg _
  have hB : 0 ≤ B := average_nonneg fun _ => sq_nonneg _
  have hM : 0 ≤ M := average_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  change D ≤ (K * B) ^ 2 at hfour
  have hBM : B ^ 2 ≤ A * M := by
    have h := average_cauchy_schwarz (fun x => Real.sqrt |f x|) (fun x => Real.sqrt |f x| ^ 3)
    have hs (x : Cube n) : Real.sqrt |f x| ^ 2 = |f x| := Real.sq_sqrt (abs_nonneg _)
    have hsix (x : Cube n) : (Real.sqrt |f x| ^ 3) ^ 2 = |f x| ^ 3 := by
      rw [← pow_mul, show 3 * 2 = 2 * 3 by decide, pow_mul, hs]
    have hprod (x : Cube n) : Real.sqrt |f x| * Real.sqrt |f x| ^ 3 = f x ^ 2 := by
      calc
        _ = (Real.sqrt |f x| ^ 2) ^ 2 := by ring
        _ = _ := by rw [hs, sq_abs]
    simpa only [hs, hsix, hprod] using h
  have hMD : M ^ 2 ≤ B * D := by
    have h := average_cauchy_schwarz (fun x => |f x|) (fun x => f x ^ 2)
    have hc (x : Cube n) : |f x| * f x ^ 2 = |f x| ^ 3 := by rw [← sq_abs (f x)]; ring
    simpa only [← pow_mul, sq_abs, hc] using h
  by_cases hb : B = 0
  · change Real.sqrt B ≤ K * A
    rw [hb, Real.sqrt_zero]
    exact mul_nonneg hK hA
  have hbpos := lt_of_le_of_ne hB (Ne.symm hb)
  have hbound : B * B ^ 3 ≤ (K * A) ^ 2 * B ^ 3 := by
    calc
      _ = (B ^ 2) ^ 2 := by ring
      _ ≤ (A * M) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hBM _
      _ = A ^ 2 * M ^ 2 := mul_pow _ _ _
      _ ≤ A ^ 2 * (B * D) := mul_le_mul_of_nonneg_left hMD (sq_nonneg _)
      _ ≤ A ^ 2 * (B * (K * B) ^ 2) := by gcongr
      _ = _ := by ring
  change Real.sqrt B ≤ K * A
  apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hK hA)
  rw [Real.sq_sqrt hB]
  exact le_of_mul_le_mul_right hbound (pow_pos hbpos _)
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {n d : ℕ} {f : Cube n → ℝ} (hf : HasDegreeLE f d) :
    Real.sqrt (cubeAverage fun x => f x ^ 2) ≤ (3 : ℝ) ^ d * cubeAverage (fun x => |f x|) :=
  normComparison_of_fourthMoment f _ (by positivity) (fourthMoment_bound hf)
end MomentComparison
