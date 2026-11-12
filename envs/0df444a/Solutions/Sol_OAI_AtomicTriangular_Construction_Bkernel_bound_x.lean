-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.Bkernel_bound_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:35:12.380973+00:00
-- url     : https://prove2.me/submissions/e065c8b0-c5d8-4e0d-82d5-84a74a67bada

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X001
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_envelopeSumBoxB_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_IntegralBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace AtomicTriangular.IntegralVectors
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma weighted_interval_bound {a b t M : ℝ} (hab : a≤b) (hbt : b≤t)
    (f : ℝ → E) (hf : ∀ x ∈ Icc a b, ‖f x‖≤M) :
    ‖∫ x in a..b, (t-x) • f x‖ ≤ ((t-a)^2-(t-b)^2)/2*M := by
  calc
    _ ≤ ∫ x in a..b, (t-x)*M := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
      · exact ae_of_all _ fun x hx => by
          rw [norm_smul,Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr (hx.2.trans hbt))]
          exact mul_le_mul_of_nonneg_left (hf x ⟨hx.1.le,hx.2⟩) (sub_nonneg.mpr (hx.2.trans hbt))
      · exact (show Continuous (fun x : ℝ => (t-x)*M) by fun_prop).intervalIntegrable a b
    _ = _ := by
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_sub (f:=fun _ : ℝ => t)
        (g:=fun x : ℝ => x) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),integral_id]
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      ring

lemma norm_integral_grid {δ : ℝ} (hδ : 0≤δ) (n : ℕ) (f : ℝ → E) (hf : Continuous f)
    (M : ℕ → ℝ) (hM : ∀ i<n, ∀ x ∈ Icc ((i:ℝ)*δ) ((i+1:ℕ)*δ), ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..(n:ℝ)*δ, f x‖ ≤ δ*∑ i ∈ Finset.range n, M i := by
  have hi := intervalIntegral.sum_integral_adjacent_intervals (a:=fun i : ℕ => (i:ℝ)*δ)
    (μ:=volume) (n:=n) (f:=f) (fun i _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero,zero_mul] at hi
  rw [←hi]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖∫ x in (i:ℝ)*δ..(i+1:ℕ)*δ, f x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ*M i := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x hx => hM i (Finset.mem_range.mp hi) x (by
          rw [Set.uIoc_of_le (show (i:ℝ)*δ≤(i+1:ℕ)*δ by push_cast <;> nlinarith)] at hx
          exact ⟨hx.1.le,hx.2⟩))
        (a := (i:ℝ)*δ) (b := (i+1:ℕ)*δ)
      have hd : |((i+1:ℕ):ℝ)*δ-(i:ℝ)*δ|=δ := by
        rw [show ((i+1:ℕ):ℝ)*δ-(i:ℝ)*δ=δ by push_cast; ring,abs_of_nonneg hδ]
      rw [hd] at hh
      simpa only [mul_comm] using hh
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma weighted_integral_grid {δ : ℝ} (hδ : 0≤δ) (n : ℕ) (f : ℝ → E) (hf : Continuous f)
    (M : ℕ → ℝ) (hM : ∀ i<n, ∀ x ∈ Icc ((i:ℝ)*δ) ((i+1:ℕ)*δ), ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..(n:ℝ)*δ, ((n:ℝ)*δ-x) • f x‖ ≤
      δ^2*∑ i ∈ Finset.range n, ((n:ℝ)-i-1/2)*M i := by
  have hc : Continuous (fun x : ℝ => ((n:ℝ)*δ-x) • f x) := by fun_prop
  have hi := intervalIntegral.sum_integral_adjacent_intervals (a:=fun i : ℕ => (i:ℝ)*δ)
    (μ:=volume) (n:=n) (f:=fun x : ℝ => ((n:ℝ)*δ-x) • f x) (fun i _ => hc.intervalIntegrable _ _)
  simp only [Nat.cast_zero,zero_mul] at hi
  rw [←hi]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖∫ x in (i:ℝ)*δ..(i+1:ℕ)*δ, ((n:ℝ)*δ-x) • f x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ^2*((n:ℝ)-i-1/2)*M i := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i+1≤n := Finset.mem_range.mp hi
      have hiR : ((i+1:ℕ):ℝ)≤n := by exact_mod_cast hin
      have hh := weighted_interval_bound (show (i:ℝ)*δ≤(i+1:ℕ)*δ by push_cast <;> nlinarith)
        (mul_le_mul_of_nonneg_right hiR hδ) f (hM i (Finset.mem_range.mp hi))
      calc
        _ ≤ (((n:ℝ)*δ-(i:ℝ)*δ)^2-((n:ℝ)*δ-((i+1:ℕ):ℝ)*δ)^2)/2*M i := by
          exact hh
        _ = _ := by push_cast <;> ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
lemma norm_integral_neg (f : ℝ → E) (t : ℝ) :
    ‖∫ x in (0:ℝ)..-t, f x‖ = ‖∫ x in (0:ℝ)..t, f (-x)‖ := by
  rw [intervalIntegral.integral_comp_neg,neg_zero,intervalIntegral.integral_symm,norm_neg]
lemma norm_weighted_integral_neg (f : ℝ → E) (t : ℝ) :
    ‖∫ x in (0:ℝ)..-t, (-t-x) • f x‖ = ‖∫ x in (0:ℝ)..t, (t-x) • f (-x)‖ := by
  rw [norm_integral_neg]
  simp only [show ∀ x : ℝ, -t- -x=-(t-x) by intro x; ring,neg_smul,
    intervalIntegral.integral_neg,norm_neg]
lemma norm_integral_grid_abs {δ t : ℝ} (hδ : 0≤δ) (n : ℕ) (ht : |t|=(n:ℝ)*δ)
    (f : ℝ → E) (hf : Continuous f) (M : ℕ → ℝ)
    (hM : ∀ i<n, ∀ x, (i:ℝ)*δ≤|x| → |x|≤(i+1:ℕ)*δ → ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..t, f x‖ ≤ δ*∑ i ∈ Finset.range n, M i := by
  rcases le_total 0 t with ht0|ht0
  · rw [abs_of_nonneg ht0] at ht
    rw [ht]
    exact norm_integral_grid hδ n f hf M (fun i hi x hx => hM i hi x
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
  · rw [abs_of_nonpos ht0] at ht
    have hte : t= -((n:ℝ)*δ) := by linarith
    rw [hte,norm_integral_neg]
    exact norm_integral_grid hδ n (fun x => f (-x)) (hf.comp continuous_neg) M (fun i hi x hx => hM i hi (-x)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
lemma weighted_integral_grid_abs {δ t : ℝ} (hδ : 0≤δ) (n : ℕ) (ht : |t|=(n:ℝ)*δ)
    (f : ℝ → E) (hf : Continuous f) (M : ℕ → ℝ)
    (hM : ∀ i<n, ∀ x, (i:ℝ)*δ≤|x| → |x|≤(i+1:ℕ)*δ → ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..t, (t-x) • f x‖ ≤ δ^2*∑ i ∈ Finset.range n, ((n:ℝ)-i-1/2)*M i := by
  rcases le_total 0 t with ht0|ht0
  · rw [abs_of_nonneg ht0] at ht
    rw [ht]
    exact weighted_integral_grid hδ n f hf M (fun i hi x hx => hM i hi x
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
  · rw [abs_of_nonpos ht0] at ht
    have hte : t= -((n:ℝ)*δ) := by linarith
    rw [hte,norm_weighted_integral_neg]
    exact weighted_integral_grid hδ n (fun x => f (-x)) (hf.comp continuous_neg) M (fun i hi x hx => hM i hi (-x)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
end AtomicTriangular.IntegralVectors
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.Interval

lemma RI.mem_pow {a : RI} {x : ℝ} (hx : a.Mem x) (n : ℕ) : (a.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa [RI.pow] using RI.mem_point 1
  | succ n ih => simpa [RI.pow,pow_succ] using RI.mem_mul ih hx

noncomputable section
open scoped BigOperators

lemma RI.mem_sqrt {a r : RI} {x : ℝ} (hx : a.Mem x) (h₀ : 0 ≤ x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.lo)
    (hr₂ : scale * a.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem (Real.sqrt x) := by
  have hs := Real.sq_sqrt h₀
  have hp := Real.sqrt_nonneg x
  have hrl : (0:ℝ) ≤ r.lo := by exact_mod_cast hr₀
  have hrh : (0:ℝ) ≤ r.hi := by exact_mod_cast hr₃
  have hrls : (r.lo:ℝ) * r.lo ≤ (scale:ℝ) * max (0:ℝ) (a.lo:ℝ) := by exact_mod_cast hr₁
  have hrhs : (scale:ℝ) * a.hi ≤ (r.hi:ℝ) * r.hi := by exact_mod_cast hr₂
  have hsl := mul_le_mul_of_nonneg_left (max_le (mul_nonneg scale_pos.le h₀) hx.1) scale_pos.le
  have hsh := mul_le_mul_of_nonneg_left hx.2 scale_pos.le
  have he : ((scale:ℝ) * Real.sqrt x)^2 = (scale:ℝ) * ((scale:ℝ)*x) := by
    rw [mul_pow, hs]
    ring
  constructor <;> nlinarith [mul_nonneg scale_pos.le hp]

lemma CI.mem_norm {a : CI} {r : RI} {x : ℂ} (hx : a.Mem x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.normSq.lo)
    (hr₂ : scale * a.normSq.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem ‖x‖ := by
  have hh := RI.mem_sqrt (CI.mem_normSq hx) (Complex.normSq_nonneg x) hr₀ hr₁ hr₂ hr₃
  simpa [Complex.normSq_eq_norm_sq] using hh

end
end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex

lemma atomPolynomial_factor (a : Fin 15) :
    atomPolynomial = atomFactor a * restPolynomial a := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm

lemma restPolynomial_coeff (a : Fin 15) (n : ℕ) :
    (restPolynomial a).coeff n = phase (-(residue a:ℂ)) *
      (-(atomPolynomial.coeff n) +
        (if n=0 then 0 else 2*(restPolynomial a).coeff (n-1)) -
        (if n<2 then 0 else phase (-(residue a:ℂ))*(restPolynomial a).coeff (n-2))) := by
  have hh := coeff_atom_mul a (restPolynomial a) n
  rw [← atomPolynomial_factor] at hh
  have he : -(atomPolynomial.coeff n) +
      (if n=0 then 0 else 2*(restPolynomial a).coeff (n-1)) -
      (if n<2 then 0 else phase (-(residue a:ℂ))*(restPolynomial a).coeff (n-2)) =
      phase (residue a)*(restPolynomial a).coeff n := by
    linear_combination -hh
  rw [he, ← mul_assoc, phase_neg_mul, one_mul]

lemma recoverRest_mem (a : Fin 15) (e : CI) (he : e.Mem (phase (residue a)))
    (v : Fin 31 → CI) (hv : ∀ j, recoverRest e v j = v j) :
    ∀ j : Fin 31, (v j).Mem ((restPolynomial a).coeff j.val) := by
  have he' : e.conj.Mem (phase (-(residue a:ℂ))) := by
    simpa only [← Complex.ofReal_intCast, phase_conj] using CI.mem_conj he
  suffices hs : ∀ n (hn : n<31), (v ⟨n,hn⟩).Mem ((restPolynomial a).coeff n) from
    fun j => hs j.val j.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [← hv, restPolynomial_coeff]
    simp only [recoverRest]
    apply CI.mem_mul he'
    apply CI.mem_sub
    · apply CI.mem_add (CI.mem_neg (atomPolynomial_coeff_mem ⟨n,hn⟩))
      split_ifs with hz
      · simpa using CI.mem_point 0
      · exact CI.mem_mul (by simpa using CI.mem_point 2) (ih (n-1) (by omega) (by omega))
    · split_ifs with hz
      · simpa using CI.mem_point 0
      · exact CI.mem_mul he' (ih (n-2) (by omega) (by omega))

lemma cCoefficient_eq (a : Fin 15) (j : Fin 31) :
    cCoefficient a j = if j.val=0 then 0
      else 4*(kappa:ℂ)^2*(restPolynomial a).coeff (j.val-1) := by
  simp only [cCoefficient, cShiftPolynomial, coeff_X_mul', cAtomPolynomial, coeff_C_mul,
    restPolynomial]

lemma dCoefficient_eq (a : Fin 15) (j : Fin 31) :
    dCoefficient a j = I*(kappa:ℂ) *
      (phase (residue a)*(restPolynomial a).coeff j.val -
        (if j.val<2 then 0 else phase (-(residue a:ℂ))*(restPolynomial a).coeff (j.val-2))) := by
  change (C (I*(kappa:ℂ)) *
    (C (phase (residue a)) - C (phase (-(residue a:ℂ))) * X^2) * restPolynomial a).coeff j.val = _
  rw [mul_assoc, coeff_C_mul, sub_mul, coeff_sub, coeff_C_mul]
  rw [show C (phase (-(residue a:ℂ))) * X^2 * restPolynomial a =
    C (phase (-(residue a:ℂ))) * (X^2 * restPolynomial a) from mul_assoc _ _ _,
    coeff_C_mul, coeff_X_sq_mul]
  split_ifs <;> ring

end AtomicTriangular.FiniteCertificate

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex
lemma kappaBox_mem : kappaBox.Mem (kappa:ℂ) := by
  have hh := CI.mem_divNat (CI.mem_ofReal piBox_mem) (by norm_num : 0 < (36:ℕ))
  simpa only [kappaBox, kappa, Complex.ofReal_div, Complex.ofReal_ofNat, Nat.cast_ofNat] using hh

lemma cCoeffBox_mem (a : Fin 15) (r : Fin 31 → CI)
    (hr : ∀ j, (r j).Mem ((restPolynomial a).coeff j.val)) (j : Fin 31) :
    (cCoeffBox r j).Mem (cCoefficient a j) := by
  rw [cCoefficient_eq]
  unfold cCoeffBox
  split_ifs
  · simpa using CI.mem_point 0
  · exact CI.mem_mul (CI.mem_mul (by simpa using CI.mem_point 4)
      (CI.mem_pow kappaBox_mem 2)) (hr ⟨j.val-1,by omega⟩)
lemma dCoeffBox_mem (a : Fin 15) (e : CI) (r : Fin 31 → CI)
    (he : e.Mem (phase (residue a)))
    (hr : ∀ j, (r j).Mem ((restPolynomial a).coeff j.val)) (j : Fin 31) :
    (dCoeffBox e r j).Mem (dCoefficient a j) := by
  rw [dCoefficient_eq]
  apply CI.mem_mul (CI.mem_mul CI.mem_imag kappaBox_mem)
  apply CI.mem_sub (CI.mem_mul he (hr j))
  split_ifs
  · simpa using CI.mem_point 0
  · have hh : e.conj.Mem (phase (-(residue a:ℂ))) := by
      simpa only [← Complex.ofReal_intCast, phase_conj] using CI.mem_conj he
    exact CI.mem_mul hh (hr ⟨j.val-2,by omega⟩)

lemma restBox0_calc (j : Fin 31) : recoverRest phaseBox0 restBox0 j = restBox0 j := by
  revert j
  decide +kernel
lemma restBox0_mem (j : Fin 31) : (restBox0 j).Mem ((restPolynomial ⟨0,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨0,by norm_num⟩ phaseBox0
  · have hr : residue ⟨0,by norm_num⟩ = (0:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox0_mem
  · exact restBox0_calc
lemma cBox0_calc (j : Fin 31) : cCoeffBox restBox0 j = cBox0 j := by
  revert j
  decide +kernel
lemma cBox0_mem (j : Fin 31) : (cBox0 j).Mem (cCoefficient ⟨0,by norm_num⟩ j) := by
  rw [← cBox0_calc]
  exact cCoeffBox_mem ⟨0,by norm_num⟩ restBox0 restBox0_mem j
lemma dBox0_calc (j : Fin 31) : dCoeffBox phaseBox0 restBox0 j = dBox0 j := by
  revert j
  decide +kernel
lemma dBox0_mem (j : Fin 31) : (dBox0 j).Mem (dCoefficient ⟨0,by norm_num⟩ j) := by
  rw [← dBox0_calc]
  apply dCoeffBox_mem ⟨0,by norm_num⟩ phaseBox0 restBox0
  · have hr : residue ⟨0,by norm_num⟩ = (0:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox0_mem
  · exact restBox0_mem
lemma restBox1_calc (j : Fin 31) : recoverRest phaseBox1 restBox1 j = restBox1 j := by
  revert j
  decide +kernel
lemma restBox1_mem (j : Fin 31) : (restBox1 j).Mem ((restPolynomial ⟨1,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨1,by norm_num⟩ phaseBox1
  · have hr : residue ⟨1,by norm_num⟩ = (1:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox1_mem
  · exact restBox1_calc
lemma cBox1_calc (j : Fin 31) : cCoeffBox restBox1 j = cBox1 j := by
  revert j
  decide +kernel
lemma cBox1_mem (j : Fin 31) : (cBox1 j).Mem (cCoefficient ⟨1,by norm_num⟩ j) := by
  rw [← cBox1_calc]
  exact cCoeffBox_mem ⟨1,by norm_num⟩ restBox1 restBox1_mem j
lemma dBox1_calc (j : Fin 31) : dCoeffBox phaseBox1 restBox1 j = dBox1 j := by
  revert j
  decide +kernel
lemma dBox1_mem (j : Fin 31) : (dBox1 j).Mem (dCoefficient ⟨1,by norm_num⟩ j) := by
  rw [← dBox1_calc]
  apply dCoeffBox_mem ⟨1,by norm_num⟩ phaseBox1 restBox1
  · have hr : residue ⟨1,by norm_num⟩ = (1:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox1_mem
  · exact restBox1_mem
lemma restBox3_calc (j : Fin 31) : recoverRest phaseBox3 restBox3 j = restBox3 j := by
  revert j
  decide +kernel
lemma restBox3_mem (j : Fin 31) : (restBox3 j).Mem ((restPolynomial ⟨2,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨2,by norm_num⟩ phaseBox3
  · have hr : residue ⟨2,by norm_num⟩ = (3:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox3_mem
  · exact restBox3_calc
lemma cBox3_calc (j : Fin 31) : cCoeffBox restBox3 j = cBox3 j := by
  revert j
  decide +kernel
lemma cBox3_mem (j : Fin 31) : (cBox3 j).Mem (cCoefficient ⟨2,by norm_num⟩ j) := by
  rw [← cBox3_calc]
  exact cCoeffBox_mem ⟨2,by norm_num⟩ restBox3 restBox3_mem j
lemma dBox3_calc (j : Fin 31) : dCoeffBox phaseBox3 restBox3 j = dBox3 j := by
  revert j
  decide +kernel
lemma dBox3_mem (j : Fin 31) : (dBox3 j).Mem (dCoefficient ⟨2,by norm_num⟩ j) := by
  rw [← dBox3_calc]
  apply dCoeffBox_mem ⟨2,by norm_num⟩ phaseBox3 restBox3
  · have hr : residue ⟨2,by norm_num⟩ = (3:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox3_mem
  · exact restBox3_mem
lemma restBox4_calc (j : Fin 31) : recoverRest phaseBox4 restBox4 j = restBox4 j := by
  revert j
  decide +kernel
lemma restBox4_mem (j : Fin 31) : (restBox4 j).Mem ((restPolynomial ⟨3,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨3,by norm_num⟩ phaseBox4
  · have hr : residue ⟨3,by norm_num⟩ = (4:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox4_mem
  · exact restBox4_calc
lemma cBox4_calc (j : Fin 31) : cCoeffBox restBox4 j = cBox4 j := by
  revert j
  decide +kernel
lemma cBox4_mem (j : Fin 31) : (cBox4 j).Mem (cCoefficient ⟨3,by norm_num⟩ j) := by
  rw [← cBox4_calc]
  exact cCoeffBox_mem ⟨3,by norm_num⟩ restBox4 restBox4_mem j
lemma dBox4_calc (j : Fin 31) : dCoeffBox phaseBox4 restBox4 j = dBox4 j := by
  revert j
  decide +kernel
lemma dBox4_mem (j : Fin 31) : (dBox4 j).Mem (dCoefficient ⟨3,by norm_num⟩ j) := by
  rw [← dBox4_calc]
  apply dCoeffBox_mem ⟨3,by norm_num⟩ phaseBox4 restBox4
  · have hr : residue ⟨3,by norm_num⟩ = (4:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox4_mem
  · exact restBox4_mem
lemma restBox7_calc (j : Fin 31) : recoverRest phaseBox7 restBox7 j = restBox7 j := by
  revert j
  decide +kernel
lemma restBox7_mem (j : Fin 31) : (restBox7 j).Mem ((restPolynomial ⟨4,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨4,by norm_num⟩ phaseBox7
  · have hr : residue ⟨4,by norm_num⟩ = (7:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox7_mem
  · exact restBox7_calc
lemma cBox7_calc (j : Fin 31) : cCoeffBox restBox7 j = cBox7 j := by
  revert j
  decide +kernel
lemma cBox7_mem (j : Fin 31) : (cBox7 j).Mem (cCoefficient ⟨4,by norm_num⟩ j) := by
  rw [← cBox7_calc]
  exact cCoeffBox_mem ⟨4,by norm_num⟩ restBox7 restBox7_mem j
lemma dBox7_calc (j : Fin 31) : dCoeffBox phaseBox7 restBox7 j = dBox7 j := by
  revert j
  decide +kernel
lemma dBox7_mem (j : Fin 31) : (dBox7 j).Mem (dCoefficient ⟨4,by norm_num⟩ j) := by
  rw [← dBox7_calc]
  apply dCoeffBox_mem ⟨4,by norm_num⟩ phaseBox7 restBox7
  · have hr : residue ⟨4,by norm_num⟩ = (7:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox7_mem
  · exact restBox7_mem
lemma restBox9_calc (j : Fin 31) : recoverRest phaseBox9 restBox9 j = restBox9 j := by
  revert j
  decide +kernel
lemma restBox9_mem (j : Fin 31) : (restBox9 j).Mem ((restPolynomial ⟨5,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨5,by norm_num⟩ phaseBox9
  · have hr : residue ⟨5,by norm_num⟩ = (9:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox9_mem
  · exact restBox9_calc
lemma cBox9_calc (j : Fin 31) : cCoeffBox restBox9 j = cBox9 j := by
  revert j
  decide +kernel
lemma cBox9_mem (j : Fin 31) : (cBox9 j).Mem (cCoefficient ⟨5,by norm_num⟩ j) := by
  rw [← cBox9_calc]
  exact cCoeffBox_mem ⟨5,by norm_num⟩ restBox9 restBox9_mem j
lemma dBox9_calc (j : Fin 31) : dCoeffBox phaseBox9 restBox9 j = dBox9 j := by
  revert j
  decide +kernel
lemma dBox9_mem (j : Fin 31) : (dBox9 j).Mem (dCoefficient ⟨5,by norm_num⟩ j) := by
  rw [← dBox9_calc]
  apply dCoeffBox_mem ⟨5,by norm_num⟩ phaseBox9 restBox9
  · have hr : residue ⟨5,by norm_num⟩ = (9:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox9_mem
  · exact restBox9_mem
lemma restBox12_calc (j : Fin 31) : recoverRest phaseBox12 restBox12 j = restBox12 j := by
  revert j
  decide +kernel
lemma restBox12_mem (j : Fin 31) : (restBox12 j).Mem ((restPolynomial ⟨6,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨6,by norm_num⟩ phaseBox12
  · have hr : residue ⟨6,by norm_num⟩ = (12:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox12_mem
  · exact restBox12_calc
lemma cBox12_calc (j : Fin 31) : cCoeffBox restBox12 j = cBox12 j := by
  revert j
  decide +kernel
lemma cBox12_mem (j : Fin 31) : (cBox12 j).Mem (cCoefficient ⟨6,by norm_num⟩ j) := by
  rw [← cBox12_calc]
  exact cCoeffBox_mem ⟨6,by norm_num⟩ restBox12 restBox12_mem j
lemma dBox12_calc (j : Fin 31) : dCoeffBox phaseBox12 restBox12 j = dBox12 j := by
  revert j
  decide +kernel
lemma dBox12_mem (j : Fin 31) : (dBox12 j).Mem (dCoefficient ⟨6,by norm_num⟩ j) := by
  rw [← dBox12_calc]
  apply dCoeffBox_mem ⟨6,by norm_num⟩ phaseBox12 restBox12
  · have hr : residue ⟨6,by norm_num⟩ = (12:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox12_mem
  · exact restBox12_mem
lemma restBox13_calc (j : Fin 31) : recoverRest phaseBox13 restBox13 j = restBox13 j := by
  revert j
  decide +kernel
lemma restBox13_mem (j : Fin 31) : (restBox13 j).Mem ((restPolynomial ⟨7,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨7,by norm_num⟩ phaseBox13
  · have hr : residue ⟨7,by norm_num⟩ = (13:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox13_mem
  · exact restBox13_calc
lemma cBox13_calc (j : Fin 31) : cCoeffBox restBox13 j = cBox13 j := by
  revert j
  decide +kernel
lemma cBox13_mem (j : Fin 31) : (cBox13 j).Mem (cCoefficient ⟨7,by norm_num⟩ j) := by
  rw [← cBox13_calc]
  exact cCoeffBox_mem ⟨7,by norm_num⟩ restBox13 restBox13_mem j
lemma dBox13_calc (j : Fin 31) : dCoeffBox phaseBox13 restBox13 j = dBox13 j := by
  revert j
  decide +kernel
lemma dBox13_mem (j : Fin 31) : (dBox13 j).Mem (dCoefficient ⟨7,by norm_num⟩ j) := by
  rw [← dBox13_calc]
  apply dCoeffBox_mem ⟨7,by norm_num⟩ phaseBox13 restBox13
  · have hr : residue ⟨7,by norm_num⟩ = (13:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox13_mem
  · exact restBox13_mem
lemma restBox16_calc (j : Fin 31) : recoverRest phaseBox16 restBox16 j = restBox16 j := by
  revert j
  decide +kernel
lemma restBox16_mem (j : Fin 31) : (restBox16 j).Mem ((restPolynomial ⟨8,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨8,by norm_num⟩ phaseBox16
  · have hr : residue ⟨8,by norm_num⟩ = (16:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox16_mem
  · exact restBox16_calc
lemma cBox16_calc (j : Fin 31) : cCoeffBox restBox16 j = cBox16 j := by
  revert j
  decide +kernel
lemma cBox16_mem (j : Fin 31) : (cBox16 j).Mem (cCoefficient ⟨8,by norm_num⟩ j) := by
  rw [← cBox16_calc]
  exact cCoeffBox_mem ⟨8,by norm_num⟩ restBox16 restBox16_mem j
lemma dBox16_calc (j : Fin 31) : dCoeffBox phaseBox16 restBox16 j = dBox16 j := by
  revert j
  decide +kernel
lemma dBox16_mem (j : Fin 31) : (dBox16 j).Mem (dCoefficient ⟨8,by norm_num⟩ j) := by
  rw [← dBox16_calc]
  apply dCoeffBox_mem ⟨8,by norm_num⟩ phaseBox16 restBox16
  · have hr : residue ⟨8,by norm_num⟩ = (16:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox16_mem
  · exact restBox16_mem
lemma restBox19_calc (j : Fin 31) : recoverRest phaseBox19 restBox19 j = restBox19 j := by
  revert j
  decide +kernel
lemma restBox19_mem (j : Fin 31) : (restBox19 j).Mem ((restPolynomial ⟨9,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨9,by norm_num⟩ phaseBox19
  · have hr : residue ⟨9,by norm_num⟩ = (19:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox19_mem
  · exact restBox19_calc
lemma cBox19_calc (j : Fin 31) : cCoeffBox restBox19 j = cBox19 j := by
  revert j
  decide +kernel
lemma cBox19_mem (j : Fin 31) : (cBox19 j).Mem (cCoefficient ⟨9,by norm_num⟩ j) := by
  rw [← cBox19_calc]
  exact cCoeffBox_mem ⟨9,by norm_num⟩ restBox19 restBox19_mem j
lemma dBox19_calc (j : Fin 31) : dCoeffBox phaseBox19 restBox19 j = dBox19 j := by
  revert j
  decide +kernel
lemma dBox19_mem (j : Fin 31) : (dBox19 j).Mem (dCoefficient ⟨9,by norm_num⟩ j) := by
  rw [← dBox19_calc]
  apply dCoeffBox_mem ⟨9,by norm_num⟩ phaseBox19 restBox19
  · have hr : residue ⟨9,by norm_num⟩ = (19:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox19_mem
  · exact restBox19_mem
lemma restBox21_calc (j : Fin 31) : recoverRest phaseBox21 restBox21 j = restBox21 j := by
  revert j
  decide +kernel
lemma restBox21_mem (j : Fin 31) : (restBox21 j).Mem ((restPolynomial ⟨10,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨10,by norm_num⟩ phaseBox21
  · have hr : residue ⟨10,by norm_num⟩ = (21:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox21_mem
  · exact restBox21_calc
lemma cBox21_calc (j : Fin 31) : cCoeffBox restBox21 j = cBox21 j := by
  revert j
  decide +kernel
lemma cBox21_mem (j : Fin 31) : (cBox21 j).Mem (cCoefficient ⟨10,by norm_num⟩ j) := by
  rw [← cBox21_calc]
  exact cCoeffBox_mem ⟨10,by norm_num⟩ restBox21 restBox21_mem j
lemma dBox21_calc (j : Fin 31) : dCoeffBox phaseBox21 restBox21 j = dBox21 j := by
  revert j
  decide +kernel
lemma dBox21_mem (j : Fin 31) : (dBox21 j).Mem (dCoefficient ⟨10,by norm_num⟩ j) := by
  rw [← dBox21_calc]
  apply dCoeffBox_mem ⟨10,by norm_num⟩ phaseBox21 restBox21
  · have hr : residue ⟨10,by norm_num⟩ = (21:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox21_mem
  · exact restBox21_mem
end AtomicTriangular.FiniteCertificate

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnTable_mem (col : Fin 23) (j : Fin 31) : (columnTable col j).Mem (finiteColumn col j) := by
  fin_cases col
  · exact cBox0_mem j
  · exact dBox0_mem j
  · exact cBox1_mem j
  · exact dBox1_mem j
  · exact cBox3_mem j
  · exact dBox3_mem j
  · exact cBox4_mem j
  · exact dBox4_mem j
  · exact cBox7_mem j
  · exact dBox7_mem j
  · exact cBox9_mem j
  · exact dBox9_mem j
  · exact cBox12_mem j
  · exact dBox12_mem j
  · exact cBox13_mem j
  · exact dBox13_mem j
  · exact cBox16_mem j
  · exact dBox16_mem j
  · exact cBox19_mem j
  · exact dBox19_mem j
  · exact cBox21_mem j
  · exact dBox21_mem j
  · exact atomPolynomial_coeff_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.Envelope
open Real

lemma mul_exp_neg_le {x y δ : ℝ} (hx : 0<x) (hxy : x≤y) (hδ : 1≤δ*x) :
    y*exp (-δ*y)≤x*exp (-δ*x) := by
  have hx0 : x≠0 := ne_of_gt hx
  have hr : y/x≤δ*(y-x)+1 := by
    apply (div_le_iff₀ hx).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hδ)]
  have he : y/x≤exp (δ*(y-x)) := hr.trans (add_one_le_exp _)
  calc
    y*exp (-δ*y) = (y/x)*(x*exp (-δ*y)) := by field_simp
    _ ≤ exp (δ*(y-x))*(x*exp (-δ*y)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = x*exp (-δ*x) := by
      rw [mul_left_comm,←exp_add]
      congr 2
      ring

lemma sqrt_prefactor_identity {x a p c d δ : ℝ} (hx : 0<x) :
    (a+p*sqrt (c+d*x))*sqrt x*exp (-δ*x) =
      (a/sqrt x+p*sqrt (c/x+d))*(x*exp (-δ*x)) := by
  have hs : sqrt x≠0 := ne_of_gt (sqrt_pos.mpr hx)
  have he : c/x+d=(c+d*x)/x := by field_simp
  rw [he,sqrt_div' _ hx.le]
  have hh := sq_sqrt hx.le
  field_simp
  rw [hh]
  ring

lemma sqrt_exp_antitone {x y a p c d δ : ℝ} (hx : 0<x) (hxy : x≤y)
    (ha : 0≤a) (hp : 0≤p) (hc : 0 ≤ c) (hδ : 1≤δ*x) :
    (a+p*sqrt (c+d*y))*sqrt y*exp (-δ*y) ≤
      (a+p*sqrt (c+d*x))*sqrt x*exp (-δ*x) := by
  have hy : 0<y := hx.trans_le hxy
  rw [sqrt_prefactor_identity hy,sqrt_prefactor_identity hx]
  have hfactor : a/sqrt y+p*sqrt (c/y+d) ≤ a/sqrt x+p*sqrt (c/x+d) := by
    apply add_le_add
    · exact div_le_div_of_nonneg_left ha (sqrt_pos.mpr hx) (sqrt_le_sqrt hxy)
    · apply mul_le_mul_of_nonneg_left _ hp
      apply sqrt_le_sqrt
      simpa only [add_comm] using add_le_add_right (div_le_div_of_nonneg_left hc hx hxy) d
  exact mul_le_mul hfactor (mul_exp_neg_le hx hxy hδ) (by positivity) (by positivity)
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma Xwave_pos {k : ℝ} (hk : 0<k) (t : ℝ) : 0<Xwave k t := by
  unfold Xwave
  exact div_pos (by norm_num) (waveDen_pos hk t)
lemma Xwave_square {k : ℝ} (hk : 0<k) (t : ℝ) :
    (k^2+t^2)*Xwave k t=4/3 := by
  unfold Xwave waveDen
  field_simp [ne_of_gt (waveDen_pos hk t)]
lemma normSq_lambda {k : ℝ} (hk : 0<k) (t : ℝ) : normSq (lambda k t)=Xwave k t := by
  unfold lambda
  rw [map_div₀]
  simp only [normSq_apply,add_re,ofReal_re,mul_re,I_re,zero_mul,I_im,ofReal_im,
    mul_zero,sub_zero,add_zero,add_im,mul_im,one_mul,zero_add]
  dsimp [Xwave,waveDen]
  have hb := b_sq
  have hd : k^2+t^2≠0 := ne_of_gt (waveDen_pos hk t)
  field_simp [ne_of_gt b_pos, hd]
  nlinarith [mul_nonneg (sq_nonneg k) (sq_nonneg t)]
lemma norm_lambda {k : ℝ} (hk : 0<k) (t : ℝ) : ‖lambda k t‖=Real.sqrt (Xwave k t) := by
  rw [Complex.norm_def,normSq_lambda hk]
lemma normSq_zeta {k : ℝ} (hk : 0<k) (v t : ℝ) :
    normSq (zeta k v t)=v^2+(4/3-2*k*v)*Xwave k t := by
  unfold zeta
  simp only [normSq_apply,add_re,neg_re,mul_re,ofReal_re,ofReal_im,mul_zero,
    sub_zero,I_re,zero_mul,I_im,one_mul,add_zero,add_im,neg_im,mul_im,zero_add]
  linear_combination Xwave k t * Xwave_square hk t
lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]
lemma norm_wavePhase {k : ℝ} (hk : 0<k) (v t : ℝ) :
    ‖I*Real.pi*zeta k v t‖=Real.pi*Real.sqrt (v^2+(4/3-2*k*v)*Xwave k t) := by
  rw [norm_mul,norm_mul,norm_I,one_mul,norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_def,normSq_zeta hk]

lemma Xwave_antitone {k s t : ℝ} (hk : 0<k) (hs : 0 ≤ s) (hst : s ≤ t) :
    Xwave k t≤Xwave k s := by
  unfold Xwave
  apply div_le_div_of_nonneg_left (by norm_num) (waveDen_pos hk s)
  unfold waveDen
  nlinarith
lemma damping_Xwave_lower (q : Fin 2) {t : ℝ} (ht0 : 0≤t) (ht : t≤5/6) :
    1≤Real.pi*damping q*Xwave (damping q) t := by
  have hx := Xwave_antitone (damping_pos q) ht0 ht
  have hl : 1<3*damping q*Xwave (damping q) (5/6) := by
    fin_cases q <;> (first | (simp [damping,h,H,Xwave,waveDen]; all_goals first | (norm_num [damping,h,H,Xwave,waveDen]; done) | rfl | decide) | (norm_num [damping,h,H,Xwave,waveDen]; done) | norm_num [damping,h,H,Xwave,waveDen])
  have hp := Real.pi_gt_three
  have hq := damping_pos q
  have hxpos := Xwave_pos hq t
  calc
    1 ≤ 3*damping q*Xwave (damping q) (5/6) := hl.le
    _ ≤ 3*damping q*Xwave (damping q) t := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ Real.pi*damping q*Xwave (damping q) t := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp.le hq.le) hxpos.le

lemma jetEnvelope_monotone {q v : Fin 2} {n : ℤ} (hn : 1≤n) (hQ : 0<Q n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t≤5/6) :
    jetEnvelope (damping q) (damping v) n s ≤jetEnvelope (damping q) (damping v) n t := by
  have ht0 : 0≤t := hs.trans hst
  have hx := Xwave_pos (damping_pos q) t
  have hxy := Xwave_antitone (damping_pos q) hs hst
  have hb := damping_Xwave_lower q ht0 ht
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hδ : 1≤(Real.pi*damping q*n)*Xwave (damping q) t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (le_of_lt hx),damping_pos q,Real.pi_pos]
  have hh := Envelope.sqrt_exp_antitone (a:=1+|D n|) (p:=Real.pi)
    (c:=(damping v)^2) (d:=4/3-2*damping q*damping v) hx hxy
    (by positivity) Real.pi_pos.le (sq_nonneg _) hδ
  have he (x : ℝ) : Real.exp (-Real.pi*(damping q*x-damping v)*n) =
      Real.exp (Real.pi*damping v*n)*Real.exp (-(Real.pi*damping q*n)*x) := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold jetEnvelope
  rw [he,he]
  convert! mul_le_mul_of_nonneg_left hh (show 0 ≤ Real.exp (Real.pi*damping v*n)/Q n from
    div_nonneg (Real.exp_pos _).le hQ.le) using 1 <;> first | (with_reducible_and_instances rfl) | ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma normJetEnvelope_eq {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) (t : ℝ) :
    normJetEnvelope k v n t = jetEnvelope k v n t := by
  rw [normJetEnvelope,norm_wavePhase hk,norm_lambda hk]
  simp only [jetEnvelope,frequencyDecay,div_eq_mul_inv,neg_mul]
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ri0_mem : (RI.point 0).Mem (0:ℝ) := by simpa using RI.mem_point 0
lemma ri1_mem : (RI.point 1).Mem (1:ℝ) := by simpa using RI.mem_point 1
lemma fullTailWBox_mem (pn : Fin 31 → RI) (hp : ∀ l, (pn l).Mem ‖fourierCoeff l‖)
    (i : Fin 15) (d : Fin 2) : (fullTailWBox pn i d).Mem (fullTailW i d) := by
  unfold fullTailWBox fullTailW
  split_ifs with hd
  · apply RI.mem_mul (by norm_num at *; simpa using RI.mem_divNat (RI.mem_pow piBox_mem 2) (by norm_num : 0<(18^2:ℕ)))
    apply RI.mem_sum
    intro l
    split_ifs
    · apply RI.mem_mul _ (hp l)
      apply RI.mem_sub
      · simpa using RI.mem_point ((frequencyDistance l:ℤ)-i.val)
      · simpa using RI.mem_divNat ri1_mem (by norm_num : 0<(2:ℕ))
    · exact ri0_mem
  · apply RI.mem_mul (by simpa using RI.mem_divNat piBox_mem (by norm_num : 0<(18:ℕ)))
    apply RI.mem_sum
    intro l
    split_ifs
    · exact hp l
    · exact ri0_mem

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_JetEnvelopeAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction
lemma norm_transformedWave (k v t : ℝ) (n : ℤ) :
    ‖transformedWave k v t n‖ = ‖lambda k t‖ * Real.exp (-frequencyDecay k v t*n) := by
  rw [transformedWave,norm_mul,Complex.norm_exp]
  congr 2
  rw [show I*Real.pi*zeta k v t*(n:ℂ) = (I*Real.pi*zeta k v t)*(n:ℂ) by rfl,
    Complex.mul_re,Complex.intCast_re,Complex.intCast_im,mul_zero,sub_zero,wavePhase_re]
  unfold frequencyDecay
  ring
lemma jetMultiplier_pair_bound (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    (∑ d : Fin 2, ‖jetMultiplier k v n d t‖) ≤ normJetEnvelope k v n t := by
  have hqi : ‖(Q n:ℂ)⁻¹‖=(Q n)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ]
  have hb : ‖(D n:ℂ)-I*Real.pi*zeta k v t‖ ≤ |D n|+‖I*Real.pi*zeta k v t‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using norm_sub_le (D n:ℂ) (I*Real.pi*zeta k v t)
  simp only [Fin.sum_univ_two,jetMultiplier,Fin.val_zero,Fin.val_one,one_ne_zero,
    ↓reduceIte,norm_mul,norm_neg,norm_one,mul_one,hqi,norm_transformedWave]
  calc
    _ ≤ (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n)) +
        (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n))*(|D n|+‖I*Real.pi*zeta k v t‖) := by
      gcongr
    _ = _ := by unfold normJetEnvelope; ring
lemma normJetEnvelope_even (k v t : ℝ) (n : ℤ) (hk : 0<k) :
    normJetEnvelope k v n (-t)=normJetEnvelope k v n t := by
  rw [normJetEnvelope_eq hk,normJetEnvelope_eq hk]
  simp [jetEnvelope,Xwave,waveDen]
lemma normJetEnvelope_abs (k v t : ℝ) (n : ℤ) (hk : 0<k) :
    normJetEnvelope k v n |t|=normJetEnvelope k v n t := by
  rcases le_total 0 t with ht|ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht,normJetEnvelope_even k v t n hk]
lemma normJetEnvelope_monotone {q v : Fin 2} {n : ℤ} (hn : 1≤n) (hQ : 0<Q n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 5 / 6) :
    normJetEnvelope (damping q) (damping v) n s≤normJetEnvelope (damping q) (damping v) n t := by
  rw [normJetEnvelope_eq (damping_pos q),normJetEnvelope_eq (damping_pos q)]
  exact jetEnvelope_monotone hn hQ hs hst ht
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_SpectralEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma frequencyDistance_le (l : Fin 31) : frequencyDistance l≤15 := by revert l; decide +kernel
lemma frequencyDistance_eq (l : Fin 31) : |frequency l| = (frequencyDistance l:ℝ)*(1/18) := by
  fin_cases l <;> (first | (simp [frequency,frequencyDistance]; all_goals first | (norm_num [frequency,frequencyDistance]; done) | rfl | decide) | (norm_num [frequency,frequencyDistance]; done) | norm_num [frequency,frequencyDistance])
lemma range_sum_15 (N : ℕ) (hN : N≤15) (F : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, F i) = ∑ i : Fin 15, if i.val<N then F i.val else 0 := by
  rw [show (∑ i : Fin 15, if i.val<N then F i.val else 0) = ∑ i ∈ Finset.range 15, if i<N then F i else 0 by
    exact Fin.sum_univ_eq_sum_range (fun i => if i<N then F i else 0) 15,←Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_range,Finset.mem_filter]
  omega
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma spectralCVector_bound (n : ℤ) (f : ℝ → E) (hf : Continuous f) (M : Fin 15 → ℝ)
    (hM : ∀ i : Fin 15, ∀ x, (i.val:ℝ)/18≤|x| → |x|≤(i.val+1:ℕ)/18 → ‖f x‖≤M i) :
    ‖spectralCVector n f‖ ≤ ∑ i : Fin 15, M i * fullTailW i 0 := by
  let M' : ℕ → ℝ := fun i => if hi : i<15 then M ⟨i,hi⟩ else 0
  have hb (l : Fin 31) :
      ‖∫ t in (0:ℝ)..frequency l, (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t)‖ ≤
      (1/18:ℝ)^2 * ∑ i : Fin 15, if i.val<frequencyDistance l then
        ((frequencyDistance l:ℝ)-i.val-1/2)*M i else 0 := by
    have hh := IntegralVectors.weighted_integral_grid_abs (by norm_num : (0:ℝ)≤1/18)
      (frequencyDistance l) (frequencyDistance_eq l)
      (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t) (by fun_prop) M'
      (fun i hi x h1 h2 => by
        have hi15 : i<15 := lt_of_lt_of_le hi (frequencyDistance_le l)
        rw [norm_smul,norm_exp_neg_phase,one_mul]
        simpa [M',hi15] using hM ⟨i,hi15⟩ x (by convert h1 using 1; ring) (by convert h2 using 1; ring))
    rw [range_sum_15 _ (frequencyDistance_le l)] at hh
    simpa [M',Fin.is_lt] using hh
  unfold spectralCVector
  calc
    _ ≤ ∑ l : Fin 31, ‖(fourierCoeff l*exp (I*Real.pi*frequency l*n)) •
        (-(Real.pi:ℂ)^2 • ∫ t in (0:ℝ)..frequency l,
          (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 31, ‖fourierCoeff l‖ * Real.pi^2*((1/18:ℝ)^2 *
        ∑ i : Fin 15, if i.val<frequencyDistance l then ((frequencyDistance l:ℝ)-i.val-1/2)*M i else 0) := by
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_smul,norm_mul,norm_exp_phase,mul_one,norm_neg,norm_pow,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb l) (show 0≤‖fourierCoeff l‖*Real.pi^2 by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fullTailW,Fin.val_zero,↓reduceIte,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
omit [CompleteSpace E] in
lemma spectralDVector_bound (n : ℤ) (f : ℝ → E) (hf : Continuous f) (M : Fin 15 → ℝ)
    (hM : ∀ i : Fin 15, ∀ x, (i.val:ℝ)/18≤|x| → |x|≤(i.val+1:ℕ)/18 → ‖f x‖≤M i) :
    ‖spectralDVector n f‖ ≤ ∑ i : Fin 15, M i * fullTailW i 1 := by
  let M' : ℕ → ℝ := fun i => if hi : i<15 then M ⟨i,hi⟩ else 0
  have hb (l : Fin 31) :
      ‖∫ t in (0:ℝ)..frequency l, exp (-I*Real.pi*(t:ℂ)*n) • f t‖ ≤
      (1/18:ℝ) * ∑ i : Fin 15, if i.val<frequencyDistance l then M i else 0 := by
    have hh := IntegralVectors.norm_integral_grid_abs (by norm_num : (0:ℝ)≤1/18)
      (frequencyDistance l) (frequencyDistance_eq l)
      (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t) (by fun_prop) M'
      (fun i hi x h1 h2 => by
        have hi15 : i<15 := lt_of_lt_of_le hi (frequencyDistance_le l)
        rw [norm_smul,norm_exp_neg_phase,one_mul]
        simpa [M',hi15] using hM ⟨i,hi15⟩ x (by convert h1 using 1; ring) (by convert h2 using 1; ring))
    rw [range_sum_15 _ (frequencyDistance_le l)] at hh
    simpa [M',Fin.is_lt] using hh
  unfold spectralDVector
  calc
    _ ≤ ∑ l : Fin 31, ‖(fourierCoeff l*exp (I*Real.pi*frequency l*n)) •
        ((I*Real.pi) • ∫ t in (0:ℝ)..frequency l, exp (-I*Real.pi*(t:ℂ)*n) • f t)‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 31, ‖fourierCoeff l‖ * Real.pi*((1/18:ℝ) *
        ∑ i : Fin 15, if i.val<frequencyDistance l then M i else 0) := by
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_smul,norm_mul,norm_exp_phase,mul_one,norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb l) (show 0≤‖fourierCoeff l‖*Real.pi by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fullTailW,Fin.val_one,one_ne_zero,↓reduceIte,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_TailJetVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma continuous_jetVector {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) :
    Continuous (jetVector k v n) := by
  exact (PiLp.continuousLinearEquiv 1 ℂ (fun _ : Fin 2 => ℂ)).symm.continuous.comp
    (continuous_pi (fun d => continuous_jetMultiplier hk v n d))
lemma jetVector_norm_bound (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    ‖jetVector k v n t‖  ≤  normJetEnvelope k v n t := by
  rw [PiLp.norm_eq_of_L1]
  exact jetMultiplier_pair_bound k v t n hQ

lemma finiteEndpoint (i : Fin 15) :
    frequency ⟨i.val+16,by omega⟩ = (i.val+1:ℕ)/18 := by
  unfold frequency
  push_cast
  ring
lemma tailJetVector_bound (q v : Fin 2) (m n : ℤ) (hm : 1 ≤ m) (hQ : 0<Q m) (c : Fin 2) :
    ‖tailJetVector (damping q) (damping v) m n c‖  ≤ 
      ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) * fullTailW i c := by
  have hh (i : Fin 15) (x : ℝ) (h1 : (i.val:ℝ)/18 ≤ |x|) (h2 : |x| ≤ (i.val+1:ℕ)/18) :
      ‖jetVector (damping q) (damping v) m x‖  ≤ 
      normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) := by
    apply (jetVector_norm_bound _ _ _ _ hQ).trans
    rw [←normJetEnvelope_abs _ _ x m (damping_pos q),finiteEndpoint]
    apply normJetEnvelope_monotone hm hQ (abs_nonneg x) h2
    have hi : ((i.val+1:ℕ):ℝ) ≤ 15 := by exact_mod_cast (show i.val+1 ≤ 15 by omega)
    linarith
  fin_cases c
  · exact spectralCVector_bound n _ (continuous_jetVector (damping_pos q) _ _) _ hh
  · exact spectralDVector_bound n _ (continuous_jetVector (damping_pos q) _ _) _ hh
lemma tailJet_pair_bound (q v : Fin 2) (m n : ℤ) (hm : 1 ≤ m) (hQ : 0<Q m) (c : Fin 2) :
    (∑ d : Fin 2, |tailJet (damping q) (damping v) m n c d|)  ≤ 
      ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) * fullTailW i c := by
  apply le_trans _ (tailJetVector_bound q v m n hm hQ c)
  rw [PiLp.norm_eq_of_L1]
  exact Finset.sum_le_sum (fun d _ => Complex.abs_re_le_norm _)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorm2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm22_check (j : Fin 31) : 0≤(columnNorm22 j).lo ∧ (columnNorm22 j).lo*(columnNorm22 j).lo ≤ scale*max 0 (columnTable 22 j).normSq.lo ∧ scale*(columnTable 22 j).normSq.hi ≤ (columnNorm22 j).hi*(columnNorm22 j).hi ∧ 0≤(columnNorm22 j).hi := by
  revert j
  decide +kernel
lemma columnNorm22_mem (j : Fin 31) : (columnNorm22 j).Mem ‖finiteColumn 22 j‖ := by
  have hh := columnNorm22_check j
  exact CI.mem_norm (columnTable_mem 22 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fourierNorm_mem (j : Fin 31) : (columnNorm22 j).Mem ‖fourierCoeff j‖ := columnNorm22_mem j
lemma fullWTable_calc (i : Fin 15) (d : Fin 2) : fullTailWBox columnNorm22 i d=fullWTable i d := by
  revert i d
  decide +kernel
lemma fullWTable_mem (i : Fin 15) (d : Fin 2) : (fullWTable i d).Mem (fullTailW i d) := by
  rw [← fullWTable_calc]
  exact fullTailWBox_mem columnNorm22 fourierNorm_mem i d
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSumsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ri_mem_lt {a : RI} {x : ℝ} (hx : a.Mem x) (p : ℤ) (q : ℕ) (hq : 0<q)
    (h : a.hi*q < p*scale) : x < p/q := by
  have hh : (a.hi:ℝ)*(q:ℝ) < p*(scale:ℝ) := by exact_mod_cast h
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply (lt_div_iff₀ hqR).mpr
  have hx' := mul_le_mul_of_nonneg_right hx.2 hqR.le
  exact (mul_lt_mul_iff_right₀ scale_pos).mp (by nlinarith)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma boundB_calc (c : Fin 2) : RI.sum (fun i : Fin 15 => (envelopeSumBoxB ⟨i.val+16,by omega⟩).mul (fullWTable i c))=boundB c := by
  revert c
  decide +kernel
lemma boundB_mem (c : Fin 2) : (boundB c).Mem (finiteTailEnvelope c) := by
  rw [← boundB_calc]
  exact RI.mem_sum (fun i => RI.mem_mul (envelopeSumBoxB_mem_x _) (fullWTable_mem i c))
lemma finiteTailEnvelope_bound (c : Fin 2) : finiteTailEnvelope c < (335/1:ℝ) := by
  have hh := ri_mem_lt (boundB_mem c) 335 1 (by norm_num) (by revert c; decide +kernel)
  simpa only [Int.cast_ofNat, Nat.cast_one] using hh
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma finiteNode_node (i : Fin 10) : 0<finiteNode i ∧ (finiteNode i)%36 ∈ residues := by
  revert i; decide +kernel
lemma finiteNode_Qpos (i : Fin 10) : 0<Q (finiteNode i) := by
  have hh := FiniteCertificate.Q_node_bounds _ (finiteNode_node i).2
  linarith [hh.1]
lemma finite_tail_column_bound (n : ℤ) (c : Fin 2) :
    (∑ m : Fin 10, ∑ d : Fin 2, |tailJet h H (finiteNode m) n c d|) < 335 := by
  apply lt_of_le_of_lt _ (by simpa using FiniteCertificate.finiteTailEnvelope_bound c)
  calc
    _  ≤  ∑ m : Fin 10, ∑ i : Fin 15,
        normJetEnvelope h H (finiteNode m) (frequency ⟨i.val+16,by omega⟩)*fullTailW i c := by
      apply Finset.sum_le_sum
      intro m _
      exact tailJet_pair_bound 0 1 _ n (by have h := (finiteNode_node m).1; omega) (finiteNode_Qpos m) c
    _ = finiteTailEnvelope c := by
      rw [Finset.sum_comm]
      simp only [finiteTailEnvelope,finiteEnvelopeSum,damping,↓reduceIte,Fin.val_zero,Fin.val_one,one_ne_zero,Finset.sum_mul]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
lemma sum_fin20_pairs (g : Fin 10 → Fin 2 → ℝ) :
    (∑ i : Fin 20, g ⟨i.val/2,by omega⟩ ⟨i.val%2,by omega⟩) =
      ∑ n : Fin 10, ∑ d : Fin 2, g n d := by
  simpa only [finProdFinEquiv_symm_apply,Fintype.sum_prod_type,Fin.divNat,Fin.modNat] using
    ((finProdFinEquiv (m:=10) (n:=2)).symm.sum_comp (fun p => g p.1 p.2))
lemma Bkernel_bound_x_oai (p : TailNode × Fin 2) : (∑' i, |Bkernel i p|) ≤ 335 := by
  rw [tsum_fintype]
  change (∑ i : Fin 20, |tailJet h H (finiteNode ⟨i.val/2,by omega⟩) p.1.val.val p.2 ⟨i.val%2,by omega⟩|) ≤ 335
  exact (sum_fin20_pairs (fun n d => |tailJet h H (finiteNode n) p.1.val.val p.2 d|)).trans_le (finite_tail_column_bound _ _).le
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.Bkernel_bound_x_oai := @OAI.AtomicTriangular.Construction.Bkernel_bound_x_oai
