-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.actual_interpolation_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:57:58.799324+00:00
-- url     : https://prove2.me/submissions/4a483f83-5df4-407f-9cf0-06a9fedec3b9

import Mathlib
import Definitions.Def_OAIQ334E009
import Theorems.Thm_OAI_AtomicTriangular_Construction_Bkernel_bound_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_Dkernel_bound_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_Dkernel_summable_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualFiniteError_equations_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualTail_full_equations_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_finiteSolution_equations_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_tail_atom_column_bounds_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_tail_finite_column_bound_eu

section
-- module Solutions.OAIQ334_EU.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction

theorem P_factor (a : Fin 15) (s : ℂ) :
    P s = (sineFactor a s)^2 * ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2 := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm

open Polynomial

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma hasDerivAt_P (s : ℂ) : HasDerivAt P (waveDerivative 1 s) s := by
  simpa only [waveDerivative_zero] using hasDerivAt_waveDerivative 0 s

lemma fourier_node_cancel (n : Node) : waveDerivative 0 n.val = 0 := by
  rw [waveDerivative_zero, P_node]

lemma fourier_node_deriv_cancel (n : Node) : waveDerivative 1 n.val = 0 := by
  rw [← (hasDerivAt_P n.val).deriv, deriv_P_node]

end AtomicTriangular.Construction

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
-- module Solutions.OAIQ334_EU.Triangular_Certificate_JetMatrix
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
-- module Solutions.OAIQ334_EU.Triangular_Construction_FiniteJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction
open Complex

lemma sineFactor_deriv (a : Fin 15) : deriv (sineFactor a) =
    fun s => 2*(kappa:ℂ)*cos ((kappa:ℂ)*(s-(residue a:ℂ))) := by
  funext s
  have hh := ((((hasDerivAt_id s).sub_const (residue a:ℂ)).const_mul
    (kappa:ℂ)).csin.const_mul 2).deriv
  change deriv (fun y => 2*sin ((kappa:ℂ)*(y-(residue a:ℂ)))) s = _
  simpa only [id_eq,mul_one,mul_assoc,mul_comm,mul_left_comm] using hh
lemma sineFactor_second (a : Fin 15) : iteratedDeriv 2 (sineFactor a) =
    fun s => -(kappa:ℂ)^2*sineFactor a s := by
  rw [show 2 = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,sineFactor_deriv]
  funext s
  have hh := ((((hasDerivAt_id s).sub_const (residue a:ℂ)).const_mul
    (kappa:ℂ)).ccos.const_mul (2*(kappa:ℂ))).deriv
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [sineFactor,id_eq,mul_one])
  ring

lemma square_zero_jets (f : ℂ → ℂ) (hf : Differentiable ℂ f) (n : ℂ)
    (h0 : f n=0) (h2 : iteratedDeriv 2 f n=0) :
    iteratedDeriv 0 (fun s => f s*f s) n=0 ∧
    iteratedDeriv 1 (fun s => f s*f s) n=0 ∧
    iteratedDeriv 2 (fun s => f s*f s) n=2*(deriv f n)^2 ∧
    iteratedDeriv 3 (fun s => f s*f s) n=0 := by
  constructor
  · simp [iteratedDeriv_zero,h0]
  constructor
  · rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hf.contDiff.contDiffAt]
    simp [Finset.sum_range_succ,iteratedDeriv_zero,h0]
  constructor
  · rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hf.contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one,h0,h2]
    ring
  · rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hf.contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one,h0,h2]

lemma square_zero_product_jets (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (n : ℂ) (h0 : f n=0) (h2 : iteratedDeriv 2 f n=0) :
    iteratedDeriv 2 (fun s => f s^2*g s) n=2*(deriv f n)^2*g n ∧
    iteratedDeriv 3 (fun s => f s^2*g s) n=6*(deriv f n)^2*deriv g n := by
  obtain ⟨hj0,hj1,hj2,hj3⟩ := square_zero_jets f hf n h0 h2
  have hh : (fun s => f s^2) = (fun s => f s*f s) := by funext s; ring
  have hd : Differentiable ℂ (fun s => f s^2) := hf.pow 2
  constructor
  · rw [iteratedDeriv_fun_mul hd.contDiff.contDiffAt hg.contDiff.contDiffAt,hh]
    norm_num [Finset.sum_range_succ,hj0,hj1,hj2,iteratedDeriv_zero]
  · rw [iteratedDeriv_fun_mul hd.contDiff.contDiffAt hg.contDiff.contDiffAt,hh]
    norm_num [Finset.sum_range_succ,hj0,hj1,hj2,hj3,iteratedDeriv_one]
    ring_nf
    simp

lemma sineFactor_at_residue (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    sineFactor a n=0 := by
  have he : (kappa:ℂ)*((n:ℂ)-(residue a:ℂ))=(n/36:ℤ)*(Real.pi:ℂ) := by
    have hh := congrArg (fun z : ℤ => (z:ℂ)) (Int.emod_add_mul_ediv n 36)
    rw [hn] at hh
    push_cast at hh
    unfold kappa
    push_cast
    linear_combination -(Real.pi:ℂ)/36*hh
  unfold sineFactor
  rw [he]
  have hz := congrArg Complex.ofReal (Real.sin_int_mul_pi (n/36))
  have hh : Complex.sin ((n/36:ℤ)*(Real.pi:ℂ))=0 := by
    simpa only [Complex.ofReal_zero,Complex.ofReal_sin,Complex.ofReal_mul,Complex.ofReal_intCast] using hz
  simp [hh]

lemma finiteC_matching_jets (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    (finiteC a n).re=Q n ∧ 6*(deriv (finiteC a) n).re=(waveDerivative 3 n).re := by
  let g : ℂ → ℂ := fun s => ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2
  have hf : Differentiable ℂ (sineFactor a) := by unfold sineFactor; fun_prop
  have hg : Differentiable ℂ g := by unfold g sineFactor; fun_prop
  have h0 := sineFactor_at_residue a n hn
  have h2 : iteratedDeriv 2 (sineFactor a) n=0 := by simp only [sineFactor_second,h0,mul_zero]
  have hc : cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2=1 := by
    have hsin : sin ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))=0 := by
      simpa [sineFactor] using h0
    simpa [hsin] using (sin_sq_add_cos_sq ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ))))
  have hd : (deriv (sineFactor a) n)^2=4*(kappa:ℂ)^2 := by
    rw [sineFactor_deriv]
    calc
      _ = 4*(kappa:ℂ)^2*cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2 := by ring
      _ = _ := by rw [hc,mul_one]
  obtain ⟨hp2,hp3⟩ := square_zero_product_jets (sineFactor a) g hf hg n h0 h2
  have hp : (fun s => sineFactor a s^2*g s)=P := (funext (P_factor a)).symm
  rw [hp,←waveDerivative_eq_iterated,hd] at hp2 hp3
  have hfc : deriv (finiteC a) n=4*(kappa:ℂ)^2*deriv g n :=
    ((hg n).hasDerivAt.const_mul (4*(kappa:ℂ)^2)).deriv
  constructor
  · have hr := congrArg Complex.re hp2
    change (4*(kappa:ℂ)^2*g n).re= Q n
    unfold Q
    rw [hp2]
    norm_num [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im]
    ring
  · rw [hfc,hp3]
    norm_num [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im]
    ring

lemma kappa_ne_zero : (kappa:ℂ)≠0 := by
  unfold kappa
  exact_mod_cast div_ne_zero Real.pi_ne_zero (by norm_num : (36:ℝ)≠0)
lemma residue_bounds (a : Fin 15) : 0 ≤ residue a ∧ residue a<36 := by
  fin_cases a <;> (first | (simp [residue]; all_goals first | (norm_num [residue]; done) | rfl | decide) | (norm_num [residue]; done) | norm_num [residue])
lemma sineFactor_ne_zero {a : Fin 15} {n : ℤ} (hn : n%36≠residue a) :
    sineFactor a n≠0 := by
  intro hz
  have hsin : sin ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))=0 := by simpa [sineFactor] using hz
  obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  have hprod : ((n:ℂ)-(residue a:ℂ)-36*(k:ℂ))*(Real.pi:ℂ)=0 := by
    unfold kappa at hk
    push_cast at hk
    linear_combination 36*hk
  have hzero := (mul_eq_zero.mp hprod).resolve_right (by exact_mod_cast Real.pi_ne_zero)
  have hnint : n-residue a-36*k=0 := by exact_mod_cast hzero
  obtain ⟨hr0,hr36⟩ := residue_bounds a
  have hh := Int.emod_add_mul_ediv n 36
  omega

lemma finiteC_P (a : Fin 15) :
    (fun s => (sineFactor a s)^2*finiteC a s) = fun s => 4*(kappa:ℂ)^2*P s := by
  funext s
  rw [P_factor a]
  unfold finiteC
  ring
lemma finiteC_other_jets (a : Fin 15) (n : Node) (hn : n.val%36≠residue a) :
    finiteC a n.val=0 ∧ deriv (finiteC a) n.val=0 := by
  have hne : (sineFactor a n.val)^2≠0 := pow_ne_zero 2 (sineFactor_ne_zero hn)
  have hh := congrFun (finiteC_P a) (n.val:ℂ)
  have hc : finiteC a n.val=0 := by
    apply (mul_eq_zero.mp (show (sineFactor a n.val)^2*finiteC a n.val=0 by
      simpa [P_node] using hh)).resolve_left hne
  refine ⟨hc,?_⟩
  have hf : Differentiable ℂ (sineFactor a) := by unfold sineFactor; fun_prop
  have hd := (((hf (n.val:ℂ)).hasDerivAt.pow 2).mul
    ((differentiable_finiteC a (n.val:ℂ)).hasDerivAt)).deriv
  change deriv (fun s => (sineFactor a s)^2*finiteC a s) n.val = _ at hd
  rw [finiteC_P] at hd
  have hr := ((differentiable_P (n.val:ℂ)).hasDerivAt.const_mul (4*(kappa:ℂ)^2)).deriv
  rw [deriv_P_node,mul_zero] at hr
  rw [hr,hc,mul_zero,zero_add] at hd
  apply (mul_eq_zero.mp (show (sineFactor a n.val)^2*deriv (finiteC a) n.val=0 by simpa using hd.symm)).resolve_left hne

lemma finiteD_eq_ratio (a : Fin 15) : finiteD a =fun s => finiteRatio a s*finiteC a s := by
  funext s
  unfold finiteD finiteRatio finiteC sineFactor
  field_simp [kappa_ne_zero]
  ring
lemma differentiable_finiteRatio (a : Fin 15) : Differentiable ℂ (finiteRatio a) := by
  unfold finiteRatio
  fun_prop
lemma finiteRatio_matching (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    finiteRatio a n=0 ∧ deriv (finiteRatio a) n=1 := by
  have hz := sineFactor_at_residue a n hn
  have hsin : sin ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))=0 := by simpa [sineFactor] using hz
  have hc : cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2=1 := by
    simpa [hsin] using sin_sq_add_cos_sq ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))
  constructor
  · simp [finiteRatio,hsin]
  · have hθ := ((hasDerivAt_id (n:ℂ)).sub_const (residue a:ℂ)).const_mul (kappa:ℂ)
    have hh := ((hθ.csin.mul hθ.ccos).div_const (kappa:ℂ)).deriv
    change deriv (finiteRatio a) n = _ at hh
    rw [hh]
    simp only [id_eq,mul_one,hsin,zero_mul,add_zero]
    calc
      _ = ((kappa:ℂ)*cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2)/(kappa:ℂ) := by ring
      _ = _ := by rw [mul_div_cancel_left₀ _ kappa_ne_zero,hc]
lemma finiteD_matching_jets (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    finiteD a n=0 ∧ deriv (finiteD a) n=finiteC a n := by
  obtain ⟨h0,h1⟩ := finiteRatio_matching a n hn
  constructor
  · rw [finiteD_eq_ratio]
    simp only [h0,zero_mul]
  · have hh := (((differentiable_finiteRatio a (n:ℂ)).hasDerivAt).mul
      ((differentiable_finiteC a (n:ℂ)).hasDerivAt)).deriv
    change deriv (fun s => finiteRatio a s*finiteC a s) _ = _ at hh
    rw [←finiteD_eq_ratio,h0,h1,zero_mul,one_mul,add_zero] at hh
    exact hh
lemma finiteD_other_jets (a : Fin 15) (n : Node) (hn : n.val%36≠residue a) :
    finiteD a n.val=0 ∧ deriv (finiteD a) n.val=0 := by
  obtain ⟨h0,h1⟩ := finiteC_other_jets a n hn
  constructor
  · rw [finiteD_eq_ratio]
    simp only [h0,mul_zero]
  · have hh := (((differentiable_finiteRatio a (n.val:ℂ)).hasDerivAt).mul
      ((differentiable_finiteC a (n.val:ℂ)).hasDerivAt)).deriv
    change deriv (fun s => finiteRatio a s*finiteC a s) _ = _ at hh
    rw [←finiteD_eq_ratio,h0,h1,mul_zero,mul_zero,add_zero] at hh
    exact hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_NodeJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction

lemma factor_second_third (g : ℂ → ℂ) (hg : Differentiable ℂ g) (n : ℂ) :
    iteratedDeriv 2 (fun s => (s-n)^2*g s) n = 2*g n ∧
    iteratedDeriv 3 (fun s => (s-n)^2*g s) n = 6*deriv g n := by
  have hp (k : ℕ) : iteratedDeriv k (fun s : ℂ => (s-n)^2) n =
      (2:ℕ).descFactorial k * (n-n)^(2-k) := by
    have hh := congrFun (iteratedDeriv_comp_sub_const k (fun s : ℂ => s^2) n) n
    exact hh.trans (iteratedDeriv_pow 2 k)
  have hpoly : ContDiff ℂ 3 (fun s : ℂ => (s-n)^2) := by fun_prop
  constructor
  · rw [iteratedDeriv_fun_mul (hpoly.of_le (by norm_num)).contDiffAt hg.contDiff.contDiffAt]
    simp [Finset.sum_range_succ,hp,iteratedDeriv_zero]
  · rw [iteratedDeriv_fun_mul hpoly.contDiffAt hg.contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ,hp,iteratedDeriv_one]

lemma P_cBasis (n : Node) : P = fun s => (s-(n.val:ℂ))^2*cBasis n s := by
  funext s
  by_cases hs : s = (n.val:ℂ)
  · simp [hs,P_node]
  · rw [cBasis_eq n hs]
    field_simp

lemma cBasis_at_node (n : Node) : (cBasis n n.val).re = Q n.val := by
  have hh := (factor_second_third (cBasis n) (differentiable_cBasis n) n.val).1
  rw [← P_cBasis n] at hh
  have he := congrArg Complex.re hh
  rw [← waveDerivative_eq_iterated] at he
  norm_num [Complex.mul_re] at he
  unfold Q
  linarith
lemma cBasis_deriv_at_node (n : Node) : 6*(deriv (cBasis n) n.val).re =
    (waveDerivative 3 n.val).re := by
  have hh := (factor_second_third (cBasis n) (differentiable_cBasis n) n.val).2
  rw [← P_cBasis n,← waveDerivative_eq_iterated] at hh
  have he := congrArg Complex.re hh
  simpa using he.symm

lemma dBasis_cBasis (n : Node) : dBasis n = fun s => (s-(n.val:ℂ))*cBasis n s := by
  funext s
  by_cases hs : s = (n.val:ℂ)
  · simp [hs,dBasis_node]
  · rw [dBasis_eq n hs,cBasis_eq n hs]
    field_simp
lemma deriv_dBasis_at_node (n : Node) : deriv (dBasis n) n.val = cBasis n n.val := by
  have hh := (((hasDerivAt_id (n.val:ℂ)).sub_const (n.val:ℂ)).mul
    ((differentiable_cBasis n _).hasDerivAt)).deriv
  rw [dBasis_cBasis n]
  simpa using! hh

lemma cBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) : cBasis n m.val = 0 := by
  rw [cBasis_eq n (by exact_mod_cast hmn),P_node,zero_div]
lemma dBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) : dBasis n m.val = 0 := by
  rw [dBasis_eq n (by exact_mod_cast hmn),P_node,zero_div]

lemma deriv_cBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) :
    deriv (cBasis n) m.val = 0 := by
  have hh := ((((hasDerivAt_id (m.val:ℂ)).sub_const (n.val:ℂ)).pow 2).mul
    ((differentiable_cBasis n _).hasDerivAt)).deriv
  change deriv (fun s => (s-(n.val:ℂ))^2*cBasis n s) m.val = _ at hh
  rw [← P_cBasis n,deriv_P_node m,cBasis_other_node hmn] at hh
  have hne : ((m.val:ℂ)-(n.val:ℂ))^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (by exact_mod_cast hmn))
  have hzero : ((m.val:ℂ)-(n.val:ℂ))^2 * deriv (cBasis n) m.val = 0 := by simpa using hh.symm
  exact (mul_eq_zero.mp hzero).resolve_left hne
lemma deriv_dBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) :
    deriv (dBasis n) m.val = 0 := by
  have hh := (((hasDerivAt_id (m.val:ℂ)).sub_const (n.val:ℂ)).mul
    ((differentiable_cBasis n _).hasDerivAt)).deriv
  change deriv (fun s => (s-(n.val:ℂ))*cBasis n s) m.val = _ at hh
  rw [← dBasis_cBasis n,cBasis_other_node hmn,deriv_cBasis_other_node hmn] at hh
  simpa using hh

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_TailSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction
open MeasureTheory

lemma continuous_intervalIntegral_complex {f : ℂ → ℝ → ℂ}
    (hf : Continuous f.uncurry) (a b : ℝ) :
    Continuous (fun s => ∫ t in a..b, f s t) := by
  have h₁ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := a) (b := b))
  have h₂ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := b) (b := a))
  simpa only [intervalIntegral, integral_Icc_eq_integral_Ioc] using! h₁.sub h₂

lemma exponential_first_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    I*Real.pi * (∫ r in (0:ℝ)..t, exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1)/u := by
  have hc : I*(Real.pi:ℂ)*u ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  have hi := integral_exp_mul_complex (a := 0) (b := t) hc
  simp only [Complex.ofReal_zero, mul_zero, exp_zero] at hi
  simp_rw [show ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = (I*Real.pi*u)*(r:ℂ) by intro r; ring]
  rw [hi]
  field_simp

lemma exponential_second_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    -(Real.pi:ℂ)^2 * (∫ r in (0:ℝ)..t, ((t:ℂ)-r)*exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1-I*Real.pi*(t:ℂ)*u)/u^2 := by
  let c : ℂ := I*Real.pi*u
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  let F : ℝ → ℂ := fun r => (((t:ℂ)-(r:ℂ))/c+1/c^2)*exp (c*(r:ℂ))
  have hd (x : ℝ) : HasDerivAt F (((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) x := by
    have hx : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 x := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := x))
    have hf := ((hx.const_sub (t:ℂ)).div_const c).add_const (1/c^2)
    have hh := hf.mul ((hx.const_mul c).cexp)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (show IntervalIntegrable (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) volume 0 t from
      (by fun_prop : Continuous (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ)))).intervalIntegrable 0 t)
  have he : ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = c*(r:ℂ) := by intro r; dsimp [c] <;> ring
  simp_rw [he]
  rw [hi]
  dsimp [F]
  simp only [sub_self, zero_div, zero_add, mul_zero, exp_zero,
    mul_one, sub_zero]
  dsimp [c]
  field_simp
  simp [Complex.I_sq]
  ring

lemma continuous_integralDBasis (n : Node) : Continuous (integralDBasis n) := by
  unfold integralDBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma continuous_integralCBasis (n : Node) : Continuous (integralCBasis n) := by
  unfold integralCBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma exp_frequency_sub (s n : ℂ) (l : Fin 31) :
    exp (I*Real.pi*frequency l*n) * exp (I*Real.pi*frequency l*(s-n)) =
      exp (I*Real.pi*frequency l*s) := by
  rw [← exp_add]
  congr 1
  ring

lemma integralDBasis_eq (n : Node) : integralDBasis n = dBasis n := by
  apply (continuous_integralDBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_dBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [dBasis_eq n hsn]
  unfold integralDBasis
  simp_rw [exponential_first_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_one, mul_assoc, exp_frequency_sub]
    _ = P s := by
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hz, sub_zero, P_fourier]

lemma integralCBasis_eq (n : Node) : integralCBasis n = cBasis n := by
  apply (continuous_integralCBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_cBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [cBasis_eq n hsn]
  unfold integralCBasis
  simp_rw [exponential_second_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) -
        (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) * (s-n.val) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_sub, mul_one, mul_assoc, exp_frequency_sub]
      ring
    _ = P s := by
      have hd : (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_deriv_cancel n
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hd, hz, zero_mul, sub_zero, sub_zero, P_fourier]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma spectralCCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralCCLM n f = spectralC n f :=
  spectralCLinear_apply n f
lemma spectralDCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralDCLM n f = spectralD n f :=
  spectralDLinear_apply n f
lemma spectralPCLM_apply (f : C(Spectrum,ℂ)) : spectralPCLM f = spectralP f := by
  simp [spectralPCLM,spectralP]

lemma spectralCCLM_norm (n : Node) : ‖spectralCCLM n‖ ≤ cVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [cVariation, coeffAbs] <;> positivity) _
lemma spectralDCLM_norm (n : Node) : ‖spectralDCLM n‖ ≤ dVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [dVariation, coeffAbs] <;> positivity) _

lemma extend_on (f : C(Spectrum,ℂ)) (t : ℝ) (ht : t ∈ Spectrum) :
    extend f t = f ⟨t,ht⟩ := by
  simp only [extend,Set.projIcc_of_mem _ ht]

lemma interval_frequency_subset (l : Fin 31) : Set.uIcc 0 (frequency l) ⊆ Spectrum := by
  have h := Set.uIcc_subset_uIcc (show (0:ℝ) ∈ Set.uIcc (-(5/6)) (5/6) by norm_num)
    (show frequency l ∈ Set.uIcc (-(5/6)) (5/6) by simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using frequency_mem l)
  simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using h

lemma spectralD_phase (n : Node) (s : ℂ) : spectralD n (phaseFunction s) = dBasis n s := by
  rw [← integralDBasis_eq]
  unfold spectralD integralDBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [← exp_add]
  congr 1
  ring

lemma spectralC_phase (n : Node) (s : ℂ) : spectralC n (phaseFunction s) = cBasis n s := by
  rw [← integralCBasis_eq]
  unfold spectralC integralCBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [mul_assoc,← exp_add]
  congr 2
  ring

lemma spectralP_phase (s : ℂ) : spectralP (phaseFunction s) = P s := by
  exact (P_fourier s).symm

lemma exponential_apply (f : C(Spectrum,ℂ)) (t : Spectrum) :
    (NormedSpace.exp f) t = exp (f t) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t)
    (ContinuousMap.evalCLM ℂ t).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply,Complex.exp_eq_exp_ℂ] using h

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma atomSpectral_apply (S : Fin 31 → ℂ) (f : C(Spectrum,ℂ)) :
    atomSpectral S f = ∑ j : Fin 31, S j*f ⟨frequency j,frequency_mem j⟩ := by
  simp [atomSpectral]

lemma atomSpectral_finiteC_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient j) (phaseFunction s) = finiteC j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteC_fourier]
  rfl
lemma atomSpectral_finiteD_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient j) (phaseFunction s) = finiteD j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteD_fourier]
  rfl

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_WaveFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma wavePhaseFunction_apply (q br : Fin 2) (t : Spectrum) :
    wavePhaseFunction q br t=taylorPhase q br t.val := by
  fin_cases br <;> rfl
lemma waveAmplitudeFunction_apply (q br : Fin 2) (t : Spectrum) :
    waveAmplitudeFunction q br t=taylorAmplitude q br t.val := by
  fin_cases br <;> rfl

lemma waveFunctionJet_apply (q br : Fin 2) (k : ℕ) (s : ℂ) (t : Spectrum) :
    waveFunctionJet q br k s t=finiteWaveJet q br t.val k s := by
  simp only [waveFunctionJet,ContinuousMap.mul_apply,ContinuousMap.pow_apply,
    exponential_apply,ContinuousMap.smul_apply,smul_eq_mul,wavePhaseFunction_apply,
    waveAmplitudeFunction_apply,finiteWaveJet,mul_comm s]
lemma hasDerivAt_waveFunctionJet (q br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (waveFunctionJet q br k) (waveFunctionJet q br (k+1) s) s := by
  have hh := ((hasDerivAt_exp_smul_const (wavePhaseFunction q br) s).const_mul
    (waveAmplitudeFunction q br)).mul_const ((wavePhaseFunction q br)^k)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try simp only [waveFunctionJet,pow_succ])
  all_goals first | rfl | (ext t; simp [ContinuousMap.mul_apply,ContinuousMap.pow_apply]; ring)
lemma hasDerivAt_inputJJet (a : InputCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (inputJJet a br k) (inputJJet a br (k+1) s) s := by
  exact ((tailSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)).add
    ((finiteSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 1 br k s))
lemma hasDerivAt_pairJJet (a₁ a₂ : InputCoefficients) (k : ℕ) (s : ℂ) :
    HasDerivAt (pairJJet a₁ a₂ k) (pairJJet a₁ a₂ (k+1) s) s :=
  (hasDerivAt_inputJJet a₁ 0 k s).add (hasDerivAt_inputJJet a₂ 1 k s)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_DirectWaveJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma waveFunctionJet_direct_zero (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 0 0 s=exp (-(Real.pi:ℂ)*(damping q-h)*s) • phaseFunction s := by
  ext t
  rw [waveFunctionJet_apply]
  simp only [finiteWaveJet,taylorAmplitude,taylorPhase,Fin.val_zero,↓reduceIte,pow_zero,mul_one,one_mul,
    ContinuousMap.smul_apply,smul_eq_mul,phaseFunction]
  simp only [ofReal_mul,ofReal_sub,ContinuousMap.coe_mk]
  rw [show (I*Real.pi*(t.val:ℂ)-(Real.pi:ℂ)*(damping q-h))*s=
    -(Real.pi:ℂ)*(damping q-h)*s+I*Real.pi*(t.val:ℂ)*s by ring,exp_add]
lemma waveFunctionJet_zero_phase (s : ℂ) : waveFunctionJet 0 0 0 s=phaseFunction s := by
  rw [waveFunctionJet_direct_zero]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,exp_zero,one_smul]
lemma hasDerivAt_phaseFunction (s : ℂ) : HasDerivAt phaseFunction (waveFunctionJet 0 0 1 s) s := by
  have he : phaseFunction=waveFunctionJet 0 0 0 := (funext waveFunctionJet_zero_phase).symm
  rw [he]
  exact hasDerivAt_waveFunctionJet 0 0 0 s
lemma spectralC_direct (n : Node) (s : ℂ) :
    spectralCCLM n (waveFunctionJet 0 0 0 s)=cBasis n s ∧
    spectralCCLM n (waveFunctionJet 0 0 1 s)=deriv (cBasis n) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralCCLM_apply,spectralC_phase]
  · have he : (fun s => spectralCCLM n (phaseFunction s))=cBasis n := funext fun s => by rw [spectralCCLM_apply,spectralC_phase]
    have hh := ((spectralCCLM n).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma spectralD_direct (n : Node) (s : ℂ) :
    spectralDCLM n (waveFunctionJet 0 0 0 s)=dBasis n s ∧
    spectralDCLM n (waveFunctionJet 0 0 1 s)=deriv (dBasis n) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralDCLM_apply,spectralD_phase]
  · have he : (fun s => spectralDCLM n (phaseFunction s))=dBasis n := funext fun s => by rw [spectralDCLM_apply,spectralD_phase]
    have hh := ((spectralDCLM n).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma spectralP_direct (s : ℂ) :
    spectralPCLM (waveFunctionJet 0 0 0 s)=P s ∧
    spectralPCLM (waveFunctionJet 0 0 1 s)=deriv P s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralPCLM_apply,spectralP_phase]
  · have he : (fun s => spectralPCLM (phaseFunction s))=P := funext fun s => by rw [spectralPCLM_apply,spectralP_phase]
    have hh := (spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma atomC_direct (a : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient a) (waveFunctionJet 0 0 0 s)=finiteC a s ∧
    atomSpectral (FiniteCertificate.cCoefficient a) (waveFunctionJet 0 0 1 s)=deriv (finiteC a) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,atomSpectral_finiteC_phase]
  · have he : (fun s => atomSpectral (FiniteCertificate.cCoefficient a) (phaseFunction s))=finiteC a := funext (atomSpectral_finiteC_phase a)
    have hh := ((atomSpectral (FiniteCertificate.cCoefficient a)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma atomD_direct (a : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient a) (waveFunctionJet 0 0 0 s)=finiteD a s ∧
    atomSpectral (FiniteCertificate.dCoefficient a) (waveFunctionJet 0 0 1 s)=deriv (finiteD a) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,atomSpectral_finiteD_phase]
  · have he : (fun s => atomSpectral (FiniteCertificate.dCoefficient a) (phaseFunction s))=finiteD a := funext (atomSpectral_finiteD_phase a)
    have hh := ((atomSpectral (FiniteCertificate.dCoefficient a)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma waveFunctionJet_direct_one (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 0 1 s= exp (-(Real.pi:ℂ)*(damping q-h)*s) •
      (waveFunctionJet 0 0 1 s-(Real.pi*(damping q-h):ℂ) • phaseFunction s) := by
  have he : waveFunctionJet q 0 0 = fun t => exp (-(Real.pi:ℂ)*(damping q-h)*t) • phaseFunction t := funext (waveFunctionJet_direct_zero q)
  have hh := (((hasDerivAt_id s).const_mul (-(Real.pi:ℂ)*(damping q-h))).cexp.smul (hasDerivAt_phaseFunction s)).deriv
  have hj := (hasDerivAt_waveFunctionJet q 0 0 s).deriv
  rw [he] at hj
  change deriv (fun t => exp (-(Real.pi:ℂ)*(damping q-h)*t) • phaseFunction t) s = _ at hh
  rw [←hj,hh]
  simp only [id_eq,mul_one]
  module
lemma cBasis_deriv_re (n : Node) : (deriv (cBasis n) n.val).re=Q n.val*D n.val := by
  have hQ : Q n.val≠0 := (lt_trans (by norm_num) (FiniteCertificate.Q_node_bounds n.val n.property.2).1).ne'
  have hh := cBasis_deriv_at_node n
  unfold D
  field_simp
  linarith
lemma finiteC_deriv_re (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    (deriv (finiteC a) n).re=Q n*D n := by
  have hmem : n%36∈residues := by rw [hn]; exact residue_mem a
  have hQ : Q n≠0 := (lt_trans (by norm_num) (FiniteCertificate.Q_node_bounds n hmem).1).ne'
  have hh := (finiteC_matching_jets a n hn).2
  unfold D
  field_simp
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_L1Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.L1Kernel
lemma operator_apply {α β : Type*} (K : β → α → ℝ)
    (hK : ∀ j, Summable (fun i => |K i j|)) (C : ℝ)
    (hB : ∀ j, ∑' i, |K i j| ≤ C) (a : ℓ¹(α,ℝ)) (i : β) :
    operator K hK C hB a i = ∑' j, a j * K i j := by
  have hh := (lp.evalCLM ℝ (fun _ : β => ℝ) 1 i).map_tsum (summable_columns K hK C hB a)
  change (∑' j, a j • column K hK j) i = ∑' j, a j*K i j at ⊢
  change (∑' j, a j • column K hK j) i = ∑' j, (a j • column K hK j) i at hh
  simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,column] using hh
end AtomicTriangular.L1Kernel
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_TailJetVector
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
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeNorm2
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
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeNorms
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
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeSumsBase
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
-- module Solutions.OAIQ334_EU.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma tailFixedColumn_apply (c : Fin 23) (p : TailNode × Fin 2) :
    tailFixedColumn c p = jet (if c.val=22 then h else H) h p.1.val.val p.2 (finiteColumn c) := rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_VariationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma varFreqBox_mem (j : Fin 31) : (varFreqBox j).Mem |frequency j| := by
  have hx := RI.mem_divNat (RI.mem_point (frequencyDistance j)) (by norm_num : 0<(18:ℕ))
  change ((RI.point (frequencyDistance j)).divNat 18).Mem _
  convert hx using 1
  all_goals try with_reducible_and_instances rfl
  fin_cases j <;> (first | (simp [frequencyDistance, frequency]; all_goals first | (norm_num [frequencyDistance, frequency]; done) | rfl | decide) | (norm_num [frequencyDistance, frequency]; done) | norm_num [frequencyDistance, frequency])

lemma cVariationBox_mem : cVariationBox.Mem cVariation := by
  have hx := RI.mem_mul (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (fourierNorm_mem j) (RI.mem_pow (varFreqBox_mem j) 2))) (RI.mem_pow piBox_mem 2)
  have hy := RI.mem_divNat hx (by norm_num : 0<2)
  simpa only [cVariationBox,cVariation,coeffAbs,sq_abs,Nat.cast_ofNat] using hy
lemma cVariation_lt : cVariation < 119 := by
  have hx := ri_mem_lt cVariationBox_mem 119 1 (by norm_num) (by decide +kernel)
  simpa using hx

lemma dVariationBox_mem : dVariationBox.Mem dVariation := by
  have hx := RI.mem_mul (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (fourierNorm_mem j) (RI.mem_pow (varFreqBox_mem j) 1))) (RI.mem_pow piBox_mem 1)
  simpa only [dVariationBox,dVariation,coeffAbs,pow_one] using hx
lemma dVariation_lt : dVariation < 119 := by
  have hx := ri_mem_lt dVariationBox_mem 119 1 (by norm_num) (by decide +kernel)
  simpa using hx
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_CoefficientSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma finiteColumn_even (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val,by omega⟩ l=cCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val<22 by omega,↓reduceDIte,
    show 2*j.val%2=0 by omega,↓reduceIte]
  congr 2
  omega
lemma finiteColumn_odd (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val+1,by omega⟩ l=dCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val+1<22 by omega,↓reduceDIte,
    show ¬((2*j.val+1)%2=0) by omega,↓reduceIte]
  congr 2
  omega
lemma sum_fin22_pairs {M : Type*} [AddCommMonoid M] (g : Fin 22 → M) :
    (∑ c : Fin 22, g c)=∑ j : Fin 11, (g ⟨2*j.val,by omega⟩+g ⟨2*j.val+1,by omega⟩) := by
  have hh := (finProdFinEquiv (m:=11) (n:=2)).sum_comp g
  rw [Fintype.sum_prod_type] at hh
  simp only [Fin.sum_univ_two] at hh
  convert hh.symm using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  congr 2 <;> apply Fin.ext <;> simp [finProdFinEquiv, mul_comm, add_comm]
lemma finiteSpectral_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    finiteSpectral (coefficientInput C a w)=∑ c : Fin 22,
      (a c:ℂ) • atomSpectral (finiteColumn ⟨c.val,by omega⟩) := by
  rw [sum_fin22_pairs]
  simp only [finiteSpectral,coefficientInput]
  apply Finset.sum_congr rfl
  intro j _
  congr 2 <;> congr 1 <;> funext l
  · exact (finiteColumn_even j l).symm
  · exact (finiteColumn_odd j l).symm
lemma finiteSpectral_coefficient_apply (C : ℝ) (a : TrigonometricCoefficients)
    (w : TailCoefficients) (f : C(Spectrum,ℂ)) :
    finiteSpectral (coefficientInput C a w) f=∑ c : Fin 22,
      (a c:ℂ)*(∑ j : Fin 31, finiteColumn ⟨c.val,by omega⟩ j*f ⟨frequency j,frequency_mem j⟩) := by
  rw [finiteSpectral_coefficient]
  simp only [sum_apply,smul_apply,smul_eq_mul,atomSpectral_apply]
lemma tailSpectral_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput C a w)= (C:ℂ) • spectralPCLM+
      ∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val) := rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_NormalizedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction

lemma jetFunction_apply (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) (t : Spectrum) :
    jetFunction q v n d t=jetMultiplier (damping q) v n d t.val := rfl

lemma zeta_change (k v t : ℝ) : I*Real.pi*zeta k v t =
    (Real.pi*(v-h):ℂ)+I*Real.pi*zeta k h t := by
  unfold zeta
  push_cast
  ring_nf
  simp [I_sq]
  ring
lemma transformedWave_change (k v t : ℝ) (s : ℂ) : transformedWave k v t s=
    exp (Real.pi*(v-h)*s)*transformedWave k h t s := by
  unfold transformedWave
  rw [zeta_change,add_mul,exp_add]
  ring
lemma negativeJet_wave (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) (t : ℝ) :
    negativeJet v n d (finiteWaveJet q 1 t 0 n) (finiteWaveJet q 1 t 1 n)=
      jetMultiplier (damping q) v n d t := by
  simp only [finiteWaveJet,taylorPhase,taylorAmplitude,Fin.val_one,Nat.one_ne_zero,↓reduceIte,pow_zero,pow_one,mul_one]
  unfold negativeJet jetMultiplier
  rw [transformedWave_change]
  unfold transformedWave
  rw [zeta_change (damping q) v t]
  split_ifs <;> ring
lemma negativeJet_linear (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (T (waveFunctionJet q 1 0 n)) (T (waveFunctionJet q 1 1 n))=
      T (jetFunction q v n d) := by
  have he : jetFunction q v n d =
      (exp (Real.pi*(v-h)*(n:ℂ))*(Q n:ℂ)⁻¹) •
        (if d.val=0 then -waveFunctionJet q 1 0 n else
          ((D n:ℂ)-Real.pi*(v-h)) • waveFunctionJet q 1 0 n-waveFunctionJet q 1 1 n) := by
    ext t
    simp only [ContinuousMap.smul_apply,smul_eq_mul,jetFunction_apply]
    split_ifs with hd
    · simpa only [negativeJet,hd,↓reduceIte,ContinuousMap.neg_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,waveFunctionJet_apply] using (negativeJet_wave q v n d t.val).symm
    · simpa only [negativeJet,hd,↓reduceIte,ContinuousMap.neg_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,waveFunctionJet_apply] using (negativeJet_wave q v n d t.val).symm
  rw [he]
  unfold negativeJet
  split_ifs <;> simp only [map_smul,map_neg,map_sub,smul_eq_mul]
lemma finiteSpectral_jet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (finiteSpectral (coefficientInput C a w) (jetFunction q v n d)).re=
      ∑ c : Fin 22, a c*jet (damping q) v n d (finiteColumn ⟨c.val,by omega⟩) := by
  rw [finiteSpectral_coefficient_apply]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [mul_re]
  simp only [ofReal_re,ofReal_im,zero_mul,sub_zero]
  congr 1
  unfold jet
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [jetFunction_apply,mul_comm]
lemma spectralP_jet (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (spectralP (jetFunction q v n d)).re=jet (damping q) v n d (finiteColumn 22) := by
  unfold spectralP jet
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change fourierCoeff j*jetMultiplier _ _ _ _ _ = jetMultiplier _ _ _ _ _*fourierCoeff j
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_DirectCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma negativeJet_re (v : ℝ) (n : ℤ) (d : Fin 2) (a b : ℂ) :
    (negativeJet v n d a b).re=
      Real.exp (Real.pi*(v-h)*n)/(Q n)*
        (if d.val=0 then -a.re else (D n-Real.pi*(v-h))*a.re-b.re) := by
  have he : exp (Real.pi*(v-h)*(n:ℂ))=(Real.exp (Real.pi*(v-h)*n):ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; rfl
  unfold negativeJet
  rw [he,←ofReal_inv]
  split_ifs <;> simp only [mul_re,mul_im,ofReal_re,ofReal_im,neg_re,sub_re,sub_im,
    zero_mul,mul_zero,sub_zero,add_zero]
  all_goals ring
lemma damped_wave_re (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (n : ℤ) :
    (T (waveFunctionJet q 0 0 n)).re=Real.exp (-Real.pi*(damping q-h)*n)*(T (waveFunctionJet 0 0 0 n)).re ∧
    (T (waveFunctionJet q 0 1 n)).re=Real.exp (-Real.pi*(damping q-h)*n)*
      ((T (waveFunctionJet 0 0 1 n)).re-Real.pi*(damping q-h)*(T (waveFunctionJet 0 0 0 n)).re) := by
  have he : exp (-(Real.pi:ℂ)*(damping q-h)*(n:ℂ))=(Real.exp (-Real.pi*(damping q-h)*n):ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; rfl
  constructor
  · rw [waveFunctionJet_direct_zero,map_smul,←waveFunctionJet_zero_phase,he]
    simp only [smul_eq_mul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  · rw [waveFunctionJet_direct_one,map_smul,map_sub,map_smul,←waveFunctionJet_zero_phase,he]
    simp only [smul_eq_mul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,sub_re,mul_im,sub_im,mul_zero,add_zero]
lemma negativeJet_direct_re (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (T (waveFunctionJet q 0 0 n)) (T (waveFunctionJet q 0 1 n))).re=
      Real.exp (Real.pi*(v-damping q)*n)/(Q n)*
        (if d.val=0 then -(T (waveFunctionJet 0 0 0 n)).re else
          (D n-Real.pi*(v-damping q))*(T (waveFunctionJet 0 0 0 n)).re-(T (waveFunctionJet 0 0 1 n)).re) := by
  rw [negativeJet_re,(damped_wave_re T q n).1,(damped_wave_re T q n).2]
  have he : Real.exp (Real.pi*(v-h)*n)*Real.exp (-Real.pi*(damping q-h)*n)=
      Real.exp (Real.pi*(v-damping q)*n) := by rw [←Real.exp_add]; congr 1; ring
  split_ifs
  · linear_combination (-(T (waveFunctionJet 0 0 0 n)).re/(Q n))*he
  · linear_combination (((D n-Real.pi*(v-damping q))*(T (waveFunctionJet 0 0 0 n)).re-(T (waveFunctionJet 0 0 1 n)).re)/(Q n))*he

lemma negativeJet_direct_linear (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (T (waveFunctionJet q 0 0 n)) (T (waveFunctionJet q 0 1 n))=
      T (directJetFunction q v n d) := by
  unfold directJetFunction negativeJet
  split_ifs <;> simp only [map_smul,map_neg,map_sub,smul_eq_mul]
lemma Q_node_ne (n : Node) : Q n.val≠0 :=
  (lt_trans (by norm_num) (FiniteCertificate.Q_node_bounds n.val n.property.2).1).ne'
lemma spectralP_directJet (q : Fin 2) (v : ℝ) (n : Node) (d : Fin 2) :
    (spectralPCLM (directJetFunction q v n.val d)).re=0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralP_direct _).1,(spectralP_direct _).2,P_node,deriv_P_node]
  split_ifs <;> simp
lemma spectralC_directJet (n m : Node) (d : Fin 2) :
    (spectralCCLM m (directJetFunction 0 h n.val d)).re=
      if n.val=m.val ∧ d.val=0 then -1 else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralC_direct m _).1,(spectralC_direct m _).2]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,Real.exp_zero,sub_zero]
  by_cases hm : n=m
  · subst m
    rw [cBasis_at_node,cBasis_deriv_re]
    by_cases hd : d.val=0
    · simp only [hd,↓reduceIte,and_self]
      field_simp [Q_node_ne n]
    · simp only [hd,↓reduceIte,and_false]
      ring
  · have hmn : n.val≠m.val := fun he => hm (Subtype.ext he)
    rw [cBasis_other_node hmn,deriv_cBasis_other_node hmn]
    simp [hmn]
lemma spectralD_directJet (n m : Node) (d : Fin 2) :
    (spectralDCLM m (directJetFunction 0 h n.val d)).re=
      if n.val=m.val ∧ d.val=1 then -1 else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralD_direct m _).1,(spectralD_direct m _).2]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,Real.exp_zero,sub_zero]
  by_cases hm : n=m
  · subst m
    have hd0 : dBasis n n.val=0 := by rw [dBasis_cBasis]; simp
    rw [hd0,deriv_dBasis_at_node,cBasis_at_node]
    fin_cases d <;> simp only [Nat.one_ne_zero,↓reduceIte,zero_re,mul_zero,zero_sub,neg_zero,mul_zero,and_true]
    · norm_num
    · field_simp [Q_node_ne n]
  · have hmn : n.val≠m.val := fun he => hm (Subtype.ext he)
    rw [dBasis_other_node hmn,deriv_dBasis_other_node hmn]
    simp [hmn]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma atomC_directJet (a : Fin 15) (v : ℝ) (n : Node) (d : Fin 2) :
    (atomSpectral (FiniteCertificate.cCoefficient a) (directJetFunction 1 v n.val d)).re=
      if n.val%36=residue a then Real.exp (Real.pi*(v-H)*n.val)*
        (if d.val=0 then -1 else -Real.pi*(v-H)) else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(atomC_direct a _).1,(atomC_direct a _).2]
  simp only [damping,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  by_cases hm : n.val%36=residue a
  · rw [(finiteC_matching_jets a n.val hm).1,finiteC_deriv_re a n.val hm,ite_eq_left hm]
    split_ifs <;> field_simp [Q_node_ne n]
    ring
  · rw [(finiteC_other_jets a n hm).1,(finiteC_other_jets a n hm).2,ite_eq_right hm]
    split_ifs <;> simp
lemma atomD_directJet (a : Fin 15) (v : ℝ) (n : Node) (d : Fin 2) :
    (atomSpectral (FiniteCertificate.dCoefficient a) (directJetFunction 1 v n.val d)).re=
      if n.val%36=residue a then Real.exp (Real.pi*(v-H)*n.val)*
        (if d.val=0 then 0 else -1) else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(atomD_direct a _).1,(atomD_direct a _).2]
  simp only [damping,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  by_cases hm : n.val%36=residue a
  · rw [(finiteD_matching_jets a n.val hm).1,(finiteD_matching_jets a n.val hm).2,
      (finiteC_matching_jets a n.val hm).1,ite_eq_left hm]
    split_ifs <;> simp only [zero_re,neg_zero,mul_zero,zero_sub]
    field_simp [Q_node_ne n]
  · rw [(finiteD_other_jets a n hm).1,(finiteD_other_jets a n hm).2,ite_eq_right hm]
    split_ifs <;> simp
lemma finiteColumn_directJet (c : Fin 22) (v : ℝ) (n : Node) (d : Fin 2) :
    (atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 v n.val d)).re=
      if n.val%36=residue ⟨c.val/2,by omega⟩ then Real.exp (Real.pi*(v-H)*n.val)*
        (if c.val%2=0 then (if d.val=0 then -1 else -Real.pi*(v-H))
         else (if d.val=0 then 0 else -1)) else 0 := by
  unfold finiteColumn
  simp only [show c.val<22 from c.isLt,↓reduceDIte]
  by_cases hc : c.val%2=0
  · simp only [hc,↓reduceIte]
    exact atomC_directJet _ _ _ _
  · simp only [hc,↓reduceIte]
    exact atomD_directJet _ _ _ _
lemma finiteColumn_tail_directJet (c : Fin 22) (p : TailNode × Fin 2) :
    (atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 h p.1.val.val p.2)).re= -AallKernel p c := by
  rw [finiteColumn_directJet]
  unfold AallKernel repetitionKernel repetitionEntry
  have he : h-H= -eta := by norm_num [h,H,eta]
  simp only [he,mul_neg]
  split_ifs <;> ring_nf
lemma finiteSpectral_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (v : ℝ) (n : ℤ) (d : Fin 2) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 v n d)).re=
      ∑ c : Fin 22,a c*(atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 v n d)).re := by
  rw [finiteSpectral_coefficient]
  simp only [sum_apply,smul_apply,smul_eq_mul,re_sum,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
lemma finiteSpectral_tail_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 h p.1.val.val p.2)).re= -AallOperator a p := by
  rw [finiteSpectral_directJet]
  simp_rw [finiteColumn_tail_directJet,mul_neg]
  rw [Finset.sum_neg_distrib]
  congr 1
  unfold AallOperator
  erw [AtomicTriangular.L1Kernel.operator_apply,tsum_fintype]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_SpectralJetBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma spectralCVector_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (n : ℤ) (f : ℝ → E) (hf : Continuous f) :
    L (spectralCVector n f)=spectralCVector n (fun t => L (f t)) := by
  unfold spectralCVector
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro l _
  congr 2
  rw [←L.intervalIntegral_comp_comm ((by fun_prop : Continuous (fun t : ℝ =>
    (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))).intervalIntegrable 0 (frequency l))]
  apply intervalIntegral.integral_congr
  intro t _
  change L (((frequency l-t:ℝ):ℂ) • (exp (-I*Real.pi*(t:ℂ)*n) • f t)) =
    ((frequency l-t:ℝ):ℂ) • (exp (-I*Real.pi*(t:ℂ)*n) • L (f t))
  simp only [map_smul]
lemma spectralDVector_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (n : ℤ) (f : ℝ → E) (hf : Continuous f) :
    L (spectralDVector n f)=spectralDVector n (fun t => L (f t)) := by
  unfold spectralDVector
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro l _
  congr 2
  rw [←L.intervalIntegral_comp_comm ((by fun_prop : Continuous (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t)).intervalIntegrable 0 (frequency l))]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [map_smul]
lemma spectralC_of_restriction (n : Node) (f : C(Spectrum,ℂ)) (g : ℝ → ℂ)
    (hg : ∀ t (ht : t∈Spectrum), f ⟨t,ht⟩=g t) : spectralC n f=spectralCVector n.val g := by
  unfold spectralC spectralCVector
  apply Finset.sum_congr rfl
  intro l _
  simp only [smul_eq_mul]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  change ((frequency l:ℂ)-(t:ℂ))*exp (-I*Real.pi*(t:ℂ)*(n.val:ℂ))*extend f t =
    (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*(n.val:ℂ))*g t)
  have hm := interval_frequency_subset l ht
  rw [extend_on f t hm,hg]
  simp only [Complex.real_smul,ofReal_sub]
  ring
lemma spectralD_of_restriction (n : Node) (f : C(Spectrum,ℂ)) (g : ℝ → ℂ)
    (hg : ∀ t (ht : t∈Spectrum), f ⟨t,ht⟩=g t) : spectralD n f=spectralDVector n.val g := by
  unfold spectralD spectralDVector
  apply Finset.sum_congr rfl
  intro l _
  simp only [smul_eq_mul]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  have hm := interval_frequency_subset l ht
  rw [extend_on f t hm,hg]
lemma spectralC_jetFunction (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) (n : Node) :
    spectralC n (jetFunction q v m d)=(tailJetVector (damping q) v m n.val 0 d) := by
  rw [spectralC_of_restriction n _ (jetMultiplier (damping q) v m d) (fun _ _ => rfl)]
  symm
  exact spectralCVector_map (PiLp.proj 1 (fun _ : Fin 2 => ℂ) d) n.val _ (continuous_jetVector (damping_pos q) v m)
lemma spectralD_jetFunction (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) (n : Node) :
    spectralD n (jetFunction q v m d)=(tailJetVector (damping q) v m n.val 1 d) := by
  rw [spectralD_of_restriction n _ (jetMultiplier (damping q) v m d) (fun _ _ => rfl)]
  symm
  exact spectralDVector_map (PiLp.proj 1 (fun _ : Fin 2 => ℂ) d) n.val _ (continuous_jetVector (damping_pos q) v m)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_SpectralProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

lemma tailColumnSpectral_norm (p : TailNode × Fin 2) : ‖tailColumnSpectral p‖≤119 := by
  unfold tailColumnSpectral
  split_ifs
  · exact (spectralCCLM_norm _).trans cVariation_lt.le
  · exact (spectralDCLM_norm _).trans dVariation_lt.le
lemma summable_l1_complex_smul {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedSpace ℂ E] (w : ℓ¹(ι,ℝ)) (T : ι → E) (M : ℝ) (hM : ∀ i, ‖T i‖≤M) :
    Summable (fun i => (w i:ℂ) • T i) := by
  apply Summable.of_norm_bounded ((l1_summable w).mul_right M)
  intro i
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM i) (abs_nonneg _)
lemma summable_tail_columns (w : TailCoefficients) :
    Summable (fun p => (w p:ℂ) • tailColumnSpectral p) := by
  exact summable_l1_complex_smul w tailColumnSpectral 119 tailColumnSpectral_norm
lemma tsum_prod_fin_two {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (g : ι × Fin 2 → E) (hg : Summable g) :
    (∑' p, g p)=∑' i, (g (i,0)+g (i,1)) := by
  rw [hg.tsum_prod]
  simp only [tsum_fintype,Fin.sum_univ_two]
lemma tailSpectral_product (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput C a w)= (C:ℂ) • spectralPCLM+
      ∑' p : TailNode × Fin 2,(w p:ℂ) • tailColumnSpectral p := by
  have he := tsum_prod_fin_two (fun p => (w p:ℂ) • tailColumnSpectral p) (summable_tail_columns w)
  rw [he,tailSpectral_coefficient]
  rfl
lemma summable_tail_columns_apply (w : TailCoefficients) (f : C(Spectrum,ℂ)) :
    Summable (fun p => (w p:ℂ)*tailColumnSpectral p f) := by
  simpa only [ContinuousLinearMap.apply_apply,smul_apply,smul_eq_mul] using
    ((ContinuousLinearMap.apply ℂ ℂ f).summable (summable_tail_columns w))
lemma tailSpectral_product_apply (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (f : C(Spectrum,ℂ)) :
    tailSpectral (coefficientInput C a w) f=(C:ℂ)*spectralP f+
      ∑' p : TailNode × Fin 2,(w p:ℂ)*tailColumnSpectral p f := by
  rw [tailSpectral_product,add_apply,smul_apply,smul_eq_mul,spectralPCLM_apply]
  congr 1
  exact (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_tail_columns w)
lemma tailColumnSpectral_jet (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) (p : TailNode × Fin 2) :
    (tailColumnSpectral p (jetFunction q v m d)).re=tailJet (damping q) v m p.1.val.val p.2 d := by
  unfold tailColumnSpectral tailJet tailJetVector
  split_ifs with hc
  · rw [spectralCCLM_apply,spectralC_jetFunction]
    rfl
  · rw [spectralDCLM_apply,spectralD_jetFunction]
    rfl
lemma tailSpectral_jet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) :
    (tailSpectral (coefficientInput C a w) (jetFunction q v m d)).re=
      C*jet (damping q) v m d (finiteColumn 22)+
      ∑' p : TailNode × Fin 2,w p*tailJet (damping q) v m p.1.val.val p.2 d := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,spectralP_jet,tailColumnSpectral_jet]
lemma negativeJet_add (v : ℝ) (n : ℤ) (d : Fin 2) (a b c e : ℂ) :
    negativeJet v n d (a+c) (b+e)=negativeJet v n d a b+negativeJet v n d c e := by
  unfold negativeJet
  split_ifs <;> ring
lemma inputJJet_negative (a : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (inputJJet a 1 0 n) (inputJJet a 1 1 n)=
      tailSpectral a (jetFunction 0 v n d)+finiteSpectral a (jetFunction 1 v n d) := by
  unfold inputJJet
  rw [negativeJet_add,negativeJet_linear,negativeJet_linear]
lemma inputJJet_negative_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (inputJJet (coefficientInput C a w) 1 0 n)
      (inputJJet (coefficientInput C a w) 1 1 n)).re=
      C*jet h v n d (finiteColumn 22)+
      (∑' p : TailNode × Fin 2,w p*tailJet h v n p.1.val.val p.2 d)+
      ∑ c : Fin 22,a c*jet H v n d (finiteColumn ⟨c.val,by omega⟩) := by
  rw [inputJJet_negative,add_re,tailSpectral_jet,finiteSpectral_jet]
  rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_TailCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
attribute [local instance] Classical.propDecidable
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma tailColumnSpectral_directJet (p q : TailNode × Fin 2) :
    (tailColumnSpectral q (directJetFunction 0 h p.1.val.val p.2)).re=if q=p then -1 else 0 := by
  unfold tailColumnSpectral
  by_cases hc : q.2.val=0
  · simp only [hc,↓reduceIte,spectralC_directJet]
    congr 1
    apply propext
    constructor
    · rintro ⟨hn,hd⟩
      apply Prod.ext
      · exact Subtype.ext (Subtype.ext hn.symm)
      · exact Fin.ext (hc.trans hd.symm)
    · intro he; subst q; exact ⟨rfl,hc⟩
  · simp only [hc,↓reduceIte,spectralD_directJet]
    have hc1 : q.2.val=1 := by omega
    congr 1
    apply propext
    constructor
    · rintro ⟨hn,hd⟩
      apply Prod.ext
      · exact Subtype.ext (Subtype.ext hn.symm)
      · exact Fin.ext (hc1.trans hd.symm)
    · intro he; subst q; exact ⟨rfl,hc1⟩
lemma tailSpectral_tail_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (tailSpectral (coefficientInput C a w) (directJetFunction 0 h p.1.val.val p.2)).re= -w p := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,←spectralPCLM_apply,
    spectralP_directJet,tailColumnSpectral_directJet,mul_zero,zero_add,mul_ite,mul_neg,mul_one,
    tsum_ite_eq]
lemma spectralC_other_directJet (q : Fin 2) (v : ℝ) (n m : Node) (hne : n.val≠m.val) (d : Fin 2) :
    (spectralCCLM m (directJetFunction q v n.val d)).re=0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralC_direct m _).1,(spectralC_direct m _).2,
    cBasis_other_node hne,deriv_cBasis_other_node hne]
  split_ifs <;> simp
lemma spectralD_other_directJet (q : Fin 2) (v : ℝ) (n m : Node) (hne : n.val≠m.val) (d : Fin 2) :
    (spectralDCLM m (directJetFunction q v n.val d)).re=0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralD_direct m _).1,(spectralD_direct m _).2,
    dBasis_other_node hne,deriv_dBasis_other_node hne]
  split_ifs <;> simp
lemma tailColumnSpectral_other_directJet (n : Node) (hn : n.val∈FiniteNodes)
    (q : TailNode × Fin 2) (v : ℝ) (d : Fin 2) :
    (tailColumnSpectral q (directJetFunction 0 v n.val d)).re=0 := by
  have hne : n.val≠q.1.val.val := fun he => q.1.property (he ▸ hn)
  unfold tailColumnSpectral
  split_ifs
  · exact spectralC_other_directJet _ _ _ _ hne _
  · exact spectralD_other_directJet _ _ _ _ hne _
lemma tailSpectral_finite_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (n : Node) (hn : n.val∈FiniteNodes) (v : ℝ) (d : Fin 2) :
    (tailSpectral (coefficientInput C a w) (directJetFunction 0 v n.val d)).re=0 := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,←spectralPCLM_apply,
    spectralP_directJet,tailColumnSpectral_other_directJet n hn,mul_zero,zero_add,tsum_zero]
lemma inputJJet_direct_negative (a : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (inputJJet a 0 0 n) (inputJJet a 0 1 n)=
      tailSpectral a (directJetFunction 0 v n d)+finiteSpectral a (directJetFunction 1 v n d) := by
  unfold inputJJet
  rw [negativeJet_add,negativeJet_direct_linear,negativeJet_direct_linear]
lemma inputJJet_tail_direct_negative (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (negativeJet h p.1.val.val p.2 (inputJJet (coefficientInput C a w) 0 0 p.1.val.val)
      (inputJJet (coefficientInput C a w) 0 1 p.1.val.val)).re= -w p-AallOperator a p := by
  rw [inputJJet_direct_negative,add_re,tailSpectral_tail_directJet,finiteSpectral_tail_directJet]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma rowNode_mem (i : Fin 20) : (rowNode i).val∈FiniteNodes := by
  have hh : ∀ n : Fin 10,finiteNode n∈FiniteNodes := by decide +kernel
  exact hh _
lemma finite_column_matching (i : Fin 20) (c : Fin 22) :
    ((rowNode i).val%36=residue ⟨c.val/2,by omega⟩ ∧ c.val%2=i.val%2) ↔ c.val=i.val+2 := by
  have hh : ∀ i : Fin 20, ∀ c : Fin 22,
      ((rowNode i).val%36=residue ⟨c.val/2,by omega⟩ ∧ c.val%2=i.val%2) ↔ c.val=i.val+2 := by decide +kernel
  exact hh i c
lemma finiteColumn_row_directJet (c : Fin 22) (i : Fin 20) :
    (atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 H (rowNode i).val (rowDerivative i))).re=
      if c=⟨i.val+2,by omega⟩ then -1 else 0 := by
  rw [finiteColumn_directJet]
  simp only [sub_self,mul_zero,zero_mul,Real.exp_zero,one_mul,rowDerivative]
  have hh := finite_column_matching i c
  have hc0 : c.val%2<2 := Nat.mod_lt _ (by norm_num)
  have hi0 : i.val%2<2 := Nat.mod_lt _ (by norm_num)
  simp only [Fin.ext_iff]
  split_ifs <;> norm_num at * <;> (try omega)
  all_goals split_ifs <;> norm_num at * <;> try omega
  all_goals simp_all only [↓reduceIte]
  all_goals
    split_ifs <;> norm_num at *
    omega
lemma finiteSpectral_row_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (i : Fin 20) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 H (rowNode i).val (rowDerivative i))).re=
      -a ⟨i.val+2,by omega⟩ := by
  rw [finiteSpectral_directJet]
  simp only [finiteColumn_row_directJet,mul_ite,mul_neg,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
lemma inputJJet_row_direct_negative (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i) (inputJJet (coefficientInput C a w) 0 0 (rowNode i).val)
      (inputJJet (coefficientInput C a w) 0 1 (rowNode i).val)).re= -a ⟨i.val+2,by omega⟩ := by
  rw [inputJJet_direct_negative,add_re,tailSpectral_finite_directJet C a w _ (rowNode_mem i),
    finiteSpectral_row_directJet,zero_add]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_FiniteAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma finiteRow_sum (C : ℝ) (a : Fin 22 → ℝ) (i : Fin 20) :
    C*jet h H (rowNode i).val (rowDerivative i) (finiteColumn 22)+
      (∑ c : Fin 22,a c*jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨c.val,by omega⟩))=
    (∑ j : Fin 20,R i j*a ⟨j.val+2,by omega⟩)+
      R0 i 0*a 0+R0 i 1*a 1+R0 i 2*C := by
  have hR (j : Fin 20) : R i j=jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨j.val+2,by omega⟩) := by
    simp only [R,fullJetMatrix,show j.val+2≠22 by omega,↓reduceIte,rowNode,rowDerivative]
  simp_rw [hR]
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  have hh : (∑ j : Fin 20,a j.succ.succ*jet H H (rowNode i).val (rowDerivative i)
      (finiteColumn ⟨j.succ.succ.val,by omega⟩))=
      ∑ j : Fin 20,jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨j.val+2,by omega⟩)*a ⟨j.val+2,by omega⟩ := by
    apply Finset.sum_congr rfl
    intro j _
    have he : j.succ.succ=(⟨j.val+2,by omega⟩:Fin 22) := Fin.ext (by simp)
    simp only [he]
    exact mul_comm _ _
  rw [hh]
  simp only [R0,fullJetMatrix,Fin.val_zero,Fin.val_one,Fin.val_two,show 0<2 by omega,
    show 1<2 by omega,lt_self_iff_false,↓reduceIte,show (0:ℕ)≠22 by omega,show (1:ℕ)≠22 by omega]
  change _= _
  dsimp [rowNode,rowDerivative]
  ring
lemma finiteApprox_shift (side : Fin 2) (e : Fin 8 → ℝ) (i : Fin 20) :
    finiteApprox side e ⟨i.val+2,by omega⟩=(finiteSolution side *ᵥ e) i := by
  change (∑ j : Fin 8,Acoefficient side ⟨i.val+2,by omega⟩ j*e j)=_
  simp only [Acoefficient,show ¬(i.val+2<2) by omega,show i.val+2≠22 by omega,↓reduceDIte]
  rfl
lemma finiteApprox_fixed (side : Fin 2) (e : Fin 8 → ℝ) (i : Fin 2) :
    finiteApprox side e ⟨i.val,by omega⟩=(gamma side *ᵥ e) ⟨i.val,by omega⟩ := by
  change (∑ j : Fin 8,Acoefficient side ⟨i.val,by omega⟩ j*e j)=_
  simp only [Acoefficient,show i.val<2 from i.isLt,↓reduceDIte]
  rfl
lemma finiteApprox_transformed (side : Fin 2) (e : Fin 8 → ℝ) (i : Fin 20) :
    (gamma side *ᵥ e) 2*jet h H (rowNode i).val (rowDerivative i) (finiteColumn 22)+
      (∑ c : Fin 22,finiteApprox side e c*jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨c.val,by omega⟩))=
      (R *ᵥ (finiteSolution side *ᵥ e)+R0 *ᵥ (gamma side *ᵥ e)) i := by
  rw [finiteRow_sum]
  simp only [finiteApprox_shift]
  have h0 : finiteApprox side e 0=(gamma side *ᵥ e) 0 := finiteApprox_fixed side e 0
  have h1 : finiteApprox side e 1=(gamma side *ᵥ e) 1 := finiteApprox_fixed side e 1
  erw [h0,h1]
  change (∑ j : Fin 20,R i j*(finiteSolution side *ᵥ e) j)+_+_+_=
    (∑ j : Fin 20,R i j*(finiteSolution side *ᵥ e) j)+(∑ j : Fin 3,R0 i j*(gamma side *ᵥ e) j)
  rw [Fin.sum_univ_three]
  abel
lemma gamma_actual (side : Fin 2) (z : ℝ) :
    (gamma side *ᵥ actualParameter z)= ![11/25,0,if side.val=0 then -(3/500) else 3/500] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,gamma,Fin.sum_univ_succ,actualParameter]
lemma inputJJet_row_transformed (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i) (inputJJet (coefficientInput C a w) 1 0 (rowNode i).val)
      (inputJJet (coefficientInput C a w) 1 1 (rowNode i).val)).re=
    Boperator w i + C*jet h H (rowNode i).val (rowDerivative i) (finiteColumn 22)+
      (∑ c : Fin 22,a c*jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨c.val,by omega⟩)) := by
  rw [inputJJet_negative_coefficient]
  have hb : Boperator w i=∑' p : TailNode × Fin 2,w p*tailJet h H (rowNode i).val p.1.val.val p.2 (rowDerivative i) := by
    unfold Boperator
    erw [operator_apply]
    rfl
  rw [hb]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_FiniteTargetBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Matrix
namespace AtomicTriangular.Construction
lemma gaussianTarget_factor (z : ℝ) (n : Fin 10) (d : Fin 2) :
    gaussianTarget H z (finiteNode n) d=targetCoefficient n * Real.exp ((1-finiteNode n)/z)*
      (if d.val=0 then z else -1+(Real.pi*eta-D (finiteNode n))*z) := by
  have he : H-h=eta := by norm_num [H,h,eta]
  simp only [gaussianTarget,targetCoefficient,he,Real.exp_add]
  ring
lemma Yf_actual (z : ℝ) (i : Fin 20) :
    (Yf *ᵥ actualParameter z) i=
      if i.val<8 then gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ else 0 := by
  rw [gaussianTarget_factor]
  fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Yf,actualParameter,Fin.sum_univ_succ,
    finiteNode,residue] <;> ring
lemma Yf_residual (z : ℝ) (i : Fin 20) :
    (Yf *ᵥ actualParameter z) i+finiteResidual z i=
      gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ := by
  rw [Yf_actual]
  change (if i.val<8 then _ else 0)+(if i.val<8 then 0 else _)=_
  split_ifs <;> ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_TailInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma inputJJet_tail_transformed (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (negativeJet h p.1.val.val p.2 (inputJJet (coefficientInput C a w) 1 0 p.1.val.val)
      (inputJJet (coefficientInput C a w) 1 1 p.1.val.val)).re=
      Doperator w p+CallOperator a p+C*tailFixedColumn 22 p := by
  rw [inputJJet_negative_coefficient]
  have hd : Doperator w p=∑' q : TailNode × Fin 2,w q*tailJet h h p.1.val.val q.1.val.val q.2 p.2 := by
    unfold Doperator
    erw [operator_apply]
    rfl
  have hc : CallOperator a p=∑ c : Fin 22,a c*jet H h p.1.val.val p.2 (finiteColumn ⟨c.val,by omega⟩) := by
    unfold CallOperator
    erw [operator_apply,tsum_fintype]
    rfl
  rw [hd,hc,tailFixedColumn_apply]
  simp only [show (22:Fin 23).val=22 from rfl,↓reduceIte]
  ring
lemma pairJJet_negative (a₁ a₂ : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (pairJJet a₁ a₂ 0 n) (pairJJet a₁ a₂ 1 n)=
      negativeJet v n d (inputJJet a₁ 0 0 n) (inputJJet a₁ 0 1 n)+
      negativeJet v n d (inputJJet a₂ 1 0 n) (inputJJet a₂ 1 1 n) := by
  exact negativeJet_add _ _ _ _ _ _ _
lemma actual_tail_negative {z : ℝ} (hz : 0<z) (hzB : z≤Z) (p : TailNode × Fin 2) :
    (negativeJet h p.1.val.val p.2
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 p.1.val.val)
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 p.1.val.val)).re=
        -gaussianTarget h z p.1.val.val p.2 ∧
    (negativeJet h p.1.val.val p.2
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 p.1.val.val)
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 p.1.val.val)).re=0 := by
  have h0 := congrArg (fun w : TailCoefficients => w p) (actualTail_full_equations_eu hz hzB).1
  have h1 := congrArg (fun w : TailCoefficients => w p) (actualTail_full_equations_eu hz hzB).2
  simp only [lp.coeFn_add,lp.coeFn_sub,lp.coeFn_smul,Pi.add_apply,Pi.sub_apply,
    Pi.smul_apply,smul_eq_mul] at h0 h1
  change _=_+_ -_ +gaussianTarget h z p.1.val.val p.2+(3/500)*tailFixedColumn 22 p at h0
  simp only [pairJJet_negative,add_re,actualInput,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte,
    inputJJet_tail_direct_negative,inputJJet_tail_transformed]
  constructor <;> linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_FiniteInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma Roperator_apply (u : FiniteCoefficients) (i : Fin 20) :
    Roperator u i=∑ j : Fin 20,R i j*u j := by
  unfold Roperator
  erw [operator_apply,tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _
lemma extendFiniteError_fixed (u : FiniteCoefficients) (i : Fin 2) :
    extendFiniteError u ⟨i.val,by omega⟩=0 := by
  change (if hi : i.val<2 then _ else _)=_
  simp only [i.isLt,↓reduceDIte]
lemma extendFiniteError_shift (u : FiniteCoefficients) (i : Fin 20) :
    extendFiniteError u ⟨i.val+2,by omega⟩=u i := by
  change (if hi : i.val+2<2 then 0 else u ⟨i.val+2-2,by omega⟩)=_
  simp only [show ¬(i.val+2<2) by omega,↓reduceDIte]
  congr 1
lemma extendFiniteError_transformed (u : FiniteCoefficients) (i : Fin 20) :
    (∑ c : Fin 22,extendFiniteError u c*jet H H (rowNode i).val (rowDerivative i)
      (finiteColumn ⟨c.val,by omega⟩))=Roperator u i := by
  have hh := finiteRow_sum 0 (extendFiniteError u) i
  have h0 : extendFiniteError u 0=0 := extendFiniteError_fixed u 0
  have h1 : extendFiniteError u 1=0 := extendFiniteError_fixed u 1
  erw [h0] at hh
  simp only [extendFiniteError_shift,zero_mul,zero_add,mul_zero,add_zero] at hh
  rw [hh,Roperator_apply]
lemma actualTrigonometric_shift (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (i : Fin 20) :
    actualTrigonometric side z hz hzB ⟨i.val+2,by omega⟩=
      (finiteSolution side *ᵥ actualParameter z) i+actualFiniteError side z hz hzB i := by
  change finiteApprox side (actualParameter z) _+extendFiniteError (actualFiniteError side z hz hzB) _=_
  rw [finiteApprox_shift,extendFiniteError_shift]
lemma actualInput_row_transformed (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i)
      (inputJJet (actualInput side z hz hzB) 1 0 (rowNode i).val)
      (inputJJet (actualInput side z hz hzB) 1 1 (rowNode i).val)).re=
      Boperator (actualTail side z hz hzB) i+Roperator (actualFiniteError side z hz hzB) i+
      (R *ᵥ (finiteSolution side *ᵥ actualParameter z)+R0 *ᵥ (gamma side *ᵥ actualParameter z)) i := by
  rw [actualInput,inputJJet_row_transformed]
  simp only [actualTrigonometric,lp.coeFn_add,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  rw [extendFiniteError_transformed]
  have hh := finiteApprox_transformed side (actualParameter z) i
  have hc : (gamma side *ᵥ actualParameter z) 2=if side.val=0 then -(3/500) else 3/500 := by
    rw [gamma_actual]
    rfl
  rw [hc] at hh
  simp only [Pi.add_apply] at hh
  linarith
lemma actual_finite_negative {z : ℝ} (hz : 0<z) (hzB : z≤Z) (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i)
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 (rowNode i).val)
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 (rowNode i).val)).re=
      -gaussianTarget H z (rowNode i).val (rowDerivative i) ∧
    (negativeJet H (rowNode i).val (rowDerivative i)
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 (rowNode i).val)
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 (rowNode i).val)).re=0 := by
  have h0 := congrArg (fun u : FiniteCoefficients => u i) (actualFiniteError_equations_eu hz hzB).1
  have h1 := congrArg (fun u : FiniteCoefficients => u i) (actualFiniteError_equations_eu hz hzB).2
  simp only [lp.coeFn_add,Pi.add_apply] at h0 h1
  have hf0 := congrArg (fun A : Matrix (Fin 20) (Fin 8) ℝ => (A *ᵥ actualParameter z) i) finiteSolution_equations_eu.1
  have hf1 := congrArg (fun A : Matrix (Fin 20) (Fin 8) ℝ => (A *ᵥ actualParameter z) i) finiteSolution_equations_eu.2
  simp only [Matrix.add_mulVec,←Matrix.mulVec_mulVec,Pi.add_apply] at hf0 hf1
  have hy := Yf_residual z i
  simp only [pairJJet_negative,add_re,actualInput_row_transformed,Pi.add_apply]
  have hd (side : Fin 2) :
      (negativeJet H (rowNode i).val (rowDerivative i)
        (inputJJet (actualInput side z hz hzB) 0 0 (rowNode i).val)
        (inputJJet (actualInput side z hz hzB) 0 1 (rowNode i).val)).re=
        -((finiteSolution side *ᵥ actualParameter z) i+actualFiniteError side z hz hzB i) := by
    rw [actualInput,inputJJet_row_direct_negative,actualTrigonometric_shift]
  simp only [hd]
  change _= -gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ ∧ _=0
  constructor <;> linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_ActualInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma gaussianG_deriv {z : ℝ} (hz : 0<z) (s : ℝ) :
    HasDerivAt (gaussianG z) (-Q 1*Real.exp ((1-s)/z)) s := by
  have hh := ((((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div_const z).exp.const_mul (Q 1*z))
  convert hh using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; field_simp; ring)
lemma negativeJet_gaussian {z : ℝ} (hz : 0<z) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (gaussianG z n:ℂ) ((deriv (gaussianG z) (n:ℝ):ℝ):ℂ)).re = -gaussianTarget v z n d := by
  rw [negativeJet_re,(gaussianG_deriv hz n).deriv]
  simp only [ofReal_re,gaussianG,gaussianTarget,Real.exp_add]
  split_ifs <;> ring
lemma negativeJet_injective (v : ℝ) (n : Node) (a b c d : ℂ)
    (h0 : (negativeJet v n.val 0 a b).re=(negativeJet v n.val 0 c d).re)
    (h1 : (negativeJet v n.val 1 a b).re=(negativeJet v n.val 1 c d).re) :
    a.re=c.re ∧ b.re=d.re := by
  simp only [negativeJet_re,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte] at h0 h1
  have hp : Real.exp (Real.pi*(v-h)*n.val)/Q n.val≠0 := div_ne_zero (Real.exp_ne_zero _) (Q_node_ne n)
  have ha : a.re=c.re := by
    have hh := mul_left_cancel₀ hp h0
    linarith
  have hb := mul_left_cancel₀ hp h1
  constructor
  · exact ha
  · rw [ha] at hb
    linarith
lemma finiteNode_surj {n : ℤ} (hn : n∈FiniteNodes) : ∃ i : Fin 10,finiteNode i=n := by
  have hall : ∀ n∈FiniteNodes,∃ i : Fin 10,finiteNode i=n := by decide +kernel
  exact hall n hn
lemma rowNode_cover (n : Node) (hn : n.val∈FiniteNodes) (d : Fin 2) :
    ∃ i : Fin 20,rowNode i=n ∧ rowDerivative i=d := by
  obtain ⟨j,hj⟩ := finiteNode_surj hn
  refine ⟨⟨2*j.val+d.val,by omega⟩,?_,?_⟩
  · apply Subtype.ext
    change finiteNode ⟨(2*j.val+d.val)/2,by omega⟩=n.val
    convert hj using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Fin.ext
    dsimp
    omega
  · apply Fin.ext
    change (2*j.val+d.val)%2=d.val
    omega
lemma actual_node_negative {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Node) :
    ∃ v : ℝ,∀ d : Fin 2,
      (negativeJet v n.val d
        (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 n.val)
        (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 n.val)).re= -gaussianTarget v z n.val d ∧
      (negativeJet v n.val d
        (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 n.val)
        (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 n.val)).re=0 := by
  by_cases hn : n.val∈FiniteNodes
  · refine ⟨H,?_⟩
    intro d
    obtain ⟨i,hi,hd⟩ := rowNode_cover n hn d
    have hh := actual_finite_negative hz hzB i
    simpa only [hi,hd] using hh
  · refine ⟨h,?_⟩
    intro d
    exact actual_tail_negative hz hzB (⟨n,hn⟩,d)
lemma actual_interpolation_eu_oai {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Node) :
    actualJ 0 z hz hzB n.val=gaussianG z n.val ∧ deriv (actualJ 0 z hz hzB) n.val=deriv (gaussianG z) n.val ∧
    actualJ 1 z hz hzB n.val=0 ∧ deriv (actualJ 1 z hz hzB) n.val=0 := by
  obtain ⟨v,hv⟩ := actual_node_negative hz hzB n
  have h0 := negativeJet_injective v n
    (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 n.val)
    (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 n.val)
    (gaussianG z n.val:ℂ) ((deriv (gaussianG z) (n.val:ℝ):ℝ):ℂ)
    ((hv 0).1.trans (negativeJet_gaussian hz v n.val 0).symm)
    ((hv 1).1.trans (negativeJet_gaussian hz v n.val 1).symm)
  have hn0 (d : Fin 2) : negativeJet v n.val d 0 0=0 := by simp [negativeJet]
  have h1 := negativeJet_injective v n
    (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 n.val)
    (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 n.val) 0 0
    (by simpa only [hn0,zero_re] using (hv 0).2) (by simpa only [hn0,zero_re] using (hv 1).2)
  have hd0 := ((hasDerivAt_pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 n.val).real_of_complex).deriv
  have hd1 := ((hasDerivAt_pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 n.val).real_of_complex).deriv
  change deriv (actualJ 0 z hz hzB) n.val=(pairJJet _ _ 1 n.val).re at hd0
  change deriv (actualJ 1 z hz hzB) n.val=(pairJJet _ _ 1 n.val).re at hd1
  exact ⟨h0.1,hd0.trans h0.2,h1.1,hd1.trans h1.2⟩
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.actual_interpolation_eu_oai := @OAI.AtomicTriangular.Construction.actual_interpolation_eu_oai
