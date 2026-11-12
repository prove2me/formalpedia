-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.pairJ_curvature_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:18:24.470256+00:00
-- url     : https://prove2.me/submissions/d02e1773-0d03-4c63-b24a-dea08c1ea461

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X001
import Definitions.Def_OAIQ257X011
import Theorems.Thm_OAI_AtomicTriangular_Construction_finiteSpectral_curvature_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_tailCurvatureCap_sum_x

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
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma spectralCCLM_norm (n : Node) : ‖spectralCCLM n‖ ≤ cVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [cVariation, coeffAbs] <;> positivity) _
lemma spectralDCLM_norm (n : Node) : ‖spectralDCLM n‖ ≤ dVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [dVariation, coeffAbs] <;> positivity) _

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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_TailEnvelopeSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma frequencyDecay_pos (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    0 < frequencyDecay (damping q) (damping v) t := by
  have hx := Xwave_antitone (damping_pos q) (abs_nonneg t) ht
  have he : Xwave (damping q) |t|=Xwave (damping q) t := by simp [Xwave,waveDen,sq_abs]
  rw [he] at hx
  have hb : damping v < damping q * Xwave (damping q) (5/6) := by
    fin_cases q <;> fin_cases v <;> (first | (simp [damping,h,H,Xwave,waveDen]; all_goals first | (norm_num [damping,h,H,Xwave,waveDen]; done) | rfl | decide) | (norm_num [damping,h,H,Xwave,waveDen]; done) | norm_num [damping,h,H,Xwave,waveDen])
  unfold frequencyDecay
  exact mul_pos Real.pi_pos (sub_pos.mpr (hb.trans_le (mul_le_mul_of_nonneg_left hx (damping_pos q).le)))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds

lemma tail_pairs_norm (w : TailCoefficients) :
    (∑' n, (|w (n,0)| + |w (n,1)|))=‖w‖ := by
  rw [l1_norm]
  symm
  calc
    (∑' p, |w p|) = ∑' n : TailNode, ∑' d : Fin 2, |w (n,d)| := (l1_summable w).tsum_prod
    _ = _ := by simp only [tsum_fintype,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
                rfl

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_AtomicCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.Envelope
open Real Set

lemma linear_sqrt_exp_hasDerivAt {a b δ x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y : ℝ => (a+b*y)*sqrt y*exp (-δ*y))
      ((b*sqrt x+(a+b*x)/(2*sqrt x)-δ*((a+b*x)*sqrt x))*exp (-δ*x)) x := by
  have hd := (((hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul b)).mul
    (hasDerivAt_sqrt (ne_of_gt hx))).mul
    (((hasDerivAt_id x).const_mul (-δ)).exp)
  convert hd using 1 <;> first | rfl | (dsimp; ring)

lemma linear_sqrt_exp_antitone {a b δ x y : ℝ} (hx : 0<x) (hxy : x≤y)
    (ha : 0≤a) (hb : 0≤b) (hδ : 3/2≤δ*x) :
    (a+b*y)*sqrt y*exp (-δ*y) ≤ (a+b*x)*sqrt x*exp (-δ*x) := by
  have hδ0 : 0<δ := by nlinarith
  have hanti : AntitoneOn (fun u : ℝ => (a+b*u)*sqrt u*exp (-δ*u)) (Ici x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici x)
    · exact (by fun_prop : ContinuousOn (fun u : ℝ => (a+b*u)*sqrt u*exp (-δ*u)) (Ici x))
    · intro u hu
      exact (linear_sqrt_exp_hasDerivAt (a:=a) (b:=b) (δ:=δ) (hx.trans_le (mem_Ici.mp (interior_subset hu)))).differentiableAt.differentiableWithinAt
    · intro u hu
      have hux : x≤u := mem_Ici.mp (interior_subset hu)
      have hu0 := hx.trans_le hux
      rw [(linear_sqrt_exp_hasDerivAt (a:=a) (b:=b) (δ:=δ) hu0).deriv]
      apply mul_nonpos_of_nonpos_of_nonneg _ (exp_pos _).le
      have hs := sq_sqrt hu0.le
      have hsp : 0 < sqrt u := sqrt_pos.mpr hu0
      have hδu : 3/2≤δ*u := hδ.trans (mul_le_mul_of_nonneg_left hux hδ0.le)
      apply nonpos_of_mul_nonpos_left (b:=2*sqrt u) _ (by positivity)
      have he : (b*sqrt u+(a+b*u)/(2*sqrt u)-δ*((a+b*u)*sqrt u))*(2*sqrt u) =
          a+3*b*u-2*δ*u*(a+b*u) := by
        field_simp
        rw [hs]
        ring
      rw [he]
      have h1 := mul_nonneg (show 0≤2*δ*u-1 by linarith) ha
      have h2 := mul_nonneg (show 0≤2*δ*u-3 by linarith) (mul_nonneg hb hu0.le)
      nlinarith
  exact hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hxy) hxy
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma taylorPhase_re_nonpos (q br : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    (taylorPhase q br t).re≤0 := by
  fin_cases br
  · simp only [taylorPhase,↓reduceIte,sub_re,mul_re,mul_im,I_re,I_im,
      ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,zero_sub]
    have hh : h≤damping q := by fin_cases q <;> (first | (simp [damping,h,H]; all_goals first | (norm_num [damping,h,H]; done) | rfl | decide) | (norm_num [damping,h,H]; done) | norm_num [damping,h,H])
    exact neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh))
  · change (I*Real.pi*zeta (damping q) h t).re≤0
    rw [wavePhase_re]
    have hh := (frequencyDecay_pos q 0 ht).le
    change 0≤Real.pi*(damping q*Xwave (damping q) t-h) at hh
    nlinarith

lemma curvatureWave_nonneg (q br : Fin 2) (s t : ℝ) : 0 ≤ curvatureWave q br s t := by
  unfold curvatureWave; positivity
lemma curvatureWave_antitone (q br : Fin 2) {s u t : ℝ} (ht : |t|≤5/6) (hsu : s≤ u) :
    curvatureWave q br u t ≤ curvatureWave q br s t := by
  unfold curvatureWave
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsu (taylorPhase_re_nonpos q br ht))
lemma curvatureWave_direct (q : Fin 2) (s t : ℝ) :
    curvatureWave q 0 s t = Real.pi^2*(t^2+(damping q-h)^2)*Real.exp (-Real.pi*(damping q-h)*s) := by
  unfold curvatureWave
  rw [←Complex.normSq_eq_norm_sq]
  simp only [taylorPhase,taylorAmplitude,Fin.val_zero,↓reduceIte,norm_one,mul_one,
    Complex.normSq_apply,sub_re,sub_im,mul_re,mul_im,ofReal_re,ofReal_im,I_re,I_im,
    zero_mul,mul_zero,one_mul,sub_zero,zero_sub,zero_add]
  ring_nf
lemma curvatureWave_transformed (q : Fin 2) (s t : ℝ) :
    curvatureWave q 1 s t = Real.pi^2*(h^2+(4/3-2*damping q*h)*Xwave (damping q) t)*
      Real.sqrt (Xwave (damping q) t)*Real.exp (-Real.pi*(damping q*Xwave (damping q) t-h)*s) := by
  simp only [curvatureWave,taylorPhase,taylorAmplitude,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  rw [norm_wavePhase (damping_pos q),norm_lambda (damping_pos q),wavePhase_re,mul_pow,
    Real.sq_sqrt]
  rw [←normSq_zeta (damping_pos q)]
  exact normSq_nonneg _
lemma curvatureWave_even (q br : Fin 2) (s t : ℝ) :
    curvatureWave q br s (-t)=curvatureWave q br s t := by
  fin_cases br
  · simp [curvatureWave_direct]
  · simp [curvatureWave_transformed,Xwave,waveDen]
lemma curvatureWave_abs (q br : Fin 2) (s t : ℝ) :
    curvatureWave q br s |t|=curvatureWave q br s t := by
  rcases le_total 0 t with ht|ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht,curvatureWave_even]
lemma curvature_tail_direct {s t : ℝ} (ht : |t|≤5/6) :
    curvatureWave 0 0 s t ≤ curvatureWave 0 0 s (5/6) := by
  rw [curvatureWave_direct,curvatureWave_direct]
  norm_num [damping]
  have hh : t^2≤(5/6:ℝ)^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by norm_num)).mpr ht
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hh)]
lemma curvature_tail_zero {t : ℝ} (_ht : |t|≤5/6) :
    curvatureWave 0 1 0 t ≤ curvatureWave 0 1 0 0 := by
  rw [curvatureWave_transformed,curvatureWave_transformed]
  simp only [mul_zero,Real.exp_zero,mul_one]
  have hx : Xwave (damping 0) t≤Xwave (damping 0) 0 := by
    rw [←show Xwave (damping 0) |t|=Xwave (damping 0) t by simp [Xwave,waveDen]]
    exact Xwave_antitone (damping_pos 0) le_rfl (abs_nonneg t)
  have h1 : 0≤4/3-2*damping 0*h := by norm_num [damping,h]
  apply mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hx h1) _) (sq_nonneg _)) (Real.sqrt_le_sqrt hx) (Real.sqrt_nonneg _)
  exact mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (mul_nonneg h1 (Xwave_pos (damping_pos 0) 0).le))
lemma curvature_tail_positive {s t : ℝ} (hs : 1 ≤ s) (ht : |t| ≤ 5/6) :
    curvatureWave 0 1 s t ≤ curvatureWave 0 1 s (5/6) := by
  rw [←curvatureWave_abs 0 1 s t]
  rw [curvatureWave_transformed,curvatureWave_transformed]
  have hx := Xwave_pos (damping_pos 0) (5/6)
  have hxy := Xwave_antitone (damping_pos 0) (abs_nonneg t) ht
  have hbase : (3/2:ℝ)≤Real.pi*h*Xwave h (5/6) := by
    have hp := Real.pi_gt_three
    norm_num [Xwave,waveDen,h] at *
    linarith
  have hb : (3/2:ℝ)≤(Real.pi*damping 0*s)*Xwave (damping 0) (5/6) := by
    change (3/2:ℝ)≤(Real.pi*h*s)*Xwave h (5/6)
    have hh : 0 ≤ h := by norm_num [h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg Real.pi_pos.le (mul_nonneg hh hx.le))]
  have hh := Envelope.linear_sqrt_exp_antitone hx hxy (sq_nonneg h)
    (show 0≤4/3-2*damping 0*h by norm_num [damping,h]) hb
  have he (x : ℝ) : Real.exp (-Real.pi*(damping 0*x-h)*s) =
      Real.exp (Real.pi*h*s)*Real.exp (-(Real.pi*damping 0*s)*x) := by
    rw [←Real.exp_add]; congr 1; ring
  rw [he,he]
  convert mul_le_mul_of_nonneg_left hh (show 0≤Real.pi^2*Real.exp (Real.pi*h*s) by positivity) using 1 <;> first | rfl | ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_VariationBound
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
-- module Solutions.OAIQ250_TR.Triangular_Taylor_WaveFunction
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

lemma norm_finiteWaveJet_two (q br : Fin 2) (s t : ℝ) :
    ‖finiteWaveJet q br t 2 s‖=curvatureWave q br s t := by
  simp only [finiteWaveJet,norm_mul,norm_pow,Complex.norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero,curvatureWave]
  ring
lemma waveFunctionJet_uniform (q br : Fin 2) (s : ℝ) {M : ℝ} (hM : 0≤M)
    (hb : ∀ t : ℝ, |t|≤5/6 → curvatureWave q br s t≤M) :
    ‖waveFunctionJet q br 2 s‖≤M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro t
  rw [waveFunctionJet_apply,norm_finiteWaveJet_two]
  exact hb t.val (abs_le.mpr t.property)

lemma hasDerivAt_inputJJet (a : InputCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (inputJJet a br k) (inputJJet a br (k+1) s) s := by
  exact ((tailSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)).add
    ((finiteSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 1 br k s))
lemma hasDerivAt_pairJJet (a₁ a₂ : InputCoefficients) (k : ℕ) (s : ℂ) :
    HasDerivAt (pairJJet a₁ a₂ k) (pairJJet a₁ a₂ (k+1) s) s :=
  (hasDerivAt_inputJJet a₁ 0 k s).add (hasDerivAt_inputJJet a₂ 1 k s)
lemma pairJJet_iterated (a₁ a₂ : InputCoefficients) (k : ℕ) :
    (fun s : ℝ => (pairJJet a₁ a₂ k s).re)=iteratedDeriv k (pairJ a₁ a₂) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,←hk]
    exact funext fun s => ((hasDerivAt_pairJJet a₁ a₂ k s).real_of_complex).deriv.symm
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CoefficientSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma complex_smul_clm_bound (r : ℝ) (T : C(Spectrum,ℂ) →L[ℂ] ℂ) :
    ‖(r:ℂ) • T‖ ≤ |r| * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg r) (norm_nonneg T))
  intro f
  change ‖(r:ℂ) * T f‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
  exact mul_le_mul_of_nonneg_left (T.le_opNorm f) (abs_nonneg r)
lemma tail_pair_norm119 (n : Node) (u v : ℝ) :
    ‖(u:ℂ) • spectralCCLM n+(v:ℂ) • spectralDCLM n‖ ≤ 119*(|u|+|v|) := by
  have h0 := (spectralCCLM_norm n).trans cVariation_lt.le
  have h1 := (spectralDCLM_norm n).trans dVariation_lt.le
  have hsum := norm_add_le ((u:ℂ) • spectralCCLM n) ((v:ℂ) • spectralDCLM n)
  have hsm := add_le_add (complex_smul_clm_bound u (spectralCCLM n))
    (complex_smul_clm_bound v (spectralDCLM n))
  have hh : ‖(u:ℂ) • spectralCCLM n+(v:ℂ) • spectralDCLM n‖ ≤
      |u| * ‖spectralCCLM n‖+|v| * ‖spectralDCLM n‖ := by
    exact hsum.trans hsm
  nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg u),mul_le_mul_of_nonneg_left h1 (abs_nonneg v)]
lemma norm_series_bound {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (g : ι → E) (v : ι → ℝ) (hv : Summable v) (M : ℝ)
    (hb : ∀ i, ‖g i‖≤M*v i) : ‖∑' i, g i‖≤M*∑' i,v i := by
  have hs : Summable (fun i => ‖g i‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hv.mul_left M)
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hb (hv.mul_left M)).trans_eq (tsum_mul_left))
lemma tailSeries_norm (w : TailCoefficients) :
    ‖∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val)‖ ≤ 119*‖w‖ := by
  have hh := norm_series_bound (fun n : TailNode => (w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val)
    (fun n => |w (n,0)|+|w (n,1)|) (tail_pairs_summable w) 119
    (fun n => tail_pair_norm119 n.val (w (n,0)) (w (n,1)))
  rw [tail_pairs_norm] at hh
  exact hh
lemma tailSpectral_zero_constant (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput 0 a w)=
      ∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val) := by
  have hz : (0:ℂ) • spectralPCLM=(0:C(Spectrum,ℂ) →L[ℂ] ℂ) := by
    ext f
    change (0:ℂ)*_=0
    exact zero_mul _
  change (0:ℂ) • spectralPCLM+_= _
  rw [hz,zero_add]
  rfl
lemma tailSpectral_zero_constant_norm (a : TrigonometricCoefficients) (w : TailCoefficients) :
    ‖tailSpectral (coefficientInput 0 a w)‖ ≤ 119*‖w‖ := by
  rw [tailSpectral_zero_constant]
  exact tailSeries_norm w
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

lemma finiteCurvatureCap_sum (i : Fin 5) :
    (finiteCurvatureCap 0 i+finiteCurvatureCap 1 i)/2≤finiteCurvatureEnvelope i := by
  fin_cases i <;> (first | (simp [finiteCurvatureCap,finiteCurvatureEnvelope]; all_goals first | (norm_num [finiteCurvatureCap,finiteCurvatureEnvelope]; done) | rfl | decide) | (norm_num [finiteCurvatureCap,finiteCurvatureEnvelope]; done) | norm_num [finiteCurvatureCap,finiteCurvatureEnvelope])
lemma finiteCurvatureCap_nonneg (br : Fin 2) (i : Fin 5) : 0≤finiteCurvatureCap br i := by
  fin_cases br <;> fin_cases i <;> (first | (simp [finiteCurvatureCap]; all_goals first | (norm_num [finiteCurvatureCap]; done) | rfl | decide) | (norm_num [finiteCurvatureCap]; done) | norm_num [finiteCurvatureCap])
lemma tailCurvatureCap_nonneg (br : Fin 2) (i : Fin 5) : 0≤tailCurvatureCap br i := curvatureWave_nonneg _ _ _ _
lemma tailCurvatureCap_bound (br : Fin 2) (i : Fin 5) {s t : ℝ}
    (hs : curvaturePoint i≤ s) (ht : |t|≤5/6) : curvatureWave 0 br s t≤tailCurvatureCap br i := by
  apply (curvatureWave_antitone 0 br ht hs).trans
  fin_cases br
  · exact curvature_tail_direct ht
  · by_cases hi : i=0
    · subst i
      exact curvature_tail_zero ht
    · have hu : 1 ≤ curvaturePoint i := by fin_cases i <;> (first | (simp [curvaturePoint] at *; all_goals first | (norm_num [curvaturePoint] at *; done) | rfl | decide) | (norm_num [curvaturePoint] at *; done) | norm_num [curvaturePoint] at *)
      have hval : ¬i.val=0 := by simpa only [Fin.val_eq_zero_iff] using hi
      simp only [tailCurvatureCap,true_and,hval,↓reduceIte]
      convert curvature_tail_positive hu ht using 1 <;> rfl
lemma tailSpectral_curvature (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (i : Fin 5) {s : ℝ} (hs : curvaturePoint i≤ s) :
    ‖tailSpectral (coefficientInput 0 a w) (waveFunctionJet 0 br 2 s)‖≤119*‖w‖*tailCurvatureCap br i := by
  exact ((tailSpectral _).le_opNorm _).trans (mul_le_mul (tailSpectral_zero_constant_norm a w)
    (waveFunctionJet_uniform _ _ _ (tailCurvatureCap_nonneg br i) (fun t ht => tailCurvatureCap_bound br i hs ht))
    (norm_nonneg _) (by positivity))
lemma pairJ_curvature_x_oai (a b : TrigonometricCoefficients) (w v : TailCoefficients)
    (i : Fin 5) {s aL aT : ℝ} (hs : curvaturePoint i≤ s)
    (ha : ‖a‖≤aL) (hb : ‖b‖≤aL) (hw : ‖w‖≤aT) (hv : ‖v‖≤aT) :
    |iteratedDeriv 2 (pairJ (coefficientInput 0 a w) (coefficientInput 0 b v)) s|/2≤
      aL*finiteCurvatureEnvelope i+aT*tailCurvatureEnvelope i := by
  rw [←pairJJet_iterated]
  have hTa := tailSpectral_curvature a w 0 i hs
  have hTb := tailSpectral_curvature b v 1 i hs
  have hLa := finiteSpectral_curvature_x 0 a w 0 i hs
  have hLb := finiteSpectral_curvature_x 0 b v 1 i hs
  have hh := Complex.abs_re_le_norm (pairJJet (coefficientInput 0 a w) (coefficientInput 0 b v) 2 s)
  have hN := norm_add_le (inputJJet (coefficientInput 0 a w) 0 2 s) (inputJJet (coefficientInput 0 b v) 1 2 s)
  have hNa := norm_add_le (tailSpectral (coefficientInput 0 a w) (waveFunctionJet 0 0 2 s)) (finiteSpectral (coefficientInput 0 a w) (waveFunctionJet 1 0 2 s))
  have hNb := norm_add_le (tailSpectral (coefficientInput 0 b v) (waveFunctionJet 0 1 2 s)) (finiteSpectral (coefficientInput 0 b v) (waveFunctionJet 1 1 2 s))
  have hL0 := mul_le_mul_of_nonneg_right ha (finiteCurvatureCap_nonneg 0 i)
  have hL1 := mul_le_mul_of_nonneg_right hb (finiteCurvatureCap_nonneg 1 i)
  have hT0 := mul_le_mul_of_nonneg_right hw (tailCurvatureCap_nonneg 0 i)
  have hT1 := mul_le_mul_of_nonneg_right hv (tailCurvatureCap_nonneg 1 i)
  have hLf := mul_le_mul_of_nonneg_left (finiteCurvatureCap_sum i) ((norm_nonneg a).trans ha)
  have hTf := mul_le_mul_of_nonneg_left (tailCurvatureCap_sum_x i) ((norm_nonneg w).trans hw)
  change |(pairJJet _ _ 2 s).re|/2≤_
  dsimp only [pairJJet,inputJJet] at hh hN ⊢
  nlinarith
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.pairJ_curvature_x_oai := @OAI.AtomicTriangular.Construction.pairJ_curvature_x_oai
