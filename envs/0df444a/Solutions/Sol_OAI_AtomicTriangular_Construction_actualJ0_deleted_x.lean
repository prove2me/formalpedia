-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.actualJ0_deleted_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:35:32.498201+00:00
-- url     : https://prove2.me/submissions/d5e4a3f5-91d2-43b2-b47f-91c49c9c6c72

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X001
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X020
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualTail_norm_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualTrigonometric_norm_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_pairJ_curvature_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureTable01_mem_x

section
-- module Solutions.OAIQ250_TR.Compat
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

lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]

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

lemma curvatureWave_antitone (q br : Fin 2) {s u t : ℝ} (ht : |t|≤5/6) (hsu : s≤ u) :
    curvatureWave q br u t ≤ curvatureWave q br s t := by
  unfold curvatureWave
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsu (taylorPhase_re_nonpos q br ht))
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureConstant3_calc : (RI.sum (fun j : Fin 31 => (curvatureTable01 3 j).mul (columnNorm22 j))).divNat 2=curvatureConstant3 := by decide +kernel
lemma curvatureConstant3_bound : rawConstantCurvature (curvaturePoint 3) < (122/100000:ℝ) := by
  have hh := RI.mem_divNat (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable01_mem_x 3 j) (fourierNorm_mem j))) (by norm_num : 0<2)
  rw [curvatureConstant3_calc] at hh
  have hb := ri_mem_lt hh 122 100000 (by norm_num) (by decide +kernel)
  simpa only [rawConstantCurvature, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
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
lemma hasDerivAt_inputJJet (a : InputCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (inputJJet a br k) (inputJJet a br (k+1) s) s := by
  exact ((tailSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)).add
    ((finiteSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 1 br k s))
lemma hasDerivAt_pairJJet (a₁ a₂ : InputCoefficients) (k : ℕ) (s : ℂ) :
    HasDerivAt (pairJJet a₁ a₂ k) (pairJJet a₁ a₂ (k+1) s) s :=
  (hasDerivAt_inputJJet a₁ 0 k s).add (hasDerivAt_inputJJet a₂ 1 k s)
lemma pairJ_contDiff (a₁ a₂ : InputCoefficients) : ContDiff ℝ ⊤ (pairJ a₁ a₂) := by
  have hh : Differentiable ℂ (pairJJet a₁ a₂ 0) := fun s => (hasDerivAt_pairJJet a₁ a₂ 0 s).differentiableAt
  exact hh.contDiff.real_of_complex
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FarCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma hasDerivAt_spectralP_wave (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (fun t => spectralPCLM (waveFunctionJet 0 br k t))
      (spectralPCLM (waveFunctionJet 0 br (k+1) s)) s :=
  spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)
lemma transformedP_contDiff : ContDiff ℝ ⊤ transformedP := by
  exact (show Differentiable ℂ (fun s => spectralPCLM (waveFunctionJet 0 1 0 s)) from
    fun s => (hasDerivAt_spectralP_wave 1 0 s).differentiableAt).contDiff.real_of_complex
lemma transformedP_jet (k : ℕ) :
    (fun s : ℝ => (spectralPCLM (waveFunctionJet 0 1 k s)).re)=iteratedDeriv k transformedP := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,←hk]
    exact funext fun s => ((hasDerivAt_spectralP_wave 1 k s).real_of_complex).deriv.symm
lemma rawConstantCurvature_antitone {u s : ℝ} (hus : u ≤ s) :
    rawConstantCurvature s ≤ rawConstantCurvature u := by
  unfold rawConstantCurvature
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (curvatureWave_antitone 0 1 (abs_le.mpr (frequency_mem j)) hus) (norm_nonneg _)
lemma transformedP_curvature {s : ℝ} (hs : 29/2 ≤ s) :
    |iteratedDeriv 2 transformedP s|/2 ≤ 2/1000 := by
  rw [←transformedP_jet]
  have hh := abs_re_le_norm (spectralPCLM (waveFunctionJet 0 1 2 s))
  have hn := norm_sum_le (s:=Finset.univ) (fun j : Fin 31 => fourierCoeff j*(waveFunctionJet 0 1 2 (s:ℂ)) ⟨frequency j,frequency_mem j⟩)
  have he (j : Fin 31) :
      ‖fourierCoeff j*(waveFunctionJet 0 1 2 (s:ℂ)) ⟨frequency j,frequency_mem j⟩‖=
        curvatureWave 0 1 s (frequency j)*‖fourierCoeff j‖ := by
    rw [norm_mul,waveFunctionJet_apply,norm_finiteWaveJet_two]
    ring
  simp only [he] at hn
  change ‖spectralPCLM (waveFunctionJet 0 1 2 s)‖ ≤ _ at hn
  have hb := (rawConstantCurvature_antitone hs).trans curvatureConstant3_bound.le
  change rawConstantCurvature s ≤ 122/100000 at hb
  dsimp only [rawConstantCurvature] at hb
  nlinarith
lemma actualJ0_contDiff (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    ContDiff ℝ ⊤ (actualJ0 side z hz hzB) :=
  by
    change ContDiff ℝ ⊤ (fun s => _+sideConstant (otherSide side)*transformedP s)
    exact (pairJ_contDiff _ _).add (by simpa only [smul_eq_mul] using transformedP_contDiff.const_smul (sideConstant (otherSide side)))
lemma actualJ0_curvature (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (i : Fin 5) (hs : curvaturePoint i ≤ s) (hs14 : 29/2 ≤ s) :
    |iteratedDeriv 2 (actualJ0 side z hz hzB) s|/2 ≤
      (301/100)*finiteCurvatureEnvelope i+(3/1000000000)*tailCurvatureEnvelope i+(3/500)*(2/1000) := by
  let f := pairJ (coefficientInput 0 (actualTrigonometric side z hz hzB) (actualTail side z hz hzB))
    (coefficientInput 0 (actualTrigonometric (otherSide side) z hz hzB) (actualTail (otherSide side) z hz hzB))
  have hf : ContDiff ℝ 2 f := (pairJ_contDiff _ _).of_le (by norm_num)
  have hg : ContDiff ℝ 2 (sideConstant (otherSide side) • transformedP) := by
    change ContDiff ℝ 2 (fun s => sideConstant (otherSide side)*transformedP s)
    simpa only [smul_eq_mul] using (transformedP_contDiff.const_smul (sideConstant (otherSide side))).of_le (show (2:WithTop ℕ∞) ≤ ⊤ by exact le_top)
  have hl (side : Fin 2) : ‖actualTrigonometric side z hz hzB‖ ≤ 301/100 := by
    have hh := actualTrigonometric_norm_x side hz hzB
    linarith
  have ht (side : Fin 2) : ‖actualTail side z hz hzB‖ ≤ (3/1000000000:ℝ) := by
    simpa only [show (10:ℝ)^9=1000000000 by norm_num] using (actualTail_norm_x side hz hzB).le
  have hh := pairJ_curvature_x _ _ _ _ i hs (hl side) (hl (otherSide side)) (ht side) (ht (otherSide side))
  have hT := transformedP_curvature hs14
  change |iteratedDeriv 2 (f+sideConstant (otherSide side) • transformedP) s|/2 ≤ _
  rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt,iteratedDeriv_const_smul ((transformedP_contDiff.of_le (by norm_num)).contDiffAt)]
  simp only [smul_eq_mul]
  have hc : |sideConstant (otherSide side)|=(3/500:ℝ) := by unfold sideConstant; split_ifs <;> norm_num
  have ha := abs_add_le (iteratedDeriv 2 f s) (sideConstant (otherSide side)*iteratedDeriv 2 transformedP s)
  rw [abs_mul,hc] at ha
  change |iteratedDeriv 2 f s|/2 ≤ _ at hh
  nlinarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

lemma taylor_one_eval {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    taylorWithinEval f 1 (uIcc m s) m s=f m+deriv f m*(s-m) := by
  have he : iteratedDerivWithin 1 f (uIcc m s) m=iteratedDeriv 1 f m :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hms)
      (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc)
  rw [show (1:ℕ)=0+1 from rfl,taylorWithinEval_succ,he]
  simp [mul_comm]

lemma deletedSecond_eq_at_mean {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    ∃ c∈uIoo m s,deletedSecond f m s=iteratedDeriv 2 f c/2 := by
  obtain ⟨c,hc,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) hms hf.contDiffOn
  refine ⟨c,hc,?_⟩
  rw [taylor_one_eval hf hms] at he
  have hn : s-m≠0 := sub_ne_zero.mpr hms.symm
  rw [deletedSecond,ite_eq_right hms.symm]
  norm_num at he
  apply (div_eq_iff (pow_ne_zero 2 hn)).mpr
  linarith

lemma deletedSecond_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s C : ℝ}
    (hb : ∀ t∈uIcc m s,|iteratedDeriv 2 f t|≤C) : |deletedSecond f m s|≤C/2 := by
  by_cases h : m=s
  · subst s
    rw [deletedSecond,ite_eq_left rfl,abs_div,show |(2:ℝ)|=2 by norm_num]
    exact div_le_div_of_nonneg_right (hb m (left_mem_uIcc)) (by norm_num)
  · obtain ⟨c,hc,he⟩ := deletedSecond_eq_at_mean hf h
    rw [he,abs_div,show |(2:ℝ)|=2 by norm_num]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact hb c (Ioo_subset_Icc_self hc)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_FarSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma actualJ0_deleted_x_oai (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
    (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ)) :
    |deletedSecond (actualJ0 side z hz hzB) n.val s| ≤ farK i := by
  have hh := deletedSecond_bound ((actualJ0_contDiff side hz hzB).of_le (by norm_num))
    (m:=(n.val:ℝ)) (s:=s) (C:=2*farK i) (by
      intro t ht
      have hi : curvaturePoint i ≤ t := (le_min hm hs).trans ht.1
      have h14 : 29/2 ≤ t := (le_min hm14 hs14).trans ht.1
      have hc := actualJ0_curvature side hz hzB i hi h14
      change |iteratedDeriv 2 (actualJ0 side z hz hzB) t|/2 ≤ farK i at hc
      linarith)
  simpa using hh
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.actualJ0_deleted_x_oai := @OAI.AtomicTriangular.Construction.actualJ0_deleted_x_oai
