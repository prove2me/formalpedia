-- Prove2me | solution 1 for MTT.Cohomology.mixed_period_test_functions_local_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-08T11:13:04.319103+00:00
-- url     : https://prove2.me/submissions/dc1ac243-49a0-4790-bc65-7bb08427116b

import Definitions.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Analysis.Complex.CauchyIntegral


set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
namespace MTT.LocalPeriod
open MTT.Cohomology

-- Coefficient identities adapted from Chris Birkbeck's accepted
-- period_pairing_petersson_definite proof (777707bf-f8aa-4fd9-8d82-71afe645b027).
lemma binaryExponent_apply (n j : ℕ) (i : Fin 2) :
    binaryExponent n j i = if i = 0 then j else n - j := by
  simp [binaryExponent]

lemma single_add_single_eq (n j : ℕ) :
    Finsupp.single (0 : Fin 2) j + Finsupp.single 1 (n - j) = binaryExponent n j := by
  ext i
  fin_cases i <;> simp [binaryExponent_apply]

lemma coeff_periodPower (n j : ℕ) (hj : j ≤ n) (z : ℂ) :
    MvPolynomial.coeff (binaryExponent n j) (periodPower n z) = (n.choose j : ℂ) * z ^ j := by
  unfold periodPower
  rw [add_pow, MvPolynomial.coeff_sum]
  have key : ∀ m ∈ Finset.range (n + 1),
      MvPolynomial.coeff (binaryExponent n j)
        ((MvPolynomial.C z * MvPolynomial.X 0) ^ m * MvPolynomial.X 1 ^ (n - m) *
          (n.choose m : MvPolynomial (Fin 2) ℂ))
        = if m = j then (n.choose j : ℂ) * z ^ j else 0 := by
    intro m _
    have hmono : (MvPolynomial.C z * MvPolynomial.X 0) ^ m * MvPolynomial.X 1 ^ (n - m) *
          (n.choose m : MvPolynomial (Fin 2) ℂ)
        = MvPolynomial.monomial (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 (n - m))
            ((n.choose m : ℂ) * z ^ m) := by
      rw [mul_pow, ← MvPolynomial.C_pow, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.X_pow_eq_monomial, ← map_natCast MvPolynomial.C (n.choose m),
        MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul,
        mul_comm (MvPolynomial.monomial _ _) (MvPolynomial.C _), MvPolynomial.C_mul_monomial]
      congr 1
      ring
    rw [hmono, MvPolynomial.coeff_monomial]
    by_cases hmj : m = j
    · subst hmj
      rw [if_pos (single_add_single_eq n m), if_pos rfl]
    · have hne : Finsupp.single (0 : Fin 2) m + Finsupp.single 1 (n - m) ≠ binaryExponent n j := by
        intro h
        apply hmj
        have := DFunLike.congr_fun h 0
        simpa [binaryExponent_apply] using this
      rw [if_neg hne, if_neg hmj]
  rw [Finset.sum_congr rfl key]
  simp [Finset.sum_ite_eq', Nat.lt_succ_of_le hj]

lemma periodContraction_smul_smul (n : ℕ) (a b : ℂ) (P Q : Binary ℂ) :
    periodContraction n (a • P) (b • Q) = a * b * periodContraction n P Q := by
  unfold periodContraction
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

lemma periodContraction_periodPower (n : ℕ) (z w : ℂ) :
    periodContraction n (periodPower n z) (periodPower n w) = (z - w) ^ n := by
  unfold periodContraction
  rw [sub_eq_add_neg, add_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hj' : j ≤ n := by omega
  rw [coeff_periodPower n j hj' z, coeff_periodPower n (n - j) (Nat.sub_le n j) w,
    Nat.choose_symm hj']
  have hc : (n.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  rw [neg_pow]
  field_simp
  ring


lemma differential_apply (a b w : ℂ) : periodDifferential a b w = a * w + b * conj w := by
  simp [periodDifferential]

lemma mixed_mul {F G : ℂ → ℂ} {a b c d z : ℂ}
    (hF : HasFDerivAt F (periodDifferential a b) z)
    (hG : HasFDerivAt G (periodDifferential c d) z) :
    HasFDerivAt (fun w => F w * G w)
      (periodDifferential (a * G z + F z * c) (b * G z + F z * d)) z := by
  convert! hF.mul hG using 1
  ext w
  simp [differential_apply]
  ring

lemma mixed_conj {F : ℂ → ℂ} {a b z : ℂ}
    (hF : HasFDerivAt F (periodDifferential a b) z) :
    HasFDerivAt (fun w => conj (F w)) (periodDifferential (conj b) (conj a)) z := by
  convert! Complex.conjCLE.hasFDerivAt.comp z hF using 1
  ext w
  simp [differential_apply]
  ring

lemma mixed_of_complex {F : ℂ → ℂ} {a z : ℂ} (hF : HasDerivAt F a z) :
    HasFDerivAt F (periodDifferential a 0) z := by
  convert! hF.hasFDerivAt.restrictScalars ℝ using 1
  ext w
  simp [periodDifferential, mul_comm]

lemma mixed_wirtinger {F : ℂ → ℂ} {a b z : ℂ}
    (hF : HasFDerivAt F (periodDifferential a b) z) :
    (1 / 2 : ℂ) * (fderiv ℝ F z 1 - Complex.I * fderiv ℝ F z Complex.I) = a := by
  rw [hF.fderiv]
  simp [differential_apply]
  ring_nf
  simp
  ring

lemma coeff_cusp_holomorphic {N k : ℕ}
    (q : CuspForm (MTT.GammaOne N) (k : ℤ)) (n j : ℕ) (hj : j ≤ n) :
    DifferentiableOn ℂ (fun w : ℂ =>
      MvPolynomial.coeff (binaryExponent n j) (((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower n w))
      upperHalfPlaneSet := by
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, coeff_periodPower n j hj]
  exact (UpperHalfPlane.mdifferentiable_iff.mp q.holo').mul
    ((differentiableOn_const (c := (n.choose j : ℂ))).mul (differentiableOn_id.pow j))

lemma coeff_conj_cusp {N k : ℕ}
    (q : CuspForm (MTT.GammaOne N) (k : ℤ)) (n j : ℕ) (hj : j ≤ n) (w : ℂ) :
    MvPolynomial.coeff (binaryExponent n j)
      (conj ((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower n (conj w)) =
    conj (MvPolynomial.coeff (binaryExponent n j)
      (((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower n w)) := by
  simp [MvPolynomial.coeff_smul, coeff_periodPower n j hj]


lemma coeff_primitive_contDiff {N k : ℕ}
    (g v : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U)
    (j : ℕ) (hj : j ≤ k - 2) :
    ContDiffOn ℝ 1 (fun w => MvPolynomial.coeff (binaryExponent (k - 2) j) (U w))
      upperHalfPlaneSet := by
  let e := binaryExponent (k - 2) j
  let a := fun w : ℂ => MvPolynomial.coeff e
    (((↑ₕ(fun τ : ℍ => g τ)) w) • periodPower (k - 2) w)
  let b := fun w : ℂ => -MvPolynomial.coeff e
    (conj ((↑ₕ(fun τ : ℍ => v τ)) w) • periodPower (k - 2) (conj w))
  have ha : ContinuousOn a upperHalfPlaneSet :=
    (coeff_cusp_holomorphic g (k - 2) j hj).continuousOn
  have hb : ContinuousOn b upperHalfPlaneSet := by
    have hv := (Complex.conjCLE.continuous.comp_continuousOn
      (coeff_cusp_holomorphic v (k - 2) j hj).continuousOn).neg
    simp only [b, e, coeff_conj_cusp v (k - 2) j hj]
    convert! hv using 1
  rw [show (1 : WithTop ENat) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn isOpen_upperHalfPlaneSet.uniqueDiffOn]
  refine ⟨by simp, (fun w => periodDifferential (a w) (b w)), ?_, ?_⟩
  · rw [contDiffOn_zero]
    exact (ha.smul continuousOn_const).add (hb.smul continuousOn_const)
  · intro w hw
    have he : UpperHalfPlane.ofComplex w = ⟨w, hw⟩ := by
      exact (UpperHalfPlane.ofComplex_apply ⟨w, hw⟩)
    simpa [a, b, e, he] using
      (hU.2.2.1 ⟨w, hw⟩ e).hasFDerivWithinAt (s := upperHalfPlaneSet)


lemma mixed_const_mul {F : ℂ → ℂ} {a b z : ℂ} (c : ℂ)
    (hF : HasFDerivAt F (periodDifferential a b) z) :
    HasFDerivAt (fun w => c * F w) (periodDifferential (c * a) (c * b)) z := by
  convert! hF.const_mul c using 1
  ext w
  simp [differential_apply]
  ring

lemma mixed_sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℂ} {a b : ι → ℂ} {z : ℂ}
    (hF : ∀ i ∈ s, HasFDerivAt (F i) (periodDifferential (a i) (b i)) z) :
    HasFDerivAt (fun w => ∑ i ∈ s, F i w)
      (periodDifferential (∑ i ∈ s, a i) (∑ i ∈ s, b i)) z := by
  convert! HasFDerivAt.fun_sum hF using 1
  ext w
  simp [differential_apply, Finset.sum_add_distrib, Finset.sum_mul]

lemma coeff_cusp_contDiff {N k : ℕ}
    (q : CuspForm (MTT.GammaOne N) (k : ℤ)) (n j : ℕ) (hj : j ≤ n) :
    ContDiffOn ℝ 1 (fun w : ℂ =>
      MvPolynomial.coeff (binaryExponent n j) (((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower n w))
      upperHalfPlaneSet := by
  exact ((coeff_cusp_holomorphic q n j hj).contDiffOn
    isOpen_upperHalfPlaneSet).restrict_scalars ℝ

lemma first_test_contDiff {N k : ℕ}
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    ContDiffOn ℝ 1 (fun z : ℂ =>
      periodContraction (k - 2) (U z)
        (conj ((↑ₕ(fun τ : ℍ => q τ)) z) • periodPower (k - 2) (conj z)))
      upperHalfPlaneSet := by
  unfold periodContraction
  apply ContDiffOn.sum
  intro j hj
  have hj' : j ≤ k - 2 := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [coeff_conj_cusp q (k - 2) (k - 2 - j) (Nat.sub_le _ _)]
  exact ((contDiffOn_const.mul (coeff_primitive_contDiff g v U hU j hj')).mul
    (Complex.conjCLE.contDiff.comp_contDiffOn
      (coeff_cusp_contDiff q (k - 2) (k - 2 - j) (Nat.sub_le _ _)))).div_const _

lemma second_test_contDiff {N k : ℕ}
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    ContDiffOn ℝ 1 (fun z : ℂ => conj <|
      periodContraction (k - 2)
        (((↑ₕ(fun τ : ℍ => q τ)) z) • periodPower (k - 2) z) (U z))
      upperHalfPlaneSet := by
  apply Complex.conjCLE.contDiff.comp_contDiffOn
  unfold periodContraction
  apply ContDiffOn.sum
  intro j hj
  have hj' : j ≤ k - 2 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  exact ((contDiffOn_const.mul (coeff_cusp_contDiff q (k - 2) j hj')).mul
    (coeff_primitive_contDiff g v U hU (k - 2 - j) (Nat.sub_le _ _))).div_const _

end MTT.LocalPeriod


set_option autoImplicit false
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups Modular ComplexConjugate
namespace MTT.LocalPeriod
open MTT.Cohomology

lemma exponent_eq_of_coeff_ne_zero {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) {e : Fin 2 →₀ ℕ}
    (he : MvPolynomial.coeff e P ≠ 0) : binaryExponent n (e 0) = e := by
  have hd := (show P.IsHomogeneous n from hP).degree_eq_sum_deg_support
    (MvPolynomial.mem_support_iff.mpr he)
  have hs : e 0 + e 1 = n := by
    have hd' : e.sum (fun _ m => m) = n := hd.symm
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hd'
  ext i
  fin_cases i <;> simp [binaryExponent_apply, ← hs]

lemma homogeneous_expansion {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) :
    P = ∑ j ∈ Finset.range (n + 1),
      MvPolynomial.monomial (binaryExponent n j) (MvPolynomial.coeff (binaryExponent n j) P) := by
  ext e
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (e 0)]
  · rw [MvPolynomial.coeff_monomial]
    split_ifs with he
    · rw [he]
    · have hc : MvPolynomial.coeff e P = 0 := by
        by_contra hc
        exact he (exponent_eq_of_coeff_ne_zero hP hc)
      exact hc
  · intro j hj hje
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro he
    apply hje
    simpa [binaryExponent_apply] using DFunLike.congr_fun he 0
  · intro hj
    rw [MvPolynomial.coeff_monomial]
    split_ifs with he
    · have hn : n < e 0 := Nat.lt_of_not_ge (by simpa using hj)
      have hc : MvPolynomial.coeff e P = 0 := by
        by_contra hc
        have hd := (show P.IsHomogeneous n from hP).degree_eq_sum_deg_support
          (MvPolynomial.mem_support_iff.mpr hc)
        have hs : e 0 + e 1 = n := by
          have hd' : e.sum (fun _ m => m) = n := hd.symm
          simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hd'
        omega
      simpa [he] using hc
    · rfl

lemma eval_homogeneous {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (x y : ℂ) :
    MvPolynomial.eval ![x,y] P = ∑ j ∈ Finset.range (n + 1),
      MvPolynomial.coeff (binaryExponent n j) P * x ^ j * y ^ (n - j) := by
  conv_lhs => rw [homogeneous_expansion hP]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MvPolynomial.eval_monomial]
  simp [Finsupp.prod_fintype, Fin.prod_univ_two, binaryExponent_apply, mul_assoc]

lemma contraction_pure_right (n : ℕ) (P : Binary ℂ) (w : ℂ) :
    periodContraction n P (periodPower n w) =
      ∑ j ∈ Finset.range (n + 1),
        MvPolynomial.coeff (binaryExponent n j) P * (-w) ^ (n - j) := by
  unfold periodContraction
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [coeff_periodPower n (n - j) (Nat.sub_le _ _) w, Nat.choose_symm hj']
  have hc : (n.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  field_simp
  ring

lemma contraction_eval {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (w : ℂ) :
    periodContraction n P (periodPower n w) = MvPolynomial.eval ![1,-w] P := by
  rw [contraction_pure_right, eval_homogeneous hP]
  simp

lemma eval_homogeneous_scale {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (x y c : ℂ) :
    MvPolynomial.eval ![c * x, c * y] P = c ^ n * MvPolynomial.eval ![x,y] P := by
  rw [eval_homogeneous hP, eval_homogeneous hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hc : c ^ n = c ^ j * c ^ (n - j) := by rw [← pow_add, Nat.add_sub_of_le hj']
  rw [mul_pow, mul_pow, hc]
  ring


lemma act_homogeneous {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    act A P ∈ MTT.Cohomology.Sym ℂ n := by
  have h := (show P.IsHomogeneous n from hP).aeval
    (fun i => ∑ a : Fin 2, (A a i : ℂ) • (MvPolynomial.X a : Binary ℂ))
    (fun i => MvPolynomial.IsHomogeneous.sum _ _ 1 (fun a _ => by
      simpa only [MvPolynomial.smul_eq_C_mul] using
        (MvPolynomial.isHomogeneous_X ℂ a).C_mul (A a i : ℂ)))
  change MvPolynomial.IsHomogeneous
    ((MvPolynomial.aeval fun i : Fin 2 => ∑ a : Fin 2,
      (A a i : ℂ) • (MvPolynomial.X a : Binary ℂ)) P) n
  convert! h using 1 <;> simp

lemma eval_act (P : Binary ℂ) (A : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℂ) :
    MvPolynomial.eval ![x,y] (act A P) =
      MvPolynomial.eval ![(A 0 0 : ℂ) * x + (A 1 0 : ℂ) * y,
        (A 0 1 : ℂ) * x + (A 1 1 : ℂ) * y] P := by
  change MvPolynomial.aeval ![x,y] (MvPolynomial.aeval _ P) = MvPolynomial.aeval _ P
  rw [MvPolynomial.comp_aeval_apply]
  congr 1
  ext i
  fin_cases i <;> simp [Fin.sum_univ_two, MvPolynomial.smul_eq_C_mul]


lemma contraction_eval_left {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (w : ℂ) :
    periodContraction n (periodPower n w) P = MvPolynomial.eval ![-1,w] P := by
  rw [periodContraction, eval_homogeneous hP]
  rw [← Finset.sum_range_reflect (fun j =>
    MvPolynomial.coeff (binaryExponent n j) P * (-1 : ℂ) ^ j * w ^ (n - j)) (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : n + 1 - 1 - j = n - j := by omega
  rw [he, Nat.sub_sub_self hj', coeff_periodPower n j hj']
  have hc : (n.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  field_simp

lemma eval_act_mob {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (γ : SL(2, ℤ)) (w t : ℂ)
    (hd : (γ 1 0 : ℂ) * w + (γ 1 1 : ℂ) ≠ 0) :
    MvPolynomial.eval ![t, -t * (((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) /
      ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)))] (act γ.val P) =
      (((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ))⁻¹) ^ n *
        MvPolynomial.eval ![t, -t * w] P := by
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    have hh := γ.property
    rw [Matrix.det_fin_two] at hh
    exact_mod_cast hh
  rw [eval_act]
  have hx : (γ 0 0 : ℂ) * t + (γ 1 0 : ℂ) *
      (-t * (((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)))) =
      (((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ))⁻¹) * t := by
    field_simp [hd]
    linear_combination t * hdet
  have hy : (γ 0 1 : ℂ) * t + (γ 1 1 : ℂ) *
      (-t * (((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)))) =
      (((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ))⁻¹) * (-t * w) := by
    field_simp [hd]
    have hd2 : w * (γ 1 0 : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by simpa [mul_comm] using hd
    field_simp [hd2]
    linear_combination -t * w * hdet
  rw [hx, hy, eval_homogeneous_scale hP]

end MTT.LocalPeriod


set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
namespace MTT.LocalPeriod
open MTT.Cohomology

lemma first_test_derivative {N k : ℕ}
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) (z : ℍ) :
    let A : ℂ → ℂ := fun w => periodContraction (k - 2) (U w)
      (conj ((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower (k - 2) (conj w))
    (1 / 2 : ℂ) * (fderiv ℝ A z 1 - Complex.I * fderiv ℝ A z Complex.I) =
      periodContraction (k - 2) (g z • periodPower (k - 2) z)
        (conj (q z) • periodPower (k - 2) (conj (z : ℂ))) := by
  let n := k - 2
  let H := fun j w => MvPolynomial.coeff (binaryExponent n (n - j))
    (((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower n w)
  let a := fun j => MvPolynomial.coeff (binaryExponent n j) (g z • periodPower n z)
  let b := fun j => -MvPolynomial.coeff (binaryExponent n j)
    (conj (v z) • periodPower n (conj (z : ℂ)))
  let c := fun j => (-1 : ℂ) ^ (n - j) / (n.choose j : ℂ)
  let F := fun j w => c j * (MvPolynomial.coeff (binaryExponent n j) (U w) * conj (H j w))
  have hH (j : ℕ) : HasDerivAt (H j) (deriv (H j) z) z :=
    ((coeff_cusp_holomorphic q n (n - j) (Nat.sub_le _ _)) z z.im_pos).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos) |>.hasDerivAt
  have hF (j : ℕ) : HasFDerivAt (F j)
      (periodDifferential
        (c j * (a j * conj (H j z)))
        (c j * (b j * conj (H j z) +
          MvPolynomial.coeff (binaryExponent n j) (U z) * conj (deriv (H j) z)))) z := by
    simpa only [F, map_zero, mul_zero, add_zero] using
      mixed_const_mul (c j) (mixed_mul (hU.2.2.1 z (binaryExponent n j))
        (mixed_conj (mixed_of_complex (hH j))))
  have hsum := mixed_sum (Finset.range (n + 1)) (fun j _ => hF j)
  have heq : (fun w => ∑ j ∈ Finset.range (n + 1), F j w) =
      fun w => periodContraction (k - 2) (U w)
        (conj ((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower (k - 2) (conj w)) := by
    funext w
    unfold periodContraction
    apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_conj_cusp q n (n - j) (Nat.sub_le _ _)]
    dsimp [F, c, H]
    ring
  rw [heq] at hsum
  change (1 / 2 : ℂ) * _ = _
  rw [mixed_wirtinger hsum]
  unfold periodContraction
  apply Finset.sum_congr rfl
  intro j hj
  rw [show conj (q z) = conj ((↑ₕ(fun τ : ℍ => q τ)) (z : ℂ)) by simp,
    coeff_conj_cusp q n (n - j) (Nat.sub_le _ _)]
  dsimp [c, a, H, n]
  ring

lemma second_test_derivative {N k : ℕ}
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) (z : ℍ) :
    let A : ℂ → ℂ := fun w => conj <| periodContraction (k - 2)
      (((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower (k - 2) w) (U w)
    (1 / 2 : ℂ) * (fderiv ℝ A z 1 - Complex.I * fderiv ℝ A z Complex.I) =
      -conj (periodContraction (k - 2) (q z • periodPower (k - 2) z)
        (conj (v z) • periodPower (k - 2) (conj (z : ℂ)))) := by
  let n := k - 2
  let H := fun j w => MvPolynomial.coeff (binaryExponent n j)
    (((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower n w)
  let a := fun j => MvPolynomial.coeff (binaryExponent n (n - j)) (g z • periodPower n z)
  let b := fun j => -MvPolynomial.coeff (binaryExponent n (n - j))
    (conj (v z) • periodPower n (conj (z : ℂ)))
  let c := fun j => (-1 : ℂ) ^ (n - j) / (n.choose j : ℂ)
  let F := fun j w => c j * (H j w * MvPolynomial.coeff (binaryExponent n (n - j)) (U w))
  have hH (j : ℕ) (hj : j ∈ Finset.range (n + 1)) : HasDerivAt (H j) (deriv (H j) z) z :=
    ((coeff_cusp_holomorphic q n j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) z
      z.im_pos).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos) |>.hasDerivAt
  have hF (j : ℕ) (hj : j ∈ Finset.range (n + 1)) : HasFDerivAt (F j)
      (periodDifferential
        (c j * (deriv (H j) z * MvPolynomial.coeff (binaryExponent n (n - j)) (U z) + H j z * a j))
        (c j * (H j z * b j))) z := by
    simpa only [F, zero_mul, zero_add] using
      mixed_const_mul (c j) (mixed_mul (mixed_of_complex (hH j hj))
        (hU.2.2.1 z (binaryExponent n (n - j))))
  have hsum := mixed_conj (mixed_sum (Finset.range (n + 1)) hF)
  have heq : (fun w => conj (∑ j ∈ Finset.range (n + 1), F j w)) =
      fun w => conj (periodContraction (k - 2)
        (((↑ₕ(fun τ : ℍ => q τ)) w) • periodPower (k - 2) w) (U w)) := by
    funext w
    congr 1
    unfold periodContraction
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [F, c, H]
    ring
  rw [heq] at hsum
  change (1 / 2 : ℂ) * _ = _
  rw [mixed_wirtinger hsum, ← map_neg]
  congr 1
  unfold periodContraction
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [c, b, H, n]
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply]
  ring

end MTT.LocalPeriod


set_option autoImplicit false
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups Modular ComplexConjugate
namespace MTT.LocalPeriod
open MTT.Cohomology

lemma cusp_transform {N k : ℕ} (q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) (z : ℍ) :
    q (γ • z) = denom γ z ^ k * q z := by
  have hs := SlashInvariantFormClass.slash_action_eq q (Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (show Matrix.SpecialLinearGroup.mapGL ℝ γ ∈ MTT.GammaOne N from ⟨γ, hγ, rfl⟩)
  have ht := (ModularForm.slash_action_eq'_iff (k : ℤ) q γ z).mp (congrFun hs z)
  simpa [denom, zpow_natCast] using ht

lemma weight_cancel {k : ℕ} (hk : 2 ≤ k) {d : ℂ} (hd : d ≠ 0) :
    d ^ k * (d⁻¹) ^ (k - 2) = d ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel, pow_add, inv_pow]
  rw [mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ hd), one_mul]

lemma contraction_transform_right {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (γ : SL(2, ℤ)) (z : ℍ) :
    periodContraction n (act γ.val P) (periodPower n (conj ((γ • z : ℍ) : ℂ))) =
      ((conj (denom γ z))⁻¹) ^ n * periodContraction n P (periodPower n (conj (z : ℂ))) := by
  have hd : (γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
    simpa [denom] using denom_ne_zero γ z
  have hd' : (γ 1 0 : ℂ) * conj (z : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
    simpa using (map_ne_zero (starRingEnd ℂ)).mpr hd
  have hh := eval_act_mob hP γ (conj (z : ℂ)) 1 hd'
  rw [contraction_eval (act_homogeneous hP γ.val), contraction_eval hP]
  simpa [coe_specialLinearGroup_apply, coe_smul, σ, num, denom] using hh

lemma contraction_transform_left {n : ℕ} {P : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (γ : SL(2, ℤ)) (z : ℍ) :
    periodContraction n (periodPower n ((γ • z : ℍ) : ℂ)) (act γ.val P) =
      (denom γ z)⁻¹ ^ n * periodContraction n (periodPower n (z : ℂ)) P := by
  have hd : (γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
    simpa [denom] using denom_ne_zero γ z
  have hh := eval_act_mob hP γ z (-1) hd
  rw [contraction_eval_left (act_homogeneous hP γ.val), contraction_eval_left hP]
  simpa [coe_specialLinearGroup_apply, coe_smul, σ, num, denom] using hh

lemma first_test_equivariant {N k : ℕ} (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) (z : ℍ) :
    periodContraction (k - 2) (U (γ • z : ℍ))
        (conj (q (γ • z)) • periodPower (k - 2) (conj ((γ • z : ℍ) : ℂ))) =
      conj (denom γ z) ^ 2 * periodContraction (k - 2) (U z)
        (conj (q z) • periodPower (k - 2) (conj (z : ℂ))) := by
  have hsm (n : ℕ) (P Q : Binary ℂ) (b : ℂ) :
      periodContraction n P (b • Q) = b * periodContraction n P Q := by
    simpa using periodContraction_smul_smul n 1 b P Q
  rw [hsm, hsm, hU.2.1 ⟨γ, hγ⟩ z, contraction_transform_right (hU.1 z),
    cusp_transform q γ hγ z, map_mul, map_pow]
  have hd : conj (denom γ z) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr (denom_ne_zero γ z)
  calc
    _ = (conj (denom γ z) ^ k * ((conj (denom γ z))⁻¹) ^ (k - 2)) *
        (conj (q z) * periodContraction (k - 2) (U z) (periodPower (k - 2) (conj (z : ℂ)))) := by ring
    _ = _ := by rw [weight_cancel hk hd]

lemma second_test_equivariant {N k : ℕ} (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) (z : ℍ) :
    conj (periodContraction (k - 2)
        (q (γ • z) • periodPower (k - 2) ((γ • z : ℍ) : ℂ)) (U (γ • z : ℍ))) =
      conj (denom γ z) ^ 2 * conj (periodContraction (k - 2)
        (q z • periodPower (k - 2) (z : ℂ)) (U z)) := by
  have hsm (n : ℕ) (P Q : Binary ℂ) (a : ℂ) :
      periodContraction n (a • P) Q = a * periodContraction n P Q := by
    simpa using periodContraction_smul_smul n a 1 P Q
  rw [hsm, hsm, hU.2.1 ⟨γ, hγ⟩ z, contraction_transform_left (hU.1 z),
    cusp_transform q γ hγ z, ← map_pow, ← map_mul]
  congr 1
  calc
    _ = (denom γ z ^ k * (denom γ z)⁻¹ ^ (k - 2)) *
        (q z * periodContraction (k - 2) (periodPower (k - 2) (z : ℂ)) (U z)) := by ring
    _ = _ := by rw [weight_cancel hk (denom_ne_zero γ z)]

end MTT.LocalPeriod


set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology
theorem solution
    {N k : ℕ} (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    let A₁ : ℂ → ℂ := fun z =>
      periodContraction (k - 2) (U z)
        (conj ((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) (conj z))
    let A₂ : ℂ → ℂ := fun z => conj <|
      periodContraction (k - 2)
        (((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) z) (U z)
    ContDiffOn ℝ 1 A₁ upperHalfPlaneSet ∧
    (∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ,
      A₁ ((γ • τ : ℍ) : ℂ) =
        (starRingEnd ℂ (denom γ τ)) ^ 2 * A₁ τ) ∧
    (∀ z : ℍ,
      (1 / 2 : ℂ) *
          (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I) =
        periodContraction (k - 2)
          (g z • periodPower (k - 2) (z : ℂ))
          (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) ∧
    ContDiffOn ℝ 1 A₂ upperHalfPlaneSet ∧
    (∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ,
      A₂ ((γ • τ : ℍ) : ℂ) =
        (starRingEnd ℂ (denom γ τ)) ^ 2 * A₂ τ) ∧
    (∀ z : ℍ,
      (1 / 2 : ℂ) *
          (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I) =
        -conj (periodContraction (k - 2)
          (q z • periodPower (k - 2) (z : ℂ))
          (conj (v z) • periodPower (k - 2) (conj (z : ℂ)))))  := by
  refine ⟨MTT.LocalPeriod.first_test_contDiff g v q U hU, ?_,
    MTT.LocalPeriod.first_test_derivative g v q U hU,
    MTT.LocalPeriod.second_test_contDiff g v q U hU, ?_,
    MTT.LocalPeriod.second_test_derivative g v q U hU⟩
  · intro γ hγ z
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      MTT.LocalPeriod.first_test_equivariant hk g v q U hU γ hγ z
  · intro γ hγ z
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      MTT.LocalPeriod.second_test_equivariant hk g v q U hU γ hγ z

#print axioms solution
