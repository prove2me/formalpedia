-- Prove2me | solution 1 for OAI.SharpLogRamsey.SpatialPublic.actual_prepared_input
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:49:38.399983+00:00
-- url     : https://prove2.me/submissions/99d48295-8955-4834-b4fb-6f1bfae2a5f4

import Mathlib
import Definitions.Def_OAIQ045S002

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_RichLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section

section

namespace SharpLogRamsey.ImplicitBranch
open Polynomial
open scoped Ring

/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

The following Hensel lifting theorem is adapted from Mathlib.RingTheory.Henselian.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Henselian.lean

This code has been modified.
-/

 theorem hensel_nonmonic {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : Polynomial R) (a₀ : R)
    (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a, f.IsRoot a ∧ a-a₀ ∈ I := by
  classical
    let f' := derivative f

    let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
    have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
      intro n
      simp only [c]

    have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => ?_
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
    have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
      intro n
      have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
      apply IsUnit.of_map (Ideal.Quotient.mk I)
      convert! h₂ using 1
      all_goals try with_reducible_and_instances rfl
      exact SModEq.def.mp ((hc_mod n).eval _)
    have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
      intro n
      induction n with
      | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
      | succ n ih => ?_
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _

    have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
      intro m n hmn
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      clear hmn
      induction k with
      | zero => rw [add_zero]
      | succ k ih => ?_
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add

    obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
    refine ⟨a, ?_, ?_⟩
    · show f.IsRoot a
      suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
      intro n
      specialize ha n
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
      refine (ha.symm.eval f).trans ?_
      rw [SModEq.zero]
      exact Ideal.pow_le_pow_right le_self_add (hfcI _)
    · show a - a₀ ∈ I
      specialize ha (0 + 1)
      rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
      rw [← SModEq.sub_mem, ← add_zero a₀]
      refine ha.symm.trans (SModEq.rfl.add ?_)
      rw [SModEq.zero, Ideal.neg_mem_iff]
      exact Ideal.mul_mem_right _ _ h₁

variable {σ K R S : Type*} [Fintype σ] [DecidableEq σ] [Field K]
  [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

lemma aeval_hom {τ : Type*} (φ : R →ₐ[K] S) (x : τ → R) (F : MvPolynomial τ K) :
    φ (MvPolynomial.aeval x F) = MvPolynomial.aeval (fun i => φ (x i)) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf => simp [hf]

omit [Fintype σ] [DecidableEq σ] in

lemma eval_liftZ (F : MvPolynomial (Option σ) K) (h : MvPowerSeries σ K) :
    (liftZ F).eval h = MvPolynomial.aeval (fun o => o.elim h MvPowerSeries.X) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [liftZ,Polynomial.algebraMap_apply]
  | add f g hf hg => simp_all [liftZ]
  | mul_X f i hf => cases i <;> simp_all [liftZ]
omit [Fintype σ] in

lemma derivative_liftZ (F : MvPolynomial (Option σ) K) :
    (liftZ F).derivative = liftZ (MvPolynomial.pderiv none F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [liftZ,Polynomial.algebraMap_apply]
  | add f g hf hg => simp_all [liftZ]
  | mul_X f i hf =>
    cases i <;> simp_all [liftZ,Derivation.leibniz,smul_eq_mul,
      MvPolynomial.pderiv_X] <;> ring
omit [Fintype σ] [DecidableEq σ] in

lemma zeroCoeff_aeval (F : MvPolynomial (Option σ) K) :
    MvPowerSeries.constantCoeff
      (MvPolynomial.aeval (fun o => o.elim 0 MvPowerSeries.X) F) =
      MvPolynomial.constantCoeff F := by
  let φ : MvPowerSeries σ K →ₐ[K] K :=
    { MvPowerSeries.constantCoeff with
      commutes' := by intro c; simp [← MvPowerSeries.c_eq_algebraMap] }
  have H := aeval_hom φ (fun o => o.elim 0 MvPowerSeries.X) F
  have hz : (fun o : Option σ => φ (o.elim 0 MvPowerSeries.X)) = 0 := by
    funext o
    cases o with
    | none => exact map_zero φ
    | some i => change MvPowerSeries.constantCoeff (MvPowerSeries.X i) = 0; simp
  rw [hz,MvPolynomial.aeval_zero] at H
  exact H

theorem exists_formal_branch (F : MvPolynomial (Option σ) K)
    (hF : MvPolynomial.constantCoeff F = 0)
    (hD : MvPolynomial.constantCoeff (MvPolynomial.pderiv none F) ≠ 0) :
    ∃ h : MvPowerSeries σ K,
      MvPowerSeries.constantCoeff h = 0 ∧
      MvPolynomial.aeval (fun o => o.elim h MvPowerSeries.X) F = 0 := by
  let I : Ideal (MvPowerSeries σ K) := Ideal.span (Set.range MvPowerSeries.X)
  have hmem : (liftZ F).eval 0 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem,eval_liftZ]
    let φ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K ⧸ I := Ideal.Quotient.mkₐ K I
    change φ _ = 0
    rw [aeval_hom]
    have hz : (fun o : Option σ => φ (o.elim 0 MvPowerSeries.X)) = 0 := by
      funext o
      cases o with
      | none => exact map_zero φ
      | some i =>
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
    rw [hz,MvPolynomial.aeval_zero,hF,map_zero]
  have hu : IsUnit ((liftZ F).derivative.eval 0) := by
    rw [derivative_liftZ,eval_liftZ,MvPowerSeries.isUnit_iff_constantCoeff,
      zeroCoeff_aeval,isUnit_iff_ne_zero]
    exact hD
  let : IsAdicComplete I (MvPowerSeries σ K) :=
    inferInstanceAs (IsAdicComplete (Ideal.span (Set.range MvPowerSeries.X))
      (MvPowerSeries σ K))
  obtain ⟨h,hr,hh⟩ := hensel_nonmonic I (liftZ F) 0 hmem (hu.map (Ideal.Quotient.mk I))
  refine ⟨h,?_,?_⟩
  · have hi : I ≤ RingHom.ker (MvPowerSeries.constantCoeff (σ := σ) (R := K)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      simp
    apply hi
    simpa using hh
  · simpa [Polynomial.IsRoot,eval_liftZ] using hr

end SharpLogRamsey.ImplicitBranch

open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]

lemma cast_ne_zero_of_lt {n : ℕ} (hn : 0 < n) (hp : n < p) : (n : K) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff K p]
  exact fun h => (Nat.le_of_dvd hn h).not_gt hp
omit [Fintype σ] in

lemma coeff_deriv_predecessor (f : MvPowerSeries σ K) (d : σ →₀ ℕ) (i : σ)
    (hi : 0 < d i) :
    MvPowerSeries.coeff (d-single i 1) (MvPowerSeries.pderiv _ i f) =
      MvPowerSeries.coeff d f * (d i : K) := by
  have h : single i 1 ≤ d := by
    intro j
    by_cases he : i = j
    · subst j; simpa using (Nat.succ_le_iff.mpr hi)
    · simp [single_eq_of_ne (Ne.symm he)]
  rw [MvPowerSeries.coeff_pderiv,tsub_add_cancel_of_le h,
    coe_tsub,Pi.sub_apply,single_eq_same,Nat.cast_sub (by omega),Nat.cast_one,sub_add_cancel]
omit [DecidableEq σ] in

lemma degree_pos_coordinate {d : σ →₀ ℕ} (hd : 0 < degree d) :
    ∃ i, 0 < d i := by
  by_contra! h
  have hz : d = 0 := by ext i; exact Nat.eq_zero_of_le_zero (h i)
  simp [hz] at hd
omit [Fintype σ] in

lemma coordinate_le_degree (d : σ →₀ ℕ) (i : σ) : d i ≤ degree d := by
  classical
  rw [degree_apply]
  by_cases hi : i ∈ d.support
  · exact single_le_sum (fun _ _ => Nat.zero_le _) hi
  · simp at hi
    simp [hi]

theorem coeff_zero_of_hessian_zero (h : MvPowerSeries σ K)
    (hh : ∀ i j, MvPowerSeries.pderiv _ i (MvPowerSeries.pderiv _ j h) = 0)
    (d : σ →₀ ℕ) (hd : 2 ≤ degree d) (hdp : degree d < p) :
    MvPowerSeries.coeff d h = 0 := by
  obtain ⟨i,hi⟩ := degree_pos_coordinate (d := d) (by omega)
  have hs : single i 1 ≤ d := by
    intro j
    by_cases he : i = j
    · subst j; simpa using (Nat.succ_le_iff.mpr hi)
    · simp [single_eq_of_ne (Ne.symm he)]
  let e := d-single i 1
  have hed : e + single i 1 = d := tsub_add_cancel_of_le hs
  have hedeg : degree e + 1 = degree d := by
    have := congrArg degree hed
    simpa using this
  obtain ⟨j,hj⟩ := degree_pos_coordinate (d := e) (by omega)
  have hc := coeff_deriv_predecessor (MvPowerSeries.pderiv _ i h) e j hj
  rw [hh j i,MvPowerSeries.coeff_zero] at hc
  have hej : (e j : K) ≠ 0 := cast_ne_zero_of_lt (p := p) hj
    (lt_of_le_of_lt (coordinate_le_degree e j) (by omega))
  have he0 : MvPowerSeries.coeff e (MvPowerSeries.pderiv _ i h) = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_right hej
  have hc' := coeff_deriv_predecessor h d i hi
  change MvPowerSeries.coeff e (MvPowerSeries.pderiv _ i h) = _ at hc'
  rw [he0] at hc'
  exact (mul_eq_zero.mp hc'.symm).resolve_right
    (cast_ne_zero_of_lt (p := p) hi (lt_of_le_of_lt (coordinate_le_degree d i) hdp))

omit [Fintype σ] [DecidableEq σ] in

lemma mem_jetIdeal_iff (n : ℕ) (f : MvPowerSeries σ K) :
    f ∈ jetIdeal n ↔ ∀ d, degree d < n → MvPowerSeries.coeff d f = 0 := by
  constructor
  · intro h d hd
    exact MvPowerSeries.coeff_of_lt_order
      ((show ((degree d : ℕ) : ℕ∞) < n by exact_mod_cast hd).trans_le h)
  · exact MvPowerSeries.nat_le_order

theorem hessian_zero_affine_jet (h : MvPowerSeries σ K)
    (hh : ∀ i j, MvPowerSeries.pderiv _ i (MvPowerSeries.pderiv _ j h) = 0) :
    h - (MvPowerSeries.truncTotal 2 h : MvPolynomial σ K).toMvPowerSeries ∈ jetIdeal p := by
  rw [mem_jetIdeal_iff]
  intro d hdp
  rw [map_sub,MvPolynomial.coeff_coe]
  by_cases hd : degree d < 2
  · rw [MvPowerSeries.coeff_truncTotal _ hd,sub_self]
  · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega),sub_zero]
    exact coeff_zero_of_hessian_zero h hh d (by omega) hdp

variable {τ R : Type*} [CommRing R] [Algebra K R]

lemma aeval_sub_mem (I : Ideal R) (x y : τ → R)
    (hxy : ∀ i, x i-y i ∈ I) (F : MvPolynomial τ K) :
    MvPolynomial.aeval x F-MvPolynomial.aeval y F ∈ I := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simpa only [map_add,add_sub_add_comm] using I.add_mem hf hg
  | mul_X f i hf =>
    simpa only [map_mul,MvPolynomial.aeval_X,
      show MvPolynomial.aeval x f*x i-MvPolynomial.aeval y f*y i =
        x i*(MvPolynomial.aeval x f-MvPolynomial.aeval y f)+
          MvPolynomial.aeval y f*(x i-y i) from by ring] using
      I.add_mem (I.mul_mem_left (x i) hf) (I.mul_mem_left _ (hxy i))

variable [Fintype τ] [DecidableEq τ]

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma totalDegree_aeval_linear (x : τ → MvPolynomial σ K)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (F : MvPolynomial τ K) :
    (MvPolynomial.aeval x F).totalDegree ≤ F.totalDegree := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  apply le_trans (MvPolynomial.totalDegree_mul _ _)
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C,zero_add]
  calc
    _ ≤ ∑ i ∈ d.support, (x i ^ d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (MvPolynomial.totalDegree_pow _ _).trans
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d i) (hx i)
    _ ≤ F.totalDegree := MvPolynomial.le_totalDegree hd
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma toSeries_aeval (x : τ → MvPolynomial σ K) (F : MvPolynomial τ K) :
    (MvPolynomial.aeval x F).toMvPowerSeries =
      MvPolynomial.aeval (fun i => (x i).toMvPowerSeries) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [← MvPowerSeries.c_eq_algebraMap]
  | add f g hf hg => simp only [map_add,MvPolynomial.coe_add,hf,hg]
  | mul_X f i hf => simp only [map_mul,MvPolynomial.coe_mul,MvPolynomial.aeval_X,hf]

omit [Fintype σ] in

lemma polynomial_eq_zero_of_jet {F : MvPolynomial σ K} {n : ℕ}
    (hF : F.totalDegree < n) (h : F.toMvPowerSeries ∈ jetIdeal n) : F = 0 := by
  ext d
  rw [MvPolynomial.coeff_zero]
  by_cases hd : d ∈ F.support
  · have hle := MvPolynomial.le_totalDegree hd
    have hc := (mem_jetIdeal_iff n F.toMvPowerSeries).mp h d (lt_of_le_of_lt hle hF)
    simpa using hc
  · exact MvPolynomial.notMem_support_iff.mp hd

theorem flat_branch_zero_plane (F : MvPolynomial (Option σ) K)
    (hF : F.totalDegree < p) (h : MvPowerSeries σ K)
    (hroot : MvPolynomial.aeval (fun o => o.elim h MvPowerSeries.X) F = 0)
    (hh : ∀ i j, MvPowerSeries.pderiv _ i (MvPowerSeries.pderiv _ j h) = 0) :
    MvPolynomial.aeval (fun o => o.elim (MvPowerSeries.truncTotal 2 h) MvPolynomial.X) F = 0 := by
  let lin := MvPowerSeries.truncTotal 2 h
  let x : Option σ → MvPolynomial σ K := fun o => o.elim lin MvPolynomial.X
  have hx : ∀ i, (x i).totalDegree ≤ 1 := by
    intro i
    cases i with
    | none =>
      have H := MvPowerSeries.totalDegree_truncTotal_lt h (by norm_num : (2:ℕ) ≠ 0)
      change lin.totalDegree ≤ 1
      dsimp [lin]
      omega
    | some i => exact (MvPolynomial.totalDegree_X (R := K) i).le
  apply polynomial_eq_zero_of_jet (n := p)
  · exact (totalDegree_aeval_linear x hx F).trans_lt hF
  · have H := aeval_sub_mem (jetIdeal p)
      (fun o => o.elim h MvPowerSeries.X) (fun i => (x i).toMvPowerSeries) (fun i => ?_) F
    · rw [hroot,zero_sub] at H
      rw [toSeries_aeval]
      exact neg_mem_iff.mp H
    cases i with
    | none => exact hessian_zero_affine_jet h hh
    | some i => simp [x]

lemma deriv_aeval (D : Derivation K R R) (x : τ → R) (F : MvPolynomial τ K) :
    D (MvPolynomial.aeval x F) =
      ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i F) * D (x i) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg,add_mul,Finset.sum_add_distrib]
  | mul_X f j hf =>
    simp only [map_mul,MvPolynomial.aeval_X,Derivation.leibniz,smul_eq_mul,
      map_add,MvPolynomial.pderiv_X]
    simp only [
      add_mul,Finset.sum_add_distrib]
    rw [hf,Finset.mul_sum]
    congr 1
    · simp [Pi.single_apply]
    · apply Finset.sum_congr rfl
      intro i hi
      ring

lemma deriv2_aeval (D E : Derivation K R R) (x : τ → R) (F : MvPolynomial τ K) :
    D (E (MvPolynomial.aeval x F)) =
      (∑ j, ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j F)) * D (x i) * E (x j)) +
      ∑ j, MvPolynomial.aeval x (MvPolynomial.pderiv j F) * D (E (x j)) := by
  rw [deriv_aeval E,map_sum]
  simp only [Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [deriv_aeval D,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma branch_second_sum (h : MvPowerSeries σ K) (g : Option σ → MvPowerSeries σ K)
    (a b : σ) :
    (∑ j, g j * MvPowerSeries.pderiv _ a
      (MvPowerSeries.pderiv _ b (branchPoint h j))) =
    g none * MvPowerSeries.pderiv _ a (MvPowerSeries.pderiv _ b h) := by
  rw [Fintype.sum_option]
  simp [branchPoint,MvPowerSeries.pderiv_X,Pi.single_apply,apply_ite]

end SharpLogRamsey.FlatnessCore
end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_HessianTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]
variable {τ R : Type*} [CommRing R] [Algebra K R]
variable [Fintype τ] [DecidableEq τ]
lemma hessian_zero_of_tangent_zero (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (hroot : MvPolynomial.aeval (branchPoint h) F = 0)
    (hu : IsUnit (MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F)))
    (ht : ∀ a b, (∑ j, ∑ i, MvPolynomial.aeval (branchPoint h)
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) *
        branchTangent h a i * branchTangent h b j) = 0) :
    ∀ a b, MvPowerSeries.pderiv _ a (MvPowerSeries.pderiv _ b h) = 0 := by
  intro a b
  have H := deriv2_aeval (MvPowerSeries.pderiv _ a) (MvPowerSeries.pderiv _ b)
    (branchPoint h) F
  rw [hroot,map_zero,map_zero] at H
  change 0 = (∑ j, ∑ i, _ * branchTangent h a i * branchTangent h b j) + _ at H
  rw [ht a b,zero_add,branch_second_sum] at H
  exact (IsUnit.mul_right_eq_zero hu).mp H.symm

omit [Fintype σ] in

lemma aeval_scaledTangent (x : Option σ → R) (F : MvPolynomial (Option σ) K)
    (a : σ) (i : Option σ) :
    MvPolynomial.aeval x (scaledTangent (fun o => MvPolynomial.pderiv o F) a i) =
    scaledTangent (fun o => MvPolynomial.aeval x (MvPolynomial.pderiv o F)) a i := by
  cases i with
  | none => simp [scaledTangent]
  | some i => by_cases hi : i = a <;> simp [scaledTangent,hi]

lemma first_branch_derivative (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (a : σ) :
    MvPowerSeries.pderiv _ a (MvPolynomial.aeval (branchPoint h) F) =
      MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F) *
        MvPowerSeries.pderiv _ a h +
      MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv (some a) F) := by
  rw [deriv_aeval,Fintype.sum_option]
  simp [branchPoint,MvPowerSeries.pderiv_X,Pi.single_apply]

lemma scaled_branch_tangent (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (hroot : MvPolynomial.aeval (branchPoint h) F = 0)
    (a : σ) (i : Option σ) :
    MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F) *
      branchTangent h a i =
      scaledTangent (fun o => MvPolynomial.aeval (branchPoint h)
        (MvPolynomial.pderiv o F)) a i := by
  cases i with
  | none =>
    have H := first_branch_derivative F h a
    rw [hroot,map_zero] at H
    change _ * MvPowerSeries.pderiv _ a h = -_
    exact eq_neg_of_add_eq_zero_left H.symm
  | some i => simp [branchTangent,branchPoint,scaledTangent,MvPowerSeries.pderiv_X,
      Pi.single_apply,mul_ite]

lemma flatness_root_implies_hessian_zero (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (hroot : MvPolynomial.aeval (branchPoint h) F = 0)
    (hu : IsUnit (MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F)))
    (hflat : ∀ a b, MvPolynomial.aeval (branchPoint h) (flatnessPolynomial F a b) = 0) :
    ∀ a b, MvPowerSeries.pderiv _ a (MvPowerSeries.pderiv _ b h) = 0 := by
  apply hessian_zero_of_tangent_zero F h hroot hu
  intro a b
  let z := MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F)
  have H := hflat a b
  simp only [flatnessPolynomial,map_sum,map_mul,aeval_scaledTangent] at H
  have he : MvPolynomial.aeval (branchPoint h) (flatnessPolynomial F a b) =
      z*z*(∑ j, ∑ i, MvPolynomial.aeval (branchPoint h)
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) *
          branchTangent h a i * branchTangent h b j) := by
    simp only [flatnessPolynomial,map_sum,map_mul,aeval_scaledTangent,
      ← scaled_branch_tangent F h hroot,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [z]
    ring
  rw [hflat a b] at he
  exact (IsUnit.mul_right_eq_zero (hu.mul hu)).mp he.symm

end SharpLogRamsey.FlatnessCore

namespace SharpLogRamsey.LocalFlatness
open SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
omit [Fintype σ] [DecidableEq σ] in

lemma branch_constantCoeff (h : MvPowerSeries σ K)
    (hh : MvPowerSeries.constantCoeff h = 0) (F : MvPolynomial (Option σ) K) :
    MvPowerSeries.constantCoeff (MvPolynomial.aeval (branchPoint h) F) =
      MvPolynomial.constantCoeff F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [← MvPowerSeries.c_eq_algebraMap]
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf => cases i <;> simp [branchPoint,hh]
omit [Fintype σ] [DecidableEq σ] in

lemma rename_aeval (lin : MvPolynomial σ K) (G : MvPolynomial (Option σ) K) :
    MvPolynomial.rename Option.some (MvPolynomial.aeval
      (fun o => o.elim lin MvPolynomial.X) G) =
    MvPolynomial.aeval (fun o => o.elim (MvPolynomial.rename Option.some lin)
      (fun i => MvPolynomial.X (some i))) G := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => cases i <;> simp only [map_mul,MvPolynomial.aeval_X,hf,
      Option.elim_none,Option.elim_some,MvPolynomial.rename_X]

omit [Fintype σ] [DecidableEq σ] in

lemma plane_factor_of_zero (lin : MvPolynomial σ K) (G : MvPolynomial (Option σ) K)
    (hz : MvPolynomial.aeval (fun o => o.elim lin MvPolynomial.X) G = 0) :
    MvPolynomial.X none - MvPolynomial.rename Option.some lin ∣ G := by
  let L : MvPolynomial (Option σ) K := MvPolynomial.X none-MvPolynomial.rename Option.some lin
  let I := Ideal.span ({L} : Set (MvPolynomial (Option σ) K))
  have he : MvPolynomial.aeval (fun o => o.elim (MvPolynomial.rename Option.some lin)
      (fun i => MvPolynomial.X (some i))) G = 0 := by
    rw [← rename_aeval,hz,map_zero]
  have H := aeval_sub_mem I (fun o => MvPolynomial.X o)
    (fun o => o.elim (MvPolynomial.rename Option.some lin) (fun i => MvPolynomial.X (some i)))
    (fun o => by cases o; exact Ideal.subset_span (Set.mem_singleton L); simp) G
  rw [he,sub_zero,MvPolynomial.aeval_X_left_apply] at H
  exact Ideal.mem_span_singleton.mp H

theorem exists_plane_factor_of_flatness {p : ℕ} [CharP K p]
    (G F : MvPolynomial (Option σ) K) (hdeg : G.totalDegree < p)
    (hdiv : F ∣ G) (hF : MvPolynomial.constantCoeff F = 0)
    (hDz : MvPolynomial.constantCoeff (MvPolynomial.pderiv none G) ≠ 0)
    (hflat : ∀ a b, F ∣ flatnessPolynomial G a b) :
    ∃ lin : MvPolynomial σ K, lin.totalDegree ≤ 1 ∧
      MvPolynomial.constantCoeff lin = 0 ∧
      MvPolynomial.X none-MvPolynomial.rename Option.some lin ∣ G := by
  obtain ⟨J,hJ⟩ := hdiv
  have hG : MvPolynomial.constantCoeff G = 0 := by simp [hJ,hF]
  have hJ0 : MvPolynomial.constantCoeff J ≠ 0 := by
    intro hz
    apply hDz
    simp [hJ,Derivation.leibniz,smul_eq_mul,hF,hz]
  obtain ⟨h,hh,hr⟩ := ImplicitBranch.exists_formal_branch G hG hDz
  change MvPolynomial.aeval (branchPoint h) G = 0 at hr
  have hJu : IsUnit (MvPolynomial.aeval (branchPoint h) J) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,branch_constantCoeff h hh,isUnit_iff_ne_zero]
    exact hJ0
  have hFr : MvPolynomial.aeval (branchPoint h) F = 0 := by
    rw [hJ,map_mul] at hr
    exact (IsUnit.mul_left_eq_zero hJu).mp hr
  have hu : IsUnit (MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none G)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,branch_constantCoeff h hh,isUnit_iff_ne_zero]
    exact hDz
  have hf : ∀ a b, MvPolynomial.aeval (branchPoint h) (flatnessPolynomial G a b) = 0 := by
    intro a b
    obtain ⟨V,hV⟩ := hflat a b
    simp [hV,hFr]
  have hess := flatness_root_implies_hessian_zero G h hr hu hf
  have hz := flat_branch_zero_plane G hdeg h hr hess
  refine ⟨MvPowerSeries.truncTotal 2 h,?_,?_,plane_factor_of_zero _ G hz⟩
  · have H := MvPowerSeries.totalDegree_truncTotal_lt h (by norm_num : (2:ℕ) ≠ 0)
    omega
  · simpa [MvPowerSeries.constantCoeff_truncTotal_eq_ite] using hh

end SharpLogRamsey.LocalFlatness

open scoped BigOperators
open MvPolynomial Finsupp
namespace SharpLogRamsey.PolynomialGeometry
variable {σ K : Type*} [Field K]

lemma totalDegree_pderiv_lt (F : MvPolynomial σ K) (i : σ)
    (hi : pderiv i F ≠ 0) : (pderiv i F).totalDegree < F.totalDegree := by
  classical
  obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup _ (MvPolynomial.support_nonempty.mpr hi)
    (fun d : σ →₀ ℕ => d.sum fun _ e => e)
  have hc : F.coeff (d+Finsupp.single i 1) ≠ 0 := by
    have H := MvPolynomial.mem_support_iff.mp hd
    rw [MvPolynomial.coeff_pderiv] at H
    exact (mul_ne_zero_iff.mp H).1
  have H := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  change Finsupp.degree (d+Finsupp.single i 1) ≤ F.totalDegree at H
  have H' : d.degree+1 ≤ F.totalDegree := by
    simpa only [map_add, Finsupp.degree_single] using H
  change (pderiv i F).support.sup (fun d : σ →₀ ℕ => d.sum fun _ e => e) < F.totalDegree
  rw [he]
  exact H'

lemma not_dvd_pderiv (F : MvPolynomial σ K) (i : σ) (hi : pderiv i F ≠ 0) :
    ¬F ∣ pderiv i F := by
  intro h
  exact (totalDegree_pderiv_lt F i hi).not_ge
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain h hi)

lemma not_dvd_squarefree_derivative (G F : MvPolynomial σ K)
    (hs : Squarefree G) (hF : Irreducible F) (hd : F ∣ G) (i : σ)
    (hi : pderiv i F ≠ 0) : ¬ F ∣ pderiv i G := by
  obtain ⟨J,rfl⟩ := hd
  intro h
  have hp : Prime F := irreducible_iff_prime.mp hF
  have hn : ¬F ∣ J := by
    intro hj
    exact hF.not_isUnit (hs F (mul_dvd_mul dvd_rfl hj))
  have he : pderiv i (F*J) = pderiv i F*J+F*pderiv i J := by
    rw [MvPolynomial.pderiv_mul]
  rw [he,dvd_add_left (dvd_mul_right F _)] at h
  rcases hp.dvd_mul.mp h with h|h
  · exact not_dvd_pderiv F i hi h
  · exact hn h

lemma totalDegree_pos_of_irreducible (F : MvPolynomial σ K) (hF : Irreducible F) :
    0 < F.totalDegree := by
  by_contra! h
  have he : F = C (F.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
  have hc : F.coeff 0 ≠ 0 := by intro hc; apply hF.ne_zero; rw [he,hc,map_zero]
  exact hF.not_isUnit (isUnit_iff_totalDegree_of_isReduced.mpr
    ⟨isUnit_iff_ne_zero.mpr hc,Nat.eq_zero_of_le_zero h⟩)

lemma exists_nonzero_pderiv {p : ℕ} [CharP K p]
    (F : MvPolynomial σ K) (hpos : 0 < F.totalDegree) (hdeg : F.totalDegree < p) :
    ∃ i, pderiv i F ≠ 0 := by
  classical
  have hF : F ≠ 0 := by intro he; simp [he] at hpos
  obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (fun d : σ →₀ ℕ => d.sum fun _ e => e)
  change F.totalDegree = d.degree at he
  have hdz : d ≠ 0 := by intro hd0; simp [hd0] at he; omega
  obtain ⟨i,hi⟩ := Finsupp.ne_iff.mp hdz
  have hi0 : 0 < d i := Nat.pos_of_ne_zero hi
  have hdi : d i ≤ d.degree := by
    rw [Finsupp.degree_apply]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hi)
  have hcast : (d i : K) ≠ 0 := by
    rw [ne_eq,CharP.cast_eq_zero_iff K p]
    intro H
    have := Nat.le_of_dvd hi0 H
    omega
  have hs : Finsupp.single i 1 ≤ d := by
    intro j
    by_cases hij : i = j
    · subst j; simpa using (Nat.succ_le_iff.mpr hi0)
    · simp [Finsupp.single_eq_of_ne (Ne.symm hij)]
  refine ⟨i,fun hz => ?_⟩
  have hc := congrArg (fun poly : MvPolynomial σ K => poly.coeff (d-Finsupp.single i 1)) hz
  rw [coeff_pderiv,tsub_add_cancel_of_le hs,MvPolynomial.coeff_zero] at hc
  have hc' : F.coeff d * (d i : K) = 0 := by
    simpa [Finsupp.coe_tsub,Pi.sub_apply,Finsupp.single_eq_same,
      Nat.cast_sub (show 1 ≤ d i by omega)] using hc
  exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hcast) hc'

variable [Finite σ] [IsAlgClosed K]

lemma exists_zero_not_zero (F D : MvPolynomial σ K)
    (hF : Irreducible F) (hD : ¬F ∣ D) :
    ∃ x : σ → K, aeval x F = 0 ∧ aeval x D ≠ 0 := by
  classical
  let I : Ideal (MvPolynomial σ K) := Ideal.span {F}
  let : I.IsPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr
    (irreducible_iff_prime.mp hF)
  by_contra! H
  have hv : D ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
    intro x hx
    apply H x
    exact hx F (Ideal.subset_span (Set.mem_singleton F))
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hv
  exact hD (Ideal.mem_span_singleton.mp hv)

lemma exists_nonsingular_factor_zero (G F : MvPolynomial σ K)
    (hs : Squarefree G) (hF : Irreducible F) (hd : F ∣ G) (i : σ)
    (hi : pderiv i F ≠ 0) :
    ∃ x : σ → K, aeval x F = 0 ∧ aeval x (pderiv i G) ≠ 0 :=
  exists_zero_not_zero F _ hF (not_dvd_squarefree_derivative G F hs hF hd i hi)

end SharpLogRamsey.PolynomialGeometry

open scoped BigOperators
open MvPolynomial
namespace SharpLogRamsey.Translation
variable {σ K : Type*} [Field K]

lemma pderiv_translate (x : σ → K) (i : σ) (F : MvPolynomial σ K) :
    pderiv i (translate x F) = translate x (pderiv i F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f j hf =>
    simp only [map_mul,translate_X,MvPolynomial.pderiv_mul,map_add,hf,
      MvPolynomial.pderiv_X,MvPolynomial.pderiv_C,add_zero]
    simp only [Pi.single_apply]
    split_ifs <;> simp

lemma constantCoeff_translate (x : σ → K) (F : MvPolynomial σ K) :
    constantCoeff (translate x F) = aeval x F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp [hf]

lemma translate_nonunit (x : σ → K) {F : MvPolynomial σ K} (h : ¬IsUnit F) :
    ¬IsUnit (translate x F) := by
  intro hu
  apply h
  simpa using hu.map (translate (-x))
end SharpLogRamsey.Translation

namespace SharpLogRamsey.GlobalFlatness
open MvPolynomial SharpLogRamsey.FlatnessCore SharpLogRamsey.Translation
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

lemma totalDegree_translate_le {τ : Type*} [Fintype τ] (x : τ → K) (F : MvPolynomial τ K) :
    (Translation.translate x F).totalDegree ≤ F.totalDegree := by
  classical
  apply totalDegree_aeval_linear
  intro i
  apply (totalDegree_add _ _).trans
  simp

lemma translate_flatness (x : Option σ → K) (G : MvPolynomial (Option σ) K) (a b : σ) :
    Translation.translate x (flatnessPolynomial G a b) = flatnessPolynomial (Translation.translate x G) a b := by
  simp only [flatnessPolynomial,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have ht : ∀ c k, Translation.translate x (scaledTangent (fun o => pderiv o G) c k) =
      scaledTangent (fun o => pderiv o (Translation.translate x G)) c k := by
    intro c k
    cases k with
    | none => simp [scaledTangent,pderiv_translate]
    | some k => by_cases h : k = c <;> simp [scaledTangent,h,pderiv_translate]
  rw [ht,ht,← pderiv_translate,← pderiv_translate]

theorem plane_factor_of_flatness {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G F : MvPolynomial (Option σ) K) (hdeg : G.totalDegree < p)
    (hs : Squarefree G) (hF : Irreducible F) (hdiv : F ∣ G)
    (hDzF : pderiv none F ≠ 0) (hflat : ∀ a b, F ∣ flatnessPolynomial G a b) :
    ∃ L : MvPolynomial (Option σ) K, ¬IsUnit L ∧ L.totalDegree ≤ 1 ∧ L ∣ G := by
  obtain ⟨x,hx,hDx⟩ := PolynomialGeometry.exists_nonsingular_factor_zero
    G F hs hF hdiv none hDzF
  have hpl := LocalFlatness.exists_plane_factor_of_flatness
    (Translation.translate x G) (Translation.translate x F)
    ((totalDegree_translate_le x G).trans_lt hdeg) (map_dvd (Translation.translate x) hdiv)
    (by rwa [constantCoeff_translate])
    (by rwa [pderiv_translate,constantCoeff_translate])
    (fun a b => by rw [← translate_flatness]; exact map_dvd (Translation.translate x) (hflat a b))
  obtain ⟨lin,hlin,hlin0,hlind⟩ := hpl
  let L : MvPolynomial (Option σ) K := X none-rename Option.some lin
  have hL0 : constantCoeff L = 0 := by simp [L,hlin0]
  have hLu : ¬IsUnit L := by
    intro hu
    have H := hu.map (constantCoeff : MvPolynomial (Option σ) K →+* K)
    rw [hL0] at H
    exact not_isUnit_zero H
  have hLd : L.totalDegree ≤ 1 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_X none).le
    · exact (totalDegree_rename_le _ _).trans hlin
  refine ⟨Translation.translate (-x) L,translate_nonunit _ hLu,
    (totalDegree_translate_le _ _).trans hLd,?_⟩
  simpa only [translate_neg_translate] using map_dvd (Translation.translate (-x)) hlind

lemma nonplane_factor_not_flat {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G F : MvPolynomial (Option σ) K) (hdeg : G.totalDegree < p)
    (hs : Squarefree G) (hF : Irreducible F) (hdiv : F ∣ G)
    (hDzF : pderiv none F ≠ 0)
    (hn : ∀ L : MvPolynomial (Option σ) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ a b, ¬ F ∣ flatnessPolynomial G a b := by
  by_contra! h
  obtain ⟨L,hu,hd,hdv⟩ := plane_factor_of_flatness G F hdeg hs hF hdiv hDzF h
  exact hu (hn L hdv hd)
end SharpLogRamsey.GlobalFlatness

open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
namespace SharpLogRamsey.CoprimeCombination
variable {σ ι K : Type*} [Fintype ι] [Field K] [Infinite K]

theorem exists_coprime_combination (G : MvPolynomial σ K) (hG : G ≠ 0)
    (Q : ι → MvPolynomial σ K)
    (h : ∀ F : MvPolynomial σ K, Irreducible F → F ∣ G → ∃ i, ¬F ∣ Q i) :
    ∃ c : ι → K, IsRelPrime G (∑ i, c i • Q i) := by
  classical
  let : NormalizationMonoid (MvPolynomial σ K) := UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid
  let S := (normalizedFactors G).toFinset
  let P (F : S) : Submodule K (ι → K) :=
    ((Ideal.span ({F.val} : Set (MvPolynomial σ K))).restrictScalars K).comap (combinationMap Q)
  have hp : ∀ F, P F ≠ ⊤ := by
    intro F ht
    have hfm : F.val ∈ normalizedFactors G := Multiset.mem_toFinset.mp F.property
    obtain ⟨i,hi⟩ := h F.val (prime_of_normalized_factor _ hfm).irreducible
      (dvd_of_mem_normalizedFactors hfm)
    have H : Pi.single i 1 ∈ P F := ht ▸ Submodule.mem_top
    change combinationMap Q (Pi.single i 1) ∈ Ideal.span ({F.val} : Set (MvPolynomial σ K)) at H
    simp [Pi.single_apply] at H
    exact hi (Ideal.mem_span_singleton.mp H)
  obtain ⟨c,hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hp
  refine ⟨c,(isRelPrime_iff_no_prime_factors hG).mpr ?_⟩
  intro F hFG hFQ hFp
  obtain ⟨J,hJ,hassoc⟩ := exists_mem_normalizedFactors_of_dvd hG hFp.irreducible hFG
  apply hc ⟨J,Multiset.mem_toFinset.mpr hJ⟩
  change combinationMap Q c ∈ Ideal.span ({J} : Set (MvPolynomial σ K))
  rw [combinationMap_apply,Ideal.mem_span_singleton]
  exact hassoc.dvd_iff_dvd_left.mp hFQ
end SharpLogRamsey.CoprimeCombination
end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_TotalDegreeCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
namespace SharpLogRamsey.CoprimeCombination
variable {σ ι K : Type*} [Fintype ι] [Field K] [Infinite K]
omit [Infinite K] in
lemma totalDegree_combination_le (Q : ι → MvPolynomial σ K) (c : ι → K) (D : ℕ)
    (h : ∀ i, (Q i).totalDegree ≤ D) :
    (∑ i, c i • Q i).totalDegree ≤ D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_smul_le _ _).trans (h i)
end SharpLogRamsey.CoprimeCombination

namespace SharpLogRamsey.NonplaneCertificate
open MvPolynomial FlatnessCore PolynomialGeometry
variable {K : Type*} [Field K]
noncomputable section

lemma squarefree_equiv {A B : Type*} [Monoid A] [Monoid B]
    (e : A ≃* B) {f : A} (h : Squarefree f) : Squarefree (e f) := by
  intro x hx
  have H : e.symm x*e.symm x ∣ f := by
    simpa only [map_mul,e.symm_apply_apply] using map_dvd e.symm hx
  have H' := (h _ H).map e
  simpa only [e.apply_symm_apply] using H'

lemma totalDegree_equiv_le {α β : Type*} (e : α ≃ β) (F : MvPolynomial α K) :
    (renameEquiv K e F).totalDegree ≤ F.totalDegree := totalDegree_rename_le _ _

lemma pderiv_equiv {α β : Type*} (e : α ≃ β) (F : MvPolynomial α K) (i : α) :
    pderiv (e i) (renameEquiv K e F) = renameEquiv K e (pderiv i F) :=
  pderiv_rename e.injective i F

lemma nonplane_witness {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G F : MvPolynomial (Fin 3) K) (hG : G ≠ 0) (hdeg : G.totalDegree < p)
    (hs : Squarefree G) (hF : Irreducible F) (hdiv : F ∣ G)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ i : Index, ¬F ∣ flatFamily G i := by
  obtain ⟨i,hi⟩ := exists_nonzero_pderiv F
    (totalDegree_pos_of_irreducible F hF)
    ((totalDegree_le_of_dvd_of_isDomain hdiv hG).trans_lt hdeg)
  let e : Option (Fin 2) ≃ Fin 3 := (finSuccEquiv' i).symm
  let E := renameEquiv K e
  have hen : e none = i := finSuccEquiv'_symm_none i
  have hdn : pderiv none (E.symm F) ≠ 0 := by
    have he := pderiv_equiv e.symm F i
    have hnone : e.symm i = none := by rw [← hen]; simp
    rw [hnone] at he
    change pderiv none (E.symm F) = E.symm (pderiv i F) at he
    rw [he]
    exact fun h => hi (E.symm.injective (h.trans (map_zero E.symm).symm))
  obtain ⟨a,b,hab⟩ := GlobalFlatness.nonplane_factor_not_flat
    (E.symm G) (E.symm F)
    ((totalDegree_equiv_le e.symm G).trans_lt hdeg)
    (squarefree_equiv E.symm.toMulEquiv hs)
    ((MulEquiv.irreducible_iff E.symm).mpr hF) (map_dvd E.symm hdiv) hdn
    (fun L hd hdl => by
      have hL := hn (E L) (by simpa only [E.apply_symm_apply] using map_dvd E hd)
        ((totalDegree_equiv_le e L).trans hdl)
      exact (isUnit_map_iff E L).mp hL)
  refine ⟨⟨e,a,b⟩,fun hd => hab ?_⟩
  have H := map_dvd E.symm hd
  change E.symm F ∣ E.symm (E (flatnessPolynomial (E.symm G) a b)) at H
  simpa only [E.symm_apply_apply] using H

lemma totalDegree_partial_le {α : Type*} (F : MvPolynomial α K) (i : α) :
    (pderiv i F).totalDegree ≤ F.totalDegree := by
  by_cases h : pderiv i F = 0
  · simp [h]
  · exact (totalDegree_pderiv_lt F i h).le

lemma totalDegree_tangent_le (G : MvPolynomial (Option (Fin 2)) K) (a : Fin 2)
    (i : Option (Fin 2)) :
    (scaledTangent (fun i => pderiv i G) a i).totalDegree ≤ G.totalDegree := by
  cases i with
  | none => simpa [scaledTangent] using totalDegree_partial_le G (some a)
  | some i =>
    by_cases hi : i = a
    · simpa [scaledTangent,hi] using totalDegree_partial_le G none
    · simp [scaledTangent,hi]

lemma totalDegree_flatness_le (G : MvPolynomial (Option (Fin 2)) K) (a b : Fin 2) :
    (flatnessPolynomial G a b).totalDegree ≤ 3*G.totalDegree := by
  apply totalDegree_finsetSum_le
  intro j hj
  apply totalDegree_finsetSum_le
  intro i hi
  have H := totalDegree_mul (pderiv i (pderiv j G)*scaledTangent (fun i => pderiv i G) a i)
    (scaledTangent (fun i => pderiv i G) b j)
  have H' := totalDegree_mul (pderiv i (pderiv j G)) (scaledTangent (fun i => pderiv i G) a i)
  have H'' := (totalDegree_partial_le (pderiv j G) i).trans (totalDegree_partial_le G j)
  have H1 := totalDegree_tangent_le G a i
  have H2 := totalDegree_tangent_le G b j
  omega

lemma totalDegree_family_le (G : MvPolynomial (Fin 3) K) (i : Index) :
    (flatFamily G i).totalDegree ≤ 3*G.totalDegree := by
  exact (totalDegree_equiv_le _ _).trans ((totalDegree_flatness_le _ _ _).trans
    (Nat.mul_le_mul_left _ (totalDegree_equiv_le _ _)))

theorem exists_coprime_flat_combination {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G : MvPolynomial (Fin 3) K) (hG : G ≠ 0) (hdeg : G.totalDegree < p)
    (hs : Squarefree G)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ c : Index → K, IsRelPrime G (∑ i, c i • flatFamily G i) ∧
      (∑ i, c i • flatFamily G i).totalDegree ≤ 3*G.totalDegree := by
  obtain ⟨c,hc⟩ := CoprimeCombination.exists_coprime_combination G hG (flatFamily G)
    (fun F hF hd => nonplane_witness G F hG hdeg hs hF hd hn)
  exact ⟨c,hc,CoprimeCombination.totalDegree_combination_le _ _ _ (totalDegree_family_le G)⟩
end
end SharpLogRamsey.NonplaneCertificate

open scoped BigOperators
open Finset MvPolynomial
namespace SharpLogRamsey.LineFlatness
variable {K σ R : Type*} [Field K] [Fintype σ] [DecidableEq σ]
  [CommRing R] [Algebra K R]

lemma deriv_aeval (D : Derivation K R R) (x : σ → R) (F : MvPolynomial σ K) :
    D (MvPolynomial.aeval x F) =
      ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i F) * D (x i) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg,add_mul,Finset.sum_add_distrib]
  | mul_X f j hf =>
    simp only [map_mul,MvPolynomial.aeval_X,Derivation.leibniz,smul_eq_mul,
      map_add,MvPolynomial.pderiv_X]
    simp only [
      add_mul,Finset.sum_add_distrib]
    rw [hf,Finset.mul_sum]
    congr 1
    · simp [Pi.single_apply]
    · apply Finset.sum_congr rfl
      intro i hi
      ring

lemma deriv2_aeval (D E : Derivation K R R) (x : σ → R) (F : MvPolynomial σ K) :
    D (E (MvPolynomial.aeval x F)) =
      (∑ j, ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j F)) * D (x i) * E (x j)) +
      ∑ j, MvPolynomial.aeval x (MvPolynomial.pderiv j F) * D (E (x j)) := by
  rw [deriv_aeval E,map_sum]
  simp only [Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [deriv_aeval D,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [Fintype σ] [DecidableEq σ] in

lemma eval_restrictLine (x v : σ → K) (F : MvPolynomial σ K) (t : K) :
    (restrictLine x v F).eval t = eval (fun i => x i + v i*t) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [restrictLine]
  | add f g hf hg => simp_all [restrictLine]
  | mul_X f i hf => simp_all [restrictLine]

lemma derivative_restrictLine (x v : σ → K) (F : MvPolynomial σ K) :
    Polynomial.derivative (restrictLine x v F) =
      ∑ i, restrictLine x v (pderiv i F) * Polynomial.C (v i) := by
  have H := deriv_aeval Polynomial.derivative'
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F
  simpa [restrictLine] using H

lemma line_tangent (x v : σ → K) (F : MvPolynomial σ K)
    (h : restrictLine x v F = 0) :
    ∑ i, eval x (pderiv i F)*v i = 0 := by
  have H := congrArg (Polynomial.eval (0 : K)) (derivative_restrictLine x v F)
  simpa [h,Polynomial.eval_finsetSum,eval_restrictLine] using H.symm

lemma line_hessian (x v : σ → K) (F : MvPolynomial σ K)
    (h : restrictLine x v F = 0) :
    ∑ j, ∑ i, eval x (pderiv i (pderiv j F))*v i*v j = 0 := by
  have H := deriv2_aeval Polynomial.derivative' Polynomial.derivative'
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F
  change Polynomial.derivative (Polynomial.derivative (restrictLine x v F)) = _ at H
  simp only [show ∀ i, Polynomial.derivative'
      (Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) = Polynomial.C (v i)
      from fun i => by simp, show ∀ i, Polynomial.derivative' (Polynomial.C (v i)) = 0
      from fun i => by simp,mul_zero,sum_const_zero,add_zero] at H
  change Polynomial.derivative (Polynomial.derivative (restrictLine x v F)) =
    ∑ j, ∑ i, restrictLine x v (pderiv i (pderiv j F)) * Polynomial.C (v i) * Polynomial.C (v j) at H
  have E := congrArg (Polynomial.eval (0 : K)) H
  simpa [h,Polynomial.eval_finsetSum,eval_restrictLine] using E.symm
omit [Fintype σ] in

lemma pderiv_swap (F : MvPolynomial σ K) (i j : σ) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f k hf =>
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [pderiv_X,Pi.single_apply,apply_ite,hi,hj,hf,add_comm,add_left_comm]
    all_goals split_ifs <;> simp_all

lemma quadratic_vandermonde (v : Fin 3 → Fin 2 → K) :
    (Matrix.of (fun (i j : Fin 3) => ![(v i 0)^2, v i 0*v i 1, (v i 1)^2] j)).det =
      (v 0 0*v 1 1-v 0 1*v 1 0) * (v 0 0*v 2 1-v 0 1*v 2 0) *
      (v 1 0*v 2 1-v 1 1*v 2 0) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  dsimp
  ring

theorem binary_quadratic_three (v : Fin 3 → Fin 2 → K) (A B C : K)
    (h01 : v 0 0*v 1 1-v 0 1*v 1 0 ≠ 0)
    (h02 : v 0 0*v 2 1-v 0 1*v 2 0 ≠ 0)
    (h12 : v 1 0*v 2 1-v 1 1*v 2 0 ≠ 0)
    (hv : ∀ i, A*(v i 0)^2+B*(v i 0*v i 1)+C*(v i 1)^2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  let M : Matrix (Fin 3) (Fin 3) K :=
    Matrix.of (fun i j => ![(v i 0)^2,v i 0*v i 1,(v i 1)^2] j)
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero,quadratic_vandermonde]
    exact mul_ne_zero (mul_ne_zero h01 h02) h12
  have hm : M.mulVec ![A,B,C] = 0 := by
    ext i
    simpa [M,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,mul_comm,add_assoc] using hv i
  have E := congrArg (Matrix.mulVec M⁻¹) hm
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul M hdet,
    Matrix.one_mulVec,Matrix.mulVec_zero] at E
  exact ⟨congrFun E 0,congrFun E 1,congrFun E 2⟩

omit [DecidableEq σ] in

lemma hessian_smul_left (x : σ → K) (F : MvPolynomial σ K) (a : K) (u v : σ → K) :
    hessian x F (a • u) v = a*hessian x F u v := by
  simp only [hessian,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  congr 1; ext j
  congr 1; ext i
  ring
omit [DecidableEq σ] in

lemma hessian_smul_right (x : σ → K) (F : MvPolynomial σ K) (a : K) (u v : σ → K) :
    hessian x F u (a • v) = a*hessian x F u v := by
  simp only [hessian,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  congr 1; ext j
  congr 1; ext i
  ring
omit [DecidableEq σ] in

lemma hessian_add_left (x : σ → K) (F : MvPolynomial σ K) (u v w : σ → K) :
    hessian x F (u+v) w = hessian x F u w+hessian x F v w := by
  simp [hessian,mul_add,add_mul,sum_add_distrib]
omit [DecidableEq σ] in

lemma hessian_add_right (x : σ → K) (F : MvPolynomial σ K) (u v w : σ → K) :
    hessian x F u (v+w) = hessian x F u v+hessian x F u w := by
  simp [hessian,mul_add,sum_add_distrib]

lemma hessian_symm (x : σ → K) (F : MvPolynomial σ K) (u v : σ → K) :
    hessian x F u v = hessian x F v u := by
  unfold hessian
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [pderiv_swap F i j]
  ring

lemma tangent_expansion (g v : Option (Fin 2) → K)
    (hv : ∑ i, g i*v i = 0) :
    g none • v = v (some 0) • scaledTangent g 0 + v (some 1) • scaledTangent g 1 := by
  ext i
  cases i with
  | none =>
    simp only [Fintype.sum_option,Fin.sum_univ_two] at hv
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,scaledTangent,Option.elim_none]
    linear_combination hv
  | some i => fin_cases i <;> simp [scaledTangent,mul_comm]

lemma tangent_projection_independent (g : Option (Fin 2) → K) (hg : g none ≠ 0)
    (v : Fin 2 → Option (Fin 2) → K) (hv : ∀ a, ∑ i, g i*v a i = 0)
    (hli : LinearIndependent K v) :
    LinearIndependent K (fun a i => v a (some i)) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  apply hli c
  ext i
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp only [Fin.sum_univ_two,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at h0 h1 ⊢
  cases i with
  | some i => fin_cases i <;> assumption
  | none =>
    apply (mul_left_cancel₀ hg)
    rw [mul_zero]
    have h2 := hv 0
    have h3 := hv 1
    simp only [Fintype.sum_option,Fin.sum_univ_two] at h2 h3
    linear_combination c 0*h2+c 1*h3-g (some 0)*h0-g (some 1)*h1

lemma tangent_projection_det (g : Option (Fin 2) → K) (hg : g none ≠ 0)
    (u v : Option (Fin 2) → K) (hu : ∑ i, g i*u i = 0) (hv : ∑ i, g i*v i = 0)
    (hli : LinearIndependent K ![u,v]) :
    u (some 0)*v (some 1)-u (some 1)*v (some 0) ≠ 0 := by
  have hl := tangent_projection_independent g hg ![u,v]
    (fun i => by fin_cases i <;> assumption) hli
  let M : Matrix (Fin 2) (Fin 2) K := Matrix.of (fun i j => ![u,v] i (some j))
  have hM : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hl
  have hD := (Matrix.isUnit_iff_isUnit_det M).mp hM
  simpa [M,Matrix.det_fin_two,isUnit_iff_ne_zero] using hD

theorem three_lines_flat (F : MvPolynomial (Option (Fin 2)) K)
    (x : Option (Fin 2) → K) (v : Fin 3 → Option (Fin 2) → K)
    (h2 : (2 : K) ≠ 0) (hz : eval x (pderiv none F) ≠ 0)
    (hlines : ∀ i, restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2]) :
    ∀ a b, hessian x F (scaledTangent (fun i => eval x (pderiv i F)) a)
      (scaledTangent (fun i => eval x (pderiv i F)) b) = 0 := by
  let g : Option (Fin 2) → K := fun i => eval x (pderiv i F)
  let t := scaledTangent g
  have ht (i : Fin 3) : ∑ a, g a*v i a = 0 := line_tangent x (v i) F (hlines i)
  have hH (i : Fin 3) : hessian x F (v i) (v i) = 0 := line_hessian x (v i) F (hlines i)
  have he (i : Fin 3) := tangent_expansion g (v i) (ht i)
  have hq (i : Fin 3) :
      hessian x F (t 0) (t 0)*(v i (some 0))^2 +
        (2*hessian x F (t 0) (t 1))*(v i (some 0)*v i (some 1)) +
      hessian x F (t 1) (t 1)*(v i (some 1))^2 = 0 := by
    have E : hessian x F (g none • v i) (g none • v i) = 0 := by
      rw [hessian_smul_left,hessian_smul_right,hH,mul_zero,mul_zero]
    rw [he,hessian_add_left,hessian_add_right,hessian_add_right] at E
    simp only [hessian_smul_left,hessian_smul_right] at E
    rw [hessian_symm x F (t 1) (t 0)] at E
    linear_combination E
  obtain ⟨h00,h01',h11⟩ := binary_quadratic_three
    (fun i a => v i (some a)) _ _ _
    (tangent_projection_det g hz _ _ (ht 0) (ht 1) h01)
    (tangent_projection_det g hz _ _ (ht 0) (ht 2) h02)
    (tangent_projection_det g hz _ _ (ht 1) (ht 2) h12) hq
  have h01z := (mul_eq_zero.mp h01').resolve_left h2
  intro a b
  fin_cases a <;> fin_cases b
  · exact h00
  · exact h01z
  · exact (hessian_symm x F (t 1) (t 0)).trans h01z
  · exact h11

lemma three_lines_all_tangents (F : MvPolynomial (Option (Fin 2)) K)
    (x : Option (Fin 2) → K) (v : Fin 3 → Option (Fin 2) → K)
    (h2 : (2 : K) ≠ 0) (hz : eval x (pderiv none F) ≠ 0)
    (hlines : ∀ i, restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2])
    (u w : Option (Fin 2) → K)
    (hu : ∑ i, eval x (pderiv i F)*u i = 0)
    (hw : ∑ i, eval x (pderiv i F)*w i = 0) : hessian x F u w = 0 := by
  let g := fun i => eval x (pderiv i F)
  have H := three_lines_flat F x v h2 hz hlines h01 h02 h12
  apply mul_left_cancel₀ (mul_ne_zero hz hz)
  rw [mul_zero]
  calc
    _ = hessian x F (g none • u) (g none • w) := by
      rw [hessian_smul_left,hessian_smul_right]; ring
    _ = 0 := by
      rw [tangent_expansion g u hu,tangent_expansion g w hw,
        hessian_add_left,hessian_add_right,hessian_add_right]
      simp only [hessian_smul_left,hessian_smul_right,g,H,mul_zero,add_zero]

variable {τ : Type*} [Fintype τ] [DecidableEq τ]
omit [DecidableEq σ] [DecidableEq τ] in
lemma hessian_rename (e : σ ≃ τ) (F : MvPolynomial σ K) (x u v : τ → K) :
    hessian x (renameEquiv K e F) u v = hessian (x ∘ e) F (u ∘ e) (v ∘ e) := by
  unfold hessian
  rw [← e.sum_comp]
  apply sum_congr rfl
  intro j hj
  rw [← e.sum_comp]
  apply sum_congr rfl
  intro i hi
  simp only [renameEquiv_apply,pderiv_rename e.injective,eval_rename,Function.comp_apply]
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma restrictLine_rename (e : σ ≃ τ) (F : MvPolynomial σ K) (x v : τ → K) :
    restrictLine x v (renameEquiv K e F) = restrictLine (x ∘ e) (v ∘ e) F := by
  simp only [restrictLine,renameEquiv_apply,aeval_rename,Function.comp_def]
omit [DecidableEq σ] [DecidableEq τ] in

lemma tangent_rename (e : σ ≃ τ) (F : MvPolynomial σ K) (x v : τ → K) :
    (∑ i, eval x (pderiv i (renameEquiv K e F))*v i) =
      ∑ i, eval (x ∘ e) (pderiv i F)*(v ∘ e) i := by
  rw [← e.sum_comp]
  apply sum_congr rfl
  intro i hi
  simp only [renameEquiv_apply,pderiv_rename e.injective,eval_rename,Function.comp_apply]
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma independent_rename (e : σ ≃ τ) (u v : τ → K)
    (h : LinearIndependent K ![u,v]) : LinearIndependent K ![u ∘ e,v ∘ e] := by
  let E := LinearEquiv.funCongrLeft K K e
  have H := h.map' E.toLinearMap E.ker
  change LinearIndependent K (fun i => ![u,v] i ∘ e) at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  fin_cases i <;> rfl

theorem three_lines_tangent_zero (F : MvPolynomial (Fin 3) K)
    (x : Fin 3 → K) (v : Fin 3 → Fin 3 → K)
    (h2 : (2 : K) ≠ 0) (hn : ∃ i, eval x (pderiv i F) ≠ 0)
    (hlines : ∀ i, restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2])
    (u w : Fin 3 → K) (hu : ∑ i, eval x (pderiv i F)*u i = 0)
    (hw : ∑ i, eval x (pderiv i F)*w i = 0) : hessian x F u w = 0 := by
  obtain ⟨i,hi⟩ := hn
  let e : Option (Fin 2) ≃ Fin 3 := (finSuccEquiv' i).symm
  have hen : e none = i := finSuccEquiv'_symm_none i
  have hc (z : Fin 3 → K) : (z ∘ e) ∘ e.symm = z := by ext j; simp
  have hz : eval (x ∘ e) (pderiv none (renameEquiv K e.symm F)) ≠ 0 := by
    have he := pderiv_rename e.symm.injective i F
    have hnone : e.symm i = none := by rw [← hen]; simp
    rw [hnone] at he
    simpa only [renameEquiv_apply,he,eval_rename,hc] using hi
  have H := three_lines_all_tangents (renameEquiv K e.symm F) (x ∘ e)
    (fun j => v j ∘ e) h2 hz
    (fun j => by simpa only [restrictLine_rename,hc] using hlines j)
    (independent_rename e _ _ h01) (independent_rename e _ _ h02)
    (independent_rename e _ _ h12) (u ∘ e) (w ∘ e)
    (by simpa only [tangent_rename,hc] using hu)
    (by simpa only [tangent_rename,hc] using hw)
  simpa only [hessian_rename,hc] using H

end SharpLogRamsey.LineFlatness

end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ScaledTangentDot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators
open Finset MvPolynomial
namespace SharpLogRamsey.RichLinePolynomial
open MvPolynomial Finset
open FlatnessCore NonplaneCertificate
variable {K : Type*} [Field K]
lemma scaled_tangent_dot (g : Option (Fin 2) → K) (a : Fin 2) :
    ∑ i, g i*FlatnessCore.scaledTangent g a i = 0 := by
  simp [FlatnessCore.scaledTangent,Fintype.sum_option,mul_comm]

lemma eval_flatness (F : MvPolynomial (Option (Fin 2)) K) (x : Option (Fin 2) → K)
    (a b : Fin 2) : eval x (FlatnessCore.flatnessPolynomial F a b) =
    LineFlatness.hessian x F
      (FlatnessCore.scaledTangent (fun i => eval x (pderiv i F)) a)
      (FlatnessCore.scaledTangent (fun i => eval x (pderiv i F)) b) := by
  unfold FlatnessCore.flatnessPolynomial LineFlatness.hessian
  simp only [map_sum,map_mul]
  congr 1; ext j
  congr 1; ext i
  have he (a : Fin 2) (i : Option (Fin 2)) :
      eval x (FlatnessCore.scaledTangent (fun i => pderiv i F) a i) =
        FlatnessCore.scaledTangent (fun i => eval x (pderiv i F)) a i := by
    cases i with
    | none => simp [FlatnessCore.scaledTangent]
    | some i => by_cases hi : i = a <;> simp [FlatnessCore.scaledTangent,hi]
  rw [he,he]

theorem family_zero_at_three_lines (F : MvPolynomial (Fin 3) K)
    (x : Fin 3 → K) (v : Fin 3 → Fin 3 → K)
    (h2 : (2 : K) ≠ 0) (hl : ∀ i, LineFlatness.restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2]) (idx : Index) :
    eval x (flatFamily F idx) = 0 := by
  let e := idx.1
  let G := renameEquiv K e.symm F
  let y := x ∘ e
  let g := fun i => eval y (pderiv i G)
  have hc (z : Fin 3 → K) : (z ∘ e) ∘ e.symm = z := by ext i; simp
  have hge (i : Option (Fin 2)) : g i = eval x (pderiv (e i) F) := by
    have H := pderiv_rename e.symm.injective (e i) F
    simpa only [g,G,y,renameEquiv_apply,e.symm_apply_apply,eval_rename,hc] using congrArg (eval y) H
  change eval x (renameEquiv K e (flatnessPolynomial G idx.2.1 idx.2.2)) = 0
  rw [renameEquiv_apply,eval_rename,eval_flatness]
  change LineFlatness.hessian y G (FlatnessCore.scaledTangent g idx.2.1)
    (FlatnessCore.scaledTangent g idx.2.2) = 0
  by_cases hn : ∃ i, eval x (pderiv i F) ≠ 0
  · let u := FlatnessCore.scaledTangent g idx.2.1
    let w := FlatnessCore.scaledTangent g idx.2.2
    have hu : ∑ i, eval x (pderiv i F)*(u ∘ e.symm) i = 0 := by
      rw [← e.sum_comp]
      simpa only [Function.comp_apply,e.symm_apply_apply,← hge] using
        scaled_tangent_dot g idx.2.1
    have hw : ∑ i, eval x (pderiv i F)*(w ∘ e.symm) i = 0 := by
      rw [← e.sum_comp]
      simpa only [Function.comp_apply,e.symm_apply_apply,← hge] using
        scaled_tangent_dot g idx.2.2
    have H := LineFlatness.three_lines_tangent_zero F x v h2 hn hl h01 h02 h12
      (u ∘ e.symm) (w ∘ e.symm) hu hw
    simpa only [G,y,LineFlatness.hessian_rename,hc] using H
  · have hg : g = 0 := by
      ext i
      exact not_ne_iff.mp (fun h => hn ⟨e i,hge i ▸ h⟩)
    simp [hg,FlatnessCore.scaledTangent,LineFlatness.hessian]

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
omit [Fintype σ] [DecidableEq σ] in
lemma natDegree_aeval_linear (x : σ → Polynomial K)
    (hx : ∀ i, (x i).natDegree ≤ 1) (F : MvPolynomial σ K) :
    (aeval x F).natDegree ≤ F.totalDegree := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [aeval_monomial]
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.algebraMap_apply,Polynomial.natDegree_C,zero_add]
  calc
    _ ≤ ∑ i ∈ d.support, (x i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Polynomial.natDegree_pow]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d i) (hx i)
    _ ≤ F.totalDegree := le_totalDegree hd
omit [Fintype σ] [DecidableEq σ] in

lemma restriction_degree (x v : σ → K) (F : MvPolynomial σ K) :
    (LineFlatness.restrictLine x v F).natDegree ≤ F.totalDegree := by
  apply natDegree_aeval_linear
  intro i
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
    ((Polynomial.natDegree_mul_le).trans (by simp)))
omit [Fintype σ] [DecidableEq σ] in

lemma restriction_eval (x v : σ → K) (F : MvPolynomial σ K) (t : K) :
    (LineFlatness.restrictLine x v F).eval t = eval (fun i => x i+v i*t) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [LineFlatness.restrictLine]
  | add f g hf hg => simp_all [LineFlatness.restrictLine]
  | mul_X f i hf => simp_all [LineFlatness.restrictLine]
omit [Fintype σ] [DecidableEq σ] in

lemma restriction_zero_of_many (x v : σ → K) (F : MvPolynomial σ K)
    (S : Finset K) (hcard : F.totalDegree < S.card)
    (hzero : ∀ t ∈ S, eval (fun i => x i+v i*t) F = 0) :
    LineFlatness.restrictLine x v F = 0 := by
  by_contra hn
  have H : S.card ≤ (LineFlatness.restrictLine x v F).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    exact (Polynomial.mem_roots hn).mpr ((restriction_eval x v F t).trans (hzero t ht))
  exact (not_lt_of_ge (H.trans (restriction_degree x v F))) hcard

theorem auxiliary_polynomial {p : ℕ} [CharP K p] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hdeg : F.totalDegree < p)
    (hs : Squarefree F) (h2 : (2 : K) ≠ 0)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ Q : MvPolynomial (Fin 3) K, IsRelPrime F Q ∧ Q.totalDegree ≤ 3*F.totalDegree ∧
      ∀ (x v : Fin 3 → K) (S : Finset K), 3*F.totalDegree < S.card →
        (∀ t ∈ S, ∃ w : Fin 3 → Fin 3 → K,
          (∀ i, LineFlatness.restrictLine (fun j => x j+v j*t) (w i) F = 0) ∧
          LinearIndependent K ![w 0,w 1] ∧ LinearIndependent K ![w 0,w 2] ∧
          LinearIndependent K ![w 1,w 2]) → LineFlatness.restrictLine x v Q = 0 := by
  obtain ⟨c,hc,hd⟩ := exists_coprime_flat_combination F hF hdeg hs hn
  refine ⟨∑ i, c i • flatFamily F i,hc,hd,?_⟩
  intro x v S hS hpoints
  apply restriction_zero_of_many x v _ S (hd.trans_lt hS)
  intro t ht
  obtain ⟨w,hw,h01,h02,h12⟩ := hpoints t ht
  simp only [map_sum,Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,eval_C]
  apply sum_eq_zero
  intro i hi
  rw [family_zero_at_three_lines F _ w h2 hw h01 h02 h12 i,mul_zero]

end SharpLogRamsey.RichLinePolynomial

end

section

section

open scoped BigOperators nonZeroDivisors
open Polynomial Finset
namespace SharpLogRamsey.ParametricBezout

section Fraction
variable {R K : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

lemma isCoprime_map_fraction {f g : R[X]} (h : IsRelPrime f g) :
    IsCoprime (f.map (algebraMap R K)) (g.map (algebraMap R K)) := by
  apply isRelPrime_iff_isCoprime.mp
  intro a haf hag
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at haf hag
    have hf : f = 0 := (Polynomial.map_injective _ (IsFractionRing.injective R K))
      (by simpa using haf)
    have hg : g = 0 := (Polynomial.map_injective _ (IsFractionRing.injective R K))
      (by simpa using hag)
    rcases h.ne_zero_or_ne_zero with H|H <;> contradiction
  let b : R[X] := IsLocalization.integerNormalization R⁰ a
  have hb : b.primPart.IsPrimitive := Polynomial.isPrimitive_primPart b
  have hab : b.primPart.map (algebraMap R K) ∣ a := by
    have H := Polynomial.map_dvd (algebraMap R K) (Polynomial.primPart_dvd b)
    obtain ⟨c,hc,hbmap⟩ := IsLocalization.integerNormalization_spec R⁰ a
    change b.map (algebraMap R K) = _ at hbmap
    rw [hbmap,Algebra.smul_def,Polynomial.algebraMap_apply] at H
    have hc0 : algebraMap R K c ≠ 0 := by
      intro he
      apply nonZeroDivisors.ne_zero hc
      apply IsFractionRing.injective R K
      simpa using he
    exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr hc0))).mp H
  have hbf := hb.dvd_of_fraction_map_dvd_fraction_map (hab.trans haf)
  have hbg := hb.dvd_of_fraction_map_dvd_fraction_map (hab.trans hag)
  exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart ha (h hbf hbg)

include K in
lemma resultant_ne_zero_of_isRelPrime {f g : R[X]} (h : IsRelPrime f g) :
    f.resultant g ≠ 0 := by
  have hc := isCoprime_map_fraction (K := K) h
  have H := Polynomial.resultant_ne_zero _ _ hc
  have hf := Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R K) f
  have hg := Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R K) g
  rw [hf,hg,Polynomial.resultant_map_map] at H
  exact fun he => H (by rw [he,map_zero])
end Fraction

variable {K : Type*} [CommRing K] [IsDomain K] [NormalizedGCDMonoid K]
omit [IsDomain K] [NormalizedGCDMonoid K] in

lemma natDegree_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K[X]) (d : ι → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.natDegree ≤ ∑ j,d j := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply sum_le_sum
  intro i hi
  exact h (e i) i

omit [IsDomain K] [NormalizedGCDMonoid K] in

lemma resultant_degree_bound (f g : (K[X])[X]) (Df Dg : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg) :
    (f.resultant g).natDegree ≤ f.natDegree*Dg+g.natDegree*Df := by
  calc
    _ ≤ ∑ j : Fin (f.natDegree+g.natDegree),
        j.addCases (fun _ => Dg) (fun _ => Df) := by
      apply natDegree_det_le
      intro i j
      refine Fin.addCases ?_ ?_ j
      · intro j
        simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_left]
        split_ifs <;> simp_all
      · intro j
        simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_right]
        split_ifs <;> simp_all
    _ = _ := by rw [Fin.sum_univ_add]; simp

omit [IsDomain K] [NormalizedGCDMonoid K] in

lemma resultant_eval_zero (f g : (K[X])[X]) (x y : K)
    (hf : (f.map (Polynomial.evalRingHom x)).eval y = 0)
    (hg : (g.map (Polynomial.evalRingHom x)).eval y = 0)
    (hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) :
    (f.resultant g).eval x = 0 := by
  obtain ⟨a,b,ha,hb,H⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl hdeg
  have h := congrArg (fun p : (K[X])[X] => (p.map (Polynomial.evalRingHom x)).eval y) H
  simpa [hf,hg] using h.symm

lemma common_points_card_le (f g : (K[X])[X]) (Df Dg : ℕ)
    (hc : IsRelPrime f g)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg)
    (hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0)
    (S : Finset (K × K)) (hinj : Set.InjOn Prod.fst (S : Set (K × K)))
    (hS : ∀ z ∈ S, (f.map (Polynomial.evalRingHom z.1)).eval z.2 = 0 ∧
      (g.map (Polynomial.evalRingHom z.1)).eval z.2 = 0) :
    S.card ≤ f.natDegree*Dg+g.natDegree*Df := by
  classical
  have hne : f.resultant g ≠ 0 :=
    resultant_ne_zero_of_isRelPrime (K := FractionRing K[X]) hc
  calc
    S.card = (S.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (f.resultant g).natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      exact (Polynomial.mem_roots hne).mpr (resultant_eval_zero f g z.1 z.2
        (hS z hz).1 (hS z hz).2 hdeg)
    _ ≤ _ := resultant_degree_bound f g Df Dg hf hg
omit [NormalizedGCDMonoid K] in

lemma no_common_point_of_degree_zero (f g : (K[X])[X]) (hc : IsRelPrime f g)
    (hf : f.natDegree = 0) (hg : g.natDegree = 0) (x y : K)
    (hfx : (f.map (Polynomial.evalRingHom x)).eval y = 0)
    (hgx : (g.map (Polynomial.evalRingHom x)).eval y = 0) : False := by
  have hef := Polynomial.eq_C_of_natDegree_eq_zero hf
  have heg := Polynomial.eq_C_of_natDegree_eq_zero hg
  have hfr : (f.coeff 0).IsRoot x := by
    rw [hef] at hfx
    simpa only [Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom, Polynomial.IsRoot] using hfx
  have hgr : (g.coeff 0).IsRoot x := by
    rw [heg] at hgx
    simpa only [Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom, Polynomial.IsRoot] using hgx
  have hfd := map_dvd (Polynomial.C : K[X] →+* (K[X])[X])
    (Polynomial.dvd_iff_isRoot.mpr hfr)
  have hgd := map_dvd (Polynomial.C : K[X] →+* (K[X])[X])
    (Polynomial.dvd_iff_isRoot.mpr hgr)
  have hu : IsUnit (Polynomial.C (Polynomial.X-Polynomial.C x) : (K[X])[X]) := by
    apply hc
    · rwa [← hef] at hfd
    · rwa [← heg] at hgd
  exact Polynomial.not_isUnit_X_sub_C x (Polynomial.isUnit_C.mp hu)

theorem graph_branches_card_le (f g : (K[X])[X]) (Df Dg : ℕ)
    (hc : IsRelPrime f g)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg)
    (hfo : f.natDegree ≤ Df) (hgo : g.natDegree ≤ Dg)
    (S : Finset (K × K)) (hinj : Set.InjOn Prod.fst (S : Set (K × K)))
    (hS : ∀ z ∈ S, (f.map (Polynomial.evalRingHom z.1)).eval z.2 = 0 ∧
      (g.map (Polynomial.evalRingHom z.1)).eval z.2 = 0) :
    S.card ≤ 2*Df*Dg := by
  by_cases hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0
  · apply (common_points_card_le f g Df Dg hc hf hg hdeg S hinj hS).trans
    nlinarith
  · push Not at hdeg
    have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact no_common_point_of_degree_zero f g hc hdeg.1 hdeg.2 z.1 z.2
        (hS z hz).1 (hS z hz).2
    simp [he]

end SharpLogRamsey.ParametricBezout

end

section

namespace SharpLogRamsey.GenericCoordinates
open MvPolynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]
noncomputable section

lemma exists_eval_ne_zero {σ : Type*} (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, eval x F ≠ 0 := by
  by_contra! h
  apply hF
  exact MvPolynomial.funext (by simpa using h)

lemma exists_first (T : Finset (Fin 3 → K)) (hT : ∀ v ∈ T, v ≠ 0) :
    ∃ a b : K, ∀ v ∈ T, v 0+a*v 1+b*v 2 ≠ 0 := by
  classical
  let f (v : Fin 3 → K) : MvPolynomial (Fin 2) K :=
    C (v 0)+C (v 1)*X 0+C (v 2)*X 1
  have hf : ∀ v ∈ T, f v ≠ 0 := by
    intro v hv H
    have h0 := congrArg (eval (fun _ => (0:K))) H
    have h1 := congrArg (eval ![1,0]) H
    have h2 := congrArg (eval ![0,1]) H
    simp [f] at h0 h1 h2
    apply hT v hv
    ext i
    fin_cases i <;> simp_all
  obtain ⟨x,hx⟩ := exists_eval_ne_zero (∏ v ∈ T, f v) (Finset.prod_ne_zero_iff.mpr hf)
  refine ⟨x 0,x 1,?_⟩
  intro v hv H
  apply hx
  rw [map_prod]
  apply Finset.prod_eq_zero hv
  simp [f,H,mul_comm]

lemma exists_second (a b : K) (T : Finset (Fin 3 → K))
    (hT : ∀ v ∈ T, v ≠ 0)
    (hk : ∀ v ∈ T, v 0+a*v 1+b*v 2 = 0) :
    ∃ c : K, ∀ v ∈ T, v 1+c*v 2 ≠ 0 := by
  classical
  let f (v : Fin 3 → K) : MvPolynomial Unit K := C (v 1)+C (v 2)*X ()
  have hf : ∀ v ∈ T, f v ≠ 0 := by
    intro v hv H
    have h1 := congrArg (eval (fun _ => (0:K))) H
    have h2 := congrArg (eval (fun _ => (1:K))) H
    simp [f] at h1 h2
    have h0 := hk v hv
    apply hT v hv
    ext i
    fin_cases i <;> simp_all
  obtain ⟨x,hx⟩ := exists_eval_ne_zero (∏ v ∈ T, f v) (Finset.prod_ne_zero_iff.mpr hf)
  refine ⟨x (),?_⟩
  intro v hv H
  apply hx
  rw [map_prod]
  apply Finset.prod_eq_zero hv
  simp [f,H,mul_comm]

omit [Infinite K] in

lemma map_direction (t : (Fin 3 → K) →ₗ[K] K) (v : Fin 3 → K) (hv : t v ≠ 0) :
    t (direction t v) = 1 := by simp [direction,hv]
omit [Infinite K] in
lemma map_base (t : (Fin 3 → K) →ₗ[K] K) (x v : Fin 3 → K) (hv : t v ≠ 0) :
    t (base t x v) = 0 := by simp [base,map_direction t v hv]
omit [Infinite K] in

lemma line_normalize (t : (Fin 3 → K) →ₗ[K] K) (x v : Fin 3 → K) (hv : t v ≠ 0) :
    line (base t x v) (direction t v) = line x v := by
  ext y
  constructor
  · rintro ⟨r,rfl⟩
    refine ⟨(r-t x)*(t v)⁻¹,?_⟩
    ext i
    simp [base,direction]
    ring
  · rintro ⟨r,rfl⟩
    refine ⟨t x+r*t v,?_⟩
    ext i
    simp [base,direction]
    field_simp
    ; ring

theorem exists_separating_coordinates {ι : Type*} [Fintype ι]
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => line (x i) (v i))) :
    ∃ a b c : K, (∀ i, first a b (v i) ≠ 0) ∧
      Function.Injective (fun i =>
        Polynomial.C ((shear a b c (base (first a b) (x i) (v i))) 1)+
        Polynomial.C ((shear a b c (direction (first a b) (v i))) 1)*Polynomial.X) := by
  classical
  obtain ⟨a,b,hab⟩ := exists_first (Finset.univ.image v) (by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    exact hv i)
  have ht : ∀ i, first a b (v i) ≠ 0 := by
    intro i
    exact hab (v i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  let u := fun i => direction (first a b) (v i)
  let z := fun i => base (first a b) (x i) (v i)
  have hdistinct : ∀ i j, i ≠ j → z i ≠ z j ∨ u i ≠ u j := by
    intro i j hij
    by_contra! H
    apply hij
    apply hd
    change line (x i) (v i) = line (x j) (v j)
    rw [← line_normalize (first a b) (x i) (v i) (ht i),
      ← line_normalize (first a b) (x j) (v j) (ht j)]
    exact congrArg₂ line H.1 H.2
  let I := {ij : ι × ι // ij.1 ≠ ij.2}
  let w : I → Fin 3 → K := fun ij =>
    if z ij.val.1 ≠ z ij.val.2 then z ij.val.1-z ij.val.2 else u ij.val.1-u ij.val.2
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    change (if z i.val.1 ≠ z i.val.2 then z i.val.1-z i.val.2 else u i.val.1-u i.val.2) ≠ 0
    by_cases H : z i.val.1 ≠ z i.val.2
    · rw [ite_eq_left H]; exact sub_ne_zero.mpr H
    · rw [ite_eq_right H]; exact sub_ne_zero.mpr ((hdistinct _ _ i.property).resolve_left H)
  have hk : ∀ i, first a b (w i) = 0 := by
    intro i
    change first a b (if z i.val.1 ≠ z i.val.2 then z i.val.1-z i.val.2 else u i.val.1-u i.val.2) = 0
    by_cases H : z i.val.1 ≠ z i.val.2
    · rw [ite_eq_left H,map_sub,map_base _ _ _ (ht _),map_base _ _ _ (ht _),sub_self]
    · rw [ite_eq_right H,map_sub,map_direction _ _ (ht _),map_direction _ _ (ht _),sub_self]
  obtain ⟨c,hc⟩ := exists_second a b (Finset.univ.image w) (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hw i) (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hk i)
  refine ⟨a,b,c,ht,?_⟩
  intro i j H
  by_contra hij
  have h0 := congrArg (fun p : Polynomial K => p.coeff 0) H
  have h1 := congrArg (fun p : Polynomial K => p.coeff 1) H
  simp only [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_zero,mul_zero,add_zero,Polynomial.coeff_X_one,mul_one,
    zero_add,ite_true,ite_false,Nat.one_ne_zero] at h0 h1
  have Hc := hc (w ⟨(i,j),hij⟩) (Finset.mem_image.mpr ⟨⟨(i,j),hij⟩,Finset.mem_univ _,rfl⟩)
  apply Hc
  change (if z i ≠ z j then z i-z j else u i-u j) 1+
    c*(if z i ≠ z j then z i-z j else u i-u j) 2 = 0
  by_cases Hz : z i ≠ z j
  · rw [ite_eq_left Hz]
    change z i 1+c*z i 2 = z j 1+c*z j 2 at h0
    simp only [Pi.sub_apply]
    linear_combination h0
  · rw [ite_eq_right Hz]
    change u i 1+c*u i 2 = u j 1+c*u j 2 at h1
    simp only [Pi.sub_apply]
    linear_combination h1

end
end SharpLogRamsey.GenericCoordinates

end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Triple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
namespace SharpLogRamsey.PolynomialCoordinates
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section

lemma encode_natDegree (F : MvPolynomial (Fin 3) K) :
    (encode F).natDegree ≤ F.totalDegree := by
  simp only [encode,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv]
  rw [Polynomial.natDegree_map_eq_of_injective (AlgEquiv.injective _),natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree _ _).trans (totalDegree_rename_le _ _)

lemma coeff_degree_le {n : ℕ} (F : MvPolynomial (Fin (n+1)) K) (i : ℕ) :
    ((finSuccEquiv K n F).coeff i).totalDegree ≤ F.totalDegree := by
  by_cases h : (finSuccEquiv K n F).coeff i = 0
  · simp [h]
  · exact (Nat.le_add_right _ _).trans (totalDegree_coeff_finSuccEquiv_add_le F i h)

lemma encode_coeff_natDegree (F : MvPolynomial (Fin 3) K) (i : ℕ) :
    ((encode F).coeff i).natDegree ≤ F.totalDegree := by
  simp only [encode,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,Polynomial.coeff_map]
  change (Polynomial.map (uniqueAlgEquiv K (Fin 1)).toRingHom
    (finSuccEquiv K 1 (((finSuccEquiv K 2) ((renameEquiv K (Equiv.swap 0 2)) F)).coeff i))).natDegree ≤ F.totalDegree
  rw [Polynomial.natDegree_map_eq_of_injective (AlgEquiv.injective _),natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree _ _).trans
    ((coeff_degree_le _ i).trans (totalDegree_rename_le _ _))

lemma totalDegree_aeval_linear {σ τ : Type*} (x : τ → MvPolynomial σ K)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (F : MvPolynomial τ K) :
    (MvPolynomial.aeval x F).totalDegree ≤ F.totalDegree := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  apply le_trans (MvPolynomial.totalDegree_mul _ _)
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C,zero_add]
  calc
    _ ≤ ∑ i ∈ d.support, (x i ^ d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (MvPolynomial.totalDegree_pow _ _).trans
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d i) (hx i)
    _ ≤ F.totalDegree := MvPolynomial.le_totalDegree hd

lemma change_degree (a b c : K) (F : MvPolynomial (Fin 3) K) :
    (change a b c F).totalDegree ≤ F.totalDegree := by
  apply totalDegree_aeval_linear
  intro i
  fin_cases i
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_sub _ _).trans
      apply max_le (by simp)
      exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C,totalDegree_X]; omega)
    · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C,totalDegree_X]; omega)
  · apply (totalDegree_sub _ _).trans
    apply max_le (by simp)
    exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C,totalDegree_X]; omega)
  · simp

lemma eval_change (a b c : K) (w : Fin 3 → K) (F : MvPolynomial (Fin 3) K) :
    eval w (change a b c F) =
      eval ![w 0-a*w 1+(a*c-b)*w 2,w 1-c*w 2,w 2] F := by
  change eval w (changeHom a b c F) = _
  induction F using MvPolynomial.induction_on with
  | C r => simp [changeHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,hf]
    congr 1
    fin_cases i <;> simp [changeHom]

lemma eval_encode (y z : Polynomial K) (r : K) (F : MvPolynomial (Fin 3) K) :
    (((encode F).map (Polynomial.evalRingHom y)).eval z).eval r =
      eval ![r,y.eval r,z.eval r] F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add,Polynomial.map_add,Polynomial.eval_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,Polynomial.map_mul,Polynomial.eval_mul,hf]
    congr 1
    fin_cases i <;> simp

end
end SharpLogRamsey.PolynomialCoordinates

end

namespace SharpLogRamsey.CommonLines
open GenericCoordinates PolynomialCoordinates
variable {K : Type*} [Field K] [Infinite K]
noncomputable section

lemma coprime_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {F G : R} (h : IsRelPrime F G) : IsRelPrime (e F) (e G) := by
  intro a haf hag
  have hu := h (by simpa using map_dvd e.symm haf) (by simpa using map_dvd e.symm hag)
  simpa using hu.map e
omit [Infinite K] in

lemma eval_change_shear (a b c : K) (w : Fin 3 → K) (F : MvPolynomial (Fin 3) K) :
    MvPolynomial.eval (shear a b c w) (change a b c F) = MvPolynomial.eval w F := by
  rw [eval_change]
  apply congrArg (fun z : Fin 3 → K => MvPolynomial.eval z F)
  ext i
  fin_cases i <;> simp [shear] ; ring

lemma graph_zero (a b c : K) (x v : Fin 3 → K) (hv : first a b v ≠ 0)
    (F : MvPolynomial (Fin 3) K) (hF : ∀ r : K, MvPolynomial.eval (x+r • v) F = 0) :
    let U := direction (first a b) v
    let B := base (first a b) x v
    let Y := Polynomial.C ((shear a b c B) 1)+Polynomial.C ((shear a b c U) 1)*Polynomial.X
    let Z := Polynomial.C ((shear a b c B) 2)+Polynomial.C ((shear a b c U) 2)*Polynomial.X
    ((encode (change a b c F)).map (Polynomial.evalRingHom Y)).eval Z = 0 := by
  dsimp only
  apply Polynomial.funext
  intro r
  rw [Polynomial.eval_zero,eval_encode]
  let U := direction (first a b) v
  let B := base (first a b) x v
  have h0 : (shear a b c (B+r • U)) 0 = r := by
    change first a b (B+r • U) = r
    rw [map_add,map_smul,map_base _ _ _ hv,map_direction _ _ hv]
    simp
  have he : ![r,
      (Polynomial.C ((shear a b c B) 1)+Polynomial.C ((shear a b c U) 1)*Polynomial.X).eval r,
      (Polynomial.C ((shear a b c B) 2)+Polynomial.C ((shear a b c U) 2)*Polynomial.X).eval r] =
      shear a b c (B+r • U) := by
    ext i
    fin_cases i
    · exact h0.symm
    · change (Polynomial.C ((shear a b c B) 1)+Polynomial.C ((shear a b c U) 1)*Polynomial.X).eval r =
        (shear a b c (B+r • U)) 1
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    · change (Polynomial.C ((shear a b c B) 2)+Polynomial.C ((shear a b c U) 2)*Polynomial.X).eval r =
        (shear a b c (B+r • U)) 2
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [he,eval_change_shear]
  have hp : B+r • U ∈ line x v := by
    rw [← line_normalize (first a b) x v hv]
    exact ⟨r,rfl⟩
  obtain ⟨s,hs⟩ := hp
  rw [← hs]
  exact hF s

theorem card_le {ι : Type*} [Fintype ι]
    (F G : MvPolynomial (Fin 3) K) (hc : IsRelPrime F G)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => line (x i) (v i)))
    (hF : ∀ i (r : K), MvPolynomial.eval (x i+r • v i) F = 0)
    (hG : ∀ i (r : K), MvPolynomial.eval (x i+r • v i) G = 0) :
    Fintype.card ι ≤ 2*F.totalDegree*G.totalDegree := by
  classical
  obtain ⟨a,b,c,ht,hsep⟩ := exists_separating_coordinates x v hv hd
  let Y := fun i => Polynomial.C ((shear a b c (base (first a b) (x i) (v i))) 1)+
    Polynomial.C ((shear a b c (direction (first a b) (v i))) 1)*Polynomial.X
  let Z := fun i => Polynomial.C ((shear a b c (base (first a b) (x i) (v i))) 2)+
    Polynomial.C ((shear a b c (direction (first a b) (v i))) 2)*Polynomial.X
  let e : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (Polynomial (Polynomial K)) :=
    (change a b c).trans (encode (K := K))
  let S := Finset.univ.image (fun i => (Y i,Z i))
  have hpair : Function.Injective (fun i => (Y i,Z i)) := by
    intro i j H
    exact hsep (congrArg Prod.fst H)
  have hcard : S.card = Fintype.card ι := by simp [S,Finset.card_image_of_injective _ hpair]
  rw [← hcard]
  apply ParametricBezout.graph_branches_card_le (e F) (e G) F.totalDegree G.totalDegree
  · exact coprime_equiv (S := Polynomial (Polynomial (Polynomial K))) e.toRingEquiv hc
  · intro i
    exact (encode_coeff_natDegree (change a b c F) i).trans (change_degree a b c F)
  · intro i
    exact (encode_coeff_natDegree (change a b c G) i).trans (change_degree a b c G)
  · exact (encode_natDegree (change a b c F)).trans (change_degree a b c F)
  · exact (encode_natDegree (change a b c G)).trans (change_degree a b c G)
  · intro y hy z hz H
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    exact congrArg (fun i => (Y i,Z i)) (hsep H)
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨graph_zero a b c (x i) (v i) (ht i) F (hF i),
      graph_zero a b c (x i) (v i) (ht i) G (hG i)⟩

end
end SharpLogRamsey.CommonLines

end

section

namespace SharpLogRamsey.AffineIncidence
open Finset
open scoped BigOperators
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]
noncomputable section

lemma parametrization_injective (x v : Fin 3 → K) (hv : v ≠ 0) :
    Function.Injective (fun r : K => x+r • v) := by
  intro a b H
  exact (smul_left_injective K hv) (add_left_cancel H)

lemma rebase (x v y : Fin 3 → K) (hy : y ∈ carrier x v) :
    carrier y v = carrier x v := by
  obtain ⟨s,rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨r,rfl⟩
    refine ⟨s+r,?_⟩
    simp only [add_smul]
    abel
  · rintro ⟨r,rfl⟩
    refine ⟨r-s,?_⟩
    simp only [sub_smul]
    abel

lemma scale (x v : Fin 3 → K) (a : K) (ha : a ≠ 0) :
    carrier x (a • v) = carrier x v := by
  ext z
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨r*a,by simp [mul_smul]⟩
  · rintro ⟨r,rfl⟩
    exact ⟨r/a,by simp [smul_smul,ha]⟩
omit [Fintype ι] in

lemma independent_at_intersection (x v : ι → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (i j : ι) (hij : i ≠ j) (y : Fin 3 → K)
    (hi : y ∈ carrier (x i) (v i)) (hj : y ∈ carrier (x j) (v j)) :
    LinearIndependent K ![v i,v j] := by
  rw [linearIndependent_fin2]
  refine ⟨hv j,?_⟩
  intro a ha
  have ha0 : a ≠ 0 := by intro h; subst a; simp only [zero_smul] at ha; exact hv i ha.symm
  apply hij
  apply hd
  change carrier (x i) (v i) = carrier (x j) (v j)
  change a • v j = v i at ha
  rw [← rebase (x i) (v i) y hi,← rebase (x j) (v j) y hj,← ha,scale y (v j) a ha0]
omit [Fintype ι] in

lemma intersection_subsingleton (x v : ι → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (i j : ι) (hij : i ≠ j) :
    (carrier (x i) (v i) ∩ carrier (x j) (v j)).Subsingleton := by
  intro y hy z hz
  have hlin := independent_at_intersection x v hv hd i j hij y hy.1 hy.2
  have hzi : z ∈ carrier y (v i) := by rw [rebase (x i) (v i) y hy.1]; exact hz.1
  have hzj : z ∈ carrier y (v j) := by rw [rebase (x j) (v j) y hy.2]; exact hz.2
  obtain ⟨a,ha⟩ := hzi
  obtain ⟨b,hb⟩ := hzj
  have he : a • v i = b • v j := add_left_cancel (ha.trans hb.symm)
  have hc := hlin.eq_coords_of_eq (f := ![a,0]) (g := ![0,b])
    (by simpa using he) 0
  have ha0 : a = 0 := hc
  simpa [ha0] using ha
omit [Fintype ι] in

lemma points_intersection_le [DecidableEq K] (x v : ι → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (A : ι → Finset (Fin 3 → K)) (hA : ∀ i, (A i : Set _) ⊆ carrier (x i) (v i))
    (i j : ι) (hij : i ≠ j) : (A i ∩ A j).card ≤ 1 := by
  apply card_le_one.mpr
  intro y hy z hz
  exact intersection_subsingleton x v hv hd i j hij
    ⟨hA i (mem_inter.mp hy).1,hA j (mem_inter.mp hy).2⟩
    ⟨hA i (mem_inter.mp hz).1,hA j (mem_inter.mp hz).2⟩

variable (x v : ι → Fin 3 → K)

lemma split_points (S : Finset (Fin 3 → K)) (i : ι) :
    (richPoints x v S i).card+(poorPoints x v S i).card = (onLine x v S i).card := by
  classical
  simpa [richPoints,poorPoints,not_lt] using
    card_filter_add_card_filter_not (s := onLine x v S i) (p := fun y => 2 < (pencil x v y).card)

lemma poor_total (S : Finset (Fin 3 → K)) :
    (∑ i, (poorPoints x v S i).card) ≤ 2*S.card := by
  classical
  have he : (∑ i, (poorPoints x v S i).card) =
      ∑ y ∈ S, if (pencil x v y).card ≤ 2 then (pencil x v y).card else 0 := by
    simp only [poorPoints,onLine,filter_filter]
    simp only [card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro y hy
    by_cases H : (pencil x v y).card ≤ 2
    · simp only [H,and_true,ite_true]
      rw [show (pencil x v y).card = ∑ i, if y ∈ carrier (x i) (v i) then 1 else 0 by
        simp only [pencil,card_filter]]
    · simp only [H,and_false,ite_false,sum_const_zero]
  rw [he]
  calc
    _ ≤ ∑ _y ∈ S, 2 := by
      apply sum_le_sum
      intro y hy
      split_ifs with H
      · exact H
      · omega
    _ = 2*S.card := by simp [Nat.mul_comm]

theorem pruning_bound (S : Finset (Fin 3 → K)) (M D : ℕ)
    (hM : ∀ i, M ≤ (onLine x v S i).card) :
    let bad := Finset.univ.filter (fun i => (richPoints x v S i).card ≤ D)
    bad.card*(M-D) ≤ 2*S.card := by
  classical
  dsimp only
  calc
    _ = ∑ i ∈ univ.filter (fun i => (richPoints x v S i).card ≤ D), (M-D) := by simp
    _ ≤ ∑ i ∈ univ.filter (fun i => (richPoints x v S i).card ≤ D), (poorPoints x v S i).card := by
      apply sum_le_sum
      intro i hi
      have h := (mem_filter.mp hi).2
      have hs := split_points x v S i
      have hm := hM i
      omega
    _ ≤ ∑ i, (poorPoints x v S i).card := sum_le_sum_of_subset (filter_subset _ _)
    _ ≤ 2*S.card := poor_total x v S

end
end SharpLogRamsey.AffineIncidence

end

namespace SharpLogRamsey.NonplaneRichLines
open Finset MvPolynomial
open AffineIncidence
variable {K : Type*} [Field K] [Infinite K]
noncomputable section
omit [Infinite K] in

lemma eval_of_restrict_zero (x v : Fin 3 → K) (F : MvPolynomial (Fin 3) K)
    (h : LineFlatness.restrictLine x v F = 0) (y : Fin 3 → K)
    (hy : y ∈ carrier x v) : eval y F = 0 := by
  obtain ⟨t,rfl⟩ := hy
  have H := congrArg (fun p : Polynomial K => p.eval t) h
  rw [RichLinePolynomial.restriction_eval] at H
  have he : (fun i => x i+v i*t) = x+t • v := by ext i; simp [mul_comm]
  simpa only [he,Polynomial.eval_zero] using H

lemma restrict_zero_rebase (x v y : Fin 3 → K) (F : MvPolynomial (Fin 3) K)
    (h : LineFlatness.restrictLine x v F = 0) (hy : y ∈ carrier x v) :
    LineFlatness.restrictLine y v F = 0 := by
  apply Polynomial.funext
  intro r
  rw [RichLinePolynomial.restriction_eval,Polynomial.eval_zero]
  apply eval_of_restrict_zero x v F h
  rw [← rebase x v y hy]
  exact ⟨r,by ext i; simp [mul_comm]⟩

variable {ι : Type*} [Fintype ι]

lemma three_lines_at_rich (F : MvPolynomial (Fin 3) K)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (hF : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0)
    (y : Fin 3 → K) (hy : 2 < (pencil x v y).card) :
    ∃ w : Fin 3 → Fin 3 → K,
      (∀ i, LineFlatness.restrictLine y (w i) F = 0) ∧
      LinearIndependent K ![w 0,w 1] ∧ LinearIndependent K ![w 0,w 2] ∧
      LinearIndependent K ![w 1,w 2] := by
  classical
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp hy
  have ha' : y ∈ carrier (x a) (v a) := (mem_filter.mp ha).2
  have hb' : y ∈ carrier (x b) (v b) := (mem_filter.mp hb).2
  have hc' : y ∈ carrier (x c) (v c) := (mem_filter.mp hc).2
  refine ⟨![v a,v b,v c],?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact restrict_zero_rebase (x a) (v a) y F (hF a) ha'
    · exact restrict_zero_rebase (x b) (v b) y F (hF b) hb'
    · exact restrict_zero_rebase (x c) (v c) y F (hF c) hc'
  · exact independent_at_intersection x v hv hd a b hab y ha' hb'
  · exact independent_at_intersection x v hv hd a c hac y ha' hc'
  · exact independent_at_intersection x v hv hd b c hbc y hb' hc'
omit [Infinite K] in

lemma many_parameters (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (S : Finset (Fin 3 → K)) (i : ι) :
    ∃ T : Finset K, T.card = (richPoints x v S i).card ∧
      ∀ t ∈ T, 2 < (pencil x v (fun j => x i j+v i j*t)).card := by
  classical
  let f : K → Fin 3 → K := fun t => x i+t • v i
  let T := (richPoints x v S i).preimage f (parametrization_injective _ _ (hv i)).injOn
  refine ⟨T,?_,?_⟩
  · rw [card_preimage]
    congr 1
    apply filter_eq_self.mpr
    intro y hy
    exact (mem_filter.mp (mem_filter.mp hy).1).2
  · intro t ht
    have H := (mem_filter.mp (mem_preimage.mp ht)).2
    have he : f t = (fun j => x i j+v i j*t) := by ext j; simp [f,mul_comm]
    simpa only [he] using H

end
end SharpLogRamsey.NonplaneRichLines
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Card
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
namespace SharpLogRamsey.NonplaneRichLines
open Finset MvPolynomial
open AffineIncidence
variable {K : Type*} [Field K] [Infinite K]
noncomputable section
variable {ι : Type*} [Fintype ι]
theorem card_le {p : ℕ} [CharP K p] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hdeg : F.totalDegree < p)
    (hs : Squarefree F) (h2 : (2 : K) ≠ 0)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree ≤ 1 → IsUnit L)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (hzero : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0)
    (S : Finset (Fin 3 → K)) (M : ℕ) (hM : ∀ i, M ≤ (onLine x v S i).card)
    (hMD : 3*F.totalDegree < M) :
    Fintype.card ι ≤ 2*S.card/(M-3*F.totalDegree)+6*F.totalDegree^2 := by
  classical
  obtain ⟨Q,hQ,hQD,hQr⟩ := RichLinePolynomial.auxiliary_polynomial F hF hdeg hs h2 hn
  let bad := univ.filter (fun i => (richPoints x v S i).card ≤ 3*F.totalDegree)
  let good := univ.filter (fun i => 3*F.totalDegree < (richPoints x v S i).card)
  have hb : bad.card ≤ 2*S.card/(M-3*F.totalDegree) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    exact pruning_bound x v S M (3*F.totalDegree) hM
  have hgood : ∀ i ∈ good, LineFlatness.restrictLine (x i) (v i) Q = 0 := by
    intro i hi
    obtain ⟨T,hcard,hT⟩ := many_parameters x v hv S i
    apply hQr (x i) (v i) T (by rw [hcard]; exact (mem_filter.mp hi).2)
    intro t ht
    exact three_lines_at_rich F x v hv hd hzero _ (hT t ht)
  have hg : good.card ≤ 6*F.totalDegree^2 := by
    have H := CommonLines.card_le F Q hQ (fun i : good => x i) (fun i : good => v i)
      (fun i => hv i) (fun i j H => Subtype.ext (hd H))
      (fun i t => eval_of_restrict_zero _ _ F (hzero i) _ ⟨t,rfl⟩)
      (fun i t => eval_of_restrict_zero _ _ Q (hgood i i.property) _ ⟨t,rfl⟩)
    have H' : good.card ≤ 2*F.totalDegree*Q.totalDegree := by simpa using H
    calc
      _ ≤ 2*F.totalDegree*Q.totalDegree := H'
      _ ≤ 2*F.totalDegree*(3*F.totalDegree) := Nat.mul_le_mul_left _ hQD
      _ = 6*F.totalDegree^2 := by ring
  have hsplit : bad.card+good.card = Fintype.card ι := by
    simpa only [bad,good,not_le,card_univ] using
      card_filter_add_card_filter_not (s := univ) (p := fun i => (richPoints x v S i).card ≤ 3*F.totalDegree)
  omega

end
end SharpLogRamsey.NonplaneRichLines

section

namespace SharpLogRamsey.PlaneDecomposition
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section

lemma unit_of_degree_zero (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (h : F.totalDegree = 0) : IsUnit F := by
  have he := totalDegree_eq_zero_iff_eq_C.mp h
  have hc : F.coeff 0 ≠ 0 := by
    intro H
    apply hF
    rw [he,H,map_zero]
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

theorem exists_decomposition (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (hs : Squarefree F) :
    ∃ (planes : List (MvPolynomial (Fin 3) K)) (G : MvPolynomial (Fin 3) K),
      G ≠ 0 ∧ Squarefree G ∧ F = planes.prod*G ∧
      (∀ L ∈ planes, L.totalDegree = 1) ∧
      planes.Pairwise IsRelPrime ∧
      (∀ L ∈ planes, L ∣ F) ∧
      (∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) ∧
      planes.length+G.totalDegree = F.totalDegree := by
  classical
  suffices H : ∀ n (F : MvPolynomial (Fin 3) K), F.totalDegree = n → F ≠ 0 → Squarefree F →
    ∃ (planes : List (MvPolynomial (Fin 3) K)) (G : MvPolynomial (Fin 3) K),
      G ≠ 0 ∧ Squarefree G ∧ F = planes.prod*G ∧
      (∀ L ∈ planes, L.totalDegree = 1) ∧ planes.Pairwise IsRelPrime ∧
      (∀ L ∈ planes, L ∣ F) ∧
      (∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) ∧
      planes.length+G.totalDegree = F.totalDegree by
    exact H F.totalDegree F rfl hF hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hn hF hs
    by_cases hno : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree ≤ 1 → IsUnit L
    · exact ⟨[],F,hF,hs,by simp,by simp,by simp,by simp,hno,by simp⟩
    push Not at hno
    obtain ⟨L,hLF,hd,hnu⟩ := hno
    have hL : L ≠ 0 := ne_zero_of_dvd_ne_zero hF hLF
    have hdL : L.totalDegree = 1 := by
      have hn0 : L.totalDegree ≠ 0 := fun h => hnu (unit_of_degree_zero L hL h)
      omega
    obtain ⟨A,hFA⟩ := hLF
    have hA : A ≠ 0 := by
      intro H
      apply hF
      rw [hFA,H,mul_zero]
    have hde : F.totalDegree = 1+A.totalDegree := by
      rw [hFA,totalDegree_mul_of_isDomain hL hA,hdL]
    have hAl : A.totalDegree < n := by omega
    have hsq := squarefree_mul_iff.mp (hFA ▸ hs)
    obtain ⟨planes,G,hG,hGs,hAG,hplanes,hpair,hdiv,hng,hdeg⟩ :=
      ih A.totalDegree hAl A rfl hA hsq.2.2
    refine ⟨L::planes,G,hG,hGs,?_,?_,?_,?_,hng,?_⟩
    · simp only [List.prod_cons]
      rw [mul_assoc,← hAG,← hFA]
    · intro J hJ
      obtain rfl | hJ := List.mem_cons.mp hJ
      · exact hdL
      · exact hplanes J hJ
    · apply List.pairwise_cons.mpr
      exact ⟨fun J hJ => hsq.1.of_dvd_right (hdiv J hJ),hpair⟩
    · intro J hJ
      obtain rfl | hJ := List.mem_cons.mp hJ
      · exact ⟨A,hFA⟩
      · exact (hdiv J hJ).trans (hFA ▸ dvd_mul_left A L)
    · simp only [List.length_cons]
      omega

end
end SharpLogRamsey.PlaneDecomposition

end

section

namespace SharpLogRamsey.PlaneCount
open Finset
open scoped BigOperators
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq X]
noncomputable section
omit [DecidableEq ι] in

lemma incidence_sum (A : ι → Finset X) (U : Finset X) (hU : ∀ i, A i ⊆ U) :
    (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card) = ∑ i, (A i).card := by
  classical
  simp only [card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have H : U.filter (fun x => x ∈ A i) = A i := by
    ext x
    simp only [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hU i h,h⟩⟩
  rw [← card_filter,H]
omit [DecidableEq ι] in

lemma incidence_sq_sum (A : ι → Finset X) (U : Finset X) (hU : ∀ i, A i ⊆ U) :
    (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card^2) =
      ∑ i, ∑ j, (A i ∩ A j).card := by
  classical
  have he (x : X) : (univ.filter (fun i => x ∈ A i)).card^2 =
      ∑ i, ∑ j, if x ∈ A i ∧ x ∈ A j then (1:ℕ) else 0 := by
    simp only [card_filter,pow_two,sum_mul,mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    by_cases H : x ∈ A i <;> by_cases H' : x ∈ A j <;> simp [H,H']
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have H : U.filter (fun x => x ∈ A i ∧ x ∈ A j) = A i ∩ A j := by
    ext x
    simp only [mem_filter,mem_inter]
    exact ⟨fun h => h.2, fun h => ⟨hU i h.1,h⟩⟩
  rw [← card_filter,H]

theorem card_mul_le (A : ι → Finset X) (U : Finset X) (M K : ℕ)
    (hU : ∀ i, A i ⊆ U) (hM : ∀ i, (A i).card = M)
    (hi : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hK : U.card ≤ K) (hMK : 2*K ≤ M^2) (hM0 : 0 < M) :
    Fintype.card ι*M ≤ 2*K := by
  classical
  let u := Fintype.card ι
  have hs : (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card) = u*M := by
    rw [incidence_sum A U hU]
    simp [hM,u]
  have hs2 : (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card^2) ≤ u*(M+u) := by
    rw [incidence_sq_sum A U hU]
    calc
      _ ≤ ∑ i : ι, ∑ j : ι, ((if i = j then M else 0)+1) := by
        apply sum_le_sum; intro i _
        apply sum_le_sum; intro j _
        by_cases H : i = j
        · subst j; simp [hM]
        · simpa [H] using (hi i j H)
      _ = u*(M+u) := by simp [u,sum_add_distrib]
  have hcs := sq_sum_le_card_mul_sum_sq (s := U)
    (f := fun x => (univ.filter (fun i => x ∈ A i)).card)
  rw [hs] at hcs
  have H : (u*M)^2 ≤ K*(u*(M+u)) := hcs.trans (Nat.mul_le_mul hK hs2)
  by_cases hu : u = 0
  · change u*M ≤ 2*K
    simp [hu]
  have hu0 : 0 < u := Nat.pos_of_ne_zero hu
  have hcancel : u*M^2 ≤ K*(M+u) := by
    apply Nat.le_of_mul_le_mul_left (c := u)
    calc
      u*(u*M^2) = (u*M)^2 := by ring
      _ ≤ K*(u*(M+u)) := H
      _ = u*(K*(M+u)) := by ring
    exact hu0
  have hmid : u*M^2 ≤ 2*K*M := by nlinarith [Nat.mul_le_mul_left u hMK]
  change u*M ≤ 2*K
  apply Nat.le_of_mul_le_mul_right (c := M)
  · nlinarith
  · exact hM0

lemma exclusive_card (A : ι → Finset X) (i : ι)
    (hi : ∀ j, i ≠ j → (A i ∩ A j).card ≤ 1) :
    (A i).card ≤ (A i \ (univ.erase i).biUnion A).card+Fintype.card ι := by
  classical
  have he : A i ∩ (univ.erase i).biUnion A =
      (univ.erase i).biUnion (fun j => A i ∩ A j) := by
    ext x
    simp only [mem_inter,mem_biUnion]
    aesop
  have h : (A i ∩ (univ.erase i).biUnion A).card ≤ Fintype.card ι := by
    rw [he]
    calc
      _ ≤ ∑ j ∈ univ.erase i, (A i ∩ A j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ univ.erase i, 1 := by
        apply sum_le_sum
        intro j hj
        exact hi j (mem_erase.mp hj).1.symm
      _ ≤ Fintype.card ι := by simp
  have hs := card_sdiff_add_card_inter (A i) ((univ.erase i).biUnion A)
  omega

lemma exclusive_disjoint (A : ι → Finset X) :
    (↑(univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => A i \ (univ.erase i).biUnion A) := by
  classical
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro x hxi hxj
  have hxi' := mem_sdiff.mp hxi
  have hxj' := mem_sdiff.mp hxj
  apply hxi'.2
  apply mem_biUnion.mpr
  exact ⟨j,mem_erase.mpr ⟨hij.symm,mem_univ j⟩,hxj'.1⟩

theorem union_lower (A : ι → Finset X) (M : ℕ)
    (hM : ∀ i, M ≤ (A i).card)
    (hi : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) :
    Fintype.card ι*(M-Fintype.card ι) ≤ (univ.biUnion A).card := by
  classical
  let E := fun i => A i \ (univ.erase i).biUnion A
  calc
    _ = ∑ _i : ι, (M-Fintype.card ι) := by simp
    _ ≤ ∑ i, (E i).card := by
      apply sum_le_sum
      intro i _
      have H := exclusive_card A i (hi i)
      have hm := hM i
      dsimp [E]
      omega
    _ = (univ.biUnion E).card := (card_biUnion (exclusive_disjoint A)).symm
    _ ≤ (univ.biUnion A).card := by
      apply card_le_card
      intro x hx
      obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨i,hi,(mem_sdiff.mp hx).1⟩

end
end SharpLogRamsey.PlaneCount

namespace SharpLogRamsey.SinglePlaneCount
open Finset
open scoped BigOperators
variable {κ ι X : Type*} [Fintype κ] [Fintype ι] [DecidableEq X]
noncomputable section

theorem card_mul_le (A : ι → Finset X) (P : κ → Finset X) (owner : ι → κ)
    (U : Finset X) (M K : ℕ) (hM0 : 0 < M)
    (hM : ∀ i, (A i).card = M)
    (hAU : ∀ i, A i ⊆ P (owner i)) (hPU : ∀ j, P j ⊆ U)
    (hcap : ∀ j, (P j).card ≤ K)
    (hcross : ∀ i j, j ≠ owner i → (A i ∩ P j).card ≤ 1)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hKM : 8*K ≤ M^2) (hDM : 4*Fintype.card κ ≤ M) :
    Fintype.card ι*M ≤ 2*U.card := by
  classical
  let D := Fintype.card κ
  let Region (j : κ) := P j \ (univ.erase j).biUnion P
  let u (j : κ) := Fintype.card {i : ι // owner i = j}
  have hu (j : κ) : 4*u j ≤ M := by
    have H := PlaneCount.card_mul_le (fun i : {i : ι // owner i = j} => A i.val)
      (P j) M K (by intro i; simpa [i.property] using hAU i.val)
      (fun i => hM i.val) (fun i k hik => hpair i.val k.val (by intro he; exact hik (Subtype.ext he)))
      (hcap j) (by omega) hM0
    change u j*M ≤ 2*K at H
    apply Nat.le_of_mul_le_mul_right (c := M)
    · nlinarith
    · exact hM0
  have hlocal (j : κ) : u j*M ≤ 2*(Region j).card := by
    let E : {i : ι // owner i = j} → Finset X := fun i => A i.val \ (univ.erase j).biUnion P
    have hEc (i : {i : ι // owner i = j}) : M-D ≤ (E i).card := by
      have he : A i.val ∩ (univ.erase j).biUnion P =
          (univ.erase j).biUnion (fun k => A i.val ∩ P k) := by
        ext a
        simp only [mem_inter,mem_biUnion]
        aesop
      have H : (A i.val ∩ (univ.erase j).biUnion P).card ≤ D := by
        rw [he]
        calc
          _ ≤ ∑ k ∈ univ.erase j, (A i.val ∩ P k).card := card_biUnion_le
          _ ≤ ∑ _k ∈ univ.erase j, 1 := by
            apply sum_le_sum
            intro k hk
            apply hcross
            simpa [i.property] using (mem_erase.mp hk).1
          _ ≤ D := by simp [D]
      have H' := card_sdiff_add_card_inter (A i.val) ((univ.erase j).biUnion P)
      rw [hM] at H'
      change M-D ≤ (A i.val \ (univ.erase j).biUnion P).card
      omega
    have hE (i : {i : ι // owner i = j}) : E i ⊆ Region j := by
      intro a ha
      obtain ⟨ha,hn⟩ := mem_sdiff.mp ha
      apply mem_sdiff.mpr
      exact ⟨by simpa [i.property] using hAU i.val ha,hn⟩
    have hp (i k : {i : ι // owner i = j}) (hik : i ≠ k) : (E i ∩ E k).card ≤ 1 := by
      apply le_trans (card_le_card ?_) (hpair i.val k.val (by intro he; exact hik (Subtype.ext he)))
      intro a ha
      exact mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp ha).1).1,(mem_sdiff.mp (mem_inter.mp ha).2).1⟩
    have H := PlaneCount.union_lower E (M-D) hEc hp
    have H' : (univ.biUnion E).card ≤ (Region j).card := by
      apply card_le_card
      intro a ha
      obtain ⟨i,hi,ha⟩ := mem_biUnion.mp ha
      exact hE i ha
    have hnum : M ≤ 2*(M-D-u j) := by
      have h1 := hu j
      change 4*D ≤ M at hDM
      omega
    change u j*(M-D-u j) ≤ (univ.biUnion E).card at H
    nlinarith [Nat.mul_le_mul_left (u j) hnum]
  have hregions : (↑(univ : Finset κ) : Set κ).PairwiseDisjoint Region :=
    PlaneCount.exclusive_disjoint P
  have hregionU : univ.biUnion Region ⊆ U := by
    intro a ha
    obtain ⟨j,hj,ha⟩ := mem_biUnion.mp ha
    exact hPU j (mem_sdiff.mp ha).1
  have hsumu : ∑ j, u j = Fintype.card ι := by
    simp only [u,Fintype.card_subtype]
    exact (card_eq_sum_card_fiberwise (s := (univ : Finset ι)) (t := univ)
      (by intro _ _; exact mem_univ _)).symm
  calc
    _ = ∑ j, u j*M := by rw [← sum_mul,hsumu]
    _ ≤ ∑ j, 2*(Region j).card := sum_le_sum (fun j _ => hlocal j)
    _ = 2*(univ.biUnion Region).card := by rw [card_biUnion hregions,mul_sum]
    _ ≤ 2*U.card := Nat.mul_le_mul_left _ (card_le_card hregionU)

end
end SharpLogRamsey.SinglePlaneCount

end

namespace SharpLogRamsey.SurfaceRichLines
open MvPolynomial Finset AffineIncidence
open scoped BigOperators Classical
variable {K : Type*} [Field K] [Infinite K]
noncomputable section
omit [Infinite K] in

lemma plane_crossing (S : Finset (Fin 3 → K)) (x v : Fin 3 → K) (hv : v ≠ 0)
    (L : MvPolynomial (Fin 3) K) (hL : L.totalDegree ≤ 1)
    (hn : LineFlatness.restrictLine x v L ≠ 0) :
    (S.filter (fun y => y ∈ carrier x v ∧ eval y L = 0)).card ≤ 1 := by
  classical
  let A := S.filter (fun y => y ∈ carrier x v ∧ eval y L = 0)
  let f : K → Fin 3 → K := fun t => x+t • v
  let T := A.preimage f (parametrization_injective _ _ hv).injOn
  have hc : T.card = A.card := by
    rw [card_preimage]
    congr 1
    apply filter_eq_self.mpr
    intro y hy
    exact (mem_filter.mp hy).2.1
  have H : T.card ≤ (LineFlatness.restrictLine x v L).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    apply (Polynomial.mem_roots hn).mpr
    change Polynomial.eval t (LineFlatness.restrictLine x v L) = 0
    rw [RichLinePolynomial.restriction_eval]
    have H := (mem_filter.mp (mem_preimage.mp ht)).2.2
    have he : f t = (fun j => x j+v j*t) := by ext j; simp [f,mul_comm]
    simpa only [he] using H
  rw [hc] at H
  exact H.trans ((RichLinePolynomial.restriction_degree x v L).trans hL)

variable {ι : Type*} [Fintype ι]

theorem card_le {p : ℕ} [CharP K p] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hdeg : F.totalDegree < p)
    (hs : Squarefree F) (h2 : (2 : K) ≠ 0)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (hzero : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0)
    (S : Finset (Fin 3 → K)) (M Kp : ℕ)
    (hM : ∀ i, M ≤ (onLine x v S i).card)
    (hcap : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree = 1 →
      (S.filter (fun y => eval y L = 0)).card ≤ Kp)
    (hMD : 6*F.totalDegree < M) (hKM : 8*Kp ≤ M^2) :
    Fintype.card ι ≤ 2*S.card/M+2*S.card/(M-3*F.totalDegree)+8*F.totalDegree^2 := by
  classical
  obtain ⟨planes,G,hG,hGs,hprod,hplanes,hpair,hdiv,hng,hde⟩ :=
    PlaneDecomposition.exists_decomposition F hF hs
  let κ := Fin planes.length
  let L : κ → MvPolynomial (Fin 3) K := planes.get
  have hLd (j : κ) : (L j).totalDegree = 1 := hplanes _ (List.get_mem planes j)
  have hLdiv (j : κ) : L j ∣ F := hdiv _ (List.get_mem planes j)
  have hLc (j k : κ) (hjk : j ≠ k) : IsRelPrime (L j) (L k) := by
    rcases lt_or_gt_of_ne hjk with H | H
    · exact hpair.rel_get_of_lt H
    · exact (hpair.rel_get_of_lt H).symm
  let On : ι → κ → Prop := fun i j => LineFlatness.restrictLine (x i) (v i) (L j) = 0
  let multiple : Finset ι := univ.filter (fun i => ∃ j k, j ≠ k ∧ On i j ∧ On i k)
  let single : Finset ι := univ.filter (fun i => (∃ j, On i j) ∧ i ∉ multiple)
  let none : Finset ι := univ.filter (fun i => ¬∃ j, On i j)
  have hm : multiple.card ≤ 2*F.totalDegree^2 := by
    let Both (j k : κ) := univ.filter (fun i => On i j ∧ On i k)
    have hB (j k : κ) (hjk : j ≠ k) : (Both j k).card ≤ 2 := by
      have H := CommonLines.card_le (L j) (L k) (hLc j k hjk)
        (fun i : Both j k => x i) (fun i : Both j k => v i) (fun i => hv i)
        (fun i l H => Subtype.ext (hd H))
        (fun i t => NonplaneRichLines.eval_of_restrict_zero _ _ _ (mem_filter.mp i.property).2.1 _ ⟨t,rfl⟩)
        (fun i t => NonplaneRichLines.eval_of_restrict_zero _ _ _ (mem_filter.mp i.property).2.2 _ ⟨t,rfl⟩)
      simpa only [Fintype.card_coe,hLd,mul_one] using H
    have hc : multiple ⊆ univ.biUnion (fun j : κ => (univ.erase j).biUnion (Both j)) := by
      intro i hi
      obtain ⟨j,k,hjk,hj,hk⟩ := (mem_filter.mp hi).2
      exact mem_biUnion.mpr ⟨j,mem_univ j,mem_biUnion.mpr
        ⟨k,mem_erase.mpr ⟨hjk.symm,mem_univ k⟩,mem_filter.mpr ⟨mem_univ i,hj,hk⟩⟩⟩
    calc
      _ ≤ (univ.biUnion (fun j : κ => (univ.erase j).biUnion (Both j))).card := card_le_card hc
      _ ≤ ∑ j : κ, ((univ.erase j).biUnion (Both j)).card := card_biUnion_le
      _ ≤ ∑ j : κ, ∑ k ∈ univ.erase j, 2 := by
        apply sum_le_sum
        intro j hj
        apply le_trans card_biUnion_le
        apply sum_le_sum
        intro k hk
        exact hB j k (mem_erase.mp hk).1.symm
      _ ≤ 2*planes.length^2 := by
        simp only [sum_const, Nat.nsmul_eq_mul, card_erase_of_mem (mem_univ _), card_univ]
        have H : planes.length - 1 ≤ planes.length := Nat.sub_le _ _
        dsimp [κ]
        simp only [Fintype.card_fin]
        nlinarith [Nat.mul_le_mul_left planes.length H]
      _ ≤ 2*F.totalDegree^2 := by nlinarith
  have hsing : single.card ≤ 2*S.card/M := by
    have howner : ∀ i : single, ∃ j, On i.val j := fun i => (mem_filter.mp i.property).2.1
    choose owner ho using howner
    have hchoices : ∀ i : single, ∃ A ⊆ onLine x v S i.val, A.card = M :=
      fun i => exists_subset_card_eq (hM i.val)
    choose A hA hAc using hchoices
    let P : κ → Finset (Fin 3 → K) := fun j => S.filter (fun y => eval y (L j) = 0)
    have hAP (i : single) : A i ⊆ P (owner i) := by
      intro y hy
      have hy' := mem_filter.mp (hA i hy)
      apply mem_filter.mpr
      exact ⟨hy'.1,NonplaneRichLines.eval_of_restrict_zero _ _ _ (ho i) y hy'.2⟩
    have hc (i : single) (j : κ) (hj : j ≠ owner i) : (A i ∩ P j).card ≤ 1 := by
      have hn : ¬On i.val j := by
        intro H
        exact (mem_filter.mp i.property).2.2 (mem_filter.mpr ⟨mem_univ i.val,
          j,owner i,hj,H,ho i⟩)
      apply le_trans (card_le_card ?_) (plane_crossing S (x i) (v i) (hv i) (L j) (hLd j).le hn)
      intro y hy
      have hAi := mem_filter.mp (hA i (mem_inter.mp hy).1)
      exact mem_filter.mpr ⟨hAi.1,hAi.2,(mem_filter.mp (mem_inter.mp hy).2).2⟩
    have hp (i k : single) (hik : i ≠ k) : (A i ∩ A k).card ≤ 1 := by
      exact points_intersection_le (fun i : single => x i) (fun i : single => v i)
        (fun i => hv i) (fun i k H => Subtype.ext (hd H)) A
        (fun i _ hy => (mem_filter.mp (hA i hy)).2) i k hik
    have H := SinglePlaneCount.card_mul_le A P owner S M Kp (by omega) hAc hAP
      (fun j => filter_subset _ _) (fun j => hcap (L j) (hLdiv j) (hLd j)) hc hp hKM
      (by simp only [κ,Fintype.card_fin]; omega)
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    simpa only [Fintype.card_coe] using H
  have hn : none.card ≤ 2*S.card/(M-3*F.totalDegree)+6*F.totalDegree^2 := by
    have hz (i : none) : LineFlatness.restrictLine (x i) (v i) G = 0 := by
      let φ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
        aeval (fun j => Polynomial.C (x i j)+Polynomial.C (v i j)*Polynomial.X)
      have H : φ F = 0 := hzero i
      rw [hprod,map_mul] at H
      apply (mul_eq_zero.mp H).resolve_left
      intro hp0
      rw [map_list_prod,List.prod_eq_zero_iff,List.mem_map] at hp0
      obtain ⟨J,hJ,hφJ⟩ := hp0
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hJ
      exact (mem_filter.mp i.property).2 ⟨j,hφJ⟩
    have H := NonplaneRichLines.card_le G hG (by omega) hGs h2 hng
      (fun i : none => x i) (fun i : none => v i) (fun i => hv i)
      (fun i k H => Subtype.ext (hd H)) hz S M (fun i => hM i) (by omega)
    have H' : none.card ≤ 2*S.card/(M-3*G.totalDegree)+6*G.totalDegree^2 := by
      simpa only [Fintype.card_coe] using H
    apply H'.trans
    apply Nat.add_le_add
    · exact Nat.div_le_div_left (by omega) (by omega)
    · nlinarith
  have hsplit : Fintype.card ι ≤ single.card+multiple.card+none.card := by
    have H : (univ : Finset ι) ⊆ single ∪ multiple ∪ none := by
      intro i hi
      by_cases he : ∃ j, On i j
      · by_cases hm : i ∈ multiple
        · exact mem_union_left _ (mem_union_right _ hm)
        · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi,he,hm⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hi,he⟩)
    have H' := (card_le_card H).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    simpa only [card_univ] using H'
  omega

end
end SharpLogRamsey.SurfaceRichLines

end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PencilGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] in

lemma radialFiber_disjoint (S : Finset (Projectivization K V)) (x : Projectivization K V)
    {W U : RadialLine x} (hne : W ≠ U) : Disjoint (radialFiber S x W) (radialFiber S x U) := by
  apply Finset.disjoint_left.mpr
  intro y hyW hyU
  obtain ⟨_, hyx, hyW⟩ := (mem_radialFiber S x y W).mp hyW
  have hyU := ((mem_radialFiber S x y U).mp hyU).2.2
  exact hne (Subtype.ext ((radial_unique x y hyx.symm W hyW).symm.trans
    (radial_unique x y hyx.symm U hyU)))

lemma radial_biUnion (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) :
    (Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U)).biUnion (radialFiber S x) =
      S.filter (fun y => y ≠ x ∧ y.submodule ≤ U) := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_radialFiber]
  constructor
  · rintro ⟨W, hWU, hyS, hyx, hyW⟩
    exact ⟨hyS, hyx, hyW.trans hWU⟩
  · rintro ⟨hyS, hyx, hyU⟩
    refine ⟨⟨x.submodule ⊔ y.submodule, finrank_join x y hyx.symm, le_sup_left⟩,
      sup_le hx hyU, hyS, hyx, le_sup_right⟩

theorem radial_count (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) :
    ∑ W ∈ Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U), (radialFiber S x W).card =
      (S.filter (fun y => y ≠ x ∧ y.submodule ≤ U)).card := by
  rw [← Finset.card_biUnion, radial_biUnion S x U hx]
  intro W _ U _ hne
  exact radialFiber_disjoint S x hne

theorem radial_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) (c : ℝ) :
    ∑ W ∈ Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U), c*(radialFiber S x W).card =
      c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ U)).card := by
  rw [← Finset.mul_sum, ← Nat.cast_sum, radial_count S x U hx]

end
end SharpLogRamsey.PreparedProjectiveGeometry

open Finset Classical

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_RadialPairCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.RadialPairCount
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α ι : Type*}

theorem rich_lines (C : Finset α) (F : Finset ι) (L : ι → Finset α) (r : ℕ)
    (hr : ∀ i ∈ F, r ≤ (C ∩ L i).card)
    (hunique : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → (L i ∩ L j).card ≤ 1) :
    F.card * (r*(r-1)) ≤ C.card^2 := by
  have hd : (↑F : Set ι).PairwiseDisjoint (fun i => (C ∩ L i).offDiag) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro z hzi hzj
    have hi' := mem_offDiag.mp hzi
    have hj' := mem_offDiag.mp hzj
    have htwo : 1 < (L i ∩ L j).card := one_lt_card.mpr
      ⟨z.1, mem_inter.mpr ⟨(mem_inter.mp hi'.1).2,(mem_inter.mp hj'.1).2⟩,
       z.2, mem_inter.mpr ⟨(mem_inter.mp hi'.2.1).2,(mem_inter.mp hj'.2.1).2⟩,hi'.2.2⟩
    exact (not_lt_of_ge (hunique i hi j hj hij)) htwo
  calc
    F.card*(r*(r-1)) = ∑ _i ∈ F, r*(r-1) := by simp
    _ ≤ ∑ i ∈ F, (C ∩ L i).offDiag.card := by
      apply sum_le_sum
      intro i hi
      rw [offDiag_card,← Nat.mul_sub_one]
      exact Nat.mul_le_mul (hr i hi) (Nat.sub_le_sub_right (hr i hi) 1)
    _ = (F.biUnion (fun i => (C ∩ L i).offDiag)).card := (card_biUnion hd).symm
    _ ≤ (C ×ˢ C).card := card_le_card (by
      intro z hz
      obtain ⟨i,hi,hz⟩ := mem_biUnion.mp hz
      have hz' := mem_offDiag.mp hz
      exact mem_product.mpr ⟨(mem_inter.mp hz'.1).1,(mem_inter.mp hz'.2.1).1⟩)
    _ = C.card^2 := by simp [pow_two]

theorem weighted_square_sum (m : ℕ) (c : Fin m → ℕ)
    (hc : Antitone c) :
    (∑ i, (i.val+1)*(c i)^2) ≤ (∑ i, c i)^2 := by
  have hterm (i : Fin m) : (i.val+1)*(c i)^2 ≤
      c i * ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), c j := by
    have hcard : (Finset.univ.filter (fun j : Fin m => j ≤ i)).card = i.val+1 := by
      have he : Finset.univ.filter (fun j : Fin m => j ≤ i) = Finset.Iic i := by ext j; simp
      rw [he]
      exact Fin.card_Iic i
    calc
      (i.val+1)*(c i)^2 = (c i)*((Finset.univ.filter (fun j : Fin m => j ≤ i)).card*c i) := by
        rw [hcard]; ring
      _ = c i*(∑ _j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), c i) := by simp
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        apply sum_le_sum
        intro j hj
        exact hc (mem_filter.mp hj).2
  calc
    _ ≤ ∑ i, c i * ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), c j :=
      sum_le_sum (fun i _ => hterm i)
    _ ≤ ∑ i, c i * ∑ j, c j := by
      apply sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset (filter_subset _ _))
    _ = _ := by rw [← sum_mul]; ring

theorem centered_rich_lines {m : ℕ} (C : Fin m → Finset α)
    (F : Fin m → Finset ι) (L : ι → Finset α) (centers : Fin m → ι → Finset α)
    (r : ℕ) (hr : ∀ i j, j ∈ F i → r ≤ (C i ∩ L j).card)
    (hunique : ∀ i ∈ univ.biUnion F, ∀ j ∈ univ.biUnion F,
      i ≠ j → (L i ∩ L j).card ≤ 1)
    (hcenter : ∀ i j, j ∈ F i → (centers i j).card ≤ i.val)
    (hmono : Antitone (fun i => (C i).card)) :
    ((univ.biUnion (fun i => (F i).biUnion (fun j => centers i j ×ˢ {j}))).card)*
      (r*(r-1)) ≤ (∑ i, (C i).card)^2 := by
  have hcount (i : Fin m) : ((F i).biUnion (fun j => centers i j ×ˢ {j})).card ≤
      i.val*(F i).card := by
    apply (card_biUnion_le).trans
    calc
      (∑ j ∈ F i, (centers i j ×ˢ {j}).card) ≤ ∑ _j ∈ F i, i.val := by
        apply sum_le_sum
        intro j hj
        simpa using hcenter i j hj
      _ = _ := by simp [mul_comm]
  calc
    _ ≤ (∑ i, ((F i).biUnion (fun j => centers i j ×ˢ {j})).card)*(r*(r-1)) :=
      Nat.mul_le_mul_right _ card_biUnion_le
    _ ≤ (∑ i, i.val*(F i).card)*(r*(r-1)) :=
      Nat.mul_le_mul_right _ (sum_le_sum (fun i _ => hcount i))
    _ = ∑ i, i.val*((F i).card*(r*(r-1))) := by
      rw [sum_mul]; apply sum_congr rfl; intros; ring
    _ ≤ ∑ i, (i.val+1)*(C i).card^2 := by
      apply sum_le_sum
      intro i _
      apply Nat.mul_le_mul (by omega)
      apply rich_lines (C i) (F i) L r (hr i)
      intro a ha b hb hab
      exact hunique a (mem_biUnion.mpr ⟨i,mem_univ _,ha⟩)
        b (mem_biUnion.mpr ⟨i,mem_univ _,hb⟩) hab
    _ ≤ _ := weighted_square_sum m (fun i => (C i).card) hmono

end
end SharpLogRamsey.RadialPairCount

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_VectorMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
namespace SharpLogRamsey.ProjectiveBaseChange
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

lemma pointMap_injective : Function.Injective (pointMap (K := K) (E := E) (n := n)) := by
  intro P Q h
  induction P using Projectivization.ind with | h p hp =>
    induction Q using Projectivization.ind with | h q hq =>
      simp only [pointMap, Projectivization.map_mk, Projectivization.mk_eq_mk_iff'] at h ⊢
      obtain ⟨c,hc⟩ := h
      obtain ⟨i,hi⟩ : ∃ i, q i ≠ 0 := by simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hq
      have hqi : algebraMap K E (q i) ≠ 0 := (map_ne_zero (algebraMap K E)).mpr hi
      have hci : c = algebraMap K E (p i / q i) := by
        have he := congrFun hc i
        simp only [Pi.smul_apply, smul_eq_mul, vectorSemi_apply] at he
        rw [map_div₀]
        exact (eq_div_iff hqi).mpr he
      refine ⟨p i / q i, ?_⟩
      ext j
      apply (algebraMap K E).injective
      have he := congrFun hc j
      simpa only [hci, map_mul, Pi.smul_apply, smul_eq_mul, vectorSemi_apply] using he

lemma coordinate_decomposition (v : Fin n → K) :
    (∑ i, v i • Pi.single i (1 : K)) = v := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

lemma extendDual_map (f : (Fin n → K) →ₗ[K] K) (v : Fin n → K) :
    extendDual (E := E) f (vectorMap v) = algebraMap K E (f v) := by
  have hf : f v = ∑ i, v i*f (Pi.single i 1) := by
    conv_lhs => rw [← coordinate_decomposition v]
    simp
  rw [hf, map_sum]
  simp only [extendDual, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, vectorMap_apply, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mem_extendSpace (W : Submodule K (Fin n → K)) (v : Fin n → K) :
    vectorMap (E := E) v ∈ extendSpace (E := E) W ↔ v ∈ W := by
  constructor
  · intro hv
    by_contra hn
    obtain ⟨f,hf,hfW⟩ := W.exists_dual_map_eq_bot_of_notMem hn inferInstance
    have hW : extendSpace (E := E) W ≤ LinearMap.ker (extendDual (E := E) f) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨w,hw,rfl⟩
      change extendDual f (vectorMap w) = 0
      rw [extendDual_map]
      have hh : f w = 0 := by
        have hm : f w ∈ W.map f := Submodule.mem_map.mpr ⟨w,hw,rfl⟩
        simpa only [hfW, Submodule.mem_bot] using hm
      simp [hh]
    have he := hW hv
    rw [LinearMap.mem_ker, extendDual_map] at he
    exact hf ((algebraMap K E).injective (by simpa using he))
  · intro hv
    exact Submodule.subset_span ⟨v,hv,rfl⟩

theorem rational_hyperplane (f : (Fin n → E) →ₗ[E] E) (hf : f ≠ 0) :
    ∃ g : (Fin n → K) →ₗ[K] K, g ≠ 0 ∧
      ∀ v, f (vectorMap (K := K) v) = 0 → g v = 0 := by
  have hex : ∃ i : Fin n, f (Pi.single i 1) ≠ 0 := by
    by_contra! h
    apply hf
    apply LinearMap.ext
    intro v
    rw [← coordinate_decomposition v, map_sum]
    simp [h]
  obtain ⟨i,hi⟩ := hex
  obtain ⟨z,hz⟩ := Module.Projective.exists_dual_ne_zero K hi
  let g : (Fin n → K) →ₗ[K] K := z.comp ((f.restrictScalars K).comp vectorMap)
  refine ⟨g, ?_, ?_⟩
  · intro hg
    apply hz
    have hh := LinearMap.congr_fun hg (Pi.single i 1)
    have hsingle : vectorMap (K := K) (E := E) (Pi.single i 1) = Pi.single i 1 := by
      ext j
      by_cases hj : j = i <;> simp [vectorMap, hj]
    change z (f (vectorMap (Pi.single i 1))) = 0 at hh
    rw [hsingle] at hh
    exact hh
  · intro v hv
    change z (f (vectorMap v)) = 0
    simp [hv]

end
end SharpLogRamsey.ProjectiveBaseChange
end

section

namespace SharpLogRamsey.ProjectiveAffineChart
open scoped BigOperators
open Finset Classical
noncomputable section
variable {E : Type*} [Field E] {n : ℕ}

lemma normalize_eq_lift (a : Fin n → E) (P : Projectivization E (Fin (n+1) → E))
    (hP : first a P.rep ≠ 0) :
    (first a P.rep)⁻¹ • P.rep = lift a (chart a P) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (first a P.rep)⁻¹ * P.rep 0 = 1-∑ j, a j*((first a P.rep)⁻¹*P.rep j.succ)
    have ht : ∑ j, a j*((first a P.rep)⁻¹*P.rep j.succ) =
        (first a P.rep)⁻¹ * ∑ j, a j*P.rep j.succ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [ht]
    have hh : (first a P.rep)⁻¹ * (P.rep 0 + ∑ j, a j*P.rep j.succ) = 1 := by
      rw [← first_apply, inv_mul_cancel₀ hP]
    linear_combination hh
  · rfl

lemma mk_lift_chart (a : Fin n → E) (P : Projectivization E (Fin (n+1) → E))
    (hP : first a P.rep ≠ 0) :
    Projectivization.mk E (lift a (chart a P)) (lift_ne_zero _ _) = P := by
  calc
    _ = Projectivization.mk E P.rep P.rep_nonzero := by
      apply (Projectivization.mk_eq_mk_iff' E _ _ _ _).mpr
      exact ⟨(first a P.rep)⁻¹, normalize_eq_lift a P hP⟩
    _ = P := P.mk_rep

lemma chart_injOn (a : Fin n → E) :
    Set.InjOn (chart a) {P | first a P.rep ≠ 0} := by
  intro P hP Q hQ he
  rw [← mk_lift_chart a P hP, ← mk_lift_chart a Q hQ]
  congr 1
  exact congrArg (lift a) he

lemma lift_mem_iff (a : Fin n → E) (P : Projectivization E (Fin (n+1) → E))
    (hP : first a P.rep ≠ 0) (W : Submodule E (Fin (n+1) → E)) :
    lift a (chart a P) ∈ W ↔ P.submodule ≤ W := by
  have hp := congrArg Projectivization.submodule (mk_lift_chart a P hP)
  rw [Projectivization.submodule_mk] at hp
  rw [← hp, Submodule.span_singleton_le_iff_mem]

theorem lift_mem_span_pair (a x y z : Fin n → E) :
    lift a z ∈ Submodule.span E {lift a x, lift a y} ↔
      ∃ t : E, z = x+t • (y-x) := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨u,v,hh⟩
    have huv := congrArg (first a) hh
    simp only [map_add, map_smul, first_lift, smul_eq_mul, mul_one] at huv
    refine ⟨v, ?_⟩
    ext i
    have hi := congrFun hh i.succ
    simp only [Pi.add_apply, Pi.smul_apply, lift_succ, smul_eq_mul] at hi ⊢
    simp only [Pi.sub_apply]
    linear_combination -hi + x i * huv
  · rintro ⟨t,rfl⟩
    refine ⟨1-t,t,?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.add_apply, Pi.smul_apply, lift_zero, smul_eq_mul]
      simp only [Pi.sub_apply]
      simp_rw [mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have he : ∑ j, a j*(t*y j) = t*∑ j, a j*y j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hx : ∑ j, a j*(t*x j) = t*∑ j, a j*x j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he,hx]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, lift_succ, Pi.sub_apply, smul_eq_mul]
      ring

theorem exists_avoiding [Infinite E] (S : Finset (Projectivization E (Fin (n+1) → E))) :
    ∃ a : Fin n → E, ∀ P ∈ S, first a P.rep ≠ 0 := by
  classical
  let F (v : Fin (n+1) → E) : MvPolynomial (Fin n) E :=
    MvPolynomial.C (v 0) + ∑ i, MvPolynomial.C (v i.succ)*MvPolynomial.X i
  have hF (v : Fin (n+1) → E) (hv : v ≠ 0) : F v ≠ 0 := by
    intro h
    have h0 := congrArg (MvPolynomial.eval (fun _ => (0:E))) h
    simp [F] at h0
    have hs (i : Fin n) : v i.succ = 0 := by
      have hi := congrArg (MvPolynomial.eval (Pi.single i (1:E))) h
      simpa [F, h0, Pi.single_apply] using hi
    apply hv
    ext i
    exact Fin.cases h0 hs i
  have hprod : (∏ P ∈ S, F P.rep) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P _ => hF P.rep P.rep_nonzero)
  have hex : ∃ a : Fin n → E, MvPolynomial.eval a (∏ P ∈ S, F P.rep) ≠ 0 := by
    by_contra! hh
    apply hprod
    apply MvPolynomial.funext
    intro a
    simpa using hh a
  obtain ⟨a,ha⟩ := hex
  refine ⟨a, ?_⟩
  intro P hPS hP
  apply ha
  rw [map_prod]
  apply Finset.prod_eq_zero hPS
  simpa [F, first_apply, mul_comm] using hP

end
end SharpLogRamsey.ProjectiveAffineChart
end

section

namespace SharpLogRamsey.AffinePlaneCoefficients
open scoped BigOperators
open MvPolynomial Finset Classical
noncomputable section
variable {E : Type*} [Field E] {n : ℕ}

theorem degree_one_form (F : MvPolynomial (Fin n) E) (hF : F.totalDegree ≤ 1) :
    F = C (F.coeff 0)+∑ i, C (F.coeff (Finsupp.single i 1))*X i := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = 0
  · subst d
    simp [coeff_C_mul, coeff_X, coeff_sum]
  by_cases hi : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i,rfl⟩ := hi
    simp only [MvPolynomial.coeff_add, Finsupp.add_apply, coeff_C,
      ite_eq_right (Ne.symm hd), zero_add, coeff_sum,
      coeff_C_mul, coeff_X]
    have he (j : Fin n) : ((Finsupp.single j 1 : Fin n →₀ ℕ) = Finsupp.single i 1) ↔ j = i :=
      (Finsupp.single_left_injective (by decide : (1:ℕ) ≠ 0)).eq_iff
    simp_rw [he]
    simp
  · have hc : F.coeff d = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      have hdeg : d.sum (fun (_ : Fin n) k => k) ≠ 0 := by
        exact fun hh => hd ((Finsupp.degree_eq_zero_iff d).mp hh)
      have hne : d.sum (fun (_ : Fin n) k => k) ≠ 1 := by
        exact fun hh => hi ((Finsupp.sum_eq_one_iff d).mp hh)
      have hh : 1 < d.sum (fun (_ : Fin n) k => k) := by omega
      exact hF.trans_lt hh
    rw [hc]
    simp only [MvPolynomial.coeff_add, Finsupp.add_apply, coeff_C,
      ite_eq_right (Ne.symm hd), zero_add, coeff_sum, coeff_C_mul, coeff_X]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun hh => hi ⟨i,hh.symm⟩), mul_zero]

lemma eval_degree_one (F : MvPolynomial (Fin n) E) (hF : F.totalDegree ≤ 1)
    (x : Fin n → E) :
    eval x F = F.coeff 0+∑ i, F.coeff (Finsupp.single i 1)*x i := by
  conv_lhs => rw [degree_one_form F hF]
  simp

end
end SharpLogRamsey.AffinePlaneCoefficients
end

section

namespace SharpLogRamsey.RationalAffineChart
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.ProjectiveBaseChange SharpLogRamsey.ProjectiveAffineChart
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

lemma map_submodule (P : Projectivization K (Fin n → K)) :
    (pointMap (E := E) P).submodule = Submodule.span E {vectorMap (E := E) P.rep} := by
  conv_lhs => rw [← P.mk_rep]
  simp only [pointMap, Projectivization.map_mk, Projectivization.submodule_mk]
  rfl

lemma map_submodule_le (P : Projectivization K (Fin n → K))
    (W : Submodule K (Fin n → K)) :
    (pointMap (E := E) P).submodule ≤ extendSpace (E := E) W ↔ P.submodule ≤ W := by
  rw [map_submodule, Submodule.span_singleton_le_iff_mem, mem_extendSpace,
    Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]

lemma coord_injOn (a : Fin n → E) : Set.InjOn (coord (K := K) a) (Avoids (K := K) a) := by
  intro P hP Q hQ hh
  apply pointMap_injective (E := E)
  exact chart_injOn a hP hQ hh

lemma lift_coord_mem (a : Fin n → E) (P : Projectivization K (Fin (n+1) → K))
    (hP : Avoids a P) (W : Submodule K (Fin (n+1) → K)) :
    lift a (coord a P) ∈ extendSpace (E := E) W ↔ P.submodule ≤ W := by
  rw [lift_mem_iff a _ hP, map_submodule_le]

lemma lift_coord_kernel (a : Fin n → E) (P : Projectivization K (Fin (n+1) → K))
    (hP : Avoids a P) (f : (Fin (n+1) → E) →ₗ[E] E) :
    f (lift a (coord a P)) = 0 ↔ f (vectorMap (E := E) P.rep) = 0 := by
  change lift a (coord a P) ∈ f.ker ↔ vectorMap (E := E) P.rep ∈ f.ker
  rw [lift_mem_iff a _ hP, map_submodule, Submodule.span_singleton_le_iff_mem]

lemma exists_avoiding [Infinite E] (S : Finset (Projectivization K (Fin (n+1) → K))) :
    ∃ a : Fin n → E, ∀ P ∈ S, Avoids a P := by
  classical
  obtain ⟨a,ha⟩ := ProjectiveAffineChart.exists_avoiding (S.image (pointMap (E := E)))
  exact ⟨a,fun P hP => ha _ (mem_image.mpr ⟨P,hP,rfl⟩)⟩

lemma homogeneousPlane_lift (a x : Fin n → E) (F : MvPolynomial (Fin n) E)
    (hF : F.totalDegree ≤ 1) :
    homogeneousPlane a F (lift a x) = MvPolynomial.eval x F := by
  rw [AffinePlaneCoefficients.eval_degree_one F hF]
  simp [homogeneousPlane]

lemma homogeneousPlane_ne_zero [Infinite E] (a : Fin n → E) (F : MvPolynomial (Fin n) E)
    (hF : F.totalDegree = 1) : homogeneousPlane a F ≠ 0 := by
  intro hh
  have hpoly : F = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [← homogeneousPlane_lift a x F hF.le, hh]
    simp
  rw [hpoly, MvPolynomial.totalDegree_zero] at hF
  exact Nat.zero_ne_one hF

theorem plane_cap_transfer [Infinite E]
    (S : Finset (Projectivization K (Fin (n+1) → K))) (a : Fin n → E)
    (ha : ∀ P ∈ S, Avoids a P) (Kp : ℕ)
    (hcap : ∀ g : (Fin (n+1) → K) →ₗ[K] K, g ≠ 0 →
      (S.filter (fun P => g P.rep = 0)).card ≤ Kp)
    (F : MvPolynomial (Fin n) E) (hF : F.totalDegree = 1) :
    ((S.image (coord (K := K) a)).filter (fun x => MvPolynomial.eval x F = 0)).card ≤ Kp := by
  classical
  obtain ⟨g,hg,hfg⟩ := rational_hyperplane (K := K) (homogeneousPlane a F) (homogeneousPlane_ne_zero a F hF)
  let Z := S.filter (fun P => g P.rep = 0)
  have hsub : ((S.image (coord (K := K) a)).filter (fun x => MvPolynomial.eval x F = 0)) ⊆
      Z.image (coord (K := K) a) := by
    intro x hx
    obtain ⟨P,hPS,rfl⟩ := mem_image.mp (mem_filter.mp hx).1
    refine mem_image.mpr ⟨P,mem_filter.mpr ⟨hPS,?_⟩,rfl⟩
    apply hfg
    apply (lift_coord_kernel a P (ha P hPS) _).mp
    rw [homogeneousPlane_lift a _ F hF.le]
    exact (mem_filter.mp hx).2
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (hcap g hg))

end
end SharpLogRamsey.RationalAffineChart
end

section

namespace SharpLogRamsey.ProjectiveLineChart
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.ProjectiveBaseChange SharpLogRamsey.ProjectiveAffineChart
  SharpLogRamsey.RationalAffineChart
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

lemma extendSpace_span_pair (u v : Fin n → K) :
    extendSpace (E := E) (Submodule.span K {u,v}) =
      Submodule.span E {vectorMap (E := E) u, vectorMap (E := E) v} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hw
    apply Submodule.mem_span_pair.mpr
    refine ⟨algebraMap K E a,algebraMap K E b,?_⟩
    ext i
    simp [Algebra.smul_def]
  · apply Submodule.span_le.mpr
    intro w hw
    rcases hw with rfl | rfl
    · exact (mem_extendSpace _ _).mpr (Submodule.subset_span (Set.mem_insert _ _))
    · exact (mem_extendSpace _ _).mpr (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

end
end SharpLogRamsey.ProjectiveLineChart
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in

theorem mem_selected (f : V → Bool) (v : V) : v ∈ selected f ↔ f v = true := by
  simp [selected]
omit [DecidableEq V] in

theorem weight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : V → Bool) :
    0 ≤ weight p f := by
  apply prod_nonneg
  intro v _
  split <;> linarith

theorem sum_weight (p : ℝ) : ∑ f : V → Bool, weight p f = 1 := by
  simp_rw [weight]
  rw [← Fintype.prod_sum (fun (_v : V) (b : Bool) => if b then p else 1-p)]
  simp

theorem containment_moment (p : ℝ) (A : Finset V) :
    (∑ f : V → Bool, weight p f * (if A ⊆ selected f then 1 else 0)) = p^A.card := by
  have hi (f : V → Bool) :
      (if A ⊆ selected f then (1 : ℝ) else 0) =
        ∏ v : V, if v ∈ A then (if f v then 1 else 0) else 1 := by
    by_cases h : A ⊆ selected f
    · rw [ite_eq_left h]
      symm
      apply prod_eq_one
      intro v _
      by_cases hv : v ∈ A
      · simp [hv, (mem_selected f v).mp (h hv)]
      · simp [hv]
    · rw [ite_eq_right h]
      obtain ⟨v, hv, hfv⟩ := not_subset.mp h
      symm
      apply prod_eq_zero (mem_univ v)
      simp only [mem_selected, Bool.not_eq_true] at hfv
      simp [hv, hfv]
  simp_rw [hi, weight, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : V) (b : Bool) =>
    (if b then p else 1-p) * (if v ∈ A then (if b then (1:ℝ) else 0) else 1))]
  calc
    _ = ∏ v : V, if v ∈ A then p else 1 := by
      apply prod_congr rfl
      intro v _
      by_cases hv : v ∈ A <;> simp [hv]
    _ = p^A.card := by simp

theorem size_moment (p : ℝ) :
    (∑ f : V → Bool, weight p f * (selected f).card) = p * Fintype.card V := by
  have hc (f : V → Bool) : ((selected f).card : ℝ) =
      ∑ v : V, if ({v} : Finset V) ⊆ selected f then 1 else 0 := by
    simp [selected, sum_boole]
  simp_rw [hc, mul_sum]
  rw [sum_comm]
  simp_rw [containment_moment]
  simp [mul_comm]

theorem exists_ge_mean {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (X : (V → Bool) → ℝ) : ∃ f, (∑ g, weight p g * X g) ≤ X f := by
  obtain ⟨f, _, hf⟩ := exists_max_image (univ : Finset (V → Bool)) X univ_nonempty
  refine ⟨f, ?_⟩
  calc
    (∑ g, weight p g * X g) ≤ ∑ g, weight p g * X f := by
      exact sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hf g (mem_univ g))
        (weight_nonneg hp hp1 g))
    _ = X f := by rw [← sum_mul, sum_weight, one_mul]

end SharpLogRamsey.Sampling

namespace SharpLogRamsey.RichSampling
open Sampling Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

lemma moment (p b : ℝ) (A : Finset V) :
    (∑ f : V → Bool, weight p f * b^(A ∩ selected f).card) =
      (1-p+p*b)^A.card := by
  have hi (f : V → Bool) : b^(A ∩ selected f).card =
      ∏ v : V, if v ∈ A ∧ f v = true then b else 1 := by
    rw [← prod_filter]
    simp only [prod_const]
    congr 2
    ext v
    simp [selected]
  simp_rw [hi,weight,← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : V) (a : Bool) =>
    (if a then p else 1-p)*(if v ∈ A ∧ a = true then b else 1))]
  calc
    _ = ∏ v : V, if v ∈ A then 1-p+p*b else 1 := by
      apply prod_congr rfl
      intro v hv
      by_cases H : v ∈ A <;> simp [H] ; ring
    _ = _ := by simp

lemma exp_neg_half_le : Real.exp (-(1/2:ℝ)) ≤ 2/3 := by
  have h := Real.add_one_le_exp (1/2:ℝ)
  have he : Real.exp (-(1/2:ℝ))*Real.exp (1/2:ℝ) = 1 := by rw [← Real.exp_add]; norm_num
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(1/2:ℝ))).le
  nlinarith

lemma lower_tail (p M : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset V) (hM : M ≤ A.card) :
    (∑ f : V → Bool, weight p f *
      (if ((A ∩ selected f).card : ℝ) ≤ p*M/2 then 1 else 0)) ≤
      Real.exp (-p*M/12) := by
  have hpoint (f : V → Bool) :
      (if ((A ∩ selected f).card : ℝ) ≤ p*M/2 then (1:ℝ) else 0) ≤
        Real.exp (p*M/4)*Real.exp (-(1/2:ℝ))^(A ∩ selected f).card := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    split_ifs with H
    · rw [Real.one_le_exp_iff]
      linarith
    · exact (Real.exp_pos _).le
  have hb0 : 0 ≤ 1-p+p*Real.exp (-(1/2:ℝ)) :=
    add_nonneg (by linarith) (mul_nonneg hp (Real.exp_pos _).le)
  have hb : 1-p+p*Real.exp (-(1/2:ℝ)) ≤ Real.exp (-p/3) := by
    have H := mul_le_mul_of_nonneg_left exp_neg_half_le hp
    have E := Real.add_one_le_exp (-p/3)
    linarith
  calc
    _ ≤ ∑ f : V → Bool, weight p f *
        (Real.exp (p*M/4)*Real.exp (-(1/2:ℝ))^(A ∩ selected f).card) :=
      sum_le_sum (fun f hf => mul_le_mul_of_nonneg_left (hpoint f) (weight_nonneg hp hp1 f))
    _ = Real.exp (p*M/4)*(1-p+p*Real.exp (-(1/2:ℝ)))^A.card := by
      rw [← moment p (Real.exp (-(1/2:ℝ))) A,mul_sum]
      apply sum_congr rfl
      intro f hf
      ring
    _ ≤ Real.exp (p*M/4)*(Real.exp (-p/3))^A.card :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb _) (Real.exp_pos _).le
    _ = Real.exp (p*M/4+(A.card:ℝ)*(-p/3)) := by rw [Real.exp_add,Real.exp_nat_mul]
    _ ≤ Real.exp (-p*M/12) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hM hp]

theorem exists_sample [Nonempty V] (p M : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (L : Finset (Finset V)) (hM : ∀ A ∈ L, M ≤ A.card)
    (hprob : (L.card:ℝ)*Real.exp (-p*M/12) < 1/2) :
    ∃ S : Finset V, (S.card:ℝ) ≤ 2*p*Fintype.card V ∧
      ∀ A ∈ L, p*M/2 < ((A ∩ S).card:ℝ) := by
  classical
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (Fintype.card_pos (α := V))
  let bad := fun f : V → Bool => ∑ A ∈ L,
    if ((A ∩ selected f).card:ℝ) ≤ p*M/2 then (1:ℝ) else 0
  let X := fun f : V → Bool => ((selected f).card:ℝ)+2*p*N*bad f
  have hb : (∑ f : V → Bool, weight p f*bad f) ≤
      L.card*Real.exp (-p*M/12) := by
    simp only [bad,mul_sum]
    rw [sum_comm]
    calc
      _ ≤ ∑ _A ∈ L, Real.exp (-p*M/12) :=
        sum_le_sum (fun A hA => lower_tail p M hp.le hp1 A (hM A hA))
      _ = _ := by simp
  have hmean : (∑ f, weight p f*X f) < 2*p*N := by
    have he : (∑ f, weight p f*X f) = p*N+2*p*N*(∑ f, weight p f*bad f) := by
      simp only [X,mul_add,sum_add_distrib]
      rw [size_moment,mul_sum]
      congr 1
      apply sum_congr rfl
      intro f hf
      ring
    rw [he]
    have hlt := hb.trans_lt hprob
    have hpos : 0 < p*N := mul_pos hp hN
    nlinarith
  obtain ⟨f,hf⟩ := exists_ge_mean hp.le hp1 (fun f => -X f)
  simp only [mul_neg,Finset.sum_neg_distrib] at hf
  have hX : X f < 2*p*N := by linarith
  have hb0 : 0 ≤ bad f := by apply sum_nonneg; intro A hA; split_ifs <;> norm_num
  refine ⟨selected f,?_,?_⟩
  · have hcoef : 0 ≤ 2*p*N := by positivity
    change ((selected f).card:ℝ) ≤ 2*p*N
    dsimp only [X] at hX
    nlinarith [mul_nonneg hcoef hb0]
  · intro A hA
    by_contra H
    have ha : ((A ∩ selected f).card:ℝ) ≤ p*M/2 := le_of_not_gt H
    have hb1 : 1 ≤ bad f := by
      have H := single_le_sum (s := L) (f := fun B =>
        if ((B ∩ selected f).card:ℝ) ≤ p*M/2 then (1:ℝ) else 0)
        (fun B hB => by split_ifs <;> norm_num) hA
      simpa only [ite_eq_left ha] using H
    have hcoef : 0 ≤ 2*p*N := by positivity
    have hcard : 0 ≤ ((selected f).card:ℝ) := Nat.cast_nonneg _
    dsimp only [X] at hX
    nlinarith [mul_le_mul_of_nonneg_left hb1 hcoef]

end
end SharpLogRamsey.RichSampling

end

section

namespace SharpLogRamsey.Interpolation
open Finset MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]
noncomputable section

lemma exponent_injective (n h : ℕ) : Function.Injective (exponent (n := n) (h := h)) := by
  intro d e H
  ext i
  exact congrArg (fun f : Fin n →₀ ℕ => f i) H

lemma exponent_degree_le {n h : ℕ} (d : Box n h) : (exponent d).degree ≤ n*h := by
  change (exponent d).sum (fun _ e => e) ≤ n*h
  rw [Finsupp.sum_fintype]
  · calc
      ∑ i, (exponent d) i ≤ ∑ _i : Fin n, h := by
        apply sum_le_sum
        intro i hi
        exact Nat.le_of_lt_succ (d i).isLt
      _ = n*h := by simp
  · simp

lemma monomials_independent (n h : ℕ) :
    LinearIndependent K (fun d : Box n h => monomial (exponent d) (1:K)) :=
  (basisMonomials (Fin n) K).linearIndependent.comp exponent (exponent_injective n h)

theorem exists_vanishing (n h : ℕ) (S : Finset (Fin n → K))
    (hS : S.card < (h+1)^n) :
    ∃ F : MvPolynomial (Fin n) K, F ≠ 0 ∧ F.totalDegree ≤ n*h ∧
      ∀ x ∈ S, eval x F = 0 := by
  classical
  let v : Box n h → (S → K) := fun d x => eval x.val (monomial (exponent d) (1:K))
  have hn : ¬LinearIndependent K v := by
    intro H
    have H' := H.fintype_card_le_finrank
    have he : Fintype.card (Box n h) = (h+1)^n := by simp [Box]
    have hf : Module.finrank K (S → K) = S.card := by simp
    rw [he,hf] at H'
    omega
  obtain ⟨c,hc,d,hd⟩ := Fintype.not_linearIndependent_iff.mp hn
  refine ⟨∑ d, c d • monomial (exponent d) (1:K),?_,?_,?_⟩
  · intro H
    exact hd ((Fintype.linearIndependent_iff.mp (monomials_independent (K := K) n h)) c H d)
  · apply totalDegree_finsetSum_le
    intro d hd
    apply (totalDegree_smul_le _ _).trans
    exact (totalDegree_monomial_le _ _).trans (exponent_degree_le d)
  · intro x hx
    have H := congrFun hc ⟨x,hx⟩
    simpa [v,Algebra.smul_def] using H

end
end SharpLogRamsey.Interpolation

end

namespace SharpLogRamsey.SamplePolynomial
open Finset MvPolynomial AffineIncidence
open scoped BigOperators
variable {K V ι : Type*} [Field K] [Fintype V] [Nonempty V] [Fintype ι]
noncomputable section

lemma degree_le_of_dvd {F G : MvPolynomial (Fin 3) K} (hF : F ≠ 0) (h : G ∣ F) :
    G.totalDegree ≤ F.totalDegree := by
  obtain ⟨H,rfl⟩ := h
  have hG : G ≠ 0 := left_ne_zero_of_mul hF
  have hH : H ≠ 0 := right_ne_zero_of_mul hF
  rw [totalDegree_mul_of_isDomain hG hH]
  omega

omit [Fintype ι] in

lemma squarefree_reduction (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (x v : ι → Fin 3 → K) (hzero : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0) :
    ∃ G : MvPolynomial (Fin 3) K, G ≠ 0 ∧ Squarefree G ∧
      G.totalDegree ≤ F.totalDegree ∧
      ∀ i, LineFlatness.restrictLine (x i) (v i) G = 0 := by
  obtain ⟨G,n,hG,hGF,hFG⟩ := exists_squarefree_dvd_pow_of_ne_zero hF
  refine ⟨G,ne_zero_of_dvd_ne_zero hF hGF,hG,degree_le_of_dvd hF hGF,?_⟩
  intro i
  have H := map_dvd (aeval (fun j => Polynomial.C (x i j)+Polynomial.C (v i j)*Polynomial.X)) hFG
  change LineFlatness.restrictLine (x i) (v i) F ∣
    (aeval (fun j => Polynomial.C (x i j)+Polynomial.C (v i j)*Polynomial.X)) (G^n) at H
  rw [hzero i,map_pow] at H
  exact eq_zero_of_pow_eq_zero (zero_dvd_iff.mp H)

theorem exists_polynomial (points : V → Fin 3 → K) (hinj : Function.Injective points)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (A : ι → Finset V) (hA : ∀ i a, a ∈ A i → points a ∈ carrier (x i) (v i))
    (p M : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : ∀ i, M ≤ (A i).card)
    (hprob : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2)
    (h : ℕ) (hsize : 2*p*Fintype.card V < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ p*M/2) :
    ∃ F : MvPolynomial (Fin 3) K, F ≠ 0 ∧ Squarefree F ∧ F.totalDegree ≤ 3*h ∧
      ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0 := by
  classical
  let L := univ.image A
  have hL : (L.card:ℝ)*Real.exp (-p*M/12) < 1/2 := by
    have hc : L.card ≤ Fintype.card ι := (card_image_le).trans_eq (card_univ)
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.exp_pos _).le).trans_lt hprob
  obtain ⟨S,hS,hall⟩ := RichSampling.exists_sample p M hp hp1 L
    (by intro B hB; obtain ⟨i,hi,rfl⟩ := mem_image.mp hB; exact hM i) hL
  let T := S.image points
  have hT : T.card < (h+1)^3 := by
    have he : T.card = S.card := card_image_of_injective S hinj
    rw [he]
    exact_mod_cast hS.trans_lt hsize
  obtain ⟨F,hF,hFd,hFT⟩ := Interpolation.exists_vanishing 3 h T hT
  have hzero (i : ι) : LineFlatness.restrictLine (x i) (v i) F = 0 := by
    let B := (A i ∩ S).image points
    let f : K → Fin 3 → K := fun t => x i+t • v i
    let R := B.preimage f (parametrization_injective _ _ (hv i)).injOn
    have hR : R.card = (A i ∩ S).card := by
      rw [card_preimage]
      have he : B.filter (fun y => y ∈ Set.range f) = B := by
        apply filter_eq_self.mpr
        intro y hy
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
        exact hA i a (mem_inter.mp ha).1
      rw [he,card_image_of_injective _ hinj]
    have hr : F.totalDegree < R.card := by
      rw [hR]
      have H := (show (3*h:ℕ) ≤ p*M/2 from hdeg).trans_lt (hall (A i) (mem_image.mpr ⟨i,mem_univ i,rfl⟩))
      have H' : 3*h < (A i ∩ S).card := by exact_mod_cast H
      exact hFd.trans_lt H'
    apply RichLinePolynomial.restriction_zero_of_many (x i) (v i) F R hr
    intro t ht
    have H : f t ∈ B := mem_preimage.mp ht
    obtain ⟨a,ha,he⟩ := mem_image.mp H
    have he' : points a = (fun j => x i j+v i j*t) := by
      rw [he]
      ext j
      simp [f,mul_comm]
    rw [← he']
    exact hFT (points a) (mem_image.mpr ⟨a,(mem_inter.mp ha).2,rfl⟩)
  obtain ⟨G,hG,hGs,hGd,hGz⟩ := squarefree_reduction F hF x v hzero
  exact ⟨G,hG,hGs,hGd.trans hFd,hGz⟩

end
end SharpLogRamsey.SamplePolynomial

end

namespace SharpLogRamsey.RichAffineLines
open Finset MvPolynomial AffineIncidence
open scoped BigOperators Classical
variable {K ι : Type*} [Field K] [Infinite K] [IsAlgClosed K] [Fintype ι]
noncomputable section

theorem card_mul_le {q : ℕ} [CharP K q] (h2 : (2:K) ≠ 0)
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (M Kp h C : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hM : ∀ i, M ≤ (onLine x v S i).card)
    (hcap : ∀ L : MvPolynomial (Fin 3) K, L.totalDegree = 1 →
      (S.filter (fun y => eval y L = 0)).card ≤ Kp)
    (hprob : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2)
    (hsize : 2*p*S.card < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ p*M/2)
    (hchar : 3*h < q) (hMD : 18*h < M) (hKM : 8*Kp ≤ M^2)
    (hD : h^2*M ≤ C*S.card) :
    Fintype.card ι*M ≤ (6+72*C)*S.card := by
  classical
  let : Nonempty S := hS.to_subtype
  let A : ι → Finset S := fun i => univ.filter (fun y => y.val ∈ carrier (x i) (v i))
  have hAc (i : ι) : (A i).card = (onLine x v S i).card := by
    apply card_bij (fun y _ => y.val)
    · intro y hy
      exact mem_filter.mpr ⟨y.property,(mem_filter.mp hy).2⟩
    · intro a ha b hb H
      exact Subtype.ext H
    · intro y hy
      exact ⟨⟨y,(mem_filter.mp hy).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩,rfl⟩
  obtain ⟨F,hF,hFs,hFd,hFz⟩ := SamplePolynomial.exists_polynomial
    (fun y : S => y.val) Subtype.val_injective x v hv A
    (fun i y hy => (mem_filter.mp hy).2) p M hp hp1
    (fun i => by rw [Nat.cast_le]; rw [hAc i]; exact hM i) hprob h
    (by simpa only [Fintype.card_coe] using hsize) hdeg
  have H := SurfaceRichLines.card_le F hF (hFd.trans_lt hchar) hFs h2
    x v hv hd hFz S M Kp hM (fun L _ H => hcap L H) (by omega) hKM
  have HM : 0 < M := by omega
  have HM' : 0 < M-3*F.totalDegree := by omega
  have HD' : M ≤ 2*(M-3*F.totalDegree) := by omega
  have H1 : (2*S.card/M)*M ≤ 2*S.card := Nat.div_mul_le_self _ _
  have H2 : (2*S.card/(M-3*F.totalDegree))*M ≤ 4*S.card := by
    calc
      _ ≤ (2*S.card/(M-3*F.totalDegree))*(2*(M-3*F.totalDegree)) := Nat.mul_le_mul_left _ HD'
      _ = 2*((2*S.card/(M-3*F.totalDegree))*(M-3*F.totalDegree)) := by ring
      _ ≤ 2*(2*S.card) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ = _ := by ring
  have H3 : 8*F.totalDegree^2*M ≤ 72*C*S.card := by
    calc
      _ ≤ 8*(3*h)^2*M := Nat.mul_le_mul_right M (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hFd _))
      _ = 72*(h^2*M) := by ring
      _ ≤ 72*(C*S.card) := Nat.mul_le_mul_left _ hD
      _ = _ := by ring
  have HX := Nat.mul_le_mul_right M H
  nlinarith

end
end SharpLogRamsey.RichAffineLines
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_SpanPairLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
namespace SharpLogRamsey.ProjectiveLineChart
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.ProjectiveBaseChange SharpLogRamsey.ProjectiveAffineChart
  SharpLogRamsey.RationalAffineChart
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
lemma span_pair_of_line (W : Submodule K (Fin n → K)) (hW : Module.finrank K W = 2)
    (P Q : Projectivization K (Fin n → K)) (hPQ : P ≠ Q)
    (hP : P.submodule ≤ W) (hQ : Q.submodule ≤ W) :
    Submodule.span K {P.rep,Q.rep} = W := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | rfl
    · apply hP
      rw [Projectivization.submodule_eq]
      exact Submodule.subset_span rfl
    · apply hQ
      rw [Projectivization.submodule_eq]
      exact Submodule.subset_span rfl
  · have hh := finrank_span_eq_card (Projectivization.linearIndependent_pair_iff_ne.mpr hPQ)
    have he : Set.range ![P.rep,Q.rep] = {P.rep,Q.rep} := by
      ext v
      simp [or_comm]
    rw [he] at hh
    simpa [hW] using hh

lemma normalized_span (a : Fin n → E) (P Q : Projectivization K (Fin (n+1) → K))
    (hP : Avoids a P) (hQ : Avoids a Q) :
    Submodule.span E {lift a (coord a P),lift a (coord a Q)} =
      Submodule.span E {vectorMap (E := E) P.rep,vectorMap (E := E) Q.rep} := by
  have hp := congrArg Projectivization.submodule (mk_lift_chart a (pointMap P) hP)
  have hq := congrArg Projectivization.submodule (mk_lift_chart a (pointMap Q) hQ)
  rw [Projectivization.submodule_mk, map_submodule] at hp hq
  rw [show ({lift a (coord a P),lift a (coord a Q)} : Set _) =
    {lift a (coord a P)} ∪ {lift a (coord a Q)} by rfl]
  rw [Submodule.span_union, hp, hq, ← Submodule.span_union]
  rfl

theorem coord_mem_line (a : Fin n → E) (W : Submodule K (Fin (n+1) → K))
    (hW : Module.finrank K W = 2) (P Q R : Projectivization K (Fin (n+1) → K))
    (hPQ : P ≠ Q) (hP : P.submodule ≤ W) (hQ : Q.submodule ≤ W)
    (haP : Avoids a P) (haQ : Avoids a Q) (haR : Avoids a R) :
    R.submodule ≤ W ↔ ∃ t : E, coord a R = coord a P+t • (coord a Q-coord a P) := by
  rw [← lift_coord_mem a R haR W, ← span_pair_of_line W hW P Q hPQ hP hQ,
    extendSpace_span_pair, ← normalized_span a P Q haP haQ,
    lift_mem_span_pair]

lemma line_coord_ne (a : Fin n → E) (P Q : Projectivization K (Fin (n+1) → K))
    (haP : Avoids a P) (haQ : Avoids a Q) (hPQ : P ≠ Q) : coord a Q-coord a P ≠ 0 := by
  intro hh
  apply hPQ
  exact coord_injOn a haP haQ (sub_eq_zero.mp hh).symm

variable {ι : Type*}

theorem carriers_injective (a : Fin 3 → E) (W : ι → Submodule K (Fin 4 → K))
    (hW : ∀ i, Module.finrank K (W i) = 2) (hd : Function.Injective W)
    (P Q : ι → Projectivization K (Fin 4 → K))
    (hPQ : ∀ i, P i ≠ Q i) (hP : ∀ i, (P i).submodule ≤ W i)
    (hQ : ∀ i, (Q i).submodule ≤ W i)
    (haP : ∀ i, Avoids a (P i)) (haQ : ∀ i, Avoids a (Q i)) :
    Function.Injective (fun i => AffineIncidence.carrier (coord a (P i))
      (coord a (Q i)-coord a (P i))) := by
  intro i j hij
  dsimp only at hij
  apply hd
  have hm (R : Projectivization K (Fin 4 → K)) (haR : Avoids a R)
      (hr : R.submodule ≤ W i) : R.submodule ≤ W j := by
    have ht := (coord_mem_line a (W i) (hW i) (P i) (Q i) R
      (hPQ i) (hP i) (hQ i) (haP i) (haQ i) haR).mp hr
    have hh : coord a R ∈ AffineIncidence.carrier (coord a (P i))
        (coord a (Q i)-coord a (P i)) := by
      obtain ⟨t,ht⟩ := ht
      exact ⟨t,ht.symm⟩
    rw [hij] at hh
    apply (coord_mem_line a (W j) (hW j) (P j) (Q j) R
      (hPQ j) (hP j) (hQ j) (haP j) (haQ j) haR).mpr
    obtain ⟨t,ht⟩ := hh
    exact ⟨t,ht.symm⟩
  rw [← span_pair_of_line (W i) (hW i) (P i) (Q i) (hPQ i) (hP i) (hQ i)]
  exact span_pair_of_line (W j) (hW j) (P i) (Q i) (hPQ i)
    (hm _ (haP i) (hP i)) (hm _ (haQ i) (hQ i))

end
end SharpLogRamsey.ProjectiveLineChart
end

section

namespace SharpLogRamsey.RichProjectiveLines
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.ProjectiveBaseChange SharpLogRamsey.ProjectiveAffineChart
  SharpLogRamsey.RationalAffineChart SharpLogRamsey.ProjectiveLineChart
noncomputable section
variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]
    [Infinite E] [IsAlgClosed E] [Fintype ι]

theorem card_lines_square
    (S : Finset (Projectivization K (Fin 4 → K)))
    (W : ι → Submodule K (Fin 4 → K))
    (hW : ∀ i, Module.finrank K (W i) = 2) (hd : Function.Injective W)
    (hM : ∀ i, 2 ≤ (S.filter (fun P => P.submodule ≤ W i)).card) :
    Fintype.card ι ≤ S.card^2 := by
  classical
  have htwo (i : ι) : ∃ P Q : Projectivization K (Fin 4 → K),
      P ∈ S ∧ Q ∈ S ∧ P.submodule ≤ W i ∧ Q.submodule ≤ W i ∧ P ≠ Q := by
    obtain ⟨P,hP,Q,hQ,hPQ⟩ := Finset.one_lt_card.mp (show
      1 < (S.filter (fun P => P.submodule ≤ W i)).card by have := hM i; omega)
    exact ⟨P,Q,(mem_filter.mp hP).1,(mem_filter.mp hQ).1,
      (mem_filter.mp hP).2,(mem_filter.mp hQ).2,hPQ⟩
  choose P Q hPS hQS hP hQ hPQ using htwo
  let f (i : ι) : S × S := (⟨P i,hPS i⟩,⟨Q i,hQS i⟩)
  have hf : Function.Injective f := by
    intro i j hij
    have hp : P i = P j := congrArg (fun x : S × S => x.1.val) hij
    have hq : Q i = Q j := congrArg (fun x : S × S => x.2.val) hij
    apply hd
    rw [← span_pair_of_line (W i) (hW i) (P i) (Q i) (hPQ i) (hP i) (hQ i),
      ← span_pair_of_line (W j) (hW j) (P j) (Q j) (hPQ j) (hP j) (hQ j),hp,hq]
  simpa only [Fintype.card_prod, Fintype.card_coe, pow_two] using
    Fintype.card_le_of_injective f hf

theorem card_mul_le {q : ℕ} [CharP E q] (h2 : (2:E) ≠ 0)
    (S : Finset (Projectivization K (Fin 4 → K))) (hS : S.Nonempty)
    (W : ι → Submodule K (Fin 4 → K))
    (hW : ∀ i, Module.finrank K (W i) = 2) (hd : Function.Injective W)
    (M Kp h C : ℕ) (hM2 : 2 ≤ M) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hM : ∀ i, M ≤ (S.filter (fun P => P.submodule ≤ W i)).card)
    (hcap : ∀ f : (Fin 4 → K) →ₗ[K] K, f ≠ 0 →
      (S.filter (fun P => f P.rep = 0)).card ≤ Kp)
    (hprob : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2)
    (hsize : 2*p*S.card < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ p*M/2)
    (hchar : 3*h < q) (hMD : 18*h < M) (hKM : 8*Kp ≤ M^2)
    (hD : h^2*M ≤ C*S.card) :
    Fintype.card ι*M ≤ (6+72*C)*S.card := by
  classical
  obtain ⟨a,ha⟩ := RationalAffineChart.exists_avoiding (E := E) S
  have htwo (i : ι) : ∃ P Q : Projectivization K (Fin 4 → K),
      P ∈ S ∧ Q ∈ S ∧ P.submodule ≤ W i ∧ Q.submodule ≤ W i ∧ P ≠ Q := by
    have hc : 1 < (S.filter (fun P => P.submodule ≤ W i)).card := by
      have := hM i
      omega
    obtain ⟨P,hP,Q,hQ,hPQ⟩ := Finset.one_lt_card.mp hc
    exact ⟨P,Q,(mem_filter.mp hP).1,(mem_filter.mp hQ).1,
      (mem_filter.mp hP).2,(mem_filter.mp hQ).2,hPQ⟩
  choose P Q hPS hQS hP hQ hPQ using htwo
  let x (i : ι) := coord a (P i)
  let v (i : ι) := coord a (Q i)-coord a (P i)
  let T := S.image (coord (K := K) a)
  have hTc : T.card = S.card := card_image_of_injOn (fun P hP Q hQ hh =>
    coord_injOn a (ha P hP) (ha Q hQ) hh)
  have hA (i : ι) : AffineIncidence.onLine x v T i =
      (S.filter (fun P => P.submodule ≤ W i)).image (coord (K := K) a) := by
    ext z
    simp only [AffineIncidence.onLine,T,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨R,hRS,rfl⟩,t,ht⟩
      refine ⟨R,⟨hRS,?_⟩,rfl⟩
      apply (coord_mem_line a (W i) (hW i) (P i) (Q i) R
        (hPQ i) (hP i) (hQ i) (ha _ (hPS i)) (ha _ (hQS i)) (ha R hRS)).mpr
      exact ⟨t,ht.symm⟩
    · rintro ⟨R,⟨hRS,hRW⟩,rfl⟩
      refine ⟨⟨R,hRS,rfl⟩,?_⟩
      obtain ⟨t,ht⟩ := (coord_mem_line a (W i) (hW i) (P i) (Q i) R
        (hPQ i) (hP i) (hQ i) (ha _ (hPS i)) (ha _ (hQS i)) (ha R hRS)).mp hRW
      exact ⟨t,ht.symm⟩
  have hAc (i : ι) : (AffineIncidence.onLine x v T i).card =
      (S.filter (fun P => P.submodule ≤ W i)).card := by
    rw [hA]
    apply card_image_of_injOn
    intro P hP Q hQ hh
    exact coord_injOn a (ha P (mem_filter.mp hP).1) (ha Q (mem_filter.mp hQ).1) hh
  have H := RichAffineLines.card_mul_le h2 T (hS.image _) x v
    (fun i => line_coord_ne a (P i) (Q i) (ha _ (hPS i)) (ha _ (hQS i)) (hPQ i))
    (carriers_injective a W hW hd P Q hPQ hP hQ (fun i => ha _ (hPS i)) (fun i => ha _ (hQS i)))
    M Kp h C p hp hp1 (fun i => by rw [hAc]; exact hM i)
    (plane_cap_transfer S a ha Kp hcap) hprob
    (by rw [hTc]; exact hsize) hdeg hchar hMD hKM (by rw [hTc]; exact hD)
  simpa only [hTc] using H

end
end SharpLogRamsey.RichProjectiveLines
end

section

namespace SharpLogRamsey.RichLineScales
open scoped BigOperators
noncomputable section

theorem choose_parameters (N M q : ℕ) (hM : 0 < M) (hMN : M ≤ N)
    (hsmall : 198*Real.sqrt ((N:ℝ)/M) < M)
    (hchar : 33*Real.sqrt ((N:ℝ)/M) < q)
    (hprob : (N:ℝ)^2*Real.exp (-5*Real.sqrt ((N:ℝ)/M)) < 1/2) :
    ∃ h : ℕ, ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
      (N:ℝ)^2*Real.exp (-p*M/12) < 1/2 ∧
      2*p*N < ((h+1)^3:ℕ) ∧ (3*h:ℕ) ≤ p*M/2 ∧
      3*h < q ∧ 18*h < M ∧ h^2*M ≤ 121*N := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hmn : (M:ℝ) ≤ N := by exact_mod_cast hMN
  let r := Real.sqrt ((N:ℝ)/M)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : 1 ≤ r := by
    have := Real.sqrt_le_sqrt ((le_div_iff₀ hm).mpr (by linarith : 1*(M:ℝ) ≤ N))
    simpa only [Real.sqrt_one] using this
  have hr : r^2*(M:ℝ) = N := by
    rw [Real.sq_sqrt (by positivity), div_mul_cancel₀ _ hm.ne']
  let h : ℕ := ⌈10*r⌉₊
  have hhlo : 10*r ≤ (h:ℝ) := Nat.le_ceil _
  have hhhi : (h:ℝ) ≤ 11*r := by
    have H := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 10*r)
    change (h:ℝ) < 10*r+1 at H
    linarith
  have hhpos : (0:ℝ) < h := by linarith
  have hhm : 18*(h:ℝ) < M := by
    change 198*r < M at hsmall
    linarith
  have hhq : 3*(h:ℝ) < q := by
    change 33*r < q at hchar
    linarith
  let p : ℝ := 6*h/M
  have hp : 0 < p := div_pos (by positivity) hm
  have hpm : p*M = 6*h := by dsimp [p]; rw [div_mul_cancel₀ _ hm.ne']
  have hp1 : p ≤ 1 := (div_le_iff₀ hm).mpr (by linarith)
  have hhsq : (h:ℝ)^2 ≤ 121*r^2 := by
    have := mul_le_mul hhhi hhhi (by positivity) (by positivity)
    nlinarith
  have hdsq : (h:ℝ)^2*(M:ℝ) ≤ 121*N := by
    have := mul_le_mul_of_nonneg_right hhsq hm.le
    nlinarith [hr]
  have hhbig : 12*r^2 < (h:ℝ)^2 := by
    have := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 10*r) hhlo
    nlinarith [sq_nonneg (r-1)]
  refine ⟨h,p,hp,hp1,?_,?_,?_,?_,?_,?_⟩
  · apply lt_of_le_of_lt _ hprob
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    rw [neg_mul, hpm]
    change -(6*(h:ℝ))/12 ≤ -5*r
    linarith
  · have hhN : 12*(N:ℝ) < (h:ℝ)^2*M := by
      have := mul_lt_mul_of_pos_right hhbig hm
      nlinarith [hr]
    have hsize' : 2*p*N < (h:ℝ)^3 := by
      have h1 : 2*p*N*M < (h:ℝ)^3*M := by
        calc
          _ = 12*(h:ℝ)*N := by nlinarith [congrArg (fun x : ℝ => 2*(N:ℝ)*x) hpm]
          _ < (h:ℝ)*((h:ℝ)^2*M) := by nlinarith [mul_lt_mul_of_pos_left hhN hhpos]
          _ = _ := by ring
      exact (mul_lt_mul_iff_left₀ hm).mp (by simpa only [mul_comm _ (M:ℝ)] using h1)
    have hnext : (h:ℝ)^3 < ((h:ℝ)+1)^3 := by nlinarith [sq_nonneg (h:ℝ)]
    exact_mod_cast hsize'.trans hnext
  · simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [hpm]
    linarith
  · exact_mod_cast hhq
  · exact_mod_cast hhm
  · exact_mod_cast hdsq

end
end SharpLogRamsey.RichLineScales
end

section

namespace SharpLogRamsey.RichProjectiveCount
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]
    [Infinite E] [IsAlgClosed E] [Fintype ι]

theorem card_mul_le {q : ℕ} [CharP E q] (h2 : (2:E) ≠ 0)
    (S : Finset (Projectivization K (Fin 4 → K))) (hS : S.Nonempty)
    (W : ι → Submodule K (Fin 4 → K))
    (hW : ∀ i, Module.finrank K (W i) = 2) (hd : Function.Injective W)
    (M Kp : ℕ) (hM2 : 2 ≤ M) (hMN : M ≤ S.card)
    (hM : ∀ i, M ≤ (S.filter (fun P => P.submodule ≤ W i)).card)
    (hcap : ∀ f : (Fin 4 → K) →ₗ[K] K, f ≠ 0 →
      (S.filter (fun P => f P.rep = 0)).card ≤ Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/M) < M)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/M) < q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M)) < 1/2)
    (hKM : 8*Kp ≤ M^2) : Fintype.card ι*M ≤ 8718*S.card := by
  obtain ⟨h,p,hp,hp1,hprob',hsize,hdeg,hchar',hMD,hD⟩ :=
    RichLineScales.choose_parameters S.card M q (by omega) hMN hsmall hchar hprob
  have hc := RichProjectiveLines.card_lines_square S W hW hd (fun i => hM2.trans (hM i))
  have hprob'' : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2 := by
    apply lt_of_le_of_lt _ hprob'
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact_mod_cast hc
  exact RichProjectiveLines.card_mul_le (E := E) h2 S hS W hW hd M Kp h 121 hM2
    p hp hp1 hM hcap hprob'' hsize hdeg hchar' hMD hKM hD

end
end SharpLogRamsey.RichProjectiveCount
end

section

namespace SharpLogRamsey.RichFiniteProjective
open scoped BigOperators
open Finset Classical
noncomputable section
variable {q : ℕ} [Fact q.Prime] {ι : Type*} [Fintype ι]

theorem card_mul_le (hq : 3 ≤ q)
    (S : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))) (hS : S.Nonempty)
    (W : ι → Submodule (ZMod q) (Fin 4 → ZMod q))
    (hW : ∀ i, Module.finrank (ZMod q) (W i) = 2) (hd : Function.Injective W)
    (M Kp : ℕ) (hM2 : 2 ≤ M) (hMN : M ≤ S.card)
    (hM : ∀ i, M ≤ (S.filter (fun P => P.submodule ≤ W i)).card)
    (hcap : ∀ f : (Fin 4 → ZMod q) →ₗ[ZMod q] ZMod q, f ≠ 0 →
      (S.filter (fun P => f P.rep = 0)).card ≤ Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/M) < M)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/M) < q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M)) < 1/2)
    (hKM : 8*Kp ≤ M^2) : Fintype.card ι*M ≤ 8718*S.card := by
  apply RichProjectiveCount.card_mul_le (E := AlgebraicClosure (ZMod q))
    (q := q) _ S hS W hW hd M Kp hM2 hMN hM (by
      intro functional nonzero
      convert! (preTransparency := .all) hcap functional nonzero) hsmall hchar hprob hKM
  intro hh
  have hdiv : q ∣ 2 := (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q 2).mp
    (by simpa only [Nat.cast_ofNat] using hh)
  have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

end
end SharpLogRamsey.RichFiniteProjective
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_GreedyIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

theorem exists_complete (F : Finset β) (U : β → Finset α) (m : ℕ) (hm : 0 < m)
    (S : Finset α) : ∃ bs, Complete F U m S bs := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hall : ∀ b ∈ F, (S ∩ U b).card < m
    · exact ⟨[],Complete.nil S hall⟩
    · have hex : ∃ c ∈ F, m ≤ (S ∩ U c).card := by
        push Not at hall
        exact hall
      obtain ⟨c,hc,hcm⟩ := hex
      obtain ⟨b,hb,hmax⟩ := exists_max_image F (fun b => (S ∩ U b).card) ⟨c,hc⟩
      have hrich := hcm.trans (hmax c hc)
      have hsmall : (S \ U b).card < n := by
        have he := card_sdiff_add_card_inter S (U b)
        omega
      obtain ⟨bs,hbs⟩ := ih (S \ U b).card hsmall (S \ U b) rfl
      exact ⟨b::bs,Complete.cons S b bs hb hrich hmax hbs⟩

lemma residual_subset (S : Finset α) (U : β → Finset α) (bs : List β) :
    residual S U bs ⊆ S := by
  induction bs generalizing S with
  | nil => exact subset_rfl
  | cons b bs ih => exact (ih _).trans sdiff_subset

theorem card_partition (S : Finset α) (U : β → Finset α) (bs : List β) :
    ((cells S U bs).map Finset.card).sum + (residual S U bs).card = S.card := by
  induction bs generalizing S with
  | nil => simp [cells,residual]
  | cons b bs ih =>
    simp only [cells,residual,List.map_cons,List.sum_cons]
    have ht := ih (S \ U b)
    have he := card_sdiff_add_card_inter S (U b)
    omega

lemma complete_small_residual {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) :
    ∀ b ∈ F, (residual S U bs ∩ U b).card < m := by
  induction h with
  | nil S ht => exact ht
  | cons S b bs hb hrich hmax htail ih => exact ih

lemma complete_length_bound {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) :
    bs.length*m+(residual S U bs).card ≤ S.card := by
  induction h with
  | nil S ht => simp [residual]
  | cons S b bs hb hrich hmax htail ih =>
    simp only [List.length_cons,Nat.add_mul,one_mul,residual]
    have he := card_sdiff_add_card_inter S (U b)
    omega

lemma complete_cells_bounded {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs)
    (B : ℕ) (hB : ∀ b ∈ F, (S ∩ U b).card ≤ B) :
    ∀ C ∈ cells S U bs, C.card ≤ B := by
  induction h with
  | nil S ht => simp [cells]
  | cons S b bs hb hrich hmax htail ih =>
    intro C hC
    simp only [cells,List.mem_cons] at hC
    rcases hC with rfl | hc
    · exact hB b hb
    · apply ih (fun c hc => (card_le_card ?_).trans (hB c hc)) C hc
      exact inter_subset_inter_right sdiff_subset

theorem complete_nonincreasing {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) :
    (cells S U bs).Pairwise (fun C D => D.card ≤ C.card) := by
  induction h with
  | nil S ht => simp [cells]
  | cons S b bs hb hrich hmax htail ih =>
    rw [cells,List.pairwise_cons]
    refine ⟨?_,ih⟩
    apply complete_cells_bounded htail
    intro c hc
    apply (card_le_card (inter_subset_inter_right (sdiff_subset (s:=S) (t:=U b)))).trans
    exact hmax c hc

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

lemma residual_eq (S : Finset α) (U : β → Finset α) (bs : List β) :
    residual S U bs = S \ bs.toFinset.biUnion U := by
  induction bs generalizing S with
  | nil => simp [residual]
  | cons b bs ih =>
    rw [residual,ih]
    ext x
    simp only [mem_sdiff,List.toFinset_cons,mem_biUnion,mem_insert]
    aesop

lemma removed_subset (S : Finset α) (U : β → Finset α) (bs : List β) :
    removed S U bs ⊆ S := sdiff_subset

lemma removed_eq (S : Finset α) (U : β → Finset α) (bs : List β) :
    removed S U bs = S ∩ bs.toFinset.biUnion U := by
  rw [removed,residual_eq]
  ext x
  simp only [mem_sdiff,mem_inter]
  tauto

lemma removed_cons (S : Finset α) (U : β → Finset α) (b : β) (bs : List β) :
    removed S U (b::bs) = (S ∩ U b) ∪ removed (S \ U b) U bs := by
  simp only [removed_eq,List.toFinset_cons,biUnion_insert]
  ext x
  simp only [mem_union,mem_inter,mem_sdiff]
  tauto

lemma cell_subset_removed (S : Finset α) (U : β → Finset α) (bs : List β)
    (C : Finset α) (hC : C ∈ cells S U bs) : C ⊆ removed S U bs := by
  induction bs generalizing S with
  | nil => simp [cells] at hC
  | cons b bs ih =>
    rw [removed_cons]
    simp only [cells,List.mem_cons] at hC
    rcases hC with rfl | hc
    · exact subset_union_left
    · exact (ih _ hc).trans subset_union_right

lemma own_empty_or_cell (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x = ∅ ∨ own S U bs x ∈ cells S U bs := by
  induction bs generalizing S with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    rw [own]
    split_ifs with hx
    · exact Or.inr (by simp [cells])
    · rcases ih (S \ U b) with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by simp only [cells,List.mem_cons]; exact Or.inr hh)

lemma own_subset_removed (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x ⊆ removed S U bs := by
  rcases own_empty_or_cell S U bs x with hh | hh
  · rw [hh]; exact empty_subset _
  · exact cell_subset_removed S U bs _ hh

lemma removed_card (S : Finset α) (U : β → Finset α) (bs : List β) :
    (removed S U bs).card + (residual S U bs).card = S.card :=
  card_sdiff_add_card_eq_card (residual_subset S U bs)

lemma removed_card_eq_sum (S : Finset α) (U : β → Finset α) (bs : List β) :
    (removed S U bs).card = ((cells S U bs).map Finset.card).sum := by
  have h := removed_card S U bs
  have h' := card_partition S U bs
  omega

theorem preparation (F : Finset β) (U : β → Finset α) (m : ℕ) (hm : 0 < m)
    (S : Finset α) :
    (∃ S' : Finset α, S' ⊆ S ∧ S.card ≤ 2*S'.card ∧
      ∀ b ∈ F, (S' ∩ U b).card < m) ∨
    (∃ bs : List β, Complete F U m S bs ∧ S.card ≤ 2*(removed S U bs).card ∧
      bs.length*m ≤ S.card ∧
      (cells S U bs).Pairwise (fun C D => D.card ≤ C.card)) := by
  obtain ⟨bs,hbs⟩ := exists_complete F U m hm S
  by_cases hh : S.card ≤ 2*(removed S U bs).card
  · refine Or.inr ⟨bs,hbs,hh,?_,complete_nonincreasing hbs⟩
    have := complete_length_bound hbs
    omega
  · refine Or.inl ⟨residual S U bs,residual_subset S U bs,?_,complete_small_residual hbs⟩
    have := removed_card S U bs
    omega

lemma removed_inter_card_le (S : Finset α) (U : β → Finset α) (bs : List β)
    (L : Finset α) (hL : ∀ b ∈ bs, (U b ∩ L).card ≤ 1) :
    (removed S U bs ∩ L).card ≤ bs.length := by
  induction bs generalizing S with
  | nil => simp [removed,residual]
  | cons b bs ih =>
    rw [removed_cons,union_inter_distrib_right]
    apply (card_union_le _ _).trans
    have h1 : (S ∩ U b ∩ L).card ≤ 1 :=
      (card_le_card (inter_subset_inter_right inter_subset_right)).trans (hL b (by simp))
    have h2 := ih (S \ U b) (fun c hc => hL c (by simp [hc]))
    simpa only [List.length_cons] using Nat.add_le_add h1 h2 |>.trans_eq (Nat.add_comm 1 bs.length)

lemma outside_first_inter_empty (S : Finset α) (U : β → Finset α) (b : β)
    (bs : List β) (L : Finset α) (hL : L ⊆ U b) (x : α) (hx : x ∈ L) :
    ((removed S U (b::bs) \ own S U (b::bs) x) ∩ L) = ∅ := by
  rw [own,ite_eq_left (hL hx),removed_cons]
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hy,hyL⟩ := mem_inter.mp hy
  obtain ⟨hy,hyn⟩ := mem_sdiff.mp hy
  rcases mem_union.mp hy with hh | hh
  · exact hyn hh
  · have hyS := removed_subset (S \ U b) U bs hh
    exact (mem_sdiff.mp hyS).2 (hL hyL)

lemma outside_inter_prefix (S : Finset α) (U : β → Finset α) (pre : List β)
    (b : β) (post : List β) (L : Finset α) (hL : L ⊆ U b)
    (x : α) (hx : x ∈ L) (hpre : ∀ c ∈ pre, x ∉ U c)
    (hline : ∀ c ∈ pre, (U c ∩ L).card ≤ 1) :
    ((removed S U (pre ++ b::post) \ own S U (pre ++ b::post) x) ∩ L).card ≤ pre.length := by
  induction pre generalizing S with
  | nil => simp only [List.nil_append,outside_first_inter_empty S U b post L hL x hx,card_empty,List.length_nil]
           exact le_rfl
  | cons c pre ih =>
    simp only [List.cons_append,own,ite_eq_right (hpre c (by simp))]
    rw [removed_cons]
    have hsubset : (((S ∩ U c) ∪ removed (S \ U c) U (pre ++ b::post)) \
        own (S \ U c) U (pre ++ b::post) x) ∩ L ⊆
      (S ∩ U c ∩ L) ∪ ((removed (S \ U c) U (pre ++ b::post) \
        own (S \ U c) U (pre ++ b::post) x) ∩ L) := by
      intro y hy
      simp only [mem_inter,mem_union,mem_sdiff] at hy ⊢
      tauto
    apply (card_le_card hsubset).trans ((card_union_le _ _).trans ?_)
    have h1 : (S ∩ U c ∩ L).card ≤ 1 :=
      (card_le_card (inter_subset_inter_right inter_subset_right)).trans (hline c (by simp))
    have h2 := ih (S \ U c) (fun e he => hpre e (by simp [he]))
      (fun e he => hline e (by simp [he]))
    simp only [List.length_cons]
    omega

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

lemma residual_append (S : Finset α) (U : β → Finset α) (a b : List β) :
    residual S U (a++b) = residual (residual S U a) U b := by
  induction a generalizing S with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append,residual] using ih (S \ U x)

lemma removed_append (S : Finset α) (U : β → Finset α) (a b : List β) :
    removed S U (a++b) = removed S U a ∪ removed (residual S U a) U b := by
  rw [removed,residual_append,removed,removed]
  have h1 := residual_subset S U a
  have h2 := residual_subset (residual S U a) U b
  ext x
  simp only [mem_sdiff,mem_union]
  constructor
  · intro hx
    by_cases hr : x ∈ residual S U a
    · exact Or.inr ⟨hr,hx.2⟩
    · exact Or.inl ⟨hx.1,hr⟩
  · rintro (hx|hx)
    · exact ⟨hx.1,fun hn => hx.2 (h2 hn)⟩
    · exact ⟨h1 hx.1,hx.2⟩

lemma cells_get (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : ℕ) (hi : i < bs.length) :
    (cells S U bs)[i]'(by rw [cells_length]; exact hi) =
      residual S U (bs.take i) ∩ U bs[i] := by
  induction bs generalizing S i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [cells,List.getElem_cons_succ,List.take_succ_cons,residual]
      exact ih (S \ U b) i (by simpa using hi)

lemma indexedCell_eq (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : Fin bs.length) : indexedCell S U bs i =
      (cells S U bs)[i.val]'(by rw [cells_length]; exact i.isLt) :=
  (cells_get S U bs i.val i.isLt).symm

lemma indexedCell_antitone {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) :
    Antitone (fun i : Fin bs.length => (indexedCell S U bs i).card) := by
  intro i j hij
  change (indexedCell S U bs j).card ≤ (indexedCell S U bs i).card
  rw [indexedCell_eq,indexedCell_eq]
  by_cases he : i = j
  · subst j; exact le_rfl
  · have hlt : i.val < j.val := by
      have hne : i.val ≠ j.val := fun hh => he (Fin.ext hh)
      exact lt_of_le_of_ne hij hne
    exact (List.pairwise_iff_getElem.mp (complete_nonincreasing h))
      i.val j.val (by rw [cells_length]; exact i.isLt)
      (by rw [cells_length]; exact j.isLt) hlt

lemma indexedCell_sum (S : Finset α) (U : β → Finset α) (bs : List β) :
    ∑ i : Fin bs.length, (indexedCell S U bs i).card = (removed S U bs).card := by
  rw [removed_card_eq_sum]
  induction bs generalizing S with
  | nil => simp [cells]
  | cons b bs ih =>
    change (∑ i : Fin (bs.length+1), (indexedCell S U (b::bs) i).card) = _
    rw [Fin.sum_univ_succ]
    simp only [indexedCell,Fin.val_zero,List.take_zero,residual,List.getElem_cons_zero,
      Fin.val_succ,List.take_succ_cons,List.getElem_cons_succ,cells,List.map_cons,List.sum_cons]
    congr 1
    exact ih (S \ U b)

lemma residual_after_first_disjoint (S : Finset α) (U : β → Finset α)
    (b : β) (post : List β) (L : Finset α) (hL : L ⊆ U b) :
    Disjoint (removed (S \ U b) U post) L := by
  apply disjoint_left.mpr
  intro x hx hxL
  exact (mem_sdiff.mp (removed_subset (S \ U b) U post hx)).2 (hL hxL)

lemma removed_line_le_prefix_cell (S : Finset α) (U : β → Finset α)
    (pre : List β) (b : β) (post : List β) (L : Finset α) (hL : L ⊆ U b)
    (hpre : ∀ c ∈ pre, (U c ∩ L).card ≤ 1) :
    (removed S U (pre++b::post) ∩ L).card ≤
      pre.length + (residual S U pre ∩ U b ∩ L).card := by
  rw [removed_append,removed_cons,union_inter_distrib_right,
    union_inter_distrib_right]
  have he : removed (residual S U pre \ U b) U post ∩ L = ∅ :=
    disjoint_iff_inter_eq_empty.mp (residual_after_first_disjoint _ U b post L hL)
  rw [he,union_empty]
  exact (card_union_le _ _).trans (Nat.add_le_add_right
    (removed_inter_card_le S U pre L hpre) _)

lemma first_containing (U : β → Finset α) (bs : List β) (L : Finset α)
    (hex : ∃ b ∈ bs, L ⊆ U b) :
    ∃ pre b post, bs=pre++b::post ∧ L ⊆ U b ∧ ∀ c ∈ pre, ¬ L ⊆ U c := by
  induction bs with
  | nil => simp at hex
  | cons b bs ih =>
    by_cases hb : L ⊆ U b
    · exact ⟨[],b,bs,rfl,hb,by simp⟩
    · have hex' : ∃ c ∈ bs, L ⊆ U c := by
        obtain ⟨c,hc,hcL⟩ := hex
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact (hb hcL).elim
        · exact ⟨c,hc,hcL⟩
      obtain ⟨pre,c,post,he,hc,hpre⟩ := ih hex'
      refine ⟨b::pre,c,post,by simp [he],hc,?_⟩
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hb
      · exact hpre d hd

end
end SharpLogRamsey.GreedyPreparation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*} [Fintype α]

omit [Fintype α] in
lemma sized_planes (S : Finset α) (U : β → Finset α) (bs : List β) :
    (sized S U bs).map Prod.fst=bs := by
  induction bs generalizing S with
  | nil => rfl
  | cons b bs ih => simp [sized,ih]

end
end SharpLogRamsey.GreedyPreparation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PreparedRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β γ : Type*}

lemma list_union_inter_card_le (U : β → Finset α) (bs : List β)
    (L : Finset α) (hL : ∀ b ∈ bs, (U b ∩ L).card ≤ 1) :
    (bs.toFinset.biUnion U ∩ L).card ≤ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.toFinset_cons,biUnion_insert,union_inter_distrib_right]
    have h1 := hL b (by simp)
    have h2 := ih (fun c hc => hL c (by simp [hc]))
    have hh := card_union_le (U b ∩ L) (bs.toFinset.biUnion U ∩ L)
    simp only [List.length_cons]
    omega

theorem prepared_list_radial {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs)
    (A : Finset α) (G : Finset γ) (L : γ → Finset α) (r : ℕ) (hr0 : 0 < r)
    (hplane : ∀ b ∈ bs, ∀ j ∈ G, ¬ L j ⊆ U b → (U b ∩ L j).card ≤ 1)
    (hunique : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → (L i ∩ L j).card ≤ 1) :
    ((A ×ˢ G).filter (fun z => z.1 ∈ L z.2 ∧
      bs.length+r ≤ ((removed S U bs \ own S U bs z.1) ∩ L z.2).card)).card *
      (r*(r-1)) ≤ (removed S U bs).card^2 := by
  let C := indexedCell S U bs
  let E : Fin bs.length → Finset γ := fun i => G.filter (fun j =>
    L j ⊆ U bs[i.val] ∧ (∀ b ∈ bs.take i.val, ¬ L j ⊆ U b) ∧
    r ≤ (C i ∩ L j).card)
  let centers : Fin bs.length → γ → Finset α := fun i j =>
    (bs.take i.val).toFinset.biUnion U ∩ L j
  have hcenter (i : Fin bs.length) (j : γ) (hj : j ∈ E i) :
      (centers i j).card ≤ i.val := by
    have hj' := mem_filter.mp hj
    have hh := list_union_inter_card_le U (bs.take i.val) (L j) (fun b hb =>
      hplane b (List.mem_of_mem_take hb) j hj'.1 (hj'.2.2.1 b hb))
    exact hh.trans (List.length_take_le _ _)
  have hcover : (A ×ˢ G).filter (fun z => z.1 ∈ L z.2 ∧
      bs.length+r ≤ ((removed S U bs \ own S U bs z.1) ∩ L z.2).card) ⊆
      univ.biUnion (fun i => (E i).biUnion (fun j => centers i j ×ˢ {j})) := by
    intro z hz
    obtain ⟨hzAG,hzx,hzrich⟩ := mem_filter.mp hz
    have hjG := (mem_product.mp hzAG).2
    have hex : ∃ b ∈ bs, L z.2 ⊆ U b := by
      by_contra hn
      push Not at hn
      have hb := removed_inter_card_le S U bs (L z.2)
        (fun b hb => hplane b hb z.2 hjG (hn b hb))
      have hs : ((removed S U bs \ own S U bs z.1) ∩ L z.2).card ≤
          (removed S U bs ∩ L z.2).card :=
        card_le_card (inter_subset_inter_right sdiff_subset)
      omega
    obtain ⟨pre,b,post,he,hLb,hpre⟩ := first_containing U bs (L z.2) hex
    have hplen : pre.length < bs.length := by rw [he,List.length_append,List.length_cons]; omega
    let i : Fin bs.length := ⟨pre.length,hplen⟩
    have htake : bs.take i.val = pre := by simp [i,he]
    have hget : bs[i.val] = b := by simp [i,he,List.getElem_append_right]
    have hpreline : ∀ c ∈ pre, (U c ∩ L z.2).card ≤ 1 := by
      intro c hc
      exact hplane c (by rw [he]; simp [hc]) z.2 hjG (hpre c hc)
    have hci : r ≤ (C i ∩ L z.2).card := by
      have hh := removed_line_le_prefix_cell S U pre b post (L z.2) hLb hpreline
      have hs : ((removed S U bs \ own S U bs z.1) ∩ L z.2).card ≤
          (removed S U bs ∩ L z.2).card :=
        card_le_card (inter_subset_inter_right sdiff_subset)
      have hce : C i = residual S U pre ∩ U b := by
        dsimp [C,indexedCell]
        rw [htake,hget]
      rw [hce]
      rw [← he] at hh
      omega
    have hearlier : z.1 ∈ pre.toFinset.biUnion U := by
      by_contra hn
      have hxpre : ∀ c ∈ pre, z.1 ∉ U c := by
        intro c hc hxc
        exact hn (mem_biUnion.mpr ⟨c,List.mem_toFinset.mpr hc,hxc⟩)
      have hh := outside_inter_prefix S U pre b post (L z.2) hLb z.1 hzx hxpre hpreline
      rw [← he] at hh
      omega
    refine mem_biUnion.mpr ⟨i,mem_univ _,mem_biUnion.mpr ⟨z.2,?_,?_⟩⟩
    · apply mem_filter.mpr
      refine ⟨hjG,?_,?_,hci⟩
      · rw [hget]; exact hLb
      · simpa only [htake] using hpre
    · exact mem_product.mpr ⟨by simpa only [centers,htake] using
        (mem_inter.mpr ⟨hearlier,hzx⟩),mem_singleton_self _⟩
  calc
    _ ≤ ((univ.biUnion (fun i => (E i).biUnion (fun j => centers i j ×ˢ {j}))).card)*
        (r*(r-1)) := Nat.mul_le_mul_right _ (card_le_card hcover)
    _ ≤ (∑ i, (C i).card)^2 :=
      RadialPairCount.centered_rich_lines C E L centers r
        (fun _ _ hj => (mem_filter.mp hj).2.2.2)
        (fun a ha b hb hab => hunique a
          (by obtain ⟨i,_,hi⟩ := mem_biUnion.mp ha; exact (mem_filter.mp hi).1)
          b (by obtain ⟨i,_,hi⟩ := mem_biUnion.mp hb; exact (mem_filter.mp hi).1) hab)
        hcenter (indexedCell_antitone h)
    _ = _ := by rw [indexedCell_sum]

end
end SharpLogRamsey.GreedyPreparation
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma points_mono {U W : Submodule K V} (h : U ≤ W) : planePoints U ⊆ planePoints W := by
  intro x hx
  exact mem_planePoints.mpr ((mem_planePoints.mp hx).trans h)

omit [Finite K] in

lemma join_eq_line (x y : Projectivization K V) (hne : x ≠ y)
    (W : Submodule K V) (hW : Module.finrank K W = 2)
    (hx : x.submodule ≤ W) (hy : y.submodule ≤ W) :
    x.submodule ⊔ y.submodule = W :=
  Submodule.eq_of_le_of_finrank_eq (sup_le hx hy) ((finrank_join x y hne).trans hW.symm)

lemma line_inter_points_le_one (W U : Submodule K V) (hW : Module.finrank K W = 2)
    (hnot : ¬ planePoints W ⊆ planePoints U) :
    (planePoints U ∩ planePoints W).card ≤ 1 := by
  by_contra hn
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (by omega : 1 < (planePoints U ∩ planePoints W).card)
  have hx' := mem_inter.mp hx
  have hy' := mem_inter.mp hy
  have he := join_eq_line x y hxy W hW (mem_planePoints.mp hx'.2) (mem_planePoints.mp hy'.2)
  apply hnot
  apply points_mono
  rw [← he]
  exact sup_le (mem_planePoints.mp hx'.1) (mem_planePoints.mp hy'.1)

lemma distinct_lines_inter_le_one (W U : Submodule K V)
    (hW : Module.finrank K W = 2) (hU : Module.finrank K U = 2) (hne : W ≠ U) :
    (planePoints W ∩ planePoints U).card ≤ 1 := by
  by_contra hn
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (by omega : 1 < (planePoints W ∩ planePoints U).card)
  have hx' := mem_inter.mp hx
  have hy' := mem_inter.mp hy
  have heW := join_eq_line x y hxy W hW (mem_planePoints.mp hx'.1) (mem_planePoints.mp hy'.1)
  have heU := join_eq_line x y hxy U hU (mem_planePoints.mp hx'.2) (mem_planePoints.mp hy'.2)
  exact hne (heW.symm.trans heU)

attribute [local instance] OAI.SharpLogRamsey.PreparedProjectiveGeometry.flat_JoinedPreparedRadial_2
theorem projective_prepared_radial (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V))
    (h : GreedyPreparation.Complete F planePoints m S bs)
    (r : ℕ) (hr : 0 < r) :
    ((univ : Finset (Projectivization K V × ProjectiveLine (K:=K) (V:=V))).filter
      (fun z => z.1 ∈ planePoints z.2.1 ∧ bs.length+r ≤
        ((GreedyPreparation.removed S planePoints bs \
          (GreedyPreparation.own S planePoints bs z.1 ∪ {z.1})) ∩ planePoints z.2.1).card)).card *
      (r*(r-1)) ≤ (GreedyPreparation.removed S planePoints bs).card^2 := by
  have hh := GreedyPreparation.prepared_list_radial h univ univ
    (fun W : ProjectiveLine (K:=K) (V:=V) => planePoints W.1) r hr
    (fun b _ W _ hn => line_inter_points_le_one W.1 b W.2 hn)
    (fun W _ U _ hne => distinct_lines_inter_le_one W.1 U.1 W.2 U.2
      (fun he => hne (Subtype.ext he)))
  apply le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) hh
  intro z hz
  have hz' := (mem_filter.mp hz).2
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_univ _,mem_univ _⟩,hz'.1,hz'.2.trans ?_⟩
  apply card_le_card
  apply inter_subset_inter_right
  exact sdiff_subset_sdiff subset_rfl subset_union_left

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PreparedRadialCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedProjectiveGeometry.flat_JoinedPreparedRadialCount_2
lemma planePoints_card (W : Submodule K V) :
    (planePoints W).card=∑ i∈range (Module.finrank K W),Nat.card K^i := by
  rw [planePoints,←Fintype.card_subtype,←Nat.card_eq_fintype_card,
    ←Nat.card_congr (Incidence.projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

lemma linePoints_card (W : ProjectiveLine (K:=K) (V:=V)) :
    (planePoints W.1).card=Nat.card K+1 := by
  rw [planePoints_card,W.2]
  simp [sum_range_succ,Nat.add_comm]

theorem residual_pairs_le (S : Finset (Projectivization K V))
    (X : Projectivization K V→Finset (Projectivization K V))
    (hX : ∀ x,X x⊆S) (M : ℕ) :
    ((univ : Finset (Projectivization K V × ProjectiveLine (K:=K) (V:=V))).filter
      (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card ≤
    (Nat.card K+1)*((univ : Finset (ProjectiveLine (K:=K) (V:=V))).filter
      (fun W => M≤(S∩planePoints W.1).card)).card := by
  let R := (univ : Finset (ProjectiveLine (K:=K) (V:=V))).filter
      (fun W => M≤(S∩planePoints W.1).card)
  have hs : (univ.filter
      (fun z : Projectivization K V × ProjectiveLine (K:=K) (V:=V) =>
        z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)) ⊆
      R.biUnion (fun W => planePoints W.1 ×ˢ {W}) := by
    intro z hz
    obtain ⟨_,hx,hrich⟩ := mem_filter.mp hz
    apply mem_biUnion.mpr
    refine ⟨z.2,mem_filter.mpr ⟨mem_univ _,hrich.trans ?_⟩,
      mem_product.mpr ⟨hx,mem_singleton_self _⟩⟩
    exact card_le_card (inter_subset_inter_right (hX z.1))
  calc
    _ ≤ (R.biUnion (fun W => planePoints W.1 ×ˢ {W})).card := card_le_card hs
    _ ≤ ∑ W∈R,(planePoints W.1 ×ˢ {W}).card := card_biUnion_le
    _ = (Nat.card K+1)*R.card := by simp [linePoints_card,mul_comm]

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PreparedRadialResidual
open Finset PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]

theorem rich_card (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (M Kp : ℕ) (hM2 : 2≤M) (hMN : M≤S.card)
    (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/M)<M)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/M)<q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M))<1/2)
    (hKM : 8*Kp≤M^2) :
    ((univ : Finset (ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q))).filter
       (fun W => M≤(S∩planePoints W.1).card)).card*M≤8718*S.card := by
  let R := ((univ : Finset (ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q))).filter
       (fun W => M≤(S∩planePoints W.1).card))
  have he (W : ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q)) :
      S∩planePoints W.1=S.filter (fun P => P.submodule≤W.1) := by
    ext P; simp
  have hh := RichFiniteProjective.card_mul_le hq S hS (fun W : {W // W∈R} => W.1.1)
    (fun W => W.1.2) (by intro W U h; exact Subtype.ext (Subtype.ext h)) M Kp hM2 hMN
    (fun W => by simpa only [←he] using (mem_filter.mp W.2).2)
    hcap hsmall hchar hprob hKM
  simpa only [Fintype.card_coe] using hh

attribute [local instance] OAI.SharpLogRamsey.PreparedRadialResidual.flat_JoinedPreparedRadialCount_7
theorem residual_pairs (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
    (hX : ∀ x,X x⊆S) (M Kp : ℕ) (hM2 : 2≤M) (hMN : M≤S.card)
    (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/M)<M)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/M)<q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M))<1/2)
    (hKM : 8*Kp≤M^2) :
    ((univ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q) ×
        ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q))).filter
      (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card*M ≤
      8718*(q+1)*S.card := by
  have h1 := Nat.mul_le_mul_right M (residual_pairs_le S X hX M)
  have h2 := Nat.mul_le_mul_left (q+1) (rich_card hq S hS M Kp hM2 hMN hcap hsmall hchar hprob hKM)
  have hqcard : Nat.card (ZMod q)=q := by simp
  rw [hqcard] at h1
  nlinarith

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_RadialExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.RadialExceptions
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α ι : Type*} [Fintype α]

theorem count_exception (s : α→ℝ) (hs : ∀ x,0 ≤ s x) (K : ℝ) :
    ((univ.filter (fun x => K < s x)).card:ℝ)*K ≤ ∑ x,s x := by
  calc
    _ = ∑ _x∈univ.filter (fun x => K < s x),K := by simp
    _ ≤ ∑ x∈univ.filter (fun x => K < s x),s x :=
      sum_le_sum (fun _ hx => (mem_filter.mp hx).2.le)
    _ ≤ ∑ x,s x := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun x _ _ => hs x)

theorem radial_exceptions (I : Finset ι) (a : ι→ℝ) (ha : ∀ i∈I,0<a i)
    (r : α→ι→ℕ) (q K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hcrude : ∀ x i,i∈I → (r x i:ℝ)*a i≤q)
    (hpair : ∀ i∈I, K<q*a i^99 → (∑ x,(r x i:ℝ))*a i^2≤C) :
    ∃ D : Finset α,
      (D.card:ℝ)*K≤C*∑ i∈I,a i^98 ∧
      ∀ x,x∉D → ∀ i∈I,(r x i:ℝ)*a i^100≤K := by
  let E := fun i => univ.filter (fun x => K<(r x i:ℝ)*a i^100)
  refine ⟨I.biUnion E,?_,?_⟩
  · have hlocal (i : ι) (hi : i∈I) : ((E i).card:ℝ)*K≤C*a i^98 := by
      by_cases he : q*a i^99≤K
      · have hempty : E i=∅ := by
          apply filter_eq_empty_iff.mpr
          intro x _ hx
          have hh := mul_le_mul_of_nonneg_right (hcrude x i hi) (pow_nonneg (ha i hi).le 99)
          have hp : a i*a i^99=a i^100 := by ring
          rw [mul_assoc,hp] at hh
          exact (not_lt_of_ge (hh.trans he)) hx
        rw [hempty,card_empty,Nat.cast_zero,zero_mul]
        positivity
      · have hh := count_exception (fun x => (r x i:ℝ)*a i^100)
          (fun x => by positivity) K
        change ((E i).card:ℝ)*K≤_ at hh
        have hs : (∑ x,(r x i:ℝ)*a i^100)=
            ((∑ x,(r x i:ℝ))*a i^2)*a i^98 := by rw [←sum_mul]; ring
        rw [hs] at hh
        exact hh.trans (mul_le_mul_of_nonneg_right
          (hpair i hi (lt_of_not_ge he)) (pow_nonneg (ha i hi).le 98))
    calc
      _ ≤ (∑ i∈I,((E i).card:ℝ))*K := by
        apply mul_le_mul_of_nonneg_right _ hK
        exact_mod_cast card_biUnion_le (s:=I) (t:=E)
      _ = ∑ i∈I,((E i).card:ℝ)*K := by rw [sum_mul]
      _ ≤ ∑ i∈I,C*a i^98 := sum_le_sum hlocal
      _ = _ := by rw [mul_sum]
  · intro x hx i hi
    exact le_of_not_gt (fun he => hx (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_univ _,he⟩⟩))

theorem strong_exceptions (r : α→ℕ) (a C : ℝ)
    (hpair : (∑ x,(r x:ℝ))*a^2≤C) :
    ∃ D : Finset α,(D.card:ℝ)*a^2≤C ∧ ∀ x,x∉D → r x=0 := by
  let D := univ.filter (fun x => 0 < r x)
  refine ⟨D,?_,?_⟩
  · have hh : (D.card:ℝ)≤∑ x,(r x:ℝ) := by
      calc
        _ = ∑ _x∈D,(1:ℝ) := by simp
        _ ≤ ∑ x∈D,(r x:ℝ) := sum_le_sum (by
          intro x hx; exact_mod_cast (mem_filter.mp hx).2)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intro x _ _; positivity)
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg a)).trans hpair
  · intro x hx
    have hh : ¬0 < r x := by simpa only [D,mem_filter,mem_univ,true_and] using hx
    omega

end
end SharpLogRamsey.RadialExceptions

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem richRadials_mul_le (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c a : ℝ) (hc : 0 ≤ c) : ((richRadials S x c a).card:ℝ)*a ≤ c*S.card := by
  calc
    _ = ∑ _W∈richRadials S x c a,a := by simp
    _ ≤ ∑ W∈richRadials S x c a,strength S x c W :=
      sum_le_sum (fun W hW => (mem_filter.mp hW).2)
    _ ≤ ∑ W,strength S x c W := sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) (fun W _ _ => mul_nonneg hc (Nat.cast_nonneg _))
    _ = c*(S.filter (fun y => y≠x)).card := by
      simpa only [strength,le_top,Finset.filter_true,and_true] using
        radial_mass S x ⊤ le_top c
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_filter_le _ _)) hc

attribute [local instance] OAI.SharpLogRamsey.PreparedProjectiveGeometry.flat_JoinedRadialExceptions_2
theorem sum_richRadials_le_pairs
    (X : Projectivization K V→Finset (Projectivization K V)) (c a : ℝ) (M : ℕ)
    (hM : ∀ x (W : RadialLine x),a ≤ strength (X x) x c W →
      M≤(X x∩planePoints W.1).card) :
    (∑ x,(richRadials (X x) x c a).card)≤
    ((univ : Finset (Projectivization K V × ProjectiveLine (K:=K) (V:=V))).filter
      (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card := by
  let F := (univ : Finset (Projectivization K V)).sigma
    (fun x => richRadials (X x) x c a)
  have he : F.card=∑ x,(richRadials (X x) x c a).card := by simp [F,card_sigma]
  rw [←he]
  let f : (Σ x : Projectivization K V,RadialLine x) →
      Projectivization K V × ProjectiveLine (K:=K) (V:=V) :=
    fun z => (z.1,⟨z.2.1,z.2.2.1⟩)
  apply card_le_card_of_injOn f
  · intro z hz
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,?_⟩
    · exact mem_planePoints.mpr z.2.2.2
    · exact hM z.1 z.2 (mem_filter.mp (mem_sigma.mp hz).2).2
  · rintro ⟨x,W⟩ _ ⟨y,U⟩ _ hh
    have hxy : x=y := congrArg Prod.fst hh
    subst y
    have hWU : W.1=U.1 := congrArg (fun z => z.2.1) hh
    have hWU' : W=U := Subtype.ext hWU
    cases hWU'
    rfl

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PreparedRadialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section

lemma pair_square_budget (P N M J : ℕ) (hJ : 2*J≤M) (hM : 4≤M)
    (hp : P*((M-J)*(M-J-1))≤N^2) : (P:ℝ)*(M:ℝ)^2≤8*(N:ℝ)^2 := by
  have h1 : M≤2*(M-J) := by omega
  have h2 : M≤4*(M-J-1) := by omega
  have h1' : (M:ℝ)≤2*((M-J:ℕ):ℝ) := by exact_mod_cast h1
  have h2' : (M:ℝ)≤4*((M-J-1:ℕ):ℝ) := by exact_mod_cast h2
  have hd : (M:ℝ)^2≤8*((M-J:ℕ):ℝ)*((M-J-1:ℕ):ℝ) := by
    have hh := mul_le_mul h1' h2' (Nat.cast_nonneg M) (by positivity)
    nlinarith
  have hp' : (P:ℝ)*(((M-J:ℕ):ℝ)*((M-J-1:ℕ):ℝ))≤(N:ℝ)^2 := by exact_mod_cast hp
  have hh := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg P)
  nlinarith

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma rich_threshold (X : Finset (Projectivization K V)) (x : Projectivization K V)
    (W : RadialLine x) (a c : ℝ) (hc : 0 < c) (ha : a ≤ strength X x c W) :
    ⌈a/c⌉₊≤(X∩planePoints W.1).card := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hc).mpr
  have hsub : radialFiber X x W⊆X∩planePoints W.1 := by
    intro y hy
    have hh := (mem_radialFiber X x y W).mp hy
    exact mem_inter.mpr ⟨hh.1,mem_planePoints.mpr hh.2.2⟩
  exact ha.trans (by
    have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub)) hc.le
    simpa only [strength,mul_comm] using hh)

attribute [local instance] OAI.SharpLogRamsey.PreparedProjectiveGeometry.flat_JoinedPreparedRadialBounds_2
theorem list_radial_pairs (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V))
    (h : GreedyPreparation.Complete F planePoints m S bs)
    (c a : ℝ) (hc : 0 < c) (ha : 0≤a)
    (hJ : 2*bs.length≤⌈a/c⌉₊) (hM : 4≤⌈a/c⌉₊) :
    (∑ x,((richRadials
      (GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})) x c a).card:ℝ))*a^2≤
      8*(c*(GreedyPreparation.removed S planePoints bs).card)^2 := by
  let X := fun x => GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})
  let M := ⌈a/c⌉₊
  let P := ((univ : Finset (Projectivization K V × ProjectiveLine (K:=K) (V:=V))).filter
    (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card
  have hMJ : bs.length≤M := by dsimp [M]; omega
  have hr : 0<M-bs.length := by dsimp [M]; omega
  have hp := projective_prepared_radial F m S bs h (M-bs.length) hr
  have he : bs.length+(M-bs.length)=M := Nat.add_sub_of_le hMJ
  rw [he] at hp
  change P*((M-bs.length)*(M-bs.length-1))≤_ at hp
  have hp2 := pair_square_budget P (GreedyPreparation.removed S planePoints bs).card M bs.length hJ hM hp
  have hsum : (∑ x,((richRadials (X x) x c a).card:ℝ))≤P := by
    exact_mod_cast sum_richRadials_le_pairs X c a M (fun x W hw => rich_threshold (X x) x W a c hc hw)
  have haM : a ≤ c*M := by
    have hh := Nat.le_ceil (a/c)
    exact (div_le_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  have hsquare : a^2 ≤ c^2*(M:ℝ)^2 := by nlinarith
  have hsum' := mul_le_mul_of_nonneg_right hsum (sq_nonneg a)
  have hPscale := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg P)
  have hfinal := mul_le_mul_of_nonneg_left hp2 (sq_nonneg c)
  change (∑ x,((richRadials (X x) x c a).card:ℝ))*a^2≤_
  nlinarith

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparationInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

lemma own_inter_right (S T : Finset α) (U : β→Finset α) (bs : List β) (x : α) :
    own (S∩T) U bs x=own S U bs x∩T := by
  induction bs generalizing S with
  | nil => simp [own]
  | cons b bs ih =>
    simp only [own]
    split_ifs with hx
    · ext y; simp only [mem_inter]; tauto
    · rw [←sdiff_inter_right_comm,ih]

lemma own_removed (S : Finset α) (U : β→Finset α) (bs : List β) (x : α) :
    own (removed S U bs) U bs x=own S U bs x := by
  rw [removed_eq,own_inter_right]
  apply inter_eq_left.mpr
  have hh := own_subset_removed S U bs x
  rw [removed_eq] at hh
  exact hh.trans inter_subset_right

lemma residual_inter (S T : Finset α) (U : β→Finset α) (bs : List β) :
    residual (S∩T) U bs=residual S U bs∩T := by
  rw [residual_eq,residual_eq]
  exact (sdiff_inter_right_comm _ _ _).symm

lemma indexedCell_inter (S T : Finset α) (U : β→Finset α) (bs : List β) (i : Fin bs.length) :
    indexedCell (S∩T) U bs i=indexedCell S U bs i∩T := by
  simp only [indexedCell,residual_inter]
  ext y; simp only [mem_inter]; tauto

lemma indexedCell_removed (S : Finset α) (U : β→Finset α) (bs : List β) (i : Fin bs.length) :
    indexedCell (removed S U bs) U bs i=indexedCell S U bs i := by
  rw [removed_eq,indexedCell_inter]
  apply inter_eq_left.mpr
  have hh : indexedCell S U bs i⊆removed S U bs := by
    apply cell_subset_removed
    rw [indexedCell_eq]
    exact List.getElem_mem _
  rw [removed_eq] at hh
  exact hh.trans inter_subset_right

end
end SharpLogRamsey.GreedyPreparation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace SharpLogRamsey.ScaleSelection
open Filter Real
open scoped Topology
open SharpLogRamsey.MomentBudgetBridge

theorem eventually_polynomial_le_exp_rpow (C a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ Real.exp (c*x^b) := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound (show 0 < (1/(|C|+1) : ℝ) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    C*x^a ≤ (|C|+1)*x^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx0.le _)
    _ ≤ (|C|+1)*((1/(|C|+1))*Real.exp (c*x^b)) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ = _ := by field_simp

end SharpLogRamsey.ScaleSelection
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_SourceRadialTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

lemma exp_rat (x y : ℝ) : exp x / exp y = exp (x-y) := by
  rw [Real.exp_sub]

theorem threshold_bounds {σ g a : ℝ} {N : ℕ}
    (hσ : 2 ≤ σ) (hg : 0 ≤ g) (ha : exp (-g/20) ≤ a) (ha2 : a ≤ 2)
    (hN : exp (3*σ/2+g)/2 ≤ (N:ℝ)) :
    let M := ⌈a*(N:ℝ)/exp σ⌉₊
    exp (σ/2+19*g/20)/2 ≤ (M:ℝ) ∧
    (M:ℝ) ≤ 3*(N:ℝ)/exp σ ∧
    exp σ/3 ≤ (N:ℝ)/(M:ℝ) ∧
    (N:ℝ)/(M:ℝ) ≤ exp (σ+g/20) := by
  dsimp only
  let M := ⌈a*(N:ℝ)/exp σ⌉₊
  have hN0 : (0:ℝ) < N := (div_pos (exp_pos _) (by norm_num)).trans_le hN
  have ha0 : 0 < a := (exp_pos _).trans_le ha
  have hl : a*(N:ℝ)/exp σ ≤ (M:ℝ) := Nat.le_ceil _
  have hM0 : (0:ℝ) < M := (div_pos (mul_pos ha0 hN0) (exp_pos _)).trans_le hl
  have hmq : a*(N:ℝ) ≤ (M:ℝ)*exp σ := (div_le_iff₀ (exp_pos _)).mp hl
  have hNq : exp σ ≤ (N:ℝ) := by
    have hh : 2 ≤ exp (σ/2+g) := by linarith [Real.add_one_le_exp (σ/2+g)]
    have he : exp (3*σ/2+g)=exp σ*exp (σ/2+g) := by
      rw [←exp_add]; congr 1; ring
    rw [he] at hN
    nlinarith [exp_pos σ]
  have hlo : exp (σ/2+19*g/20)/2 ≤ (M:ℝ) := by
    calc
      _ = exp (-g/20)*(exp (3*σ/2+g)/2)/exp σ := by
        rw [show exp (-g/20)*(exp (3*σ/2+g)/2)/exp σ =
          (exp (-g/20)*exp (3*σ/2+g)/exp σ)/2 by ring,
          ←exp_add,exp_rat]
        congr 2
        ring
      _  ≤  a*(N:ℝ)/exp σ := by gcongr
      _  ≤  _ := hl
  have hup : (M:ℝ) ≤ 3*(N:ℝ)/exp σ := by
    have hm := Nat.ceil_lt_add_one (show 0 ≤ a*(N:ℝ)/exp σ by positivity)
    change (M:ℝ) < _ at hm
    have hq : 1 ≤ (N:ℝ)/exp σ := (one_le_div (exp_pos _)).mpr hNq
    have hh := mul_le_mul_of_nonneg_right ha2 (div_nonneg hN0.le (exp_pos σ).le)
    rw [←mul_div_assoc] at hh
    calc
      (M:ℝ)  ≤  a*(N:ℝ)/exp σ+1 := hm.le
      _  ≤  2*((N:ℝ)/exp σ)+(N:ℝ)/exp σ := add_le_add hh hq
      _ = _ := by ring
  refine ⟨hlo,hup,?_,?_⟩
  · apply (le_div_iff₀ hM0).mpr
    have hh := (le_div_iff₀ (exp_pos _)).mp hup
    nlinarith
  · apply (div_le_iff₀ hM0).mpr
    have hh := mul_le_mul_of_nonneg_right ha hN0.le
    have hexp : exp (-g/20)*exp (σ+g/20)=exp σ := by
      rw [←exp_add]; congr 1; ring
    have H := mul_le_mul_of_nonneg_right (hh.trans hmq) (exp_pos (σ+g/20)).le
    rw [mul_assoc (M:ℝ),mul_comm (exp σ),←mul_assoc (M:ℝ)] at H
    have hs : exp (-g/20)*(N:ℝ)*exp (σ+g/20)=(N:ℝ)*exp σ := by
      rw [mul_right_comm,hexp]
      ring
    rw [hs] at H
    have H' : (N:ℝ)*exp σ ≤ (exp (σ+g/20)*(M:ℝ))*exp σ := by
      simpa only [mul_comm,mul_left_comm,mul_assoc] using H
    exact (mul_le_mul_iff_left₀ (exp_pos σ)).mp H'

theorem rich_tests {σ g m n kp : ℝ}
    (hg : 100000 ≤ g) (hm : exp (σ/2+19*g/20)/2 ≤ m)
    (hr : n/m ≤ exp (σ+g/20)) (hn : 0 ≤ n)
    (hk : kp ≤ 2*exp (σ+17*g/15)) :
    198*sqrt (n/m) < m ∧ 8*kp ≤ m^2 := by
  have hm0 : 0 < m := (div_pos (exp_pos _) (by norm_num)).trans_le hm
  have hsq : exp (σ+19*g/10) ≤ 4*m^2 := by
    have hh := mul_self_le_mul_self (div_nonneg (exp_pos _).le (by norm_num)) hm
    have he : exp (σ/2+19*g/20)^2=exp (σ+19*g/10) := by
      rw [←exp_nat_mul]; congr 1; norm_num; ring
    nlinarith only [hh,he]
  have he : exp (σ+19*g/10)=exp (σ+g/20)*exp (37*g/20) := by
    rw [←exp_add]; congr 1; ring
  have hc : 4*198^2 < exp (37*g/20) := by linarith [add_one_le_exp (37*g/20)]
  have hprod := mul_lt_mul_of_pos_left hc (exp_pos (σ+g/20))
  have hs := sq_sqrt (div_nonneg hn hm0.le)
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ (198:ℝ)^2 by norm_num)
  have hsmall : 198*sqrt (n/m) < m := by
    rw [he] at hsq
    nlinarith [sqrt_nonneg (n/m)]
  have he' : exp (σ+19*g/10)=exp (σ+17*g/15)*exp (23*g/30) := by
    rw [←exp_add]; congr 1; ring
  have hc' : 64 ≤ exp (23*g/30) := by linarith [add_one_le_exp (23*g/30)]
  have hprod' := mul_le_mul_of_nonneg_left hc' (exp_pos (σ+17*g/15)).le
  rw [he'] at hsq
  exact ⟨hsmall,by nlinarith only [hk,hprod',hsq]⟩

theorem characteristic_test {σ g C r : ℝ}
    (hσ : 2000*exp (C/20) ≤ σ) (hg : g ≤ σ/2+C)
    (hr : r ≤ exp (σ+g/20)) : 33*sqrt r < exp σ := by
  have hc : 33^2*exp (C/20) < exp (39*σ/40) := by
    linarith [add_one_le_exp (39*σ/40),exp_pos (C/20)]
  have hr' : r ≤ exp (41*σ/40)*exp (C/20) := by
    rw [←exp_add]
    exact hr.trans (exp_le_exp.mpr (by linarith))
  have H := mul_lt_mul_of_pos_left hc (exp_pos (41*σ/40))
  have he : exp σ^2=exp (41*σ/40)*exp (39*σ/40) := by
    rw [←exp_nat_mul,←exp_add]; congr 1; norm_num; ring
  have hs : sqrt r^2 ≤ exp (41*σ/40)*exp (C/20) := by
    by_cases h : 0 ≤ r
    · rwa [sq_sqrt h]
    · rw [sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
      simpa only [zero_pow (by decide : (2:ℕ)≠0)] using (le_of_lt (mul_pos (exp_pos (41*σ/40)) (exp_pos (C/20))))
  have h0 := sqrt_nonneg r
  nlinarith [exp_pos σ]

theorem failure_test {σ g C n r : ℝ}
    (_hσ : 2 ≤ σ) (hg : g ≤ σ/2+C) (hn : 0 ≤ n)
    (hn' : n ≤ exp (3*σ/2+g))
    (hr : exp σ/3 ≤ r) (hp : 3*σ^4 ≤ exp σ)
    (hc : 4*σ+2*C-5*σ^2 ≤ -2) :
    n^2*exp (-5*sqrt r) < 1/2 := by
  have hr0 : 0 ≤ r := (div_pos (exp_pos _) (by norm_num)).le.trans hr
  have hs : σ^2 ≤ sqrt r := by
    have hs' := sq_sqrt hr0
    have h0 := sqrt_nonneg r
    nlinarith [sq_nonneg σ]
  have hnn : n^2 ≤ exp (3*σ+2*g) := by
    have hh := mul_self_le_mul_self hn hn'
    have he : exp (3*σ/2+g)^2=exp (3*σ+2*g) := by
      rw [←exp_nat_mul]; congr 1; norm_num; ring
    nlinarith only [hh,he]
  have hh : n^2*exp (-5*sqrt r) ≤ exp (-2) := by
    calc
      _  ≤  exp (3*σ+2*g)*exp (-5*sqrt r) :=
        mul_le_mul_of_nonneg_right hnn (exp_pos _).le
      _ = exp (3*σ+2*g-5*sqrt r) := by rw [←exp_add]; congr 1; ring
      _  ≤  _ := exp_le_exp.mpr (by linarith)
  have he : exp (-2) < 1/2 := by
    rw [exp_neg]
    apply (inv_lt_comm₀ (exp_pos _) (by norm_num)).mpr
    norm_num
    linarith [add_one_le_exp (2:ℝ)]
  exact hh.trans_lt he

end
end SharpLogRamsey.SourceRadialTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_SourceRadialUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_rich_tests (δ C : ℝ) (hδ : 0 < δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (g a : ℝ) (N Kp : ℕ),
    σ^δ/10000 ≤ g → g ≤ σ/2+C → exp (-g/20) ≤ a → a ≤ 2 →
    exp (3*σ/2+g)/2 ≤ (N:ℝ) → (N:ℝ) ≤ exp (3*σ/2+g) →
    (Kp:ℝ) ≤ 2*exp (σ+17*g/15) →
    let M := ⌈a*(N:ℝ)/exp σ⌉₊
    4 ≤ M ∧ M ≤ N ∧
    198*sqrt ((N:ℝ)/(M:ℝ)) < (M:ℝ) ∧
    33*sqrt ((N:ℝ)/(M:ℝ)) < exp σ ∧
    (N:ℝ)^2*exp (-5*sqrt ((N:ℝ)/(M:ℝ))) < 1/2 ∧
    8*Kp ≤ M^2 := by
  have hgt : Tendsto (fun σ : ℝ => σ^δ/10000) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm] using
      (tendsto_rpow_atTop hδ).const_mul_atTop (by norm_num : (0:ℝ) < 10000⁻¹)
  have hp := ScaleSelection.eventually_polynomial_le_exp_rpow 3 4 1 1 (by norm_num) (by norm_num)
  filter_upwards [hgt.eventually_ge_atTop 100000,hp,
    eventually_ge_atTop (2:ℝ),eventually_ge_atTop (2000*exp (C/20)),
    eventually_ge_atTop (2*C+2)] with σ hg hp hσ hc hd g a N Kp hgl hgu hal hau hNl hNu hK
  dsimp only
  let M := ⌈a*(N:ℝ)/exp σ⌉₊
  have hg0 : 0 ≤ g := by linarith
  have hg' : 100000 ≤ g := hg.trans hgl
  have hb := threshold_bounds hσ hg0 hal hau hNl
  dsimp only at hb
  change exp (σ/2+19*g/20)/2 ≤ (M:ℝ) ∧ _ at hb
  have hM4 : 4 ≤ M := by
    have he := add_one_le_exp (σ/2+19*g/20)
    have hh : (4:ℝ) ≤ M := by linarith [hb.1]
    exact_mod_cast hh
  have hMN : M ≤ N := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (exp_pos _)).mpr
    have hq : a ≤ exp σ := hau.trans (by linarith [add_one_le_exp σ])
    have hh := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg N : (0:ℝ) ≤ N)
    simpa only [mul_comm] using hh
  have hh := rich_tests hg' hb.1 hb.2.2.2 (Nat.cast_nonneg N) hK
  have hchar := characteristic_test hc hgu hb.2.2.2
  have hp' : 3*σ^4 ≤ exp σ := by simpa only [Real.rpow_ofNat,Real.rpow_one,one_mul] using hp
  have hfail := failure_test hσ hgu (Nat.cast_nonneg N) hNu hb.2.2.1 hp'
    (show 4*σ+2*C-5*σ^2 ≤ -2 by nlinarith [sq_nonneg (σ-1)])
  refine ⟨hM4,hMN,hh.1,hchar,hfail,?_⟩
  exact_mod_cast hh.2

theorem list_threshold {σ g a : ℝ} {N J : ℕ}
    (hσ : 2 ≤ σ) (hg : 100000 ≤ g)
    (ha : exp (-g/20) ≤ a) (ha2 : a ≤ 2)
    (hN : exp (3*σ/2+g)/2 ≤ (N:ℝ))
    (hJ : (J:ℝ) ≤ exp (σ/2-2*g/15)) :
    2*J ≤ ⌈a*(N:ℝ)/exp σ⌉₊ := by
  have hm := (threshold_bounds hσ (by linarith) ha ha2 hN).1
  have he : exp (σ/2+19*g/20)=exp (σ/2-2*g/15)*exp (13*g/12) := by
    rw [←exp_add]; congr 1; ring
  have hc : 4 ≤ exp (13*g/12) := by linarith [add_one_le_exp (13*g/12)]
  have hh := mul_le_mul_of_nonneg_left hc (exp_pos (σ/2-2*g/15)).le
  rw [he] at hm
  have hh' : 2*(J:ℝ) ≤ (⌈a*(N:ℝ)/exp σ⌉₊:ℝ) := by nlinarith only [hJ,hh,hm]
  exact_mod_cast hh'

end
end SharpLogRamsey.SourceRadialTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedResidualBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRadialResidual
open Finset PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]

attribute [local instance] OAI.SharpLogRamsey.PreparedRadialResidual.flat_JoinedPreparedResidualBounds_3
theorem residual_radial_pairs (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
    (hX : ∀ x,X x⊆S) (c a : ℝ) (hc : 0 < c) (ha : 0≤a)
    (Kp : ℕ) (hM2 : 2≤⌈a/c⌉₊) (hMN : ⌈a/c⌉₊≤S.card)
    (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊)<⌈a/c⌉₊)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊)<q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊))<1/2)
    (hKM : 8*Kp≤⌈a/c⌉₊^2) :
    (∑ x,((richRadials (X x) x c a).card:ℝ))*a^2≤
      8718*((q:ℝ)+1)*(c*S.card)*a := by
  let M := ⌈a/c⌉₊
  let P := ((univ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q) ×
        ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q))).filter
      (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card
  have hp : P*M≤8718*(q+1)*S.card :=
    residual_pairs hq S hS X hX M Kp hM2 hMN hcap hsmall hchar hprob hKM
  have hp' : (P:ℝ)*(M:ℝ)≤8718*((q:ℝ)+1)*S.card := by exact_mod_cast hp
  have hsum : (∑ x,((richRadials (X x) x c a).card:ℝ))≤P := by
    exact_mod_cast sum_richRadials_le_pairs X c a M
      (fun x W hw => rich_threshold (X x) x W a c hc hw)
  have haM : a ≤ c*M := by
    have hh := Nat.le_ceil (a/c)
    exact (div_le_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  have hh1 := mul_le_mul_of_nonneg_right hsum ha
  have hh2 := mul_le_mul_of_nonneg_left haM (Nat.cast_nonneg P)
  have hh3 := mul_le_mul_of_nonneg_left hp' hc.le
  have hh : (∑ x,((richRadials (X x) x c a).card:ℝ))*a≤
      8718*((q:ℝ)+1)*(c*S.card) := by nlinarith
  simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right hh ha

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_DyadicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.DyadicGrid
open Finset
open scoped BigOperators
noncomputable section

lemma value_pos (i : ℕ) : 0<value i := by unfold value; positivity
lemma value_le_one (i : ℕ) : value i≤1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)
lemma value_succ (i : ℕ) : value (i+1)=value i/2 := by
  simp only [value,pow_succ,div_eq_mul_inv]; ring

lemma sum_le_two (m : ℕ) : (∑ i∈range m,value i)≤2 := by
  have he : (∑ i∈range m,value i)=2*(1-value m) := by
    induction m with
    | zero => simp [value]
    | succ m ih => rw [sum_range_succ,ih,value_succ]; ring
  rw [he]
  have hp := (value_pos m).le
  linarith

lemma sum_pow_le_two (m r : ℕ) (hr : 1 ≤ r) :
    (∑ i∈range m,(value i)^r)≤2 := by
  apply le_trans _ (sum_le_two m)
  exact sum_le_sum (fun i _ => pow_le_of_le_one (value_pos i).le (value_le_one i) (by omega))

end
end SharpLogRamsey.DyadicGrid

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_PreparedSpatialRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedProjectiveGeometry.flat_JoinedPreparedSpatialRadial_2
theorem list_radial_exceptions (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V))
    (h : GreedyPreparation.Complete F planePoints m S bs)
    (c K₀ : ℝ) (hc : 0 < c) (hK : 0≤K₀) (T : Finset I) (a : I→ℝ)
    (ha : ∀ i∈T,0<a i)
    (hJ : ∀ i∈T,K₀ < c*(GreedyPreparation.removed S planePoints bs).card*a i^99 →
      2*bs.length≤⌈a i/c⌉₊)
    (hM : ∀ i∈T,K₀ < c*(GreedyPreparation.removed S planePoints bs).card*a i^99 →
      4≤⌈a i/c⌉₊) :
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*K₀≤8*(c*(GreedyPreparation.removed S planePoints bs).card)^2*∑ i∈T,a i^98 ∧
      ∀ x,x∉D → ∀ i∈T,
      ((richRadials (GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})) x c (a i)).card:ℝ)*a i^100≤K₀ := by
  let X := fun x => GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})
  let r := fun x i => (richRadials (X x) x c (a i)).card
  apply RadialExceptions.radial_exceptions T a ha r
    (c*(GreedyPreparation.removed S planePoints bs).card) K₀
    (8*(c*(GreedyPreparation.removed S planePoints bs).card)^2) hK (by positivity)
  · intro x i _
    apply (richRadials_mul_le (X x) x c (a i) hc.le).trans
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card sdiff_subset)) hc.le
  · intro i hi hk
    exact list_radial_pairs F m S bs h c (a i) hc (ha i hi).le
      (hJ i hi hk) (hM i hi hk)

theorem list_strong_exceptions (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V))
    (h : GreedyPreparation.Complete F planePoints m S bs)
    (c a : ℝ) (hc : 0 < c) (ha : 0≤a)
    (hJ : 2*bs.length≤⌈a/c⌉₊) (hM : 4≤⌈a/c⌉₊) :
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*a^2≤8*(c*(GreedyPreparation.removed S planePoints bs).card)^2 ∧
      ∀ x,x∉D → (richRadials (GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})) x c a).card=0 := by
  exact RadialExceptions.strong_exceptions _ a _ (list_radial_pairs F m S bs h c a hc ha hJ hM)

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PreparedRadialResidual
open Finset PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]

attribute [local instance] OAI.SharpLogRamsey.PreparedRadialResidual.flat_JoinedPreparedSpatialRadial_5
theorem residual_radial_exceptions {I : Type} (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
    (hX : ∀ x,X x⊆S) (c K₀ : ℝ) (hc : 0 < c) (hK : 0≤K₀)
    (Kp : ℕ) (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (T : Finset I) (a : I→ℝ) (ha : ∀ i∈T,0<a i) (ha2 : ∀ i∈T,a i≤2)
    (htests : ∀ i∈T,K₀ < c*S.card*a i^99 →
      let M := ⌈a i/c⌉₊
      4≤M ∧ M≤S.card ∧
      198*Real.sqrt ((S.card:ℝ)/M)<M ∧
      33*Real.sqrt ((S.card:ℝ)/M)<q ∧
      (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M))<1/2 ∧
      8*Kp≤M^2) :
    ∃ D : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
      (D.card:ℝ)*K₀≤17436*((q:ℝ)+1)*(c*S.card)*∑ i∈T,a i^98 ∧
      ∀ x,x∉D → ∀ i∈T,((richRadials (X x) x c (a i)).card:ℝ)*a i^100≤K₀ := by
  apply RadialExceptions.radial_exceptions T a ha (fun x i => (richRadials (X x) x c (a i)).card)
    (c*S.card) K₀ (17436*((q:ℝ)+1)*(c*S.card)) hK (by positivity)
  · intro x i _
    exact (richRadials_mul_le (X x) x c (a i) hc.le).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card (hX x))) hc.le)
  · intro i hi hk
    obtain ⟨hM,hMN,hs,hch,hp,hKM⟩ := htests i hi hk
    have hh := residual_radial_pairs hq S hS X hX c (a i) hc
      (ha i hi).le Kp (by omega) hMN hcap hs hch hp hKM
    have hz := mul_nonneg
      (show 0≤((q:ℝ)+1)*(c*S.card) by positivity) (sub_nonneg.mpr (ha2 i hi))
    exact hh.trans (by nlinarith only [hz])

theorem residual_strong_exceptions (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
    (hX : ∀ x,X x⊆S) (c a : ℝ) (hc : 0 < c) (ha : 0≤a)
    (Kp : ℕ) (hM2 : 2≤⌈a/c⌉₊) (hMN : ⌈a/c⌉₊≤S.card)
    (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊)<⌈a/c⌉₊)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊)<q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊))<1/2)
    (hKM : 8*Kp≤⌈a/c⌉₊^2) :
    ∃ D : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
      (D.card:ℝ)*a^2≤8718*((q:ℝ)+1)*(c*S.card)*a ∧
      ∀ x,x∉D → (richRadials (X x) x c a).card=0 := by
  exact RadialExceptions.strong_exceptions _ a _
    (residual_radial_pairs hq S hS X hX c a hc ha Kp hM2 hMN hcap hsmall hchar hprob hKM)

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_SourceRadialActivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

theorem radial_activation {σ P g a : ℝ}
    (hP : 10000*(2:ℝ)^99 ≤ P) (ha : 0≤a) (ha2 : a≤2)
    (hk : exp (σ+P/100-2*g)<exp σ*a^99) :
    P/10000<g ∧ exp (-g/20)<a := by
  have he : exp (P/100-2*g)<a^99 := by
    apply (mul_lt_mul_iff_right₀ (exp_pos σ)).mp
    simpa only [←exp_add,show σ+(P/100-2*g)=σ+P/100-2*g by ring] using hk
  have hP0 : 0≤P := (by positivity : (0:ℝ)≤10000*(2:ℝ)^99).trans hP
  have hg : P/10000<g := by
    by_contra hh
    have hgg : g≤P/10000 := le_of_not_gt hh
    have hex : (2:ℝ)^99≤exp (P/100-2*g) := by
      have ht : (2:ℝ)^99≤P/100-2*g+1 := by nlinarith only [hP,hgg]
      exact ht.trans (add_one_le_exp _)
    have haa : a^99≤(2:ℝ)^99 := pow_le_pow_left₀ ha ha2 99
    linarith
  refine ⟨hg,?_⟩
  by_contra hh
  have haa : a≤exp (-g/20) := le_of_not_gt hh
  have hgg : 0≤g := by linarith
  have hpow : a^99≤exp (-99*g/20) := by
    calc
      _ ≤ (exp (-g/20))^99 := pow_le_pow_left₀ ha haa 99
      _ = exp (-99*g/20) := by rw [←exp_nat_mul]; congr 1; norm_num; ring
  have hh' : exp (-99*g/20)≤exp (P/100-2*g) := exp_le_exp.mpr (by linarith)
  exact (not_lt_of_ge (hpow.trans hh')) he

theorem eventually_activated_tests (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (P g a : ℝ) (N Kp : ℕ),
    σ^δ≤P → g≤σ/2+C → 0≤a → a≤2 →
    exp (3*σ/2+g)/2≤(N:ℝ) → (N:ℝ)≤exp (3*σ/2+g) →
    (Kp:ℝ)≤2*exp (σ+17*g/15) →
    exp (σ+P/100-2*g)<exp σ*a^99 →
    let M := ⌈a*(N:ℝ)/exp σ⌉₊
    4≤M ∧ M≤N ∧
    198*sqrt ((N:ℝ)/(M:ℝ))<(M:ℝ) ∧
    33*sqrt ((N:ℝ)/(M:ℝ))<exp σ ∧
    (N:ℝ)^2*exp (-5*sqrt ((N:ℝ)/(M:ℝ)))<1/2 ∧ 8*Kp≤M^2 := by
  filter_upwards [eventually_rich_tests δ C hδ,
    (tendsto_rpow_atTop hδ).eventually_ge_atTop (10000*(2:ℝ)^99)]
    with σ ht hp P g a N Kp hP hgu ha ha2 hN hN' hK hk
  have hh := radial_activation (hp.trans hP) ha ha2 hk
  exact ht g a N Kp ((div_le_div_of_nonneg_right hP (by norm_num)).trans hh.1.le)
    hgu hh.2.le ha2 hN hN' hK

theorem eventually_activated_list (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (P g a : ℝ) (N J : ℕ),
    σ^δ≤P → 0≤a → a≤2 →
    exp (3*σ/2+g)/2≤(N:ℝ) → (J:ℝ)≤exp (σ/2-2*g/15) →
    exp (σ+P/100-2*g)<exp σ*a^99 →
    2*J≤⌈a*(N:ℝ)/exp σ⌉₊ := by
  have ht := (tendsto_rpow_atTop hδ).eventually_ge_atTop (10000*(2:ℝ)^99)
  filter_upwards [ht,eventually_ge_atTop (2:ℝ)] with σ hp hσ P g a N J hP ha ha2 hN hJ hk
  have hh := radial_activation (hp.trans hP) ha ha2 hk
  have hg : 100000≤g := by
    have hc : (100000:ℝ)≤(2:ℝ)^99 := by norm_num
    have hp' := hp.trans hP
    linarith only [hh.1,hp',hc]
  exact list_threshold hσ hg hh.2.le ha2 hN hJ

end
end SharpLogRamsey.SourceRadialTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_SourceRadialScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

theorem radial_exception_scale {σ P g C N D A : ℝ}
    (hA : 0≤A) (hN : exp (3*σ/2+g)/2≤N) (hgu : g≤σ/2+C)
    (hD : D*exp (σ+P/100-2*g)≤A*exp (2*σ))
    (habs : 2*A*exp C≤exp (P/200)) :
    D≤N*exp (-P/200) := by
  have hd : D≤A*exp (σ-P/100+2*g) := by
    apply (mul_le_mul_iff_left₀ (exp_pos (σ+P/100-2*g))).mp
    calc
      _ ≤ A*exp (2*σ) := hD
      _ = A*exp (σ-P/100+2*g)*exp (σ+P/100-2*g) := by
        rw [mul_assoc,←exp_add]
        congr 2
        ring
  calc
    D ≤ A*exp (σ-P/100+2*g) := hd
    _ ≤ A*exp (C+(3*σ/2+g-P/100)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hA
    _ = (A*exp C)*exp (3*σ/2+g-P/100) := by rw [exp_add]; ring
    _ ≤ (exp (P/200)/2)*exp (3*σ/2+g-P/100) :=
      mul_le_mul_of_nonneg_right (by linarith only [habs]) (exp_pos _).le
    _ = (exp (3*σ/2+g)/2)*exp (-P/200) := by
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
      congr 1
      rw [←exp_add,←exp_add]
      congr 1
      ring
    _ ≤ N*exp (-P/200) := mul_le_mul_of_nonneg_right hN (exp_pos _).le

theorem eventually_radial_loss (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (P g N D : ℝ),σ^δ≤P →
      exp (3*σ/2+g)/2≤N → g≤σ/2+C →
      D*exp (σ+P/100-2*g)≤70000*exp (2*σ) →
      D≤N*exp (-P/200) := by
  have ht : Tendsto (fun σ : ℝ => exp (σ^δ/200)) atTop atTop :=
    tendsto_exp_atTop.comp ((tendsto_rpow_atTop hδ).atTop_div_const (by norm_num : (0:ℝ)<200))
  filter_upwards [ht.eventually_ge_atTop (140000*exp C)] with σ hσ P g N D hP hN hgu hD
  apply radial_exception_scale (by norm_num) hN hgu hD
  have hh : 140000*exp C≤exp (P/200) := hσ.trans
    (exp_le_exp.mpr (div_le_div_of_nonneg_right hP (by norm_num)))
  simpa only [show (2:ℝ)*70000=140000 by norm_num] using hh

theorem strong_small_support {σ P N p : ℝ} (hσ : 0≤σ) (hN : 0<N)
    (hNu : N≤exp (2*σ-4*P)) (hp : 0<p) (hpoly : 400*p≤exp P) :
    2*(exp σ+1)/(1/(100*p))≤(exp (3*σ)/N)*exp (-3*P) := by
  have hq : 1≤exp σ := one_le_exp_iff.mpr hσ
  have hb : exp (σ+4*P)≤exp (3*σ)/N := by
    apply (le_div_iff₀ hN).mpr
    calc
      _ ≤ exp (σ+4*P)*exp (2*σ-4*P) := mul_le_mul_of_nonneg_left hNu (exp_pos _).le
      _ = _ := by rw [←exp_add]; congr 1; ring
  calc
    _ = 200*p*(exp σ+1) := by field_simp; ring
    _ ≤ 400*p*exp σ := by nlinarith
    _ ≤ exp P*exp σ := mul_le_mul_of_nonneg_right hpoly (exp_pos _).le
    _ = exp (σ+4*P)*exp (-3*P) := by rw [←exp_add,←exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (exp_pos _).le

end
end SharpLogRamsey.SourceRadialTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_SourceStrongRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_strong_tests (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (P g : ℝ) (N Kp p : ℕ),
    σ^δ≤P → P≤σ/40 → σ/2-4*P≤g → g≤σ/2+C →
    0<p → (p:ℝ)≤σ^2 →
    exp (3*σ/2+g)/2≤(N:ℝ) → (N:ℝ)≤exp (3*σ/2+g) →
    (Kp:ℝ)≤2*exp (σ+17*g/15) →
    let M := ⌈(1/(100*(p:ℝ)))*(N:ℝ)/exp σ⌉₊
    4≤M ∧ M≤N ∧
    198*sqrt ((N:ℝ)/(M:ℝ))<(M:ℝ) ∧
    33*sqrt ((N:ℝ)/(M:ℝ))<exp σ ∧
    (N:ℝ)^2*exp (-5*sqrt ((N:ℝ)/(M:ℝ)))<1/2 ∧ 8*Kp≤M^2 := by
  have ht := ScaleSelection.eventually_polynomial_le_exp_rpow 100 2 1 (1/50)
    (by norm_num) (by norm_num)
  simp only [rpow_one,rpow_ofNat] at ht
  filter_upwards [ht,eventually_rich_tests δ C hδ,eventually_ge_atTop (1:ℝ)]
    with σ hpoly htest hσ P g N Kp p hP hPu hgl hgu hp hpu hN hNu hK
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hg : 2*σ/5≤g := by linarith
  have hpg : 100*(p:ℝ)≤exp (g/20) := by
    calc
      _ ≤ 100*σ^2 := mul_le_mul_of_nonneg_left hpu (by norm_num)
      _ ≤ exp ((1/50)*σ) := hpoly
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have ha : exp (-g/20)≤1/(100*(p:ℝ)) := by
    rw [show -g/20=-(g/20) by ring,exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hpg
  have ha2 : 1/(100*(p:ℝ))≤2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(p:ℝ))).mpr
    have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
    linarith
  apply htest g (1/(100*(p:ℝ))) N Kp _ hgu ha ha2 hN hNu hK
  have hpow : 0≤σ^δ := rpow_nonneg (by linarith : 0≤σ) _
  linarith

theorem eventually_strong_list :
    ∀ᶠ σ : ℝ in atTop,∀ (P g : ℝ) (N J p : ℕ),
    P≤σ/40 → σ/2-4*P≤g → 0<p → (p:ℝ)≤σ^2 →
    exp (3*σ/2+g)/2≤(N:ℝ) → (J:ℝ)≤exp (σ/2-2*g/15) →
    2*J≤⌈(1/(100*(p:ℝ)))*(N:ℝ)/exp σ⌉₊ := by
  have ht := ScaleSelection.eventually_polynomial_le_exp_rpow 100 2 1 (1/50)
    (by norm_num) (by norm_num)
  simp only [rpow_one,rpow_ofNat] at ht
  filter_upwards [ht,eventually_ge_atTop (250000:ℝ)]
    with σ hpoly hσ P g N J p hPu hgl hp hpu hN hJ
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hg : 2*σ/5≤g := by linarith
  have hpg : 100*(p:ℝ)≤exp (g/20) := by
    calc
      _ ≤ 100*σ^2 := mul_le_mul_of_nonneg_left hpu (by norm_num)
      _ ≤ exp ((1/50)*σ) := hpoly
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have ha : exp (-g/20)≤1/(100*(p:ℝ)) := by
    rw [show -g/20=-(g/20) by ring,exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hpg
  have ha2 : 1/(100*(p:ℝ))≤2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(p:ℝ))).mpr
    have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
    linarith
  simpa only [div_eq_mul_inv,mul_assoc] using
    list_threshold (by linarith : 2≤σ) (by linarith : 100000≤g) ha ha2 hN hJ

theorem strong_exception_scale {σ P N D p : ℝ} (hp : 0<p)
    (hN : exp (2*σ-4*P)/2≤N)
    (hD : D*(1/(100*p))^2≤20000*exp (2*σ))
    (hpoly : 400000000*p^2≤exp P) :
    D≤N*exp (5*P) := by
  have hd : D≤200000000*p^2*exp (2*σ) := by
    apply (mul_le_mul_iff_left₀ (show 0<(1/(100*p))^2 by positivity)).mp
    calc
      _ ≤ 20000*exp (2*σ) := hD
      _ = (200000000*p^2*exp (2*σ))*(1/(100*p))^2 := by
        field_simp
        ring
  calc
    D ≤ 200000000*p^2*exp (2*σ) := hd
    _ ≤ (exp P/2)*exp (2*σ) := mul_le_mul_of_nonneg_right (by linarith only [hpoly]) (exp_pos _).le
    _ = (exp (2*σ-4*P)/2)*exp (5*P) := by
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
      congr 1
      rw [←exp_add,←exp_add]
      congr 1
      ring
    _ ≤ N*exp (5*P) := mul_le_mul_of_nonneg_right hN (exp_pos _).le

end
end SharpLogRamsey.SourceRadialTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ResidualSourceRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRadialResidual
open Finset Filter Real PreparedProjectiveGeometry SourceRadialTests
open scoped Classical BigOperators Topology
noncomputable section

theorem source_residual_radial (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),S.Nonempty →
    ∀ (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),
    (∀ x,X x⊆S) → ∀ (P g : ℝ) (Kp p : ℕ),
    σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    exp (3*σ/2+g)/2≤(S.card:ℝ) → (S.card:ℝ)≤exp (3*σ/2+g) →
    (Kp:ℝ)≤2*exp (σ+17*g/15) →
    (∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q,f≠0 →
       (S.filter (fun x => f x.rep=0)).card≤Kp) →
    let c := exp σ/(S.card:ℝ)
    let K₀ := exp (σ+P/100-2*g)
    ∃ D₀ D₁ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
      (D₀.card:ℝ)≤S.card*exp (-P/200) ∧
      (D₁.card:ℝ)≤S.card*exp (5*P) ∧
      (∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S.card+2),
        ((richRadials (X x) x c (DyadicGrid.value i)).card:ℝ)*(DyadicGrid.value i)^100≤K₀) ∧
      (∀ x,x∉D₁ → (richRadials (X x) x c (1/(100*(p:ℝ)))).card=0 ∨
        2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P)) := by
  have hpbound := ScaleSelection.eventually_polynomial_le_exp_rpow 400000000 4 δ 1 hδ (by norm_num)
  simp only [one_mul,rpow_ofNat] at hpbound
  filter_upwards [eventually_activated_tests δ C hδ,eventually_radial_loss δ C hδ,
    eventually_strong_tests δ C hδ,hpbound,eventually_ge_atTop (1:ℝ)]
    with σ htests hloss hstrong hpoly hσ q _ hq heq S hS X hX P g Kp p hP hPu hgu hp hpu hNl hNu hK hcap
  let c := exp σ/(S.card:ℝ)
  let K₀ := exp (σ+P/100-2*g)
  have hN : (0:ℝ)<S.card := Nat.cast_pos.mpr (card_pos.mpr hS)
  have hc : 0 < c := div_pos (exp_pos _) hN
  have hcN : c*S.card=exp σ := div_mul_cancel₀ _ hN.ne'
  have hceil (a : ℝ) : ⌈a/c⌉₊=⌈a*(S.card:ℝ)/exp σ⌉₊ := by
    dsimp [c]
    congr 1
    field_simp
  obtain ⟨D₀,hD₀,hr⟩ := residual_radial_exceptions hq S hS X hX c K₀ hc (exp_pos _).le Kp hcap
    (range (Nat.log 2 S.card+2)) DyadicGrid.value
    (fun i _ => DyadicGrid.value_pos i) (fun i _ => (DyadicGrid.value_le_one i).trans (by norm_num))
    (by
      intro i hi hh
      rw [hcN] at hh
      have ht := htests P g (DyadicGrid.value i) S.card Kp hP hgu
        (DyadicGrid.value_pos i).le ((DyadicGrid.value_le_one i).trans (by norm_num)) hNl hNu hK hh
      simpa only [hceil,heq] using ht)
  have hradial : (D₀.card:ℝ)≤S.card*exp (-P/200) := by
    apply hloss P g S.card D₀.card hP hNl hgu
    have hs := DyadicGrid.sum_pow_le_two (Nat.log 2 S.card+2) 98 (by norm_num)
    rw [←heq,hcN] at hD₀
    have hq1 : 1≤exp σ := one_le_exp_iff.mpr (by linarith)
    have hd : (D₀.card:ℝ)*K₀≤69744*(exp σ)^2 := by
      calc
        _ ≤ 17436*(exp σ+1)*exp σ*2 := mul_le_mul_of_nonneg_left hs (by positivity) |>.trans' hD₀
        _ ≤ _ := by nlinarith [sq_nonneg (exp σ-1)]
    have hsq : (exp σ)^2=exp (2*σ) := by rw [←exp_nat_mul]; norm_num
    rw [hsq] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (by norm_num) (exp_pos _).le)
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
  have hpolyp : 400000000*(p:ℝ)^2≤exp P := by
    calc
      _ ≤ 400000000*(σ^2)^2 := by gcongr
      _ = 400000000*σ^4 := by ring
      _ ≤ exp (σ^δ) := hpoly
      _ ≤ _ := exp_le_exp.mpr hP
  by_cases hsmall : (S.card:ℝ)≤exp (2*σ-4*P)
  · refine ⟨D₀,∅,hradial,by simp; positivity,hr,?_⟩
    intro x _
    right
    exact strong_small_support (by linarith) hN hsmall hp'
      (le_trans (by nlinarith : 400*(p:ℝ)≤400000000*(p:ℝ)^2) hpolyp)
  · have hgl : σ/2-4*P≤g := by
      have hh := (lt_of_not_ge hsmall).trans_le hNu
      have hh' := exp_lt_exp.mp hh
      linarith
    have ht := hstrong P g S.card Kp p hP hPu hgl hgu hp hpu hNl hNu hK
    let a : ℝ := 1/(100*(p:ℝ))
    have ha : 0<a := by dsimp [a]; positivity
    have ha1 : a≤1 := by dsimp [a]; apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(p:ℝ))).mpr; linarith
    have ht' : 4≤⌈a/c⌉₊ ∧ ⌈a/c⌉₊≤S.card ∧
        198*sqrt ((S.card:ℝ)/⌈a/c⌉₊)<⌈a/c⌉₊ ∧
        33*sqrt ((S.card:ℝ)/⌈a/c⌉₊)<q ∧
        (S.card:ℝ)^2*exp (-5*sqrt ((S.card:ℝ)/⌈a/c⌉₊))<1/2 ∧ 8*Kp≤⌈a/c⌉₊^2 := by
      simpa only [hceil,heq] using ht
    obtain ⟨D₁,hD₁,hzero⟩ := residual_strong_exceptions hq S hS X hX c a hc ha.le Kp
      (by omega) ht'.2.1 hcap ht'.2.2.1 ht'.2.2.2.1 ht'.2.2.2.2.1 ht'.2.2.2.2.2
    have hsize : (D₁.card:ℝ)≤S.card*exp (5*P) := by
      have hNl' : exp (2*σ-4*P)/2≤(S.card:ℝ) :=
        (half_le_self (exp_pos _).le).trans (le_of_not_ge hsmall)
      refine strong_exception_scale hp' hNl' ?_ hpolyp
      rw [←heq,hcN] at hD₁
      have hq1 : 1≤exp σ := one_le_exp_iff.mpr (by linarith)
      calc
        _ ≤ 8718*(exp σ+1)*exp σ*a := hD₁
        _ ≤ 8718*(exp σ+1)*exp σ := mul_le_of_le_one_right (by positivity) ha1
        _ ≤ 20000*(exp σ)^2 := by nlinarith [sq_nonneg (exp σ-1)]
        _ = _ := by rw [←exp_nat_mul]; norm_num
    exact ⟨D₀,D₁,hradial,hsize,hr,fun x hx => Or.inl (hzero x hx)⟩

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real Filter PreparedProjectiveGeometry GreedyPreparation
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem low_radial (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (X : Projectivization K V→Finset (Projectivization K V)) (hX : ∀ x,X x⊆S)
    (σ P g : ℝ) (p : ℕ) (hσ : 0≤σ) (hP : 0≤P) (hPu : P≤σ/40)
    (hg : g≤P/10000) (hp : 0<p) (hpoly : 400*(p:ℝ)≤exp P)
    (hNup : (S.card:ℝ)≤exp (3*σ/2+g)) :
    let c := exp σ/(S.card:ℝ)
    (∀ x,∀ i∈range (Nat.log 2 S.card+2),
      ((richRadials (X x) x c (DyadicGrid.value i)).card:ℝ)*(DyadicGrid.value i)^100≤
        exp (σ+P/100-2*g)) ∧
    2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P) := by
  dsimp only
  have hN : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hsmall : (S.card:ℝ)≤exp (2*σ-4*P) := hNup.trans (exp_le_exp.mpr (by linarith))
  refine ⟨?_,SourceRadialTests.strong_small_support hσ hN hsmall (by exact_mod_cast hp) hpoly⟩
  intro x i _
  have hc : 0≤exp σ/(S.card:ℝ) := by positivity
  have ht := richRadials_mul_le (X x) x (exp σ/(S.card:ℝ)) (DyadicGrid.value i) hc
  have ht' : ((richRadials (X x) x (exp σ/(S.card:ℝ)) (DyadicGrid.value i)).card:ℝ)*
      DyadicGrid.value i≤exp σ := by
    apply ht.trans
    calc
      _ ≤ (exp σ/(S.card:ℝ))*(S.card:ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card (hX x))) hc
      _ = exp σ := div_mul_cancel₀ _ hN.ne'
  calc
    _ = (((richRadials (X x) x (exp σ/(S.card:ℝ)) (DyadicGrid.value i)).card:ℝ)*
        DyadicGrid.value i)*(DyadicGrid.value i)^99 := by ring
    _ ≤ exp σ*(DyadicGrid.value i)^99 := mul_le_mul_of_nonneg_right ht' (pow_nonneg (DyadicGrid.value_pos i).le _)
    _ ≤ exp σ*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (DyadicGrid.value_pos i).le (DyadicGrid.value_le_one i)) (exp_pos _).le
    _ ≤ exp (σ+P/100-2*g) := by rw [mul_one]; exact exp_le_exp.mpr (by linarith)

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PrimeListRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset Filter Real SourceRadialTests GreedyPreparation
open scoped Classical BigOperators Topology
noncomputable section

theorem prime_list_radial (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],∀ (F : Finset (Submodule (ZMod q) (Fin 4→ZMod q))) (m : ℕ)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (bs : List (Submodule (ZMod q) (Fin 4→ZMod q))),
    Complete F planePoints m S bs → (removed S planePoints bs).Nonempty →
    ∀ (P g : ℝ) (p : ℕ),σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    exp (3*σ/2+g)/2≤((removed S planePoints bs).card:ℝ) →
    ((removed S planePoints bs).card:ℝ)≤exp (3*σ/2+g) →
    (bs.length:ℝ)≤exp (σ/2-2*g/15) →
    let N := (removed S planePoints bs).card
    let c := exp σ/(N:ℝ)
    let X := fun x => removed S planePoints bs \ (own S planePoints bs x∪{x})
    let K₀ := exp (σ+P/100-2*g)
    ∃ D₀ D₁ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
      (D₀.card:ℝ)≤N*exp (-P/200) ∧ (D₁.card:ℝ)≤N*exp (5*P) ∧
      (∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 N+2),
        ((richRadials (X x) x c (DyadicGrid.value i)).card:ℝ)*(DyadicGrid.value i)^100≤K₀) ∧
      (∀ x,x∉D₁ → (richRadials (X x) x c (1/(100*(p:ℝ)))).card=0 ∨
        2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/N)*exp (-3*P)) := by
  have hpbound := ScaleSelection.eventually_polynomial_le_exp_rpow 400000000 4 δ 1 hδ (by norm_num)
  simp only [one_mul,rpow_ofNat] at hpbound
  filter_upwards [eventually_activated_tests δ C hδ,eventually_activated_list δ hδ,
    eventually_radial_loss δ C hδ,eventually_strong_tests δ C hδ,eventually_strong_list,
    hpbound,eventually_ge_atTop (1:ℝ)]
    with σ htests hlist hloss hstrong hstronglist hpoly hσ q _ F m S bs hprep hnon P g p hP hPu hgu hp hpu hNl hNu hJ
  let N := (removed S planePoints bs).card
  let c := exp σ/(N:ℝ)
  let K₀ := exp (σ+P/100-2*g)
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (card_pos.mpr hnon)
  have hc : 0 < c := div_pos (exp_pos _) hN
  have hcN : c*N=exp σ := div_mul_cancel₀ _ hN.ne'
  have hceil (a : ℝ) : ⌈a/c⌉₊=⌈a*(N:ℝ)/exp σ⌉₊ := by
    dsimp [c]
    congr 1
    field_simp
  have ha i : DyadicGrid.value i≤2 := (DyadicGrid.value_le_one i).trans (by norm_num)
  obtain ⟨D₀,hD₀,hr⟩ := list_radial_exceptions F m S bs hprep c K₀ hc (exp_pos _).le
    (range (Nat.log 2 N+2)) DyadicGrid.value (fun i _ => DyadicGrid.value_pos i)
    (by
      intro i hi hh
      change K₀ < c*N*(DyadicGrid.value i)^99 at hh
      rw [hcN] at hh
      rw [hceil]
      exact hlist P g (DyadicGrid.value i) N bs.length hP (DyadicGrid.value_pos i).le (ha i) hNl hJ hh)
    (by
      intro i hi hh
      change K₀ < c*N*(DyadicGrid.value i)^99 at hh
      rw [hcN] at hh
      rw [hceil]
      exact (htests P g (DyadicGrid.value i) N 0 hP hgu (DyadicGrid.value_pos i).le (ha i) hNl hNu
        (by simp; positivity) hh).1)
  have hradial : (D₀.card:ℝ)≤N*exp (-P/200) := by
    apply hloss P g N D₀.card hP hNl hgu
    have hs := DyadicGrid.sum_pow_le_two (Nat.log 2 N+2) 98 (by norm_num)
    change (D₀.card:ℝ)*K₀≤8*(c*N)^2*∑ i∈range (Nat.log 2 N+2),(DyadicGrid.value i)^98 at hD₀
    rw [hcN] at hD₀
    calc
      _ ≤ 8*(exp σ)^2*2 := hD₀.trans (mul_le_mul_of_nonneg_left hs (by positivity))
      _ ≤ 70000*(exp σ)^2 := by nlinarith [sq_nonneg (exp σ)]
      _ = _ := by rw [←exp_nat_mul]; norm_num
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
  have hpolyp : 400000000*(p:ℝ)^2≤exp P := by
    calc
      _ ≤ 400000000*(σ^2)^2 := by gcongr
      _ = 400000000*σ^4 := by ring
      _ ≤ exp (σ^δ) := hpoly
      _ ≤ _ := exp_le_exp.mpr hP
  by_cases hsmall : (N:ℝ)≤exp (2*σ-4*P)
  · refine ⟨D₀,∅,hradial,by simp; positivity,hr,?_⟩
    intro x _
    right
    exact strong_small_support (by linarith) hN hsmall hp'
      (le_trans (by nlinarith : 400*(p:ℝ)≤400000000*(p:ℝ)^2) hpolyp)
  · have hgl : σ/2-4*P≤g := by
      have hh := (lt_of_not_ge hsmall).trans_le hNu
      have hh' := exp_lt_exp.mp hh
      linarith
    have ht := hstrong P g N 0 p hP hPu hgl hgu hp hpu hNl hNu (by simp; positivity)
    have hJ' := hstronglist P g N bs.length p hPu hgl hp hpu hNl hJ
    obtain ⟨D₁,hD₁,hzero⟩ := list_strong_exceptions F m S bs hprep c (1/(100*(p:ℝ))) hc
      (by positivity) (by simpa only [hceil] using hJ') (by simpa only [hceil] using ht.1)
    have hsize : (D₁.card:ℝ)≤N*exp (5*P) := by
      have hNl' : exp (2*σ-4*P)/2≤(N:ℝ) :=
        (half_le_self (exp_pos _).le).trans (le_of_not_ge hsmall)
      refine strong_exception_scale hp' hNl' ?_ hpolyp
      change (D₁.card:ℝ)*(1/(100*(p:ℝ)))^2≤8*(c*N)^2 at hD₁
      rw [hcN] at hD₁
      calc
        _ ≤ 8*(exp σ)^2 := hD₁
        _ ≤ 20000*(exp σ)^2 := by nlinarith [sq_nonneg (exp σ)]
        _ = _ := by rw [←exp_nat_mul]; norm_num
    exact ⟨D₀,D₁,hradial,hsize,hr,fun x hx => Or.inl (hzero x hx)⟩

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialGreedy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedProjectiveGeometry GreedyPreparation
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma complete_members {α β : Type*} {F : Finset β} {U : β→Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) : ∀ b∈bs,b∈F := by
  induction h with
  | nil => simp
  | cons S b bs hb hr hm ht ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact hb
    · exact ih a ha

omit [Finite K] in
lemma kernel_plane (hdim : Module.finrank K V=4) (f : Module.Dual K V) (hf : f≠0) :
    Module.finrank K (LinearMap.ker f)=3 := by
  have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  omega

lemma filter_kernel (S : Finset (Projectivization K V)) (f : Module.Dual K V) :
    S.filter (fun x => f x.rep=0)=S∩planePoints (LinearMap.ker f) := by
  ext x
  simp only [mem_filter,mem_inter,mem_planePoints,Projectivization.submodule_eq,
    Submodule.span_singleton_le_iff_mem,LinearMap.mem_ker]

attribute [local instance] OAI.SharpLogRamsey.SpatialLearning.flat_JoinedSpatialGreedy_4
theorem greedy (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty) (σ g : ℝ)
    (hσ : 0≤σ) (hg : 0≤g) (hN : (S.card:ℝ)=exp (3*σ/2+g)) :
    let m := ⌈exp (σ+17*g/15)⌉₊
    let F := (univ : Finset (Submodule K V)).filter (fun (W : Submodule K V) => Module.finrank K W=3)
    (∃ W : Submodule K V,Module.finrank K W=3 ∧
      (S.card:ℝ)/50≤(S∩planePoints W).card) ∨
    (∃ S' : Finset (Projectivization K V),S'⊆S ∧ S'.Nonempty ∧ S.card≤2*S'.card ∧
      (m:ℝ)≤2*exp (σ+17*g/15) ∧
      (∀ f : Module.Dual K V, f ≠ 0 → (S'.filter (fun x => f x.rep = 0)).card ≤ m)) ∨
    (∃ bs : List (Submodule K V),Complete F (planePoints (K:=K) (V:=V)) m S bs ∧
      (removed S planePoints bs).Nonempty ∧ S.card≤2*(removed S planePoints bs).card ∧
      (bs.length:ℝ)≤exp (σ/2-2*g/15) ∧
      ∀ i : Fin bs.length,((indexedCell (removed S planePoints bs) planePoints bs i).card:ℝ)/
        (removed S planePoints bs).card≤1/25) := by
  dsimp only
  let m := ⌈exp (σ+17*g/15)⌉₊
  let F := (univ : Finset (Submodule K V)).filter (fun (W : Submodule K V) => Module.finrank K W=3)
  have hm0 : 0< m := Nat.ceil_pos.mpr (exp_pos _)
  have hm : exp (σ+17*g/15)≤(m:ℝ) := Nat.le_ceil _
  have hmup : (m:ℝ)≤2*exp (σ+17*g/15) := by
    have hh := Nat.ceil_lt_add_one (exp_pos (σ+17*g/15)).le
    have he : 1≤exp (σ+17*g/15) := one_le_exp_iff.mpr (by linarith)
    change (m:ℝ)<_ at hh
    linarith
  have hSc : 0<S.card := card_pos.mpr hS
  rcases GreedyPreparation.preparation F (planePoints (K:=K) (V:=V)) m hm0 S with ⟨S',hsub,hhalf,hcap⟩|⟨bs,hbs,hhalf,hJ,_⟩
  · right; left
    refine ⟨S',hsub,card_pos.mp (by omega),hhalf,hmup,?_⟩
    intro f hf
    rw [filter_kernel]
    exact (hcap _ (mem_filter.mpr ⟨mem_univ _,kernel_plane hdim f hf⟩)).le
  · have hn : (removed S planePoints bs).Nonempty := card_pos.mp (by omega)
    by_cases hcell : ∀ i : Fin bs.length,((indexedCell (removed S planePoints bs) planePoints bs i).card:ℝ)/
        (removed S planePoints bs).card≤1/25
    · right; right
      refine ⟨bs,hbs,hn,hhalf,?_,hcell⟩
      have hr : (bs.length:ℝ)*(m:ℝ)≤S.card := by exact_mod_cast hJ
      have hmul : (bs.length:ℝ)*exp (σ+17*g/15)≤exp (3*σ/2+g) :=
        (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)).trans (hr.trans_eq hN)
      have he : exp (σ/2-2*g/15)*exp (σ+17*g/15)=exp (3*σ/2+g) := by
        rw [←exp_add]; congr 1; ring
      rw [←he] at hmul
      exact (mul_le_mul_iff_left₀ (exp_pos _)).mp hmul
    · push Not at hcell
      obtain ⟨i,hi⟩ := hcell
      left
      refine ⟨bs[i],(mem_filter.mp (complete_members hbs _ (List.getElem_mem _))).2,?_⟩
      rw [indexedCell_removed] at hi
      have hnc : (0:ℝ)<(removed S planePoints bs).card := by exact_mod_cast card_pos.mpr hn
      have hh := (lt_div_iff₀ hnc).mp hi
      have hh' : (S.card:ℝ)≤2*(removed S planePoints bs).card := by exact_mod_cast hhalf
      have hs : indexedCell S planePoints bs i⊆S∩planePoints bs[i] := by
        dsimp only [indexedCell]
        intro x hx
        exact mem_inter.mpr ⟨residual_subset S planePoints _ (mem_inter.mp hx).1,(mem_inter.mp hx).2⟩
      have hcc : ((indexedCell S planePoints bs i).card:ℝ)≤(S∩planePoints bs[i]).card :=
        Nat.cast_le.mpr (card_le_card hs)
      linarith

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real Filter PreparedProjectiveGeometry GreedyPreparation
open scoped Classical BigOperators Topology
noncomputable section

theorem prepared_input (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),S.Nonempty →
    ∀ (P g : ℝ) (p : ℕ),σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    (S.card:ℝ)=exp (3*σ/2+g) →
    (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
      (S.card:ℝ)/50≤(S∩planePoints W).card) ∨
    (∃ (S' : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (bs : List (Submodule (ZMod q) (Fin 4→ZMod q))),
      S'⊆S ∧ S'.Nonempty ∧ S.card≤2*S'.card ∧
      (bs.length:ℝ)≤exp (σ/2-2*g/15) ∧
      (∀ W∈bs,Module.finrank (ZMod q) W=3) ∧
      (∀ i : Fin bs.length,((indexedCell S' planePoints bs i).card:ℝ)/(S'.card:ℝ)≤1/25) ∧
      ∃ D₀ D₁ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
        (D₀.card:ℝ)≤S'.card*exp (-P/200) ∧ (D₁.card:ℝ)≤S'.card*exp (5*P) ∧
        (∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S'.card+2),
          ((richRadials (S'\(own S' planePoints bs x∪{x})) x (exp σ/(S'.card:ℝ))
            (DyadicGrid.value i)).card:ℝ)*(DyadicGrid.value i)^100≤exp (σ+P/100-2*g)) ∧
        (∀ x,x∉D₁ →
          (richRadials (S'\(own S' planePoints bs x∪{x})) x (exp σ/(S'.card:ℝ))
            (1/(100*(p:ℝ)))).card=0 ∨
          2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S'.card)*exp (-3*P))) := by
  have hpoly := ScaleSelection.eventually_polynomial_le_exp_rpow 400 2 δ 1 hδ (by norm_num)
  simp only [one_mul,rpow_ofNat] at hpoly
  filter_upwards [PreparedRadialResidual.source_residual_radial δ C hδ,
    prime_list_radial δ C hδ,hpoly,eventually_ge_atTop (1:ℝ)] with σ hres hlist hpol hσ
  intro q _ hq heq S hS P g p hP hPu hgu hp hpu hN
  have hdim : Module.finrank (ZMod q) (Fin 4→ZMod q)=4 := by simp
  have hP0 : 0≤P := (rpow_nonneg (by linarith : 0≤σ) δ).trans hP
  have hNl : exp (3*σ/2+g)/2≤(S.card:ℝ) := by rw [hN]; exact half_le_self (exp_pos _).le
  by_cases hg : g≤P/10000
  · right
    refine ⟨S,[],Subset.rfl,hS,by omega,by simp; positivity,by simp,by simp,∅,∅,?_,?_,?_,?_⟩
    · simp; positivity
    · simp; positivity
    · have hh := low_radial S hS (fun x => S\(own S planePoints [] x∪{x}))
        (fun _ => sdiff_subset) σ P g p (by linarith) hP0 hPu hg hp
        ((mul_le_mul_of_nonneg_left hpu (by norm_num)).trans (hpol.trans (exp_le_exp.mpr hP))) hN.le
      exact fun x _ => hh.1 x
    · have hh := low_radial S hS (fun x => S\(own S planePoints [] x∪{x}))
        (fun _ => sdiff_subset) σ P g p (by linarith) hP0 hPu hg hp
        ((mul_le_mul_of_nonneg_left hpu (by norm_num)).trans (hpol.trans (exp_le_exp.mpr hP))) hN.le
      exact fun _ _ => Or.inr hh.2
  · have hg0 : 0≤g := by linarith
    rcases greedy hdim S hS σ g (by linarith) hg0 hN with hh|⟨S',hsub,hn,hhalf,hm,hcap⟩|⟨bs,hbs,hn,hhalf,hJ,hcell⟩
    · exact Or.inl hh
    · right
      have hNu' : (S'.card:ℝ)≤exp (3*σ/2+g) := (Nat.cast_le.mpr (card_le_card hsub)).trans hN.le
      have hNl' : exp (3*σ/2+g)/2≤(S'.card:ℝ) := by
        have hh : (S.card:ℝ)≤2*S'.card := by exact_mod_cast hhalf
        rw [hN] at hh
        linarith
      refine ⟨S',[],hsub,hn,hhalf,by simp; positivity,by simp,by simp,?_⟩
      exact hres q hq heq S' hn (fun x => S'\(own S' planePoints [] x∪{x}))
        (fun _ => sdiff_subset) P g _ p hP hPu hgu hp hpu hNl' hNu' hm (by
          intro f hf
          convert hcap f hf using 1
          all_goals try with_reducible_and_instances rfl
          congr 1
          ext x
          simp only [mem_filter])
    · right
      have hNu' : ((removed S planePoints bs).card:ℝ)≤exp (3*σ/2+g) :=
        (Nat.cast_le.mpr (card_le_card (removed_subset S planePoints bs))).trans hN.le
      have hNl' : exp (3*σ/2+g)/2≤((removed S planePoints bs).card:ℝ) := by
        have hh : (S.card:ℝ)≤2*(removed S planePoints bs).card := by exact_mod_cast hhalf
        rw [hN] at hh
        linarith
      refine ⟨removed S planePoints bs,bs,removed_subset S planePoints bs,hn,hhalf,hJ,?_,hcell,?_⟩
      · intro W hW
        exact (mem_filter.mp (complete_members hbs W hW)).2
      · simpa only [own_removed] using hlist q _ _ S bs hbs hn P g p hP hPu hgu hp hpu hNl' hNu' hJ

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialInputBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SpatialLearning GreedyPreparation PreparedProjectiveGeometry
open scoped Classical BigOperators Topology NNReal
noncomputable section

theorem actual_prepared_input_oai (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (U S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q)))),
    S⊆U → S.Nonempty → T.Nonempty → S.card≤T.card →
    ∀ (P g b τ : ℝ) (p : ℕ),0≤τ →
    σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    (S.card:ℝ)=exp (3*σ/2+g) →
    (q:ℝ)^4*exp (-b)≤(S.card:ℝ)*T.card →
    (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/q →
    (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
      (S.card:ℝ)/50≤(S∩planePoints W).card) ∨
    (∃ (S' : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (planes : List (Submodule (ZMod q) (Fin 4→ZMod q))),
      S'⊆S ∧ S'.Nonempty ∧ S.card≤2*S'.card ∧
      (planes.length:ℝ)≤exp (σ/2-2*g/15) ∧
      (∀ W∈planes,Module.finrank (ZMod q) W=3) ∧
      Input U S'.card planePoints (sized S' planePoints planes)
        σ P g (b+log 2) (2*τ) (Real.toNNReal ((q:ℝ)/S'.card)) p S') := by
  filter_upwards [prepared_input δ C hδ] with σ hprep
  intro q _ hq hx U S T hSU hS hT hST P g b τ p hτ hP hPu hgu hp hpu hN hprod hsp
  rcases hprep q hq hx S hS P g p hP hPu hgu hp hpu hN with hh|hh
  · exact Or.inl hh
  · obtain ⟨S',planes,hsub,hn,hhalf,hJ,hrank,hcell,D₀,D₁,hD₀,hD₁,hrad,hstrong⟩ := hh
    right
    refine ⟨S',planes,hsub,hn,hhalf,hJ,hrank,?_⟩
    have hc : S'.card≤S.card := card_le_card hsub
    have hc' : (S'.card:ℝ)≤S.card := by exact_mod_cast hc
    have hh' : (S.card:ℝ)≤2*S'.card := by exact_mod_cast hhalf
    have hqp : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
    have hns : (0:ℝ)<S'.card := by exact_mod_cast card_pos.mpr hn
    have he : exp (-(b+log 2))=exp (-b)/2 := by
      rw [neg_add,exp_add,exp_neg (log 2),exp_log (by norm_num : (0:ℝ)<2)]
      ring
    have hmon : Incidence.incidenceCount S' T≤Incidence.incidenceCount S T := by
      apply sum_le_sum
      intro y _
      exact card_le_card (filter_subset_filter _ hsub)
    have hsp' : (Incidence.incidenceCount S' T:ℝ)≤(2*τ)*(S'.card:ℝ)*T.card/q := by
      calc
        _ ≤ (Incidence.incidenceCount S T:ℝ) := by exact_mod_cast hmon
        _ ≤ τ*(S.card:ℝ)*T.card/q := hsp
        _ ≤ τ*(2*S'.card)*T.card/q := by gcongr
        _ = _ := by ring
    have hcq : (Real.toNNReal ((q:ℝ)/S'.card):ℝ)=(q:ℝ)/S'.card :=
      Real.coe_toNNReal _ (by positivity)
    unfold Input
    rw [sized_planes]
    refine ⟨hsub.trans hSU,rfl,hc'.trans hN.le,rfl,hcell,⟨T,hT,hc.trans hST,?_,?_⟩,
      D₀,D₁,hD₀,hD₁,?_,?_⟩
    · have ht : 0≤(T.card:ℝ) := Nat.cast_nonneg _
      rw [Nat.card_eq_fintype_card,ZMod.card,he]
      nlinarith [mul_le_mul_of_nonneg_right hh' ht]
    · simpa only [Nat.card_eq_fintype_card,ZMod.card] using hsp'
    · simpa only [hcq,hx] using hrad
    · simpa only [hcq,hx] using hstrong

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.SpatialPublic.actual_prepared_input_oai := @OAI.SharpLogRamsey.SpatialPublic.actual_prepared_input_oai
