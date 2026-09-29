-- Prove2me | solution 1 for HeckeEis.eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6c1c936e-06eb-5d21-a7d4-f65e68dde1f5

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self

set_option autoImplicit false

noncomputable section

namespace ATHC13H0

open MvPolynomial HeckeEis CongruenceSubgroup
open scoped MatrixGroups Polynomial

variable {K : Type*} [Field K]

def dvec : Fin 2 → K[X] := ![1, Polynomial.X]

@[scoped simp] theorem dvec_zero : (dvec (K := K)) 0 = 1 := rfl
@[scoped simp] theorem dvec_one : (dvec (K := K)) 1 = Polynomial.X := rfl

def D : MvPolynomial (Fin 2) K →ₐ[K] K[X] := aeval dvec

theorem D_apply (P : MvPolynomial (Fin 2) K) : D P = aeval dvec P := rfl

def δ (a k : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 (a - k) + Finsupp.single 1 k

@[scoped simp] theorem δ_zero (a k : ℕ) : δ a k 0 = a - k := by
  simp [δ]

@[scoped simp] theorem δ_one (a k : ℕ) : δ a k 1 = k := by
  simp [δ]

theorem degree_eq_of_mem_support {a : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous a)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ P.support) : d.degree = a := by
  rw [Finsupp.degree_eq_weight_one]
  exact hP (mem_support_iff.mp hd)

theorem eq_δ_of_degree {a : ℕ} {d : Fin 2 →₀ ℕ} (hd : d.degree = a) : d = δ a (d 1) := by
  have hsum : d 0 + d 1 = a := by
    rw [← hd, Finsupp.degree_eq_sum]
    simp [Fin.sum_univ_two]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, δ_zero]
    omega
  · simp

theorem degree_δ {a k : ℕ} (hk : k ≤ a) : (δ a k).degree = a := by
  rw [Finsupp.degree_eq_sum]
  simp [Fin.sum_univ_two]
  omega

theorem D_monomial (d : Fin 2 →₀ ℕ) (c : K) :
    D (monomial d c) = Polynomial.C c * Polynomial.X ^ (d 1) := by
  rw [D_apply, aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two, Polynomial.C_eq_algebraMap]

theorem coeff_D {a : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous a) (k : ℕ) :
    (D P).coeff k = coeff (δ a k) P := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  simp only [D_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (δ a k)]
  · simp
  · intro d hd hne
    rw [if_neg]
    intro hk
    apply hne
    have := eq_δ_of_degree (degree_eq_of_mem_support hP hd)
    rw [this, ← hk]
  · intro hnot
    simp [notMem_support_iff.mp hnot]

theorem eq_zero_of_D_eq_zero {a : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous a)
    (h : D P = 0) : P = 0 := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_zero]
  by_cases hd : d.degree = a
  · have hk := coeff_D hP (d 1)
    rw [h, Polynomial.coeff_zero] at hk
    rw [eq_δ_of_degree hd]
    exact hk.symm
  · exact hP.coeff_eq_zero hd

theorem natDegree_D_le {a : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous a) :
    (D P).natDegree ≤ a := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_D hP k]
  apply hP.coeff_eq_zero
  rw [Finsupp.degree_eq_sum]
  simp [Fin.sum_univ_two]
  omega

theorem D_binarySubst_upper (P : MvPolynomial (Fin 2) K) :
    D (binarySubst K !![1, 1; 0, 1] P) = (D P).comp (Polynomial.X + 1) := by
  rw [Polynomial.comp_eq_aeval, D_apply, D_apply, binarySubst, comp_aeval_apply, comp_aeval_apply]
  congr 1
  ext j : 1
  fin_cases j <;> simp [Fin.sum_univ_two, dvec, add_comm]

theorem D_binarySubst_lower_X_pow (c : ℤ) (a : ℕ) :
    D (binarySubst K !![1, 0; c, 1] ((X 0 : MvPolynomial (Fin 2) K) ^ a))
      = (1 + Polynomial.C (c : K) * Polynomial.X) ^ a := by
  rw [map_pow, map_pow, binarySubst_X, D_apply]
  simp [Fin.sum_univ_two, dvec]

theorem eq_C_of_comp_X_add_one_eq {p : ℕ} [Fact p.Prime] [CharP K p] (f : K[X])
    (hf : f.comp (Polynomial.X + 1) = f) (hdeg : f.natDegree < p) :
    f = Polynomial.C (f.eval 0) := by
  classical

  have hstep : ∀ m : ℕ, f.eval ((m : K) + 1) = f.eval (m : K) := by
    intro m
    have := congrArg (Polynomial.eval (m : K)) hf
    rwa [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at this
  have hval : ∀ m : ℕ, f.eval (m : K) = f.eval 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ, hstep, ih]
  set g : K[X] := f - Polynomial.C (f.eval 0) with hg
  have hgdeg : g.natDegree < p :=
    lt_of_le_of_lt ((Polynomial.natDegree_sub_le _ _).trans (max_le le_rfl (by simp))) hdeg
  suffices hg0 : g = 0 by
    rwa [hg, sub_eq_zero] at hg0
  by_contra hg0

  let Z : Finset K := (Finset.range p).image (fun m : ℕ => (m : K))
  have hZcard : Z.card = p := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy hxy
    exact CharP.natCast_injOn_Iio K p (Finset.mem_range.mp hx) (Finset.mem_range.mp hy) hxy
  have hZroots : Z.val ⊆ g.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    obtain ⟨m, -, rfl⟩ := hx
    rw [Polynomial.mem_roots hg0, Polynomial.IsRoot.def, hg, Polynomial.eval_sub, Polynomial.eval_C,
      hval m, sub_self]
  have := Polynomial.card_le_degree_of_subset_roots hZroots
  omega

def gT (N : ℕ) : Gamma0 N :=
  ⟨ModularGroup.T, by
    rw [Gamma0_mem, ModularGroup.coe_T]
    simp⟩

@[scoped simp] theorem coe_gT (N : ℕ) : (((gT N : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 1; 0, 1] := by
  simp [gT, ModularGroup.coe_T]

def gL (N : ℕ) : Gamma0 N :=
  ⟨⟨!![1, 0; (N : ℤ), 1], by norm_num [Matrix.det_fin_two_of]⟩, by
    rw [Gamma0_mem]
    simp⟩

@[scoped simp] theorem coe_gL (N : ℕ) : (((gL N : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (N : ℤ), 1] :=
  rfl

theorem D_X_pow (a : ℕ) : D ((X 0 : MvPolynomial (Fin 2) K) ^ a) = 1 := by
  rw [map_pow, D_apply, aeval_X, dvec_zero, one_pow]

theorem main {p : ℕ} [Fact p.Prime] [CharP K p] (N a : ℕ) (ha : 0 < a) (hap : a < p)
    (hpN : ¬ p ∣ N) (P : ↥(BinaryForm K a))
    (hP : ∀ g : Gamma0 N, (binaryFormRepSL K a).comp (Gamma0 N).subtype g P = P) : P = 0 := by
  have hPhom : (P : MvPolynomial (Fin 2) K).IsHomogeneous a := (mem_homogeneousSubmodule a _).mp P.2

  have hT : binarySubst K !![1, 1; 0, 1] (P : MvPolynomial (Fin 2) K) = P := by
    have := congrArg Subtype.val (hP (gT N))
    simpa only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
      binaryFormRepSL_apply_coe, coe_gT] using this
  have hcomp : (D (P : MvPolynomial (Fin 2) K)).comp (Polynomial.X + 1) = D (P : MvPolynomial (Fin 2) K) := by
    rw [← D_binarySubst_upper, hT]
  have hdeg : (D (P : MvPolynomial (Fin 2) K)).natDegree < p :=
    lt_of_le_of_lt (natDegree_D_le hPhom) hap
  set c : K := (D (P : MvPolynomial (Fin 2) K)).eval 0 with hc
  have hDP : D (P : MvPolynomial (Fin 2) K) = Polynomial.C c := eq_C_of_comp_X_add_one_eq _ hcomp hdeg

  have hPX : (P : MvPolynomial (Fin 2) K) = C c * X 0 ^ a := by
    have hhom : ((P : MvPolynomial (Fin 2) K) - C c * X 0 ^ a).IsHomogeneous a :=
      hPhom.sub ((isHomogeneous_X_pow (R := K) (0 : Fin 2) a).C_mul c)
    have hD0 : D ((P : MvPolynomial (Fin 2) K) - C c * X 0 ^ a) = 0 := by
      rw [map_sub, map_mul, D_X_pow, hDP, D_apply, aeval_C, mul_one, Polynomial.C_eq_algebraMap, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_D_eq_zero hhom hD0)

  have hL : binarySubst K !![1, 0; (N : ℤ), 1] (P : MvPolynomial (Fin 2) K) = P := by
    have := congrArg Subtype.val (hP (gL N))
    simpa only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
      binaryFormRepSL_apply_coe, coe_gL] using this
  have hcpow : Polynomial.C c * (1 + Polynomial.C ((N : ℤ) : K) * Polynomial.X) ^ a = Polynomial.C c := by
    have := congrArg D hL
    rw [hPX, map_mul, binarySubst_C, map_mul, D_binarySubst_lower_X_pow, D_apply, aeval_C,
      D_apply, map_mul, aeval_C, map_pow, aeval_X, dvec_zero, one_pow, mul_one] at this
    simpa only [Polynomial.C_eq_algebraMap] using this
  have hc0 : c = 0 := by
    by_contra hc0
    have hpow : (1 + Polynomial.C ((N : ℤ) : K) * Polynomial.X) ^ a = 1 := by
      have h1 : Polynomial.C c * ((1 + Polynomial.C ((N : ℤ) : K) * Polynomial.X) ^ a - 1) = 0 := by
        rw [mul_sub, mul_one, hcpow, sub_self]
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd (Polynomial.C_eq_zero.mp h) hc0
      · exact sub_eq_zero.mp h
    have hN : ((N : ℤ) : K) ≠ 0 := by
      rw [Int.cast_natCast]
      intro h
      exact hpN ((CharP.cast_eq_zero_iff K p N).mp h)
    have hlin : (1 + Polynomial.C ((N : ℤ) : K) * Polynomial.X).natDegree = 1 := by
      rw [add_comm, ← Polynomial.C_1]
      exact Polynomial.natDegree_linear hN
    have := congrArg Polynomial.natDegree hpow
    rw [Polynomial.natDegree_pow, hlin, mul_one, Polynomial.natDegree_one] at this
    omega
  apply Subtype.ext
  rw [hPX, hc0, C_0, zero_mul]
  rfl

end ATHC13H0
p2m_reactivate "P2MW.S_HeckeEis_eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self.ATHC13H0"

end
p2m_reactivate "P2MW.S_HeckeEis_eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self.ATHC13H0"

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (N a : ℕ) (ha : 0 < a) (hap : a < p) (hpN : ¬ p ∣ N)
    (P : ↥(HeckeEis.BinaryForm K a))
    (hP : ∀ g : CongruenceSubgroup.Gamma0 N,
      (HeckeEis.binaryFormRepSL K a).comp (CongruenceSubgroup.Gamma0 N).subtype g P = P) :
    P = 0 :=
  ATHC13H0.main N a ha hap hpN P hP

end S_HeckeEis_eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self
end P2MW
export P2MW.S_HeckeEis_eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self (solution)
