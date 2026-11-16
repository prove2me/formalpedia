-- Prove2me | solution 1 for GenericGroupWE.Main.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-15T11:34:20.165296+00:00
-- url     : https://prove2.me/submissions/71975db0-4a33-49a3-b4a8-63a3260d9b93

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod



namespace GenericGroupWE.Main
open scoped BigOperators
open Polynomial
open Module

theorem polynomial_degree_basis_proved
    (K : Type*) [Field K] (r : ℕ) (W : Submodule K (Polynomial K))
    (b₀ : Basis (Fin r) K W) :
    ∃ b : Basis (Fin r) K W,
      Function.Injective (fun a : Fin r => (b a : Polynomial K).natDegree) := by
  classical
  let size (b : Basis (Fin r) K W) : ℕ := ∑ a : Fin r, (b a : Polynomial K).natDegree
  have hex : ∃ n : ℕ, ∃ b : Basis (Fin r) K W, size b = n := ⟨size b₀, b₀, rfl⟩
  obtain ⟨b, hb⟩ := Nat.find_spec hex
  have hmin (b' : Basis (Fin r) K W) : size b ≤ size b' := by
    rw [hb]
    exact Nat.find_min' hex ⟨b', rfl⟩
  refine ⟨b, ?_⟩
  intro i j hijdeg
  change (b i : Polynomial K).natDegree = (b j : Polynomial K).natDegree at hijdeg
  by_contra hij
  have hi : (b i : Polynomial K) ≠ 0 := by
    intro h
    exact b.ne_zero i (Subtype.ext h)
  have hj : (b j : Polynomial K) ≠ 0 := by
    intro h
    exact b.ne_zero j (Subtype.ext h)
  let u : K := (b i : Polynomial K).leadingCoeff / (b j : Polynomial K).leadingCoeff
  have hli : (b i : Polynomial K).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hi
  have hlj : (b j : Polynomial K).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hj
  have hu : u ≠ 0 := div_ne_zero hli hlj
  have ht : b.coord i (-u • b j) = 0 := by
    simp [Basis.coord_apply, Ne.symm hij]
  let e : W ≃ₗ[K] W := LinearEquiv.transvection ht
  let b' : Basis (Fin r) K W := b.map e
  have hb'i : (b' i : Polynomial K) = (b i : Polynomial K) - u • (b j : Polynomial K) := by
    simp [b', e, LinearMap.transvection.apply, Basis.coord_apply, sub_eq_add_neg]
  have hb'k (k : Fin r) (hk : k ≠ i) : (b' k : Polynomial K) = (b k : Polynomial K) := by
    simp [b', e, LinearMap.transvection.apply, Basis.coord_apply, hk]
  have hnew : (b' i : Polynomial K) ≠ 0 := by
    intro h
    exact b'.ne_zero i (Subtype.ext h)
  have hdeg : (b i : Polynomial K).degree = (u • (b j : Polynomial K)).degree := by
    rw [smul_eq_C_mul, degree_mul, degree_C hu, zero_add,
      degree_eq_natDegree hi, degree_eq_natDegree hj, hijdeg]
  have hlc : (b i : Polynomial K).leadingCoeff =
      (u • (b j : Polynomial K)).leadingCoeff := by
    rw [smul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C]
    exact (div_mul_cancel₀ _ hlj).symm
  have hlt : (b' i : Polynomial K).natDegree < (b i : Polynomial K).natDegree := by
    apply natDegree_lt_natDegree hnew
    rw [hb'i]
    exact degree_sub_lt_left hdeg hi hlc
  have hsize : size b' < size b := by
    apply Finset.sum_lt_sum
    · intro k hk
      by_cases hki : k = i
      · subst k
        exact hlt.le
      · rw [hb'k k hki]
    · exact ⟨i, Finset.mem_univ _, hlt⟩
  exact (not_lt_of_ge (hmin b')) hsize


end GenericGroupWE.Main


namespace GenericGroupWE.Main
open scoped BigOperators
open Polynomial

theorem coeff_prod_sum_of_natDegree_bounds
    {K ι : Type*} [Field K] [DecidableEq ι]
    (s : Finset ι) (f : ι → Polynomial K) (d : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, (f i).natDegree ≤ d i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i :=
      (natDegree_prod_le s f).trans (Finset.sum_le_sum hs)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      coeff_mul_add_eq_of_natDegree_le (hf a (Finset.mem_insert_self _ _)) hprod,
      ih hs, Finset.prod_insert ha]

theorem geometric_top_coefficient_proved
    (K : Type*) [Field K] (r : ℕ) (q : K) (f : Fin r → Polynomial K) :
    (Matrix.of fun a j : Fin r =>
      (f a).comp (C (q ^ j.val) * X)).det.coeff
        (∑ a : Fin r, (f a).natDegree) =
      (∏ a : Fin r, (f a).leadingCoeff) *
        (Matrix.vandermonde (fun a : Fin r => q ^ (f a).natDegree)).det := by
  classical
  calc
    _ = (Matrix.of fun a j : Fin r =>
        (f a).leadingCoeff * (q ^ (f a).natDegree) ^ j.val).det := by
      rw [Matrix.det_apply, finsetSum_coeff, Matrix.det_apply]
      apply Finset.sum_congr rfl
      intro σ hσ
      have hsum : (∑ a : Fin r, (f a).natDegree) =
          ∑ j : Fin r, (f (σ j)).natDegree := by
        exact (Equiv.sum_comp σ (fun a : Fin r => (f a).natDegree)).symm
      rw [hsum, coeff_smul]
      congr 1
      rw [coeff_prod_sum_of_natDegree_bounds]
      · apply Finset.prod_congr rfl
        intro j hj
        simp only [Matrix.of_apply, comp_C_mul_X_coeff, coeff_natDegree]
        rw [← pow_mul, ← pow_mul, Nat.mul_comm j.val (f (σ j)).natDegree]
      · intro j hj
        have hlinear : (C (q ^ j.val) * X : Polynomial K).natDegree ≤ 1 :=
          natDegree_mul_le.trans (by simp)
        exact natDegree_comp_le.trans
          ((Nat.mul_le_mul_left _ hlinear).trans (by simp))
    _ = _ := by
      simpa only [Matrix.vandermonde_apply, Matrix.of_apply, mul_comm] using
        Matrix.det_mul_column (fun a : Fin r => (f a).leadingCoeff)
          (Matrix.vandermonde (fun a : Fin r => q ^ (f a).natDegree))


end GenericGroupWE.Main


namespace GenericGroupWE.Main
open scoped BigOperators
open Polynomial
open Module

-- Intended to be checked after the fully proved local helper declarations.
theorem geometric_determinant_nonzero :
  ∀ (K : Type*) [Field K] (N r : ℕ) (q : K),
  Function.Injective (fun i : Fin (N + 1) => q ^ i.val) →
  ∀ A : Matrix (Fin r) (Fin (N + 1)) K,
    Submodule.span K (Set.range (fun i : Fin (N + 1) => fun a : Fin r => A a i)) = ⊤ →
    (Matrix.of fun a j : Fin r => ∑ i : Fin (N + 1),
      C (A a i) * (C (q ^ j.val) * X) ^ i.val).det ≠ 0 := by
  intro K _ N r q hq A hA
  classical
  change Submodule.span K (Set.range A.col) = ⊤ at hA
  let f : Fin r → Polynomial K := fun a => ∑ i : Fin (N + 1), C (A a i) * X ^ i.val
  have hcoeff (a : Fin r) (i : Fin (N + 1)) : (f a).coeff i.val = A a i := by
    simp [f, coeff_C_mul, coeff_X_pow, Fin.val_inj]
  have hrow : LinearIndependent K A.row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← A.rank_eq_finrank_span_row, A.rank_eq_finrank_span_cols, hA]
    simp
  let F : Polynomial K →ₗ[K] (Fin (N + 1) → K) :=
    LinearMap.pi (fun i => Polynomial.lcoeff K i.val)
  have hf : LinearIndependent K f := by
    apply LinearIndependent.of_comp F
    have heq : F ∘ f = A.row := by
      ext a i
      exact hcoeff a i
    rw [heq]
    exact hrow
  let W := Submodule.span K (Set.range f)
  let b₀ : Basis (Fin r) K W := Basis.span hf
  obtain ⟨b, hbinj⟩ := polynomial_degree_basis_proved K r W b₀
  let g : Fin r → Polynomial K := fun a => (b a : Polynomial K)
  have hfdeg (a : Fin r) : (f a).natDegree ≤ N := by
    apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ i.isLt)
  have hW : W ≤ Polynomial.degreeLE K N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact Polynomial.mem_degreeLE.mpr (natDegree_le_iff_degree_le.mp (hfdeg a))
  have hgdeg (a : Fin r) : (g a).natDegree ≤ N :=
    natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp (hW (b a).property))
  have hpoints : Function.Injective (fun a : Fin r => q ^ (g a).natDegree) := by
    intro a z haz
    apply hbinj
    let a' : Fin (N + 1) := ⟨(g a).natDegree, Nat.lt_succ_of_le (hgdeg a)⟩
    let z' : Fin (N + 1) := ⟨(g z).natDegree, Nat.lt_succ_of_le (hgdeg z)⟩
    exact congrArg Fin.val (hq (show q ^ a'.val = q ^ z'.val from haz))
  have hg0 (a : Fin r) : g a ≠ 0 := by
    intro h
    exact b.ne_zero a (Subtype.ext h)
  let E : Matrix (Fin r) (Fin r) (Polynomial K) :=
    fun a j => (g a).comp (C (q ^ j.val) * X)
  have hdetg : E.det ≠ 0 := by
    have hnonzero : E.det.coeff (∑ a : Fin r, (g a).natDegree) ≠ 0 := by
      change (Matrix.of fun a j : Fin r => (g a).comp (C (q ^ j.val) * X)).det.coeff
        (∑ a : Fin r, (g a).natDegree) ≠ 0
      rw [geometric_top_coefficient_proved]
      apply mul_ne_zero
      · exact Finset.prod_ne_zero_iff.mpr (fun a ha => leadingCoeff_ne_zero.mpr (hg0 a))
      · exact Matrix.det_vandermonde_ne_zero_iff.mpr hpoints
    intro h
    exact hnonzero (by simp [h])
  let fs : Fin r → W := fun a => ⟨f a, Submodule.subset_span (Set.mem_range_self a)⟩
  let T : Matrix (Fin r) (Fin r) K := fun a z => b.equivFun (fs a) z
  have hfs : LinearIndependent K fs := LinearIndependent.of_comp W.subtype hf
  have hTli : LinearIndependent K T.row := by
    exact hfs.map' b.equivFun.toLinearMap (by simp)
  have hTdet : T.det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp (.of_linearIndependent_row hTli)
  have hfexp (a : Fin r) : f a = ∑ z : Fin r, T a z • g z := by
    have heq := congrArg Subtype.val (b.sum_equivFun (fs a))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, T, g, fs] using heq.symm
  have hM : (Matrix.of fun a j : Fin r => ∑ i : Fin (N + 1),
      C (A a i) * (C (q ^ j.val) * X) ^ i.val) = T.map C * E := by
    apply Matrix.ext
    intro a j
    change (∑ i : Fin (N + 1), C (A a i) * (C (q ^ j.val) * X) ^ i.val) =
      ∑ z : Fin r, C (T a z) * E z j
    have hcomp := congrArg (fun v : Polynomial K => v.comp (C (q ^ j.val) * X)) (hfexp a)
    simpa only [f, sum_comp, mul_comp, C_comp, pow_comp, X_comp,
      smul_comp, smul_eq_C_mul, Matrix.mul_apply, Matrix.map_apply, E] using hcomp
  rw [hM, Matrix.det_mul]
  apply mul_ne_zero
  · change (C.mapMatrix T).det ≠ 0
    rw [← RingHom.map_det]
    exact Polynomial.C_ne_zero.mpr hTdet
  · exact hdetg


end GenericGroupWE.Main


namespace GenericGroupWE.Main
open scoped BigOperators
open Polynomial

theorem geometric_matrix_degree (K : Type*) [Field K] (N r : ℕ)
    (q : K) (A : Matrix (Fin r) (Fin (N + 1)) K) :
    (Matrix.of fun a j : Fin r => ∑ i : Fin (N + 1),
      C (A a i) * (C (q ^ j.val) * X) ^ i.val).det.natDegree ≤ N * r := by
  classical
  let M : Matrix (Fin r) (Fin r) (Polynomial K) :=
    fun a j => ∑ i : Fin (N + 1), C (A a i) * (C (q ^ j.val) * X) ^ i.val
  have hentry (a j : Fin r) : (M a j).natDegree ≤ N := by
    dsimp only [M]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    have hlinear : (C (q ^ j.val) * X : Polynomial K).natDegree ≤ 1 :=
      natDegree_mul_le.trans (by simp)
    calc
      _ ≤ (C (A a i)).natDegree + ((C (q ^ j.val) * X) ^ i.val).natDegree :=
        natDegree_mul_le
      _ ≤ 0 + i.val * 1 := by
        simp only [natDegree_C, zero_add]
        exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ hlinear)
      _ ≤ N := by simpa using Nat.le_of_lt_succ i.isLt
  change M.det.natDegree ≤ N * r
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  change (σ.sign • ∏ j : Fin r, M (σ j) j).natDegree ≤ N * r
  calc
    (σ.sign • ∏ j : Fin r, M (σ j) j).natDegree ≤ (∏ j : Fin r, M (σ j) j).natDegree :=
      natDegree_smul_le _ _
    _ ≤ ∑ j : Fin r, (M (σ j) j).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _j : Fin r, N := Finset.sum_le_sum (fun j hj => hentry (σ j) j)
    _ = N * r := by simp [Nat.mul_comm]

theorem two_powers_injective (p N : ℕ) [Fact p.Prime] (hp : 2 ^ N < p) :
    Function.Injective (fun i : Fin (N + 1) => (2 : ZMod p) ^ i.val) := by
  intro i j hij
  have hi : 2 ^ i.val < p := (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ i.isLt)).trans_lt hp
  have hj : 2 ^ j.val < p := (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ j.isLt)).trans_lt hp
  have heq : (2 : ℕ) ^ i.val = 2 ^ j.val := by
    have hcast : ((2 ^ i.val : ℕ) : ZMod p) = ((2 ^ j.val : ℕ) : ZMod p) := by
      simpa using hij
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
    simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod
  apply Fin.ext
  exact (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))) heq

theorem lemma_5_2 (p N : ℕ) [Fact p.Prime] (hp : 2^N < p)
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (c : Fin (N + 1) → V)
    (hpos : 0 < Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range c))) :
    let ρ := Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range c))
    ∃ Δ : Polynomial (ZMod p), Δ ≠ 0 ∧ Δ.natDegree ≤ N * ρ ∧
      ∀ t : ZMod p, Δ.eval t ≠ 0 →
        let ds := fun j : Fin ρ => ∑ i : Fin (N+1),
          ((((2 : ZMod p)^j.val) * t)^i.val) • c i
        LinearIndependent (ZMod p) ds ∧
          Submodule.span (ZMod p) (Set.range ds) = Submodule.span (ZMod p) (Set.range c) := by
  classical
  let K := ZMod p
  let S := Submodule.span K (Set.range c)
  let ρ := Module.finrank K S
  let cs : Fin (N + 1) → S := fun i => ⟨c i, Submodule.subset_span (Set.mem_range_self i)⟩
  let e : S ≃ₗ[K] (Fin ρ → K) := (Module.finBasis K S).equivFun
  let A : Matrix (Fin ρ) (Fin (N + 1)) K := fun a i => e (cs i) a
  have hcs : Submodule.span K (Set.range cs) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff S _).mpr rfl
  have hA : Submodule.span K (Set.range A.col) = ⊤ := by
    have hmap := congrArg (Submodule.map e.toLinearMap) hcs
    change Submodule.span K (Set.range fun i => e (cs i)) = ⊤
    simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearEquiv.range, LinearEquiv.coe_coe, Function.comp_def] using hmap
  let M : Matrix (Fin ρ) (Fin ρ) (Polynomial K) :=
    fun a j => ∑ i : Fin (N + 1), C (A a i) * (C ((2 : K) ^ j.val) * X) ^ i.val
  refine ⟨M.det, geometric_determinant_nonzero K N ρ 2 (two_powers_injective p N hp) A hA,
    geometric_matrix_degree K N ρ 2 A, ?_⟩
  intro t ht
  let ds : Fin ρ → S := fun j => ∑ i : Fin (N + 1),
    ((((2 : K) ^ j.val) * t) ^ i.val) • cs i
  let B : Matrix (Fin ρ) (Fin ρ) K := fun a j => e (ds j) a
  have heval : (Polynomial.evalRingHom t).mapMatrix M = B := by
    ext a j
    change Polynomial.eval t (M a j) = e (ds j) a
    simp [M, ds, A, eval_finsetSum, map_sum, map_smul, mul_comm]
  have hdet : B.det ≠ 0 := by
    rw [← heval, ← RingHom.map_det]
    exact ht
  have heds : LinearIndependent K (fun j => e (ds j)) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hds : LinearIndependent K ds := LinearIndependent.of_comp e.toLinearMap heds
  have hspan : Submodule.span K (Set.range ds) = ⊤ :=
    hds.span_eq_top_of_card_eq_finrank' (by simp [ρ])
  have hcoe : (fun j => (ds j : V)) = fun j : Fin ρ =>
      ∑ i : Fin (N + 1), ((((2 : K) ^ j.val) * t) ^ i.val) • c i := by
    funext j
    simp [ds, cs]
  constructor
  · rw [← hcoe]
    exact hds.map' S.subtype (by simp)
  · rw [← hcoe]
    have hmap := congrArg (Submodule.map S.subtype) hspan
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.map_top, Submodule.range_subtype, Submodule.subtype_apply] using hmap

end GenericGroupWE.Main

open scoped BigOperators
open GenericGroupWE.Main

theorem solution :
  ∀ (p N : ℕ) [Fact p.Prime] (hp : 2^N < p)
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (c : Fin (N + 1) → V)
    (hpos : 0 < Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range c))),
let ρ := Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range c))
    ∃ Δ : Polynomial (ZMod p), Δ ≠ 0 ∧ Δ.natDegree ≤ N * ρ ∧
      ∀ t : ZMod p, Δ.eval t ≠ 0 →
        let ds := fun j : Fin ρ => ∑ i : Fin (N+1),
          ((((2 : ZMod p)^j.val) * t)^i.val) • c i
        LinearIndependent (ZMod p) ds ∧
          Submodule.span (ZMod p) (Set.range ds) = Submodule.span (ZMod p) (Set.range c) := @GenericGroupWE.Main.lemma_5_2
