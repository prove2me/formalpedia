-- Prove2me | solution 1 for GenericGroupWE.Main.sec_6_4_rank
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-15T13:07:06.439042+00:00
-- url     : https://prove2.me/submissions/38d0d4ca-14eb-4534-b7ec-7463e2fda73d

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_GenericGroupWE_Main_Tables

-- Local proof module: WitnessEncryption.GeometricDeterminant
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

-- Local proof module: WitnessEncryption.GeometricSpan
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

-- Local proof module: WitnessEncryption.SurvivingRelations
namespace GenericGroupWE.Main
namespace SurvivingProof
open scoped BigOperators
open Module

def optionPoint {K : Type*} [Zero K] [One K] {N : ℕ}
    (b : BooleanAssignment N) : Option (Fin N) → K
  | none => 1
  | some i => booleanPoint b i

noncomputable def extendBit {N d : ℕ} (hd : 1 ≤ d)
    (i : Option (Fin N)) (U : BitMonomial N (d - 1)) : BitMonomial N d :=
  match i with
  | none => ⟨U.val, U.property.trans (Nat.sub_le d 1)⟩
  | some i => ⟨insert i U.val, by have hu := U.property; have hi := Finset.card_insert_le i U.val; omega⟩

theorem column_apply {K : Type*} [Field K] {N d : ℕ} (hd : 1 ≤ d)
    (A : Matrix (StackRow N d) (BitMonomial N d) K)
    (i : Option (Fin N)) (U : BitMonomial N (d - 1)) (row : StackRow N d) :
    survivingColumn hd A i U row = A row (extendBit hd i U) := by
  cases i <;> rfl

theorem split_bit {N d : ℕ} (hd : 1 ≤ d) (S : BitMonomial N d) :
    ∃ (i : Option (Fin N)) (U : BitMonomial N (d - 1)), extendBit hd i U = S := by
  classical
  by_cases hs : S.val = ∅
  · refine ⟨none, ⟨∅, Nat.zero_le _⟩, ?_⟩
    apply Subtype.ext
    simpa [extendBit] using hs.symm
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hc : (S.val.erase i).card ≤ d - 1 := by
      have hcard := Finset.card_erase_of_mem hi
      have hS := S.property
      omega
    refine ⟨some i, ⟨S.val.erase i, hc⟩, ?_⟩
    apply Subtype.ext
    simpa [extendBit] using Finset.insert_erase hi

theorem bitProduct_union {K : Type*} [Field K] {N : ℕ}
    (b : BooleanAssignment N) (S T : Finset (Fin N)) :
    bitProduct (K := K) b (S ∪ T) = bitProduct b S * bitProduct b T := by
  classical
  have hp (U : Finset (Fin N)) : bitProduct (K := K) b U =
      if ∀ i ∈ U, b i = true then 1 else 0 := by
    simp [bitProduct, booleanPoint, Finset.prod_boole]
  rw [hp, hp, hp]
  have hst : (∀ i ∈ S ∪ T, b i = true) ↔
      (∀ i ∈ S, b i = true) ∧ (∀ i ∈ T, b i = true) := by
    constructor
    · intro h
      exact ⟨fun i hi => h i (Finset.mem_union_left _ hi),
        fun i hi => h i (Finset.mem_union_right _ hi)⟩
    · rintro ⟨hs, ht⟩ i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hs i hi
      · exact ht i hi
  by_cases hs : ∀ i ∈ S, b i = true
  · by_cases ht : ∀ i ∈ T, b i = true
    · rw [if_pos (hst.mpr ⟨hs, ht⟩), if_pos hs, if_pos ht, one_mul]
    · rw [if_neg (fun h => ht (hst.mp h).2), if_pos hs, if_neg ht, mul_zero]
  · by_cases ht : ∀ i ∈ T, b i = true
    · rw [if_neg (fun h => hs (hst.mp h).1), if_neg hs, if_pos ht, zero_mul]
    · rw [if_neg (fun h => hs (hst.mp h).1), if_neg hs, if_neg ht, zero_mul]

theorem bitProduct_extend {K : Type*} [Field K] {N d : ℕ} (hd : 1 ≤ d)
    (b : BooleanAssignment N) (i : Option (Fin N)) (U : BitMonomial N (d - 1)) :
    bitProduct (K := K) b (extendBit hd i U).val = optionPoint b i * bitProduct b U.val := by
  classical
  cases i with
  | none => simp [extendBit, optionPoint]
  | some i =>
    have hh := bitProduct_union (K := K) b {i} U.val
    simpa [extendBit, optionPoint, bitProduct] using hh

theorem stack_apply {K : Type*} [Field K] {N d : ℕ}
    (coefficients : BooleanAssignment N → K) (row : StackRow N d) (col : BitMonomial N d) :
    representedStack coefficients row col =
      ∑ b, coefficients b * stackWeight row.1 b * bitProduct b row.2.val * bitProduct b col.val := by
  simp only [representedStack, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    assignmentStack]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem surviving_pos {K : Type*} [Field K] {N d : ℕ} (hd : 1 ≤ d)
    (A : Matrix (StackRow N d) (BitMonomial N d) K) (hne : A ≠ 0) :
    1 ≤ survivingDimension hd A := by
  classical
  apply Submodule.one_le_finrank_iff.mpr
  intro hz
  apply hne
  apply Matrix.ext
  intro row col
  obtain ⟨i, U, hi⟩ := split_bit hd col
  have hmem := Submodule.subset_span (R := K) (Set.mem_range_self (f := survivingColumn hd A) i)
  rw [hz] at hmem
  have hzero : survivingColumn hd A i = 0 := hmem
  have heq := congrFun (congrFun hzero U) row
  simpa only [column_apply, hi, Pi.zero_apply, Matrix.zero_apply] using heq

theorem split_set {N a b : ℕ} (S : Finset (Fin N)) (hS : S.card ≤ a + b) :
    ∃ (U : BitMonomial N a) (V : BitMonomial N b), U.val ∪ V.val = S := by
  classical
  obtain ⟨U, hUS, hU⟩ := Finset.exists_subset_card_eq (Nat.min_le_right a S.card)
  have hV : (S \ U).card ≤ b := by
    rw [Finset.card_sdiff_of_subset hUS, hU]
    omega
  exact ⟨⟨U, by rw [hU]; exact Nat.min_le_left _ _⟩, ⟨S \ U, hV⟩,
    Finset.union_sdiff_of_subset hUS⟩

theorem eval_monomial_boolean {K : Type*} [Field K] {N : ℕ}
    (b : BooleanAssignment N) (e : Fin N →₀ ℕ) (c : K) :
    MvPolynomial.eval (booleanPoint b) (MvPolynomial.monomial e c) =
      c * bitProduct b e.support := by
  classical
  rw [MvPolynomial.eval_monomial]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have he : e i ≠ 0 := Finsupp.mem_support_iff.mp hi
  by_cases hb : b i = true <;> simp [booleanPoint, hb, he]

theorem support_card_le {N : ℕ} (e : Fin N →₀ ℕ) : e.support.card ≤ e.sum (fun _ n => n) := by
  classical
  calc
    e.support.card = ∑ _i ∈ e.support, 1 := by simp
    _ ≤ ∑ i ∈ e.support, e i := Finset.sum_le_sum
      (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem polynomial_zero_of_bitProducts {K : Type*} [Field K] {N e : ℕ}
    (w : BooleanAssignment N → K)
    (hw : ∀ S : Finset (Fin N), S.card ≤ e → ∑ b, w b * bitProduct b S = 0)
    (f : MvPolynomial (Fin N) K) (hf : f.totalDegree ≤ e) :
    ∑ b, w b * MvPolynomial.eval (booleanPoint b) f = 0 := by
  classical
  rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  have hcard : m.support.card ≤ e :=
    (support_card_le m).trans ((MvPolynomial.le_totalDegree hm).trans hf)
  simp_rw [eval_monomial_boolean]
  calc
    ∑ b, w b * (MvPolynomial.coeff m f * bitProduct b m.support) =
      MvPolynomial.coeff m f * ∑ b, w b * bitProduct b m.support := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
    _ = 0 := by rw [hw m.support hcard, mul_zero]

theorem relation_propagates {K : Type*} [Field K] {N d : ℕ} (hd : 1 ≤ d)
    (coefficients : BooleanAssignment N → K) (κ : Option (Fin N) → K)
    (hκ : (∑ i, κ i • survivingColumn hd (representedStack coefficients) i) = 0)
    (h : WeightLabel N d) (f : MvPolynomial (Fin N) K)
    (hf : f.totalDegree + 1 ≤ 2 * d) :
    ∑ b, coefficients b * affineBit κ b * stackWeight h b *
      MvPolynomial.eval (booleanPoint b) f = 0 := by
  classical
  have hbase (S : BitMonomial N d) (U : BitMonomial N (d - 1)) :
      ∑ b, coefficients b * affineBit κ b * stackWeight h b *
        (bitProduct b S.val * bitProduct b U.val) = 0 := by
    have heq := congrFun (congrFun hκ U) (h, S)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heq
    change (∑ i, κ i * survivingColumn hd (representedStack coefficients) i U (h, S)) = 0 at heq
    simp_rw [column_apply, stack_apply, bitProduct_extend] at heq
    have ha (b : BooleanAssignment N) : ∑ i, κ i * optionPoint b i = affineBit κ b := by
      simp [Fintype.sum_option, optionPoint, affineBit]
    calc
      _ = ∑ b, ∑ i, κ i * (coefficients b * stackWeight h b * bitProduct b S.val *
          (optionPoint b i * bitProduct b U.val)) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [← ha, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by
        rw [Finset.sum_comm]
        simpa only [Finset.mul_sum] using heq
  apply polynomial_zero_of_bitProducts (e := d + (d - 1))
      (fun b => coefficients b * affineBit κ b * stackWeight h b) ?_ f (by omega)
  intro S hS
  obtain ⟨U, V, hUV⟩ := split_set (a := d) (b := d - 1) S hS
  simpa only [← bitProduct_union, hUV] using hbase U V


end SurvivingProof
end GenericGroupWE.Main


open scoped BigOperators
namespace GenericGroupWE.Main

theorem surviving_relation_propagates :
  ∀ {K : Type*} [Field K] {N d : ℕ} (hd : 1 ≤ d)
  (coefficients : BooleanAssignment N → K) (κ : Option (Fin N) → K),
  (∑ i, κ i • survivingColumn hd (representedStack coefficients) i) = 0 →
  ∀ (h : WeightLabel N d) (f : MvPolynomial (Fin N) K),
    f.totalDegree + 1 ≤ 2*d →
      ∑ b, coefficients b * affineBit κ b * stackWeight h b *
        MvPolynomial.eval (booleanPoint b) f = 0 := by
  intro K _ N d hd coefficients κ hκ h f hf
  exact SurvivingProof.relation_propagates hd coefficients κ hκ h f hf

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.UsefulSample
namespace GenericGroupWE.Main
namespace StackRankProof
open scoped BigOperators
open Polynomial

noncomputable def sampleFormPolynomial {K : Type*} [Field K] {N : ℕ}
    (j : ℕ) (b : BooleanAssignment N) : Polynomial K :=
  1 + ∑ i : Fin N, C (booleanPoint b i) * (C ((2 : K) ^ j) * X) ^ (i.val + 1)

theorem sampleForm_degree {K : Type*} [Field K] {N : ℕ} (j : ℕ)
    (b : BooleanAssignment N) : (sampleFormPolynomial (K := K) j b).natDegree ≤ N := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    have hlinear : (C ((2 : K) ^ j) * X).natDegree ≤ 1 :=
      natDegree_mul_le.trans (by simp)
    calc
      _ ≤ (C (booleanPoint b i)).natDegree +
          ((C ((2 : K) ^ j) * X) ^ (i.val + 1)).natDegree := natDegree_mul_le
      _ ≤ 0 + (i.val + 1) * 1 := by
        simp only [natDegree_C, zero_add]
        exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ hlinear)
      _ ≤ N := by simpa using Nat.succ_le_of_lt i.isLt

theorem sampleForm_eval {K : Type*} [Field K] {N : ℕ} (j t : ℕ)
    (b : BooleanAssignment N) :
    (sampleFormPolynomial (K := K) j b).eval (t : K) = geometricForm j t b := by
  simp [sampleFormPolynomial, Polynomial.eval_finsetSum, geometricForm, mul_comm]

noncomputable def sampleWeightPolynomial {K : Type*} [Field K] {N d : ℕ}
    (α : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
    (b : BooleanAssignment N) : Polynomial K :=
  ∏ j : Fin ((rankTarget N d)^2), (sampleFormPolynomial j.val b) ^ (α.val j).val

theorem sampleWeight_degree {K : Type*} [Field K] {N d : ℕ}
    (α : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
    (b : BooleanAssignment N) :
    (sampleWeightPolynomial (K := K) α b).natDegree ≤ N * weightDegree N := by
  classical
  calc
    _ ≤ ∑ j : Fin ((rankTarget N d)^2),
        ((sampleFormPolynomial (K := K) j.val b) ^ (α.val j).val).natDegree :=
      natDegree_prod_le _ _
    _ ≤ ∑ j : Fin ((rankTarget N d)^2), (α.val j).val * N :=
      Finset.sum_le_sum (fun j hj => natDegree_pow_le.trans
        (Nat.mul_le_mul_left _ (sampleForm_degree j.val b)))
    _ = (∑ j : Fin ((rankTarget N d)^2), (α.val j).val) * N :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ N * weightDegree N := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right N α.property

noncomputable def sampleEntryPolynomial {K : Type*} [Field K] {N d : ℕ}
    (coefficients : BooleanAssignment N → K)
    (α : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
    (S T : BitMonomial N d) : Polynomial K :=
  ∑ b, C (coefficients b * bitProduct b S.val * bitProduct b T.val) *
    sampleWeightPolynomial α b

theorem sampleEntry_degree {K : Type*} [Field K] {N d : ℕ}
    (coefficients : BooleanAssignment N → K)
    (α : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
    (S T : BitMonomial N d) :
    (sampleEntryPolynomial coefficients α S T).natDegree ≤ N * weightDegree N := by
  apply natDegree_sum_le_of_forall_le
  intro b hb
  apply natDegree_mul_le.trans
  simpa only [natDegree_C, zero_add] using sampleWeight_degree (K := K) α b

theorem sampleEntry_eval {K : Type*} [Field K] {N d : ℕ}
    (coefficients : BooleanAssignment N → K)
    (α : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
    (S T : BitMonomial N d)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1)) :
    (sampleEntryPolynomial coefficients α S T).eval (t.val : K) =
      sampleStack (representedStack (d := d) coefficients) t (α, S) T := by
  classical
  change (sampleEntryPolynomial coefficients α S T).eval (t.val : K) =
    representedStack coefficients ((t, α), S) T
  rw [SurvivingProof.stack_apply]
  simp only [sampleEntryPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, sampleWeightPolynomial, Polynomial.eval_prod, Polynomial.eval_pow,
    sampleForm_eval, stackWeight]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem nat_samples_injective (p M : ℕ) (hp : M < p) :
    Function.Injective (fun i : Fin (M + 1) => (i.val : ZMod p)) := by
  intro i j hij
  apply Fin.ext
  have hi : i.val < p := (Nat.le_of_lt_succ i.isLt).trans_lt hp
  have hj : j.val < p := (Nat.le_of_lt_succ j.isLt).trans_lt hp
  have hh := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hij
  simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hh

theorem joint_useful_sample_aux
    (p N d : ℕ) [Fact p.Prime] (hd : 1 ≤ d)
    (hp : max (2 ^ N) (N * ((rankTarget N d) ^ 2 + weightDegree N)) < p)
    (coefficients : BooleanAssignment N → ZMod p)
    (hne : representedStack (d := d) coefficients ≠ 0)
    (havailable : survivingDimension hd (representedStack (d := d) coefficients) ≤
      (rankTarget N d) ^ 2) :
    ∃ (t : Fin (N * ((rankTarget N d) ^ 2 + weightDegree N) + 1))
      (μ : Fin N → Fin (survivingDimension hd (representedStack (d := d) coefficients)) → ZMod p),
      IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ ∧
        sampleStack (representedStack (d := d) coefficients) t ≠ 0 := by
  classical
  let K := ZMod p
  let A := representedStack (d := d) coefficients
  let δ := survivingDimension hd A
  let V := BitMonomial N (d - 1) → StackRow N d → K
  let c : Fin (N + 1) → V :=
    Fin.cases (survivingColumn hd A none) (fun i => survivingColumn hd A (some i))
  have hc : Set.range c = Set.range (survivingColumn hd A) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact ⟨none, rfl⟩
      | succ i => exact ⟨some i, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact ⟨0, rfl⟩
      | some i => exact ⟨i.succ, rfl⟩
  have hdim : Module.finrank K (Submodule.span K (Set.range c)) = δ := by rw [hc]; rfl
  have hpos : 0 < Module.finrank K (Submodule.span K (Set.range c)) := by
    rw [hdim]
    have hh := SurvivingProof.surviving_pos hd A hne
    omega
  obtain ⟨Δ, hΔ, hΔdeg, hΔgood⟩ :=
    lemma_5_2 p N ((Nat.le_max_left _ _).trans_lt hp) V c hpos
  rw [hdim] at hΔdeg hΔgood
  have hds (t : ℕ) :
      (fun j : Fin δ => ∑ i : Fin (N + 1),
        ((((2 : K)^j.val) * (t : K))^i.val) • c i) =
      fun j : Fin δ => geometricColumn hd A j.val t := by
    funext j
    simp [Fin.sum_univ_succ, c, geometricColumn]
  have hentry : ∃ (row : StackRow N d) (col : BitMonomial N d), A row col ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hne
    apply Matrix.ext
    exact hh
  obtain ⟨row, T, hentry⟩ := hentry
  rcases row with ⟨⟨t₀, α⟩, S⟩
  let F := sampleEntryPolynomial coefficients α S T
  have hF : F ≠ 0 := by
    intro hz
    apply hentry
    have heq := sampleEntry_eval coefficients α S T t₀
    change F.eval (t₀.val : K) = A ((t₀, α), S) T at heq
    exact heq.symm.trans (by simp [hz])
  let M := N * ((rankTarget N d)^2 + weightDegree N)
  have hprod : F * Δ ≠ 0 := mul_ne_zero hF hΔ
  have hproddeg : (F * Δ).natDegree ≤ M := by
    calc
      _ ≤ F.natDegree + Δ.natDegree := natDegree_mul_le
      _ ≤ N * weightDegree N + N * δ :=
        Nat.add_le_add (sampleEntry_degree coefficients α S T) hΔdeg
      _ ≤ N * weightDegree N + N * ((rankTarget N d)^2) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left N havailable) _
      _ = M := by dsimp [M]; ring
  have hsome : ∃ t : Fin (M + 1), (F * Δ).eval (t.val : K) ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hprod
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (F * Δ)
      (nat_samples_injective p M ((Nat.le_max_right _ _).trans_lt hp)) hh
      (by simpa using Nat.lt_succ_of_le hproddeg)
  obtain ⟨t, ht⟩ := hsome
  have hFval : F.eval (t.val : K) ≠ 0 := by
    rw [Polynomial.eval_mul] at ht
    exact (mul_ne_zero_iff.mp ht).1
  have hΔval : Δ.eval (t.val : K) ≠ 0 := by
    rw [Polynomial.eval_mul] at ht
    exact (mul_ne_zero_iff.mp ht).2
  have hgood := hΔgood (t.val : K) hΔval
  rw [hds t.val, hc] at hgood
  have hcoeff (i : Fin N) : ∃ a : Fin δ → K,
      ∑ j, a j • geometricColumn hd A j.val t.val = survivingColumn hd A (some i) := by
    apply (Submodule.mem_span_range_iff_exists_fun K).mp
    rw [hgood.2]
    exact Submodule.subset_span (Set.mem_range_self _)
  choose μ hμ using hcoeff
  refine ⟨t, μ, ⟨hgood.1, hgood.2, fun i => (hμ i).symm⟩, ?_⟩
  intro hz
  apply hFval
  rw [sampleEntry_eval]
  exact congrFun (congrFun hz (α, S)) T


end StackRankProof
end GenericGroupWE.Main


open scoped BigOperators
namespace GenericGroupWE.Main

theorem joint_useful_sample :
  ∀ (p N d : ℕ) [Fact p.Prime] (hd : 1 ≤ d)
    (hp : max (2 ^ N) (N * ((rankTarget N d) ^ 2 + weightDegree N)) < p)
    (coefficients : BooleanAssignment N → ZMod p)
    (hne : representedStack (d := d) coefficients ≠ 0)
    (havailable : survivingDimension hd (representedStack (d := d) coefficients) ≤
      (rankTarget N d) ^ 2),
    ∃ (t : Fin (N * ((rankTarget N d) ^ 2 + weightDegree N) + 1))
      (μ : Fin N → Fin (survivingDimension hd (representedStack (d := d) coefficients)) → ZMod p),
      IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ ∧
        sampleStack (representedStack (d := d) coefficients) t ≠ 0 := by
  intro p N d _ hd hp coefficients hne havailable
  exact StackRankProof.joint_useful_sample_aux p N d hd hp coefficients hne havailable

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.SurvivingColumns
namespace GenericGroupWE.Main
namespace SurvivingProof
open scoped BigOperators
open Module

theorem exists_actual_row_expansion {K R C : Type*} [Field K] [Fintype R] [Fintype C]
    (A : Matrix R C K) :
    ∃ (r : Fin A.rank → R) (P : R → Fin A.rank → K),
      ∀ row col, A row col = ∑ v, P row v * A (r v) col := by
  classical
  rw [A.rank_eq_finrank_span_row]
  let W := Submodule.span K (Set.range A.row)
  let ρ := Module.finrank K W
  obtain ⟨f, hfmem, hfspan, hfLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  choose r hr using hfmem
  let fs : Fin ρ → W := fun i => ⟨f i, Submodule.subset_span ⟨r i, hr i⟩⟩
  have hfs : LinearIndependent K fs := LinearIndependent.of_comp W.subtype hfLI
  have hspan : Submodule.span K (Set.range fs) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff W _).mpr hfspan
  let b : Basis (Fin ρ) K W := Basis.mk hfs hspan.ge
  let P : R → Fin ρ → K := fun row =>
    b.equivFun ⟨A.row row, Submodule.subset_span (Set.mem_range_self row)⟩
  refine ⟨r, P, ?_⟩
  intro row col
  change A.row row col = ∑ v, P row v * A.row (r v) col
  have heq := congrArg (fun x : W => (x : C → K) col)
    (b.sum_equivFun ⟨A.row row, Submodule.subset_span (Set.mem_range_self row)⟩)
  simpa only [b, Basis.coe_mk, fs, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, P, ← hr] using heq.symm

theorem stack_swap {K : Type*} [Field K] {N d : ℕ} (hd : 1 ≤ d)
    (coefficients : BooleanAssignment N → K) (h : WeightLabel N d)
    (a i : Option (Fin N)) (V U : BitMonomial N (d - 1)) :
    representedStack coefficients (h, extendBit hd a V) (extendBit hd i U) =
      representedStack coefficients (h, extendBit hd i V) (extendBit hd a U) := by
  rw [stack_apply, stack_apply]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [bitProduct_extend]
  ring

theorem surviving_rank_sq {K : Type*} [Field K] {N d : ℕ} (hd : 1 ≤ d)
    (coefficients : BooleanAssignment N → K) :
    survivingDimension hd (representedStack coefficients) ≤
      (representedStack (d := d) coefficients).rank ^ 2 := by
  classical
  let A := representedStack (d := d) coefficients
  let W := Submodule.span K (Set.range A.row)
  obtain ⟨r, P, hexpand⟩ := exists_actual_row_expansion A
  choose a Uv ha using (fun v : Fin A.rank => split_bit hd (r v).2)
  let L : (Fin A.rank → W) →ₗ[K] (BitMonomial N (d - 1) → StackRow N d → K) :=
    { toFun := fun x U row => ∑ v, P row v * (x v : BitMonomial N d → K) (extendBit hd (a v) U)
      map_add' := by
        intro x y
        funext U row
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro k x
        funext U row
        simp [Finset.mul_sum, mul_left_comm] }
  let x : Option (Fin N) → Fin A.rank → W := fun i v =>
    ⟨A.row ((r v).1, extendBit hd i (Uv v)),
      Submodule.subset_span (Set.mem_range_self _)⟩
  have hfactor (i : Option (Fin N)) : survivingColumn hd A i = L (x i) := by
    funext U row
    rw [column_apply, hexpand]
    change (∑ v, P row v * A (r v) (extendBit hd i U)) =
      ∑ v, P row v * A ((r v).1, extendBit hd i (Uv v)) (extendBit hd (a v) U)
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    change A ((r v).1, (r v).2) (extendBit hd i U) =
      A ((r v).1, extendBit hd i (Uv v)) (extendBit hd (a v) U)
    rw [← ha v]
    exact stack_swap hd coefficients (r v).1 (a v) i (Uv v) U
  have hspan : Submodule.span K (Set.range (survivingColumn hd A)) ≤ LinearMap.range L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨x i, (hfactor i).symm⟩
  have hWrank : Module.finrank K W = A.rank := A.rank_eq_finrank_span_row.symm
  calc
    survivingDimension hd A ≤ Module.finrank K (LinearMap.range L) :=
      Submodule.finrank_mono hspan
    _ ≤ Module.finrank K (Fin A.rank → W) := L.finrank_range_le
    _ = A.rank ^ 2 := by simp [Module.finrank_pi_fintype, hWrank, pow_two]


end SurvivingProof
end GenericGroupWE.Main


namespace GenericGroupWE.Main
open scoped BigOperators

theorem eq_29_30 (K : Type*) [Field K] (N d : ℕ) (hd : 1 ≤ d)
    (coefficients : BooleanAssignment N → K)
    (hne : representedStack (d := d) coefficients ≠ 0) :
    let A := representedStack (d := d) coefficients
    1 ≤ survivingDimension hd A ∧ survivingDimension hd A ≤ A.rank ^ 2 ∧
    ∀ κ : Option (Fin N) → K,
      (∑ i, κ i • survivingColumn hd A i) = 0 →
      ∀ (h : WeightLabel N d) (f : MvPolynomial (Fin N) K), f.totalDegree + 1 ≤ 2*d →
        ∑ b, coefficients b * affineBit κ b * stackWeight h b *
          MvPolynomial.eval (booleanPoint b) f = 0 := by
  dsimp only
  refine ⟨SurvivingProof.surviving_pos hd _ hne,
    SurvivingProof.surviving_rank_sq hd coefficients, ?_⟩
  intro κ hκ h f hf
  exact surviving_relation_propagates hd coefficients κ hκ h f hf

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.RectangularSelector
namespace GenericGroupWE.Main
namespace SelectorProof

open scoped BigOperators

noncomputable def ofExponent {N e : ℕ} (d : Fin N →₀ ℕ)
    (hd : d.sum (fun _ n => n) ≤ e) : OrdinaryMonomial N e := by
  classical
  refine ⟨fun i => ⟨d i, ?_⟩, ?_⟩
  · have hi : d i ≤ ∑ j : Fin N, d j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hs : (∑ j : Fin N, d j) ≤ e := by
      simpa [Finsupp.sum_fintype] using hd
    omega
  · simpa [Finsupp.sum_fintype] using hd

theorem polynomial_ofExponent {K : Type*} [Field K] {N e : ℕ}
    (d : Fin N →₀ ℕ) (hd : d.sum (fun _ n => n) ≤ e) :
    monomialPolynomial (K := K) (ofExponent d hd) = MvPolynomial.monomial d 1 := by
  classical
  have he : Finsupp.equivFunOnFinite.symm
      (fun j => ((ofExponent d hd).val j).val) = d := by
    ext j
    simp [ofExponent]
  unfold monomialPolynomial
  rw [he]

theorem monomial_degree_le {K : Type*} [Field K] {N e : ℕ}
    (u : OrdinaryMonomial N e) :
    (monomialPolynomial (K := K) u).totalDegree ≤ e := by
  unfold monomialPolynomial
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  simpa [Finsupp.sum_fintype] using u.property

/-- Split the list of factors after a factors; its two pieces fit the side bounds. -/
theorem split_monomial {K : Type*} [Field K] {N : ℕ} (a b : ℕ)
    (d : Fin N →₀ ℕ) (hd : d.sum (fun _ n => n) ≤ a+b) :
    ∃ (u : OrdinaryMonomial N a) (v : OrdinaryMonomial N b),
      MvPolynomial.monomial d (1 : K) = monomialPolynomial u * monomialPolynomial v := by
  classical
  let l := d.toMultiset.toList
  have hlen : l.length ≤ a+b := by
    simpa [l, Multiset.length_toList, Finsupp.card_toMultiset, Function.id_def] using hd
  let d1 := Multiset.toFinsupp ((l.take a : List (Fin N)) : Multiset (Fin N))
  let d2 := Multiset.toFinsupp ((l.drop a : List (Fin N)) : Multiset (Fin N))
  have hd1 : d1.sum (fun _ n => n) ≤ a := by
    change (Multiset.toFinsupp ((l.take a : List (Fin N)) : Multiset (Fin N))).sum
      (fun _ => id) ≤ a
    rw [Multiset.toFinsupp_sum_eq, Multiset.coe_card, List.length_take]
    exact Nat.min_le_left a l.length
  have hd2 : d2.sum (fun _ n => n) ≤ b := by
    change (Multiset.toFinsupp ((l.drop a : List (Fin N)) : Multiset (Fin N))).sum
      (fun _ => id) ≤ b
    rw [Multiset.toFinsupp_sum_eq, Multiset.coe_card, List.length_drop]
    omega
  have hadd : d1+d2 = d := by
    dsimp [d1, d2]
    rw [← Multiset.toFinsupp_add, Multiset.coe_add, List.take_append_drop]
    simp [l]
  refine ⟨ofExponent d1 hd1, ofExponent d2 hd2, ?_⟩
  rw [polynomial_ofExponent, polynomial_ofExponent, MvPolynomial.monomial_mul,
    one_mul, hadd]

theorem table_zero_iff {K : Type*} [Field K] {N : ℕ} (a b : ℕ)
    (L : MvPolynomial (Fin N) K →ₗ[K] K) :
    rectangularTable a b L = 0 ↔
      ∀ f : MvPolynomial (Fin N) K, f.totalDegree ≤ a+b → L f = 0 := by
  classical
  constructor
  · intro hz f hf
    rw [f.as_sum, map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    obtain ⟨u, v, hprod⟩ := split_monomial (K := K) a b d
      ((MvPolynomial.le_totalDegree hd).trans hf)
    have hm : L (MvPolynomial.monomial d 1) = 0 := by
      rw [hprod]
      exact congrFun (congrFun hz u) v
    have heq : MvPolynomial.monomial d (MvPolynomial.coeff d f) =
        (MvPolynomial.coeff d f) • MvPolynomial.monomial d (1 : K) := by
      simp [MvPolynomial.smul_monomial]
    rw [heq, map_smul, hm, smul_zero]
  · intro hz
    ext u v
    change L (monomialPolynomial u * monomialPolynomial v) = 0
    apply hz
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (monomial_degree_le u) (monomial_degree_le v))

/-- A truncated one-variable recurrence forces evaluation at the corresponding point. -/
theorem evaluation_of_recurrence {K : Type*} [Field K] {N : ℕ} (e : ℕ)
    (L : MvPolynomial (Fin N) K →ₗ[K] K) (point : Fin N → K)
    (hrec : ∀ (i : Fin N) (f : MvPolynomial (Fin N) K),
      f.totalDegree + 1 ≤ e → L (MvPolynomial.X i * f) = point i * L f) :
    ∀ f : MvPolynomial (Fin N) K, f.totalDegree ≤ e →
      L f = L 1 * MvPolynomial.eval point f := by
  classical
  have hm : ∀ (d : Fin N →₀ ℕ) (c : K),
      (MvPolynomial.monomial d c).totalDegree ≤ e →
      L (MvPolynomial.monomial d c) =
        L 1 * MvPolynomial.eval point (MvPolynomial.monomial d c) := by
    apply MvPolynomial.induction_on_monomial
      (motive := fun p : MvPolynomial (Fin N) K =>
        p.totalDegree ≤ e → L p = L 1 * MvPolynomial.eval point p)
    · intro c hc
      simpa [MvPolynomial.smul_eq_C_mul, mul_comm] using (L.map_smul c (1 : MvPolynomial (Fin N) K))
    · intro p i ih hpdeg
      by_cases hp : p = 0
      · simp [hp]
      have hdp : p.totalDegree + 1 ≤ e := by
        simpa [MvPolynomial.totalDegree_mul_of_isDomain hp (MvPolynomial.X_ne_zero i)] using hpdeg
      have hval := hrec i p hdp
      calc
        L (p * MvPolynomial.X i) = L (MvPolynomial.X i * p) := by rw [mul_comm]
        _ = point i * L p := hval
        _ = L 1 * MvPolynomial.eval point (p * MvPolynomial.X i) := by
          rw [ih (by omega)]
          simp [MvPolynomial.eval_mul, mul_left_comm, mul_comm, mul_assoc]
  intro f hf
  rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply hm
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans
    ((MvPolynomial.le_totalDegree hd).trans hf)

end SelectorProof

/-- Registered selector child, proved from bounded functional recurrences. -/
theorem rectangular_selector_nonzero :
  ∀ (K : Type*) [Field K] (N k a b : ℕ)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (hunsat : NoBooleanZero q) (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (hidentities : AnnihilatesEquations q L ((a+1)+(b+1)))
    (hne : rectangularTable (a+1) (b+1) L ≠ 0),
    ∃ i : Fin N,
      rectangularTable a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) ≠ 0 ∧
      rectangularTable (a+1) b
        (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) ≠ 0 := by
  intro K _ N k a b q hq hunsat L hidentities hne
  classical
  by_contra hsplit
  have hchoice : ∀ i : Fin N,
      rectangularTable a (b+1) (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) = 0 ∨
      rectangularTable (a+1) b
        (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) = 0 := by
    intro i
    by_cases hx : rectangularTable a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) = 0
    · exact Or.inl hx
    · apply Or.inr
      by_contra hc
      exact hsplit ⟨i, hx, hc⟩
  let assignment : BooleanAssignment N := fun i =>
    if rectangularTable a (b+1)
      (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) = 0 then false else true
  have hrec : ∀ (i : Fin N) (f : MvPolynomial (Fin N) K),
      f.totalDegree + 1 ≤ (a+1)+(b+1) →
      L (MvPolynomial.X i * f) = booleanPoint assignment i * L f := by
    intro i f hf
    by_cases hx : rectangularTable a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) = 0
    · have hsmall : f.totalDegree ≤ a+(b+1) := by omega
      have hz := (SelectorProof.table_zero_iff a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i)))).mp hx f hsmall
      simpa [booleanPoint, assignment, hx] using hz
    · have hc := (hchoice i).resolve_left hx
      have hsmall : f.totalDegree ≤ (a+1)+b := by omega
      have hz := (SelectorProof.table_zero_iff (a+1) b
        (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))).mp hc f hsmall
      change L ((1 - MvPolynomial.X i) * f) = 0 at hz
      have hsub : L f - L (MvPolynomial.X i * f) = 0 := by
        simpa [sub_mul, map_sub] using hz
      have hX : L (MvPolynomial.X i * f) = L f := (sub_eq_zero.mp hsub).symm
      simpa [booleanPoint, assignment, hx] using hX
  have hall := SelectorProof.evaluation_of_recurrence ((a+1)+(b+1)) L
    (booleanPoint assignment) hrec
  have hL1 : L 1 ≠ 0 := by
    intro hz
    apply hne
    apply (SelectorProof.table_zero_iff (a+1) (b+1) L).mpr
    intro f hf
    rw [hall f hf, hz, zero_mul]
  obtain ⟨s, hs⟩ := hunsat assignment
  have hzero : L (q s) = 0 := by
    have hh := (hidentities 1 (by simp; omega)).2 s
    simpa using hh
  have hdegree : (q s).totalDegree ≤ (a+1)+(b+1) := by have hh := hq s; omega
  have hmul : L 1 * MvPolynomial.eval (booleanPoint assignment) (q s) = 0 := by
    rw [← hall (q s) hdegree]
    exact hzero
  exact hs ((mul_eq_zero.mp hmul).resolve_left hL1)

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.WeightedSubstitution
namespace GenericGroupWE.Main
namespace WeightExpansionProof
open scoped BigOperators

noncomputable def evaluationMap {K Ω : Type*} [Field K] {N : ℕ}
    (point : Ω → Fin N → K) : MvPolynomial (Fin N) K →ₗ[K] (Ω → K) where
  toFun f b := MvPolynomial.eval (point b) f
  map_add' f g := by ext b; simp
  map_smul' c f := by ext b; simp [MvPolynomial.smul_eq_C_mul]

theorem degree_substitution_le {K : Type*} [Field K] {N M : ℕ}
    (v : Fin N → MvPolynomial (Fin M) K) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (f : MvPolynomial (Fin N) K) :
    (MvPolynomial.eval₂Hom MvPolynomial.C v f).totalDegree ≤ f.totalDegree := by
  classical
  let S := MvPolynomial.eval₂Hom MvPolynomial.C v
  have hm : ∀ (d : Fin N →₀ ℕ) (c : K),
      (S (MvPolynomial.monomial d c)).totalDegree ≤ (MvPolynomial.monomial d c).totalDegree := by
    apply MvPolynomial.induction_on_monomial
      (motive := fun p : MvPolynomial (Fin N) K => (S p).totalDegree ≤ p.totalDegree)
    · intro c
      simp [S]
    · intro p i ih
      by_cases hp : p = 0
      · simp [hp, S]
      have hdeg : (p * MvPolynomial.X i).totalDegree = p.totalDegree+1 := by
        simpa using MvPolynomial.totalDegree_mul_of_isDomain hp (MvPolynomial.X_ne_zero i)
      have hSi : S (MvPolynomial.X i) = v i := by simp [S]
      rw [map_mul, hSi, hdeg]
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ih (hv i))
  calc
    (MvPolynomial.eval₂Hom MvPolynomial.C v f).totalDegree =
        (∑ d ∈ f.support, S (MvPolynomial.monomial d (MvPolynomial.coeff d f))).totalDegree := by
          simpa only [map_sum] using congrArg
            (fun p : MvPolynomial (Fin N) K => (S p).totalDegree) f.as_sum
    _ ≤ f.totalDegree := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro d hd
      exact (hm d (MvPolynomial.coeff d f)).trans
        ((MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree hd))

theorem eval_substitution {K : Type*} [Field K] {N M : ℕ}
    (v : Fin N → MvPolynomial (Fin M) K) (point : Fin M → K)
    (f : MvPolynomial (Fin N) K) :
    MvPolynomial.eval point (MvPolynomial.eval₂Hom MvPolynomial.C v f) =
      MvPolynomial.eval (fun i => MvPolynomial.eval point (v i)) f := by
  exact (MvPolynomial.eval_assoc v point f).symm

noncomputable def geometryPolynomial {K : Type*} [Field K] {N : ℕ}
    (j t : ℕ) : MvPolynomial (Fin N) K :=
  1 + ∑ i : Fin N, MvPolynomial.C ((((2 : K)^j) * (t : K))^(i.val+1)) * MvPolynomial.X i

theorem geometry_degree_le {K : Type*} [Field K] {N : ℕ} (j t : ℕ) :
    (geometryPolynomial (K := K) (N := N) j t).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])

theorem eval_geometry {K : Type*} [Field K] {N : ℕ} (j t : ℕ)
    (b : BooleanAssignment N) :
    MvPolynomial.eval (booleanPoint b) (geometryPolynomial (K := K) j t) = geometricForm j t b := by
  simp [geometryPolynomial, geometricForm]

noncomputable def replacementBits {K : Type*} [Field K] {N δ : ℕ}
    (t : ℕ) (μ : Fin N → Fin δ → K) (i : Fin N) : MvPolynomial (Fin N) K :=
  ∑ j : Fin δ, MvPolynomial.C (μ i j) * geometryPolynomial j.val t

noncomputable def replacementGeometry {K : Type*} [Field K] {N M δ : ℕ}
    (hav : δ ≤ M) (μ : Fin N → Fin δ → K) (i : Fin N) : MvPolynomial (Fin M) K :=
  ∑ j : Fin δ, MvPolynomial.C (μ i j) * MvPolynomial.X (Fin.castLE hav j)

theorem replacementBits_degree {K : Type*} [Field K] {N δ : ℕ}
    (t : ℕ) (μ : Fin N → Fin δ → K) (i : Fin N) :
    (replacementBits t μ i).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa using geometry_degree_le (K := K) (N := N) j.val t)

theorem replacementGeometry_degree {K : Type*} [Field K] {N M δ : ℕ}
    (hav : δ ≤ M) (μ : Fin N → Fin δ → K) (i : Fin N) :
    (replacementGeometry hav μ i).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem eval_replacementBits {K : Type*} [Field K] {N δ : ℕ}
    (t : ℕ) (μ : Fin N → Fin δ → K) (b : BooleanAssignment N) (i : Fin N) :
    MvPolynomial.eval (booleanPoint b) (replacementBits t μ i) = replacement t μ b i := by
  simp [replacementBits, replacement, eval_geometry]

theorem eval_replacementGeometry {K : Type*} [Field K] {N M δ : ℕ}
    (hav : δ ≤ M) (t : ℕ) (μ : Fin N → Fin δ → K) (b : BooleanAssignment N) (i : Fin N) :
    MvPolynomial.eval (fun j : Fin M => geometricForm j.val t b) (replacementGeometry hav μ i) =
      replacement t μ b i := by
  simp [replacementGeometry, replacement]

theorem eval_substituteBits {K : Type*} [Field K] {N δ : ℕ}
    (t : ℕ) (μ : Fin N → Fin δ → K) (b : BooleanAssignment N) (f : MvPolynomial (Fin N) K) :
    MvPolynomial.eval (booleanPoint b) (MvPolynomial.eval₂Hom MvPolynomial.C (replacementBits t μ) f) =
      MvPolynomial.eval (replacement t μ b) f := by
  rw [eval_substitution]
  apply congrArg (fun point : Fin N → K => MvPolynomial.eval point f)
  funext i
  exact eval_replacementBits t μ b i

theorem eval_substituteGeometry {K : Type*} [Field K] {N M δ : ℕ}
    (hav : δ ≤ M) (t : ℕ) (μ : Fin N → Fin δ → K) (b : BooleanAssignment N)
    (f : MvPolynomial (Fin N) K) :
    MvPolynomial.eval (fun j : Fin M => geometricForm j.val t b)
      (MvPolynomial.eval₂Hom MvPolynomial.C (replacementGeometry hav μ) f) =
      MvPolynomial.eval (replacement t μ b) f := by
  rw [eval_substitution]
  apply congrArg (fun point : Fin N → K => MvPolynomial.eval point f)
  funext i
  exact eval_replacementGeometry hav t μ b i

theorem eval_weight {K : Type*} [Field K] {N d : ℕ}
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (u : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N)) (b : BooleanAssignment N) :
    MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b)
      (monomialPolynomial (K := K) u) = stackWeight (t,u) b := by
  classical
  simp [monomialPolynomial, MvPolynomial.eval_monomial, Finsupp.prod_fintype, stackWeight]

theorem weight_polynomial_vanish {K : Type*} [Field K] {N d s : ℕ}
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (F : (BooleanAssignment N → K) →ₗ[K] K)
    (hF : ∀ (u : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
      (p : MvPolynomial (Fin N) K), p.totalDegree ≤ s →
      F (fun b => stackWeight (t,u) b * MvPolynomial.eval (booleanPoint b) p) = 0)
    (H : MvPolynomial (Fin ((rankTarget N d)^2)) K) (hH : H.totalDegree ≤ weightDegree N)
    (p : MvPolynomial (Fin N) K) (hp : p.totalDegree ≤ s) :
    F (fun b => MvPolynomial.eval
      (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) H *
        MvPolynomial.eval (booleanPoint b) p) = 0 := by
  classical
  let W := F.comp ((LinearMap.mulRight K (fun b : BooleanAssignment N => MvPolynomial.eval (booleanPoint b) p)).comp
    (evaluationMap (fun b : BooleanAssignment N => fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b)))
  change W H = 0
  rw [H.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  have hdegree : m.sum (fun _ n => n) ≤ weightDegree N := (MvPolynomial.le_totalDegree hm).trans hH
  have hu := hF (SelectorProof.ofExponent m hdegree) p hp
  have hw : W (MvPolynomial.monomial m 1) = 0 := by
    have heval (b : BooleanAssignment N) :
        MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b)
          (MvPolynomial.monomial m (1 : K)) = stackWeight (t,SelectorProof.ofExponent m hdegree) b := by
      rw [← SelectorProof.polynomial_ofExponent m hdegree]
      exact eval_weight t _ b
    simpa [W, evaluationMap, Pi.mul_def, heval] using hu
  have heq : MvPolynomial.monomial m (MvPolynomial.coeff m H) =
      MvPolynomial.coeff m H • MvPolynomial.monomial m (1 : K) := by
    simp [MvPolynomial.smul_monomial]
  rw [heq, map_smul, hw, smul_zero]

end WeightExpansionProof

open scoped BigOperators

/-- Fully general weighted degree expansion; no equations or basis condition. -/
theorem weighted_substitution_vanish :
  ∀ (K : Type*) [Field K] (N d δ s : ℕ)
    (havailable : δ ≤ (rankTarget N d)^2)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K) (F : (BooleanAssignment N → K) →ₗ[K] K)
    (hF : ∀ (u : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
      (p : MvPolynomial (Fin N) K), p.totalDegree ≤ s →
      F (fun b => stackWeight (t,u) b * MvPolynomial.eval (booleanPoint b) p) = 0)
    (f : MvPolynomial (Fin N) K) (hf : f.totalDegree ≤ weightDegree N + s),
    F (fun b => MvPolynomial.eval (replacement t.val μ b) f) = 0 := by
  intro K _ N d δ s havailable t μ F hF f hf
  classical
  let W := F.comp (WeightExpansionProof.evaluationMap (replacement t.val μ))
  change W f = 0
  rw [f.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨u, v, hprod⟩ := SelectorProof.split_monomial (K := K) (weightDegree N) s m
    ((MvPolynomial.le_totalDegree hm).trans hf)
  have hW : W (monomialPolynomial u * monomialPolynomial v) = 0 := by
    let H := MvPolynomial.eval₂Hom MvPolynomial.C
      (WeightExpansionProof.replacementGeometry havailable μ) (monomialPolynomial u)
    let p := MvPolynomial.eval₂Hom MvPolynomial.C
      (WeightExpansionProof.replacementBits t.val μ) (monomialPolynomial v)
    have hH : H.totalDegree ≤ weightDegree N :=
      (WeightExpansionProof.degree_substitution_le _
        (WeightExpansionProof.replacementGeometry_degree havailable μ) _).trans
          (SelectorProof.monomial_degree_le u)
    have hp : p.totalDegree ≤ s :=
      (WeightExpansionProof.degree_substitution_le _
        (WeightExpansionProof.replacementBits_degree t.val μ) _).trans
          (SelectorProof.monomial_degree_le v)
    have hh := WeightExpansionProof.weight_polynomial_vanish t F hF H hH p hp
    have hHv (b : BooleanAssignment N) : MvPolynomial.eval
        (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) H =
          MvPolynomial.eval (replacement t.val μ b) (monomialPolynomial u) :=
      WeightExpansionProof.eval_substituteGeometry havailable t.val μ b (monomialPolynomial u)
    have hpv (b : BooleanAssignment N) : MvPolynomial.eval (booleanPoint b) p =
        MvPolynomial.eval (replacement t.val μ b) (monomialPolynomial v) :=
      WeightExpansionProof.eval_substituteBits t.val μ b (monomialPolynomial v)
    change F (fun b => MvPolynomial.eval (replacement t.val μ b)
      (monomialPolynomial u * monomialPolynomial v)) = 0
    simpa only [map_mul, hHv, hpv] using hh
  have heq : MvPolynomial.monomial m (MvPolynomial.coeff m f) =
      MvPolynomial.coeff m f • (monomialPolynomial u * monomialPolynomial v) := by
    rw [← hprod]
    simp [MvPolynomial.smul_monomial]
  rw [heq, map_smul, hW, smul_zero]

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.StackForward
namespace GenericGroupWE.Main
namespace StackRankProof
open scoped BigOperators

theorem feature_factorization {K Ω R C I J : Type*} [Field K]
    [Fintype Ω] [Fintype R] [Fintype C]
    (coefficients : Ω → K) (r : R → Ω → K) (c : C → Ω → K)
    (P : Matrix I R K) (Q : Matrix C J K) :
    (Matrix.of fun i j => ∑ b, coefficients b *
      (∑ row, P i row * r row b) * (∑ col, Q col j * c col b)) =
      P * (Matrix.of fun row col => ∑ b, coefficients b * r row b * c col b) * Q := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ b, coefficients b * (∑ row, P i row * r row b) *
    (∑ col, Q col j * c col b)) =
      ∑ col, (∑ row, P i row * (∑ b, coefficients b * r row b * c col b)) * Q col j
  calc
    _ = ∑ b, ∑ row, ∑ col,
        coefficients b * (P i row * r row b) * (Q col j * c col b) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum Finset.univ (fun row => P i row * r row b) (coefficients b),
        Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ row, ∑ col, ∑ b,
        coefficients b * (P i row * r row b) * (Q col j * c col b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro row hrow
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro col hcol
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row hrow
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      ring

theorem boolean_eval_mem_span {K : Type*} [Field K] {N e : ℕ}
    (p : MvPolynomial (Fin N) K) (hp : p.totalDegree ≤ e) :
    (fun b : BooleanAssignment N => MvPolynomial.eval (booleanPoint b) p) ∈
      Submodule.span K (Set.range (fun S : BitMonomial N e => fun b => bitProduct (K := K) b S.val)) := by
  classical
  let E : MvPolynomial (Fin N) K →ₗ[K] (BooleanAssignment N → K) :=
    WeightExpansionProof.evaluationMap (fun b : BooleanAssignment N => booleanPoint (K := K) b)
  change E p ∈ _
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro m hm
  have hcard : m.support.card ≤ e :=
    (SurvivingProof.support_card_le m).trans ((MvPolynomial.le_totalDegree hm).trans hp)
  let S : BitMonomial N e := ⟨m.support, hcard⟩
  have heq : E (MvPolynomial.monomial m (MvPolynomial.coeff m p)) =
      MvPolynomial.coeff m p • (fun b : BooleanAssignment N => bitProduct (K := K) b S.val) := by
    funext b
    exact SurvivingProof.eval_monomial_boolean b m _
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self S))

theorem boolean_eval_expansion {K : Type*} [Field K] {N e : ℕ}
    (p : MvPolynomial (Fin N) K) (hp : p.totalDegree ≤ e) :
    ∃ a : BitMonomial N e → K, ∀ b : BooleanAssignment N,
      MvPolynomial.eval (booleanPoint b) p = ∑ S, a S * bitProduct b S.val := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (boolean_eval_mem_span p hp)
  refine ⟨a, ?_⟩
  intro b
  have hh := congrFun ha b
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh.symm

theorem replacement_row_mem_span {K : Type*} [Field K] {N d δ : ℕ}
    (havailable : δ ≤ (rankTarget N d)^2)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K) (f : MvPolynomial (Fin N) K)
    (hf : f.totalDegree ≤ weightDegree N + d) :
    (fun b : BooleanAssignment N => MvPolynomial.eval (replacement t.val μ b) f) ∈
      Submodule.span K (Set.range (fun row :
        OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d =>
        fun b : BooleanAssignment N => stackWeight (t, row.1) b * bitProduct (K := K) b row.2.val)) := by
  classical
  let features := fun row : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) ×
      BitMonomial N d => fun b : BooleanAssignment N =>
        stackWeight (t, row.1) b * bitProduct (K := K) b row.2.val
  let S := Submodule.span K (Set.range features)
  change _ ∈ S
  by_contra hx
  obtain ⟨F, hFx, hFS⟩ := Submodule.exists_le_ker_of_notMem hx
  apply hFx
  apply weighted_substitution_vanish K N d δ d havailable t μ F ?_ f hf
  intro u p hp
  obtain ⟨a, ha⟩ := boolean_eval_expansion p hp
  have heq : (fun b : BooleanAssignment N => stackWeight (t, u) b *
      MvPolynomial.eval (booleanPoint b) p) =
      ∑ T : BitMonomial N d, a T • features (u, T) := by
    funext b
    simp only [ha b, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, features]
    apply Finset.sum_congr rfl
    intro T hT
    ring
  rw [heq]
  apply hFS
  exact Submodule.sum_mem S (fun T hT => S.smul_mem _ (Submodule.subset_span (Set.mem_range_self (u, T))))

theorem rectangular_forward_factorization_aux
    (K : Type*) [Field K] (N d δ : ℕ) (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (coefficients : BooleanAssignment N → K)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K) :
    ∃ (P : Matrix (OrdinaryMonomial N (weightDegree N + d))
        (OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d) K)
      (Q : Matrix (BitMonomial N d) (OrdinaryMonomial N d) K),
      rectangularTable (weightDegree N + d) d (replacementFunctional coefficients t.val μ) =
        P * sampleStack (representedStack (d := d) coefficients) t * Q := by
  classical
  let rowfeatures := fun row : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) ×
      BitMonomial N d => fun b : BooleanAssignment N =>
        stackWeight (t, row.1) b * bitProduct (K := K) b row.2.val
  have hrow (u : OrdinaryMonomial N (weightDegree N + d)) :
      ∃ a : (OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d) → K,
      ∀ b : BooleanAssignment N,
        MvPolynomial.eval (replacement t.val μ b) (monomialPolynomial u) =
          ∑ row, a row * rowfeatures row b := by
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
      (replacement_row_mem_span havailable t μ (monomialPolynomial u)
        (SelectorProof.monomial_degree_le u))
    refine ⟨a, ?_⟩
    intro b
    have hh := congrFun ha b
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh.symm
  choose P hP using hrow
  have hcol (v : OrdinaryMonomial N d) : ∃ a : BitMonomial N d → K,
      ∀ b : BooleanAssignment N,
        MvPolynomial.eval (replacement t.val μ b) (monomialPolynomial v) =
          ∑ T, a T * bitProduct b T.val := by
    let g := MvPolynomial.eval₂Hom MvPolynomial.C
      (WeightExpansionProof.replacementBits t.val μ) (monomialPolynomial v)
    have hdeg : g.totalDegree ≤ d :=
      (WeightExpansionProof.degree_substitution_le _
        (WeightExpansionProof.replacementBits_degree t.val μ) _).trans
        (SelectorProof.monomial_degree_le v)
    obtain ⟨a, ha⟩ := boolean_eval_expansion g hdeg
    refine ⟨a, ?_⟩
    intro b
    simpa only [g, WeightExpansionProof.eval_substituteBits] using ha b
  choose Q hQ using hcol
  have hH : rectangularTable (weightDegree N + d) d (replacementFunctional coefficients t.val μ) =
      (Matrix.of fun u v => ∑ b, coefficients b *
        (∑ row, P u row * rowfeatures row b) * (∑ T, Q v T * bitProduct b T.val)) := by
    apply Matrix.ext
    intro u v
    change (∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b)
      (monomialPolynomial u * monomialPolynomial v)) = _
    simp only [Matrix.of_apply, map_mul, hP u, hQ v, mul_assoc]
  have hA : sampleStack (representedStack (d := d) coefficients) t =
      (Matrix.of fun row T => ∑ b, coefficients b * rowfeatures row b * bitProduct b T.val) := by
    apply Matrix.ext
    intro row T
    change representedStack coefficients ((t, row.1), row.2) T = _
    rw [SurvivingProof.stack_apply]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [rowfeatures]
    ring
  refine ⟨Matrix.of P, Matrix.of (fun T v => Q v T), ?_⟩
  rw [hH, hA]
  exact feature_factorization coefficients rowfeatures
    (fun T : BitMonomial N d => fun b : BooleanAssignment N => bitProduct b T.val)
    (Matrix.of P) (Matrix.of (fun T v => Q v T))


end StackRankProof
end GenericGroupWE.Main


open scoped BigOperators
namespace GenericGroupWE.Main

theorem rectangular_forward_factorization :
  ∀ (K : Type*) [Field K] (N d δ : ℕ) (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d) ^ 2)
    (coefficients : BooleanAssignment N → K)
    (t : Fin (N * ((rankTarget N d) ^ 2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K),
    ∃ (P : Matrix (OrdinaryMonomial N (weightDegree N + d))
        (OrdinaryMonomial ((rankTarget N d) ^ 2) (weightDegree N) × BitMonomial N d) K)
      (Q : Matrix (BitMonomial N d) (OrdinaryMonomial N d) K),
      rectangularTable (weightDegree N + d) d (replacementFunctional coefficients t.val μ) =
        P * sampleStack (representedStack (d := d) coefficients) t * Q := by
  intro K _ N d δ hd havailable coefficients t μ
  exact StackRankProof.rectangular_forward_factorization_aux K N d δ hd havailable coefficients t μ

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.TransferMoments
namespace GenericGroupWE.Main
namespace ReplacementMomentProof
open scoped BigOperators

noncomputable def weightedSum {K Ω : Type*} [Field K] [Fintype Ω]
    (w : Ω → K) : (Ω → K) →ₗ[K] K where
  toFun f := ∑ b, w b * f b
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

def geometricCoefficients {K : Type*} [Field K] {N : ℕ}
    (j t : ℕ) : Option (Fin N) → K
  | none => 1
  | some i => (((2 : K)^j) * (t : K))^(i.val+1)

theorem column_geometric {K : Type*} [Field K] {N d : ℕ} (hd : 1 ≤ d)
    (A : Matrix (StackRow N d) (BitMonomial N d) K) (j t : ℕ) :
    Fintype.linearCombination K (survivingColumn hd A) (geometricCoefficients j t) =
      geometricColumn hd A j t := by
  simp [Fintype.linearCombination_apply, Fintype.sum_option, geometricCoefficients, geometricColumn]

theorem affine_linearCombination {K : Type*} [Field K] {N : ℕ}
    (b : BooleanAssignment N) (κ : Option (Fin N) → K) :
    Fintype.linearCombination K (SurvivingProof.optionPoint b) κ = affineBit κ b := by
  simp [Fintype.linearCombination_apply, Fintype.sum_option, SurvivingProof.optionPoint,
    affineBit, smul_eq_mul]

theorem defect_base {K : Type*} [Field K] {N d δ : ℕ} (hd : 1 ≤ d)
    (coefficients : BooleanAssignment N → K) (t : ℕ) (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t μ)
    (i : Fin N) (h : WeightLabel N d) (p : MvPolynomial (Fin N) K)
    (hp : p.totalDegree+1 ≤ 2*d) :
    ∑ b, coefficients b * (replacement t μ b i - booleanPoint b i) * stackWeight h b *
      MvPolynomial.eval (booleanPoint b) p = 0 := by
  classical
  let A := representedStack (d := d) coefficients
  let γ : Fin δ → Option (Fin N) → K := fun j => geometricCoefficients j.val t
  let κ : Option (Fin N) → K := (∑ j : Fin δ, μ i j • γ j) - Pi.single (some i) 1
  let C := Fintype.linearCombination K (survivingColumn hd A)
  have hCγ (j : Fin δ) : C (γ j) = geometricColumn hd A j.val t := column_geometric hd A j.val t
  have hCσ : C (Pi.single (some i) 1) = survivingColumn hd A (some i) := by simp [C]
  have hCκ : C κ = 0 := by
    change C ((∑ j : Fin δ, μ i j • γ j) - Pi.single (some i) 1) = 0
    rw [map_sub, map_sum, hCσ]
    simp_rw [map_smul, hCγ]
    exact sub_eq_zero.mpr (hbasis.2.2 i).symm
  have hrelation : (∑ a, κ a • survivingColumn hd A a) = 0 := by
    exact hCκ
  have haffine (b : BooleanAssignment N) : affineBit κ b = replacement t μ b i - booleanPoint b i := by
    let E := Fintype.linearCombination K (SurvivingProof.optionPoint (K := K) b)
    have hEγ (j : Fin δ) : E (γ j) = geometricForm j.val t b := by
      rw [affine_linearCombination]
      rfl
    have hEσ : E (Pi.single (some i) 1) = booleanPoint b i := by
      simp [E, SurvivingProof.optionPoint]
    calc
      affineBit κ b = E κ := (affine_linearCombination b κ).symm
      _ = (∑ j : Fin δ, μ i j * geometricForm j.val t b) - booleanPoint b i := by
        simp only [κ, map_sub, map_sum, map_smul, hEγ, hEσ, smul_eq_mul]
      _ = replacement t μ b i - booleanPoint b i := rfl
  have hh := surviving_relation_propagates hd coefficients κ hrelation h p hp
  simpa only [haffine] using hh

theorem defect_affine {K : Type*} [Field K] {N d δ : ℕ} (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (coefficients : BooleanAssignment N → K)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ)
    (i : Fin N) (g : MvPolynomial (Fin N) K) (hg : g.totalDegree ≤ 1)
    (f : MvPolynomial (Fin N) K) (hf : f.totalDegree+2 ≤ weightDegree N+2*d) :
    ∑ b, coefficients b * (replacement t.val μ b i - booleanPoint b i) *
      MvPolynomial.eval (booleanPoint b) g * MvPolynomial.eval (replacement t.val μ b) f = 0 := by
  let F := weightedSum (fun b => coefficients b * (replacement t.val μ b i - booleanPoint b i) *
    MvPolynomial.eval (booleanPoint b) g)
  have hF : ∀ (u : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
      (p : MvPolynomial (Fin N) K), p.totalDegree ≤ 2*d-2 →
      F (fun b => stackWeight (t,u) b * MvPolynomial.eval (booleanPoint b) p) = 0 := by
    intro u p hp
    have hdegree : (g*p).totalDegree+1 ≤ 2*d := by
      have hh := MvPolynomial.totalDegree_mul g p
      omega
    have hh := defect_base hd coefficients t.val μ hbasis i (t,u) (g*p) hdegree
    simpa [F, weightedSum, map_mul, mul_assoc, mul_left_comm, mul_comm] using hh
  have hdegree : f.totalDegree ≤ weightDegree N + (2*d-2) := by omega
  have hh := weighted_substitution_vanish K N d δ (2*d-2) havailable t μ F hF f hdegree
  simpa [F, weightedSum, mul_assoc] using hh

end ReplacementMomentProof
open scoped BigOperators

theorem replacement_low_moments :
  ∀ (K : Type*) [Field K] (N d δ : ℕ) (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (coefficients : BooleanAssignment N → K)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ)
    (f : MvPolynomial (Fin N) K) (hf : f.totalDegree + 2 ≤ weightDegree N + 2*d),
    (∀ i : Fin N, ∑ b, coefficients b *
      (replacement t.val μ b i - booleanPoint b i) *
        MvPolynomial.eval (replacement t.val μ b) f = 0) ∧
    (∀ i j : Fin N, ∑ b, coefficients b *
      (replacement t.val μ b i * replacement t.val μ b j - booleanPoint b i * booleanPoint b j) *
        MvPolynomial.eval (replacement t.val μ b) f = 0) := by
  intro K _ N d δ hd havailable coefficients t μ hbasis f hf
  constructor
  · intro i
    have hh := ReplacementMomentProof.defect_affine hd havailable coefficients t μ hbasis i
      1 (by simp) f hf
    simpa using hh
  · intro i j
    have hi := ReplacementMomentProof.defect_affine hd havailable coefficients t μ hbasis i
      (WeightExpansionProof.replacementBits t.val μ j)
      (WeightExpansionProof.replacementBits_degree t.val μ j) f hf
    simp only [WeightExpansionProof.eval_replacementBits] at hi
    have hj := ReplacementMomentProof.defect_affine hd havailable coefficients t μ hbasis j
      (MvPolynomial.X i) (by simp) f hf
    simp only [MvPolynomial.eval_X] at hj
    calc
      ∑ b, coefficients b *
          (replacement t.val μ b i * replacement t.val μ b j - booleanPoint b i * booleanPoint b j) *
            MvPolynomial.eval (replacement t.val μ b) f =
        (∑ b, coefficients b * (replacement t.val μ b i - booleanPoint b i) *
          replacement t.val μ b j * MvPolynomial.eval (replacement t.val μ b) f) +
        (∑ b, coefficients b * (replacement t.val μ b j - booleanPoint b j) *
          booleanPoint b i * MvPolynomial.eval (replacement t.val μ b) f) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = 0 := by rw [hi, hj, add_zero]

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.MixedReplacement
namespace GenericGroupWE.Main
namespace MixedReplacementProof
open scoped BigOperators

/-- Geometric-input version of weighted expansion, with arbitrary residual degree. -/
theorem geometry_expansion_vanish {K : Type*} [Field K] {N d s : ℕ}
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (F : (BooleanAssignment N → K) →ₗ[K] K)
    (hF : ∀ (u : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
      (p : MvPolynomial (Fin N) K), p.totalDegree ≤ s →
      F (fun b => stackWeight (t,u) b * MvPolynomial.eval (booleanPoint b) p) = 0)
    (g : MvPolynomial (Fin ((rankTarget N d)^2)) K)
    (hg : g.totalDegree ≤ weightDegree N+s) :
    F (fun b => MvPolynomial.eval
      (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g) = 0 := by
  classical
  let W := F.comp (WeightExpansionProof.evaluationMap
    (fun b : BooleanAssignment N => fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b))
  change W g = 0
  rw [g.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨u,v,hprod⟩ := SelectorProof.split_monomial (K := K) (weightDegree N) s m
    ((MvPolynomial.le_totalDegree hm).trans hg)
  have hW : W (monomialPolynomial u * monomialPolynomial v) = 0 := by
    let p : MvPolynomial (Fin N) K := MvPolynomial.eval₂Hom MvPolynomial.C
      (fun j : Fin ((rankTarget N d)^2) =>
        WeightExpansionProof.geometryPolynomial (K := K) (N := N) j.val t.val)
      (monomialPolynomial (K := K) v)
    have hp : p.totalDegree ≤ s :=
      (WeightExpansionProof.degree_substitution_le _
        (fun j => WeightExpansionProof.geometry_degree_le (K := K) (N := N) j.val t.val) _).trans
          (SelectorProof.monomial_degree_le v)
    have hpval (b : BooleanAssignment N) : MvPolynomial.eval (booleanPoint b) p =
        MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b)
          (monomialPolynomial (K := K) v) := by
      rw [WeightExpansionProof.eval_substitution]
      apply congrArg (fun point : Fin ((rankTarget N d)^2) → K =>
        MvPolynomial.eval point (monomialPolynomial (K := K) v))
      funext j
      exact WeightExpansionProof.eval_geometry j.val t.val b
    have hh := hF u p hp
    change F (fun b => MvPolynomial.eval
      (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b)
        (monomialPolynomial u * monomialPolynomial v)) = 0
    simpa only [map_mul, WeightExpansionProof.eval_weight, hpval] using hh
  have heq : MvPolynomial.monomial m (MvPolynomial.coeff m g) =
      MvPolynomial.coeff m g • (monomialPolynomial u * monomialPolynomial v) := by
    rw [← hprod]
    simp [MvPolynomial.smul_monomial]
  rw [heq, map_smul, hW, smul_zero]

end MixedReplacementProof
open scoped BigOperators

/-- Provisional full mixed Eq31 interface: no equations, nonzero condition or prime bound. -/
theorem mixed_replacement_moment :
  ∀ (K : Type*) [Field K] (N d δ : ℕ) (hd : 1 ≤ d)
    (coefficients : BooleanAssignment N → K)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ)
    (i : Fin N) (f : MvPolynomial (Fin N) K)
    (g : MvPolynomial (Fin ((rankTarget N d)^2)) K)
    (hf : f.totalDegree ≤ 2*d-1)
    (hfg : f.totalDegree+g.totalDegree ≤ weightDegree N+2*d-1),
    ∑ b, coefficients b * (booleanPoint b i - replacement t.val μ b i) *
      MvPolynomial.eval (booleanPoint b) f *
        MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g = 0 := by
  intro K _ N d δ hd coefficients t μ hbasis i f g hf hfg
  let F := ReplacementMomentProof.weightedSum (fun b => coefficients b *
    (replacement t.val μ b i - booleanPoint b i) * MvPolynomial.eval (booleanPoint b) f)
  have hF : ∀ (u : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
      (p : MvPolynomial (Fin N) K), p.totalDegree ≤ 2*d-1-f.totalDegree →
      F (fun b => stackWeight (t,u) b * MvPolynomial.eval (booleanPoint b) p) = 0 := by
    intro u p hp
    have hdegree : (f*p).totalDegree+1 ≤ 2*d := by
      have hh := MvPolynomial.totalDegree_mul f p
      omega
    have hh := ReplacementMomentProof.defect_base hd coefficients t.val μ hbasis i (t,u) (f*p) hdegree
    simpa [F, ReplacementMomentProof.weightedSum, map_mul, mul_assoc, mul_left_comm, mul_comm] using hh
  have hg : g.totalDegree ≤ weightDegree N+(2*d-1-f.totalDegree) := by omega
  have hh := MixedReplacementProof.geometry_expansion_vanish t F hF g hg
  have hpositive : ∑ b, coefficients b * (replacement t.val μ b i - booleanPoint b i) *
      MvPolynomial.eval (booleanPoint b) f *
        MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g = 0 := by
    simpa [F, ReplacementMomentProof.weightedSum, mul_assoc] using hh
  calc
    ∑ b, coefficients b * (booleanPoint b i - replacement t.val μ b i) *
        MvPolynomial.eval (booleanPoint b) f *
          MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g =
      -(∑ b, coefficients b * (replacement t.val μ b i - booleanPoint b i) *
        MvPolynomial.eval (booleanPoint b) f *
          MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = 0 := by rw [hpositive, neg_zero]

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.StackReverse
namespace GenericGroupWE.Main
namespace StackRankProof
open scoped BigOperators

noncomputable def polynomialMoment {K Ω : Type*} [Field K] [Fintype Ω] {N : ℕ}
    (coefficients multiplier : Ω → K) (point : Ω → Fin N → K) :
    MvPolynomial (Fin N) K →ₗ[K] K where
  toFun f := ∑ b, coefficients b * MvPolynomial.eval (point b) f * multiplier b
  map_add' f g := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp [MvPolynomial.smul_eq_C_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem bit_moment_substitution {K : Type*} [Field K] {N d δ : ℕ} (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (coefficients : BooleanAssignment N → K)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ)
    (f : MvPolynomial (Fin N) K)
    (g : MvPolynomial (Fin ((rankTarget N d)^2)) K)
    (hf : f.totalDegree ≤ 2*d) (hfg : f.totalDegree + g.totalDegree ≤ weightDegree N + 2*d) :
    (∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) f *
      MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g) =
    ∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b) f *
      MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g := by
  classical
  have hm : ∀ (m : Fin N →₀ ℕ) (c : K)
      (g : MvPolynomial (Fin ((rankTarget N d)^2)) K),
      (MvPolynomial.monomial m c).totalDegree ≤ 2*d →
      (MvPolynomial.monomial m c).totalDegree + g.totalDegree ≤ weightDegree N + 2*d →
      (∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) (MvPolynomial.monomial m c) *
        MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g) =
      ∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b) (MvPolynomial.monomial m c) *
        MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g := by
    apply MvPolynomial.induction_on_monomial
      (motive := fun p : MvPolynomial (Fin N) K =>
        ∀ g : MvPolynomial (Fin ((rankTarget N d)^2)) K,
          p.totalDegree ≤ 2*d → p.totalDegree + g.totalDegree ≤ weightDegree N + 2*d →
          (∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) p *
            MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g) =
          ∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b) p *
            MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g)
    · intro c g hc hcg
      simp
    · intro p i ih g hp hpg
      by_cases hz : p = 0
      · simp [hz]
      have hdeg : (p * MvPolynomial.X i).totalDegree = p.totalDegree + 1 := by
        simpa using MvPolynomial.totalDegree_mul_of_isDomain hz (MvPolynomial.X_ne_zero i)
      rw [hdeg] at hp hpg
      let g' := WeightExpansionProof.replacementGeometry havailable μ i * g
      have hg' : p.totalDegree + g'.totalDegree ≤ weightDegree N + 2*d := by
        have hmul := MvPolynomial.totalDegree_mul
          (WeightExpansionProof.replacementGeometry havailable μ i) g
        have hlin := WeightExpansionProof.replacementGeometry_degree havailable μ i
        dsimp only [g']
        omega
      have hzero := mixed_replacement_moment K N d δ hd coefficients t μ hbasis i p g
        (by omega) (by omega)
      have hone :
          (∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) p * booleanPoint b i *
            MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g) =
          ∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) p * replacement t.val μ b i *
            MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g := by
        apply sub_eq_zero.mp
        rw [← Finset.sum_sub_distrib]
        calc
          _ = ∑ b, coefficients b * (booleanPoint b i - replacement t.val μ b i) *
              MvPolynomial.eval (booleanPoint b) p *
                MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g := by
            apply Finset.sum_congr rfl
            intro b hb
            ring
          _ = 0 := hzero
      calc
        _ = ∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) p * booleanPoint b i *
            MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g := by
          simp only [map_mul, MvPolynomial.eval_X, mul_assoc]
        _ = ∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) p * replacement t.val μ b i *
            MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g := hone
        _ = ∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) p *
            MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g' := by
          simp only [g', map_mul, WeightExpansionProof.eval_replacementGeometry, mul_assoc]
        _ = ∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b) p *
            MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g' :=
          ih g' (by omega) hg'
        _ = _ := by
          simp only [g', map_mul, MvPolynomial.eval_X,
            WeightExpansionProof.eval_replacementGeometry, mul_assoc]
  let L := polynomialMoment coefficients
    (fun b : BooleanAssignment N => MvPolynomial.eval
      (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g)
    (fun b : BooleanAssignment N => booleanPoint b)
  let M := polynomialMoment coefficients
    (fun b : BooleanAssignment N => MvPolynomial.eval
      (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) g)
    (replacement t.val μ)
  change L f = M f
  rw [f.as_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm'
  have hdeg : (MvPolynomial.monomial m (MvPolynomial.coeff m f)).totalDegree ≤ f.totalDegree :=
    (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree hm')
  exact hm m (MvPolynomial.coeff m f) g (hdeg.trans hf)
    ((Nat.add_le_add_right hdeg _).trans hfg)

noncomputable def substitutionLinear {K : Type*} [Field K] {M : ℕ}
    (v : Fin M → MvPolynomial (Fin M) K) :
    MvPolynomial (Fin M) K →ₗ[K] MvPolynomial (Fin M) K where
  toFun f := MvPolynomial.eval₂Hom MvPolynomial.C v f
  map_add' f g := map_add _ _ _
  map_smul' c f := by simp [MvPolynomial.smul_eq_C_mul]

theorem functional_substitution {K : Type*} [Field K] {M : ℕ}
    (E : ℕ) (v : Fin M → MvPolynomial (Fin M) K) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (L : MvPolynomial (Fin M) K →ₗ[K] K)
    (hdef : ∀ (i : Fin M) (p : MvPolynomial (Fin M) K), p.totalDegree + 1 ≤ E →
      L ((MvPolynomial.X i - v i) * p) = 0)
    (f g : MvPolynomial (Fin M) K) (hfg : f.totalDegree + g.totalDegree ≤ E) :
    L (f * g) = L (MvPolynomial.eval₂Hom MvPolynomial.C v f * g) := by
  classical
  let S := substitutionLinear v
  have hSmul (a b : MvPolynomial (Fin M) K) : S (a * b) = S a * S b := by
    change (MvPolynomial.eval₂Hom MvPolynomial.C v) (a*b) =
      (MvPolynomial.eval₂Hom MvPolynomial.C v) a * (MvPolynomial.eval₂Hom MvPolynomial.C v) b
    exact map_mul _ _ _
  have hSX (i : Fin M) : S (MvPolynomial.X i) = v i := by simp [S, substitutionLinear]
  have hm : ∀ (m : Fin M →₀ ℕ) (c : K) (g : MvPolynomial (Fin M) K),
      (MvPolynomial.monomial m c).totalDegree + g.totalDegree ≤ E →
      L (MvPolynomial.monomial m c * g) = L (S (MvPolynomial.monomial m c) * g) := by
    apply MvPolynomial.induction_on_monomial
      (motive := fun p : MvPolynomial (Fin M) K => ∀ g : MvPolynomial (Fin M) K,
        p.totalDegree + g.totalDegree ≤ E → L (p * g) = L (S p * g))
    · intro c g hcg
      simp [S, substitutionLinear]
    · intro p i ih g hpg
      by_cases hz : p = 0
      · simp [hz]
      have hdeg : (p * MvPolynomial.X i).totalDegree = p.totalDegree + 1 := by
        simpa using MvPolynomial.totalDegree_mul_of_isDomain hz (MvPolynomial.X_ne_zero i)
      rw [hdeg] at hpg
      have hmul := MvPolynomial.totalDegree_mul p g
      have hzero := hdef i (p*g) (by omega)
      have hone : L ((p * MvPolynomial.X i) * g) = L ((p * v i) * g) := by
        apply sub_eq_zero.mp
        rw [← map_sub]
        have heq : (p * MvPolynomial.X i) * g - (p * v i) * g =
            (MvPolynomial.X i - v i) * (p*g) := by ring
        rw [heq]
        exact hzero
      have hbound : p.totalDegree + (v i * g).totalDegree ≤ E := by
        have hh := MvPolynomial.totalDegree_mul (v i) g
        have hh' := hv i
        omega
      calc
        _ = L (p * (v i * g)) := by rw [hone]; congr 1; ring
        _ = L (S p * (v i * g)) := ih _ hbound
        _ = _ := by rw [hSmul, hSX]; congr 1; ring
  let Lg := L.comp (LinearMap.mulRight K g)
  let Mg := Lg.comp S
  change Lg f = Mg f
  rw [f.as_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm'
  have hdeg : (MvPolynomial.monomial m (MvPolynomial.coeff m f)).totalDegree ≤ f.totalDegree :=
    (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree hm')
  exact hm m (MvPolynomial.coeff m f) g ((Nat.add_le_add_right hdeg _).trans hfg)

theorem weighted_stack_replacement {K : Type*} [Field K] {N d δ : ℕ} (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (coefficients : BooleanAssignment N → K)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ)
    (H : MvPolynomial (Fin ((rankTarget N d)^2)) K)
    (f : MvPolynomial (Fin N) K) (hH : H.totalDegree ≤ weightDegree N) (hf : f.totalDegree ≤ 2*d) :
    (∑ b, coefficients b *
      MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b) H *
        MvPolynomial.eval (booleanPoint b) f) =
    replacementFunctional coefficients t.val μ
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun j : Fin ((rankTarget N d)^2) =>
          WeightExpansionProof.geometryPolynomial (K := K) (N := N) j.val t.val) H * f) := by
  classical
  let point : BooleanAssignment N → Fin ((rankTarget N d)^2) → K :=
    fun b j => geometricForm j.val t.val b
  let geo : Fin ((rankTarget N d)^2) → MvPolynomial (Fin N) K :=
    fun j => WeightExpansionProof.geometryPolynomial j.val t.val
  let bits := WeightExpansionProof.replacementGeometry havailable μ
  let G : Fin ((rankTarget N d)^2) → MvPolynomial (Fin ((rankTarget N d)^2)) K :=
    fun j => MvPolynomial.eval₂Hom MvPolynomial.C bits (geo j)
  let L : MvPolynomial (Fin ((rankTarget N d)^2)) K →ₗ[K] K :=
    (ReplacementMomentProof.weightedSum coefficients).comp (WeightExpansionProof.evaluationMap point)
  let E := weightDegree N + 2*d
  have hG (j : Fin ((rankTarget N d)^2)) : (G j).totalDegree ≤ 1 :=
    (WeightExpansionProof.degree_substitution_le bits
      (WeightExpansionProof.replacementGeometry_degree havailable μ) (geo j)).trans
      (WeightExpansionProof.geometry_degree_le j.val t.val)
  have hgeoEval (b : BooleanAssignment N) (j : Fin ((rankTarget N d)^2)) :
      point b j = MvPolynomial.eval (booleanPoint b) (geo j) :=
    (WeightExpansionProof.eval_geometry j.val t.val b).symm
  have hGEval (b : BooleanAssignment N) (j : Fin ((rankTarget N d)^2)) :
      MvPolynomial.eval (point b) (G j) = MvPolynomial.eval (replacement t.val μ b) (geo j) :=
    WeightExpansionProof.eval_substituteGeometry havailable t.val μ b (geo j)
  have hdef (j : Fin ((rankTarget N d)^2)) (p : MvPolynomial (Fin ((rankTarget N d)^2)) K)
      (hp : p.totalDegree + 1 ≤ E) : L ((MvPolynomial.X j - G j) * p) = 0 := by
    have hgeo := WeightExpansionProof.geometry_degree_le (K := K) (N := N) j.val t.val
    have hh := bit_moment_substitution hd havailable coefficients t μ hbasis (geo j) p
      (by dsimp only [geo]; omega) (by dsimp only [E] at hp; dsimp only [geo]; omega)
    change (∑ b, coefficients b * MvPolynomial.eval (point b) ((MvPolynomial.X j - G j) * p)) = 0
    have heq :
        (∑ b, coefficients b * MvPolynomial.eval (point b) ((MvPolynomial.X j - G j) * p)) =
        (∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) (geo j) * MvPolynomial.eval (point b) p) -
          ∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b) (geo j) * MvPolynomial.eval (point b) p := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [map_mul, map_sub, MvPolynomial.eval_X, hgeoEval, hGEval]
      ring
    rw [heq, hh, sub_self]
  let g := MvPolynomial.eval₂Hom MvPolynomial.C bits f
  have hg : g.totalDegree ≤ f.totalDegree :=
    WeightExpansionProof.degree_substitution_le bits
      (WeightExpansionProof.replacementGeometry_degree havailable μ) f
  have hinv := functional_substitution E G hG L hdef H g
    (by dsimp only [E]; exact Nat.add_le_add hH (hg.trans hf))
  have hgEval (b : BooleanAssignment N) :
      MvPolynomial.eval (point b) g = MvPolynomial.eval (replacement t.val μ b) f :=
    WeightExpansionProof.eval_substituteGeometry havailable t.val μ b f
  have hτEval (b : BooleanAssignment N) :
      MvPolynomial.eval (point b) (MvPolynomial.eval₂Hom MvPolynomial.C G H) =
        MvPolynomial.eval (replacement t.val μ b) (MvPolynomial.eval₂Hom MvPolynomial.C geo H) := by
    calc
      _ = MvPolynomial.eval (fun j => MvPolynomial.eval (point b) (G j)) H :=
        WeightExpansionProof.eval_substitution G (point b) H
      _ = MvPolynomial.eval (fun j => MvPolynomial.eval (replacement t.val μ b) (geo j)) H := by
        apply congrArg (fun pt : Fin ((rankTarget N d)^2) → K => MvPolynomial.eval pt H)
        funext j
        exact hGEval b j
      _ = _ := (WeightExpansionProof.eval_substitution geo (replacement t.val μ b) H).symm
  calc
    _ = ∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) f * MvPolynomial.eval (point b) H := by
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b) f * MvPolynomial.eval (point b) H :=
      bit_moment_substitution hd havailable coefficients t μ hbasis f H hf (by omega)
    _ = L (H*g) := by
      change _ = ∑ b, coefficients b * MvPolynomial.eval (point b) (H*g)
      simp only [map_mul, hgEval]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = L (MvPolynomial.eval₂Hom MvPolynomial.C G H * g) := hinv
    _ = _ := by
      change (∑ b, coefficients b * MvPolynomial.eval (point b)
          (MvPolynomial.eval₂Hom MvPolynomial.C G H * g)) =
        ∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b)
          (MvPolynomial.eval₂Hom MvPolynomial.C geo H * f)
      simp only [map_mul, hgEval, hτEval]

noncomputable def bitPolynomial {K : Type*} [Field K] {N : ℕ}
    (S : Finset (Fin N)) : MvPolynomial (Fin N) K := ∏ i ∈ S, MvPolynomial.X i

theorem bitPolynomial_degree {K : Type*} [Field K] {N : ℕ} (S : Finset (Fin N)) :
    (bitPolynomial (K := K) S).totalDegree ≤ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [bitPolynomial]
  | @insert i S hi ih =>
    simp only [bitPolynomial, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      rw [MvPolynomial.totalDegree_X]
      dsimp only [bitPolynomial] at ih
      omega)

theorem bitPolynomial_eval {K : Type*} [Field K] {N : ℕ}
    (S : Finset (Fin N)) (b : BooleanAssignment N) :
    MvPolynomial.eval (booleanPoint b) (bitPolynomial (K := K) S) = bitProduct b S := by
  simp [bitPolynomial, bitProduct]

theorem ordinary_polynomial_expansion {K : Type*} [Field K] {N e : ℕ}
    (p : MvPolynomial (Fin N) K) (hp : p.totalDegree ≤ e) :
    ∃ a : OrdinaryMonomial N e → K, p = ∑ u, a u • monomialPolynomial u := by
  classical
  have hmem : p ∈ Submodule.span K (Set.range (fun u : OrdinaryMonomial N e => monomialPolynomial (K := K) u)) := by
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro m hm
    have hdeg : m.sum (fun _ n => n) ≤ e := (MvPolynomial.le_totalDegree hm).trans hp
    have heq : MvPolynomial.monomial m (MvPolynomial.coeff m p) =
        MvPolynomial.coeff m p • monomialPolynomial (SelectorProof.ofExponent m hdeg) := by
      rw [SelectorProof.polynomial_ofExponent]
      simp [MvPolynomial.smul_monomial]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  exact ⟨a, ha.symm⟩

theorem rectangular_reverse_factorization_aux
    (K : Type*) [Field K] (N d δ : ℕ) (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (coefficients : BooleanAssignment N → K)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ) :
    ∃ (P : Matrix (OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d)
        (OrdinaryMonomial N (weightDegree N + d)) K)
      (Q : Matrix (OrdinaryMonomial N d) (BitMonomial N d) K),
      sampleStack (representedStack (d := d) coefficients) t =
        P * rectangularTable (weightDegree N + d) d
          (replacementFunctional coefficients t.val μ) * Q := by
  classical
  let geo : Fin ((rankTarget N d)^2) → MvPolynomial (Fin N) K :=
    fun j => WeightExpansionProof.geometryPolynomial j.val t.val
  let rp : (OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d) →
      MvPolynomial (Fin N) K := fun row =>
    MvPolynomial.eval₂Hom MvPolynomial.C geo (monomialPolynomial row.1) * bitPolynomial row.2.val
  let cp : BitMonomial N d → MvPolynomial (Fin N) K := fun T => bitPolynomial T.val
  have hrp (row : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d) :
      (rp row).totalDegree ≤ weightDegree N + d :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add
      ((WeightExpansionProof.degree_substitution_le geo
        (fun j => WeightExpansionProof.geometry_degree_le j.val t.val) _).trans
        (SelectorProof.monomial_degree_le row.1))
      ((bitPolynomial_degree row.2.val).trans row.2.property))
  have hcp (T : BitMonomial N d) : (cp T).totalDegree ≤ d :=
    (bitPolynomial_degree T.val).trans T.property
  have hentry (row : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d)
      (T : BitMonomial N d) :
      sampleStack (representedStack (d := d) coefficients) t row T =
        ∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b) (rp row) *
          MvPolynomial.eval (replacement t.val μ b) (cp T) := by
    have hdeg : ((bitPolynomial (K := K) row.2.val) * bitPolynomial T.val).totalDegree ≤ 2*d :=
      (MvPolynomial.totalDegree_mul _ _).trans (by
        have hh := bitPolynomial_degree (K := K) row.2.val
        have hh' := bitPolynomial_degree (K := K) T.val
        have hr := row.2.property
        have hc := T.property
        omega)
    have hh := weighted_stack_replacement hd havailable coefficients t μ hbasis
      (monomialPolynomial row.1) (bitPolynomial row.2.val * bitPolynomial T.val)
      (SelectorProof.monomial_degree_le row.1) hdeg
    change (∑ b, coefficients b *
      MvPolynomial.eval (fun j : Fin ((rankTarget N d)^2) => geometricForm j.val t.val b)
        (monomialPolynomial row.1) *
      MvPolynomial.eval (booleanPoint b) (bitPolynomial row.2.val * bitPolynomial T.val)) =
      ∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b)
        (MvPolynomial.eval₂Hom MvPolynomial.C geo (monomialPolynomial row.1) *
          (bitPolynomial row.2.val * bitPolynomial T.val)) at hh
    simpa only [sampleStack, SurvivingProof.stack_apply, WeightExpansionProof.eval_weight,
      map_mul, bitPolynomial_eval, rp, cp, geo, mul_assoc] using hh
  have hrow (row : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d) :
      ∃ a : OrdinaryMonomial N (weightDegree N + d) → K,
        rp row = ∑ u, a u • monomialPolynomial u := ordinary_polynomial_expansion (rp row) (hrp row)
  choose P hP using hrow
  have hcol (T : BitMonomial N d) : ∃ a : OrdinaryMonomial N d → K,
      cp T = ∑ v, a v • monomialPolynomial v := ordinary_polynomial_expansion (cp T) (hcp T)
  choose Q hQ using hcol
  let r := fun u : OrdinaryMonomial N (weightDegree N + d) =>
    fun b : BooleanAssignment N => MvPolynomial.eval (replacement t.val μ b) (monomialPolynomial u)
  let c := fun v : OrdinaryMonomial N d =>
    fun b : BooleanAssignment N => MvPolynomial.eval (replacement t.val μ b) (monomialPolynomial v)
  have hrowEval (row : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d)
      (b : BooleanAssignment N) :
      MvPolynomial.eval (replacement t.val μ b) (rp row) = ∑ u, P row u * r u b := by
    rw [hP row]
    simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, r]
  have hcolEval (T : BitMonomial N d) (b : BooleanAssignment N) :
      MvPolynomial.eval (replacement t.val μ b) (cp T) = ∑ v, Q T v * c v b := by
    rw [hQ T]
    simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, c]
  have hH : rectangularTable (weightDegree N + d) d (replacementFunctional coefficients t.val μ) =
      (Matrix.of fun u v => ∑ b, coefficients b * r u b * c v b) := by
    apply Matrix.ext
    intro u v
    change (∑ b, coefficients b * MvPolynomial.eval (replacement t.val μ b)
      (monomialPolynomial u * monomialPolynomial v)) = _
    simp only [Matrix.of_apply, map_mul, r, c, mul_assoc]
  have hAt : sampleStack (representedStack (d := d) coefficients) t =
      (Matrix.of fun row T => ∑ b, coefficients b *
        (∑ u, P row u * r u b) * (∑ v, Q T v * c v b)) := by
    apply Matrix.ext
    intro row T
    rw [hentry]
    simp only [Matrix.of_apply, hrowEval, hcolEval]
  refine ⟨Matrix.of P, Matrix.of (fun v T => Q T v), ?_⟩
  rw [hAt, hH]
  exact feature_factorization coefficients r c (Matrix.of P) (Matrix.of (fun v T => Q T v))


end StackRankProof
end GenericGroupWE.Main


open scoped BigOperators
namespace GenericGroupWE.Main

theorem rectangular_reverse_factorization :
  ∀ (K : Type*) [Field K] (N d δ : ℕ) (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d) ^ 2)
    (coefficients : BooleanAssignment N → K)
    (t : Fin (N * ((rankTarget N d) ^ 2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ),
    ∃ (P : Matrix (OrdinaryMonomial ((rankTarget N d) ^ 2) (weightDegree N) × BitMonomial N d)
        (OrdinaryMonomial N (weightDegree N + d)) K)
      (Q : Matrix (OrdinaryMonomial N d) (BitMonomial N d) K),
      sampleStack (representedStack (d := d) coefficients) t =
        P * rectangularTable (weightDegree N + d) d
          (replacementFunctional coefficients t.val μ) * Q := by
  intro K _ N d δ hd havailable coefficients t μ hbasis
  exact StackRankProof.rectangular_reverse_factorization_aux K N d δ hd havailable coefficients t μ hbasis

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.TestedReplacementMoments
namespace GenericGroupWE.Main
namespace TestedTransferProof
open scoped BigOperators

noncomputable def weightedSum {K Ω : Type*} [Field K] [Fintype Ω]
    (w : Ω → K) : (Ω → K) →ₗ[K] K where
  toFun f := ∑ b, w b * f b
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem represented_moment_eq {K : Type*} [Field K] {N d : ℕ}
    (coefficients other : BooleanAssignment N → K)
    (heq : representedStack (d := d) coefficients = representedStack other)
    (h : WeightLabel N d) (p : MvPolynomial (Fin N) K) (hp : p.totalDegree ≤ 2*d) :
    ∑ b, coefficients b * stackWeight h b * MvPolynomial.eval (booleanPoint b) p =
      ∑ b, other b * stackWeight h b * MvPolynomial.eval (booleanPoint b) p := by
  classical
  have hbit : ∀ S : Finset (Fin N), S.card ≤ 2*d →
      ∑ b, (coefficients b - other b) * stackWeight h b * bitProduct b S = 0 := by
    intro S hS
    obtain ⟨U, V, hUV⟩ := SurvivingProof.split_set (a := d) (b := d) S (by omega)
    have hentry := congrFun (congrFun heq (h,U)) V
    rw [SurvivingProof.stack_apply, SurvivingProof.stack_apply] at hentry
    have hentry' : ∑ b, coefficients b * stackWeight h b * bitProduct b S =
        ∑ b, other b * stackWeight h b * bitProduct b S := by
      simpa only [mul_assoc, ← SurvivingProof.bitProduct_union, hUV] using hentry
    calc
      ∑ b, (coefficients b - other b) * stackWeight h b * bitProduct b S =
          (∑ b, coefficients b * stackWeight h b * bitProduct b S) -
            ∑ b, other b * stackWeight h b * bitProduct b S := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = 0 := sub_eq_zero.mpr hentry'
  have hzero := SurvivingProof.polynomial_zero_of_bitProducts
    (fun b => (coefficients b - other b) * stackWeight h b) hbit p hp
  apply sub_eq_zero.mp
  calc
    (∑ b, coefficients b * stackWeight h b * MvPolynomial.eval (booleanPoint b) p) -
        (∑ b, other b * stackWeight h b * MvPolynomial.eval (booleanPoint b) p) =
      ∑ b, (coefficients b - other b) * stackWeight h b *
        MvPolynomial.eval (booleanPoint b) p := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = 0 := hzero

theorem tested_base {K : Type*} [Field K] {N k d : ℕ} (hd : 1 ≤ d)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (coefficients : BooleanAssignment N → K)
    (hmem : representedStack (d := d) coefficients ∈ testedSpace q)
    (h : WeightLabel N d) (s : Fin k) (p : MvPolynomial (Fin N) K)
    (hp : p.totalDegree + 2 ≤ 2*d) :
    ∑ b, coefficients b * stackWeight h b * MvPolynomial.eval (booleanPoint b) (q s) *
      MvPolynomial.eval (booleanPoint b) p = 0 := by
  classical
  rcases hmem with ⟨other, heq, htests⟩
  have hother : ∑ b, other b * stackWeight h b * MvPolynomial.eval (booleanPoint b) (q s) *
      MvPolynomial.eval (booleanPoint b) p = 0 := by
    apply SurvivingProof.polynomial_zero_of_bitProducts (e := 2*d-2)
      (fun b => other b * stackWeight h b * MvPolynomial.eval (booleanPoint b) (q s))
      ?_ p (by omega)
    intro S hS
    exact htests h s S (by omega)
  have hpq : (q s * p).totalDegree ≤ 2*d := by
    have hm := MvPolynomial.totalDegree_mul (q s) p
    have hqdegree := hq s
    omega
  have heqp := represented_moment_eq coefficients other heq h (q s * p) hpq
  have hother' : ∑ b, other b * stackWeight h b *
      MvPolynomial.eval (booleanPoint b) (q s * p) = 0 := by
    simpa only [map_mul, mul_assoc] using hother
  simpa only [map_mul, mul_assoc] using heqp.trans hother'

end TestedTransferProof
open scoped BigOperators

theorem tested_replacement_moments :
  ∀ (K : Type*) [Field K] (N k d δ : ℕ) (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (coefficients : BooleanAssignment N → K)
    (hmem : representedStack (d := d) coefficients ∈ testedSpace q)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (f : MvPolynomial (Fin N) K) (hf : f.totalDegree + 2 ≤ weightDegree N + 2*d)
    (s : Fin k),
    ∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) (q s) *
      MvPolynomial.eval (replacement t.val μ b) f = 0 := by
  intro K _ N k d δ hd havailable q hq coefficients hmem t μ f hf s
  let F := TestedTransferProof.weightedSum
    (fun b => coefficients b * MvPolynomial.eval (booleanPoint b) (q s))
  have hF : ∀ (u : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N))
      (p : MvPolynomial (Fin N) K), p.totalDegree ≤ 2*d-2 →
      F (fun b => stackWeight (t,u) b * MvPolynomial.eval (booleanPoint b) p) = 0 := by
    intro u p hp
    have hh := TestedTransferProof.tested_base hd q hq coefficients hmem (t,u) s p (by omega)
    simpa [F, TestedTransferProof.weightedSum, mul_assoc, mul_left_comm, mul_comm] using hh
  have hdegree : f.totalDegree ≤ weightDegree N + (2*d-2) := by omega
  have hh := weighted_substitution_vanish K N d δ (2*d-2) havailable t μ F hF f hdegree
  simpa [F, TestedTransferProof.weightedSum, mul_assoc] using hh

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.TransferEquations
namespace GenericGroupWE.Main
namespace TransferProof

open scoped BigOperators

theorem agreement_succ {K : Type*} [Field K] {N : ℕ} (e : ℕ)
    (L M : MvPolynomial (Fin N) K →ₗ[K] K) (hone : L 1 = M 1)
    (hmul : ∀ (i : Fin N) (p : MvPolynomial (Fin N) K), p.totalDegree ≤ e →
      L (MvPolynomial.X i * p) = M (MvPolynomial.X i * p)) :
    ∀ f : MvPolynomial (Fin N) K, f.totalDegree ≤ e+1 → L f = M f := by
  classical
  have hm : ∀ (d : Fin N →₀ ℕ) (c : K),
      (MvPolynomial.monomial d c).totalDegree ≤ e+1 →
      L (MvPolynomial.monomial d c) = M (MvPolynomial.monomial d c) := by
    apply MvPolynomial.induction_on_monomial
      (motive := fun p : MvPolynomial (Fin N) K => p.totalDegree ≤ e+1 → L p = M p)
    · intro c hc
      have hC : MvPolynomial.C c = c • (1 : MvPolynomial (Fin N) K) := by
        simp [MvPolynomial.smul_eq_C_mul]
      rw [hC, map_smul, map_smul, hone]
    · intro p i ih hpdeg
      by_cases hp : p = 0
      · simp [hp]
      have hdp : p.totalDegree ≤ e := by
        have hh : p.totalDegree + 1 ≤ e+1 := by
          simpa [MvPolynomial.totalDegree_mul_of_isDomain hp (MvPolynomial.X_ne_zero i)] using hpdeg
        omega
      simpa only [mul_comm p (MvPolynomial.X i)] using hmul i p hdp
  intro f hf
  rw [f.as_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply hm
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans
    ((MvPolynomial.le_totalDegree hd).trans hf)

theorem agreement_affine {K : Type*} [Field K] {N : ℕ}
    (L M : MvPolynomial (Fin N) K →ₗ[K] K) (hone : L 1 = M 1)
    (hX : ∀ i : Fin N, L (MvPolynomial.X i) = M (MvPolynomial.X i)) :
    ∀ f : MvPolynomial (Fin N) K, f.totalDegree ≤ 1 → L f = M f := by
  apply agreement_succ 0 L M hone
  intro i p hp
  have hz : p.totalDegree = 0 := by omega
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz]
  simp only [mul_comm (MvPolynomial.X i), ← MvPolynomial.smul_eq_C_mul, map_smul, hX i]

theorem agreement_quadratic {K : Type*} [Field K] {N : ℕ}
    (L M : MvPolynomial (Fin N) K →ₗ[K] K) (hone : L 1 = M 1)
    (hX : ∀ i : Fin N, L (MvPolynomial.X i) = M (MvPolynomial.X i))
    (hXX : ∀ i j : Fin N, L (MvPolynomial.X i * MvPolynomial.X j) =
      M (MvPolynomial.X i * MvPolynomial.X j)) :
    ∀ f : MvPolynomial (Fin N) K, f.totalDegree ≤ 2 → L f = M f := by
  apply agreement_succ 1 L M hone
  intro i p hp
  exact agreement_affine (L.comp (LinearMap.mulLeft K (MvPolynomial.X i)))
    (M.comp (LinearMap.mulLeft K (MvPolynomial.X i)))
    (by simpa using hX i) (fun j => hXX i j) p hp

noncomputable def moment {K Ω : Type*} [Field K] [Fintype Ω]
    (coefficients multiplier : Ω → K) : (Ω → K) →ₗ[K] K where
  toFun g := ∑ b, coefficients b * g b * multiplier b
  map_add' g h := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c g := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

noncomputable def evaluationMap {K Ω : Type*} [Field K] {N : ℕ}
    (point : Ω → Fin N → K) : MvPolynomial (Fin N) K →ₗ[K] (Ω → K) where
  toFun f b := MvPolynomial.eval (point b) f
  map_add' f g := by ext b; simp
  map_smul' c f := by ext b; simp [MvPolynomial.smul_eq_C_mul]

/-- Closed algebraic bridge: first/second moments transfer every quadratic test. -/
theorem annihilation_from_moments {K : Type*} [Field K] {N k δ : ℕ}
    (e : ℕ) (q : Fin k → MvPolynomial (Fin N) K)
    (hq : ∀ s, (q s).totalDegree ≤ 2)
    (coefficients : BooleanAssignment N → K) (t : ℕ) (μ : Fin N → Fin δ → K)
    (hlow : ∀ f : MvPolynomial (Fin N) K, f.totalDegree + 2 ≤ e →
      (∀ i : Fin N, ∑ b, coefficients b *
        (replacement t μ b i - booleanPoint b i) * MvPolynomial.eval (replacement t μ b) f = 0) ∧
      (∀ i j : Fin N, ∑ b, coefficients b *
        (replacement t μ b i * replacement t μ b j - booleanPoint b i * booleanPoint b j) *
          MvPolynomial.eval (replacement t μ b) f = 0))
    (htested : ∀ f : MvPolynomial (Fin N) K, f.totalDegree + 2 ≤ e →
      ∀ s : Fin k, ∑ b, coefficients b * MvPolynomial.eval (booleanPoint b) (q s) *
        MvPolynomial.eval (replacement t μ b) f = 0) :
    AnnihilatesEquations q (replacementFunctional coefficients t μ) e := by
  intro f hf
  obtain ⟨hfirst, hsecond⟩ := hlow f hf
  let F := moment coefficients (fun b => MvPolynomial.eval (replacement t μ b) f)
  let Ls := F.comp (evaluationMap (replacement t μ))
  let Lb := F.comp (evaluationMap (fun b : BooleanAssignment N => booleanPoint b))
  have hX : ∀ i : Fin N, Ls (MvPolynomial.X i) = Lb (MvPolynomial.X i) := by
    intro i
    apply sub_eq_zero.mp
    change F (fun b => MvPolynomial.eval (replacement t μ b) (MvPolynomial.X i)) -
      F (fun b => MvPolynomial.eval (booleanPoint b) (MvPolynomial.X i)) = 0
    simp only [MvPolynomial.eval_X]
    rw [← map_sub]
    exact hfirst i
  have hXX : ∀ i j : Fin N, Ls (MvPolynomial.X i * MvPolynomial.X j) =
      Lb (MvPolynomial.X i * MvPolynomial.X j) := by
    intro i j
    apply sub_eq_zero.mp
    change F (fun b => MvPolynomial.eval (replacement t μ b) (MvPolynomial.X i * MvPolynomial.X j)) -
      F (fun b => MvPolynomial.eval (booleanPoint b) (MvPolynomial.X i * MvPolynomial.X j)) = 0
    simp only [map_mul, MvPolynomial.eval_X]
    rw [← map_sub]
    exact hsecond i j
  have hagree := agreement_quadratic Ls Lb (by simp [Ls, Lb, evaluationMap]) hX hXX
  constructor
  · intro i
    have hdeg : ((MvPolynomial.X i)^2 - MvPolynomial.X i : MvPolynomial (Fin N) K).totalDegree ≤ 2 :=
      (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    have hbool : ∀ b : BooleanAssignment N,
        MvPolynomial.eval (booleanPoint b) ((MvPolynomial.X i)^2 - MvPolynomial.X i :
          MvPolynomial (Fin N) K) = 0 := by
      intro b
      simp only [map_sub, map_pow, MvPolynomial.eval_X]
      cases hb : b i <;> simp [booleanPoint, hb]
    have hLb : Lb ((MvPolynomial.X i)^2 - MvPolynomial.X i) = 0 := by
      simp [Lb, F, moment, evaluationMap, hbool]
    have hLs := (hagree _ hdeg).trans hLb
    simpa [Ls, F, moment, evaluationMap, replacementFunctional, mul_assoc] using hLs
  · intro s
    have hLb : Lb (q s) = 0 := htested f hf s
    have hLs := (hagree (q s) (hq s)).trans hLb
    simpa [Ls, F, moment, evaluationMap, replacementFunctional, mul_assoc] using hLs

end TransferProof
end GenericGroupWE.Main


namespace GenericGroupWE.Main
open scoped BigOperators

theorem eq_32 (K : Type*) [Field K] (N k d δ : ℕ) (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (q : Fin k → MvPolynomial (Fin N) K)
    (hq : ∀ s, (q s).totalDegree ≤ 2)
    (coefficients : BooleanAssignment N → K)
    (hmem : representedStack (d := d) coefficients ∈ testedSpace q)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ) :
    AnnihilatesEquations q (replacementFunctional coefficients t.val μ)
      (weightDegree N + 2*d) := by
  exact TransferProof.annihilation_from_moments (weightDegree N + 2*d) q hq
    coefficients t.val μ
    (fun f hf => replacement_low_moments K N d δ hd havailable coefficients t μ hbasis f hf)
    (fun f hf s => tested_replacement_moments K N k d δ hd havailable q hq
      coefficients hmem t μ f hf s)

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.RectangularRankSplit
namespace GenericGroupWE.Main

/-- Generic rank-nullity ingredient for the proposed additive rank child. -/
theorem finrank_split_of_triple_comp_zero
    {K U V W T : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (h : U →ₗ[K] V) (p : V →ₗ[K] W) (q : T →ₗ[K] U)
    (hz : p.comp (h.comp q) = 0) :
    Module.finrank K (LinearMap.range (p.comp h)) +
      Module.finrank K (LinearMap.range (h.comp q)) ≤
      Module.finrank K (LinearMap.range h) := by
  let R := LinearMap.range h
  let pR := p.domRestrict R
  let qR : T →ₗ[K] R := (h.comp q).codRestrict R (fun x => ⟨q x, rfl⟩)
  have hpR : LinearMap.range pR = LinearMap.range (p.comp h) := by
    simp [pR, R, LinearMap.range_domRestrict, LinearMap.range_comp]
  have hqR : Module.finrank K (LinearMap.range (h.comp q)) =
      Module.finrank K (LinearMap.range qR) := by
    have heq : R.subtype.comp qR = h.comp q := by ext x; rfl
    rw [← heq, LinearMap.range_comp, Submodule.finrank_map_subtype_eq]
  have hsub : LinearMap.range qR ≤ LinearMap.ker pR := by
    rintro x ⟨y, rfl⟩
    change p (h (q y)) = 0
    exact congrArg (fun f : T →ₗ[K] W => f y) hz
  calc
    Module.finrank K (LinearMap.range (p.comp h)) +
        Module.finrank K (LinearMap.range (h.comp q)) =
        Module.finrank K (LinearMap.range pR) +
          Module.finrank K (LinearMap.range qR) := by rw [hpR, hqR]
    _ ≤ Module.finrank K (LinearMap.range pR) +
          Module.finrank K (LinearMap.ker pR) :=
      Nat.add_le_add_left (Submodule.finrank_mono hsub) _
    _ = Module.finrank K (LinearMap.range h) :=
      pR.finrank_range_add_finrank_ker


open scoped BigOperators

noncomputable def ordinaryIncl {N e : ℕ} (u : OrdinaryMonomial N e) :
    OrdinaryMonomial N (e+1) :=
  ⟨fun j => ⟨(u.val j).val, by have h := (u.val j).isLt; omega⟩,
    by simpa using u.property.trans (Nat.le_succ e)⟩

noncomputable def ordinaryRaise {N e : ℕ} (i : Fin N) (u : OrdinaryMonomial N e) :
    OrdinaryMonomial N (e+1) := by
  classical
  refine ⟨fun j => ⟨(u.val j).val + if j=i then 1 else 0, ?_⟩, ?_⟩
  · have h := (u.val j).isLt
    split_ifs <;> omega
  · change (∑ j : Fin N, ((u.val j).val + if j=i then 1 else 0)) ≤ e+1
    rw [Finset.sum_add_distrib]
    simpa using Nat.add_le_add_right u.property 1

theorem monomial_ordinaryIncl {K : Type*} [Field K] {N e : ℕ}
    (u : OrdinaryMonomial N e) :
    monomialPolynomial (K := K) (ordinaryIncl u) = monomialPolynomial u := by
  rfl

theorem monomial_ordinaryRaise {K : Type*} [Field K] {N e : ℕ}
    (i : Fin N) (u : OrdinaryMonomial N e) :
    monomialPolynomial (K := K) (ordinaryRaise i u) =
      MvPolynomial.X i * monomialPolynomial u := by
  classical
  have hexp :
      Finsupp.equivFunOnFinite.symm (fun j => ((ordinaryRaise i u).val j).val) =
      Finsupp.single i 1 + Finsupp.equivFunOnFinite.symm (fun j => (u.val j).val) := by
    ext j
    simp [ordinaryRaise, Finsupp.single_apply, eq_comm, add_comm]
  unfold monomialPolynomial
  change MvPolynomial.monomial _ (1 : K) =
    MvPolynomial.monomial (Finsupp.single i 1) 1 * MvPolynomial.monomial _ 1
  rw [MvPolynomial.monomial_mul, one_mul, hexp]

theorem monomial_totalDegree_le {K : Type*} [Field K] {N e : ℕ}
    (u : OrdinaryMonomial N e) :
    (monomialPolynomial (K := K) u).totalDegree ≤ e := by
  unfold monomialPolynomial
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  simpa [Finsupp.sum_fintype] using u.property

/-- Direct proof draft for the named registered child. -/
theorem rectangular_rank_split :
  ∀ (K : Type*) [Field K] (N a b : ℕ)
    (L : MvPolynomial (Fin N) K →ₗ[K] K) (i : Fin N)
    (hboolean : ∀ f : MvPolynomial (Fin N) K,
      f.totalDegree + 2 ≤ (a+1)+(b+1) →
      L (((MvPolynomial.X i)^2 - MvPolynomial.X i) * f) = 0),
    (rectangularTable a (b+1)
      (L.comp (LinearMap.mulLeft K (MvPolynomial.X i)))).rank +
    (rectangularTable (a+1) b
      (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))).rank ≤
    (rectangularTable (a+1) (b+1) L).rank := by
  intro K _ N a b L i hboolean
  classical
  let H : Matrix (OrdinaryMonomial N (a+1)) (OrdinaryMonomial N (b+1)) K :=
    rectangularTable (a+1) (b+1) L
  let P : Matrix (OrdinaryMonomial N a) (OrdinaryMonomial N (a+1)) K :=
    Matrix.of fun u w => if w = ordinaryRaise i u then 1 else 0
  let Q : Matrix (OrdinaryMonomial N (b+1)) (OrdinaryMonomial N b) K :=
    Matrix.of fun w v => (if w = ordinaryIncl v then 1 else 0) -
      (if w = ordinaryRaise i v then 1 else 0)
  have hPH : P * H = rectangularTable a (b+1)
      (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) := by
    ext u v
    change (∑ w, P u w * H w v) =
      L (MvPolynomial.X i * (monomialPolynomial u * monomialPolynomial v))
    simp [P, H, ite_mul, rectangularTable, monomial_ordinaryRaise, mul_assoc]
  have hHQ : H * Q = rectangularTable (a+1) b
      (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) := by
    ext u v
    change (∑ w, H u w * Q w v) =
      L ((1 - MvPolynomial.X i) * (monomialPolynomial u * monomialPolynomial v))
    simp only [Q, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change L (monomialPolynomial u * monomialPolynomial (ordinaryIncl v)) -
      L (monomialPolynomial u * monomialPolynomial (ordinaryRaise i v)) =
      L ((1 - MvPolynomial.X i) * (monomialPolynomial u * monomialPolynomial v))
    rw [monomial_ordinaryIncl, monomial_ordinaryRaise, ← map_sub]
    congr 1
    ring
  have hz : P * H * Q = 0 := by
    rw [Matrix.mul_assoc, hHQ]
    ext u v
    change (∑ w, P u w *
      L ((1 - MvPolynomial.X i) * (monomialPolynomial w * monomialPolynomial v))) = 0
    simp only [P, Matrix.of_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change L ((1 - MvPolynomial.X i) *
      (monomialPolynomial (ordinaryRaise i u) * monomialPolynomial v)) = 0
    rw [monomial_ordinaryRaise]
    have hdeg : (monomialPolynomial (K := K) u * monomialPolynomial v).totalDegree + 2 ≤
        (a+1)+(b+1) := by
      have hu := monomial_totalDegree_le (K := K) u
      have hv := monomial_totalDegree_le (K := K) v
      have hm := MvPolynomial.totalDegree_mul
        (monomialPolynomial (K := K) u) (monomialPolynomial (K := K) v)
      omega
    have hb := hboolean (monomialPolynomial u * monomialPolynomial v) hdeg
    have heq : (1 - MvPolynomial.X i) *
        ((MvPolynomial.X i * monomialPolynomial u) * monomialPolynomial v) =
        -(((MvPolynomial.X i)^2 - MvPolynomial.X i) *
          (monomialPolynomial (K := K) u * monomialPolynomial v)) := by ring
    rw [heq, map_neg, hb, neg_zero]
  have hcomp : P.mulVecLin.comp (H.mulVecLin.comp Q.mulVecLin) = 0 := by
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, ← Matrix.mul_assoc,
      hz, Matrix.mulVecLin_zero]
  have hr := finrank_split_of_triple_comp_zero H.mulVecLin P.mulVecLin Q.mulVecLin hcomp
  rw [Matrix.rank, Matrix.rank, Matrix.rank, ← hPH, ← hHQ,
    Matrix.mulVecLin_mul, Matrix.mulVecLin_mul]
  exact hr

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.RectangularTables
universe u

namespace GenericGroupWE.Main

/-- Provisional local helper; no changes to the canonical definitions. -/
theorem nonzero_matrix_rank_ge_one {K : Type*} [Field K]
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n K) (hne : A ≠ 0) :
    1 ≤ A.rank := by
  classical
  by_contra h
  have hr : A.rank = 0 := by omega
  rw [Matrix.rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at hr
  apply hne
  ext i j
  have hj : A.col j ∈ Submodule.span K (Set.range A.col) :=
    Submodule.subset_span (Set.mem_range_self j)
  rw [hr] at hj
  have hj0 : A.col j = 0 := hj
  exact congrFun hj0 i

/-- Multiplication by any affine polynomial costs one degree. -/
theorem annihilates_mul_affine {K : Type*} [Field K] {N k e : ℕ}
    (q : Fin k → MvPolynomial (Fin N) K)
    (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (p : MvPolynomial (Fin N) K) (hp : p.totalDegree ≤ 1)
    (h : AnnihilatesEquations q L (e+1)) :
    AnnihilatesEquations q (L.comp (LinearMap.mulLeft K p)) e := by
  intro f hf
  have hpf : (p*f).totalDegree + 2 ≤ e + 1 := by
    have hd := MvPolynomial.totalDegree_mul p f
    omega
  obtain ⟨hb, hq⟩ := h (p*f) hpf
  constructor
  · intro i
    change L (p * (((MvPolynomial.X i)^2 - MvPolynomial.X i) * f)) = 0
    convert hb i using 1 <;> congr 1 <;> ring
  · intro s
    change L (p * (q s * f)) = 0
    convert hq s using 1 <;> congr 1 <;> ring

/-- Completely closed base case for either zero side length. -/
theorem rectangular_zero_side {K : Type*} [Field K] {N : ℕ}
    (a b : ℕ) (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (hz : a = 0 ∨ b = 0) (hne : rectangularTable a b L ≠ 0) :
    Nat.choose (a+b) a ≤ (rectangularTable a b L).rank := by
  have hr := nonzero_matrix_rank_ge_one (rectangularTable a b L) hne
  rcases hz with rfl | rfl
  · simpa using hr
  · simpa using hr

end GenericGroupWE.Main

namespace GenericGroupWE.Main

/-- Bounded direct proof of the induction, parameterized by provisional children. -/
theorem rectangular_from_splits
    (selector : ∀ (K : Type u) [Field K] (N k a b : ℕ)
      (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
      (hunsat : NoBooleanZero q) (L : MvPolynomial (Fin N) K →ₗ[K] K)
      (hidentities : AnnihilatesEquations q L ((a+1)+(b+1)))
      (hne : rectangularTable (a+1) (b+1) L ≠ 0),
      ∃ i : Fin N,
        rectangularTable a (b+1)
          (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) ≠ 0 ∧
        rectangularTable (a+1) b
          (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) ≠ 0)
    (split : ∀ (K : Type u) [Field K] (N a b : ℕ)
      (L : MvPolynomial (Fin N) K →ₗ[K] K) (i : Fin N)
      (hboolean : ∀ f : MvPolynomial (Fin N) K,
        f.totalDegree + 2 ≤ (a+1)+(b+1) →
        L (((MvPolynomial.X i)^2 - MvPolynomial.X i) * f) = 0),
      (rectangularTable a (b+1)
        (L.comp (LinearMap.mulLeft K (MvPolynomial.X i)))).rank +
      (rectangularTable (a+1) b
        (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))).rank ≤
      (rectangularTable (a+1) (b+1) L).rank)
    (K : Type u) [Field K] (N k : ℕ)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (hunsat : NoBooleanZero q) :
    ∀ (a b : ℕ) (L : MvPolynomial (Fin N) K →ₗ[K] K)
      (hidentities : a ≠ 0 → b ≠ 0 → AnnihilatesEquations q L (a+b))
      (hne : rectangularTable a b L ≠ 0),
      Nat.choose (a+b) a ≤ (rectangularTable a b L).rank := by
  intro a
  induction a with
  | zero =>
      intro b L hidentities hne
      exact rectangular_zero_side 0 b L (Or.inl rfl) hne
  | succ a ihA =>
      intro b
      induction b with
      | zero =>
          intro L hidentities hne
          exact rectangular_zero_side (a+1) 0 L (Or.inr rfl) hne
      | succ b ihB =>
          intro L hidentities hne
          have hAnn := hidentities (by omega) (by omega)
          obtain ⟨i, hx, h1x⟩ := selector K N k a b q hq hunsat L hAnn hne
          have hxAnn : AnnihilatesEquations q
              (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) (a+(b+1)) := by
            apply annihilates_mul_affine q L (MvPolynomial.X i) (by simp)
            convert hAnn using 1 <;> omega
          have h1xAnn : AnnihilatesEquations q
              (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i))) ((a+1)+b) := by
            apply annihilates_mul_affine q L (1 - MvPolynomial.X i)
            · exact (MvPolynomial.totalDegree_sub 1 (MvPolynomial.X i)).trans (by simp)
            · convert hAnn using 1 <;> omega
          have hxBound := ihA (b+1)
            (L.comp (LinearMap.mulLeft K (MvPolynomial.X i))) (fun _ _ => hxAnn) hx
          have h1xBound := ihB
            (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))
            (fun _ _ => h1xAnn) h1x
          calc
            Nat.choose ((a+1)+(b+1)) (a+1) =
                Nat.choose (a+(b+1)) a + Nat.choose ((a+1)+b) (a+1) := by
                  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Nat.choose_succ_succ' (a+b+1) a)
            _ ≤ (rectangularTable a (b+1)
                  (L.comp (LinearMap.mulLeft K (MvPolynomial.X i)))).rank +
                (rectangularTable (a+1) b
                  (L.comp (LinearMap.mulLeft K (1 - MvPolynomial.X i)))).rank :=
              Nat.add_le_add hxBound h1xBound
            _ ≤ (rectangularTable (a+1) (b+1) L).rank :=
              split K N a b L i (fun f hf => (hAnn f hf).1 i)

end GenericGroupWE.Main

namespace GenericGroupWE.Main

theorem lemma_6_2 (K : Type*) [Field K] (N k a b : ℕ)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (hunsat : NoBooleanZero q) (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (hidentities : a ≠ 0 → b ≠ 0 → AnnihilatesEquations q L (a+b))
    (hne : rectangularTable a b L ≠ 0) :
    Nat.choose (a+b) a ≤ (rectangularTable a b L).rank := by
  exact rectangular_from_splits rectangular_selector_nonzero rectangular_rank_split
    K N k q hq hunsat a b L hidentities hne

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.StackRank
namespace GenericGroupWE.Main
open scoped BigOperators

theorem sec_6_4_rank (p N k d : ℕ) [Fact p.Prime] (hd : 1 ≤ d)
    (hp : max (2^N) (N * ((rankTarget N d)^2 + weightDegree N)) < p)
    (q : Fin k → MvPolynomial (Fin N) (ZMod p))
    (hq : ∀ s, (q s).totalDegree ≤ 2) (hunsat : NoBooleanZero q)
    (A : Matrix (StackRow N d) (BitMonomial N d) (ZMod p))
    (hmem : A ∈ testedSpace q) (hne : A ≠ 0) :
    rankTarget N d ≤ A.rank := by
  classical
  by_cases hbig : rankTarget N d ≤ A.rank
  · exact hbig
  have hsmall : A.rank < rankTarget N d := Nat.lt_of_not_ge hbig
  obtain ⟨coefficients, hA, htests⟩ := hmem
  subst A
  let A := representedStack (d := d) coefficients
  let δ := survivingDimension hd A
  have hsurv := eq_29_30 (ZMod p) N d hd coefficients hne
  have havailable : δ ≤ (rankTarget N d) ^ 2 :=
    hsurv.2.1.trans (Nat.pow_le_pow_left hsmall.le 2)
  obtain ⟨t, μ, hbasis, hsample⟩ := joint_useful_sample p N d hd hp coefficients hne havailable
  let L := replacementFunctional coefficients t.val μ
  let H := rectangularTable (weightDegree N + d) d L
  obtain ⟨P, Q, hforward⟩ := rectangular_forward_factorization (ZMod p) N d δ hd havailable coefficients t μ
  obtain ⟨U, V, hreverse⟩ := rectangular_reverse_factorization (ZMod p) N d δ hd havailable coefficients t μ hbasis
  change H = P * sampleStack A t * Q at hforward
  change sampleStack A t = U * H * V at hreverse
  have hH : H ≠ 0 := by
    intro hz
    apply hsample
    rw [hz, Matrix.mul_zero, Matrix.zero_mul] at hreverse
    exact hreverse
  have hrank : H.rank ≤ A.rank := by
    calc
      H.rank = (P * sampleStack A t * Q).rank := congrArg Matrix.rank hforward
      _ ≤ (sampleStack A t).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      _ ≤ A.rank := A.rank_submatrix_le
        (fun row : OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d =>
          ((t, row.1), row.2)) id
  have hmem' : A ∈ testedSpace q := ⟨coefficients, rfl, htests⟩
  have hann := eq_32 (ZMod p) N k d δ hd havailable q hq coefficients hmem' t μ hbasis
  have hlower := lemma_6_2 (ZMod p) N k (weightDegree N + d) d q hq hunsat L
    (fun _ _ => by convert hann using 1 <;> omega) hH
  have hchoose : Nat.choose ((weightDegree N + d) + d) (weightDegree N + d) =
      rankTarget N d := by
    rw [Nat.choose_symm_add]
    simp only [rankTarget, Nat.two_mul, Nat.add_assoc]
  rw [hchoose] at hlower
  exact (not_lt_of_ge (hlower.trans hrank) hsmall).elim

end GenericGroupWE.Main

open scoped BigOperators
open GenericGroupWE.Main

theorem solution :
∀ (p N k d : ℕ) [Fact p.Prime] (hd : 1 ≤ d)
    (hp : max (2^N) (N * ((rankTarget N d)^2 + weightDegree N)) < p)
    (q : Fin k → MvPolynomial (Fin N) (ZMod p))
    (hq : ∀ s, (q s).totalDegree ≤ 2) (hunsat : NoBooleanZero q)
    (A : Matrix (StackRow N d) (BitMonomial N d) (ZMod p))
    (hmem : A ∈ testedSpace q) (hne : A ≠ 0),
rankTarget N d ≤ A.rank :=
  @GenericGroupWE.Main.sec_6_4_rank
