-- Prove2me | solution 1 for GenericGroupWE.Main.eq_29_30
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-15T12:24:28.207451+00:00
-- url     : https://prove2.me/submissions/4a371e3c-5ff9-4fbd-8963-92eeb3aa1f8e

import Definitions.Def_GenericGroupWE_Main_Tables


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

open scoped BigOperators
open GenericGroupWE.Main

theorem solution :
  ∀ (K : Type*) [Field K] (N d : ℕ) (hd : 1 ≤ d)
    (coefficients : BooleanAssignment N → K)
    (hne : representedStack (d := d) coefficients ≠ 0),
let A := representedStack (d := d) coefficients;
    1 ≤ survivingDimension hd A ∧ survivingDimension hd A ≤ A.rank ^ 2 ∧
    ∀ κ : Option (Fin N) → K,
      (∑ i, κ i • survivingColumn hd A i) = 0 →
      ∀ (h : WeightLabel N d) (f : MvPolynomial (Fin N) K), f.totalDegree + 1 ≤ 2*d →
        ∑ b, coefficients b * affineBit κ b * stackWeight h b *
          MvPolynomial.eval (booleanPoint b) f = 0 := @GenericGroupWE.Main.eq_29_30
