-- Prove2me | solution 1 for GenericGroupWE.Main.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-15T12:35:56.275839+00:00
-- url     : https://prove2.me/submissions/ce920559-6bf3-412e-9486-b5d0b3a26721

import Definitions.Def_GenericGroupWE_Main_Tables

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

open scoped BigOperators
open GenericGroupWE.Main

theorem solution :
∀ (K : Type*) [Field K] (N k d δ : ℕ) (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (q : Fin k → MvPolynomial (Fin N) K)
    (hq : ∀ s, (q s).totalDegree ≤ 2)
    (coefficients : BooleanAssignment N → K)
    (hmem : representedStack (d := d) coefficients ∈ testedSpace q)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ),
AnnihilatesEquations q (replacementFunctional coefficients t.val μ)
      (weightDegree N + 2*d) :=
  @GenericGroupWE.Main.eq_32
