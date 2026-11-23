-- Prove2me | solution 1 for GlobalTheory.SplitWeil.iwasawa_blockTriangular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:40.502752+00:00
-- url     : https://prove2.me/submissions/3da03930-c970-44c1-ad54-bfc12b6f8a2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
namespace GlobalTheory.SplitWeil
private theorem entries_mem_integer_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] {g : GL ι k} (hg : g ∈ KO k ι) (i j : ι) :
    g.val i j ∈ 𝒪[k] ∧ (g⁻¹).val i j ∈ 𝒪[k] := by
  obtain ⟨x, rfl⟩ := hg
  refine ⟨(x.val i j).2, ?_⟩
  rw [← map_inv]
  exact ((x⁻¹).val i j).2
private theorem exists_mem_KO_of_integral_inverse_pair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι k) (hM : ∀ i j, M i j ∈ 𝒪[k])
    (hN : ∀ i j, N i j ∈ 𝒪[k]) (hMN : M * N = 1) (hNM : N * M = 1) :
    ∃ g : GL ι k, g ∈ KO k ι ∧ g.val = M ∧ (g⁻¹).val = N := by
  let M' : Matrix ι ι 𝒪[k] := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix ι ι 𝒪[k] := Matrix.of fun i j => ⟨N i j, hN i j⟩
  have e1 : (algebraMap 𝒪[k] k).mapMatrix M' = M := by ext i j; rfl
  have e2 : (algebraMap 𝒪[k] k).mapMatrix N' = N := by ext i j; rfl
  have inj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix : Matrix ι ι 𝒪[k] →+* Matrix ι ι k) :=
    Matrix.map_injective Subtype.val_injective
  have h1 : M' * N' = 1 := inj (by rw [map_mul, map_one, e1, e2, hMN])
  have h2 : N' * M' = 1 := inj (by rw [map_mul, map_one, e1, e2, hNM])
  let x : GL ι 𝒪[k] := ⟨M', N', h1, h2⟩
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x, ⟨x, rfl⟩, e1, ?_⟩
  rw [← map_inv]
  exact e2
private theorem exists_mem_KO_eq_one_add_of_sq_eq_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι k) (hN : ∀ i j, N i j ∈ 𝒪[k]) (hNN : N * N = 0) :
    ∃ g ∈ KO k ι, g.val = 1 + N := by
  have hone : ∀ i j, (1 : Matrix ι ι k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
  have e2 : (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
  obtain ⟨g, hg, hv, -⟩ := exists_mem_KO_of_integral_inverse_pair (1 + N) (1 - N) (fun i j => add_mem (hone i j) (hN i j))
    (fun i j => sub_mem (hone i j) (hN i j)) (by rw [e1, hNN, sub_zero]) (by rw [e2, hNN, sub_zero])
  exact ⟨g, hg, hv⟩
private theorem exists_mem_KO_pivot_ne_zero_valuation_max {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι k) (i0 : ι) :
    ∃ u ∈ KO k ι, (g * u).val i0 i0 ≠ 0 ∧
      ∀ j, valuation k ((g * u).val i0 j) ≤ valuation k ((g * u).val i0 i0) := by
  have hrow : ∃ j, g.val i0 j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have h1 := congrFun (congrFun (Units.mul_inv g) i0) i0
    simp [Matrix.mul_apply, hcon] at h1
  have : Nonempty ι := ⟨i0⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j => valuation k (g.val i0 j))
  have hj0ne : g.val i0 j0 ≠ 0 := by
    obtain ⟨j, hj⟩ := hrow
    intro hz
    have h := hj0 j
    simp only [hz, map_zero] at h
    exact hj ((Valuation.zero_iff _).mp (le_antisymm h zero_le))
  by_cases hcase : valuation k (g.val i0 j0) ≤ valuation k (g.val i0 i0)
  · refine ⟨1, one_mem _, ?_, ?_⟩
    · simp only [mul_one]
      intro hz
      rw [hz, map_zero] at hcase
      exact hj0ne ((Valuation.zero_iff _).mp (le_antisymm hcase zero_le))
    · intro j
      simp only [mul_one]
      exact (hj0 j).trans hcase
  · replace hcase := not_le.mp hcase
    have hne : j0 ≠ i0 := by
      rintro rfl
      exact lt_irrefl _ hcase
    obtain ⟨u, hu, hval⟩ := exists_mem_KO_eq_one_add_of_sq_eq_zero (Matrix.of fun l j => if l = j0 ∧ j = i0 then (1 : k) else 0)
      (by
        intro l j
        simp only [Matrix.of_apply]
        split_ifs
        exacts [one_mem _, zero_mem _])
      (by
        ext l j
        simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
        apply Finset.sum_eq_zero
        intro m _
        by_cases hm : m = i0
        · have : ¬ (m = j0 ∧ j = i0) := fun h => hne (h.1.symm.trans hm)
          simp [this]
        · simp [hm])
    refine ⟨u, hu, ?_⟩
    have key : ∀ j, (g * u).val i0 j = g.val i0 j + if j = i0 then g.val i0 j0 else 0 := by
      intro j
      rw [Units.val_mul, hval, mul_add, mul_one, Matrix.add_apply]
      congr 1
      by_cases hj : j = i0
      · simp [Matrix.mul_apply, hj]
      · simp [Matrix.mul_apply, hj]
    have hsum : valuation k ((g * u).val i0 i0) = valuation k (g.val i0 j0) := by
      rw [key, if_pos rfl]
      exact (valuation k).map_add_eq_of_lt_right hcase
    refine ⟨?_, ?_⟩
    · intro hz
      rw [hz, map_zero] at hsum
      exact hj0ne ((Valuation.zero_iff _).mp hsum.symm)
    · intro j
      rw [hsum]
      by_cases hj : j = i0
      · rw [hj, hsum]
      · rw [key, if_neg hj, add_zero]
        exact hj0 j
private theorem exists_mem_KO_row_eq_zero_of_pivot_max {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι k) (i0 : ι) (hc : g.val i0 i0 ≠ 0)
    (hle : ∀ j, valuation k (g.val i0 j) ≤ valuation k (g.val i0 i0)) :
    ∃ u ∈ KO k ι, ∀ j, j ≠ i0 → (g * u).val i0 j = 0 := by
  obtain ⟨u, hu, hval⟩ := exists_mem_KO_eq_one_add_of_sq_eq_zero
    (Matrix.of fun l j => if l = i0 ∧ j ≠ i0 then -(g.val i0 j / g.val i0 i0) else 0)
    (by
      intro l j
      simp only [Matrix.of_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, Valuation.map_neg, Valuation.map_div]
        have hpos : 0 < valuation k (g.val i0 i0) := by
          rw [zero_lt_iff]
          exact (Valuation.ne_zero_iff _).mpr hc
        exact div_le_one_of_le₀ (hle j) zero_le
      · exact zero_mem _)
    (by
      ext l j
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro m _
      by_cases hm : m = i0
      · simp [hm]
      · simp [hm])
  refine ⟨u, hu, fun j hj => ?_⟩
  rw [Units.val_mul, hval, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  have hx : ∀ x, (x = i0 ∧ j ≠ i0) ↔ x = i0 := fun x => ⟨And.left, fun h => ⟨h, hj⟩⟩
  simp only [Matrix.of_apply, hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp
  ring
private theorem exists_GL_compl_eq_of_row_eq_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (m : GL ι k) (i0 : ι) (hrow : ∀ j, j ≠ i0 → m.val i0 j = 0) :
    ∃ A : GL {i // i ≠ i0} k, ∀ i j : {i // i ≠ i0}, A.val i j = m.val i j := by
  have key : ∀ j, m.val i0 i0 * (m⁻¹).val i0 j = (1 : Matrix ι ι k) i0 j := by
    intro j
    have h := congrFun (congrFun (Units.mul_inv m) i0) j
    rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0,
      Finset.sum_eq_zero (fun l _ => by rw [hrow _ l.2, zero_mul]), add_zero] at h
    exact h
  have hc : m.val i0 i0 ≠ 0 := by
    intro hz
    have h := key i0
    rw [hz, zero_mul, Matrix.one_apply_eq] at h
    exact zero_ne_one h
  have hinv : ∀ j, j ≠ i0 → (m⁻¹).val i0 j = 0 := by
    intro j hj
    have h := key j
    rw [Matrix.one_apply_ne (Ne.symm hj)] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  refine ⟨⟨Matrix.of fun i j => m.val i j, Matrix.of fun i j => (m⁻¹).val i j, ?_, ?_⟩, fun i j => rfl⟩
  · ext i j
    have h := congrFun (congrFun (Units.mul_inv m) i) j
    rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, hinv _ j.2, mul_zero, zero_add] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [h]
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun h => hij (Subtype.ext h))]
  · ext i j
    have h := congrFun (congrFun (Units.inv_mul m) i) j
    rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, hrow _ j.2, mul_zero, zero_add] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [h]
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun h => hij (Subtype.ext h))]
private theorem exists_mem_KO_extend_of_mem_KO_compl {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (i0 : ι) (g : GL {i // i ≠ i0} k) (hg : g ∈ KO k {i // i ≠ i0}) :
    ∃ V ∈ KO k ι, (∀ j, V.val i0 j = if j = i0 then 1 else 0) ∧ (∀ i, i ≠ i0 → V.val i i0 = 0) ∧
      ∀ i j : {i // i ≠ i0}, V.val i j = g.val i j := by
  let E : Matrix {i // i ≠ i0} {i // i ≠ i0} k → Matrix ι ι k := fun X => Matrix.of fun i j =>
    if hi : i = i0 then (if j = i0 then 1 else 0) else if hj : j = i0 then 0 else X ⟨i, hi⟩ ⟨j, hj⟩
  have hl : ∀ l : {i // i ≠ i0}, ((l : ι) = i0) ↔ False := fun l => iff_false_intro l.2
  have hE : ∀ X Y, E X * E Y = E (X * Y) := by
    intro X Y
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0]
    by_cases hi : i = i0 <;> by_cases hj : j = i0 <;> simp [E, hi, hj, hl, Matrix.mul_apply]
  have hE1 : E 1 = 1 := by
    ext i j
    by_cases hi : i = i0
    · rw [hi]
      by_cases hj : j = i0
      · rw [hj]
        simp [E]
      · simp [E, hj, Matrix.one_apply_ne (Ne.symm hj)]
    · by_cases hj : j = i0
      · simp [E, hi, hj]
      · simp [E, hi, hj, Matrix.one_apply]
  have hint : ∀ X : Matrix {i // i ≠ i0} {i // i ≠ i0} k, (∀ i j, X i j ∈ 𝒪[k]) → ∀ i j, E X i j ∈ 𝒪[k] := by
    intro X hX i j
    simp only [E, Matrix.of_apply]
    split_ifs
    exacts [one_mem _, zero_mem _, zero_mem _, hX _ _]
  obtain ⟨V, hV, hv, -⟩ := exists_mem_KO_of_integral_inverse_pair (E g.val) (E (g⁻¹).val)
    (hint _ fun i j => (entries_mem_integer_of_mem_KO hg i j).1) (hint _ fun i j => (entries_mem_integer_of_mem_KO hg i j).2)
    (by rw [hE, Units.mul_inv, hE1]) (by rw [hE, Units.inv_mul, hE1])
  refine ⟨V, hV, ?_, ?_, ?_⟩
  · intro j
    rw [hv]
    simp [E]
  · intro i hi
    rw [hv]
    simp [E, hi]
  · intro i j
    rw [hv]
    simp [E, i.2, j.2]
private theorem exists_blockTriangular_mul_mem_KO_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n → ∀ (lv : ι → ℕ) (h : GL ι k),
      ∃ (b : GL ι k), b.val.BlockTriangular lv ∧ ∃ w ∈ KO k ι, h = b * w := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hn lv h
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨h, ?_, 1, one_mem _, (mul_one h).symm⟩
    intro i
    exact isEmptyElim i
  · obtain ⟨i0, hi0⟩ := Finite.exists_max lv
    obtain ⟨u1, hu1, hc, hle⟩ := exists_mem_KO_pivot_ne_zero_valuation_max h i0
    obtain ⟨u2, hu2, hrow⟩ := exists_mem_KO_row_eq_zero_of_pivot_max (h * u1) i0 hc hle
    obtain ⟨A, hA⟩ := exists_GL_compl_eq_of_row_eq_zero (h * u1 * u2) i0 hrow
    have hcard : Fintype.card {i // i ≠ i0} < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (p := fun i => i ≠ i0) (x := i0) (fun h => h rfl)
    obtain ⟨b', hb', w', hw', hAw⟩ := ih _ hcard {i // i ≠ i0} rfl (fun i => lv i) A
    obtain ⟨V, hV, hV1, -, hV3⟩ := exists_mem_KO_extend_of_mem_KO_compl i0 w'⁻¹ (inv_mem hw')
    refine ⟨h * u1 * u2 * V, ?_, V⁻¹ * (u1 * u2)⁻¹, mul_mem (inv_mem hV) (inv_mem (mul_mem hu1 hu2)), by group⟩
    intro i j hij
    have hj : j ≠ i0 := by
      rintro rfl
      exact absurd (hi0 i) (not_le.mpr hij)
    rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, hV1 j, if_neg hj,
      mul_zero, zero_add]
    by_cases hi : i = i0
    · apply Finset.sum_eq_zero
      intro l _
      rw [hi, hrow _ l.2, zero_mul]
    · have hb : b'.val ⟨i, hi⟩ ⟨j, hj⟩ = 0 := hb' hij
      have hbA : b' = A * w'⁻¹ := by rw [hAw, mul_inv_cancel_right]
      have e : ∑ l : {i // i ≠ i0}, (h * u1 * u2).val i l * V.val l j = (A * w'⁻¹).val ⟨i, hi⟩ ⟨j, hj⟩ := by
        rw [show (A * w'⁻¹).val = A.val * (w'⁻¹).val from Units.val_mul _ _, Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hA, ← hV3]
      rw [e, ← hbA]
      exact hb
end GlobalTheory.SplitWeil
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.SplitWeil
namespace GlobalTheory.SplitWeil
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (lv : ι → ℕ) (h : GL ι k),
    ∃ (b : GL ι k), b.val.BlockTriangular lv ∧ ∃ w ∈ KO k ι, h = b * w := by
  intro k _ _ _ _ ι _ _ lv h
  exact exists_blockTriangular_mul_mem_KO_eq _ ι rfl lv h
end GlobalTheory.SplitWeil
