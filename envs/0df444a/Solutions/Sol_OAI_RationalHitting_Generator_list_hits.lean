-- Prove2me | solution 1 for OAI.RationalHitting.Generator.list_hits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:18:02.513748+00:00
-- url     : https://prove2.me/submissions/86db2175-234e-420e-9a80-a7ef5473b322

import Mathlib
import Definitions.Def_RationalHitting
import Definitions.Def_OAIQWRHT003

section
-- module Solutions.OAIQW_RationalHitting.Evaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting

namespace Formula
variable {n : ℕ} {R S : Type*} [Ring R] [Ring S]

lemma Eval.unique {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a b : R}
    (ha : Eval c X h a) (hb : Eval c X h b) : a = b := by
  induction ha generalizing b with
  | var i => cases hb; rfl
  | const a => cases hb; rfl
  | add hf hg ihf ihg => cases hb with
    | add hf' hg' => rw [ihf hf', ihg hg']
  | mul hf hg ihf ihg => cases hb with
    | mul hf' hg' => rw [ihf hf', ihg hg']
  | @inv h a v ha hav hva ih =>
    cases hb with
    | @inv _ a' w ha' haw hwa =>
      have heq := ih ha'
      subst a'
      calc
        v = v * 1 := (mul_one _).symm
        _ = v * (a*b) := by rw [haw]
        _ = b := by rw [← mul_assoc, hva, one_mul]

lemma Eval.map {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a : R}
    (ha : Eval c X h a) (f : R →+* S) :
    Eval (f.comp c) (fun i => f (X i)) h (f a) := by
  induction ha with
  | var i => exact .var i
  | const a => exact .const a
  | add _ _ ihf ihg => simpa only [map_add] using Eval.add ihf ihg
  | mul _ _ ihf ihg => simpa only [map_mul] using Eval.mul ihf ihg
  | inv ha hab hba ih =>
    exact .inv ih (by rw [← map_mul, hab, map_one]) (by rw [← map_mul, hba, map_one])

/-- Defined evaluations lift through a homomorphism reflecting units. In
particular this handles every inverse occurrence before considering the root. -/
lemma Eval.lift (f : R →+* S) (hf : ∀ x, IsUnit (f x) → IsUnit x)
    {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a : S}
    (ha : Eval (f.comp c) (fun i => f (X i)) h a) :
    ∃ b : R, Eval c X h b ∧ f b = a := by
  induction ha with
  | var i => exact ⟨X i, .var i, rfl⟩
  | const a => exact ⟨c a, .const a, rfl⟩
  | add ha hb iha ihb =>
    obtain ⟨a',ha',ea⟩ := iha
    obtain ⟨b',hb',eb⟩ := ihb
    exact ⟨a'+b', .add ha' hb', by rw [map_add,ea,eb]⟩
  | mul ha hb iha ihb =>
    obtain ⟨a',ha',ea⟩ := iha
    obtain ⟨b',hb',eb⟩ := ihb
    exact ⟨a'*b', .mul ha' hb', by rw [map_mul,ea,eb]⟩
  | @inv h a b ha hab hba ih =>
    obtain ⟨a',ha',ea⟩ := ih
    have hau : IsUnit (f a') := ea ▸ ⟨⟨a,b,hab,hba⟩,rfl⟩
    obtain ⟨u,hu⟩ := hf a' hau
    have heval : Eval c X (.inv h) (↑u⁻¹ : R) :=
      .inv ha' (by rw [← hu]; exact u.mul_inv) (by rw [← hu]; exact u.inv_mul)
    refine ⟨_,heval,?_⟩
    exact (heval.map f).unique (.inv ha hab hba)

/-- Mapping a defined nonzero value out of a division ring makes it a unit.
This is used after the partial-specialization domain proof, not instead of it. -/
lemma Eval.unit_of_division_lift {D : Type*} [DivisionRing D] [Nontrivial R]
    (f : D →+* R) {c : ℚ →+* D} {X : Fin n → D} {h : Formula n} {a : R}
    (ha : Eval (f.comp c) (fun i => f (X i)) h a) (ha0 : a ≠ 0) : IsUnit a := by
  have hf : ∀ x, IsUnit (f x) → IsUnit x := by
    intro x hx
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    exact hx.ne_zero (by rw [hzero,map_zero])
  obtain ⟨b,hb,heq⟩ := ha.lift f hf
  have hb0 : b ≠ 0 := by intro h; apply ha0; rw [← heq,h,map_zero]
  exact heq ▸ (isUnit_iff_ne_zero.mpr hb0).map f

end Formula
end RationalHitting


namespace RationalHitting.NoncommBlocks
open Matrix
variable {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

lemma upper_unit (B : Matrix ι κ R) : IsUnit (fromBlocks (1 : Matrix ι ι R) B 0 (1 : Matrix κ κ R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 (-B) 0 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

lemma lower_unit (C : Matrix κ ι R) : IsUnit (fromBlocks (1 : Matrix ι ι R) 0 C (1 : Matrix κ κ R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 0 (-C) 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

lemma diag_unit_iff (A : Matrix ι ι R) (D : Matrix κ κ R) :
    IsUnit (fromBlocks A 0 0 D) ↔ IsUnit A ∧ IsUnit D := by
  constructor
  · rintro ⟨u,hu⟩
    have hh := u.val_inv
    have hh' := u.inv_val
    rw [hu] at hh hh'
    refine ⟨isUnit_iff_exists.mpr ⟨(↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₁₁, ?_, ?_⟩,
      isUnit_iff_exists.mpr ⟨(↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₂₂, ?_, ?_⟩⟩
    · have h := congrArg Matrix.toBlocks₁₁ hh
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₁₁ hh'
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₂₂ hh
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₂₂ hh'
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
  · rintro ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩
    apply isUnit_iff_exists.mpr
    refine ⟨fromBlocks (↑u⁻¹) 0 0 (↑v⁻¹), ?_, ?_⟩ <;> simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

lemma schur_factor (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    fromBlocks A B C 0 =
      fromBlocks 1 0 (C * A') 1 * fromBlocks A 0 0 (-C * A' * B) *
      fromBlocks 1 (A' * B) 0 1 := by
  simp only [fromBlocks_multiply, add_zero, zero_add,
    one_mul, mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc A A' B, hAA', Matrix.one_mul, Matrix.mul_assoc C A' A, hA'A, Matrix.mul_one]
  simp [Matrix.mul_assoc, Matrix.neg_mul]

lemma schur_unit_iff (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    IsUnit (fromBlocks A B C 0) ↔ IsUnit (C * A' * B) := by
  rw [schur_factor A A' B C hAA' hA'A]
  obtain ⟨u,hu⟩ := upper_unit (A' * B)
  obtain ⟨v,hv⟩ := lower_unit (C * A')
  rw [← hu, ← hv, Units.isUnit_mul_units, Units.isUnit_units_mul]
  rw [diag_unit_iff]
  have hA : IsUnit A := isUnit_iff_exists.mpr ⟨A',hAA',hA'A⟩
  simp [hA, Matrix.neg_mul, IsUnit.neg_iff]


lemma schur_inverse (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (a b : Matrix κ κ R) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (ha : C * A' * B = a) (hab : a*b=1) (hba : b*a=1) :
    ∃ M : Matrix (ι ⊕ κ) (ι ⊕ κ) R,
      fromBlocks A B C 0 * M = 1 ∧ M * fromBlocks A B C 0 = 1 ∧
      matMul (matMul (fromCols (0 : Matrix κ ι R) (-1)) M)
        (fromRows (0 : Matrix ι κ R) (1 : Matrix κ κ R)) = b := by
  let U : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks 1 0 (C*A') 1, fromBlocks 1 0 (-(C*A')) 1,
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]⟩
  let V : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks 1 (A'*B) 0 1, fromBlocks 1 (-(A'*B)) 0 1,
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]⟩
  let D : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks A 0 0 (-a), fromBlocks A' 0 0 (-b),
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,hAA',hab],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,hA'A,hba]⟩
  have hS : (↑(U*D*V) : Matrix (ι ⊕ κ) (ι ⊕ κ) R) = fromBlocks A B C 0 := by
    change fromBlocks 1 0 (C*A') 1 * fromBlocks A 0 0 (-a) *
      fromBlocks 1 (A'*B) 0 1 = _
    rw [← ha]
    simpa [Matrix.neg_mul] using (schur_factor A A' B C hAA' hA'A).symm
  refine ⟨↑(U*D*V)⁻¹, ?_, ?_, ?_⟩
  · rw [← hS]; exact (U*D*V).mul_inv
  · rw [← hS]; exact (U*D*V).inv_mul
  · change matMul (matMul (fromCols (0 : Matrix κ ι R) (-1))
      (V.inv * (D.inv * U.inv))) (fromRows (0 : Matrix ι κ R) (1 : Matrix κ κ R)) = b
    simp [matMul,V,D,U,fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,
      Matrix.fromCols_mul_fromBlocks,fromCols_mul_fromRows,
      Matrix.mul_assoc,Matrix.neg_mul,Matrix.mul_neg]

end RationalHitting.NoncommBlocks

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Affine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting
open Matrix

namespace Formula
noncomputable section
variable {n : ℕ}

lemma card_index (f : Formula n) : Fintype.card f.Index = f.size + 1 := by
  induction f with
  | var i =>
    change Fintype.card (Unit ⊕ Unit) = 2
    exact (Fintype.card_sum (α := Unit) (β := Unit)).trans rfl
  | const a =>
    change Fintype.card (Unit ⊕ Unit) = 2
    exact (Fintype.card_sum (α := Unit) (β := Unit)).trans rfl
  | add f g ihf ihg =>
    change Fintype.card (Index f ⊕ Index g) = f.size + g.size + 1 + 1
    rw [Fintype.card_sum,ihf,ihg]
    omega
  | mul f g ihf ihg =>
    change Fintype.card (Index f ⊕ Index g) = f.size + g.size + 1 + 1
    rw [Fintype.card_sum,ihf,ihg]
    omega
  | inv f ih =>
    change Fintype.card (Index f ⊕ Unit) = f.size + 1 + 1
    rw [Fintype.card_sum,ih,Fintype.card_unique]

variable {R : Type*} [Ring R] (c : ℚ →+* R) (X : Fin n → R)

lemma leaf_realization (a : R) :
    ∃ M : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) R,
      fromBlocks 1 (-scalar a) 0 1 * M = 1 ∧
      M * fromBlocks 1 (-scalar a) 0 1 = 1 ∧
      NoncommBlocks.matMul (NoncommBlocks.matMul (fromCols (1 : Matrix Unit Unit R) 0) M)
        (fromRows (0 : Matrix Unit Unit R) (1 : Matrix Unit Unit R)) = scalar a := by
  refine ⟨fromBlocks 1 (scalar a) 0 1, ?_, ?_, ?_⟩
  · simp [fromBlocks_multiply]
  · simp [fromBlocks_multiply]
  · dsimp only [NoncommBlocks.matMul]
    rw [fromCols_mul_fromBlocks,fromCols_mul_fromRows]
    simp

/-- Exact affine realization of every defined original subtree. -/
theorem Eval.realization {f : Formula n} {a : R} (ha : Eval c X f a) :
    ∃ M : Matrix f.Index f.Index R,
      realized c X f * M = 1 ∧ M * realized c X f = 1 ∧
      rowR c f * M * colR c f = scalar a := by
  induction ha with
  | var i =>
    have hL : realized c X (.var i) = fromBlocks 1 (-scalar (X i)) 0 1 := by
      change (fromBlocks (Affine.constMatrix (1 : Matrix Unit Unit ℚ))
        (Matrix.of (fun _ _ => -Affine.varForm i)) 0 (Affine.constMatrix 1)).map (Affine.eval c X) = _
      rw [fromBlocks_map]
      simp only [Affine.eval_constMatrix, Matrix.map_one c (map_zero c) (map_one c), Matrix.map_zero, map_zero]
      congr 1 ; ext i j ; simp [scalar,Matrix.map,Matrix.of_apply]
    have hu : rowR c (.var i) = fromCols 1 0 := by
      change (fromCols (1 : Matrix Unit Unit ℚ) 0).map c = _
      rw [fromCols_map]; simp
    have hv : colR c (.var i) = fromRows 0 1 := by
      change (fromRows 0 (1 : Matrix Unit Unit ℚ)).map c = _
      rw [fromRows_map]; simp
    rw [hL,hu,hv]
    exact leaf_realization (X i)
  | const a =>
    have hL : realized c X (.const a) = fromBlocks 1 (-scalar (c a)) 0 1 := by
      change (fromBlocks (Affine.constMatrix (1 : Matrix Unit Unit ℚ))
        (Matrix.of (fun _ _ => -Affine.constant a)) 0 (Affine.constMatrix 1)).map (Affine.eval c X) = _
      rw [fromBlocks_map]
      simp only [Affine.eval_constMatrix, Matrix.map_one c (map_zero c) (map_one c), Matrix.map_zero, map_zero]
      congr 1 ; ext i j ; simp [scalar,Matrix.map,Matrix.of_apply]
    have hu : rowR (n := n) c (.const a) = fromCols 1 0 := by
      change (fromCols (1 : Matrix Unit Unit ℚ) 0).map c = _
      rw [fromCols_map]; simp
    have hv : colR (n := n) c (.const a) = fromRows 0 1 := by
      change (fromRows 0 (1 : Matrix Unit Unit ℚ)).map c = _
      rw [fromRows_map]; simp
    rw [hL,hu,hv]
    exact leaf_realization (c a)
  | @add f g a b hf hg ihf ihg =>
    obtain ⟨Mf,hf1,hf2,hfr⟩ := ihf
    obtain ⟨Mg,hg1,hg2,hgr⟩ := ihg
    refine ⟨fromBlocks Mf 0 0 Mg, ?_, ?_, ?_⟩
    · rw [realized_add,fromBlocks_multiply]
      simp [hf1,hg1,Matrix.mul_zero,Matrix.zero_mul]
    · rw [realized_add,fromBlocks_multiply]
      simp [hf2,hg2,Matrix.mul_zero,Matrix.zero_mul]
    · rw [rowR_add,colR_add,fromCols_mul_fromBlocks,fromCols_mul_fromRows]
      simp only [Matrix.mul_zero,add_zero,zero_add,hfr,hgr]
      exact (map_add (Matrix.uniqueRingEquiv (m := Unit)).symm a b).symm
  | @mul f g a b hf hg ihf ihg =>
    obtain ⟨Mf,hf1,hf2,hfr⟩ := ihf
    obtain ⟨Mg,hg1,hg2,hgr⟩ := ihg
    let B := Mf * colR c f * rowR c g * Mg
    have hB1 : realized c X f * B = colR c f * rowR c g * Mg := by
      simp [B,← Matrix.mul_assoc,hf1,Matrix.one_mul]
    have hB2 : B * realized c X g = Mf * colR c f * rowR c g := by
      simp [B,Matrix.mul_assoc,hg2,Matrix.mul_one]
    refine ⟨fromBlocks Mf B 0 Mg, ?_, ?_, ?_⟩
    · rw [realized_mul,fromBlocks_multiply]
      simp [hf1,hg1,hB1,Matrix.mul_zero,Matrix.zero_mul,Matrix.neg_mul]
    · rw [realized_mul,fromBlocks_multiply]
      simp [hf2,hg2,hB2,Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_neg,Matrix.neg_mul,← Matrix.mul_assoc]
    · rw [rowR_mul,colR_mul,fromCols_mul_fromBlocks,fromCols_mul_fromRows]
      simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
      simp only [B]
      have hh : rowR c f * (Mf * colR c f * rowR c g * Mg) * colR c g =
          (rowR c f * Mf * colR c f) * (rowR c g * Mg * colR c g) := by
        simp only [Matrix.mul_assoc]
      rw [hh,hfr,hgr]
      exact (map_mul (Matrix.uniqueRingEquiv (m := Unit)).symm a b).symm
  | @inv f a b hf hab hba ih =>
    obtain ⟨Mf,hf1,hf2,hfr⟩ := ih
    rw [realized_inv,rowR_inv,colR_inv]
    exact NoncommBlocks.schur_inverse _ _ _ _ (scalar a) (scalar b)
      hf1 hf2 hfr (by rw [← map_mul,hab,map_one]) (by rw [← map_mul,hba,map_one])

end
end Formula
end RationalHitting

namespace RationalHitting.Formula
open Matrix
noncomputable section
variable {n : ℕ} {R : Type*} [Ring R]
variable (c : ℚ →+* R) (X : Fin n → R)

lemma Eval.pencil_isUnit {f : Formula n} {a : R} (ha : Eval c X f a) :
    IsUnit (realized c X f) := by
  obtain ⟨M,hM,hM',_⟩ := ha.realization
  exact isUnit_iff_exists.mpr ⟨M,hM,hM'⟩

lemma Eval.augmented_isUnit_iff {f : Formula n} {a : R} (ha : Eval c X f a) :
    IsUnit (realized c X (.inv f)) ↔ IsUnit a := by
  obtain ⟨M,hM,hM',hr⟩ := ha.realization
  rw [realized_inv,NoncommBlocks.schur_unit_iff _ _ _ _ hM hM',hr]
  constructor
  · intro h; simpa using h.map (Matrix.uniqueRingEquiv (m := Unit))
  · intro h; exact h.map (Matrix.uniqueRingEquiv (m := Unit)).symm

lemma Eval.inverseNodes_units {f : Formula n} {a : R} (ha : Eval c X f a) :
    ∀ h ∈ inverseNodes f, IsUnit (realized c X h) := by
  induction ha with
  | var i => simp [inverseNodes]
  | const a => simp [inverseNodes]
  | add hf hg ihf ihg => simpa only [inverseNodes,List.mem_append,or_imp,forall_and] using And.intro ihf ihg
  | mul hf hg ihf ihg => simpa only [inverseNodes,List.mem_append,or_imp,forall_and] using And.intro ihf ihg
  | @inv f a b hf hab hba ih =>
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact (Eval.inv hf hab hba).pencil_isUnit
    · exact ih h hh

lemma eval_of_inverseNodes_units (f : Formula n)
    (hu : ∀ h ∈ inverseNodes f, IsUnit (realized c X h)) :
    ∃ a, Eval c X f a := by
  induction f with
  | var i => exact ⟨X i,.var i⟩
  | const a => exact ⟨c a,.const a⟩
  | add f g ihf ihg =>
    obtain ⟨a,ha⟩ := ihf (fun h hh => hu h (List.mem_append_left _ hh))
    obtain ⟨b,hb⟩ := ihg (fun h hh => hu h (List.mem_append_right _ hh))
    exact ⟨a+b,.add ha hb⟩
  | mul f g ihf ihg =>
    obtain ⟨a,ha⟩ := ihf (fun h hh => hu h (List.mem_append_left _ hh))
    obtain ⟨b,hb⟩ := ihg (fun h hh => hu h (List.mem_append_right _ hh))
    exact ⟨a*b,.mul ha hb⟩
  | inv f ih =>
    obtain ⟨a,ha⟩ := ih (fun h hh => hu h (List.mem_cons_of_mem _ hh))
    have hua := ha.augmented_isUnit_iff.mp (hu (.inv f) (List.mem_cons_self ..))
    obtain ⟨b,hab,hba⟩ := isUnit_iff_exists.mp hua
    exact ⟨b,.inv ha hab hba⟩

/-- Full original-tree definedness and invertible final value are equivalent to
all affine-pencil certificates. No rational cancellation is performed. -/
theorem certificates_iff (f : Formula n) :
    (∀ h ∈ certificates f, IsUnit (realized c X h)) ↔
      ∃ a, Eval c X f a ∧ IsUnit a := by
  constructor
  · intro hu
    obtain ⟨a,ha⟩ := eval_of_inverseNodes_units c X f
      (fun h hh => hu h (List.mem_append_left _ hh))
    exact ⟨a,ha,ha.augmented_isUnit_iff.mp (hu (.inv f) (by simp [certificates]))⟩
  · rintro ⟨a,ha,hua⟩ h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact Eval.inverseNodes_units c X ha h hh
    · have heq : h = .inv f := by simpa using hh
      subst h
      exact ha.augmented_isUnit_iff.mpr hua

lemma inverseNodes_length (f : Formula n) : (inverseNodes f).length ≤ f.size := by
  induction f <;> simp_all [inverseNodes,size] <;> omega

lemma size_le_of_mem_inverseNodes {f h : Formula n} (hh : h ∈ inverseNodes f) :
    h.size ≤ f.size := by
  induction f with
  | var i => simp [inverseNodes] at hh
  | const a => simp [inverseNodes] at hh
  | add f g ihf ihg =>
    rcases List.mem_append.mp hh with hh | hh
    · have := ihf hh; simp only [size]; omega
    · have := ihg hh; simp only [size]; omega
  | mul f g ihf ihg =>
    rcases List.mem_append.mp hh with hh | hh
    · have := ihf hh; simp only [size]; omega
    · have := ihg hh; simp only [size]; omega
  | inv f ih =>
    rcases List.mem_cons.mp hh with rfl | hh
    · rfl
    · have := ih hh; simp only [size]; omega

lemma certificate_bounds (f : Formula n) (s : ℕ) (hs : 1 ≤ s) (hf : f.size ≤ s) :
    (certificates f).length ≤ s+1 ∧
      ∀ h ∈ certificates f, 0 < Fintype.card h.Index ∧ Fintype.card h.Index ≤ 2*s+1 := by
  refine ⟨?_,?_⟩
  · simp only [certificates,List.length_append,List.length_singleton]
    have := inverseNodes_length f
    omega
  · intro h hh
    rw [card_index]
    refine ⟨by omega,?_⟩
    rcases List.mem_append.mp hh with hh | hh
    · have := size_le_of_mem_inverseNodes hh
      omega
    · have heq : h = .inv f := by simpa using hh
      rw [heq,size]
      omega

end
end RationalHitting.Formula

namespace RationalHitting.Affine
open Matrix
open scoped BigOperators
noncomputable section
variable {n : ℕ} {R : Type*} [Ring R]

lemma homogeneous_one (c : ℚ →+* R) (X : Fin n → R) (a : Form n) :
    homogeneous c (Fin.cases 1 X) a = eval c X a := by
  simp [homogeneous,coeff,Fin.sum_univ_succ,eval]

lemma normalized [Algebra ℚ R] (Z : Fin (n+1) → R) (u : R) (hu : Z 0*u=1)
    (a : Form n) :
    homogeneous (algebraMap ℚ R) Z a =
      Z 0 * eval (algebraMap ℚ R) (fun i => u * Z i.succ) a := by
  change (∑ i, (algebraMap ℚ R) (coeff a i) * Z i) =
    Z 0 * ((algebraMap ℚ R) a.1 + ∑ i, (algebraMap ℚ R) (a.2 i) * (u*Z i.succ))
  rw [Fin.sum_univ_succ]
  simp only [coeff,Fin.cases_zero,Fin.cases_succ,mul_add,Finset.mul_sum]
  congr 1
  · exact (Algebra.commutes a.1 (Z 0))
  · apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc,← (Algebra.commutes (a.2 i) (Z 0)),mul_assoc,
      ← mul_assoc (Z 0) u,hu,one_mul]

lemma normalized_pencil {ι : Type*} [Fintype ι] [DecidableEq ι] [Algebra ℚ R]
    (L : Matrix ι ι (Form n)) (Z : Fin (n+1) → R) (u : R) (hu : Z 0*u=1) :
    L.map (homogeneous (algebraMap ℚ R) Z) =
      Matrix.scalar ι (Z 0) * L.map (eval (algebraMap ℚ R) (fun i => u*Z i.succ)) := by
  funext i j
  change homogeneous (algebraMap ℚ R) Z (L i j) =
    (Matrix.diagonal (fun _ : ι => Z 0) * L.map (eval (algebraMap ℚ R) (fun i => u*Z i.succ)) : Matrix ι ι R) i j
  rw [Matrix.diagonal_mul]
  exact normalized Z u hu (L i j)

lemma normalized_pencil_unit {ι : Type*} [Fintype ι] [DecidableEq ι] [Algebra ℚ R]
    (L : Matrix ι ι (Form n)) (Z : Fin (n+1) → R) (z : Rˣ) (hz : (z : R)=Z 0)
    (hL : IsUnit (L.map (homogeneous (algebraMap ℚ R) Z))) :
    IsUnit (L.map (eval (algebraMap ℚ R) (fun i => (↑z⁻¹ : R)*Z i.succ))) := by
  have hu : Z 0*(↑z⁻¹ : R)=1 := by rw [← hz]; exact z.val_inv
  rw [normalized_pencil L Z (↑z⁻¹ : R) hu] at hL
  exact (z.isUnit.map (Matrix.scalar ι) |>.mul_left_iff).mp (by simpa [hz] using hL)

variable {K : Type*} [Field K] [CharZero K] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Homogeneous affine coefficients give exactly the ordinary Kronecker pencil. -/
lemma homogeneous_flat.{v_2, v_3, v_4} {n : ℕ} {K : Type v_2} [Field K]
  [CharZero K] {ι : Type v_3} {κ : Type v_4} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] (L : Matrix ι ι (RationalHitting.Affine.Form n))
  (Z : Fin (n + 1) → Matrix κ κ K) :
  (Matrix.compRingEquiv ι κ K)
      (L.map (RationalHitting.Affine.homogeneous (algebraMap ℚ (Matrix κ κ K)) Z)) =
    fun a b => ∑ r, (algebraMap ℚ K) (RationalHitting.Affine.coeff (L a.1 b.1) r) * Z r a.2 b.2 := by
  funext ⟨i,a⟩ ⟨j,b⟩
  change (∑ r, (algebraMap ℚ (Matrix κ κ K)) (coeff (L i j) r) * Z r) a b = _
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  change (Matrix.diagonal (fun _ : κ => (algebraMap ℚ K) (coeff (L i j) r)) * Z r : Matrix κ κ K) a b = _
  rw [Matrix.diagonal_mul]

end
end RationalHitting.Affine

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Wronskian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.Expansion
open Polynomial Module
open scoped BigOperators Polynomial

noncomputable section


/-- Factoring prescribed powers from the columns keeps track of the first
possible coefficient of a determinant. -/
lemma det_factor_column_orders {K ι : Type*} [CommRing K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K[X]) (d : ι → ℕ)
    (hd : ∀ i j, X ^ d j ∣ A i j) :
    ∃ B : Matrix ι ι K[X],
      A.det = X ^ (∑ j, d j) * B.det ∧
      (∀ i j, (B i j).coeff 0 = (A i j).coeff (d j)) := by
  classical
  choose B hB using hd
  refine ⟨Matrix.of B, ?_, ?_⟩
  · have hA : A = Matrix.of (fun i j => X ^ d j * (Matrix.of B) i j) := by
      apply Matrix.ext
      intro i j
      exact hB i j
    rw [hA, Matrix.det_mul_row, ← Finset.prod_pow_eq_pow_sum]
  · intro i j
    simp only [Matrix.of_apply]
    rw [hB i j, coeff_X_pow_mul']
    simp

lemma coeff_scaled_derivative_at {K : Type*} [CommRing K]
    (f : K[X]) (r d : ℕ) :
    (X ^ r * derivative^[r] f).coeff d =
      (d.descFactorial r : K) * f.coeff d := by
  by_cases hr : r ≤ d
  · rw [coeff_X_pow_mul', ite_eq_left hr, coeff_iterate_derivative,
      Nat.sub_add_cancel hr, nsmul_eq_mul]
  · rw [coeff_X_pow_mul', ite_eq_right hr,
      Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hr), Nat.cast_zero, zero_mul]

lemma scaled_derivative_order {K : Type*} [CommRing K]
    (f : K[X]) (r : ℕ) : X ^ f.natTrailingDegree ∣ X ^ r * derivative^[r] f := by
  apply X_pow_dvd_iff.mpr
  intro a ha
  rw [coeff_scaled_derivative_at, coeff_eq_zero_of_lt_natTrailingDegree ha, mul_zero]

/-- The local order formula at zero, before translation to an arbitrary point.
The sum of the row numbers is C(h,2). -/
lemma wronskian_order_of_distinct_orders {K : Type*} [Field K] [CharZero K]
    {h : ℕ} (f : Fin h → K[X]) (hf : ∀ j, f j ≠ 0)
    (hd : Function.Injective (fun j => (f j).natTrailingDegree)) :
    wronskian f ≠ 0 ∧
      (wronskian f).natTrailingDegree + (∑ i : Fin h, i.val) =
        ∑ j, (f j).natTrailingDegree := by
  let A : Matrix (Fin h) (Fin h) K[X] :=
    Matrix.of fun i j => X ^ i.val * derivative^[i.val] (f j)
  obtain ⟨B, hdet, hB⟩ := det_factor_column_orders A
    (fun j => (f j).natTrailingDegree) (fun i j => scaled_derivative_order (f j) i.val)
  have hfall : Matrix.det (Matrix.of fun i j : Fin h =>
      ((f j).natTrailingDegree.descFactorial i.val : K)) ≠ 0 := by
    let p : Fin h → K[X] := fun j => descPochhammer K j.val
    have hp := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun j : Fin h => ((f j).natTrailingDegree : K)) p
      (fun j => by simp [p]) (fun j => monic_descPochhammer K j.val)
    have he : (Matrix.of fun i j : Fin h =>
        ((f j).natTrailingDegree.descFactorial i.val : K)) =
        (Matrix.of fun i j : Fin h => (p j).eval ((f i).natTrailingDegree : K)).transpose := by
      ext i j
      simp [p, descPochhammer_eval_eq_descFactorial]
    rw [he, Matrix.det_transpose, ← hp, Matrix.det_vandermonde_ne_zero_iff]
    exact (Nat.cast_injective (R := K)).comp hd
  have hBc : B.det.coeff 0 ≠ 0 := by
    have he : B.map (evalRingHom (0 : K)) =
        Matrix.of (fun i j : Fin h => (f j).trailingCoeff *
          ((f j).natTrailingDegree.descFactorial i.val : K)) := by
      ext i j
      change eval (0 : K) (B i j) = _
      rw [← coeff_zero_eq_eval_zero, hB i j]
      change (X ^ i.val * derivative^[i.val] (f j)).coeff (f j).natTrailingDegree = _
      rw [coeff_scaled_derivative_at]
      exact mul_comm _ _
    rw [coeff_zero_eq_eval_zero]
    change (evalRingHom (0 : K)) B.det ≠ 0
    rw [RingHom.map_det]
    change (B.map (evalRingHom (0 : K))).det ≠ 0
    rw [he]
    have hscale := Matrix.det_mul_row (fun j => (f j).trailingCoeff)
      (Matrix.of fun i j : Fin h => ((f j).natTrailingDegree.descFactorial i.val : K))
    simp only [Matrix.of_apply] at hscale
    rw [hscale]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ =>
      trailingCoeff_nonzero_iff_nonzero.mpr (hf j)) hfall
  have hB0 : B.det ≠ 0 := by intro hz; simp [hz] at hBc
  have hA0 : A.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) hB0
  have hscale : A.det = X ^ (∑ i : Fin h, i.val) * wronskian f := by
    have he := Matrix.det_mul_column (fun i : Fin h => (X : K[X]) ^ i.val)
      (Matrix.of fun i j : Fin h => derivative^[i.val] (f j))
    simp only [Matrix.of_apply] at he
    change _ = _ * Matrix.det (Matrix.of fun i j : Fin h => derivative^[i.val] (f j))
    rw [← Finset.prod_pow_eq_pow_sum]
    exact he
  have hw : wronskian f ≠ 0 := by
    intro hz
    rw [hscale, hz, mul_zero] at hA0
    exact hA0 rfl
  refine ⟨hw, ?_⟩
  have ho : A.det.natTrailingDegree = ∑ j, (f j).natTrailingDegree := by
    rw [hdet, mul_comm, natTrailingDegree_mul_X_pow hB0,
      natTrailingDegree_eq_zero.mpr (Or.inr hBc), zero_add]
  rw [hscale, mul_comm, natTrailingDegree_mul_X_pow hw] at ho
  exact ho


/-- Polynomial row reduction, derived rather than assumed: every bounded-degree
subspace has a basis with distinct largest degrees. -/
lemma exists_degree_echelon_family {K : Type*} [Field K]
    (d : ℕ) (V : Submodule K K[X])
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    ∃ (h : ℕ) (f : Fin h → K[X]), LinearIndependent K f ∧
      Submodule.span K (Set.range f) = V ∧
      Function.Injective (fun i => (f i).natDegree) := by
  classical
  induction d generalizing V with
  | zero =>
    have hzero : V = ⊥ := by
      apply le_antisymm _ bot_le
      intro f hf
      change f = 0
      by_contra hn
      exact Nat.not_lt_zero _ (hV f hf hn)
    refine ⟨0, Fin.elim0, linearIndependent_empty_type, ?_, ?_⟩
    · simp [hzero]
    · intro i; exact Fin.elim0 i
  | succ d ih =>
    by_cases hall : ∀ f ∈ V, f.coeff d = 0
    · apply ih V
      intro f hf hn
      have hl := hV f hf hn
      have hne : f.natDegree ≠ d := by
        intro he
        have hc := hall f hf
        rw [← he, coeff_natDegree] at hc
        exact (leadingCoeff_ne_zero.mpr hn) hc
      omega
    · push Not at hall
      obtain ⟨f, hfV, hfc⟩ := hall
      have hf0 : f ≠ 0 := by intro hz; simp [hz] at hfc
      have hfd : f.natDegree = d := by
        have hl := hV f hfV hf0
        have hr := le_natDegree_of_ne_zero hfc
        omega
      let W : Submodule K K[X] := V ⊓ LinearMap.ker (lcoeff K d)
      have hW : ∀ g ∈ W, g ≠ 0 → g.natDegree < d := by
        intro g hg hn
        have hl := hV g hg.1 hn
        have hc : g.coeff d = 0 := hg.2
        have hne : g.natDegree ≠ d := by
          intro he
          rw [← he, coeff_natDegree] at hc
          exact (leadingCoeff_ne_zero.mpr hn) hc
        omega
      obtain ⟨h, g, hgLI, hgspan, hgdeg⟩ := ih W hW
      have hgmem : ∀ j, g j ∈ W := by
        intro j
        rw [← hgspan]
        exact Submodule.subset_span ⟨j, rfl⟩
      have hnot : f ∉ Submodule.span K (Set.range g) := by
        rw [hgspan]
        exact fun hh => hfc hh.2
      refine ⟨h + 1, Fin.cons f g, hgLI.finCons hnot, ?_, ?_⟩
      · apply le_antisymm
        · apply Submodule.span_le.mpr
          rintro _ ⟨j, rfl⟩
          refine Fin.cases ?_ (fun i => ?_) j
          · exact hfV
          · exact (hgmem i).1
        · intro u hu
          let c : K := u.coeff d / f.coeff d
          have hr : u - c • f ∈ W := by
            refine ⟨V.sub_mem hu (V.smul_mem c hfV), ?_⟩
            change (u - c • f).coeff d = 0
            simp [c, coeff_sub, coeff_smul, div_mul_cancel₀ _ hfc]
          have hsub : W ≤ Submodule.span K (Set.range (Fin.cons f g)) := by
            rw [← hgspan]
            apply Submodule.span_mono
            rw [Fin.range_cons]
            exact Set.subset_insert f _
          have hfj : f ∈ Submodule.span K (Set.range (Fin.cons f g)) :=
            Submodule.subset_span ⟨0, by simp⟩
          have hh := (Submodule.span K (Set.range (Fin.cons f g))).add_mem
            (hsub hr) ((Submodule.span K (Set.range (Fin.cons f g))).smul_mem c hfj)
          simpa only [sub_add_cancel] using hh
      · have he : (fun i => ((Fin.cons f g : Fin (h + 1) → K[X]) i).natDegree) =
            Fin.cons f.natDegree (fun i => (g i).natDegree) := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        rw [he]
        apply Fin.cons_injective_of_injective ?_ hgdeg
        rintro ⟨j, hj⟩
        change (g j).natDegree = f.natDegree at hj
        have hh := hW (g j) (hgmem j) (hgLI.ne_zero j)
        rw [hfd] at hj
        omega


lemma order_reflect {K : Type*} [Field K] (N : ℕ) (f : K[X])
    (hf : f ≠ 0) (hd : f.natDegree ≤ N) :
    (reflect N f).natTrailingDegree = N - f.natDegree := by
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [coeff_reflect, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hf
  · apply le_natTrailingDegree (reflect_eq_zero_iff.not.mpr hf)
    intro j hj
    rw [coeff_reflect, revAt_le (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

lemma exists_order_echelon_family {K : Type*} [Field K]
    (d : ℕ) (V : Submodule K K[X])
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    ∃ (h : ℕ) (f : Fin h → K[X]), LinearIndependent K f ∧
      Submodule.span K (Set.range f) = V ∧
      Function.Injective (fun i => (f i).natTrailingDegree) := by
  classical
  let e := reflectLinearEquiv K (d - 1)
  let W := V.map e.toLinearMap
  have hW : ∀ g ∈ W, g ≠ 0 → g.natDegree < d := by
    rintro g ⟨f, hfV, rfl⟩ hfn
    have hf : f ≠ 0 := by intro hz; simp [hz] at hfn
    have hd := hV f hfV hf
    have he := natDegree_reflect_le (N := d - 1) (p := f)
    change (reflect (d - 1) f).natDegree < d
    omega
  obtain ⟨h, g, hgLI, hgspan, hgdeg⟩ := exists_degree_echelon_family d W hW
  have hgW : ∀ i, g i ∈ W := by
    intro i
    rw [← hgspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨h, fun i => e.symm (g i), hgLI.map' e.symm.toLinearMap (by simp), ?_, ?_⟩
  · have hs : Submodule.span K (Set.range (fun i => e.symm (g i))) =
        (Submodule.span K (Set.range g)).map e.symm.toLinearMap := by
      rw [Submodule.map_span]
      congr 1
      exact Set.range_comp _ _
    rw [hs, hgspan, ← Submodule.map_comp]
    change (V.map (e.symm.toLinearMap.comp e.toLinearMap)) = V
    simp
  · intro i j hij
    change (reflect (d - 1) (g i)).natTrailingDegree =
      (reflect (d - 1) (g j)).natTrailingDegree at hij
    have hi := hW (g i) (hgW i) (hgLI.ne_zero i)
    have hj := hW (g j) (hgW j) (hgLI.ne_zero j)
    rw [order_reflect _ _ (hgLI.ne_zero i) (by omega),
      order_reflect _ _ (hgLI.ne_zero j) (by omega)] at hij
    apply hgdeg
    change (g i).natDegree = (g j).natDegree
    omega


lemma wronskian_linearCombination {K : Type*} [CommRing K] {h : ℕ}
    (f : Fin h → K[X]) (A : Matrix (Fin h) (Fin h) K) :
    wronskian (fun j => ∑ i, A i j • f i) = wronskian f * C A.det := by
  have he : (Matrix.of fun r j : Fin h =>
        derivative^[r.val] (∑ i, A i j • f i)) =
      (Matrix.of fun r i : Fin h => derivative^[r.val] (f i)) * A.map C := by
    apply Matrix.ext
    intro r j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
    calc
      derivative^[r.val] (∑ i, A i j • f i) =
          ∑ i, derivative^[r.val] (A i j • f i) := by
            simp only [← Module.End.pow_apply, map_sum]
      _ = _ := by
        simp only [iterate_derivative_smul]
        simp only [smul_eq_C_mul, mul_comm]
  unfold wronskian
  rw [he, Matrix.det_mul]
  congr 1
  exact (C.map_det A).symm

lemma basis_toMatrix_det_ne_zero {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {h : ℕ} (b b' : Basis (Fin h) K M) :
    (b.toMatrix b').det ≠ 0 := by
  have hh := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip b')
  rw [Matrix.det_mul, Matrix.det_one] at hh
  exact left_ne_zero_of_mul_eq_one hh

lemma wronskian_basis_change {K : Type*} [Field K] {h : ℕ}
    {V : Submodule K K[X]} (b b' : Basis (Fin h) K V) :
    wronskian (fun j => (b' j : K[X])) =
      wronskian (fun j => (b j : K[X])) * C (b.toMatrix b').det := by
  have he : (fun j => (b' j : K[X])) =
      (fun j => ∑ i, b.toMatrix b' i j • (b i : K[X])) := by
    funext j
    have hh := congrArg (fun v : V => (v : K[X])) (b.sum_repr (b' j))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Basis.toMatrix_apply] using hh.symm
  rw [he, wronskian_linearCombination]

lemma exists_order_echelon_basis {K : Type*} [Field K]
    (d : ℕ) (V : Submodule K K[X]) {h : ℕ} (b : Basis (Fin h) K V)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    ∃ b' : Basis (Fin h) K V,
      Function.Injective (fun j => (b' j : K[X]).natTrailingDegree) := by
  obtain ⟨k, f, hLI, hspan, hord⟩ := exists_order_echelon_family d V hV
  let b' : Basis (Fin k) K V := (Basis.span hLI).map (LinearEquiv.ofEq _ _ hspan)
  have hb' : ∀ j, (b' j : K[X]) = f j := by
    intro j
    simp only [b', Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  have hk : k = h := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 := Module.finrank_eq_card_basis b'
    simp only [Fintype.card_fin] at h1 h2
    omega
  subst k
  exact ⟨b', by simpa only [hb'] using hord⟩

lemma wronskian_basis_ne_zero {K : Type*} [Field K] [CharZero K]
    (d : ℕ) {V : Submodule K K[X]} {h : ℕ} (b : Basis (Fin h) K V)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    wronskian (fun j => (b j : K[X])) ≠ 0 := by
  obtain ⟨b', hord⟩ := exists_order_echelon_basis d V b hV
  have hne : ∀ j, (b' j : K[X]) ≠ 0 := by
    intro j hz
    exact b'.ne_zero j (Subtype.ext hz)
  have hn := (wronskian_order_of_distinct_orders _ hne hord).1
  rw [wronskian_basis_change b b'] at hn
  exact (mul_ne_zero_iff.mp hn).1

lemma derivative_taylor {K : Type*} [CommRing K] (a : K) (f : K[X]) :
    derivative (taylor a f) = taylor a (derivative f) := by
  simp only [taylor_apply, derivative_comp, derivative_add, derivative_X,
    derivative_C, add_zero, one_mul]

lemma iterate_derivative_taylor {K : Type*} [CommRing K] (a : K)
    (f : K[X]) (r : ℕ) :
    derivative^[r] (taylor a f) = taylor a (derivative^[r] f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, derivative_taylor, Function.iterate_succ_apply']

lemma wronskian_taylor {K : Type*} [CommRing K] {h : ℕ}
    (a : K) (f : Fin h → K[X]) :
    wronskian (fun j => taylor a (f j)) = taylor a (wronskian f) := by
  unfold wronskian
  have he : (Matrix.of fun i j : Fin h => derivative^[i.val] (taylor a (f j))) =
      (Matrix.of fun i j : Fin h => derivative^[i.val] (f j)).map (taylorEquiv a) := by
    apply Matrix.ext
    intro i j
    exact iterate_derivative_taylor a (f j) i.val
  rw [he]
  exact ((taylorEquiv a).toRingHom.map_det _).symm

lemma natDegree_wronskian_le {K : Type*} [CommRing K] {h : ℕ}
    (f : Fin h → K[X]) (D : ℕ) (hd : ∀ j, (f j).natDegree ≤ D) :
    (wronskian f).natDegree ≤ h * D := by
  unfold wronskian
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro g _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    ∑ j : Fin h, (derivative^[(g j).val] (f j)).natDegree
        ≤ ∑ _j : Fin h, D := Finset.sum_le_sum fun j _ =>
          (natDegree_iterate_derivative _ _).trans ((Nat.sub_le _ _).trans (hd j))
    _ = h * D := by simp

lemma sum_rootMultiplicity_le_natDegree {K : Type*} [Field K]
    (f : K[X]) (s : Finset K) :
    ∑ a ∈ s, f.rootMultiplicity a ≤ f.natDegree := by
  classical
  simp only [← count_roots]
  calc
    ∑ a ∈ s, f.roots.count a ≤ ∑ a ∈ s ∪ f.roots.toFinset, f.roots.count a :=
      Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = f.roots.card := Multiset.sum_count_eq_card (fun a ha =>
      Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ f.natDegree := card_roots' f


lemma wronskian_order_at {K : Type*} [Field K] [CharZero K] {h : ℕ}
    (a : K) (f : Fin h → K[X]) (hf : ∀ j, f j ≠ 0)
    (hd : Function.Injective (fun j => (f j).rootMultiplicity a)) :
    (wronskian f).rootMultiplicity a + (∑ i : Fin h, i.val) =
      ∑ j, (f j).rootMultiplicity a := by
  have hn : ∀ j, taylor a (f j) ≠ 0 := by
    intro j hz
    exact hf j ((taylorEquiv a).injective (by simpa using hz))
  have ho : Function.Injective (fun j => (taylor a (f j)).natTrailingDegree) := by
    simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using hd
  have hh := (wronskian_order_of_distinct_orders _ hn ho).2
  rw [wronskian_taylor] at hh
  simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using hh

lemma wronskian_basis_rootMultiplicity {K : Type*} [Field K] [CharZero K]
    (d : ℕ) {V : Submodule K K[X]} {h : ℕ}
    (b b' : Basis (Fin h) K V) (a : K)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    (wronskian (fun j => (b' j : K[X]))).rootMultiplicity a =
      (wronskian (fun j => (b j : K[X]))).rootMultiplicity a := by
  rw [wronskian_basis_change b b', rootMultiplicity_mul
    (mul_ne_zero (wronskian_basis_ne_zero d b hV)
      (C_ne_zero.mpr (basis_toMatrix_det_ne_zero b b'))), rootMultiplicity_C, add_zero]

/-- The Wronskian order bound for distinct points of a characteristic-zero
field and order-echelon bases. The triangular sum is exactly binom(h,2). -/

theorem wronskian_order_bound {K : Type*} [Field K] [CharZero K]
    (d : ℕ) {V : Submodule K K[X]} {h w : ℕ}
    (b : Basis (Fin h) K V) (a : Fin w → K) (ha : Function.Injective a)
    (e : Fin w → Basis (Fin h) K V)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d)
    (he : ∀ i, Function.Injective (fun j => (e i j : K[X]).rootMultiplicity (a i))) :
    ∑ i, ∑ j, (e i j : K[X]).rootMultiplicity (a i) ≤
      h * (d - 1) + w * (∑ j : Fin h, j.val) := by
  classical
  have localOrder : ∀ i, ∑ j, (e i j : K[X]).rootMultiplicity (a i) =
      (wronskian (fun j => (b j : K[X]))).rootMultiplicity (a i) +
        (∑ j : Fin h, j.val) := by
    intro i
    rw [← wronskian_order_at (a i) _ (fun j hz => (e i).ne_zero j (Subtype.ext hz)) (he i),
      wronskian_basis_rootMultiplicity d b (e i) (a i) hV]
  simp_rw [localOrder]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  apply Nat.add_le_add_right
  let W := wronskian (fun j => (b j : K[X]))
  have hsum : (∑ i, W.rootMultiplicity (a i)) =
      ∑ x ∈ Finset.univ.image a, W.rootMultiplicity x := by
    rw [Finset.sum_image]
    exact fun i _ j _ hij => ha hij
  rw [hsum]
  apply (sum_rootMultiplicity_le_natDegree W _).trans
  apply natDegree_wronskian_le
  intro j
  have hh := hV (b j) (b j).property (fun hz => b.ne_zero j (Subtype.ext hz))
  omega


lemma exists_echelon_basis_at {K : Type*} [Field K]
    (d : ℕ) (V : Submodule K K[X]) {h : ℕ} (b : Basis (Fin h) K V)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) (a : K) :
    ∃ b' : Basis (Fin h) K V,
      Function.Injective (fun j => (b' j : K[X]).rootMultiplicity a) := by
  let e := (taylorEquiv a).toLinearEquiv
  let W := V.map e.toLinearMap
  let eV : V ≃ₗ[K] W := e.submoduleMap V
  have hW : ∀ f ∈ W, f ≠ 0 → f.natDegree < d := by
    rintro g ⟨f, hfV, rfl⟩ hne
    have hf : f ≠ 0 := by intro hz; simp [hz] at hne
    change (taylor a f).natDegree < d
    rw [natDegree_taylor]
    exact hV f hfV hf
  obtain ⟨c, hc⟩ := exists_order_echelon_basis d W (b.map eV) hW
  refine ⟨c.map eV.symm, ?_⟩
  have ht : ∀ j, taylor a ((c.map eV.symm) j : K[X]) = (c j : K[X]) := by
    intro j
    rw [Basis.map_apply]
    change e (e.symm (c j : K[X])) = (c j : K[X])
    exact e.apply_symm_apply _
  intro i j hij
  apply hc
  simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply, ht] using hij

/-- Distinct leading orders make vanishing conditions triangular; no linear
combination can cancel its first nonzero echelon term. -/
lemma low_coefficients_force_zero {K : Type*} [Field K] {h : ℕ}
    (f : Fin h → K[X]) (hf : ∀ j, f j ≠ 0)
    (hd : Function.Injective (fun j => (f j).natTrailingDegree))
    (c : Fin h → K) (r : ℕ)
    (hz : ∀ m < r, (∑ j, c j • f j).coeff m = 0) :
    ∀ j, (f j).natTrailingDegree < r → c j = 0 := by
  classical
  have hi : ∀ m, ∀ j, (f j).natTrailingDegree = m → m < r → c j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j hj hmr
      have hs : (∑ k, c k • f k).coeff m = c j * (f j).coeff m := by
        simp only [finsetSum_coeff, coeff_smul, smul_eq_mul]
        apply Finset.sum_eq_single j
        · intro k _ hkj
          by_cases hk : (f k).natTrailingDegree < m
          · rw [ih _ hk k rfl (hk.trans hmr), zero_mul]
          · rw [coeff_eq_zero_of_lt_natTrailingDegree (show m < (f k).natTrailingDegree by
              have hn : (f k).natTrailingDegree ≠ m := by
                intro hh
                exact hkj (hd (hh.trans hj.symm))
              omega), mul_zero]
        · intro hh
          exact (hh (Finset.mem_univ j)).elim
      have htc : (f j).coeff m ≠ 0 := by
        rw [← hj]
        change (f j).trailingCoeff ≠ 0
        exact mt trailingCoeff_eq_zero.mp (hf j)
      exact (mul_eq_zero.mp ((hs.symm.trans (hz m hmr)))).resolve_right htc
  intro j hj
  exact hi _ j rfl hj


lemma vanishingFiltration_eq_span {K : Type*} [Field K]
    {V : Submodule K K[X]} {h : ℕ} (b : Basis (Fin h) K V)
    (a : K) (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a))
    (r : ℕ) :
    vanishingFiltration V a r = Submodule.span K
      (Set.range (fun j : {j : Fin h // r ≤ (b j : K[X]).rootMultiplicity a} =>
        (b j.val : K[X]))) := by
  classical
  apply le_antisymm
  · intro f hf
    let c := b.repr ⟨f, hf.1⟩
    have hs : ∑ j, c j • (b j : K[X]) = f := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg (fun x : V => (x : K[X])) (b.sum_repr ⟨f, hf.1⟩)
    have hne : ∀ j, taylor a (b j : K[X]) ≠ 0 := by
      intro j hz
      exact b.ne_zero j (Subtype.ext ((taylorEquiv a).injective (by simpa using hz)))
    have hinj : Function.Injective (fun j => (taylor a (b j : K[X])).natTrailingDegree) := by
      simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using hb
    have hz : ∀ m < r, (∑ j, c j • taylor a (b j : K[X])).coeff m = 0 := by
      intro m hm
      have ht := congrArg (taylor a) hs
      simp only [map_sum, map_smul] at ht
      rw [ht]
      exact hf.2 m hm
    have hc := low_coefficients_force_zero (fun j => taylor a (b j : K[X]))
      hne hinj c r hz
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨fun j => c j.val, ?_⟩
    have hst := Finset.sum_subtype (F := inferInstance) (p := fun j => r ≤ (b j : K[X]).rootMultiplicity a)
      (Finset.univ.filter (fun j => r ≤ (b j : K[X]).rootMultiplicity a))
      (by simp) (fun j => c j • (b j : K[X]))
    rw [← hst]
    rw [Finset.sum_filter]
    calc
      ∑ j, (if r ≤ (b j : K[X]).rootMultiplicity a then c j • (b j : K[X]) else 0) =
          ∑ j, c j • (b j : K[X]) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with hj
        · rfl
        · have hj' : (taylor a (b j : K[X])).natTrailingDegree < r := by
            simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using
              (Nat.lt_of_not_ge hj)
          rw [hc j hj', zero_smul]
      _ = f := hs
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨(b j.val).property, ?_⟩
    intro m hm
    apply coeff_eq_zero_of_lt_natTrailingDegree
    apply hm.trans_le
    simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using j.property

/-- Row reduction exactly describes the whole vanishing filtration,
not only the basis vectors. -/
theorem finrank_vanishingFiltration {K : Type*} [Field K]
    {V : Submodule K K[X]} {h : ℕ} (b : Basis (Fin h) K V)
    (a : K) (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a))
    (r : ℕ) :
    finrank K (vanishingFiltration V a r) =
      Fintype.card {j : Fin h // r ≤ (b j : K[X]).rootMultiplicity a} := by
  rw [vanishingFiltration_eq_span b a hb]
  apply finrank_span_eq_card
  exact (b.linearIndependent.map' V.subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).comp _ Subtype.val_injective

end
end RationalHitting.Expansion


/-! An integral frame records integral coordinate functionals, making
saturation explicit. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.LaurentReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.LaurentReduction
open Module
open scoped BigOperators LaurentSeries PowerSeries
noncomputable section

variable {K : Type*} [Field K]

lemma integral_iff (x : F K) : Integral x ↔ Valued.v x ≤ 1 :=
  (LaurentSeries.val_le_one_iff_eq_coe K x).symm

lemma integral_zero : Integral (0 : F K) := ⟨0, map_zero _⟩
lemma Integral.add {x y : F K} (hx : Integral x) (hy : Integral y) : Integral (x + y) := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  exact ⟨p + q, map_add _ _ _⟩
lemma Integral.neg {x : F K} (hx : Integral x) : Integral (-x) := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨-p, map_neg _ _⟩
lemma Integral.sub {x y : F K} (hx : Integral x) (hy : Integral y) : Integral (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg
lemma Integral.mul {x y : F K} (hx : Integral x) (hy : Integral y) : Integral (x * y) := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  exact ⟨p * q, map_mul _ _ _⟩

lemma reduction_mul {x y : F K} (hx : Integral x) (hy : Integral y) :
    reduction (x * y) = reduction x * reduction y := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  rw [← map_mul]
  have hc : ∀ s : PowerSeries K, reduction (HahnSeries.ofPowerSeries ℤ K s) =
      PowerSeries.constantCoeff s := by
    intro s
    simpa only [reduction, Int.natCast_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (LaurentSeries.coeff_coe_powerSeries s 0)
  rw [hc, hc, hc, map_mul]

lemma normalize_vector {ι : Type*} [Fintype ι] (x : ι → F K) (hx : x ≠ 0) :
    ∃ (c : ι) (u : F K), u ≠ 0 ∧ (∀ i, Integral (u * x i)) ∧ u * x c = 1 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  change x j ≠ 0 at hj
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (x i))
    ⟨j, Finset.mem_univ _⟩
  have hxc : x c ≠ 0 := by
    intro hz
    have hh := hc j (Finset.mem_univ _)
    rw [hz, map_zero] at hh
    exact hj ((Valuation.zero_iff _).mp (le_antisymm hh zero_le))
  refine ⟨c, (x c)⁻¹, inv_ne_zero hxc, ?_, inv_mul_cancel₀ hxc⟩
  intro i
  rw [integral_iff, mul_comm, ← div_eq_mul_inv, Valuation.map_div]
  apply (div_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hxc))).mpr
  exact hc i (Finset.mem_univ _)

lemma IntegralVector.sub {ι : Type*} {x y : ι → F K}
    (hx : IntegralVector x) (hy : IntegralVector y) : IntegralVector (x - y) :=
  fun i => (hx i).sub (hy i)


/-- Valuation-adapted Gaussian elimination constructs an integral frame for
any Laurent-series subspace. The coordinate functionals guarantee saturation. -/
theorem exists_integralFrame {ι : Type*} [Fintype ι]
    (U : Submodule (F K) (ι → F K)) : Nonempty (IntegralFrame U) := by
  classical
  suffices ∀ k, ∀ U : Submodule (F K) (ι → F K),
      Module.finrank (F K) U = k → Nonempty (IntegralFrame U) from
    this _ U rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro U hdim
    by_cases hU : U = ⊥
    · subst U
      exact ⟨{ length := 0
               vector := Fin.elim0
               coordinate := Fin.elim0
               span_eq := by simp
               vector_integral := fun j => Fin.elim0 j
               coordinate_integral := fun j => Fin.elim0 j
               pairing := fun i => Fin.elim0 i
               reduced_independent := linearIndependent_empty_type }⟩
    obtain ⟨v, hvU, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    obtain ⟨c, u, hu, hxint, hxc⟩ := normalize_vector v hv
    let x : ι → F K := u • v
    have hxU : x ∈ U := U.smul_mem u hvU
    have hxI : IntegralVector x := hxint
    have hxc' : x c = 1 := hxc
    let π : (ι → F K) →ₗ[F K] F K := LinearMap.proj c
    let W := U ⊓ LinearMap.ker π
    have hWU : W < U := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro he
      have hxW : x ∈ W := he.symm ▸ hxU
      have hh : x c = 0 := hxW.2
      exact one_ne_zero (hxc'.symm.trans hh)
    have hdimW : Module.finrank (F K) W < k := by
      rw [← hdim]
      exact Submodule.finrank_lt_finrank_of_lt hWU
    obtain ⟨b⟩ := ih _ hdimW W rfl
    have hbW : ∀ j, b.vector j ∈ W := by
      intro j
      exact b.span_eq.le (Submodule.subset_span ⟨j, rfl⟩)
    have hbc : ∀ j, b.vector j c = 0 := fun j => (hbW j).2
    let φ : Fin b.length → ((ι → F K) →ₗ[F K] F K) := fun j =>
      b.coordinate j - b.coordinate j x • π
    refine ⟨{ length := b.length + 1
              vector := Fin.cons x b.vector
              coordinate := Fin.cons π φ
              span_eq := ?_
              vector_integral := ?_
              coordinate_integral := ?_
              pairing := ?_
              reduced_independent := ?_ }⟩
    · apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact Fin.cases hxU (fun i => (hbW i).1) j
      · intro y hy
        have hr : y - y c • x ∈ W := by
          refine ⟨U.sub_mem hy (U.smul_mem _ hxU), ?_⟩
          change y c - y c * x c = 0
          simp [hxc']
        have hsub : W ≤ Submodule.span (F K) (Set.range (Fin.cons x b.vector)) := by
          apply le_trans b.span_eq.ge
          apply Submodule.span_mono
          rw [Fin.range_cons]
          exact Set.subset_insert x _
        have hxspan : x ∈ Submodule.span (F K) (Set.range (Fin.cons x b.vector)) :=
          Submodule.subset_span ⟨0, by simp⟩
        have hh := (Submodule.span (F K) (Set.range (Fin.cons x b.vector))).add_mem
          (hsub hr) ((Submodule.span (F K) (Set.range (Fin.cons x b.vector))).smul_mem (y c) hxspan)
        simpa only [sub_add_cancel] using hh
    · intro j
      exact Fin.cases hxI b.vector_integral j
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact fun y hy => hy c
      · intro y hy
        change Integral (b.coordinate i y - b.coordinate i x * y c)
        exact (b.coordinate_integral i y hy).sub
          ((b.coordinate_integral i x hxI).mul (hy c))
    · intro i j
      refine Fin.cases ?_ (fun a => ?_) i <;>
        refine Fin.cases ?_ (fun z => ?_) j
      · simp [π, hxc']
      · simp [π, hbc, Ne.symm (Fin.succ_ne_zero _)]
      · simp [φ, π, hxc']
      · simp [φ, π, hbc, b.pairing]
    · have he : (fun j : Fin (b.length + 1) => reduce ((Fin.cons x b.vector : Fin (b.length + 1) → (ι → F K)) j)) =
          Fin.cons (reduce x) (fun j => reduce (b.vector j)) := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      rw [he, linearIndependent_finCons]
      refine ⟨b.reduced_independent, ?_⟩
      have hsp : Submodule.span K (Set.range (fun j => reduce (b.vector j))) ≤
          LinearMap.ker (LinearMap.proj c : (ι → K) →ₗ[K] K) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        change reduction (b.vector j c) = 0
        rw [hbc, reduction_zero]
      intro hx
      have hh : reduction (x c) = 0 := hsp hx
      rw [hxc', reduction_one] at hh
      exact one_ne_zero hh

namespace IntegralFrame

variable {ι : Type*} {U : Submodule (F K) (ι → F K)} (b : IntegralFrame U)

lemma linearIndependent : LinearIndependent (F K) b.vector := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  have hh := congrArg (b.coordinate j) hc
  simpa only [map_sum, map_smul, b.pairing, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, hj, ite_true, map_zero] using hh

lemma vector_mem (j : Fin b.length) : b.vector j ∈ U := by
  exact b.span_eq.le (Submodule.subset_span ⟨j, rfl⟩)

/-- Full integral-lattice saturation: every integral member has integral
basis coordinates, explicitly given by the constructed functionals. -/
lemma integral_coordinates (x : ι → F K) (hx : IntegralVector x) :
    ∀ j, Integral (b.coordinate j x) := fun j => b.coordinate_integral j x hx

lemma sum_coordinates (x : ι → F K) (hx : x ∈ U) :
    ∑ j, b.coordinate j x • b.vector j = x := by
  classical
  have hx := b.span_eq.ge hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (F K)).mp hx
  congr 1
  funext j
  simp only [map_sum, map_smul, b.pairing, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma length_eq_finrank : b.length = finrank (F K) U := by
  have hh := finrank_span_eq_card b.linearIndependent
  rw [b.span_eq] at hh
  simpa using hh.symm

end IntegralFrame

lemma integral_C (a : K) : Integral (HahnSeries.C a : F K) :=
  ⟨PowerSeries.C a, PowerSeries.coe_C a⟩

lemma reduce_sum {ι τ : Type*} (s : Finset τ) (v : τ → (ι → F K)) :
    reduce (∑ j ∈ s, v j) = ∑ j ∈ s, reduce (v j) := by
  ext i
  simp [reduce, reduction]

lemma reduce_smul {ι : Type*} {a : F K} {v : ι → F K}
    (ha : Integral a) (hv : IntegralVector v) :
    reduce (a • v) = reduction a • reduce v := by
  ext i
  exact reduction_mul ha (hv i)

lemma reduce_C_smul {ι : Type*} (a : K) (v : ι → F K) :
    reduce ((HahnSeries.C a : F K) • v) = a • reduce v := by
  ext i
  change reduction (HahnSeries.C a * v i) = a * reduction (v i)
  rw [HahnSeries.C_mul_eq_smul]
  rfl

lemma reducedSet_eq_span {ι : Type*} {U : Submodule (F K) (ι → F K)}
    (b : IntegralFrame U) :
    ReducedSet U = (Submodule.span K (Set.range (fun j => reduce (b.vector j))) : Set (ι → K)) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hxU, hxI, rfl⟩
    have he := congrArg reduce (b.sum_coordinates x hxU)
    rw [reduce_sum] at he
    simp_rw [reduce_smul (b.integral_coordinates x hxI _) (b.vector_integral _)] at he
    rw [← he]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, rfl⟩)
  · intro hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
    refine ⟨∑ j, (HahnSeries.C (c j) : F K) • b.vector j, ?_, ?_, ?_⟩
    · exact U.sum_mem fun j _ => U.smul_mem _ (b.vector_mem j)
    · intro i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_induction _ _ (fun _ _ => Integral.add) integral_zero
      intro j _
      exact (integral_C _).mul (b.vector_integral j i)
    · rw [reduce_sum]
      simp_rw [reduce_C_smul]

lemma reducedSubspace_eq_span {ι : Type*} {U : Submodule (F K) (ι → F K)}
    (b : IntegralFrame U) :
    reducedSubspace U = Submodule.span K (Set.range (fun j => reduce (b.vector j))) := by
  rw [reducedSubspace, reducedSet_eq_span b, Submodule.span_eq]

/-- Full integral reduction preserves dimension. -/
theorem finrank_reducedSubspace {ι : Type*} [Fintype ι]
    (U : Submodule (F K) (ι → F K)) :
    finrank K (reducedSubspace U) = finrank (F K) U := by
  obtain ⟨b⟩ := exists_integralFrame U
  rw [reducedSubspace_eq_span b, finrank_span_eq_card b.reduced_independent,
    Fintype.card_fin, b.length_eq_finrank]


lemma Integral.order_nonneg {x : F K} (hx : Integral x) : 0 ≤ x.order := by
  by_cases hz : x = 0
  · simp [hz]
  apply (HahnSeries.le_order_iff_forall hz).mpr
  have hv := (integral_iff x).mp hx
  have hh : Valued.v x ≤ WithZero.exp (-(0 : ℤ)) := by simpa using hv
  exact (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).mp hh

lemma Integral.order_eq_zero {x : F K} (hx : Integral x) (hr : reduction x ≠ 0) :
    x.order = 0 :=
  le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hr) hx.order_nonneg

lemma weightMap_injective {ι : Type*} (w : ι → ℕ) :
    Function.Injective (weightMap (K := K) w) := by
  intro x y h
  funext i
  have he := congrFun h i
  change HahnSeries.single (w i : ℤ) (1 : K) * x i =
    HahnSeries.single (w i : ℤ) 1 * y i at he
  exact mul_left_cancel₀ (HahnSeries.single_ne_zero one_ne_zero) he

/-- The key valuation step of order reversal: an integral normalized input
having a nonzero low reduction cannot give a high leading output coefficient. -/
lemma weighted_high_reduction_zero {ι : Type*} (w : ι → ℕ) (A : ℕ)
    (x : ι → F K) (hx : IntegralVector x)
    (hlow : ∃ j, w j ≤ A ∧ reduction (x j) ≠ 0)
    (c : F K) (hc : c ≠ 0)
    (hy : IntegralVector (c • weightMap w x)) :
    ∀ i, A < w i → reduction ((c • weightMap w x) i) = 0 := by
  obtain ⟨j, hjA, hj⟩ := hlow
  have hxj : x j ≠ 0 := by intro he; simp [he] at hj
  have ht (i : ι) : (HahnSeries.single (w i : ℤ) (1 : K) : F K) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hj0 := (hy j).order_nonneg
  change 0 ≤ (c * (HahnSeries.single (w j : ℤ) 1 * x j)).order at hj0
  rw [HahnSeries.order_mul hc (mul_ne_zero (ht j) hxj),
    HahnSeries.order_mul (ht j) hxj, HahnSeries.order_single one_ne_zero,
    (hx j).order_eq_zero hj, add_zero] at hj0
  intro i hi
  by_cases hxi : x i = 0
  · simp [weightMap, hxi, reduction]
  change (c * (HahnSeries.single (w i : ℤ) 1 * x i)).coeff 0 = 0
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [HahnSeries.order_mul hc (mul_ne_zero (ht i) hxi),
    HahnSeries.order_mul (ht i) hxi, HahnSeries.order_single one_ne_zero]
  have hxi0 := (hx i).order_nonneg
  omega

/-- Low coordinates detect reduction throughout U. This controls its full
integral image lattice, not only the images of an arbitrary integral basis. -/
theorem reduction_weighted_supported {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (A : ℕ) (U : Submodule (F K) (ι → F K))
    (hdetect : ∀ x ∈ U, IntegralVector x →
      (∀ i, w i ≤ A → reduction (x i) = 0) → reduce x = 0)
    (y : ι → F K) (hyU : y ∈ U.map (weightMap w)) (hyI : IntegralVector y) :
    ∀ i, A < w i → reduction (y i) = 0 := by
  classical
  obtain ⟨x, hxU, rfl⟩ := hyU
  by_cases hx : x = 0
  · subst x
    simp [weightMap, reduction]
  obtain ⟨c, u, hu, hnI, hnc⟩ := normalize_vector x hx
  have hnU : u • x ∈ U := U.smul_mem u hxU
  have hnI' : IntegralVector (u • x) := hnI
  have hr : reduce (u • x) ≠ 0 := by
    intro he
    have hh := congrFun he c
    change reduction (u * x c) = 0 at hh
    rw [hnc, reduction_one] at hh
    exact one_ne_zero hh
  have hd : ∃ j, w j ≤ A ∧ reduction ((u • x) j) ≠ 0 := by
    by_contra! hh
    exact hr (hdetect _ hnU hnI' hh)
  have he : u⁻¹ • weightMap w (u • x) = weightMap w x := by
    rw [map_smul, smul_smul, inv_mul_cancel₀ hu, one_smul]
  exact he ▸ weighted_high_reduction_zero w A (u • x) hnI' hd u⁻¹
    (inv_ne_zero hu) (he.symm ▸ hyI)


lemma exists_independent_subfamily {V : Type*} [AddCommGroup V] [Module K V]
    {h : ℕ} (v : Fin h → V) :
    ∃ (k : ℕ) (a : Fin k → Fin h), Function.Injective a ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) ∧
      LinearIndependent K (v ∘ a) := by
  classical
  obtain ⟨κ, a, ha, hs, hi⟩ := exists_linearIndependent' K v
  let : Fintype κ := Fintype.ofInjective a ha
  let e := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, a ∘ e, ha.comp e.injective, ?_, hi.comp e e.injective⟩
  have he : Set.range (v ∘ a ∘ e) = Set.range (v ∘ a) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨e j, rfl⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨r, rfl⟩ := e.surjective j
      exact ⟨r, rfl⟩
  change Submodule.span K (Set.range (v ∘ a ∘ e)) = _
  rw [he, hs]

lemma reducedSubspace_mono {ι : Type*} {U V : Submodule (F K) (ι → F K)}
    (h : U ≤ V) : reducedSubspace U ≤ reducedSubspace V := by
  apply Submodule.span_mono
  rintro y ⟨x, hx, hI, rfl⟩
  exact ⟨x, h hx, hI, rfl⟩

/-- Choose an integral-lattice subspace on whose reduction a specified
projection is injective, of dimension equal to that projection's rank. -/
theorem exists_projection_subspace {ι : Type*} [Fintype ι]
    {V : Type*} [AddCommGroup V] [Module K V]
    (U : Submodule (F K) (ι → F K)) (P : (ι → K) →ₗ[K] V) :
    ∃ U' : Submodule (F K) (ι → F K), U' ≤ U ∧
      finrank (F K) U' = finrank K ((reducedSubspace U).map P) ∧
      ∀ x ∈ U', IntegralVector x → P (reduce x) = 0 → reduce x = 0 := by
  classical
  obtain ⟨b⟩ := exists_integralFrame U
  obtain ⟨k, a, ha, hs, hi⟩ := exists_independent_subfamily (K := K)
    (fun j => P (reduce (b.vector j)))
  let b' := b.subframe a ha
  let U' := Submodule.span (F K) (Set.range (b.vector ∘ a))
  refine ⟨U', ?_, ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact b.vector_mem (a j)
  · rw [reducedSubspace_eq_span b, Submodule.map_span, ← Set.range_comp]
    change finrank (F K) U' = finrank K (Submodule.span K
      (Set.range (fun j => P (reduce (b.vector j)))))
    rw [← hs, finrank_span_eq_card hi, Fintype.card_fin]
    exact b'.length_eq_finrank.symm
  · intro x hxU hxI hxP
    have hx : reduce x ∈ Submodule.span K (Set.range (fun j => reduce (b'.vector j))) := by
      change reduce x ∈ (Submodule.span K (Set.range (fun j => reduce (b'.vector j))) : Set (ι → K))
      rw [← reducedSet_eq_span b']
      exact ⟨x, hxU, hxI, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    have hh : ∑ j, c j • (P (reduce (b.vector (a j)))) = 0 := by
      rw [← hxP, ← hc, map_sum]
      simp only [map_smul]
      rfl
    have hz := (Fintype.linearIndependent_iff.mp hi) c hh
    rw [← hc]
    apply Finset.sum_eq_zero
    intro i _
    have hci : c i = 0 := hz i
    rw [hci, zero_smul]

lemma finrank_map_injective {L : Type*} [Field L] {V W : Type*}
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (f : V →ₗ[L] W) (hf : Function.Injective f) (U : Submodule L V) :
    finrank L (U.map f) = finrank L U := by
  have he : (f.domRestrict U).range = U.map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  rw [← he]
  exact LinearMap.finrank_range_of_inj (hf.comp Subtype.val_injective)

/-- Filtration version of order reversal, before a constant coordinate change.
This uses the whole integral lattice on both sides. -/
theorem weighted_filtration_rank {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (A : ℕ) (U : Submodule (F K) (ι → F K))
    (W : Submodule (F K) (ι → F K)) (hW : U.map (weightMap w) ≤ W) :
    finrank K ((reducedSubspace U).map (lowProjection w A)) ≤
      finrank K ↥(reducedSubspace W ⊓ lowSupported w A) := by
  obtain ⟨U', hU, hdim, hdetect⟩ := exists_projection_subspace U (lowProjection w A)
  have hs : reducedSubspace (U'.map (weightMap w)) ≤ lowSupported w A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hyU, hyI, rfl⟩
    apply reduction_weighted_supported w A U' ?_ y hyU hyI
    intro x hx hxI hh
    apply hdetect x hx hxI
    funext i
    exact hh i i.property
  have hw : reducedSubspace (U'.map (weightMap w)) ≤ reducedSubspace W :=
    reducedSubspace_mono ((Submodule.map_mono hU).trans hW)
  have hh := Submodule.finrank_mono (le_inf hw hs)
  rw [finrank_reducedSubspace, finrank_map_injective _ (weightMap_injective w), hdim] at hh
  exact hh


section ConstantChanges
variable {ι κ τ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]

lemma liftMap_apply.{v_1, v_2, v_3} {K : Type v_1} [Field K]
  {ι : Type v_2} {κ : Type v_3} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (P : (ι → K) →ₗ[K] κ → K) (x : ι → RationalHitting.LaurentReduction.F K) (j : κ) :
  (RationalHitting.LaurentReduction.liftMap P) x j =
    ∑ i, HahnSeries.C (LinearMap.toMatrix' P j i) * x i := rfl

lemma liftMap_integral (P : (ι → K) →ₗ[K] (κ → K)) {x : ι → F K}
    (hx : IntegralVector x) : IntegralVector (liftMap P x) := by
  intro j
  rw [liftMap_apply]
  apply Finset.sum_induction _ _ (fun _ _ => Integral.add) integral_zero
  intro i _
  exact (integral_C _).mul (hx i)

lemma reduction_liftMap.{v_1, v_2, v_3} {K : Type v_1} [Field K]
  {ι : Type v_2} {κ : Type v_3} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (P : (ι → K) →ₗ[K] κ → K) (x : ι → RationalHitting.LaurentReduction.F K) :
  RationalHitting.LaurentReduction.reduce ((RationalHitting.LaurentReduction.liftMap P) x) =
    P (RationalHitting.LaurentReduction.reduce x) := by
  have hc (a : K) (z : F K) : reduction (HahnSeries.C a * z) = a * reduction z := by
    rw [HahnSeries.C_mul_eq_smul]; rfl
  funext j
  conv_rhs => rw [← Matrix.toLin'_toMatrix' P]
  change reduction (∑ i, HahnSeries.C (LinearMap.toMatrix' P j i) * x i) = _
  simp only [reduction, HahnSeries.coeff_sum] -- constant multiplication commutes with reduction
  change (∑ i, reduction (HahnSeries.C (LinearMap.toMatrix' P j i) * x i)) = _
  simp only [hc]
  rfl

lemma integral_liftEquiv_iff (E : (ι → K) ≃ₗ[K] (κ → K)) (x : ι → F K) :
    IntegralVector (liftEquiv E x) ↔ IntegralVector x := by
  constructor
  · intro h
    have hh := liftMap_integral E.symm.toLinearMap h
    change IntegralVector ((liftEquiv E).symm (liftEquiv E x)) at hh
    simpa using hh
  · exact liftMap_integral E.toLinearMap

lemma reducedSubspace_liftEquiv (E : (ι → K) ≃ₗ[K] (κ → K))
    (U : Submodule (F K) (ι → F K)) :
    reducedSubspace (U.map (liftEquiv E).toLinearMap) =
      (reducedSubspace U).map E.toLinearMap := by
  rw [reducedSubspace, reducedSubspace, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨x, hxU, rfl⟩, hzI, rfl⟩
    have hxI := (integral_liftEquiv_iff E x).mp hzI
    exact ⟨reduce x, ⟨x, hxU, hxI, rfl⟩, (reduction_liftMap E.toLinearMap x).symm⟩
  · rintro ⟨z, ⟨x, hxU, hxI, rfl⟩, rfl⟩
    exact ⟨liftEquiv E x, ⟨x, hxU, rfl⟩, liftMap_integral E.toLinearMap hxI,
      reduction_liftMap E.toLinearMap x⟩

end ConstantChanges


theorem conjugated_filtration_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ein Eout : (ι → K) ≃ₗ[K] (ι → K)) (w : ι → ℕ) (A : ℕ)
    (U W : Submodule (F K) (ι → F K))
    (hW : U.map (conjugatedWeight Ein Eout w) ≤ W) :
    finrank K (((reducedSubspace U).map Ein.toLinearMap).map (lowProjection w A)) ≤
      finrank K ↥((reducedSubspace W).map Eout.toLinearMap ⊓ lowSupported w A) := by
  have hh : (U.map (liftEquiv Ein).toLinearMap).map (weightMap w) ≤
      W.map (liftEquiv Eout).toLinearMap := by
    rintro y ⟨z, ⟨x, hxU, rfl⟩, rfl⟩
    refine ⟨conjugatedWeight Ein Eout w x, hW ⟨x, hxU, rfl⟩, ?_⟩
    exact (liftEquiv Eout).apply_symm_apply _
  have h := weighted_filtration_rank w A (U.map (liftEquiv Ein).toLinearMap)
    (W.map (liftEquiv Eout).toLinearMap) hh
  rwa [reducedSubspace_liftEquiv, reducedSubspace_liftEquiv] at h

lemma finrank_map_add_finrank_inf_ker {L : Type*} [Field L] {V W : Type*}
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (f : V →ₗ[L] W) (U : Submodule L V) [FiniteDimensional L U] :
    finrank L (U.map f) + finrank L ↥(U ⊓ f.ker) = finrank L U := by
  have hr : (f.domRestrict U).range = U.map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  have hk : ((f.domRestrict U).ker).map U.subtype = U ⊓ f.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.property, hy⟩
    · rintro ⟨hx, hf⟩; exact ⟨⟨x, hx⟩, hf, rfl⟩
  have hd := (f.domRestrict U).finrank_range_add_finrank_ker
  rw [hr, ← finrank_map_injective U.subtype Subtype.val_injective, hk] at hd
  exact hd

end
end RationalHitting.LaurentReduction

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.SmallExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.SmallExpansion
open Module Polynomial
open scoped BigOperators
open LaurentReduction Expansion
noncomputable section
variable {K : Type*} [Field K]

lemma polynomialMap_injective (M : ℕ) : Function.Injective (polynomialMap (K := K) M) :=
  Subtype.val_injective.comp (Polynomial.degreeLTEquiv K M).symm.injective

lemma polynomialMap_mem (M : ℕ) (x : Fin M → K) :
    polynomialMap M x ∈ Polynomial.degreeLT K M :=
  ((Polynomial.degreeLTEquiv K M).symm x).property

lemma polynomialMap_coeff_high (M : ℕ) (x : Fin M → K) (j : ℕ) (hj : M ≤ j) :
    (polynomialMap M x).coeff j = 0 := by
  apply coeff_eq_zero_of_degree_lt
  exact (Polynomial.mem_degreeLT.mp (polynomialMap_mem M x)).trans_le (by exact_mod_cast hj)

lemma finrank_polynomialSpace {M : ℕ} (V : Submodule K (Fin M → K)) :
    finrank K (polynomialSpace V) = finrank K V :=
  finrank_map_injective _ (polynomialMap_injective M) V

lemma polynomialSpace_bound {M : ℕ} (V : Submodule K (Fin M → K)) :
    ∀ f ∈ polynomialSpace V, f ≠ 0 → f.natDegree < M := by
  rintro f ⟨x, hx, rfl⟩ hn
  exact (natDegree_lt_iff_degree_lt hn).mpr (Polynomial.mem_degreeLT.mp (polynomialMap_mem M x))

lemma taylorCoordinates_apply (M : ℕ) (a : K) (x : Fin M → K) (j : Fin M) :
    taylorCoordinates M a x j = (taylor a (polynomialMap M x)).coeff j := rfl

/-- Kernel of the low Taylor projection is precisely the vanishing filtration. -/
lemma map_taylor_projection_kernel (M : ℕ) (a : K) (A : ℕ)
    (V : Submodule K (Fin M → K)) :
    (V ⊓ ((lowProjection Fin.val A).comp (taylorCoordinates M a).toLinearMap).ker).map
      (polynomialMap M) = vanishingFiltration (polynomialSpace V) a (A+1) := by
  ext f
  constructor
  · rintro ⟨x, ⟨hxV, hx⟩, rfl⟩
    refine ⟨⟨x, hxV, rfl⟩, ?_⟩
    intro j hj
    by_cases hjM : j < M
    · have he := congrFun hx (⟨⟨j, hjM⟩, by change j ≤ A; omega⟩ : {i : Fin M // i.val ≤ A})
      exact he
    · apply coeff_eq_zero_of_degree_lt
      have hdeg := Polynomial.mem_degreeLT.mp (polynomialMap_mem M x)
      rw [degree_taylor]
      exact hdeg.trans_le (by exact_mod_cast (Nat.le_of_not_gt hjM))
  · rintro ⟨⟨x, hxV, rfl⟩, hx⟩
    refine ⟨x, ⟨hxV, ?_⟩, rfl⟩
    change (lowProjection Fin.val A) (taylorCoordinates M a x) = 0
    funext j
    exact hx j.val.val (by have := j.property; omega)

/-- The output-side low reverse coordinates mean high ordinary Taylor order. -/
lemma map_reverseTaylor_lowSupported (M : ℕ) (a : K) (A : ℕ)
    (V : Submodule K (Fin M → K)) :
    ((V.map (reverseTaylorCoordinates M a).toLinearMap) ⊓ lowSupported Fin.val A).map
      ((polynomialMap M).comp (reverseTaylorCoordinates M a).symm.toLinearMap) =
      vanishingFiltration (polynomialSpace V) a (M-1-A) := by
  ext f
  constructor
  · rintro ⟨y, ⟨⟨x, hxV, rfl⟩, hy⟩, rfl⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    refine ⟨⟨x, hxV, rfl⟩, ?_⟩
    intro j hj
    have hjM : j < M := by omega
    have hh := hy (Fin.rev ⟨j, hjM⟩) (by simp only [Fin.val_rev]; omega)
    change taylorCoordinates M a x ((Fin.rev ⟨j, hjM⟩).rev) = 0 at hh
    simpa only [Fin.rev_rev, taylorCoordinates_apply] using hh
  · rintro ⟨⟨x, hxV, rfl⟩, hx⟩
    refine ⟨reverseTaylorCoordinates M a x, ⟨⟨x, hxV, rfl⟩, ?_⟩, ?_⟩
    · intro j hj
      change taylorCoordinates M a x j.rev = 0
      exact hx j.rev.val (by simp only [Fin.val_rev]; omega)
    · simp


lemma finrank_lowTaylor (M : ℕ) (a : K) (A : ℕ)
    (V : Submodule K (Fin M → K)) {h : ℕ}
    (b : Basis (Fin h) K (polynomialSpace V))
    (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a)) :
    finrank K ((V.map (taylorCoordinates M a).toLinearMap).map (lowProjection Fin.val A)) =
      Fintype.card {j : Fin h // (b j : K[X]).rootMultiplicity a ≤ A} := by
  classical
  have hd := finrank_map_add_finrank_inf_ker
    ((lowProjection Fin.val A).comp (taylorCoordinates M a).toLinearMap) V
  have hk := finrank_map_injective (polynomialMap M) (polynomialMap_injective M)
    (V ⊓ ((lowProjection Fin.val A).comp (taylorCoordinates M a).toLinearMap).ker)
  rw [map_taylor_projection_kernel, finrank_vanishingFiltration b a hb] at hk
  have hdim : finrank K V = h := by
    rw [← finrank_polynomialSpace, Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [Submodule.map_comp, ← hk, hdim] at hd
  have hc : Fintype.card {j : Fin h // (b j : K[X]).rootMultiplicity a ≤ A} +
      Fintype.card {j : Fin h // A+1 ≤ (b j : K[X]).rootMultiplicity a} = h := by
    simp only [Fintype.card_subtype, Nat.add_one_le_iff, ← not_le]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun j : Fin h => (b j : K[X]).rootMultiplicity a ≤ A)
  omega

lemma finrank_reverseTaylor (M : ℕ) (a : K) (A : ℕ)
    (V : Submodule K (Fin M → K)) {h : ℕ}
    (b : Basis (Fin h) K (polynomialSpace V))
    (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a)) :
    finrank K ↥((V.map (reverseTaylorCoordinates M a).toLinearMap) ⊓ lowSupported Fin.val A) =
      Fintype.card {j : Fin h // M-1-A ≤ (b j : K[X]).rootMultiplicity a} := by
  rw [← finrank_map_injective ((polynomialMap M).comp (reverseTaylorCoordinates M a).symm.toLinearMap)
    ((polynomialMap_injective M).comp (reverseTaylorCoordinates M a).symm.injective),
    map_reverseTaylor_lowSupported, finrank_vanishingFiltration b a hb]

/-- The rank form of order reversal, at every threshold. -/
theorem order_reversal_counts (M : ℕ) (a : K) (A : ℕ)
    (U W : Submodule (F K) (Fin M → F K)) (hW : U.map (testMap M a) ≤ W)
    {k l : ℕ} (b : Basis (Fin k) K (polynomialSpace (reducedSubspace U)))
    (c : Basis (Fin l) K (polynomialSpace (reducedSubspace W)))
    (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a))
    (hc : Function.Injective (fun j => (c j : K[X]).rootMultiplicity a)) :
    Fintype.card {j : Fin k // (b j : K[X]).rootMultiplicity a ≤ A} ≤
      Fintype.card {j : Fin l // M-1-A ≤ (c j : K[X]).rootMultiplicity a} := by
  have hh := conjugated_filtration_rank (taylorCoordinates M a) (reverseTaylorCoordinates M a)
    Fin.val A U W hW
  rwa [finrank_lowTaylor M a A _ b hb, finrank_reverseTaylor M a A _ c hc] at hh

/-- Counting all thresholds counts each order with its exact multiplicity. -/
lemma sum_threshold_counts {h : ℕ} (d : Fin h → ℕ) (L : ℕ) :
    (∑ A ∈ Finset.range L, Fintype.card {j : Fin h // d j ≤ A}) =
      ∑ j, (L - d j) := by
  classical
  simp only [Fintype.card_subtype]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he : (Finset.range L).filter (fun A => d j ≤ A) = Finset.Ico (d j) L := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  rw [← Finset.card_filter, he, Nat.card_Ico]

lemma sum_reversed_counts {h : ℕ} (d : Fin h → ℕ) (L : ℕ) (hd : ∀ j, d j ≤ L) :
    (∑ A ∈ Finset.range L, Fintype.card {j : Fin h // L-A ≤ d j}) = ∑ j, d j := by
  have he : ∀ A, (fun j : Fin h => L-A ≤ d j) = (fun j : Fin h => L-d j ≤ A) := by
    intro A
    funext j
    exact propext (by omega)
  simp_rw [he]
  rw [sum_threshold_counts]
  apply Finset.sum_congr rfl
  intro j _
  have := hd j
  omega

/-- Summation of order reversal, without selecting incompatible auxiliary
subspaces: all inequalities concern the fixed filtration of the same W. -/
theorem order_reversal_sum (M : ℕ) (a : K)
    (U W : Submodule (F K) (Fin M → F K)) (hW : U.map (testMap M a) ≤ W)
    {k l : ℕ} (b : Basis (Fin k) K (polynomialSpace (reducedSubspace U)))
    (c : Basis (Fin l) K (polynomialSpace (reducedSubspace W)))
    (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a))
    (hc : Function.Injective (fun j => (c j : K[X]).rootMultiplicity a)) :
    k * (M-1) ≤ (∑ j, (b j : K[X]).rootMultiplicity a) +
      (∑ j, (c j : K[X]).rootMultiplicity a) := by
  classical
  have hbd : ∀ j, (b j : K[X]).rootMultiplicity a ≤ M-1 := by
    intro j
    have hle : (b j : K[X]).rootMultiplicity a ≤ (b j : K[X]).natDegree := by
      rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
      exact (natTrailingDegree_le_natDegree _).trans (le_of_eq (natDegree_taylor _ _))
    apply hle.trans
    have hh := polynomialSpace_bound (reducedSubspace U) _ (b j).property
      (fun hz => b.ne_zero j (Subtype.ext hz))
    omega
  have hcd : ∀ j, (c j : K[X]).rootMultiplicity a ≤ M-1 := by
    intro j
    have hle : (c j : K[X]).rootMultiplicity a ≤ (c j : K[X]).natDegree := by
      rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
      exact (natTrailingDegree_le_natDegree _).trans (le_of_eq (natDegree_taylor _ _))
    apply hle.trans
    have hh := polynomialSpace_bound (reducedSubspace W) _ (c j).property
      (fun hz => c.ne_zero j (Subtype.ext hz))
    omega
  have hh := Finset.sum_le_sum (s := Finset.range (M-1))
    (fun A _ => order_reversal_counts M a A U W hW b c hb hc)
  rw [sum_threshold_counts, sum_reversed_counts _ _ hcd] at hh
  have he : (∑ j, (M-1 - (b j : K[X]).rootMultiplicity a)) +
      (∑ j, (b j : K[X]).rootMultiplicity a) = k * (M-1) := by
    rw [← Finset.sum_add_distrib]
    simp only [Nat.sub_add_cancel (hbd _), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  omega


lemma sum_fin_val_le_square (h : ℕ) : (∑ j : Fin h, j.val) ≤ h*h := by
  calc
    _ ≤ ∑ _j : Fin h, h := Finset.sum_le_sum fun j _ => Nat.le_of_lt j.isLt
    _ = h*h := by simp

lemma expansion_numeric (w B M N k l : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N + 2*w^3*B) (hk : 1 ≤ k) (hkB : k ≤ B)
    (hh : w * (k*(M-1)) ≤ k*(N-1) + w*(∑ j : Fin k, j.val) +
      (l*(M-1) + w*(∑ j : Fin l, j.val))) :
    (w-1)*k < l := by
  by_contra! hl
  have hk2 := sum_fin_val_le_square k
  have hl2 := sum_fin_val_le_square l
  have hh' : w*(k*(M-1)) ≤ k*(N-1) + w*(k*k) +
      (l*(M-1) + w*(l*l)) := by
    exact hh.trans (by gcongr)
  have hgap : M-1 = N-1 + 2*w^3*B := by omega
  have hw' : w-1+1 = w := by omega
  have hmul := Nat.mul_le_mul_right (M-1) hl
  have hlSq : l*l ≤ ((w-1)*k)*((w-1)*k) := Nat.mul_self_le_mul_self hl
  have hwSq : (w-1)*(w-1)+1 ≤ w*w := by nlinarith
  have hsq : k*k + l*l ≤ w*w*(k*k) := by
    have hm := Nat.mul_le_mul_right (k*k) hwSq
    linarith
  have hkSq : k*k ≤ B*k := Nat.mul_le_mul_right k hkB
  have hfinal : w*(k*k + l*l) ≤ w^3*B*k := by
    calc
      _ ≤ w*(w*w*(k*k)) := Nat.mul_le_mul_left w hsq
      _ ≤ w*(w*w*(B*k)) := by gcongr
      _ = w^3*B*k := by ring
  have hB : 0 < B := by omega
  have hpos : 0 < w^3*B*k := by positivity
  have hbase : k*(M-1) ≤ k*(N-1)+w*(k*k+l*l) := by
    have he : w*(k*(M-1)) = k*(M-1) + (w-1)*k*(M-1) := by
      calc
        _ = (1+(w-1))*(k*(M-1)) := by congr 1; omega
        _ = _ := by ring
    have hb : w*(k*(M-1)) ≤ k*(N-1)+w*(k*k+l*l)+(w-1)*k*(M-1) := by
      calc
        _ ≤ k*(N-1)+w*(k*k)+((w-1)*k*(M-1)+w*(l*l)) :=
          hh'.trans (by gcongr)
        _ = _ := by ring
    rw [he] at hb
    exact Nat.le_of_add_le_add_right hb
  have hneed : k*(2*w^3*B) ≤ w*(k*k+l*l) := by
    rw [hgap] at hbase
    linarith only [hbase]
  linarith

lemma reduced_degree_bound {M N : ℕ} (U : Submodule (F K) (Fin M → F K))
    (hU : ∀ x ∈ U, ∀ j : Fin M, N ≤ j.val → x j = 0) :
    ∀ f ∈ polynomialSpace (reducedSubspace U), f ≠ 0 → f.natDegree < N := by
  have hr : ∀ y ∈ reducedSubspace U, ∀ j : Fin M, N ≤ j.val → y j = 0 := by
    intro y hy
    obtain ⟨b⟩ := exists_integralFrame U
    have hyy : y ∈ ReducedSet U := by
      rw [reducedSet_eq_span b]
      rwa [reducedSubspace_eq_span b] at hy
    obtain ⟨x, hx, hI, rfl⟩ := hyy
    intro j hj
    simp only [reduce, hU x hx j hj, reduction_zero]
  rintro f ⟨x, hx, rfl⟩ hn
  apply (natDegree_lt_iff_degree_lt hn).mpr
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  by_cases hjM : j < M
  · exact (polynomialMap_coeff M x ⟨j, hjM⟩).trans (hr x hx ⟨j, hjM⟩ hj)
  · exact polynomialMap_coeff_high M x j (Nat.le_of_not_gt hjM)

/-- Small-subspace expansion in monomial coordinates in a common output space.
The input subspace is restricted to degrees < N, not changed by padding. -/

theorem small_expansion [CharZero K] (w B M N : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N + 2*w^3*B) (points : Fin w → K) (hp : Function.Injective points)
    (U W : Submodule (F K) (Fin M → F K))
    (hU : ∀ x ∈ U, ∀ j : Fin M, N ≤ j.val → x j = 0)
    (hW : ∀ i, U.map (testMap M (points i)) ≤ W)
    (hk : 1 ≤ finrank (F K) U) (hkB : finrank (F K) U ≤ B) :
    (w-1) * finrank (F K) U < finrank (F K) W := by
  classical
  let k := finrank (F K) U
  let l := finrank (F K) W
  let V := polynomialSpace (reducedSubspace U)
  let Z := polynomialSpace (reducedSubspace W)
  let : Module.Finite K V := by
    dsimp [V, polynomialSpace]
    exact Module.Finite.map (reducedSubspace U) (polynomialMap M)
  let : Module.Finite K Z := by
    dsimp [Z, polynomialSpace]
    exact Module.Finite.map (reducedSubspace W) (polynomialMap M)
  have hVdim : finrank K V = k := by
    rw [finrank_polynomialSpace, finrank_reducedSubspace]
  have hZdim : finrank K Z = l := by
    rw [finrank_polynomialSpace, finrank_reducedSubspace]
  let b : Basis (Fin k) K V := (Module.finBasis K V).reindex (finCongr hVdim)
  let c : Basis (Fin l) K Z := (Module.finBasis K Z).reindex (finCongr hZdim)
  have hV := reduced_degree_bound U hU
  have hZ := polynomialSpace_bound (reducedSubspace W)
  choose be hbe using (fun i : Fin w => exists_echelon_basis_at N V b hV (points i))
  choose ce hce using (fun i : Fin w => exists_echelon_basis_at M Z c hZ (points i))
  have horder := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => order_reversal_sum M (points i) U W (hW i) (be i) (ce i) (hbe i) (hce i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_add_distrib] at horder
  have hWrU := wronskian_order_bound N b points hp be hV hbe
  have hWrW := wronskian_order_bound M c points hp ce hZ hce
  exact expansion_numeric w B M N k l hw hN hMN hk hkB
    (horder.trans (Nat.add_le_add hWrU hWrW))

end
end RationalHitting.SmallExpansion

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Rectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.Rectangular
open Module Matrix
open scoped BigOperators Kronecker
noncomputable section
variable {F : Type*} [Field F]

lemma no_shrunk_subspace {w q e : ℕ} (he : 0 < e)
    (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F)
    (hX : Function.Injective (blockEval A X))
    (V W : Submodule F (Fin q → F))
    (hVW : ∀ i, V.map (A i).mulVecLin ≤ W) : finrank F V ≤ finrank F W := by
  let g : (Fin e → V) →ₗ[F] (Fin e → W) :=
    { toFun := fun v β => ⟨∑ i, ∑ δ, X i β δ • (A i).mulVec (v δ), by
        apply W.sum_mem
        intro i _
        apply W.sum_mem
        intro δ _
        exact W.smul_mem _ (hVW i ⟨v δ, (v δ).property, rfl⟩)⟩
      map_add' := by
        intro v u
        funext β
        apply Subtype.ext
        simp only [Submodule.coe_add, Pi.add_apply, Matrix.mulVec_add,
          smul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        funext β
        apply Subtype.ext
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply,
          Matrix.mulVec_smul, Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro δ _
        rw [mul_comm] }
  have hg : Function.Injective g := by
    intro v u h
    have hh : blockEval A X (fun δ => (v δ : Fin q → F)) =
        blockEval A X (fun δ => (u δ : Fin q → F)) := by
      funext β
      exact congrArg Subtype.val (congrFun h β)
    have heq := hX hh
    funext δ
    exact Subtype.ext (congrFun heq δ)
  have hd := LinearMap.finrank_le_finrank_of_injective hg
  simp only [Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hd
  exact Nat.le_of_mul_le_mul_left hd he


variable {P Q : Type*} [AddCommGroup P] [Module F P]
  [AddCommGroup Q] [Module F Q]

lemma span_component_top {q : ℕ} (f : Fin q → P) :
    Submodule.span F (Set.range (component (F := F) f)) = ⊤ := by
  apply Submodule.map_injective_of_injective (componentSpace (F := F) f).injective_subtype
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
  rfl

lemma rank_coefficientMatrix {q k : ℕ} (f : Fin q → P)
    (b : Basis (Fin k) F (componentSpace (F := F) f)) : (coefficientMatrix f b).rank = k := by
  have hs : Submodule.span F (Set.range (coefficientMatrix f b)) = ⊤ := by
    have hh := congrArg (Submodule.map b.equivFun.toLinearMap) (span_component_top f)
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr b.equivFun.surjective] at hh
    exact hh
  rw [Matrix.rank_eq_finrank_span_row]
  change finrank F (Submodule.span F (Set.range (coefficientMatrix f b))) = k
  rw [hs]
  simp

lemma coefficientMatrix_expansion {q k : ℕ} (f : Fin q → P)
    (b : Basis (Fin k) F (componentSpace (F := F) f)) (α : Fin q) :
    ∑ j, (coefficientMatrix f b) α j • (b j : P) = f α := by
  simpa only [coefficientMatrix, Basis.equivFun_apply, Submodule.coe_sum,
    Submodule.coe_smul, component] using congrArg Subtype.val (b.sum_repr (component (F := F) f α))

lemma concat_row_relation {w q k : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F) (T : Fin w → P →ₗ[F] Q)
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f))
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • T i (f γ) = 0) (α : Fin q) :
    (concatMatrix A (coefficientMatrix f b)).row α ∈
      (imageCombination T (fun j => (b j : P))).ker := by
  rw [LinearMap.mem_ker]
  change (∑ ij : Fin w × Fin k,
    (∑ γ, A ij.1 α γ * coefficientMatrix f b γ ij.2) • T ij.1 (b ij.2 : P)) = 0
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_smul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  simp_rw [mul_smul, ← Finset.smul_sum, ← map_smul, ← map_sum,
    coefficientMatrix_expansion]
  exact hker α

lemma rank_concat_lt {w q k : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F) (T : Fin w → P →ₗ[F] Q)
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f))
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • T i (f γ) = 0)
    (hex : (w-1)*k < finrank F (imageCombination T (fun j => (b j : P))).range)
    (hw : 1 ≤ w) : (concatMatrix A (coefficientMatrix f b)).rank < k := by
  let H := imageCombination T (fun j => (b j : P))
  have hle : Submodule.span F (Set.range (concatMatrix A (coefficientMatrix f b)).row) ≤
      H.ker := by
    rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact concat_row_relation A T f b hker α
  have hr := Submodule.finrank_mono hle
  rw [← Matrix.rank_eq_finrank_span_row] at hr
  have hd := H.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin] at hd
  have hw' : (w-1)*k+k = w*k := by
    calc
      _ = (w-1+1)*k := by ring
      _ = _ := by congr 1; omega
  change (w-1)*k < finrank F H.range at hex
  omega

lemma coefficient_image_le_concat {w q k : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F) (P : Matrix (Fin q) (Fin k) F) (i : Fin w) :
    (Submodule.span F (Set.range P.col)).map (A i).mulVecLin ≤
      Submodule.span F (Set.range (concatMatrix A P).col) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨v, ⟨j, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨(i,j), ?_⟩
  funext α
  simp [concatMatrix, Matrix.mulVec, Matrix.mul_apply, dotProduct]


lemma component_image_le_range {w q k : ℕ} (T : Fin w → P →ₗ[F] Q)
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f)) (i : Fin w) :
    (componentSpace (F := F) f).map (T i) ≤
      (imageCombination T (fun j => (b j : P))).range := by
  rw [imageCombination, Fintype.range_linearCombination]
  rintro _ ⟨x, hx, rfl⟩
  have he : (∑ j, (b.repr ⟨x,hx⟩) j • (b j : P)) = x := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val (b.sum_repr ⟨x,hx⟩)
  rw [← he, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(i,j), rfl⟩

/-- A kernel vector with sufficiently expansive component span contradicts
any invertible block evaluation of the same coefficient matrices. -/
theorem kernel_impossible {w q k e : ℕ} (hw : 1 ≤ w) (he : 0 < e)
    (A : Fin w → Matrix (Fin q) (Fin q) F) (T : Fin w → P →ₗ[F] Q)
    (X : Fin w → Matrix (Fin e) (Fin e) F)
    (hX : Function.Injective (blockEval A X))
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f))
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • T i (f γ) = 0)
    (hex : (w-1)*k < finrank F (imageCombination T (fun j => (b j : P))).range) :
    False := by
  let Pmat := coefficientMatrix f b
  let Cmat := concatMatrix A Pmat
  let V := Submodule.span F (Set.range Pmat.col)
  let W := Submodule.span F (Set.range Cmat.col)
  have hVW : ∀ i, V.map (A i).mulVecLin ≤ W :=
    fun i => coefficient_image_le_concat A Pmat i
  have hd := no_shrunk_subspace he A X hX V W hVW
  have hV : finrank F V = k := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact rank_coefficientMatrix f b
  have hW : finrank F W < k := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact rank_concat_lt A T f b hker hex hw
  omega


lemma blockMatrix_mulVec {w q e : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) (v : Fin e → Fin q → F)
    (α : Fin q) (β : Fin e) :
    (blockMatrix A X).mulVec (fun j => v j.2 j.1) (α,β) = blockEval A X v β α := by
  classical
  simp only [blockMatrix, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.kronecker_apply, Finset.sum_mul, Fintype.sum_prod_type,
    blockEval, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext δ; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro γ _
  ring

lemma blockEval_injective_of_isUnit {w q e : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) (h : IsUnit (blockMatrix A X)) :
    Function.Injective (blockEval A X) := by
  have hh := Matrix.mulVec_injective_iff_isUnit.mpr h
  intro v u hv
  have hflat : (fun j : Fin q × Fin e => v j.2 j.1) = (fun j => u j.2 j.1) := by
    apply hh
    funext j
    rw [blockMatrix_mulVec, blockMatrix_mulVec]
    exact congrFun (congrFun hv j.2) j.1
  funext β α
  exact congrFun hflat (α,β)

end
end RationalHitting.Rectangular


namespace RationalHitting.RectangularExpansion
open Module Matrix
open scoped BigOperators
open LaurentReduction SmallExpansion Rectangular
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The rectangular Taylor tests have no nonzero kernel component family when
the same coefficients have an invertible matrix witness. -/
theorem rectangular_kernel_zero (w B M N q e : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N + 2*w^3*B) (hq : q ≤ B) (he : 0 < e)
    (points : Fin w → K) (hp : Function.Injective points)
    (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (X : Fin w → Matrix (Fin e) (Fin e) (F K))
    (hX : Function.Injective (blockEval A X))
    (f : Fin q → Fin M → F K)
    (hf : ∀ α j, N ≤ j.val → f α j = 0)
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • testMap M (points i) (f γ) = 0) : f = 0 := by
  classical
  by_contra hn
  obtain ⟨α, hα⟩ : ∃ α, f α ≠ 0 := by
    by_contra! hh
    exact hn (funext hh)
  let U := componentSpace (F := F K) f
  let k := finrank (F K) U
  let b := Module.finBasis (F K) U
  let T := fun i => testMap M (points i)
  let W := (imageCombination T (fun j => (b j : Fin M → F K))).range
  have hk : 1 ≤ k := by
    apply finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨component (F := F K) f α, ?_⟩
    intro hz
    exact hα (congrArg Subtype.val hz)
  have hkq : k ≤ q := by
    simpa using finrank_le_of_span_eq_top (span_component_top (F := F K) f)
  have hU : ∀ x ∈ U, ∀ j : Fin M, N ≤ j.val → x j = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨α, rfl⟩ := hx; exact hf α
    | zero => intro j _; rfl
    | add x y _ _ hx hy => intro j hj; simp [hx j hj, hy j hj]
    | smul c x _ hx => intro j hj; simp [hx j hj]
  have hW : ∀ i, U.map (T i) ≤ W := fun i => component_image_le_range T f b i
  have hex := small_expansion w B M N hw hN hMN points hp U W hU hW hk (hkq.trans hq)
  exact kernel_impossible hw he A T X hX f b hker hex

end
end RationalHitting.RectangularExpansion

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.PaddedRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TestPolynomial
open Polynomial Matrix Module
open LaurentReduction SmallExpansion Rectangular RectangularExpansion
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

lemma polynomialMap_single (M : ℕ) (b : Fin M) :
    polynomialMap M (Pi.single b (1 : K)) = X^b.val := by
  ext j
  by_cases hj : j < M
  · rw [polynomialMap_coeff M _ ⟨j,hj⟩,coeff_X_pow]
    simp [Pi.single_apply,Fin.ext_iff,eq_comm]
  · rw [polynomialMap_coeff_high M _ j (Nat.le_of_not_gt hj)]
    rw [coeff_X_pow]
    have hb : b.val ≠ j := by omega
    simp [Ne.symm hb]

lemma taylorCoordinates_symm (M : ℕ) (a : K) :
    (taylorCoordinates M a).symm = taylorCoordinates M (-a) := by
  ext x i
  rfl

lemma reverseCoordinates_symm_apply (M : ℕ) (x : Fin M → K) :
    (reverseCoordinates M).symm x = fun j => x j.rev := rfl

lemma reverseTaylor_symm_matrix (M : ℕ) (a : K) (i j : Fin M) :
    LinearMap.toMatrix' (reverseTaylorCoordinates M a).symm.toLinearMap i j =
      (((X + C (-a))^j.rev.val : K[X]).coeff i.val) := by
  rw [LinearMap.toMatrix'_apply]
  simp only [reverseTaylorCoordinates, LinearEquiv.trans_symm,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, reverseCoordinates_symm_apply]
  rw [taylorCoordinates_symm]
  have he : (fun k : Fin M => (Pi.single j (1 : K) : Fin M → K) k.rev) =
      (Pi.single j.rev (1 : K) : Fin M → K) := by
    funext k
    simp only [Pi.single_apply]
    have hh : k.rev = j ↔ k = j.rev := by
      constructor <;> intro h
      · rw [← Fin.rev_rev k,h]
      · rw [h,Fin.rev_rev]
    congr 1
    exact propext hh
  rw [he,taylorCoordinates_apply,polynomialMap_single,taylor_X_pow]

lemma embed_C (a : K) : embed (C a) = HahnSeries.C a := by simp [embed]
lemma embed_X_pow (a : ℕ) : embed ((X : K[X])^a) = HahnSeries.single (a : ℤ) 1 := by
  simp [embed,HahnSeries.single_pow]

lemma full_embed (M : ℕ) (a : K) :
    (embed.mapMatrix (full M a)) = LinearMap.toMatrix' (testMap M a) := by
  apply Matrix.ext
  intro i j
  change embed (full M a i j) = testMap M a (Pi.single j 1) i
  simp only [full,map_sum,map_mul,embed_C,embed_X_pow]
  change _ = liftMap (reverseTaylorCoordinates M a).symm.toLinearMap
    (weightMap Fin.val (liftMap (taylorCoordinates M a).toLinearMap (Pi.single j 1))) i
  rw [liftMap_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [reverseTaylor_symm_matrix]
  have hin : liftMap (taylorCoordinates M a).toLinearMap (Pi.single j (1 : F K)) r =
      HahnSeries.C ((((X+C a)^j.val : K[X]).coeff r.val)) := by
    rw [liftMap_apply]
    simp [Pi.single_apply,taylorCoordinates_apply,polynomialMap_single]
  simp only [weightMap,LinearMap.coe_mk,AddHom.coe_mk,hin]
  ring

lemma full_natDegree_le (M : ℕ) (a : K) (i j : Fin M) :
    (full M a i j).natDegree ≤ M-1 := by
  apply natDegree_sum_le_of_forall_le
  intro r _
  apply (natDegree_C_mul_le _ _).trans
  simpa using Nat.le_sub_one_of_lt r.isLt

lemma padded_natDegree_le (M N : ℕ) (a : K) (i j : Fin M) :
    (padded M N a i j).natDegree ≤ M-1 := by
  by_cases hj : j.val < N
  · simpa [padded,hj] using full_natDegree_le M a i j
  · simp [padded,hj]

end
end RationalHitting.TestPolynomial

namespace RationalHitting.PaddedRank
open Matrix Module
open TestPolynomial LaurentReduction SmallExpansion Rectangular RectangularExpansion
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

lemma raw_apply.{v_1} {K : Type v_1} [Field K] [CharZero K] {w q M : ℕ}
  (A : Fin w → Matrix (Fin q) (Fin q) (RationalHitting.LaurentReduction.F K))
  (R : Fin w → Matrix (Fin M) (Fin M) (RationalHitting.LaurentReduction.F K))
  (f : Fin q × Fin M → RationalHitting.LaurentReduction.F K) (α : Fin q) (j : Fin M) :
  (RationalHitting.PaddedRank.raw A R).mulVec f (α, j) =
    ∑ i, ∑ γ, A i α γ * (R i).mulVec (fun b => f (γ, b)) j := by
  simp only [Matrix.mulVec, dotProduct, raw, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin w)))
    (t := (Finset.univ : Finset (Fin q)))]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma extend_low.{v_1} {K : Type v_1} [Field K] [CharZero K] (q M N : ℕ)
  (f : Fin q × Fin N → RationalHitting.LaurentReduction.F K) (α : Fin q) (j : Fin M) :
  N ≤ ↑j → (RationalHitting.PaddedRank.extend q M N) f (α, j) = 0 := by
  intro hj
  simp [extend,not_lt.mpr hj]

lemma extend_injective.{v_1} {K : Type v_1} [Field K] [CharZero K]
  (q M N : ℕ) (hNM : N ≤ M) :
  Function.Injective ⇑(RationalHitting.PaddedRank.extend (K := K) q M N) := by
  intro f g h
  funext ⟨α,j⟩
  have hh := congrFun h (α,⟨j.val,j.isLt.trans_le hNM⟩)
  simpa [extend,j.isLt] using hh

lemma padded_mulVec_low.{v_1} {K : Type v_1} [Field K] [CharZero K] (M N : ℕ)
  (a : K) (f : Fin M → RationalHitting.LaurentReduction.F K)
  (hf : ∀ (j : Fin M), N ≤ ↑j → f j = 0) :
  (RationalHitting.TestPolynomial.embed.mapMatrix
          (RationalHitting.TestPolynomial.padded M N a)).mulVec
      f =
    (RationalHitting.SmallExpansion.testMap M a) f := by
  rw [← Matrix.toLin'_toMatrix' (testMap M a), ← full_embed M a, Matrix.toLin'_apply]
  funext i
  simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < N
  · simp [padded,hj]
  · simp [padded,hj,hf j (Nat.le_of_not_gt hj)]

/-- The padded test matrices satisfy a rectangular rank lower bound,
using an invertible witness and the expansion theorem. -/
theorem rank_ge (w B M N q e : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N+2*w^3*B) (hq : q ≤ B) (he : 0 < e)
    (points : Fin w → K) (hp : Function.Injective points)
    (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (X : Fin w → Matrix (Fin e) (Fin e) (F K))
    (hX : Function.Injective (blockEval A X)) :
    q*N ≤ (raw A (fun i => embed.mapMatrix (padded M N (points i)))).rank := by
  let R := fun i => embed.mapMatrix (padded M N (points i))
  let L := (raw A R).mulVecLin.comp (extend q M N)
  have hi : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    let f : Fin q → Fin M → F K := fun α j => extend q M N v (α,j)
    have hf : ∀ α j, N ≤ j.val → f α j = 0 := extend_low q M N v
    have hker : ∀ α, ∑ i, ∑ γ, A i α γ • testMap M (points i) (f γ) = 0 := by
      intro α
      funext j
      have hh := congrFun hv (α,j)
      change (raw A R).mulVec (extend q M N v) (α,j) = 0 at hh
      rw [raw_apply] at hh
      simpa only [R, f, padded_mulVec_low M N _ _ (hf _),
        Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hh
    have hzero := rectangular_kernel_zero w B M N q e hw hN hMN hq he points hp A X hX f hf hker
    have hext : extend q M N v = 0 := by
      funext ⟨α,j⟩
      exact congrFun (congrFun hzero α) j
    apply extend_injective q M N (by omega)
    simpa only [map_zero] using hext
  let E := LinearMap.toMatrix' (extend (K := K) q M N)
  have hE : E.mulVecLin = extend q M N := Matrix.toLin'_toMatrix' _
  have hr : (raw A R * E).rank = q*N := by
    rw [Matrix.rank,Matrix.mulVecLin_mul,hE]
    rw [LinearMap.finrank_range_of_inj hi]
    simp
  exact hr ▸ Matrix.rank_mul_le_left (raw A R) E

lemma numeric_gap (w B M N q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hMN : M = N+2*w^3*B) (hM : B*(2*w^3*B) < M) : (q-1)*M < q*N := by
  have hh : q*(2*w^3*B) < M := (Nat.mul_le_mul_right _ hqB).trans_lt hM
  have hq' : q-1+1=q := by omega
  have heq : q*M = (q-1)*M+M := by
    calc
      _ = (q-1+1)*M := by rw [hq']
      _ = _ := by ring
  have heq' : q*N+q*(2*w^3*B) = (q-1)*M+M := by
    calc
      _ = q*M := by rw [hMN]; ring
      _ = _ := heq
  omega

end
end RationalHitting.PaddedRank

namespace RationalHitting.TestPolynomial
open Polynomial Matrix
open LaurentReduction
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [Field E]

lemma map_taylor_coeff (φ : K →+* E) (a : K) (j r : ℕ) :
    φ (((X+C a)^j : K[X]).coeff r) = (((X+C (φ a))^j : E[X]).coeff r) := by
  rw [← Polynomial.coeff_map]
  simp

lemma full_map (φ : K →+* E) (M : ℕ) (a : K) (i j : Fin M) :
    (full M a i j).map φ = full M (φ a) i j := by
  unfold full
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_mul]
  rw [map_taylor_coeff φ (-a),map_taylor_coeff φ a,map_neg]

lemma padded_map (φ : K →+* E) (M N : ℕ) (a : K) (i j : Fin M) :
    (padded M N a i j).map φ = padded M N (φ a) i j := by
  by_cases hj : j.val < N <;> simp [padded,hj,full_map]

lemma eval₂_padded (φ : K →+* E) (M N : ℕ) (a : K) (i j : Fin M) :
    (padded M N a i j).eval₂ (HahnSeries.C.comp φ) (HahnSeries.single 1 1) =
      embed (padded M N (φ a) i j) := by
  rw [← padded_map φ M N a i j]
  change (padded M N a i j).eval₂ ((HahnSeries.C : E →+* F E).comp φ) (HahnSeries.single (1 : ℤ) 1) =
    ((padded M N a i j).map φ).eval₂ HahnSeries.C (HahnSeries.single 1 1)
  rw [Polynomial.eval₂_map]

end
end RationalHitting.TestPolynomial

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.QuantumMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.QuantumMatrices
open Matrix
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K) (hχ : χ.IsPrimitive)

lemma orthogonality.{v_1} {K : Type v_1} [Field K] [CharZero K] {d : ℕ}
  [NeZero d] (χ : AddChar (ZMod d) K) (hχ : χ.IsPrimitive) (x : ZMod d) :
  ∑ a, χ (a * x) = if x = 0 then ↑d else 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx, ZMod.card]
  · rw [ite_eq_right hx]
    simpa [AddChar.mulShift_apply, mul_comm] using AddChar.sum_eq_zero_of_ne_one (hχ hx)

include hχ in
/-- Fourier inversion on each cyclic matrix diagonal. -/

theorem fourier_reconstruction (R : Matrix (ZMod d) (ZMod d) K) :
    (∑ a, ∑ b, fourierCoeff χ R a b • weyl χ a b) = R := by
  classical
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, weyl]
  simp_rw [mul_ite, mul_zero]
  have heq (a : ZMod d) :
      (∑ b, if i = j+b then fourierCoeff χ R a b * χ (a*i) else 0) =
      fourierCoeff χ R a (i-j) * χ (a*i) := by
    rw [Finset.sum_eq_single (i-j)]
    · simp
    · intro b hb hne
      rw [ite_eq_right]
      intro h
      apply hne
      linear_combination -h
    · simp
  simp_rw [heq, fourierCoeff, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hc (k : ZMod d) :
      (∑ a, χ (-a*k) * R k (k-(i-j)) * χ (a*i)) =
      (if i = k then (d : K) else 0) * R k (k-(i-j)) := by
    calc
      _ = (∑ a, χ (a*(i-k))) * R k (k-(i-j)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        rw [mul_right_comm, ← AddChar.map_add_eq_mul]
        congr 2
        ring
      _ = _ := by simp only [orthogonality χ hχ, sub_eq_zero]
  simp_rw [hc]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [Nat.cast_ne_zero.mpr (NeZero.ne d)]

end
end RationalHitting.QuantumMatrices


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BlockDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.PolynomialHahn
open HahnSeries MvPolynomial
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

lemma exponent_injective : Function.Injective exponent := by
  intro m n h
  have h' : ((m 0 : ℤ), (m 1 : ℤ)) = ((n 0 : ℤ), (n 1 : ℤ)) := congrArg ofLex h
  ext i
  fin_cases i
  · exact Int.ofNat.inj (by simpa using congrArg Prod.fst h')
  · exact Int.ofNat.inj (by simpa using congrArg Prod.snd h')

lemma embed_monomial (m : Fin 2 →₀ ℕ) (a : K) :
    embed (monomial m a) = single (exponent m) a := by
  rw [embed, eval₂Hom_monomial, Finsupp.prod_fintype _ _ (by simp)]
  have he : (m 0 : Exponents) * toLex (1,0) + (m 1 : Exponents) * toLex (0,1) =
      exponent m := by
    change toLex ((m 0 : ℤ)*1+(m 1 : ℤ)*0, (m 0 : ℤ)*0+(m 1 : ℤ)*1) = _
    simp [exponent]
  simp [variableSeries, Fin.prod_univ_two, HahnSeries.single_pow,
    HahnSeries.single_mul_single, HahnSeries.algebraMap_apply, HahnSeries.C_apply, he]

lemma embed_coeff (p : MvPolynomial (Fin 2) K) (m : Fin 2 →₀ ℕ) :
    (embed p).coeff (exponent m) = p.coeff m := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum, HahnSeries.coeff_sum]
  simp_rw [embed_monomial, HahnSeries.coeff_single]
  simp only [exponent_injective.eq_iff]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (not_not.mp (mt mem_support_iff.mpr h)).symm

lemma embed_injective : Function.Injective (embed (K := K)) := by
  intro p q hpq
  ext m
  have h := congrArg (fun x : HahnSeries Exponents K => x.coeff (exponent m)) hpq
  simpa only [embed_coeff] using h

end
end RationalHitting.PolynomialHahn


namespace RationalHitting.BlockDivision
open Module Matrix
open scoped BigOperators
noncomputable section
variable {D E : Type*} [DivisionRing D] [Field E]
variable {m κ : Type*} [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

lemma unit_of_vecMul_injective (A : Matrix (m) (m) D)
    (hA : Function.Injective A.vecMulLinear) : IsUnit A := by
  let e := LinearEquiv.ofBijective A.vecMulLinear
    ⟨hA, (LinearMap.injective_iff_surjective).mp hA⟩
  let B := e.symm.toLinearMap.toMatrixRight'
  have hAB : A * B = 1 := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
    change (LinearMap.toMatrixRight'.symm (LinearMap.toMatrixRight' e.symm.toLinearMap)).comp
      e.toLinearMap = LinearMap.id
    rw [LinearEquiv.symm_apply_apply]
    exact e.symm_comp
  have hBA : B * A = 1 := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
    change e.toLinearMap.comp
      (LinearMap.toMatrixRight'.symm (LinearMap.toMatrixRight' e.symm.toLinearMap)) = LinearMap.id
    rw [LinearEquiv.symm_apply_apply]
    exact e.comp_symm

  exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩

lemma kernelRows_injective.{v_1, v_2, v_3, v_4}
    {D : Type v_1} {E : Type v_2} [DivisionRing D] [Field E]
    {m : Type v_3} {κ : Type v_4} [Fintype m] [DecidableEq m]
    [Fintype κ] [DecidableEq κ] (φ : D →+* Matrix (κ) (κ) E)
    (v : m → D) (hv : v ≠ 0) : Function.Injective (kernelRows φ v) := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! hh
    exact hv (funext hh)
  have hunit : IsUnit (φ (v j)) := (isUnit_iff_ne_zero.mpr hj).map φ
  intro x y h
  apply Matrix.vecMul_injective_of_isUnit hunit
  funext α
  exact congrFun h (j,α)

lemma kernelRows_mem (φ : D →+* Matrix (κ) (κ) E)
    (A : Matrix (m) (m) D) (v : m → D)
    (hv : v ᵥ* A = 0) (x : κ → E) :
    kernelRows φ v x ∈ (blockEmbedding φ A).vecMulLinear.ker := by
  change (kernelRows φ v x) ᵥ* (blockEmbedding φ A) = 0
  funext ⟨j,β⟩
  have hh := congrArg (fun z : D => (x ᵥ* φ z) β) (congrFun hv j)
  change (∑ i : m × κ,
    (∑ γ, x γ * φ (v i.1) γ i.2) * φ (A i.1 j) i.2 β) = 0
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, mul_assoc]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have heq : (∑ γ, ∑ i, ∑ α, x γ * (φ (v i) γ α * φ (A i j) α β)) =
      (x ᵥ* φ ((v ᵥ* A) j)) β := by
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Matrix.sum_apply,
      Matrix.mul_apply, Finset.mul_sum]
  rw [heq, hv]
  simp


/-- The rank gap obtained by block elimination over a division ring. -/

theorem rank_gap (φ : D →+* Matrix (κ) (κ) E)
    (A : Matrix (m) (m) D) :
    IsUnit (blockEmbedding φ A) ∨ (blockEmbedding φ A).rank + Fintype.card κ ≤ Fintype.card m * Fintype.card κ := by
  classical
  by_cases hu : IsUnit (blockEmbedding φ A)
  · exact Or.inl hu
  right
  have hn : ¬ Function.Injective A.vecMulLinear := by
    intro h
    exact hu ((unit_of_vecMul_injective A h).map (blockEmbedding φ))
  have hk : A.vecMulLinear.ker ≠ ⊥ := by
    intro h
    exact hn (LinearMap.ker_eq_bot.mp h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  let g : (κ → E) →ₗ[E] (blockEmbedding φ A).vecMulLinear.ker :=
    (kernelRows φ v).codRestrict _ (kernelRows_mem φ A v hv)
  have hg : Function.Injective g := by
    intro x y h
    exact kernelRows_injective φ v hv0 (congrArg Subtype.val h)
  have hdim := LinearMap.finrank_le_finrank_of_injective hg
  have hrank := (blockEmbedding φ A).vecMulLinear.finrank_range_add_finrank_ker
  have heq : finrank E (blockEmbedding φ A).vecMulLinear.range =
      (blockEmbedding φ A).rank := by
    rw [← Matrix.mulVecLin_transpose, ← Matrix.rank, Matrix.rank_transpose]
  rw [heq] at hrank
  simp only [Module.finrank_pi, Fintype.card_prod] at hdim hrank
  omega

theorem isUnit_of_rank_gt (φ : D →+* Matrix (κ) (κ) E)
    (A : Matrix (m) (m) D) (hq : 1 ≤ Fintype.card m)
    (h : (Fintype.card m-1)*Fintype.card κ < (blockEmbedding φ A).rank) : IsUnit (blockEmbedding φ A) := by
  rcases rank_gap φ A with hunit | hgap
  · exact hunit
  have heq : (Fintype.card m-1)*Fintype.card κ+Fintype.card κ = Fintype.card m * Fintype.card κ := by
    calc
      _ = (Fintype.card m-1+1)*Fintype.card κ := by ring
      _ = Fintype.card m * Fintype.card κ := by rw [Nat.sub_add_cancel hq]
  omega

end
end RationalHitting.BlockDivision


namespace RationalHitting.RankSpecialization
open Matrix
noncomputable section
variable {K P E ι : Type*} [Field K] [CommRing P] [Field E]
  [Algebra K P] [Fintype ι] [DecidableEq ι]

/-- Specialization cannot raise the generic rank. This version requires no
unstated minor criterion: a rank normal form supplies a nonzero minor after
constant row and column changes. -/
theorem rank_le (ev : P →ₐ[K] K) (inclusion : P →+* E)
    (hinj : Function.Injective inclusion) (A : Matrix ι ι P) :
    (ev.toRingHom.mapMatrix A).rank ≤ (inclusion.mapMatrix A).rank := by
  classical
  let S := ev.toRingHom.mapMatrix A
  obtain ⟨V,U,e,hV,hU,hform⟩ := Matrix.exists_rank_normal_form S
  let c := algebraMap K P
  let T := c.mapMatrix V * A * c.mapMatrix U
  let j : Fin S.rank → ι := fun i => e.symm (Sum.inl i)
  have hT : ev.toRingHom.mapMatrix T = V*S*U := by
    dsimp [T]
    rw [map_mul, map_mul]
    congr 2
    · ext i j; exact ev.commutes (V i j)
    · ext i j; exact ev.commutes (U i j)
  have hminor : ev.toRingHom.mapMatrix (T.submatrix j j) = 1 := by
    change (ev.toRingHom.mapMatrix T).submatrix j j = 1
    rw [hT, hform]
    ext i k
    simp [j, Matrix.submatrix, Matrix.one_apply]
  have hdet : (T.submatrix j j).det ≠ 0 := by
    intro hz
    have h := ev.toRingHom.map_det (T.submatrix j j)
    rw [hz, map_zero, hminor, det_one] at h
    exact zero_ne_one h
  have hdetE : (inclusion.mapMatrix (T.submatrix j j)).det ≠ 0 := by
    rw [← inclusion.map_det]
    exact fun h => hdet (hinj (h.trans (map_zero inclusion).symm))
  have hrk := Matrix.rank_of_det_ne_zero hdetE
  have hsub : (inclusion.mapMatrix (T.submatrix j j)).rank ≤
      (inclusion.mapMatrix T).rank :=
    Matrix.rank_submatrix_le (inclusion.mapMatrix T) j j
  have hmul : (inclusion.mapMatrix T).rank ≤ (inclusion.mapMatrix A).rank := by
    dsimp [T]
    rw [map_mul, map_mul]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  simp only [Fintype.card_fin] at hrk
  exact hrk ▸ hsub.trans hmul

end
end RationalHitting.RankSpecialization

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Deformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.QuantumLift
open HahnSeries Matrix MvPolynomial
open RationalHitting.QuantumMatrices RationalHitting.PolynomialHahn
open RationalHitting.BlockDivision
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

lemma polynomialLift_embed (R : Matrix (ZMod d) (ZMod d) K) :
    PolynomialHahn.embed.mapMatrix (polynomialLift χ R) = representation χ (liftD χ R) := by
  ext i j g
  change (PolynomialHahn.embed (polynomialLift χ R i j)).coeff g = (lift χ R).coeff g i j
  simp only [polynomialLift, map_sum, HahnSeries.coeff_sum, embed_monomial,
    lift, Matrix.sum_apply, ]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have he : exponent (Finsupp.single 0 a.val + Finsupp.single 1 b.val) =
      toLex ((a.val : ℤ), (b.val : ℤ)) := by simp [exponent]
  rw [he]
  simp only [HahnSeries.coeff_single]
  split_ifs <;> rfl

lemma polynomialLift_specialize (hχ : χ.IsPrimitive) (R : Matrix (ZMod d) (ZMod d) K) :
    (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))).toRingHom.mapMatrix
      (polynomialLift χ R) = R := by
  have h := fourier_reconstruction χ hχ R
  ext i j
  have hij := congrFun (congrFun h i) j
  simpa [polynomialLift, eval_monomial, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul] using hij

variable {m : Type*} [Fintype m] [DecidableEq m]

lemma blockPolynomial_embed (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    PolynomialHahn.embed.mapMatrix (blockPolynomial χ A) =
      blockEmbedding (representation χ) (fun i j => liftD χ (A i j)) := by
  funext ⟨i,a⟩ ⟨j,b⟩
  exact congrFun (congrFun (polynomialLift_embed χ (A i j)) a) b

lemma blockPolynomial_specialize (hχ : χ.IsPrimitive)
    (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))).toRingHom.mapMatrix
      (blockPolynomial χ A) = blockOriginal A := by
  funext ⟨i,a⟩ ⟨j,b⟩
  exact congrFun (congrFun (polynomialLift_specialize χ hχ (A i j)) a) b

/-- The rank gap forces the determinant of the actual polynomial lift to be
nonzero. The Hahn division ring is only a proof device; the resulting polynomial
is the original finite Fourier lift, not a new generator. -/
theorem blockPolynomial_det_ne_zero (hχ : χ.IsPrimitive)
    (A : Matrix m m (Matrix (ZMod d) (ZMod d) K))
    (hm : 1 ≤ Fintype.card m)
    (hA : (Fintype.card m - 1)*d < (blockOriginal A).rank) :
    (blockPolynomial χ A).det ≠ 0 := by
  let B := blockPolynomial χ A
  have hrank := RationalHitting.RankSpecialization.rank_le
    (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))) PolynomialHahn.embed
    PolynomialHahn.embed_injective B
  rw [blockPolynomial_specialize χ hχ, blockPolynomial_embed] at hrank
  have hu := isUnit_of_rank_gt (representation χ) (fun i j => liftD χ (A i j)) hm
    (by simpa [ZMod.card] using hA.trans_le hrank)
  have hdet : (PolynomialHahn.embed.mapMatrix B).det ≠ 0 := by
    rw [blockPolynomial_embed]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hu |>.ne_zero
  intro hz
  rw [← RingHom.map_det, hz, map_zero] at hdet
  exact hdet rfl

end
end RationalHitting.QuantumLift

namespace RationalHitting.ThreeLift
open Matrix Polynomial MvPolynomial
open QuantumMatrices QuantumLift
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [Field E] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

lemma specialize_uni (φ : K →+* E) (t : E) (p : K[X]) :
    specialize φ t (uni p) = MvPolynomial.C (p.eval₂ φ t) := by
  have he : (specialize φ t).comp uni =
      MvPolynomial.C.comp (Polynomial.eval₂RingHom φ t) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [specialize,uni]
    · simp [specialize,uni]
  exact congrArg (fun h : K[X] →+* MvPolynomial (Fin 2) E => h p) he

lemma coeffP_eval (φ : K →+* E) (t : E)
    (R : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) :
    (coeffP χ R a b).eval₂ φ t =
      QuantumMatrices.fourierCoeff (φ.toMonoidHom.compAddChar χ) ((Polynomial.eval₂RingHom φ t).mapMatrix R) a b := by
  simp [coeffP,QuantumMatrices.fourierCoeff,Polynomial.eval₂_mul,Polynomial.eval₂_finsetSum]

lemma weyl_map.{v_1, v_2} {K : Type v_1} {E : Type v_2} [Field K] [Field E]
  {d : ℕ} [NeZero d] (χ : AddChar (ZMod d) K) (φ : K →+* E) (a b i j : ZMod d) :
  φ (weyl χ a b i j) = weyl (φ.toMonoidHom.compAddChar χ) a b i j := by
  by_cases h : i = j+b <;> simp [weyl,h]

lemma specialize_lift (φ : K →+* E) (t : E)
    (R : Matrix (ZMod d) (ZMod d) K[X]) :
    (specialize φ t).mapMatrix (lift χ R) =
      polynomialLift (φ.toMonoidHom.compAddChar χ) ((Polynomial.eval₂RingHom φ t).mapMatrix R) := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply,Matrix.map_apply,lift,map_sum,map_mul,map_pow,
    specialize_uni,coeffP_eval]
  simp only [specialize,eval₂Hom_X',eval₂Hom_C,RingHom.comp_apply,weyl_map,polynomialLift]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial,map_mul]
  rfl

lemma uni_totalDegree_le (p : K[X]) : (uni p).totalDegree ≤ p.natDegree := by
  classical
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  simp only [map_sum,map_mul,map_pow]
  apply totalDegree_finsetSum_le
  intro j hj
  simp only [uni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,Polynomial.eval₂_X]
  apply (totalDegree_mul _ _).trans
  apply (Nat.add_le_add (totalDegree_C _).le (totalDegree_pow _ _)).trans
  simp only [zero_add,totalDegree_X,Nat.mul_one]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)

lemma coeffP_natDegree_le (R : Matrix (ZMod d) (ZMod d) K[X]) (D : ℕ)
    (hR : ∀ i j, (R i j).natDegree ≤ D) (a b : ZMod d) :
    (coeffP χ R a b).natDegree ≤ D := by
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hR _ _)

lemma lift_totalDegree_le (R : Matrix (ZMod d) (ZMod d) K[X]) (D : ℕ)
    (hR : ∀ i j, (R i j).natDegree ≤ D) (i j : ZMod d) :
    (lift χ R i j).totalDegree ≤ D+2*(d-1) := by
  apply totalDegree_finsetSum_le
  intro a _
  apply totalDegree_finsetSum_le
  intro b _
  apply (totalDegree_mul _ _).trans
  apply (Nat.add_le_add (totalDegree_mul _ _) (totalDegree_pow _ _)).trans
  apply (Nat.add_le_add (Nat.add_le_add (totalDegree_mul _ _) (totalDegree_pow _ _)) le_rfl).trans
  simp only [totalDegree_C,totalDegree_X,Nat.mul_one,Nat.add_zero]
  have hh := (uni_totalDegree_le (coeffP χ R a b)).trans (coeffP_natDegree_le χ R D hR a b)
  have ha : a.val ≤ d-1 := Nat.le_sub_one_of_lt (ZMod.val_lt a)
  have hb : b.val ≤ d-1 := Nat.le_sub_one_of_lt (ZMod.val_lt b)
  omega

end
end RationalHitting.ThreeLift

namespace RationalHitting.PencilDeformation
open Matrix Polynomial MvPolynomial
open TestPolynomial LaurentReduction
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
variable {w q M N : ℕ} [NeZero M]

lemma specialize.{v_1, v_2} {K : Type v_1} {E : Type v_2} [Field K]
  [CharZero K] [Field E] [CharZero E] {w q M N : ℕ} [NeZero M] (χ : AddChar (ZMod M) K)
  (φ : K →+* E) (t : E) (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
  (ThreeLift.specialize φ t).mapMatrix (polynomial (N := N) χ A points) =
    QuantumLift.blockPolynomial (φ.toMonoidHom.compAddChar χ)
      (fun α β => (Polynomial.eval₂RingHom φ t).mapMatrix
        (polyBlocks (M := M) (N := N) A points α β)) := by
  funext ⟨α,i⟩ ⟨β,j⟩
  exact congrFun (congrFun (ThreeLift.specialize_lift χ φ t (polyBlocks A points α β)) i) j

lemma raw_specialize.{v_1, v_2} {K : Type v_1} {E : Type v_2}
  [Field K] [CharZero K] [Field E] [CharZero E] {w q M N : ℕ} [NeZero M] (φ : K →+* E)
  (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
  QuantumLift.blockOriginal
      (fun α β => (Polynomial.eval₂RingHom ((HahnSeries.C : E →+* F E).comp φ)
        (HahnSeries.single 1 1)).mapMatrix (polyBlocks (M := M) (N := N) A points α β)) =
    (PaddedRank.raw (fun i => ((HahnSeries.C : E →+* F E).comp φ).mapMatrix (A i))
      (fun i => embed.mapMatrix (padded M N (φ (points i))))).reindex
        (Equiv.prodCongr (Equiv.refl (Fin q)) (ZMod.finEquiv M).toEquiv)
        (Equiv.prodCongr (Equiv.refl (Fin q)) (ZMod.finEquiv M).toEquiv) := by
  funext ⟨α,j⟩ ⟨β,k⟩
  simp only [QuantumLift.blockOriginal,polyBlocks,Matrix.sum_apply,Matrix.smul_apply,
    Polynomial.smul_eq_C_mul,RingHom.mapMatrix_apply,Matrix.map_apply,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,
    Polynomial.eval₂_C,Matrix.reindex_apply,Equiv.prodCongr_symm,
    Equiv.prodCongr_apply,Equiv.refl_symm,test]
  apply Finset.sum_congr rfl
  intro i _
  change ((HahnSeries.C : E →+* F E).comp φ) (A i α β) *
    (padded M N (points i) ((ZMod.finEquiv M).symm j) ((ZMod.finEquiv M).symm k)).eval₂
      ((HahnSeries.C : E →+* F E).comp φ) (HahnSeries.single 1 1) =
    ((HahnSeries.C : E →+* F E).comp φ) (A i α β) *
      embed (padded M N (φ (points i)) ((ZMod.finEquiv M).symm j) ((ZMod.finEquiv M).symm k))
  rw [eval₂_padded]

/-- The three-variable determinant is nonzero. The witness can lie over an
extension field and is never an input to the generator. -/

theorem det_ne_zero (χ : AddChar (ZMod M) K) (hχ : χ.IsPrimitive)
    (φ : K →+* E) (points : Fin w → K) (hp : Function.Injective points)
    (A : Fin w → Matrix (Fin q) (Fin q) K)
    (B e : ℕ) (hw : 1 ≤ w) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hN : 1 ≤ N) (hMN : M = N+2*w^3*B) (hM : B*(2*w^3*B) < M) (he : 0 < e)
    (X : Fin w → Matrix (Fin e) (Fin e) (F E))
    (hX : Function.Injective (Rectangular.blockEval
      (fun i => ((HahnSeries.C : E →+* F E).comp φ).mapMatrix (A i)) X)) :
    (polynomial (N := N) χ A points).det ≠ 0 := by
  let : CharZero (F E) := CharZero.of_addMonoidHom
    (HahnSeries.C : E →+* F E).toAddMonoidHom (map_one (HahnSeries.C : E →+* F E))
    HahnSeries.C_injective
  let ψ : K →+* F E := (HahnSeries.C : E →+* F E).comp φ
  let τ : F E := HahnSeries.single 1 1
  let A' := fun i => ψ.mapMatrix (A i)
  let W := fun α β => (Polynomial.eval₂RingHom ψ τ).mapMatrix (polyBlocks (M := M) (N := N) A points α β)
  have hr := PaddedRank.rank_ge w B M N q e hw hN hMN hqB he
    (fun i => φ (points i)) (φ.injective.comp hp) A' X hX
  have hr' : (q-1)*M < (QuantumLift.blockOriginal W).rank := by
    rw [show QuantumLift.blockOriginal W = _ from raw_specialize φ A points, Matrix.rank_reindex]
    exact (PaddedRank.numeric_gap w B M N q hq hqB hMN hM).trans_le hr
  have hχ' : (ψ.toMonoidHom.compAddChar χ).IsPrimitive :=
    hχ.compMulHom_of_isPrimitive ψ.injective
  have hd := QuantumLift.blockPolynomial_det_ne_zero (ψ.toMonoidHom.compAddChar χ) hχ' W
    (by simpa using hq) (by simpa using hr')
  intro hz
  have hm := congrArg (ThreeLift.specialize ψ τ) hz
  rw [map_zero, RingHom.map_det, specialize χ ψ τ] at hm
  exact hd hm

lemma polyBlocks_degree.{v_1} {K : Type v_1} [Field K] [CharZero K]
  {w q M N : ℕ} [NeZero M] (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K)
  (α β : Fin q) (i j : ZMod M) :
  (polyBlocks (M := M) (N := N) A points α β i j).natDegree ≤ M - 1 := by
  simp only [polyBlocks,Matrix.sum_apply,Matrix.smul_apply,Polynomial.smul_eq_C_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  exact padded_natDegree_le M N (points r) _ _

lemma entry_degree (χ : AddChar (ZMod M) K)
    (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K)
    (a b : Fin q × ZMod M) :
    (polynomial (N := N) χ A points a b).totalDegree ≤ 3*M := by
  have hh := ThreeLift.lift_totalDegree_le χ (polyBlocks (M := M) (N := N) A points a.1 b.1)
    (M-1) (polyBlocks_degree A points a.1 b.1) a.2 b.2
  exact hh.trans (by omega)
end
end RationalHitting.PencilDeformation


namespace RationalHitting.ThreeLift
open Matrix Polynomial MvPolynomial
open QuantumMatrices
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

lemma lift_sum {ι : Type*} (S : Finset ι) (R : ι → Matrix (ZMod d) (ZMod d) K[X]) :
    lift χ (∑ i ∈ S, R i) = ∑ i ∈ S, lift χ (R i) := map_sum (linear χ) R S
end
end RationalHitting.ThreeLift

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.CyclotomicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.CyclotomicRing
open Polynomial Matrix Module
noncomputable section

lemma character_primitive (e : ℕ) : (character e).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root _ (root_primitive e)

end
end RationalHitting.CyclotomicRing


namespace RationalHitting.FiniteGrid
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K] {k : ℕ}

/-- The fixed grid, independent of the coefficients, finds a nonzero value. -/
theorem exists_eval_ne_zero (p : MvPolynomial (Fin k) K) (hp : p ≠ 0)
    (S : Finset K) (hS : p.totalDegree < S.card) :
    ∃ x : Fin k → K, (∀ i, x i ∈ S) ∧ eval x p ≠ 0 := by
  classical
  by_contra! hz
  have hh := schwartz_zippel_totalDegree hp S
  have he : (Fintype.piFinset (fun _ : Fin k => S)).filter (fun x => eval x p = 0) =
      Fintype.piFinset (fun _ : Fin k => S) := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact hz x (Fintype.mem_piFinset.mp hx)
  rw [he] at hh
  have hpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hS
  have hpos' : (0 : ℚ≥0) < S.card := by exact_mod_cast hpos
  have hpow : (S.card : ℚ≥0)^k ≠ 0 := pow_ne_zero _ (ne_of_gt hpos')
  have hcard : (Fintype.piFinset (fun _ : Fin k => S)).card = S.card^k := by simp
  rw [hcard,Nat.cast_pow,div_self hpow] at hh
  have hlt : (p.totalDegree : ℚ≥0) / S.card < 1 :=
    (div_lt_one hpos').mpr (by exact_mod_cast hS)
  exact (not_lt_of_ge hh) hlt

lemma det_totalDegree_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial (Fin k) K)) (d : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) :
    A.det.totalDegree ≤ Fintype.card ι * d := by
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ i : ι, (A (σ i) i).totalDegree ≤ ∑ _i : ι, d := Finset.sum_le_sum (fun i _ => hA _ _)
    _ = Fintype.card ι * d := by simp

/-- The common grid specializes a list of determinant conditions
simultaneously, rather than one formula gate at a time. -/
theorem simultaneous (P : List (MvPolynomial (Fin k) K))
    (hP : ∀ p ∈ P, p ≠ 0) (d : ℕ) (hd : ∀ p ∈ P, p.totalDegree ≤ d)
    (S : Finset K) (hS : P.length * d < S.card) :
    ∃ x : Fin k → K, (∀ i, x i ∈ S) ∧ ∀ p ∈ P, eval x p ≠ 0 := by
  have hprod : P.prod ≠ 0 := List.prod_ne_zero (by intro hz; exact hP 0 hz rfl)
  have hdeg : P.prod.totalDegree ≤ P.length*d := by
    apply (totalDegree_list_prod P).trans
    clear hS hprod hP
    induction P with
    | nil => simp
    | cons p P ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have hh := hd p (by simp)
      have htail := ih (fun z hz => hd z (by simp [hz]))
      rw [Nat.add_mul,Nat.one_mul]
      omega
  obtain ⟨x,hx,hxp⟩ := exists_eval_ne_zero P.prod hprod S (hdeg.trans_lt hS)
  refine ⟨x,hx,?_⟩
  intro p hp hz
  apply hxp
  change eval₂Hom (RingHom.id K) x P.prod = 0
  rw [map_list_prod]
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨p,hp,hz⟩

end
end RationalHitting.FiniteGrid

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Certificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.LocalSpecialization
open IsLocalization Matrix
noncomputable section
variable {P K E : Type*} [CommRing P] [Field K] [Field E]

/-- Only fractions whose denominator is nonzero at the point are evaluated.
The entire division algebra is deliberately not given a specialization. -/
lemma evaluate_reflects_units (ev : P →+* K) (x : Regular ev)
    (hx : IsUnit (evaluate ev x)) : IsUnit x := by
  obtain ⟨a,b,rfl⟩ := IsLocalization.exists_mk'_eq (denominators ev) x
  have heq : ev a = ev b * evaluate ev (IsLocalization.mk' (Regular ev) a b) :=
    (IsLocalization.lift_mk'_spec _ a _ b).mp rfl
  have ha : ev a ≠ 0 := by rw [heq]; exact mul_ne_zero b.property hx.ne_zero
  let a' : denominators ev := ⟨a,ha⟩
  apply isUnit_iff_exists_inv.mpr
  exact ⟨IsLocalization.mk' (Regular ev) (b : P) a', IsLocalization.mk'_mul_mk'_eq_one a' b⟩

lemma intoField_injective (ev : P →+* K) (j : P →+* E) (hj : Function.Injective j) :
    Function.Injective (intoField ev j hj) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro x y
  constructor
  · intro h
    simpa only [intoField_algebraMap] using congrArg (intoField ev j hj) h
  · intro h
    rw [hj h]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma matrix_reflects_units (ev : P →+* K) (A : Matrix ι ι (Regular ev))
    (hA : IsUnit ((evaluate ev).mapMatrix A)) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det] at hA ⊢
  apply evaluate_reflects_units ev
  rwa [RingHom.map_det]

end
end RationalHitting.LocalSpecialization

namespace RationalHitting.QuantumLift
open Matrix HahnSeries
open RationalHitting.LocalSpecialization RationalHitting.PolynomialHahn
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
  {n : ℕ} (χ : AddChar (ZMod d) K)

/-- The original tree remains defined after the generic deformation. A nonzero
original value becomes invertible. Domain preservation uses the localization
regular at (1,1), while final invertibility uses the division subring. -/
theorem formula_invertible_value (hχ : χ.IsPrimitive) (f : Formula n)
    (W : Fin n → Matrix (ZMod d) (ZMod d) K) (a : Matrix (ZMod d) (ZMod d) K)
    (ha : f.Eval (algebraMap ℚ _) W a) (ha0 : a ≠ 0) :
    ∃ b : Matrix (ZMod d) (ZMod d) (HahnSeries Exponents K),
      f.Eval (algebraMap ℚ _) (fun i => representation χ (liftD χ (W i))) b ∧ IsUnit b := by
  let P := MvPolynomial (Fin 2) K
  let ev : P →+* K := (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))).toRingHom
  let O := Regular ev
  let cO : ℚ →+* Matrix (ZMod d) (ZMod d) O :=
    (algebraMap O _).comp ((algebraMap P O).comp (MvPolynomial.C.comp (algebraMap ℚ K)))
  let X : Fin n → Matrix (ZMod d) (ZMod d) O := fun i =>
    (algebraMap P O).mapMatrix (polynomialLift χ (W i))
  let eps : Matrix (ZMod d) (ZMod d) O →+* Matrix (ZMod d) (ZMod d) K :=
    (evaluate ev).mapMatrix
  let inc : Matrix (ZMod d) (ZMod d) O →+*
      Matrix (ZMod d) (ZMod d) (HahnSeries Exponents K) :=
    (intoField ev PolynomialHahn.embed PolynomialHahn.embed_injective).mapMatrix
  have hX : (fun i => eps (X i)) = W := by
    funext i
    change (evaluate ev).mapMatrix ((algebraMap P O).mapMatrix (polynomialLift χ (W i))) = W i
    have heq : (evaluate ev).mapMatrix ((algebraMap P O).mapMatrix (polynomialLift χ (W i))) =
        ev.mapMatrix (polynomialLift χ (W i)) := by
      ext j k
      exact evaluate_algebraMap ev _
    rw [heq]
    exact polynomialLift_specialize χ hχ (W i)
  have ha' : f.Eval (eps.comp cO) (fun i => eps (X i)) a := by
    rw [hX, RingHom.ext_rat (eps.comp cO) (algebraMap ℚ _)]
    exact ha
  obtain ⟨y,hy,hyval⟩ := ha'.lift eps (matrix_reflects_units ev)
  have hy0 : y ≠ 0 := by
    intro hz
    apply ha0
    rw [← hyval,hz,map_zero]
  have hinc : Function.Injective inc := Matrix.map_injective (intoField_injective ev _ _)
  have hb0 : inc y ≠ 0 := by
    intro hz
    exact hy0 (hinc (hz.trans (map_zero inc).symm))
  have hiX : (fun i => inc (X i)) = (fun i => representation χ (liftD χ (W i))) := by
    funext i
    have heq : inc (X i) = PolynomialHahn.embed.mapMatrix (polynomialLift χ (W i)) := by
      funext j k
      exact intoField_algebraMap ev PolynomialHahn.embed PolynomialHahn.embed_injective _
    rw [heq]
    exact polynomialLift_embed χ (W i)
  have hb : f.Eval (algebraMap ℚ _) (fun i => representation χ (liftD χ (W i))) (inc y) := by
    have hh := hy.map inc
    rw [hiX, RingHom.ext_rat (inc.comp cO) (algebraMap ℚ _)] at hh
    exact hh
  let : CharZero (Matrix (ZMod d) (ZMod d) (HahnSeries Exponents K)) :=
    charZero_of_inj_zero fun m hm => by
      have hh := congrFun (congrFun hm (0 : ZMod d)) (0 : ZMod d)
      have hh0 := congrArg (fun z : HahnSeries Exponents K => z.coeff 0) hh
      simpa [Matrix.natCast_apply, ← HahnSeries.single_zero_natCast] using hh0
  let : CharZero (DivisionSubring χ) :=
    (representation χ).charZero
  refine ⟨inc y,hb,?_⟩
  apply Formula.Eval.unit_of_division_lift (representation χ) (c := Rat.castHom (DivisionSubring χ))
    (X := fun i => liftD χ (W i)) (h := f) _ hb0
  rwa [RingHom.ext_rat ((representation χ).comp (Rat.castHom (DivisionSubring χ)))
    (algebraMap ℚ _)]

end
end RationalHitting.QuantumLift

namespace RationalHitting
open Matrix
noncomputable section

theorem formula_invertible_witness {n d : ℕ} (hd : 0 < d) (f : Formula n)
    (W : Fin n → Matrix (Fin d) (Fin d) ℚ) (a : Matrix (Fin d) (Fin d) ℚ)
    (ha : f.Eval (algebraMap ℚ _) W a) (ha0 : a ≠ 0) :
    ∃ (X : Fin n → Matrix (Fin d) (Fin d) (HahnSeries QuantumLift.Exponents ℂ))
      (v : Matrix (Fin d) (Fin d) (HahnSeries QuantumLift.Exponents ℂ)),
      f.Eval (algebraMap ℚ _) X v ∧ IsUnit v := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let e := Matrix.reindexRingEquiv ℂ (ZMod.finEquiv d).toEquiv
  let j : Matrix (Fin d) (Fin d) ℚ →+* Matrix (ZMod d) (ZMod d) ℂ :=
    e.toRingHom.comp (algebraMap ℚ ℂ).mapMatrix
  have hj : Function.Injective j := e.injective.comp (Matrix.map_injective (algebraMap ℚ ℂ).injective)
  have ha' : f.Eval (algebraMap ℚ _) (fun i => j (W i)) (j a) := by
    have hh := ha.map j
    rwa [RingHom.ext_rat (j.comp (algebraMap ℚ _)) (algebraMap ℚ _)] at hh
  have ha0' : j a ≠ 0 := by
    intro hz
    exact ha0 (hj (hz.trans (map_zero j).symm))
  have hζ := Complex.isPrimitiveRoot_exp d (NeZero.ne d)
  let χ := AddChar.zmodChar d hζ.pow_eq_one
  have hχ : χ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root d hζ
  obtain ⟨b,hb,hbu⟩ := QuantumLift.formula_invertible_value χ hχ f
    (fun i => j (W i)) (j a) ha' ha0'
  let r := Matrix.reindexRingEquiv (HahnSeries QuantumLift.Exponents ℂ) (ZMod.finEquiv d).toEquiv.symm
  refine ⟨fun i => r (QuantumLift.representation χ (QuantumLift.liftD χ (j (W i)))), r b, ?_, hbu.map r⟩
  have hh := hb.map r.toRingHom
  convert hh using 1
  all_goals first | exact RingHom.ext_rat _ _ | rfl

end
end RationalHitting

namespace RationalHitting.PencilCertificates
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]

variable {n q M N : ℕ} [NeZero M]

lemma polynomial_apply (χ : AddChar (ZMod M) K)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) (a b : Fin q × ZMod M) :
    polynomial χ N L a b = ∑ i, MvPolynomial.C ((algebraMap ℚ K) (Affine.coeff (L a.1 b.1) i)) *
      lifts χ N n i a.2 b.2 := by
  unfold polynomial PencilDeformation.polynomial PencilDeformation.polyBlocks
  rw [ThreeLift.lift_sum]
  simp only [Matrix.sum_apply,ThreeLift.lift_smul,Matrix.smul_apply,
    MvPolynomial.smul_eq_C_mul,coefficients,lifts]

lemma specialized (χ : AddChar (ZMod M) K)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) (x : Fin 3 → K) :
    (eval₂Hom (RingHom.id K) x).mapMatrix (polynomial χ N L) =
      Matrix.compRingEquiv (Fin q) (ZMod M) K
        (L.map (Affine.homogeneous (algebraMap ℚ _) (fun i =>
          (eval₂Hom (RingHom.id K) x).mapMatrix (lifts χ N n i)))) := by
  rw [Affine.homogeneous_flat]
  funext a b
  simp only [RingHom.mapMatrix_apply,Matrix.map_apply,polynomial_apply,map_sum,map_mul,
    eval₂Hom_C,RingHom.id_apply]

lemma block_eq (φ : K →+* E) (L : Matrix (Fin q) (Fin q) (Affine.Form n))
    {d : ℕ} (X : Fin n → Matrix (Fin d) (Fin d) E) :
    Rectangular.blockMatrix (fun i => φ.mapMatrix (coefficients (K := K) L i)) (Fin.cases 1 X) =
      Matrix.compRingEquiv (Fin q) (Fin d) E (L.map (Affine.eval (algebraMap ℚ _) X)) := by
  have hc (a : ℚ) : φ ((algebraMap ℚ K) a) = (algebraMap ℚ E) a :=
    DFunLike.congr_fun (RingHom.ext_rat (φ.comp (algebraMap ℚ K)) (algebraMap ℚ E)) a
  have hm : L.map (Affine.eval (algebraMap ℚ _) X) =
      L.map (Affine.homogeneous (algebraMap ℚ _) (Fin.cases 1 X)) := by
    funext a b
    exact (Affine.homogeneous_one _ X (L a b)).symm
  rw [hm,Affine.homogeneous_flat]
  funext a b
  simp only [Rectangular.blockMatrix,Matrix.sum_apply,Matrix.kroneckerMap_apply,
    RingHom.mapMatrix_apply,Matrix.map_apply,coefficients,hc]

lemma determinant_ne_zero (χ : AddChar (ZMod M) K) (hχ : χ.IsPrimitive)
    (φ : K →+* E) (L : Matrix (Fin q) (Fin q) (Affine.Form n))
    (B d : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B) (hN : 1 ≤ N)
    (hMN : M = N+2*(n+1)^3*B) (hM : B*(2*(n+1)^3*B) < M) (hd : 0 < d)
    (X : Fin n → Matrix (Fin d) (Fin d) (LaurentReduction.F E))
    (hX : IsUnit (L.map (Affine.eval (algebraMap ℚ _) X))) :
    determinant χ N L ≠ 0 := by
  apply PencilDeformation.det_ne_zero χ hχ φ (fun i : Fin (n+1) => (i.val : K))
    (by intro i j h; apply Fin.ext; change (i.val : K) = (j.val : K) at h; exact Nat.cast_injective h) (coefficients L) B d
      (by omega) hq hqB hN hMN hM hd (Fin.cases 1 X)
  apply Rectangular.blockEval_injective_of_isUnit
  rw [block_eq]
  exact hX.map (Matrix.compRingEquiv (Fin q) (Fin d) (LaurentReduction.F E))


lemma degree_le (χ : AddChar (ZMod M) K)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) :
    (determinant χ N L).totalDegree ≤ 3*q*M^2 := by
  have hh := FiniteGrid.det_totalDegree_le (polynomial χ N L) (3*M)
    (PencilDeformation.entry_degree χ (coefficients L) (fun i => (i.val : K)))
  simp only [Fintype.card_prod,Fintype.card_fin,ZMod.card] at hh
  exact hh.trans_eq (by ring)

end
end RationalHitting.PencilCertificates

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.Generator
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section

lemma mem_grid (H : ℕ) (x : Fin 3 → Fin H) : x ∈ grid H := by
  simp only [grid,List.mem_flatMap,List.mem_map]
  refine ⟨x 0,by simp, x 1,by simp,x 2,by simp,?_⟩
  funext i
  fin_cases i <;> rfl

/-- The actual emitted rational normalization is the homomorphic image of the
quotient normalization. Consequently every original inverse occurrence is kept. -/
lemma transfer {n N e : ℕ} (x : Fin 3 → ℕ) (f : Formula n)
    (z : (Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e))ˣ)
    (hz : (z : Matrix _ _ _) = Zring n N e x 0)
    (v : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e)) (CyclotomicRing.R e))
    (hf : f.Eval (algebraMap ℚ _) (fun i => (↑z⁻¹ : Matrix _ _ _) * Zring n N e x i.succ) v)
    (hu : IsUnit v) :
    ∃ a, Evaluates f (tupleAt n N e x) a ∧ IsUnit a := by
  have hzinv : regular e (↑z⁻¹ : Matrix _ _ _) = (Z n N e x 0)⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    change regular e (↑z⁻¹ : Matrix _ _ _) * regular e (Zring n N e x 0) = 1
    simp only [← map_mul,← hz,Units.inv_mul,map_one]
  refine ⟨regular e v,?_,hu.map (regular e)⟩
  have hh := hf.map (regular e)
  rw [RingHom.ext_rat ((regular e).comp (algebraMap ℚ _)) (algebraMap ℚ _)] at hh
  change f.Eval (algebraMap ℚ _) (tupleAt n N e x) (regular e v)
  change f.Eval (algebraMap ℚ _) (fun i => (regular e (Zring n N e x 0))⁻¹ * regular e (Zring n N e x i.succ)) (regular e v)
  simpa only [map_mul,hzinv,Z] using hh

lemma emitted {n N e H : ℕ} (x : Fin 3 → Fin H)
    (hz : IsUnit (Zring n N e (fun i => (x i).val+1) 0)) :
    tupleAt n N e (fun i => (x i).val+1) ∈ (output n N e H).tuples := by
  apply List.mem_filterMap.mpr
  refine ⟨x,mem_grid H x,?_⟩
  have hq := (Matrix.isUnit_iff_isUnit_det _).mp (hz.map (regular e))
  have hne : (Z n N e (fun i => (x i).val+1) 0).det ≠ 0 := hq.ne_zero
  simp [atPoint,hne]

end
end RationalHitting.Generator

namespace RationalHitting.Generator
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section

lemma finPencil_unit {n : ℕ} {R : Type*} [Ring R] (c : ℚ →+* R)
    (X : Fin n → R) (f : Formula n) :
    IsUnit ((finPencil f).map (Affine.eval c X)) ↔ IsUnit (Formula.realized c X f) := by
  let E := Matrix.reindexRingEquiv R (Fintype.equivFin f.Index)
  change IsUnit (E (Formula.realized c X f)) ↔ IsUnit (Formula.realized c X f)
  constructor
  · intro h; simpa using h.map E.symm
  · exact fun h => h.map E

lemma condition_nonzero {n s N e : ℕ} (hs : 1 ≤ s) (f : Formula n) (hf : f.size ≤ s)
    (hnz : Nonzero f)
    (hN : 1 ≤ N) (hMN : CyclotomicRing.dimension e = N+2*(n+1)^3*(2*s+1))
    (hM : (2*s+1)*(2*(n+1)^3*(2*s+1)) < CyclotomicRing.dimension e) :
    ∀ p ∈ conditions N e f, p ≠ 0 := by
  obtain ⟨d,hd,W,a,ha,ha0⟩ := hnz
  obtain ⟨X,v,hv,hvu⟩ := formula_invertible_witness hd f W a ha ha0
  let C : WitnessField →+* LaurentReduction.F WitnessField := HahnSeries.C
  let Y : Fin n → Matrix (Fin d) (Fin d) (LaurentReduction.F WitnessField) := fun i => C.mapMatrix (X i)
  have hv' : Formula.Eval (algebraMap ℚ (Matrix (Fin d) (Fin d) (LaurentReduction.F WitnessField)))
      Y f (C.mapMatrix v) := by
    convert hv.map C.mapMatrix using 1
    exact RingHom.ext_rat _ _
  have hcert : ∀ h ∈ f.certificates, IsUnit (Formula.realized (algebraMap ℚ _) Y h) :=
    (Formula.certificates_iff (algebraMap ℚ _) Y f).mpr ⟨_,hv',hvu.map C.mapMatrix⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · apply PencilCertificates.determinant_ne_zero (CyclotomicRing.character e)
      (CyclotomicRing.character_primitive e) (witnessEmbedding e) (onePencil n)
      (2*s+1) 1 (by omega) (by omega) hN hMN hM (by omega) (fun _ => 0)
    have heq : (onePencil n).map (Affine.eval (algebraMap ℚ (Matrix (Fin 1) (Fin 1)
        (LaurentReduction.F WitnessField))) (fun _ => 0)) = 1 := by
      ext i j
      simp [onePencil,Affine.eval_constant,Matrix.one_apply,Subsingleton.elim i j]
    rw [heq]
    exact isUnit_one
  · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hp
    have hb := (Formula.certificate_bounds f s hs hf).2 h hh
    apply PencilCertificates.determinant_ne_zero (CyclotomicRing.character e)
      (CyclotomicRing.character_primitive e) (witnessEmbedding e) (finPencil h)
      (2*s+1) d hb.1 hb.2 hN hMN hM hd Y
    exact (finPencil_unit _ _ h).mpr (hcert h hh)

lemma condition_degree {n s N e : ℕ} (hs : 1 ≤ s) (f : Formula n) (hf : f.size ≤ s) :
    (conditions N e f).length ≤ s+2 ∧
    ∀ p ∈ conditions N e f, p.totalDegree ≤ 3*(2*s+1)*(CyclotomicRing.dimension e)^2 := by
  refine ⟨?_,?_⟩
  · have hh := (Formula.certificate_bounds f s hs hf).1
    simpa only [conditions,List.length_cons,List.length_map] using Nat.succ_le_succ hh
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (PencilCertificates.degree_le _ _).trans (by gcongr; omega)
    · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hp
      exact (PencilCertificates.degree_le _ _).trans (by gcongr; exact (Formula.certificate_bounds f s hs hf).2 h hh |>.2)

lemma integer_grid {K : Type*} [Field K] [CharZero K] (P : List (MvPolynomial (Fin 3) K))
    (hP : ∀ p ∈ P, p ≠ 0) (d H : ℕ) (hd : ∀ p ∈ P, p.totalDegree ≤ d)
    (hH : P.length*d < H) :
    ∃ x : Fin 3 → Fin H, ∀ p ∈ P, eval (fun i => (((x i).val+1 : ℕ) : K)) p ≠ 0 := by
  classical
  let S : Finset K := (Finset.range H).image (fun i => ((i+1 : ℕ) : K))
  have hS : S.card = H := by
    rw [Finset.card_image_of_injective,Finset.card_range]
    intro i j h
    have hh : i+1=j+1 := Nat.cast_injective h
    omega
  obtain ⟨x,hx,hxp⟩ := FiniteGrid.simultaneous P hP d hd S (by rwa [hS])
  have hm (i : Fin 3) : ∃ k : Fin H, ((k.val+1 : ℕ) : K) = x i := by
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp (hx i)
    exact ⟨⟨k,Finset.mem_range.mp hk⟩,he⟩
  choose y hy using hm
  refine ⟨y,?_⟩
  intro p hp
  have heq : (fun i => (((y i).val+1 : ℕ) : K)) = x := funext hy
  simpa only [heq] using hxp p hp

lemma specialized_unit {K : Type*} [Field K] [CharZero K] {n q M N : ℕ} [NeZero M]
    (χ : AddChar (ZMod M) K) (L : Matrix (Fin q) (Fin q) (Affine.Form n)) (x : Fin 3 → K)
    (hx : eval x (PencilCertificates.determinant χ N L) ≠ 0) :
    IsUnit (L.map (Affine.homogeneous (algebraMap ℚ _) (fun i =>
      (eval₂Hom (RingHom.id K) x).mapMatrix (PencilCertificates.lifts χ N n i)))) := by
  have hd : IsUnit ((eval₂Hom (RingHom.id K) x).mapMatrix (PencilCertificates.polynomial χ N L)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.map_det]
    exact hx
  rw [PencilCertificates.specialized] at hd
  simpa using hd.map (Matrix.compRingEquiv (Fin q) (ZMod M) K).symm

lemma onePencil_unit {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Fin (n+1) → Matrix ι ι K)
    (h : IsUnit ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) Z))) : IsUnit (Z 0) := by
  have hh := h.map (Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K)).toRingHom
  have heq : (Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K))
      ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) Z)) = Z 0 := by
    change Affine.homogeneous (algebraMap ℚ _) Z (Affine.constant 1) = Z 0
    simp [Affine.homogeneous,Affine.coeff,Affine.constant,Fin.sum_univ_succ]
  change IsUnit ((Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K))
      ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) Z))) at hh
  rwa [heq] at hh

/-- The finite formula-independent list hits every admissible nonzero formula
at a defined and invertible original-tree value. -/

theorem output_hits {n s N e H : ℕ} (hs : 1 ≤ s)
    (hN : 1 ≤ N) (hMN : CyclotomicRing.dimension e = N+2*(n+1)^3*(2*s+1))
    (hM : (2*s+1)*(2*(n+1)^3*(2*s+1)) < CyclotomicRing.dimension e)
    (hH : (s+2)*(3*(2*s+1)*(CyclotomicRing.dimension e)^2) < H) :
    Hits s (output n N e H) := by
  intro f hf _ha hnz
  have hb := condition_degree hs f hf (N := N) (e := e)
  obtain ⟨x,hx⟩ := integer_grid (conditions N e f)
    (condition_nonzero hs f hf hnz hN hMN hM) _ H hb.2 (lt_of_le_of_lt (Nat.mul_le_mul_right _ hb.1) hH)
  let t : Fin 3 → ℕ := fun i => (x i).val+1
  let Zr := Zring n N e t
  have hz : IsUnit (Zr 0) := by
    apply onePencil_unit Zr
    exact specialized_unit _ _ _ (hx _ (List.mem_cons_self ..))
  obtain ⟨z,hz'⟩ := hz
  have hcert : ∀ h ∈ f.certificates,
      IsUnit (Formula.realized (algebraMap ℚ _) (fun i => (↑z⁻¹ : Matrix _ _ _)*Zr i.succ) h) := by
    intro h hh
    apply (finPencil_unit _ _ h).mp
    apply Affine.normalized_pencil_unit (finPencil h) Zr z hz'
    apply specialized_unit
    exact hx _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨h,hh,rfl⟩))
  obtain ⟨v,hv,hu⟩ := (Formula.certificates_iff _ _ f).mp hcert
  obtain ⟨a,ha,hua⟩ := transfer t f z hz' v hv hu
  exact ⟨tupleAt n N e t,emitted x ⟨z,hz'⟩,a,ha,hua⟩

end
end RationalHitting.Generator

namespace RationalHitting.Parameters

theorem threshold_lt (n s : ℕ) : B s * delta n s < M n s :=
  Nat.lt_pow_succ_log_self (by omega) _

theorem N_pos (n s : ℕ) : 1 ≤ N n s := by
  have hh := threshold_lt n s
  have hb : 1 ≤ B s := by unfold B; omega
  have hd : delta n s ≤ B s*delta n s := by nlinarith
  unfold N
  omega

theorem M_eq (n s : ℕ) : M n s = N n s+delta n s := by
  have hh := N_pos n s
  unfold N at *
  omega

theorem grid_large (n s : ℕ) : (s+2)*(3*B s*(M n s)^2) < H n s := by
  have hp : 1 ≤ M n s := Nat.one_le_iff_ne_zero.mpr (by unfold M; positivity)
  have hpow : (M n s)^2 ≤ (M n s)^3 := Nat.pow_le_pow_right hp (by omega)
  unfold H
  linarith [Nat.mul_le_mul_left (3*(s+2)*B s) hpow]

end RationalHitting.Parameters

namespace RationalHitting.Generator
noncomputable section

theorem list_hits_oai (n s : ℕ) (hs : 1 ≤ s) : Hits s (list n s) := by
  apply output_hits hs
  · exact Parameters.N_pos n s
  · exact Parameters.M_eq n s
  · exact Parameters.threshold_lt n s
  · exact Parameters.grid_large n s

end
end RationalHitting.Generator

end OAI
end

theorem solution : type_of% @OAI.RationalHitting.Generator.list_hits_oai := @OAI.RationalHitting.Generator.list_hits_oai
