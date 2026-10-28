-- Prove2me | solution 1 for OAI.Heisenberg.Bootstrap.periodic_return_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:31:55.748008+00:00
-- url     : https://prove2.me/submissions/0f3d2291-59ad-4268-a41e-3ceaa1de2580

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM000
import Definitions.Def_OAIW2HM001
import Theorems.Thm_OAI_Heisenberg_Flow_indexed_prefix_leakage

section
-- module Solutions.OAIW2_Heis.Heisenberg_DeterminantExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
open Matrix
namespace Heisenberg.Exposure

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

lemma det_two_rows (A : Matrix n n R) {i j : n} (hij : i ≠ j)
    (v : n → R) (u : R) :
    ((A.updateRow i (A i + u • v)).updateRow j (A j - u • v)).det =
      A.det + u * ((A.updateRow i v).det - (A.updateRow j v).det) := by
  have h₁ : (A.updateRow i (A i + u • v)).updateRow j (A j) =
      A.updateRow i (A i + u • v) := by
    rw [← Matrix.updateRow_ne (M := A) (b := A i + u • v) hij.symm]
    exact Matrix.updateRow_eq_self _ _
  have h₂ : ((A.updateRow i (A i + u • v)).updateRow j v).det =
      (A.updateRow j v).det := by
    rw [Matrix.updateRow_comm A hij, Matrix.det_updateRow_add,
      Matrix.det_updateRow_smul]
    have hrow : (A.updateRow j v).updateRow i (A i) = A.updateRow j v := by
      rw [← Matrix.updateRow_ne (M := A) (b := v) hij]
      exact Matrix.updateRow_eq_self _ _
    rw [hrow]
    have hz : ((A.updateRow j v).updateRow i v).det = 0 := by
      apply Matrix.det_zero_of_row_eq hij
      simp [Matrix.updateRow_self, Matrix.updateRow_ne hij.symm]
    rw [hz, mul_zero, add_zero]
  rw [sub_eq_add_neg, Matrix.det_updateRow_add, ← neg_smul,
    Matrix.det_updateRow_smul, h₁, h₂, Matrix.det_updateRow_add,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  ring

lemma one_sub_swapMix_mul (D : Matrix n n R) {i j : n} (hij : i ≠ j)
    (u : R) :
    1 - swapMix i j u * D =
      (((1 - D).updateRow i ((1 - D) i + u • (D i - D j))).updateRow j
        ((1 - D) j - u • (D i - D j))) := by
  unfold swapMix
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext k l
  by_cases hi : k = i
  · subst k
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.submatrix_apply, Equiv.swap_apply_left,
      id_eq, Matrix.updateRow_apply, hij, ite_false, ite_true,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  · by_cases hj : k = j
    · subst k
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.submatrix_apply, Equiv.swap_apply_right,
        id_eq, Matrix.updateRow_apply, ite_true,
        Pi.sub_apply, Pi.smul_apply]
      ring
    · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.submatrix_apply,
        Equiv.swap_apply_of_ne_of_ne hi hj, id_eq, Matrix.updateRow_apply,
        hi, hj, ite_false]
      ring

theorem det_swapMix (D : Matrix n n R) (i j : n) (u : R) :
    (1 - D * swapMix i j u).det =
      (1 - u) * (1 - D).det + u * (1 - D * (Equiv.swap i j).permMatrix R).det := by
  by_cases hij : i = j
  · subst j
    simp only [Equiv.swap_self, Matrix.permMatrix_refl]
    have he : swapMix i i u = (1 : Matrix n n R) := by
      simp [swapMix, ← add_smul]
    rw [he, Matrix.mul_one]
    ring
  rw [Matrix.det_one_sub_mul_comm, one_sub_swapMix_mul D hij, det_two_rows _ hij]
  have h₁ := det_two_rows (1 - D) hij (D i - D j) (1 : R)
  rw [← one_sub_swapMix_mul D hij] at h₁
  simp only [swapMix, sub_self, zero_smul, one_smul, zero_add, one_mul] at h₁
  rw [Matrix.det_one_sub_mul_comm D ((Equiv.swap i j).permMatrix R), h₁]
  ring

theorem determinantLaw_bernoulli (i j : n) (u : R) :
    DeterminantLaw (fun b : Bool => if b then u else 1 - u)
      (fun b => if b then (Equiv.swap i j).permMatrix R else 1) := by
  intro D
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false, Matrix.mul_one]
  rw [add_comm (u • _), ← swapMix, det_swapMix]
  ring

theorem DeterminantLaw.independent_mul {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    {p : Ω → R} {q : Ψ → R} {X : Ω → Matrix n n R} {Y : Ψ → Matrix n n R}
    (hX : DeterminantLaw p X) (hY : DeterminantLaw q Y) :
    DeterminantLaw (fun z : Ω × Ψ => p z.1 * q z.2)
      (fun z => X z.1 * Y z.2) := by
  intro D
  let MX := ∑ ω, p ω • X ω
  let MY := ∑ ψ, q ψ • Y ψ
  have hmean : (∑ z : Ω × Ψ, (p z.1 * q z.2) • (X z.1 * Y z.2)) = MX * MY := by
    dsimp [MX, MY]
    rw [Fintype.sum_prod_type, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro ω _
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hmean, Fintype.sum_prod_type]
  calc
    (∑ ω, ∑ ψ, (p ω * q ψ) * (1 - D * (X ω * Y ψ)).det) =
        ∑ ω, p ω * (1 - D * X ω * MY).det := by
      apply Finset.sum_congr rfl
      intro ω _
      simp_rw [mul_assoc (p ω), ← Matrix.mul_assoc D]
      rw [← Finset.mul_sum, hY]
    _ = ∑ ω, p ω * (1 - MY * D * X ω).det := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Matrix.det_one_sub_mul_comm (D * X ω) MY, Matrix.mul_assoc]
    _ = (1 - MY * D * MX).det := hX (MY * D)
    _ = (1 - D * (MX * MY)).det := by
      rw [Matrix.mul_assoc MY, Matrix.det_one_sub_mul_comm MY (D * MX),
        Matrix.mul_assoc]

end Heisenberg.Exposure

open scoped Classical
open Matrix
namespace Heisenberg.Exposure

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (R : Type*) [Field R]

omit [Fintype Q] [DecidableEq Q] in
lemma walk_add (f : Q → Option Q) (n m : ℕ) (i : Q) :
    walk f (n + m) i = (walk f n i).bind (walk f m) := by
  induction n generalizing i with
  | zero => simp [walk]
  | succ n ih =>
    simp only [Nat.succ_add, walk]
    cases h : f i with
    | none => simp
    | some j => simpa using ih j

omit [Fintype Q] [DecidableEq Q] in
lemma walk_eq_none_of_le (f : Q → Option Q) {n m : ℕ} (hnm : n ≤ m)
    {i : Q} (hi : walk f n i = none) : walk f m i = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [walk_add, hi]
  rfl

lemma pow_partialMatrix (f : Q → Option Q) (n : ℕ) (i j : Q) :
    (partialMatrix R f ^ n) i j = if walk f n i = some j then 1 else 0 := by
  induction n generalizing i with
  | zero => simp [walk, Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    cases h : f i with
    | none => simp [partialMatrix, h, walk]
    | some k =>
      simp only [partialMatrix, h, Option.some.injEq, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simpa [walk, h] using ih k

omit [Fintype Q] [DecidableEq Q] in
lemma escapes_of_none {f : Q → Option Q} {i : Q} (hi : f i = none) : Escapes f i :=
  ⟨1, by simp [walk, hi]⟩

omit [Fintype Q] [DecidableEq Q] in
lemma escapes_iff_of_some {f : Q → Option Q} {i j : Q} (h : f i = some j) :
    Escapes f i ↔ Escapes f j := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [walk] at hn
    | succ n => exact ⟨n, by simpa [walk, h] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa [walk, h] using hn⟩

lemma nilpotent_partialMatrix (f : Q → Option Q) (h : ∀ i, Escapes f i) :
    IsNilpotent (partialMatrix R f) := by
  choose n hn using h
  refine ⟨∑ i, n i, ?_⟩
  ext i j
  rw [pow_partialMatrix]
  have hi : walk f (∑ i, n i) i = none :=
    walk_eq_none_of_le f (Finset.single_le_sum (fun k _ => Nat.zero_le (n k))
      (Finset.mem_univ i)) (hn i)
  simp [hi]

lemma det_one_sub_of_nilpotent {A : Matrix Q Q R} (h : IsNilpotent A) :
    (1 - A).det = 1 := by
  have hc : A.charpoly = Polynomial.X ^ Fintype.card Q :=
    sub_eq_zero.mp <| isNilpotent_iff_eq_zero.mp <|
      Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have he := congrArg (Polynomial.eval (1 : R)) hc
  simpa [Matrix.eval_charpoly] using he

lemma det_one_sub_partialMatrix_of_not_all (f : Q → Option Q)
    (h : ¬ ∀ i, Escapes f i) : (1 - partialMatrix R f).det = 0 := by
  let v : Q → R := fun i => if Escapes f i then 0 else 1
  have hv : partialMatrix R f *ᵥ v = v := by
    ext i
    cases hi : f i with
    | none => simp [Matrix.mulVec, dotProduct, partialMatrix, hi, v, escapes_of_none hi]
    | some j =>
      simp only [Matrix.mulVec, dotProduct, partialMatrix, hi, Option.some.injEq,
        ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp [v, escapes_iff_of_some hi]
  have hz : (1 - partialMatrix R f) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self]
  by_contra hne
  have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hne hz
  push Not at h
  obtain ⟨i, hi⟩ := h
  have := congrFun hv0 i
  simp [v, hi] at this

theorem det_one_sub_partialMatrix (f : Q → Option Q) :
    (1 - partialMatrix R f).det = if ∀ i, Escapes f i then 1 else 0 := by
  split_ifs with h
  · exact det_one_sub_of_nilpotent R (nilpotent_partialMatrix R f h)
  · exact det_one_sub_partialMatrix_of_not_all R f h

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FirstReturns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open Matrix
namespace Heisenberg.Exposure

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
variable (R : Type*) [Field R]

omit [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q] in
lemma cycle_hit_of_walk_none (π : Equiv.Perm (J ⊕ Q)) (n : ℕ) (q : Q)
    (h : walk (restrictPerm π) n q = none) :
    ∃ j, π.SameCycle (Sum.inr q) (Sum.inl j) := by
  induction n generalizing q with
  | zero => simp [walk] at h
  | succ n ih =>
    cases he : π (Sum.inr q) with
    | inl j =>
      refine ⟨j, ?_⟩
      rw [← he]
      exact Equiv.Perm.SameCycle.rfl.apply_right
    | inr r =>
      have hr : walk (restrictPerm π) n r = none := by simpa [walk, restrictPerm, he] using h
      obtain ⟨j, hj⟩ := ih r hr
      refine ⟨j, ?_⟩
      rw [← he] at hj
      exact hj.of_apply_left

omit [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q] in
lemma escapes_of_pow_hit (π : Equiv.Perm (J ⊕ Q)) (n : ℕ) (q : Q) (j : J)
    (h : (π ^ n) (Sum.inr q) = Sum.inl j) : Escapes (restrictPerm π) q := by
  induction n generalizing q with
  | zero => simp at h
  | succ n ih =>
    cases he : π (Sum.inr q) with
    | inl k => exact escapes_of_none (by simp [restrictPerm, he])
    | inr r =>
      have hr : restrictPerm π q = some r := by simp [restrictPerm, he]
      apply (escapes_iff_of_some hr).mpr
      apply ih r
      simpa [pow_succ, Equiv.Perm.mul_apply, he] using h

omit [DecidableEq J] [DecidableEq Q] in
lemma escapes_restrictPerm_iff (π : Equiv.Perm (J ⊕ Q)) (q : Q) :
    Escapes (restrictPerm π) q ↔ ∃ j, π.SameCycle (Sum.inr q) (Sum.inl j) := by
  constructor
  · rintro ⟨n, hn⟩
    exact cycle_hit_of_walk_none π n q hn
  · rintro ⟨j, hj⟩
    obtain ⟨n, hn⟩ := hj.exists_nat_pow_eq
    exact escapes_of_pow_hit π n q j hn

omit [DecidableEq J] [DecidableEq Q] in
lemma allHit_iff_escapes (π : Equiv.Perm (J ⊕ Q)) :
    AllHit π ↔ ∀ q, Escapes (restrictPerm π) q := by
  constructor
  · intro h q
    exact (escapes_restrictPerm_iff π q).mpr (h (Sum.inr q))
  · intro h x
    cases x with
    | inl j => exact ⟨j, Equiv.Perm.SameCycle.rfl⟩
    | inr q => exact (escapes_restrictPerm_iff π q).mp (h q)

omit [Fintype J] [Fintype Q] in
lemma columnPerm_QQ (π : Equiv.Perm (J ⊕ Q)) :
    (columnPerm R π).submatrix Sum.inr Sum.inr = (partialMatrix R (restrictPerm π)).transpose := by
  ext i j
  simp only [columnPerm, Matrix.submatrix_apply, Matrix.transpose_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    partialMatrix]
  have heq : (Sum.inr i ∈ some (π (Sum.inr j))) ↔ restrictPerm π j = some i := by
    simp only [Option.mem_some_iff]
    unfold restrictPerm
    cases π (Sum.inr j) <;> simp [eq_comm]
  simp only [heq]

theorem det_one_sub_columnPerm_QQ (π : Equiv.Perm (J ⊕ Q)) :
    (1 - (columnPerm R π).submatrix Sum.inr Sum.inr).det = if AllHit π then 1 else 0 := by
  rw [columnPerm_QQ, ← Matrix.transpose_one, ← Matrix.transpose_sub, Matrix.det_transpose,
    det_one_sub_partialMatrix]
  simp only [← allHit_iff_escapes]

theorem det_pinTest_of_not_allHit (π : Equiv.Perm (J ⊕ Q)) (W : Matrix J J R)
    (h : ¬ AllHit π) : (1 - pinTestMatrix R (Q := Q) W * columnPerm R π).det = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, ∀ j, ¬ π.SameCycle x (Sum.inl j) := by
    simpa only [AllHit, not_forall, not_exists] using h
  let v : (J ⊕ Q) → R := fun y => if π.SameCycle x y then 1 else 0
  have hv : columnPerm R π *ᵥ v = v := by
    rw [columnPerm, Matrix.transpose_permMatrix, Matrix.permMatrix_mulVec]
    ext y
    simp [v]
  have hvJ : v ∘ Sum.inl = 0 := by
    ext j
    simp [v, hx j]
  have hd : pinTestMatrix R (Q := Q) W *ᵥ v = v := by
    rw [pinTestMatrix, Matrix.fromBlocks_mulVec, hvJ]
    simp only [Matrix.mulVec_zero, Matrix.zero_mulVec, add_zero, zero_add, Matrix.one_mulVec]
    ext y
    cases y with
    | inl j => simpa [Function.comp_def] using (congrFun hvJ j).symm
    | inr q => rfl
  have hz : (1 - pinTestMatrix R (Q := Q) W * columnPerm R π) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, hd, sub_self]
  by_contra hne
  have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hne hz
  have := congrFun hv0 x
  simp [v, Equiv.Perm.SameCycle.rfl] at this

end

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
variable (R : Type*) [Field R]

lemma pinTest_block_form (K : Matrix (J ⊕ Q) (J ⊕ Q) R) (W : Matrix J J R) :
    1 - pinTestMatrix R (Q := Q) W * K =
      Matrix.fromBlocks (1 - W * K.toBlocks₁₁) (-(W * K.toBlocks₁₂))
        (-K.toBlocks₂₁) (1 - K.toBlocks₂₂) := by
  have hk : pinTestMatrix R (Q := Q) W * K =
      Matrix.fromBlocks (W * K.toBlocks₁₁) (W * K.toBlocks₁₂)
        K.toBlocks₂₁ K.toBlocks₂₂ := by
    conv_lhs => arg 2; rw [← Matrix.fromBlocks_toBlocks K]
    simp [pinTestMatrix, Matrix.fromBlocks_multiply]
  rw [hk]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply, Matrix.fromBlocks]

theorem det_pinTest_schur (K : Matrix (J ⊕ Q) (J ⊕ Q) R) (W : Matrix J J R)
    (hK : (1 - K.toBlocks₂₂).det ≠ 0) :
    (1 - pinTestMatrix R (Q := Q) W * K).det =
      (1 - K.toBlocks₂₂).det * (1 - W * hittingResolvent R K).det := by
  let _ : Invertible (1 - K.toBlocks₂₂) :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hK)
  rw [pinTest_block_form, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  congr 2
  simp only [hittingResolvent, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc, sub_sub]

theorem det_pinTest_zero (K : Matrix (J ⊕ Q) (J ⊕ Q) R) :
    (1 - pinTestMatrix R (Q := Q) 0 * K).det = (1 - K.toBlocks₂₂).det := by
  rw [pinTest_block_form]
  simp only [Matrix.zero_mul, sub_zero, neg_zero]
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

theorem det_pinTest_allHit (π : Equiv.Perm (J ⊕ Q)) (W : Matrix J J R)
    (h : AllHit π) :
    (1 - pinTestMatrix R (Q := Q) W * columnPerm R π).det =
      (1 - W * hittingResolvent R (columnPerm R π)).det := by
  have he : (1 - (columnPerm R π).toBlocks₂₂).det = 1 := by
    simpa only [Matrix.toBlocks₂₂, Matrix.submatrix, ite_eq_left h] using det_one_sub_columnPerm_QQ R π
  rw [det_pinTest_schur R _ _ (by rw [he]; exact one_ne_zero), he, one_mul]

end

section

variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]
variable {R : Type*} [Field R]

theorem allHit_determinant (μ : Ω → R) (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω))) :
    hitWeight μ π = (1 - (∑ ω, μ ω • columnPerm R (π ω)).toBlocks₂₂).det := by
  have ht := h (pinTestMatrix R (Q := Q) (0 : Matrix J J R))
  rw [det_pinTest_zero] at ht
  convert ht using 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [det_pinTest_zero]
  have he := det_one_sub_columnPerm_QQ R (π ω)
  simp only [Matrix.toBlocks₂₂, Matrix.submatrix] at he ⊢
  rw [he]
  by_cases hh : AllHit (π ω) <;> simp [hh]

theorem allHit_determinant_before_division (μ : Ω → R)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω))) (W : Matrix J J R) :
    (∑ ω, if AllHit (π ω) then μ ω * (1 - W * hittingResolvent R (columnPerm R (π ω))).det
      else 0) = (1 - pinTestMatrix R (Q := Q) W * ∑ ω, μ ω • columnPerm R (π ω)).det := by
  rw [← h]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hh : AllHit (π ω)
  · rw [ite_eq_left hh, det_pinTest_allHit R _ _ hh]
  · rw [ite_eq_right hh, det_pinTest_of_not_allHit R _ _ hh, mul_zero]

theorem conditional_resolvent_determinant (μ : Ω → R)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω)))
    (hg : hitWeight μ π ≠ 0) (W : Matrix J J R) :
    (∑ ω, if AllHit (π ω) then (μ ω / hitWeight μ π) *
      (1 - W * hittingResolvent R (columnPerm R (π ω))).det else 0) =
      (1 - W * hittingResolvent R (∑ ω, μ ω • columnPerm R (π ω))).det := by
  have he := allHit_determinant μ π h
  have hk : (1 - (∑ ω, μ ω • columnPerm R (π ω)).toBlocks₂₂).det ≠ 0 := he ▸ hg
  have ht := allHit_determinant_before_division μ π h W
  rw [det_pinTest_schur R _ _ hk, ← he] at ht
  calc
    _ = (∑ ω, if AllHit (π ω) then μ ω *
        (1 - W * hittingResolvent R (columnPerm R (π ω))).det else 0) / hitWeight μ π := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp [div_mul_eq_mul_div]
    _ = _ := by rw [ht, mul_div_cancel_left₀ _ hg]

end

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {R : Type*} [CommRing R]

lemma det_one_sub_single_mul (A : Matrix J J R) (i j : J) :
    (1 - Matrix.single i j (1 : R) * A).det = 1 - A j i := by
  let U : Matrix J Unit R := fun k _ => if k = i then 1 else 0
  let V : Matrix Unit J R := fun _ k => A j k
  have hm : Matrix.single i j (1 : R) * A = U * V := by
    ext k l
    rw [Matrix.mul_apply, Matrix.mul_apply]
    by_cases hk : k = i
    · subst k
      simp [U, V, Matrix.single_apply]
    · simp [U, V, hk, Ne.symm hk]
  rw [hm, Matrix.det_one_sub_mul_comm, Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
  simp [U, V]

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ConditionalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.Exposure

section
variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]
variable {R : Type*} [Field R]

lemma conditional_hitWeight_sum (μ : Ω → R) (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω)))
    (hg : hitWeight μ π ≠ 0) :
    (∑ ω, if AllHit (π ω) then μ ω / hitWeight μ π else 0) = 1 := by
  have ht := conditional_resolvent_determinant μ π h hg (0 : Matrix J J R)
  simpa only [Matrix.zero_mul, sub_zero, Matrix.det_one, mul_one] using ht

theorem conditional_resolvent_first_moment (μ : Ω → R)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω)))
    (hg : hitWeight μ π ≠ 0) :
    (∑ ω, if AllHit (π ω) then
      (μ ω / hitWeight μ π) • hittingResolvent R (columnPerm R (π ω)) else 0) =
      hittingResolvent R (∑ ω, μ ω • columnPerm R (π ω)) := by
  ext i j
  have ht := conditional_resolvent_determinant μ π h hg (Matrix.single j i (1 : R))
  simp only [det_one_sub_single_mul] at ht
  have he : (∑ ω, if AllHit (π ω) then (μ ω / hitWeight μ π) *
      (1 - hittingResolvent R (columnPerm R (π ω)) i j) else 0) =
      (∑ ω, if AllHit (π ω) then μ ω / hitWeight μ π else 0) -
      (∑ ω, if AllHit (π ω) then (μ ω / hitWeight μ π) *
        hittingResolvent R (columnPerm R (π ω)) i j else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  rw [he, conditional_hitWeight_sum μ π h hg] at ht
  have hh := sub_right_injective ht
  simp only [Matrix.sum_apply]
  rw [← hh]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> rfl

end

section
variable {J Q : Type*} [Fintype J] [Fintype Q]

lemma firstPin_spec (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q) :
    (π ^ firstPinTime π h x) x = Sum.inl (firstPin π h x) :=
  Classical.choose_spec (Nat.find_spec (reachesPin π h x))

lemma firstPinTime_min (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q)
    {n : ℕ} {j : J} (hj : (π ^ n) x = Sum.inl j) : firstPinTime π h x ≤ n :=
  Nat.find_min' (reachesPin π h x) ⟨j, hj⟩

@[simp] lemma firstPinTime_inl (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J) :
    firstPinTime π h (Sum.inl j) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact firstPinTime_min π h _ (by simp : (π ^ 0) (Sum.inl j) = Sum.inl j)

@[simp] lemma firstPin_inl (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J) :
    firstPin π h (Sum.inl j) = j := by
  have hs := firstPin_spec π h (Sum.inl j)
  simpa using hs.symm

lemma firstPinTime_inr_pos (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (q : Q) :
    0 < firstPinTime π h (Sum.inr q) := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hs := firstPin_spec π h (Sum.inr q)
  simp [hz] at hs

lemma firstPinTime_step (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (q : Q) :
    firstPinTime π h (Sum.inr q) = firstPinTime π h (π (Sum.inr q)) + 1 := by
  apply Nat.le_antisymm
  · apply firstPinTime_min π h _ (j := firstPin π h (π (Sum.inr q)))
    rw [pow_succ, Equiv.Perm.mul_apply]
    exact firstPin_spec π h _
  · have hp := firstPinTime_inr_pos π h q
    have he : (π ^ (firstPinTime π h (Sum.inr q) - 1)) (π (Sum.inr q)) =
        Sum.inl (firstPin π h (Sum.inr q)) := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hp]
      exact firstPin_spec π h _
    have hm := firstPinTime_min π h _ he
    omega

lemma firstPin_step (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (q : Q) :
    firstPin π h (Sum.inr q) = firstPin π h (π (Sum.inr q)) := by
  have hs := firstPin_spec π h (Sum.inr q)
  rw [firstPinTime_step, pow_succ, Equiv.Perm.mul_apply] at hs
  exact Sum.inl.inj (hs.symm.trans (firstPin_spec π h _))

lemma nextPin_spec (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J) :
    (π ^ (firstPinTime π h (π (Sum.inl j)) + 1)) (Sum.inl j) =
      Sum.inl (nextPin π h j) := by
  rw [pow_succ, Equiv.Perm.mul_apply]
  exact firstPin_spec π h _

lemma nextPin_is_first (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J)
    {n : ℕ} (hn : 0 < n) {k : J} (hk : (π ^ n) (Sum.inl j) = Sum.inl k) :
    firstPinTime π h (π (Sum.inl j)) + 1 ≤ n := by
  have he : (π ^ (n - 1)) (π (Sum.inl j)) = Sum.inl k := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hn]
    exact hk
  have hm := firstPinTime_min π h _ he
  omega

end

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
variable (R : Type*) [Field R]

omit [DecidableEq Q] in
lemma firstPinMatrix_boundary (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) :
    (firstPinMatrix R π h).toCols₁ = 1 := by
  ext i j
  simp [firstPinMatrix, Matrix.one_apply, eq_comm]

lemma firstPinMatrix_step (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) :
    firstPinMatrix R π h * columnPerm R π =
      Matrix.fromCols (nextPinMatrix R π h) (firstPinMatrix R π h).toCols₂ := by
  ext i x
  change ((firstPinMatrix R π h) i ᵥ* columnPerm R π) x = _
  rw [columnPerm, Matrix.transpose_permMatrix, Matrix.vecMul_permMatrix]
  cases x with
  | inl j => rfl
  | inr q =>
    change (if firstPin π h (π (Sum.inr q)) = i then (1 : R) else 0) =
      (if firstPin π h (Sum.inr q) = i then (1 : R) else 0)
    rw [firstPin_step]

theorem nextPinMatrix_eq_resolvent (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) :
    nextPinMatrix R π h = hittingResolvent R (columnPerm R π) := by
  let K := columnPerm R π
  let V := (firstPinMatrix R π h).toCols₂
  have hs := firstPinMatrix_step R π h
  have hf : firstPinMatrix R π h = Matrix.fromCols 1 V := by
    rw [← Matrix.fromCols_toCols (firstPinMatrix R π h), firstPinMatrix_boundary]
  rw [hf] at hs
  change Matrix.fromCols 1 V * K = Matrix.fromCols (nextPinMatrix R π h) V at hs
  conv_lhs at hs => arg 2; rw [← Matrix.fromBlocks_toBlocks K]
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.one_mul, Matrix.one_mul] at hs
  have hJ := congrArg Matrix.toCols₁ hs
  have hQ := congrArg Matrix.toCols₂ hs
  simp only [Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols] at hJ hQ
  have hV : V * (1 - K.toBlocks₂₂) = K.toBlocks₁₂ := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    exact sub_eq_iff_eq_add.mpr hQ.symm
  have hd : IsUnit (1 - K.toBlocks₂₂).det := by
    have he : (1 - K.toBlocks₂₂).det = 1 := by
      simpa only [K, Matrix.toBlocks₂₂, Matrix.submatrix, ite_eq_left h] using
        det_one_sub_columnPerm_QQ R π
    rw [he]
    exact isUnit_one
  have hv : V = K.toBlocks₁₂ * (1 - K.toBlocks₂₂)⁻¹ := by
    rw [← hV, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  rw [← hJ, hv]
  rfl

end

variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]
variable {R : Type*} [Field R]

theorem conditional_nextPin_first_moment (μ : Ω → R)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω)))
    (hg : hitWeight μ π ≠ 0) :
    (∑ ω, if hw : AllHit (π ω) then
      (μ ω / hitWeight μ π) • nextPinMatrix R (π ω) hw else 0) =
      hittingResolvent R (∑ ω, μ ω • columnPerm R (π ω)) := by
  rw [← conditional_resolvent_first_moment μ π h hg]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hw : AllHit (π ω)
  · simp only [dite_eq_left hw, ite_eq_left hw, nextPinMatrix_eq_resolvent]
  · simp only [dite_eq_right hw, ite_eq_right hw]

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeDeterminants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.Exposure

section
variable {K J Ω : Type*} [Fintype K] [Fintype J] [Fintype Ω]
  [DecidableEq K] [DecidableEq J]
variable {R : Type*} [CommRing R]

lemma det_block_extraction (X : Matrix (K ⊕ J) (K ⊕ J) R) (D : Matrix K K R) :
    (1 - (Matrix.fromBlocks D 0 0 0) * X).det =
      (1-D*X.submatrix Sum.inl Sum.inl).det := by
  have he : 1 - (Matrix.fromBlocks D 0 0 0) * X =
      Matrix.fromBlocks (1-D*X.submatrix Sum.inl Sum.inl)
        (-D*X.submatrix Sum.inl Sum.inr) 0 1 := by
    ext i j
    rcases i with i|i <;> rcases j with j|j <;>
      simp [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks,Matrix.one_apply]
  rw [he,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]

theorem DeterminantLaw.inl {p : Ω → R} {X : Ω → Matrix (K ⊕ J) (K ⊕ J) R}
    (h : DeterminantLaw p X) :
    DeterminantLaw p (fun ω => (X ω).submatrix Sum.inl Sum.inl) := by
  intro D
  have hh := h (Matrix.fromBlocks D 0 0 0)
  simp only [det_block_extraction] at hh
  convert hh using 1
  congr 3
  ext i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.submatrix_apply]

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq N] [DecidableEq M]

theorem DeterminantLaw.reindex {p : Ω → R} {X : Ω → Matrix N N R}
    (h : DeterminantLaw p X) (e : M ≃ N) :
    DeterminantLaw p (fun ω => (X ω).submatrix e e) := by
  intro D
  have hh := h (D.submatrix e.symm e.symm)
  have hr : ∀ Y : Matrix N N R,
      (1-D.submatrix e.symm e.symm*Y).det =
        (1-D*Y.submatrix e e).det := by
    intro Y
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    change (1 : Matrix N N R).submatrix e e -
      (D.submatrix e.symm e.symm*Y).submatrix e e = _
    rw [Matrix.submatrix_one_equiv]
    rw [← Matrix.submatrix_mul_equiv _ _ e e e]
    simp only [Matrix.submatrix_submatrix,Equiv.symm_comp_self,Matrix.submatrix_id_id]
  simp only [hr] at hh
  convert hh using 1
  congr 3
  ext i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.submatrix_apply]

theorem DeterminantLaw.subtype {p : Ω → R} {X : Ω → Matrix N N R}
    (h : DeterminantLaw p X) (P : N → Prop) [DecidablePred P] :
    DeterminantLaw p (fun ω => (X ω).submatrix (fun x : {i // P i} => x.val) (fun x => x.val)) := by
  exact (h.reindex (Equiv.sumCompl P)).inl

end

variable {N Ω Ψ B R : Type*} [Fintype N] [DecidableEq N]
  [Fintype Ω] [Fintype Ψ] [Fintype B] [CommRing R]

lemma DeterminantLaw.reparam {p : Ω → R} {X : Ω → Matrix N N R}
    (h : DeterminantLaw p X) (e : Ψ ≃ Ω) :
    DeterminantLaw (p ∘ e) (X ∘ e) := by
  intro D
  change (∑ x, p (e x)*(1-D*X (e x)).det) = (1-D*(∑ x,p (e x) • X (e x))).det
  rw [e.sum_comp (fun x => p x*(1-D*X x).det),e.sum_comp (fun x => p x • X x)]
  exact h D

lemma DeterminantLaw.const_left {p : Ω → R} {X : Ω → Matrix N N R}
    (h : DeterminantLaw p X) (C : Matrix N N R) :
    DeterminantLaw p (fun ω => C*X ω) := by
  intro D
  simpa only [Matrix.mul_assoc,Matrix.mul_sum,Matrix.mul_smul] using h (D*C)

lemma determinantLaw_constant (p : Ω → R) (hp : ∑ x,p x=1) (C : Matrix N N R) :
    DeterminantLaw p (fun _ => C) := by
  intro D
  simp only [← Finset.sum_mul,← Finset.sum_smul,hp,one_mul,one_smul]

theorem determinantLaw_array (n : ℕ)
    (w : Fin n → B → R) (X : Fin n → B → Matrix N N R)
    (h : ∀ i, DeterminantLaw (w i) (X i)) :
    DeterminantLaw (fun b : Fin n → B => ∏ i,w i (b i))
      (fun b => orderedProduct n (fun i => X i (b i))) := by
  induction n with
  | zero => intro D; simp [orderedProduct]
  | succ n ih =>
    have hh := (h 0).independent_mul (ih (fun i => w i.succ) (fun i => X i.succ) (fun i => h i.succ))
    have ht := hh.reparam (splitArray (B:=B) n)
    convert ht using 1
    · funext b
      exact Fin.prod_univ_succ _
    · rfl

end Heisenberg.Exposure

namespace Heisenberg.LayeredExchange
variable {T V : Type*}

lemma fibers_swap [DecidableEq T] [DecidableEq V] (t : T) (u v : V) :
    fibers (Function.update (fun _ : T => 1) t (Equiv.swap u v)) = Equiv.swap (t,u) (t,v) := by
  ext ⟨a,b⟩ <;> by_cases ht : a = t
  · subst a
    simp [fibers,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · simp [fibers,Function.update,ht,Equiv.swap_apply_def]
  · subst a
    simp [fibers,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · simp [fibers,Function.update,ht,Equiv.swap_apply_def]

end Heisenberg.LayeredExchange

namespace Heisenberg.Exposure
variable {A B : Type*} [Monoid A] [Monoid B]

lemma orderedProduct_map (f : A →* B) (n : ℕ) (x : Fin n → A) :
    f (orderedProduct n x) = orderedProduct n (fun i => f (x i)) := by
  induction n with
  | zero => exact f.map_one
  | succ n ih => simp only [orderedProduct,map_mul,ih]

lemma orderedProduct_one (n : ℕ) (x : Fin n → A) (hx : ∀ i,x i=1) :
    orderedProduct n x = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orderedProduct,hx,ih _ fun _ => rfl]

lemma orderedProduct_single {n : ℕ} (x : Fin n → A) (i : Fin n)
    (hx : ∀ j,j ≠ i → x j=1) : orderedProduct n x = x i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rw [orderedProduct,orderedProduct_one _ _ (fun j => hx j.succ (Fin.succ_ne_zero j)),mul_one]
    | succ i =>
      rw [orderedProduct,hx 0 (Fin.succ_ne_zero i).symm,one_mul]
      exact ih _ i (fun j hj => hx j.succ (by simpa using hj))

end Heisenberg.Exposure
namespace Heisenberg.LayeredExchange

section
open Exposure
variable {T V : Type*}

lemma fibers_ordered_product (n : ℕ) (σ : Fin n → Equiv.Perm V) :
    fibers σ = orderedProduct n (fun i => fibers (Function.update (fun _ => 1) i (σ i))) := by
  change fibersHom σ = orderedProduct n
    (fun i => fibersHom (Function.update (fun _ => 1) i (σ i)))
  rw [← orderedProduct_map (fibersHom (T:=Fin n) (V:=V))]
  apply congrArg fibers
  funext i
  let eval : (Fin n → Equiv.Perm V) →* Equiv.Perm V :=
    { toFun := fun f => f i, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have he := orderedProduct_map eval n (fun j => Function.update (fun _ => 1) j (σ j))
  change σ i = eval (orderedProduct n (fun j => Function.update (fun _ => 1) j (σ j)))
  rw [he,orderedProduct_single _ i]
  · simp [eval]
  · intro j hj
    simp [eval,Function.update,Ne.symm hj]

end

open Exposure
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Type*} [CommRing R]

lemma forwardHom_swap (a b : V) :
    forwardHom (R:=R) (Equiv.swap a b) = (Equiv.swap a b).permMatrix R := by
  simp [forwardHom,Matrix.transpose_permMatrix]

lemma determinantLaw_phase {n : ℕ} (i : Fin n) (a b : V) (p : R)
    (fixed : Option (Equiv.Perm V)) :
    DeterminantLaw (fun c : Bool => if c then p else 1-p)
      (fun c => forwardHom (R:=R) (fibers (Function.update (fun _ => 1) i
        (fixed.getD (if c then Equiv.swap a b else 1))))) := by
  cases fixed with
  | some σ =>
    simp only [Option.getD_some]
    exact determinantLaw_constant (fun c : Bool => if c then p else 1-p)
      (by simp) (forwardHom (R:=R) (fibers (Function.update (fun _ => 1) i σ)))
  | none =>
    have he : ∀ c : Bool,
        forwardHom (R:=R) (fibers (Function.update (fun _ => 1) i
          ((none : Option (Equiv.Perm V)).getD (if c then Equiv.swap a b else 1)))) =
          if c then (Equiv.swap (i,a) (i,b)).permMatrix R else 1 := by
      intro c
      cases c
      · simp [forwardHom,fibers_one]
      · simp only [↓reduceIte,Option.getD_none,fibers_swap,forwardHom_swap]
    simp_rw [he]
    exact determinantLaw_bernoulli _ _ _

theorem determinantLaw_wiring {n : ℕ} (s : Equiv.Perm (Fin n))
    (a b : Fin n → V) (p : Fin n → R) (fixed : Fin n → Option (Equiv.Perm V)) :
    DeterminantLaw (fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i)
      (fun c => forwardHom (R:=R) (wiring s
        (fun i => (fixed i).getD (if c i then Equiv.swap (a i) (b i) else 1)))) := by
  have h := determinantLaw_array n (fun i (c : Bool) => if c then p i else 1-p i)
    (fun i c => forwardHom (R:=R) (fibers (Function.update (fun _ => 1) i
      ((fixed i).getD (if c then Equiv.swap (a i) (b i) else 1)))))
    (fun i => determinantLaw_phase i (a i) (b i) (p i) (fixed i))
  have hh := h.const_left (forwardHom (R:=R) (Equiv.prodCongr s (Equiv.refl V)))
  convert hh using 1
  funext c
  rw [wiring,map_mul,fibers_ordered_product,orderedProduct_map]

end Heisenberg.LayeredExchange
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.LayeredExchange
open Exposure
variable {V W Ω : Type*} [Fintype V] [Fintype W] [Fintype Ω]
  [DecidableEq V] [DecidableEq W]
variable {R : Type*} [CommRing R]

lemma forwardHom_subtype (π : Equiv.Perm V) (P : V → Prop) [DecidablePred P]
    (h : ∀ x,P (π x) ↔ P x) :
    (forwardHom (R:=R) π).submatrix (fun x : {i // P i} => x.val) (fun x => x.val) =
      forwardHom (R:=R) (π.subtypePerm h) := by
  ext i j
  change (π.permMatrix R) j.val i.val = ((π.subtypePerm h).permMatrix R) j i
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff]
  congr 1
  apply propext
  constructor
  · exact fun he => Subtype.ext he
  · exact fun he => congrArg Subtype.val he

lemma forwardHom_reindex (π : Equiv.Perm V) (e : W ≃ V) :
    (forwardHom (R:=R) π).submatrix e e = forwardHom (R:=R) (e.symm.permCongr π) := by
  ext i j
  change (π.permMatrix R) (e j) (e i) = ((e.symm.permCongr π).permMatrix R) j i
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff,Equiv.permCongr_apply,Equiv.symm_symm]
  congr 1
  exact propext e.symm_apply_eq.symm

lemma determinantLaw_holes {μ : Ω → R} {π : Ω → Equiv.Perm V}
    (h : DeterminantLaw μ (fun ω => forwardHom (R:=R) (π ω)))
    (P : V → Prop) [DecidablePred P] (hi : ∀ ω x,P (π ω x) ↔ P x) :
    DeterminantLaw μ (fun ω => forwardHom (R:=R) ((π ω).subtypePerm (hi ω))) := by
  have hh := h.subtype P
  convert hh using 1
  funext ω
  exact (forwardHom_subtype (π ω) P (hi ω)).symm

lemma determinantLaw_reindexed {μ : Ω → R} {π : Ω → Equiv.Perm V}
    (h : DeterminantLaw μ (fun ω => forwardHom (R:=R) (π ω))) (e : W ≃ V) :
    DeterminantLaw μ (fun ω => forwardHom (R:=R) (e.symm.permCongr (π ω))) := by
  have hh := h.reindex e
  convert hh using 1
  funext ω
  exact (forwardHom_reindex (π ω) e).symm

end Heisenberg.LayeredExchange

open scoped Classical
namespace Heisenberg.Cycle

section
open Equiv
variable {V : Type*}

lemma colorSpace_mem (π : Perm V) (P : Set V) (f : V → ZMod 2) :
    f ∈ colorSpace π P ↔ (∀ i, f (π i) = f i) ∧ ∀ i ∈ P, f i = 0 := Iff.rfl

variable [Fintype V]

 theorem card_colorSpace (π : Perm V) (P : Set V) :
    Nat.card (colorSpace π P) = 2 ^ missingCount π P := by
  let := Fintype.ofFinite (MissingClasses π P)
  rw [Nat.card_congr (colorEquiv π P),Nat.card_fun]
  simp [missingCount]

end

open Equiv
variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma missing_apply (π : Perm V) (P : Set V) (i : V) :
    π i ∈ MissingSet π P ↔ i ∈ MissingSet π P := by
  simp only [MissingSet,Set.mem_ofPred_eq,classOf_apply]

omit [Fintype V] in
lemma missing_disjoint_pins (π : Perm V) (P : Set V) : Disjoint (MissingSet π P) P := by
  apply Set.disjoint_left.mpr
  intro i hi hP
  exact hi i hP rfl

lemma color_zero_not_missing (π : Perm V) (P : Set V) (f : colorSpace π P)
    (i : V) (hi : i ∉ MissingSet π P) : f.val i = 0 := by
  obtain ⟨j,hj⟩ := (not_forall.mp hi)
  obtain ⟨hjP,hij⟩ := Classical.not_imp.mp hj
  exact (color_eq_of_sameCycle π P f ((classOf_eq_iff π i j).mp (not_not.mp hij))).trans (f.property.2 j hjP)

theorem missing_weight_rigid (π τ : Perm V) (P : Set V)
    (hset : MissingSet π P = MissingSet τ P)
    (hval : ∀ i ∈ MissingSet π P, π i = τ i) :
    missingCount π P = missingCount τ P := by
  have hspace : colorSpace π P = colorSpace τ P := by
    apply le_antisymm
    · intro f hf
      refine ⟨?_,hf.2⟩
      intro i
      by_cases hi : i ∈ MissingSet π P
      · rw [← hval i hi]; exact hf.1 i
      · have hτ : τ i ∉ MissingSet π P := by
          rw [hset] at hi ⊢
          exact fun h => hi ((missing_apply τ P i).mp h)
        exact (color_zero_not_missing π P ⟨f,hf⟩ _ hτ).trans (color_zero_not_missing π P ⟨f,hf⟩ _ hi).symm
    · intro f hf
      refine ⟨?_,hf.2⟩
      intro i
      by_cases hi : i ∈ MissingSet π P
      · rw [hval i hi]; exact hf.1 i
      · have hπ : π i ∉ MissingSet τ P := by
          rw [← hset]
          exact fun h => hi ((missing_apply π P i).mp h)
        rw [hset] at hi
        exact (color_zero_not_missing τ P ⟨f,hf⟩ _ hπ).trans (color_zero_not_missing τ P ⟨f,hf⟩ _ hi).symm
  have he := congrArg (fun A : Submodule (ZMod 2) (V → ZMod 2) => Nat.card A) hspace
  rw [card_colorSpace,card_colorSpace] at he
  exact Nat.pow_right_injective (by decide : 1 < (2:ℕ)) he

lemma exposed_subset_missing (π τ : Perm V) (P : Set V)
    (hval : ∀ i ∈ MissingSet π P, π i = τ i) :
    MissingSet π P ⊆ MissingSet τ P := by
  intro i hi j hj he
  obtain ⟨n,hn⟩ := ((classOf_eq_iff τ i j).mp he).exists_nat_pow_eq
  have hiter : ∀ n : ℕ, (τ^n) i ∈ MissingSet π P := by
    intro n
    induction n with
    | zero => exact hi
    | succ n ih =>
      rw [pow_succ',Perm.mul_apply,← hval _ ih]
      exact (missing_apply π P _).mpr ih
  exact missing_disjoint_pins π P |>.le_bot ⟨hn ▸ hiter n,hj⟩

lemma sameMissing_iff_outsideHit (π τ : Perm V) (P : Set V)
    (hval : ∀ i ∈ MissingSet π P, π i = τ i) :
    MissingSet τ P = MissingSet π P ↔ OutsideHit τ P (MissingSet π P) := by
  have hsub := exposed_subset_missing π τ P hval
  constructor
  · intro h i hi
    have hn : i ∉ MissingSet τ P := by rwa [h]
    simp only [MissingSet,Set.mem_ofPred_eq,not_forall,not_not] at hn
    obtain ⟨j,hj,hij⟩ := hn
    exact ⟨j,hj,(classOf_eq_iff τ i j).mp hij⟩
  · intro h
    apply Set.Subset.antisymm _ hsub
    intro i hi
    by_contra hn
    obtain ⟨j,hj,hij⟩ := h i hn
    exact hi j hj ((classOf_eq_iff τ i j).mpr hij)

end Heisenberg.Cycle
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FiniteHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical

open scoped BigOperators Classical
namespace Heisenberg.Exposure

variable {I B : Type*} [Fintype I] [Fintype B]

lemma productWeight_sum (w : I → B → ℝ) (hw : ∀ i, ∑ b, w i b = 1) :
    ∑ c, productWeight w c = 1 := by
  classical
  simp only [productWeight, ← Fintype.prod_sum, hw, Finset.prod_const_one]

omit [Fintype B] in
lemma productWeight_nonneg (w : I → B → ℝ) (hw : ∀ i b, 0 ≤ w i b) (c : I → B) :
    0 ≤ productWeight w c := Finset.prod_nonneg fun i _ => hw i (c i)

omit [Fintype I] [Fintype B] in
lemma merge_left (M : I → Prop) [DecidablePred M] (a : {i // M i} → B)
    (b : {i // ¬M i} → B) (i : {i // M i}) : merge M a b i = a i := by
  simp [merge,Equiv.piEquivPiSubtypeProd,i.property]

omit [Fintype I] [Fintype B] in
lemma merge_right (M : I → Prop) [DecidablePred M] (a : {i // M i} → B)
    (b : {i // ¬M i} → B) (i : {i // ¬M i}) : merge M a b i = b i := by
  simp [merge,Equiv.piEquivPiSubtypeProd,i.property]

omit [Fintype B] in
lemma productWeight_merge (w : I → B → ℝ) (M : I → Prop) [DecidablePred M]
    (a : {i // M i} → B) (b : {i // ¬M i} → B) :
    productWeight w (merge M a b) =
      productWeight (fun i : {i // M i} => w i) a *
        productWeight (fun i : {i // ¬M i} => w i) b := by
  rw [productWeight, ← Fintype.prod_subtype_mul_prod_subtype M]
  simp only [merge_left,merge_right,productWeight]


end Heisenberg.Exposure

open scoped Classical

namespace Heisenberg.Exposure
variable {T : Type*} [Fintype T]

lemma filtered_cylinder_disintegration (w : T → Bool → ℝ) (M : T → Prop) [DecidablePred M]
    (a : {t // M t} → Bool) (G E : (T → Bool) → Prop)
    (v F : (T → Bool) → ℝ) (q : ℝ)
    (hE : ∀ c, E c ↔ (∀ t : {t // M t}, c t = a t) ∧ G c)
    (hv : ∀ c, E c → v c = q) :
    (∑ c : T → Bool, if E c then productWeight w c * v c * F c else 0) =
      q * productWeight (fun t : {t // M t} => w t) a *
        ∑ c : {t // ¬M t} → Bool, if G (merge M a c) then
          productWeight (fun t : {t // ¬M t} => w t) c * F (merge M a c) else 0 := by
  classical
  let e := Equiv.piEquivPiSubtypeProd M (fun _ => Bool)
  rw [← e.symm.sum_comp,Fintype.sum_prod_type]
  have he (a' : {t // M t} → Bool) (c : {t // ¬M t} → Bool) :
      E (e.symm (a',c)) ↔ a' = a ∧ G (e.symm (a',c)) := by
    rw [hE]
    change (∀ t : {t // M t}, merge M a' c t = a t) ∧ _ ↔ _
    simp only [merge_left,funext_iff]
  rw [Finset.sum_eq_single a]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    change (if E (merge M a c) then productWeight w (merge M a c) * v (merge M a c) * F (merge M a c) else 0) = _
    have hh : E (merge M a c) ↔ G (merge M a c) := by
      simpa only [e,merge,eq_self_iff_true,true_and] using he a c
    by_cases hg : G (merge M a c)
    · rw [ite_eq_left (hh.mpr hg),ite_eq_left hg,hv _ (hh.mpr hg),productWeight_merge]
      ring
    · rw [ite_eq_right (hh.not.mpr hg),ite_eq_right hg,mul_zero]
  · intro a' _ hne
    apply Finset.sum_eq_zero
    intro c _
    exact ite_eq_right (fun h => hne ((he a' c).mp h).1)
  · simp

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LayerExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical

namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype T] [Fintype V] in
lemma layer_matches_iff (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (A : Set (T × V)) (b c : T → Bool) :
    (∀ z ∈ A, layerHistory s τ b z = layerHistory s τ c z) ↔
      ∀ t, layerRevealed τ A t → c t = b t := by
  constructor
  · intro h t ht
    obtain ⟨v,hv,hne⟩ := ht
    have he := congrArg Prod.snd (h (t,v) hv)
    change (if b t then τ t else 1) v = (if c t then τ t else 1) v at he
    cases hb : b t <;> cases hc : c t
    · rfl
    · exact (hne (by simpa only [hb,hc,Bool.false_eq_true,↓reduceIte,Equiv.Perm.one_apply] using he.symm)).elim
    · exact (hne (by simpa only [hb,hc,Bool.false_eq_true,↓reduceIte,Equiv.Perm.one_apply] using he)).elim
    · rfl
  · intro h ⟨t,v⟩ hv
    simp only [layerHistory,wiring_apply]
    by_cases ht : layerRevealed τ A t
    · rw [h t ht]
    · have he : τ t v = v := by by_contra hn; exact ht ⟨v,hv,hn⟩
      congr 1
      split_ifs <;> first | exact he | exact he.symm | rfl

lemma layerExposure_iff (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b c : T → Bool) :
    layerExposure s τ P b c ↔
      (∀ t, layerRevealed τ (MissingSet (layerHistory s τ b) P) t → c t = b t) ∧
      OutsideHit (layerHistory s τ c) P (MissingSet (layerHistory s τ b) P) := by
  constructor
  · rintro ⟨hm,he⟩
    exact ⟨(layer_matches_iff ..).mp hm,(sameMissing_iff_outsideHit _ _ _ hm).mp he⟩
  · rintro ⟨hc,hh⟩
    have hm := (layer_matches_iff s τ _ b c).mpr hc
    exact ⟨hm,(sameMissing_iff_outsideHit _ _ _ hm).mpr hh⟩

lemma layerExposure_weight (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b c : T → Bool) (h : layerExposure s τ P b c) :
    missingCount (layerHistory s τ c) P = missingCount (layerHistory s τ b) P :=
  (missing_weight_rigid _ _ P h.2.symm h.1).symm

theorem layer_exposure_disintegration (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (w : T → Bool → ℝ) (P : Set (T × V)) (b : T → Bool) (F : (T → Bool) → ℝ) :
    let A := MissingSet (layerHistory s τ b) P
    let M := layerRevealed τ A
    let a : {t // M t} → Bool := fun t => b t
    (∑ c : T → Bool, if layerExposure s τ P b c then
      productWeight w c * (2:ℝ)^missingCount (layerHistory s τ c) P * F c else 0) =
    (2:ℝ)^missingCount (layerHistory s τ b) P *
      productWeight (fun t : {t // M t} => w t) a *
      ∑ c : {t // ¬M t} → Bool, if OutsideHit (layerHistory s τ (merge M a c)) P A then
        productWeight (fun t : {t // ¬M t} => w t) c * F (merge M a c) else 0 := by
  dsimp only
  refine filtered_cylinder_disintegration w
    (layerRevealed τ (MissingSet (layerHistory s τ b) P)) (fun t => b t)
    (fun c => OutsideHit (layerHistory s τ c) P (MissingSet (layerHistory s τ b) P))
    (layerExposure s τ P b) (fun c => (2:ℝ)^missingCount (layerHistory s τ c) P) F
    ((2:ℝ)^missingCount (layerHistory s τ b) P) ?_ ?_
  · intro c
    rw [layerExposure_iff]
    constructor
    · rintro ⟨hc,hg⟩
      exact ⟨fun t => hc t t.property,hg⟩
    · rintro ⟨hc,hg⟩
      exact ⟨fun t ht => hc ⟨t,ht⟩,hg⟩
  · intro c hc
    rw [layerExposure_weight s τ P b c hc]

end

section
open LayeredExchange Heisenberg.Cycle
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma invariant_of_agree (π σ : Equiv.Perm V) (A : Set V)
    (hA : ∀ x,π x ∈ A ↔ x ∈ A) (he : ∀ x ∈ A,π x = σ x) :
    ∀ x,σ x ∈ A ↔ x ∈ A := by
  intro x
  constructor
  · intro hx
    have hy : π.symm (σ x) ∈ A := (hA _).mp (by simpa using hx)
    have hs := he _ hy
    have hxy : π.symm (σ x) = x := σ.injective (by simpa using hs.symm)
    exact hxy ▸ hy
  · intro hx
    rw [← he x hx]
    exact (hA x).mpr hx

omit [Fintype V] [DecidableEq V] in
lemma residual_agrees {n : ℕ} (s : Equiv.Perm (Fin n)) (τ : Fin n → Equiv.Perm V)
    (P : Set (Fin n × V)) (base c : Fin n → Bool) :
    ∀ z ∈ MissingSet (layerHistory s τ base) P,
      layerHistory s τ base z = layerHistory s τ
        (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c) z := by
  apply (layer_matches_iff _ _ _ _ _).mpr
  intro t ht
  simp [residualCoins,ht]

omit [Fintype V] [DecidableEq V] in
lemma residual_invariant {n : ℕ} (s : Equiv.Perm (Fin n)) (τ : Fin n → Equiv.Perm V)
    (P : Set (Fin n × V)) (base c : Fin n → Bool) :
    ∀ z, layerHistory s τ
        (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c) z ∉
          MissingSet (layerHistory s τ base) P ↔ z ∉ MissingSet (layerHistory s τ base) P := by
  intro z
  exact not_congr (invariant_of_agree _ _ _ (missing_apply _ _)
    (residual_agrees s τ P base c) z)

lemma residual_determinantLaw {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (P : Set (Fin n × V)) (base : Fin n → Bool) (p : Fin n → ℝ) :
    let τ := fun i => Equiv.swap (a i) (b i)
    let M := layerRevealed τ (MissingSet (layerHistory s τ base) P)
    DeterminantLaw (fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i)
      (fun c => forwardHom (R:=ℝ) (layerHistory s τ (residualCoins M base c))) := by
  dsimp only
  let τ := fun i => Equiv.swap (a i) (b i)
  let M := layerRevealed τ (MissingSet (layerHistory s τ base) P)
  let fixed := fun i => if M i then some (if base i then τ i else 1) else none
  have h := determinantLaw_wiring s a b p fixed
  convert h using 1
  funext c
  apply congrArg (forwardHom (R:=ℝ))
  apply congrArg (wiring s)
  funext i
  change (if residualCoins M base c i then τ i else 1) =
    (fixed i).getD (if c i then τ i else 1)
  by_cases hi : M i <;> simp [fixed,residualCoins,hi]

attribute [local irreducible] MissingSet layerHistory

end

open Heisenberg.Cycle LayeredExchange
variable {V W : Type*}

lemma sameCycle_congr (e : V ≃ W) (π : Equiv.Perm V) (x y : V) :
    (e.permCongr π).SameCycle (e x) (e y) ↔ π.SameCycle x y := by
  change (∃ n : ℤ,((e.permCongr π)^n) (e x) = e y) ↔ ∃ n : ℤ,(π^n) x = y
  apply exists_congr
  intro n
  have he := map_zpow e.permCongrHom π n
  change e.permCongr (π^n) = (e.permCongr π)^n at he
  rw [←he,Equiv.permCongr_apply,Equiv.symm_apply_apply,e.injective.eq_iff]

lemma allHit_splitHolePerm (σ : Equiv.Perm V) (A P : Set V)
    (hA : ∀ x,σ x ∉ A ↔ x ∉ A) (hP : Disjoint A P) :
    AllHit (splitHolePerm σ A P hA) ↔ OutsideHit σ P A := by
  let e := Equiv.sumCompl (fun x : {z : V // z ∉ A} => x.val ∈ P)
  let π := σ.subtypePerm (p := fun z => z ∉ A) hA
  have he (x y) : (splitHolePerm σ A P hA).SameCycle x y ↔
      π.SameCycle (e x) (e y) := by
    have hh := sameCycle_congr e.symm π (e x) (e y)
    simpa only [Equiv.symm_apply_apply,e,splitHolePerm] using hh
  constructor
  · intro h x hx
    obtain ⟨j,hj⟩ := h (e.symm ⟨x,hx⟩)
    refine ⟨j.val.val,j.property,?_⟩
    have hc := (he _ _).mp hj
    rw [Equiv.apply_symm_apply] at hc
    exact Equiv.Perm.sameCycle_subtypePerm.mp hc
  · intro h x
    obtain ⟨j,hj,hc⟩ := h (e x).val (e x).property
    have hjA : j ∉ A := fun hA => Set.disjoint_left.mp hP hA hj
    let y : {x : {z : V // z ∉ A} // x.val ∈ P} := ⟨⟨j,hjA⟩,hj⟩
    refine ⟨y,(he _ _).mpr ?_⟩
    exact Equiv.Perm.sameCycle_subtypePerm.mpr hc

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HittingKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical

namespace Heisenberg.Hitting
open Filter
variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma mulVec_mono {W : Type*} [Fintype W] {A : Matrix V W ℝ} (hA : ∀ i j,0 ≤ A i j)
    {f g : W → ℝ} (h : f ≤ g) : A *ᵥ f ≤ A *ᵥ g := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (hA i j))

lemma affineIter_mono {A : Matrix V V ℝ} {b : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hb : 0 ≤ b) : Monotone (affineIter A b) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa [affineIter] using hb
  | succ n ih => exact add_le_add le_rfl (mulVec_mono hA ih)

lemma affineIter_super {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) (n : ℕ) :
    affineIter A b n ≤ g := by
  induction n with
  | zero => exact hg
  | succ n ih => exact (add_le_add le_rfl (mulVec_mono hA ih)).trans hs

lemma affineIter_bdd {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) (i : V) :
    BddAbove (Set.range (fun n => affineIter A b n i)) :=
  ⟨g i,fun _ ⟨n,hn⟩ => hn ▸ affineIter_super hA hg hs n i⟩

lemma affineIter_tendsto {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hb : 0 ≤ b)
    (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) (i : V) :
    Tendsto (fun n => affineIter A b n i) atTop (nhds (affineHit A b i)) :=
  tendsto_atTop_ciSup (fun _ _ h => affineIter_mono hA hb h i) (affineIter_bdd hA hg hs i)

lemma affineHit_fixed {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hb : 0 ≤ b)
    (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) : b + A *ᵥ affineHit A b = affineHit A b := by
  funext i
  have h₁ : Tendsto (fun n => b i + ∑ j,A i j * affineIter A b n j) atTop
      (nhds (b i + ∑ j,A i j * affineHit A b j)) :=
    tendsto_const_nhds.add (tendsto_finsetSum _
      (fun j _ => tendsto_const_nhds.mul (affineIter_tendsto hA hb hg hs j)))
  have h₂ := (affineIter_tendsto hA hb hg hs i).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h₁ h₂

lemma affineHit_super {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) :
    affineHit A b ≤ g := fun i => ciSup_le (fun n => affineIter_super hA hg hs n i)

variable [DecidableEq V]

theorem affineHit_inverse {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hb : 0 ≤ b)
    (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) (hd : (1-A).det ≠ 0) :
    affineHit A b = (1-A)⁻¹ *ᵥ b := by
  have he : (1-A) *ᵥ affineHit A b = b := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec]
    exact sub_eq_iff_eq_add.mpr (affineHit_fixed hA hb hg hs).symm
  calc
    affineHit A b = (1-A)⁻¹ *ᵥ ((1-A) *ᵥ affineHit A b) := by
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec]
    _ = (1-A)⁻¹ *ᵥ b := by rw [he]

end Heisenberg.Hitting
namespace Heisenberg.Exposure

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
omit [DecidableEq J] [DecidableEq Q] in
lemma backward_split_left (K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ) (g : (J ⊕ Q) → ℝ) :
    (K.transpose *ᵥ g) ∘ Sum.inl =
      K.toBlocks₁₁.transpose *ᵥ (g ∘ Sum.inl) + K.toBlocks₂₁.transpose *ᵥ (g ∘ Sum.inr) := by
  ext i
  simp [Matrix.mulVec, dotProduct,Fintype.sum_sum_type,Matrix.toBlocks₁₁,Matrix.toBlocks₂₁]

omit [DecidableEq J] [DecidableEq Q] in
lemma backward_split_right (K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ) (g : (J ⊕ Q) → ℝ) :
    (K.transpose *ᵥ g) ∘ Sum.inr =
      K.toBlocks₁₂.transpose *ᵥ (g ∘ Sum.inl) + K.toBlocks₂₂.transpose *ᵥ (g ∘ Sum.inr) := by
  ext i
  simp [Matrix.mulVec, dotProduct,Fintype.sum_sum_type,Matrix.toBlocks₁₂,Matrix.toBlocks₂₂]

omit [DecidableEq J] in
lemma resolvent_backward (K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ) (b : J → ℝ) :
    (hittingResolvent ℝ K).transpose *ᵥ b =
      K.toBlocks₁₁.transpose *ᵥ b + K.toBlocks₂₁.transpose *ᵥ
        ((1-K.toBlocks₂₂.transpose)⁻¹ *ᵥ (K.toBlocks₁₂.transpose *ᵥ b)) := by
  simp only [hittingResolvent,Matrix.transpose_add,Matrix.transpose_mul,
    Matrix.add_mulVec,Matrix.mulVec_mulVec,Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub,Matrix.transpose_one]

omit [DecidableEq J] in
theorem resolvent_le_supersolution (K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ)
    (hK : ∀ i j,0 ≤ K i j) (hd : (1-K.toBlocks₂₂).det ≠ 0)
    (b : J → ℝ) (hb : 0 ≤ b) (g : (J ⊕ Q) → ℝ) (hg : 0 ≤ g)
    (hP : b ≤ g ∘ Sum.inl)
    (hQ : (K.transpose *ᵥ g) ∘ Sum.inr ≤ g ∘ Sum.inr) :
    (hittingResolvent ℝ K).transpose *ᵥ b ≤ (K.transpose *ᵥ g) ∘ Sum.inl := by
  let A := K.toBlocks₂₂.transpose
  let c := K.toBlocks₁₂.transpose *ᵥ b
  have hA : ∀ i j,0 ≤ A i j := fun i j => hK (Sum.inr j) (Sum.inr i)
  have hc : 0 ≤ c := by
    intro i
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hK (Sum.inl j) (Sum.inr i)) (hb j))
  have hs : c + A *ᵥ (g ∘ Sum.inr) ≤ g ∘ Sum.inr := by
    apply le_trans (add_le_add (Hitting.mulVec_mono
      (A := K.toBlocks₁₂.transpose) (fun i j => hK (Sum.inl j) (Sum.inr i)) hP) le_rfl)
    exact (backward_split_right K g) ▸ hQ
  have hdA : (1-A).det ≠ 0 := by
    have he : 1-A = (1-K.toBlocks₂₂).transpose := by
      rw [Matrix.transpose_sub,Matrix.transpose_one]
    rw [he,Matrix.det_transpose]
    exact hd
  have hv := Hitting.affineHit_super hA (fun i => hg (Sum.inr i)) hs
  rw [Hitting.affineHit_inverse hA hc (fun i => hg (Sum.inr i)) hs hdA] at hv
  rw [resolvent_backward,backward_split_left]
  apply add_le_add
  · exact Hitting.mulVec_mono (fun i j => hK (Sum.inl j) (Sum.inl i)) hP
  · exact Hitting.mulVec_mono (fun i j => hK (Sum.inr j) (Sum.inl i)) hv

end

section
variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]

omit [Fintype J] [Fintype Q] in
lemma columnPerm_nonneg (π : Equiv.Perm (J ⊕ Q)) (i j : J ⊕ Q) :
    0 ≤ columnPerm ℝ π i j := by
  change 0 ≤ if i ∈ (Equiv.toPEquiv π) j then (1:ℝ) else 0
  split_ifs <;> norm_num

omit [DecidableEq Q] in
lemma nextPinMatrix_backward (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (b : J → ℝ) :
    (nextPinMatrix ℝ π h).transpose *ᵥ b = b ∘ nextPin π h := by
  ext j
  simp [Matrix.mulVec,dotProduct,nextPinMatrix]

theorem conditional_return_le (μ : Ω → ℝ) (hμ : ∀ ω,0 ≤ μ ω)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm ℝ (π ω)))
    (hz : hitWeight μ π ≠ 0) (T : Finset J)
    (g : (J ⊕ Q) → ℝ) (hg : 0 ≤ g)
    (hT : ∀ j ∈ T,1 ≤ g (Sum.inl j))
    (hQ : (((∑ ω,μ ω • columnPerm ℝ (π ω)).transpose *ᵥ g) ∘ Sum.inr) ≤ g ∘ Sum.inr) :
    (∑ ω,if hw : AllHit (π ω) then
      (μ ω / hitWeight μ π)*(∑ j ∈ T,if nextPin (π ω) hw j ∈ T then (1:ℝ) else 0) else 0) ≤
    ∑ j ∈ T,((∑ ω,μ ω • columnPerm ℝ (π ω)).transpose *ᵥ g) (Sum.inl j) := by
  let b : J → ℝ := fun j => if j ∈ T then 1 else 0
  let K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ := ∑ ω,μ ω • columnPerm ℝ (π ω)
  have hK : ∀ i j,0 ≤ K i j := by
    intro i j
    simp only [K,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hμ ω) (columnPerm_nonneg (π ω) i j))
  have hd : (1-K.toBlocks₂₂).det ≠ 0 := by rw [←allHit_determinant μ π h]; exact hz
  have hb : 0 ≤ b := by intro j; dsimp [b]; split_ifs <;> norm_num
  have hP : b ≤ g ∘ Sum.inl := by
    intro j
    dsimp [b]
    split_ifs with hj
    · exact hT j hj
    · exact hg _
  have hs := resolvent_le_supersolution K hK hd b hb g hg hP hQ
  have he := conditional_nextPin_first_moment μ π h hz
  have hv : (hittingResolvent ℝ K).transpose *ᵥ b =
      ∑ ω,if hw : AllHit (π ω) then
        (μ ω / hitWeight μ π) • (b ∘ nextPin (π ω) hw) else 0 := by
    rw [←he,Matrix.transpose_sum,Matrix.sum_mulVec]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs with hw
    · rw [Matrix.transpose_smul,Matrix.smul_mulVec,nextPinMatrix_backward]
    · simp
  have heq : (∑ ω,if hw : AllHit (π ω) then
      (μ ω / hitWeight μ π)*(∑ j ∈ T,if nextPin (π ω) hw j ∈ T then (1:ℝ) else 0) else 0) =
      ∑ j ∈ T,((hittingResolvent ℝ K).transpose *ᵥ b) j := by
    rw [hv]
    simp only [Finset.sum_apply,Finset.sum_comm (s:=T)]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hw : AllHit (π ω)
    · simp only [dite_eq_left hw,Pi.smul_apply,smul_eq_mul,Function.comp_apply,b]
      rw [Finset.mul_sum]
    · simp [hw]
  rw [heq]
  exact Finset.sum_le_sum (fun j _ => hs j)

end

open Matrix
variable {V Ω : Type*} [Fintype V] [Fintype Ω] [DecidableEq V]

lemma mean_perm_backward (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (g : V → ℝ) (x : V) :
    ((∑ c, μ c • (π c).permMatrix ℝ) *ᵥ g) x = ∑ c,μ c*g (π c x) := by
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply,Matrix.smul_mulVec,Matrix.permMatrix_mulVec,
    Pi.smul_apply,smul_eq_mul,Function.comp_apply]

lemma split_mean_backward (μ : Ω → ℝ) (σ : Ω → Equiv.Perm V) (A P : Set V)
    (hA : ∀ c x,σ c x ∉ A ↔ x ∉ A) (g : V → ℝ)
    (x : {x : {z : V // z ∉ A} // x.val ∈ P} ⊕
      {x : {z : V // z ∉ A} // x.val ∉ P}) :
    let e := Equiv.sumCompl (fun x : {z : V // z ∉ A} => x.val ∈ P)
    ((∑ c,μ c • columnPerm ℝ (splitHolePerm (σ c) A P (hA c))).transpose *ᵥ
      (fun z => g (e z).val)) x =
        ((∑ c,μ c • (σ c).permMatrix ℝ) *ᵥ g) (e x).val := by
  dsimp only
  simp only [columnPerm,Matrix.transpose_sum,Matrix.transpose_smul,Matrix.transpose_transpose]
  rw [mean_perm_backward,mean_perm_backward]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp [splitHolePerm,Equiv.permCongr_apply]

theorem split_conditional_return_le (μ : Ω → ℝ) (hμ : ∀ c,0 ≤ μ c)
    (σ : Ω → Equiv.Perm V) (A P : Set V)
    (hA : ∀ c x,σ c x ∉ A ↔ x ∉ A)
    (hd : DeterminantLaw μ (fun c => (σ c).permMatrix ℝ |>.transpose))
    (hz : hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c)) ≠ 0)
    (T : Finset {x : {z : V // z ∉ A} // x.val ∈ P})
    (g : V → ℝ) (hg : 0 ≤ g) (hT : ∀ j ∈ T,1 ≤ g j.val.val)
    (hQ : ∀ x,x ∉ A → x ∉ P → ((∑ c,μ c • (σ c).permMatrix ℝ) *ᵥ g) x ≤ g x) :
    (∑ c,if hw : AllHit (splitHolePerm (σ c) A P (hA c)) then
      (μ c / hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c))) *
        (∑ j ∈ T,if nextPin (splitHolePerm (σ c) A P (hA c)) hw j ∈ T then (1:ℝ) else 0) else 0) ≤
      ∑ j ∈ T,((∑ c,μ c • (σ c).permMatrix ℝ) *ᵥ g) j.val.val := by
  let e := Equiv.sumCompl (fun x : {z : V // z ∉ A} => x.val ∈ P)
  let π := fun c => splitHolePerm (σ c) A P (hA c)
  have hh := LayeredExchange.determinantLaw_holes (μ:=μ) (π:=σ) hd (fun z => z ∉ A) hA
  have hh' := LayeredExchange.determinantLaw_reindexed hh e
  have he : DeterminantLaw μ (fun c => columnPerm ℝ (π c)) := hh'
  have hg' : 0 ≤ (fun z => g (e z).val) := fun _ => hg _
  have hT' : ∀ j ∈ T,1 ≤ g (e (Sum.inl j)).val := hT
  have hQ' : (((∑ c,μ c • columnPerm ℝ (π c)).transpose *ᵥ
      (fun z => g (e z).val)) ∘ Sum.inr) ≤ (fun z => g (e z).val) ∘ Sum.inr := by
    intro x
    change ((∑ c,μ c • columnPerm ℝ (splitHolePerm (σ c) A P (hA c))).transpose *ᵥ
      (fun z => g (e z).val)) (Sum.inr x) ≤ g x.val.val
    rw [split_mean_backward]
    exact hQ x.val.val x.val.property x.property
  have h := conditional_return_le μ hμ π he hz T (fun z => g (e z).val) hg' hT' hQ'
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  exact (split_mean_backward μ σ A P hA g (Sum.inl j)).symm

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HittingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical

open scoped Classical
open Filter
namespace Heisenberg.Hitting

variable {V : Type*} [Fintype V]

lemma backward_mono {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    {f g : V → ℝ} (hfg : f ≤ g) : backward U f ≤ backward U g := by
  intro i
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hfg j) (hU.nonneg j i)

lemma backward_nonneg {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    {f : V → ℝ} (hf : 0 ≤ f) : 0 ≤ backward U f := by
  intro i
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hU.nonneg j i) (hf j))

lemma backward_le_one {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    {f : V → ℝ} (hf : f ≤ 1) : backward U f ≤ 1 := by
  intro i
  exact (Finset.sum_le_sum (fun j _ =>
    mul_le_of_le_one_right (hU.nonneg j i) (hf j))).trans (hU.col i)

lemma hitStep_mono {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) : Monotone (hitStep U T) := by
  intro f g h i
  dsimp [hitStep]
  split_ifs
  · rfl
  · exact backward_mono hU h i

lemma hitIter_bounds {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) (n : ℕ) : 0 ≤ hitIter U T n ∧ hitIter U T n ≤ 1 := by
  induction n with
  | zero => constructor <;> intro i <;> simp [hitIter] <;> split_ifs <;> norm_num
  | succ n ih =>
    constructor <;> intro i <;> dsimp [hitIter, hitStep] <;> split_ifs
    · norm_num
    · exact backward_nonneg hU ih.1 i
    · rfl
    · exact backward_le_one hU ih.2 i

lemma hitIter_mono {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) : Monotone (hitIter U T) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
    intro i
    dsimp [hitIter, hitStep]
    split_ifs
    · rfl
    · exact backward_nonneg hU (hitIter_bounds hU T 0).1 i
  | succ n ih => exact hitStep_mono hU T ih

lemma hitIter_bdd {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) (i : V) : BddAbove (Set.range (fun n => hitIter U T n i)) :=
  ⟨1, fun _ ⟨n, hn⟩ => hn ▸ (hitIter_bounds hU T n).2 i⟩

lemma hitIter_tendsto {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) (i : V) :
    Tendsto (fun n => hitIter U T n i) atTop (nhds (hitting U T i)) :=
  tendsto_atTop_ciSup (fun _ _ h => hitIter_mono hU T h i) (hitIter_bdd hU T i)

lemma hitting_bounds {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) : 0 ≤ hitting U T ∧ hitting U T ≤ 1 := by
  constructor
  · intro i
    exact (hitIter_bounds hU T 0).1 i |>.trans (le_ciSup (hitIter_bdd hU T i) 0)
  · intro i
    exact ciSup_le (fun n => (hitIter_bounds hU T n).2 i)

lemma hitting_on {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) {i : V} (hi : i ∈ T) : hitting U T i = 1 := by
  apply le_antisymm ((hitting_bounds hU T).2 i)
  have h := le_ciSup (hitIter_bdd hU T i) 0
  simpa only [hitIter, ite_eq_left hi, Pi.one_apply, hitting] using h

lemma hitting_harmonic {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) {i : V} (hi : i ∉ T) :
    backward U (hitting U T) i = hitting U T i := by
  have ha : Tendsto (fun n => backward U (hitIter U T n) i) atTop
      (nhds (backward U (hitting U T) i)) := by
    unfold backward
    exact tendsto_finsetSum _ (fun j _ => tendsto_const_nhds.mul (hitIter_tendsto hU T j))
  have hb : Tendsto (fun n => backward U (hitIter U T n) i) atTop
      (nhds (hitting U T i)) := by
    have ht := (hitIter_tendsto hU T i).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n => hitIter U T (n + 1) i) atTop _ at ht
    simpa only [hitIter, hitStep, ite_eq_right hi] using ht
  exact tendsto_nhds_unique ha hb

lemma energy_transpose (U : Matrix V V ℝ) (f : V → ℝ) :
    energy U f = ∑ i, f i * (f i - backward U f i) := by
  simp only [energy, backward, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hitting_energy {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) :
    energy U (hitting U T) = ∑ i ∈ T, (1 - backward U (hitting U T) i) := by
  rw [energy_transpose]
  rw [← Finset.sum_subset (Finset.subset_univ T)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hitting_on hU T hi, one_mul]
  · intro i _ hi
    rw [hitting_harmonic hU T hi, sub_self, mul_zero]

end Heisenberg.Hitting

namespace Heisenberg.Exposure
open Matrix Heisenberg.Hitting
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

lemma killedMean_substochastic (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (hs : ∑ c,μ c=1)
    (σ : Ω → Equiv.Perm V) (D : Set V) : DoublySubstochastic (killedMean μ σ D) := by
  have hn : ∀ i j,0≤killedMean μ σ D i j := by
    intro i j
    unfold killedMean
    split_ifs
    · exact Finset.sum_nonneg (fun c _ => mul_nonneg (hμ c) (by split_ifs <;> norm_num))
    · rfl
  constructor
  · exact hn
  · intro i
    calc
      _ ≤ ∑ j,∑ c,μ c*(if i=σ c j then 1 else 0) := by
        apply Finset.sum_le_sum
        intro j _
        unfold killedMean
        split_ifs
        · rfl
        · exact Finset.sum_nonneg (fun c _ => mul_nonneg (hμ c) (by split_ifs <;> norm_num))
      _ = 1 := by
        rw [Finset.sum_comm]
        simp only [←Finset.mul_sum]
        have he (c) : (∑ j : V,if i=σ c j then (1:ℝ) else 0)=1 := by
          convert Finset.sum_ite_eq' Finset.univ ((σ c).symm i) (fun _ => (1:ℝ)) using 1
          · apply Finset.sum_congr rfl
            intro j _
            congr 1
            exact propext (by rw [Equiv.eq_symm_apply,eq_comm])
          · simp
        simp only [he,mul_one,hs]
  · intro j
    calc
      _ ≤ ∑ i,∑ c,μ c*(if i=σ c j then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        unfold killedMean
        split_ifs
        · rfl
        · exact Finset.sum_nonneg (fun c _ => mul_nonneg (hμ c) (by split_ifs <;> norm_num))
      _ = 1 := by
        rw [Finset.sum_comm]
        simp only [←Finset.mul_sum]
        simpa using hs

lemma killedMean_backward (μ : Ω → ℝ) (σ : Ω → Equiv.Perm V) (D : Set V)
    (f : V → ℝ) (hf : ∀ x,x∉D → f x=0) (i : V) (hi : i∈D) :
    backward (killedMean μ σ D) f i = ∑ c,μ c*f (σ c i) := by
  unfold backward killedMean
  have he : ∀ j,(if j∈D ∧ i∈D then ∑ c,μ c*(if j=σ c i then 1 else 0) else 0)*f j =
      ∑ c,μ c*(if j=σ c i then f j else 0) := by
    intro j
    by_cases hj : j∈D
    · simp only [hj,hi,and_self,ite_true,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    · simp [hj,hf j hj]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp

lemma killed_hitting_supported (μ : Ω → ℝ) (σ : Ω → Equiv.Perm V) (D : Set V)
    (hK : DoublySubstochastic (killedMean μ σ D)) (T : Finset V)
    (hT : (T:Set V) ⊆ D) (x : V) (hx : x∉D) : hitting (killedMean μ σ D) T x=0 := by
  have ht : x∉T := fun h => hx (hT h)
  rw [←hitting_harmonic hK T ht]
  simp [backward,killedMean,hx]

theorem split_conditional_return_energy (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (hs : ∑ c,μ c=1)
    (σ : Ω → Equiv.Perm V) (A P D : Set V)
    (hA : ∀ c x,σ c x∉A ↔ x∉A)
    (hd : DeterminantLaw μ (fun c => (σ c).permMatrix ℝ |>.transpose))
    (hz : hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c))≠0)
    (T : Finset {x : {z : V // z∉A} // x.val∈P})
    (hT : ∀ j∈T,j.val.val∈D) (hQ : Aᶜ∩Pᶜ ⊆ D) :
    let U := killedMean μ σ D
    let T' := T.image (fun j => j.val.val)
    (∑ c,if hw : AllHit (splitHolePerm (σ c) A P (hA c)) then
      (μ c / hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c))) *
        (∑ j∈T,if nextPin (splitHolePerm (σ c) A P (hA c)) hw j∈T then (1:ℝ) else 0) else 0) ≤
      (T.card:ℝ)-energy U (hitting U T') := by
  dsimp only
  let T' := T.image (fun j => j.val.val)
  let U := killedMean μ σ D
  have hU := killedMean_substochastic μ hμ hs σ D
  let f := hitting U T'
  have hTD : (T':Set V) ⊆ D := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact hT j hj
  have hf : ∀ x,x∉D → f x=0 := killed_hitting_supported μ σ D hU T' hTD
  have hb := split_conditional_return_le μ hμ σ A P hA hd hz T f (hitting_bounds hU T').1
    (fun j hj => by
      change 1 ≤ hitting U T' j.val.val
      exact le_of_eq (hitting_on hU T' (Finset.mem_image.mpr ⟨j,hj,rfl⟩)).symm)
    (by
      intro x hxA hxP
      rw [mean_perm_backward,←killedMean_backward μ σ D f hf x (hQ ⟨hxA,hxP⟩)]
      have hxT : x∉T' := by
        intro hx
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
        exact hxP j.property
      exact le_of_eq (hitting_harmonic hU T' hxT))
  have hinj : Function.Injective (fun j : {x : {z : V // z∉A} // x.val∈P} => j.val.val) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  have he : energy U f = (T.card:ℝ)-∑ j∈T,backward U f j.val.val := by
    rw [hitting_energy hU T',Finset.sum_sub_distrib]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,T',Finset.card_image_of_injective _ hinj]
    rw [Finset.sum_image (by intro a _ b _ h; exact hinj h)]
  rw [he]
  have he' : (∑ j∈T,((∑ c,μ c • (σ c).permMatrix ℝ)*ᵥ f) j.val.val) =
      ∑ j∈T,backward U f j.val.val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mean_perm_backward,killedMean_backward μ σ D f hf _ (hT j hj)]
  rw [he'] at hb
  linarith

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ReturnConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter

open scoped Classical

namespace Heisenberg.Exposure
open Heisenberg.Return
variable {V : Type*} [Fintype V]

lemma semiconj_perm_pow {X Y : Type*} (f : X → Y) (π : Equiv.Perm X) (σ : Equiv.Perm Y)
    (hf : ∀ x,f (π x)=σ (f x)) (n : ℕ) (x : X) : f ((π^n) x)=(σ^n) (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,hf,ih,pow_succ',Equiv.Perm.mul_apply]

theorem split_nextPin_eq (σ : Equiv.Perm V) (A P : Set V)
    (hA : ∀ x,σ x∉A ↔ x∉A) (hP : Disjoint A P)
    (hh : AllHit (splitHolePerm σ A P hA))
    (j : {x : {z : V // z∉A} // x.val∈P}) :
    (nextPin (splitHolePerm σ A P hA) hh j).val.val =
      (nextPermutation σ P ⟨j.val.val,j.property⟩).val := by
  let e := Equiv.sumCompl (fun x : {z : V // z∉A} => x.val∈P)
  let f : _ → V := fun x => (e x).val
  let π := splitHolePerm σ A P hA
  have hf : ∀ x,f (π x)=σ (f x) := by
    intro x
    simp only [f,π,splitHolePerm,Equiv.permCongr_apply,Equiv.apply_symm_apply,e]
    rfl
  have hinj : Function.Injective f := Subtype.val_injective.comp e.injective
  have hi (k : {x : {z : V // z∉A} // x.val∈P}) : f (Sum.inl k)=k.val.val := rfl
  let i : P := ⟨j.val.val,j.property⟩
  let k : {x : {z : V // z∉A} // x.val∈P} :=
    ⟨⟨(nextPoint σ P i).val,fun h => Set.disjoint_left.mp hP h (nextPoint σ P i).property⟩,
      (nextPoint σ P i).property⟩
  let n := firstPinTime π hh (π (Sum.inl j))+1
  have hnp : (σ^n) i.val=(nextPin π hh j).val.val := by
    rw [show i.val=f (Sum.inl j) from rfl,←semiconj_perm_pow f π σ hf]
    rw [nextPin_spec,hi]
  have hmn : nextTime σ P i≤n := nextTime_min σ P i (Nat.succ_pos _)
    (hnp ▸ (nextPin π hh j).property)
  have hmj : (π^nextTime σ P i) (Sum.inl j)=Sum.inl k := by
    apply hinj
    rw [semiconj_perm_pow f π σ hf,hi,hi]
    exact nextPoint_spec σ P i
  have hnm : n≤nextTime σ P i := nextPin_is_first π hh j (nextTime_pos σ P i) hmj
  have he : n=nextTime σ P i := Nat.le_antisymm hnm hmn
  rw [he,nextPoint_spec] at hnp
  exact hnp.symm

end Heisenberg.Exposure

open scoped Classical
namespace Heisenberg.Conditioning
variable {Ω : Type*} [Fintype Ω]

lemma mass_eq (μ : Ω → ℝ) (E : Ω → Ω → Prop) (hE : Equivalence E)
    {a b : Ω} (hab : E a b) : mass μ E a=mass μ E b := by
  apply Finset.sum_congr rfl
  intro c _
  have hh : E a c ↔ E b c := ⟨fun h => hE.trans (hE.symm hab) h,fun h => hE.trans hab h⟩
  simp only [hh]

lemma weight_le_mass (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (E : Ω → Ω → Prop)
    (hr : ∀ b,E b b) (b : Ω) : μ b ≤ mass μ E b := by
  simpa only [mass,ite_eq_left (hr b)] using Finset.single_le_sum
    (s:=Finset.univ) (f:=fun c => if E b c then μ c else 0)
    (by intro c _; split_ifs; exact hμ c; rfl) (Finset.mem_univ b)

theorem tower (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (E : Ω → Ω → Prop)
    (hE : Equivalence E) (F : Ω → ℝ) :
    (∑ b,μ b*conditional μ E F b)=∑ c,μ c*F c := by
  simp only [conditional,Finset.sum_div,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : μ c=0
  · simp [hc]
  have hm : mass μ E c≠0 := ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hμ c) (Ne.symm hc))
    (weight_le_mass μ hμ E hE.refl c))
  have hs : (∑ b, μ b*((if E b c then μ c*F c else 0)/mass μ E b)) =
      (mass μ E c/mass μ E c)*(μ c*F c) := by
    change _ = (∑ b,if E c b then μ b else 0)/(mass μ E c)*(μ c*F c)
    rw [Finset.sum_div,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : E b c
    · rw [ite_eq_left hb,ite_eq_left (hE.symm hb),mass_eq μ E hE hb]
      ring
    · rw [ite_eq_right hb,ite_eq_right (fun h => hb (hE.symm h))]
      simp
  rw [hs,div_self hm,one_mul]

theorem expected_le (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (E : Ω → Ω → Prop)
    (hE : Equivalence E) (F G : Ω → ℝ)
    (h : ∀ b,μ b≠0 → conditional μ E F b≤G b) :
    (∑ c,μ c*F c)≤∑ b,μ b*G b := by
  rw [←tower μ hμ E hE F]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : μ b=0
  · simp [hb]
  · exact mul_le_mul_of_nonneg_left (h b hb) (hμ b)

end Heisenberg.Conditioning
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LayerEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.Conditioning
variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma layerExposure_equivalence {T : Type*} [Fintype T] (s : Equiv.Perm T)
    (τ : T → Equiv.Perm V) (P : Set (T×V)) : Equivalence (layerExposure s τ P) := by
  constructor
  · intro b
    exact ⟨fun _ _ => rfl,rfl⟩
  · intro b c h
    refine ⟨?_,h.2.symm⟩
    intro z hz
    exact (h.1 z (h.2 ▸ hz)).symm
  · intro b c d hbc hcd
    refine ⟨?_,hcd.2.trans hbc.2⟩
    intro z hz
    exact (hbc.1 z hz).trans (hcd.1 z (hbc.2.symm ▸ hz))

lemma residual_integral {n : ℕ} (w : Fin n → Bool → ℝ)
    (hw : ∀ i,∑ b,w i b=1) (M : Fin n → Prop) (base : Fin n → Bool)
    (F : (Fin n → Bool) → ℝ) :
    (∑ c : Fin n → Bool,productWeight w c * F (residualCoins M base c)) =
      ∑ c : {i // ¬M i} → Bool,productWeight (fun i : {i // ¬M i} => w i) c *
        F (merge M (fun i => base i) c) := by
  let e := Equiv.piEquivPiSubtypeProd M (fun _ => Bool)
  rw [←e.symm.sum_comp,Fintype.sum_prod_type]
  have hr (a : {i // M i} → Bool) (c : {i // ¬M i} → Bool) :
      residualCoins M base (merge M a c)=merge M (fun i => base i) c := by
    funext i
    by_cases hi : M i
    · simp [residualCoins,hi,merge]
    · simp [residualCoins,hi,merge]
  change (∑ a : {i // M i} → Bool, ∑ c : {i // ¬M i} → Bool,
    productWeight w (merge M a c)*F (residualCoins M base (merge M a c))) = _
  simp_rw [hr,productWeight_merge,mul_assoc,←Finset.mul_sum]
  have hs : (∑ a : {i // M i} → Bool, productWeight (fun i : {i // M i} => w i) a) = 1 := by
    convert productWeight_sum (fun i : {i // M i} => w i) (fun i => hw i) using 1
    congr 1
    ext c
    simp
  rw [←Finset.sum_mul, hs, one_mul]

theorem layer_exposure_full {n : ℕ} (s : Equiv.Perm (Fin n))
    (τ : Fin n → Equiv.Perm V) (w : Fin n → Bool → ℝ) (hw : ∀ i,∑ b,w i b=1)
    (P : Set (Fin n×V)) (base : Fin n → Bool) (F : (Fin n → Bool) → ℝ) :
    let A := MissingSet (layerHistory s τ base) P
    let M := layerRevealed τ A
    let c₀ := (2:ℝ)^missingCount (layerHistory s τ base) P *
      productWeight (fun i : {i // M i} => w i) (fun i => base i)
    (∑ c : Fin n → Bool,if layerExposure s τ P base c then
      productWeight w c*(2:ℝ)^missingCount (layerHistory s τ c) P*F c else 0) =
      c₀ * ∑ c : Fin n → Bool,if OutsideHit (layerHistory s τ (residualCoins M base c)) P A
        then productWeight w c*F (residualCoins M base c) else 0 := by
  dsimp only
  have he := layer_exposure_disintegration s τ w P base F
  have hu : @Finset.univ (Fin n → Bool)
    (@Pi.instFintype (Fin n) (fun _ => Bool) (fun a b => Classical.propDecidable (a=b))
      (Fin.fintype n) (fun _ => Bool.fintype)) = (Finset.univ : Finset (Fin n → Bool)) := by
    ext c
    simp
  rw [hu] at he
  refine he.trans ?_
  congr 1
  have h := residual_integral w hw
    (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base
    (fun c => if OutsideHit (layerHistory s τ c) P (MissingSet (layerHistory s τ base) P)
      then F c else 0)
  simp only [mul_ite,mul_zero] at h
  convert h.symm using 1
  congr 1
  ext c
  simp

theorem conditional_layer_exposure {n : ℕ} (s : Equiv.Perm (Fin n))
    (τ : Fin n → Equiv.Perm V) (w : Fin n → Bool → ℝ)
    (hw : ∀ i,∑ b,w i b=1) (hw0 : ∀ i b,0≤w i b)
    (P : Set (Fin n×V)) (base : Fin n → Bool) (F : (Fin n → Bool) → ℝ)
    (hbase : productWeight w base≠0) :
    let A := MissingSet (layerHistory s τ base) P
    let M := layerRevealed τ A
    let σ := fun c => layerHistory s τ (residualCoins M base c)
    let μ := fun c => productWeight w c*(2:ℝ)^missingCount (layerHistory s τ c) P
    conditional μ (layerExposure s τ P) F base =
      (∑ c : Fin n → Bool,if OutsideHit (σ c) P A then
        productWeight w c*F (residualCoins M base c) else 0)/
      (∑ c : Fin n → Bool,if OutsideHit (σ c) P A then productWeight w c else 0) := by
  dsimp only
  let μ := fun c => productWeight w c*(2:ℝ)^missingCount (layerHistory s τ c) P
  have hμ : ∀ c,0≤μ c := by
    intro c
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw0 i (c i))) (by positivity)
  have hm : 0 < mass μ (layerExposure s τ P) base := lt_of_lt_of_le
    (mul_pos (lt_of_le_of_ne (Finset.prod_nonneg (fun i _ => hw0 i (base i))) (Ne.symm hbase))
      (by positivity))
    (weight_le_mass μ hμ _ (layerExposure_equivalence s τ P).refl base)
  have hden := layer_exposure_full s τ w hw P base (fun _ => 1)
  simp only [mul_one] at hden
  change mass μ (layerExposure s τ P) base = _ at hden
  have hq := left_ne_zero_of_mul (hden ▸ ne_of_gt hm)
  rw [conditional,layer_exposure_full s τ w hw P base F]
  change (_*_) / mass μ (layerExposure s τ P) base = _
  rw [hden]
  exact mul_div_mul_left _ _ hq

end Heisenberg.Exposure

open Filter Topology
open scoped RealInnerProductSpace Classical
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_KilledContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.MatrixContraction

variable {V : Type*} [Fintype V]

lemma DoublySubstochastic.mul {U W : Matrix V V ℝ}
    (hU : DoublySubstochastic U) (hW : DoublySubstochastic W) :
    DoublySubstochastic (U * W) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hU.nonneg i k) (hW.nonneg k j))
  · intro i
    change (∑ j, ∑ k, U i k * W k j) ≤ 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    exact (Finset.sum_le_sum (fun k _ =>
      mul_le_of_le_one_right (hU.nonneg i k) (hW.row k))).trans (hU.row i)
  · intro j
    change (∑ i, ∑ k, U i k * W k j) ≤ 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    exact (Finset.sum_le_sum (fun k _ =>
      mul_le_of_le_one_left (hW.nonneg k j) (hU.col k))).trans (hW.col j)

lemma weighted_square (w f : V → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * f i)
  simpa only [← mul_assoc, Real.mul_self_sqrt (hw _), mul_pow,
    Real.sq_sqrt (hw _)] using h

theorem contraction {U : Matrix V V ℝ} (hU : DoublySubstochastic U) (f : V → ℝ) :
    ∑ i, ((U.mulVec f) i) ^ 2 ≤ ∑ i, (f i) ^ 2 := by
  calc
    _ ≤ ∑ i, (∑ j, U i j) * (∑ j, U i j * f j ^ 2) := by
      exact Finset.sum_le_sum (fun i _ => weighted_square (U i) f (hU.nonneg i))
    _ ≤ ∑ i, ∑ j, U i j * f j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_left
        (Finset.sum_nonneg (fun j _ => mul_nonneg (hU.nonneg i j) (sq_nonneg _))) (hU.row i)
    _ = ∑ j, (∑ i, U i j) * f j ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_of_le_one_left (sq_nonneg _) (hU.col j))

theorem of_partial_permutation (p : V → Option V)
    (hp : ∀ i j a, p i = some a → p j = some a → i = j) :
    DoublySubstochastic (fun i j => if p j = some i then 1 else 0) := by
  constructor
  · intro i j; split_ifs <;> norm_num
  · intro i
    have hc : (Finset.univ.filter fun j => p j = some i).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj k hk
      exact hp j k i (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
    simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.cast_le_one] using (show ((Finset.univ.filter fun j => p j = some i).card : ℝ) ≤ 1 by
        exact_mod_cast hc)
  · intro j
    cases hj : p j with
    | none => simp
    | some i => simp

theorem weighted_average {I : Type*} [Fintype I] (w : I → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (U : I → Matrix V V ℝ)
    (hU : ∀ a, DoublySubstochastic (U a)) :
    DoublySubstochastic (fun i j => ∑ a, w a * U a i j) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) ((hU a).nonneg i j))
  · intro i
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ a, w a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right (hw a) ((hU a).row i))
      _ = 1 := hs
  · intro j
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ a, w a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right (hw a) ((hU a).col j))
      _ = 1 := hs

lemma dot_half (f g : V → ℝ) :
    2 * dot f g ≤ squareNorm f + squareNorm g := by
  have h : 0 ≤ ∑ i, (f i - g i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have he : (∑ i, (f i - g i) ^ 2) = squareNorm f + squareNorm g - 2 * dot f g := by
    unfold squareNorm dot
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    ring_nf
  linarith

lemma dot_transpose (B : Matrix V V ℝ) (f g : V → ℝ) :
    dot f (B.mulVec g) = dot (B.transpose.mulVec f) g := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem two_ends (A M B : Matrix V V ℝ) (hM : DoublySubstochastic M) (f : V → ℝ) :
    squareNorm f - dot f ((B * M * A).mulVec f) ≥
      ((squareNorm f - squareNorm (A.mulVec f)) +
       (squareNorm f - squareNorm (B.transpose.mulVec f))) / 2 := by
  have he : (B * M * A).mulVec f = B.mulVec (M.mulVec (A.mulVec f)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [he, dot_transpose]
  have h := dot_half (B.transpose.mulVec f) (M.mulVec (A.mulVec f))
  have hc := contraction hM (A.mulVec f)
  change squareNorm (M.mulVec (A.mulVec f)) ≤ squareNorm (A.mulVec f) at hc
  linarith

end Heisenberg.MatrixContraction

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_QuietSweeps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.MeshPair

open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma killedBetween_substochastic (D E : Set V) (σ : Equiv.Perm V) :
    DoublySubstochastic (killedBetween D E σ) := by
  let p : V → Option V := fun j => if j∈D ∧ σ j∈E then some (σ j) else none
  have hp : ∀ i j a,p i=some a → p j=some a → i=j := by
    intro i j a hi hj
    dsimp [p] at hi hj
    split_ifs at hi hj
    exact σ.injective ((Option.some.inj hi).trans (Option.some.inj hj).symm)
  have hh := of_partial_permutation p hp
  have he : killedBetween D E σ = fun i j => if p j=some i then 1 else 0 := by
    funext i j
    dsimp [killedBetween,p]
    by_cases hj : j∈D
    · by_cases he : σ j∈E
      · simp only [hj,he,and_self,ite_true,true_and,Option.some.injEq]
        by_cases h : i=σ j
        · subst i; simp [he]
        · simp [h,Ne.symm h]
      · simp only [hj,he,and_false,ite_false,true_and,reduceCtorEq,ite_false]
        split_ifs with h
        · exact False.elim (he (h.2 ▸ h.1))
        · rfl
    · simp [hj]
  rw [he]
  convert hh using 1
  apply Iff.of_eq
  apply congrArg DoublySubstochastic
  funext i j
  split_ifs <;> rfl

omit [Fintype V] in
lemma killedBetween_transpose (D E : Set V) (σ : Equiv.Perm V) :
    (killedBetween D E σ).transpose=killedBetween E D σ.symm := by
  ext i j
  simp only [killedBetween,Matrix.transpose_apply]
  have he : j=σ i ↔ i=σ.symm j := by rw [eq_comm,Equiv.eq_symm_apply,eq_comm]
  simp only [he]
  congr 1
  exact propext (by tauto)

lemma residualBetween_substochastic (D E : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    DoublySubstochastic (residualBetween D E revealed c a b p) := by
  by_cases hr : revealed
  · simp only [residualBetween,ite_eq_left hr]
    exact killedBetween_substochastic _ _ _
  · simp only [residualBetween,ite_eq_right hr]
    have h := weighted_average (fun z : Bool => if z then p else 1-p)
      (by intro z; cases z <;> simp <;> linarith)
      (by simp) (fun z => killedBetween D E (if z then Equiv.swap a b else 1))
      (fun _ => killedBetween_substochastic _ _ _)
    have he : (1-p) • killedBetween D E 1 + p • killedBetween D E (Equiv.swap a b) =
        (fun i j => ∑ z : Bool,(if z then p else 1-p)*killedBetween D E (if z then Equiv.swap a b else 1) i j) := by
      ext i j
      simp [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_comm]
    rw [he]
    exact h

omit [Fintype V] in
lemma residualBetween_transpose (D E : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) :
    (residualBetween D E revealed c a b p).transpose = residualBetween E D revealed c a b p := by
  unfold residualBetween
  by_cases hr : revealed
  · simp only [ite_eq_left hr,killedBetween_transpose]
    cases c <;> simp [show (Equiv.symm (1:Equiv.Perm V))=1 from rfl]
  · simp only [ite_eq_right hr,Matrix.transpose_add,Matrix.transpose_smul,killedBetween_transpose]
    simp [show (Equiv.symm (1:Equiv.Perm V))=1 from rfl]

end Heisenberg.MeshPair

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] [Fintype V] in
lemma layerRevealed_swap (a b : T → V) (A : Set (T×V)) (t : T) (hab : a t≠b t) :
    layerRevealed (fun i => Equiv.swap (a i) (b i)) A t ↔ (t,a t)∈A ∨ (t,b t)∈A := by
  constructor
  · rintro ⟨v,hv,hn⟩
    by_cases ha : v=a t
    · exact Or.inl (ha ▸ hv)
    · have hb : v=b t := by
        by_contra hb
        exact hn (Equiv.swap_apply_of_ne_of_ne ha hb)
      exact Or.inr (hb ▸ hv)
  · rintro (ha|hb)
    · exact ⟨a t,ha,by simpa using hab.symm⟩
    · exact ⟨b t,hb,by simpa using hab⟩

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExposedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.Exposure
open Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] in
lemma exposedStep_substochastic (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1) (t : T) :
    Heisenberg.MatrixContraction.DoublySubstochastic (exposedStep s a b base P I p t) :=
  residualBetween_substochastic _ _ _ _ _ _ _ (hp t).1 (hp t).2

end Heisenberg.Exposure

open scoped BigOperators Classical
namespace Heisenberg.Bernoulli
variable {I : Type*} [Fintype I]

lemma weight_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (c : I → Bool) :
    0 ≤ weight p c := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [(hp i).1,(hp i).2]

lemma test_insert (s : Finset I) (i : I) (c : I → Bool) :
    test (insert i s) c = (if c i then 1 else 0)*test s c := by
  simp only [test,Finset.forall_mem_insert]
  split_ifs <;> simp_all

lemma test_eq_prod (s : Finset I) (c : I → Bool) :
    test s c = ∏ i ∈ s, if c i then (1:ℝ) else 0 := by
  induction s using Finset.induction_on with
  | empty => simp [test]
  | @insert i s hi ih => rw [test_insert,Finset.prod_insert hi,ih]

lemma weight_test_sum (p : I → ℝ) (s : Finset I) :
    (∑ c,weight p c*test s c) = ∏ i ∈ s,p i := by
  have he (c : I → Bool) : weight p c*test s c =
      ∏ i, if c i then p i else if i ∈ s then 0 else 1-p i := by
    rw [test_eq_prod]
    have ht : (∏ i ∈ s, if c i then (1:ℝ) else 0) = ∏ i,if i ∈ s then (if c i then (1:ℝ) else 0) else 1 := by
      simp only [Finset.prod_ite_mem,Finset.univ_inter]
    rw [ht,weight,←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> cases c i <;> simp [hi]
  simp_rw [he]
  rw [←Fintype.prod_sum (fun i (b : Bool) => if b then p i else if i ∈ s then 0 else 1-p i)]
  simp only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
  have he : (fun i => p i + if i ∈ s then (0:ℝ) else 1-p i) = fun i => if i ∈ s then p i else 1 := by
    funext i
    split_ifs <;> ring
  rw [he]
  simp only [Finset.prod_ite_mem,Finset.univ_inter]

end Heisenberg.Bernoulli
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CycleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix
open Filter
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped BigOperators Classical

namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.Bernoulli
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype T] [Fintype V] in
lemma layerWeight_nonneg (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) :
    0 ≤ layerWeight s a b P c := by unfold layerWeight; positivity

omit [Fintype T] [Fintype V] in
lemma layerWeight_one_le (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) :
    1 ≤ layerWeight s a b P c := one_le_pow₀ (by norm_num)

lemma coin_weight_sum (p : T → ℝ) : (∑ c,weight p c)=1 := by
  simpa [Bernoulli.test] using weight_test_sum p ∅

omit [Fintype V] in
lemma layerPartition_one_le (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) : 1≤layerPartition s a b P p := by
  rw [←coin_weight_sum p]
  exact Finset.sum_le_sum fun c _ => le_mul_of_one_le_right (weight_nonneg p hp c) (layerWeight_one_le s a b P c)

omit [Fintype V] in
lemma layerMass_nonneg (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (c : T → Bool) : 0≤layerMass s a b P p c := by
  exact div_nonneg (mul_nonneg (weight_nonneg p hp c) (layerWeight_nonneg s a b P c))
    (le_trans (by norm_num) (layerPartition_one_le s a b P p hp))

end

open Heisenberg.MeshPair Heisenberg.Bernoulli

end Heisenberg.Exposure

open scoped Classical

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RoundEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped BigOperators Classical

open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma euclideanMap_mul (A B : Matrix V V ℝ) (v : EuclideanSpace ℝ V) :
    euclideanMap (A*B) v = euclideanMap A (euclideanMap B v) := by
  ext i
  change ((A*B).mulVec v.ofLp) i = (A.mulVec (B.mulVec v.ofLp)) i
  rw [Matrix.mulVec_mulVec]

lemma substochastic_one : DoublySubstochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro i j; simp only [Matrix.one_apply]; split_ifs <;> norm_num
  · intro i
    change (∑ j, if i=j then (1:ℝ) else 0)≤1
    simp
  · intro i
    change (∑ j, if j=i then (1:ℝ) else 0)≤1
    simp

lemma prefix_substochastic (K : ℕ → Matrix V V ℝ) (n : ℕ)
    (hK : ∀ i,i<n → DoublySubstochastic (K i)) : DoublySubstochastic (prefixMatrix K n) := by
  induction n with
  | zero => exact substochastic_one
  | succ n ih => exact (hK n (by omega)).mul (ih (fun i hi=>hK i (by omega)))

lemma prefix_add (K : ℕ → Matrix V V ℝ) (m n : ℕ) :
    prefixMatrix K (m+n)=prefixMatrix (fun i=>K (m+i)) n*prefixMatrix K m := by
  induction n with
  | zero => simp [prefixMatrix]
  | succ n ih =>
    change K (m+n)*prefixMatrix K (m+n)=(K (m+n)*prefixMatrix (fun i=>K (m+i)) n)*prefixMatrix K m
    rw [ih,Matrix.mul_assoc]

end Heisenberg.MeshPair

namespace Heisenberg.Exposure
open Heisenberg.MeshPair Heisenberg.MatrixContraction
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] in
lemma exposedSweep_prefix (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) (n : ℕ)
    (v : EuclideanSpace ℝ V) :
    exposedSweep s a b base P I p r n v =
      euclideanMap (prefixMatrix (fun i=>exposedStep s a b base P I p (r i)) n) v := by
  induction n with
  | zero => simp [exposedSweep,prefixMatrix]
  | succ n ih => rw [exposedSweep,prefixMatrix,euclideanMap_mul,ih]

end Heisenberg.Exposure

open scoped BigOperators Classical RealInnerProductSpace
open Filter Topology
open scoped BigOperators Classical RealInnerProductSpace
open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CyclicEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical RealInnerProductSpace

open Filter Topology
open scoped RealInnerProductSpace Classical

open scoped Classical
open Filter
namespace Heisenberg.Serial

open Matrix Heisenberg.Hitting
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma backward_profile (n : ℕ) (K : Fin n → Matrix V V ℝ) (f : Fin (n+1) → V → ℝ)
    (hf : ∀ i,(K i).transpose*ᵥ f i.succ=f i.castSucc) :
    (product n K).transpose*ᵥ f (Fin.last n)=f 0 := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [product,Matrix.transpose_mul,←Matrix.mulVec_mulVec]
    have hh := ih (fun i => K i.succ) (fun i => f i.succ) (fun i => hf i.succ)
    change (product n (fun i => K i.succ)).transpose*ᵥ f (Fin.last (n+1))=f 1 at hh
    rw [hh]
    exact hf 0

omit [DecidableEq V] in
lemma cyclicKernel_backward (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (f : Fin (n+1) × V → ℝ) (t : Fin (n+1)) (v : V) :
    backward (cyclicKernel n K) f (t,v) =
      ((K t).transpose*ᵥ (fun w => f (finRotate (n+1) t,w))) v := by
  simp only [backward,cyclicKernel,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (finRotate (n+1) t)]
  · simp [Matrix.mulVec,dotProduct]
  · intro u _ hu
    simp only [hu, ite_false, zero_mul, Finset.sum_const_zero]
  · simp

omit [DecidableEq V] in
lemma cyclicKernel_substochastic (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (hK : ∀ t,DoublySubstochastic (K t)) : DoublySubstochastic (cyclicKernel n K) := by
  constructor
  · intro ⟨t,i⟩ ⟨u,j⟩
    dsimp [cyclicKernel]
    split_ifs
    · exact (hK u).nonneg i j
    · rfl
  · intro ⟨t,i⟩
    simp only [cyclicKernel,Fintype.sum_prod_type]
    rw [Finset.sum_eq_single ((finRotate (n+1)).symm t)]
    · simpa using (hK ((finRotate (n+1)).symm t)).row i
    · intro u _ hu
      have he : t≠finRotate (n+1) u := by
        intro h
        exact hu (by rw [h,Equiv.symm_apply_apply])
      simp only [he, ite_false, Finset.sum_const_zero]
    · simp
  · intro ⟨t,j⟩
    simp only [cyclicKernel,Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (finRotate (n+1) t)]
    · simpa using (hK t).col j
    · intro u _ hu
      simp only [hu, ite_false, Finset.sum_const_zero]
    · simp

end Heisenberg.Serial

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HoleReturns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
open Filter

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical

attribute [local instance] exposureDecEq
attribute [-instance] exposureDecEq

namespace Heisenberg.Exposure
open Heisenberg.Return Heisenberg.Hitting Heisenberg.Cycle
variable {V Ω : Type*} [Fintype V] [Fintype Ω]
variable [DecidableEq V]

lemma returnCount_split (σ : Equiv.Perm V) (A P : Set V)
    (hA : ∀ x,σ x∉A ↔ x∉A) (hP : Disjoint A P)
    (hh : AllHit (splitHolePerm σ A P hA)) (T : Finset P) :
    let H := T.map (holePinEquiv A P hP).symm.toEmbedding
    (∑ j∈H,if nextPin (splitHolePerm σ A P hA) hh j∈H then (1:ℝ) else 0) =
      returnCount σ P T := by
  dsimp only
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j _
  have he : nextPin (splitHolePerm σ A P hA) hh ((holePinEquiv A P hP).symm j) =
      (holePinEquiv A P hP).symm (nextPermutation σ P j) := by
    apply Subtype.ext
    apply Subtype.ext
    exact split_nextPin_eq σ A P hA hP hh _
  simp only [Equiv.toEmbedding_apply,he,Finset.mem_map_equiv,Equiv.symm_symm,Equiv.apply_symm_apply]

omit [Fintype V] in
lemma holePins_image (A P : Set V) (hP : Disjoint A P) (T : Finset P) :
    (T.map (holePinEquiv A P hP).symm.toEmbedding).image (fun j => j.val.val) =
      T.image (fun j => j.val) := by
  rw [Finset.map_eq_image,Finset.image_image]
  rfl

theorem outside_return_energy (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (hs : ∑ c,μ c=1)
    (σ : Ω → Equiv.Perm V) (A P D : Set V)
    (hA : ∀ c x,σ c x∉A ↔ x∉A) (hP : Disjoint A P)
    (hd : DeterminantLaw μ (fun c => (σ c).permMatrix ℝ |>.transpose))
    (hz : (∑ c,if OutsideHit (σ c) P A then μ c else 0)≠0)
    (T : Finset P) (hT : ∀ j∈T,j.val∈D) (hQ : Aᶜ∩Pᶜ ⊆ D) :
    (∑ c,if OutsideHit (σ c) P A then μ c*returnCount (σ c) P T else 0) /
      (∑ c,if OutsideHit (σ c) P A then μ c else 0) ≤
      (T.card:ℝ)-energy (killedMean μ σ D) (hitting (killedMean μ σ D) (T.image Subtype.val)) := by
  let H := T.map (holePinEquiv A P hP).symm.toEmbedding
  have hz' : hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c)) ≠ 0 := by
    simpa only [hitWeight,allHit_splitHolePerm _ _ _ _ hP] using hz
  have hH : ∀ j∈H,j.val.val∈D := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact hT i hi
  have h := split_conditional_return_energy μ hμ hs σ A P D hA hd hz' H hH hQ
  dsimp only at h
  rw [show H.card=T.card from Finset.card_map _,holePins_image A P hP T] at h
  convert h using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : OutsideHit (σ c) P A
  · have hh := (allHit_splitHolePerm (σ c) A P (hA c) hP).mpr hc
    rw [ite_eq_left hc,dite_eq_left hh,returnCount_split (σ c) A P (hA c) hP hh T]
    unfold hitWeight
    simp only [allHit_splitHolePerm _ _ _ _ hP]
    ring
  · rw [ite_eq_right hc,dite_eq_right (fun h => hc ((allHit_splitHolePerm _ _ _ _ hP).mp h))]
    exact zero_div _

end Heisenberg.Exposure

namespace Heisenberg.Exposure
attribute [local irreducible] killedMean Heisenberg.Hitting.hitting Heisenberg.Hitting.energy Heisenberg.Cycle.MissingSet layerHistory
open Heisenberg.Return Heisenberg.Hitting Heisenberg.Cycle Heisenberg.Conditioning
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exposed_layer_energy {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (p : Fin n → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1) (P : Set (Fin n×V))
    (base : Fin n → Bool)
    (hbase : productWeight (fun i z => if z then p i else 1-p i) base≠0)
    (D : Set (Fin n×V)) (T : Finset P)
    (hT : ∀ j∈T,j.val∈D)
    (hQ : (MissingSet (layerHistory s (fun i => Equiv.swap (a i) (b i)) base) P)ᶜ∩Pᶜ ⊆ D) :
    let τ := fun i => Equiv.swap (a i) (b i)
    let μ₀ := productWeight (fun i z => if z then p i else 1-p i)
    let μ := fun c => μ₀ c*(2:ℝ)^missingCount (layerHistory s τ c) P
    let M := layerRevealed τ (MissingSet (layerHistory s τ base) P)
    let σ := fun c => layerHistory s τ (residualCoins M base c)
    conditional μ (layerExposure s τ P) (fun c => returnCount (layerHistory s τ c) P T) base ≤
      (T.card:ℝ)-energy (killedMean μ₀ σ D) (hitting (killedMean μ₀ σ D) (T.image Subtype.val)) := by
  dsimp only
  let τ := fun i => Equiv.swap (a i) (b i)
  let w : Fin n → Bool → ℝ := fun i z => if z then p i else 1-p i
  have hw : ∀ i,∑ z,w i z=1 := by intro i; simp [w]
  have hw0 : ∀ i z,0≤w i z := by
    intro i z
    cases z <;> simp only [w,Bool.false_eq_true,↓reduceIte] <;> linarith [(hp i).1,(hp i).2]
  let A := MissingSet (layerHistory s τ base) P
  let M := layerRevealed τ A
  let σ := fun c => layerHistory s τ (residualCoins M base c)
  have hσ : σ base=layerHistory s τ base := by
    change layerHistory s τ (residualCoins M base base)=layerHistory s τ base
    apply congrArg (layerHistory s τ)
    funext i
    simp only [residualCoins,ite_self]
  have ho : OutsideHit (σ base) P A := by
    rw [hσ]
    exact (sameMissing_iff_outsideHit _ _ P (fun _ _ => rfl)).mp rfl
  have hμ : ∀ c,0≤productWeight w c := productWeight_nonneg w hw0
  have hz : (∑ c : Fin n → Bool,if OutsideHit (σ c) P A then productWeight w c else 0)≠0 := by
    apply ne_of_gt
    have hb : 0<productWeight w base := lt_of_le_of_ne (hμ base) (Ne.symm hbase)
    exact lt_of_lt_of_le hb (by
      have he : productWeight w base=(if OutsideHit (σ base) P A then productWeight w base else 0) := (ite_eq_left ho).symm
      rw [he]
      apply Finset.single_le_sum _ (Finset.mem_univ base)
      intro c _
      split_ifs
      · exact hμ c
      · exact le_rfl)
  rw [conditional_layer_exposure s τ w hw hw0 P base _ hbase]
  have hs : (∑ c : Fin n → Bool,productWeight w c)=1 := by
    convert productWeight_sum w hw using 1
    congr 1
    ext c
    simp
  have hd : DeterminantLaw (productWeight w)
      (fun c => (σ c).permMatrix ℝ |>.transpose) := by
    exact residual_determinantLaw s a b P base p
  have hh := outside_return_energy (productWeight w) hμ hs σ A P D
    (fun c => residual_invariant s τ P base c) (missing_disjoint_pins _ P) hd hz T hT hQ
  exact hh

end Heisenberg.Exposure
end
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
-- module Solutions.OAIW2_Heis.Heisenberg_AveragedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
open Filter
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
attribute [local instance] exposureDecEq
attribute [-instance] exposureDecEq

namespace Heisenberg.Exposure
attribute [local irreducible] killedMean Heisenberg.Hitting.hitting Heisenberg.Hitting.energy Heisenberg.Cycle.MissingSet layerHistory
open Heisenberg.Return Heisenberg.Hitting Heisenberg.Cycle Heisenberg.Conditioning
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem averaged_layer_energy {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (p : Fin n → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1) (P : Set (Fin n×V))
    (D : (Fin n → Bool) → Set (Fin n×V)) (T : Finset P)
    (hT : ∀ base j,j∈T → j.val∈D base)
    (hQ : ∀ base,(MissingSet (layerHistory s (fun i => Equiv.swap (a i) (b i)) base) P)ᶜ∩Pᶜ ⊆ D base) :
    let τ := fun i => Equiv.swap (a i) (b i)
    let μ₀ := productWeight (fun i z => if z then p i else 1-p i)
    let μ := fun c => μ₀ c*(2:ℝ)^missingCount (layerHistory s τ c) P
    let θ := fun c => μ c/(∑ b,μ b)
    let σ := fun base c => layerHistory s τ
      (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c)
    (∑ c,θ c*returnCount (layerHistory s τ c) P T) ≤ (T.card:ℝ)-
      ∑ base,θ base*energy (killedMean μ₀ (σ base) (D base))
        (hitting (killedMean μ₀ (σ base) (D base)) (T.image Subtype.val)) := by
  dsimp only
  let τ := fun i => Equiv.swap (a i) (b i)
  let w : Fin n → Bool → ℝ := fun i z => if z then p i else 1-p i
  let μ := fun c => productWeight w c*(2:ℝ)^missingCount (layerHistory s τ c) P
  let Z := ∑ c,μ c
  let e := fun base => energy
    (killedMean (productWeight w) (fun c => layerHistory s τ
      (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c)) (D base))
    (hitting (killedMean (productWeight w) (fun c => layerHistory s τ
      (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c)) (D base))
      (T.image Subtype.val))
  have hw0 : ∀ i z,0≤w i z := by
    intro i z
    cases z <;> simp only [w,Bool.false_eq_true,↓reduceIte] <;> linarith [(hp i).1,(hp i).2]
  have hμ : ∀ c,0≤μ c := fun c => mul_nonneg (productWeight_nonneg w hw0 c) (by positivity)
  have hZ : 0<Z := by
    have hs : (∑ c : Fin n → Bool,productWeight w c)=1 := by
      convert productWeight_sum w (by intro i; simp [w]) using 1
      congr 1
      ext c
      simp
    apply lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    rw [←hs]
    exact Finset.sum_le_sum (fun c _ => le_mul_of_one_le_right (productWeight_nonneg w hw0 c)
      (one_le_pow₀ (by norm_num)))
  have h : (∑ c,μ c*returnCount (layerHistory s τ c) P T)≤∑ c,μ c*((T.card:ℝ)-e c) := by
    apply expected_le μ hμ (layerExposure s τ P) (layerExposure_equivalence s τ P)
    intro base hb
    simpa only [τ,μ,w,e] using
      (exposed_layer_energy s a b p hp P base (left_ne_zero_of_mul hb) (D base) T (hT base) (hQ base))
  have hh := div_le_div_of_nonneg_right h hZ.le
  have he : (∑ c,μ c*((T.card:ℝ)-e c))/Z = (T.card:ℝ)-(∑ c,μ c*e c)/Z := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
    change (Z*(T.card:ℝ)-(∑ c,μ c*e c))/Z = _
    rw [sub_div,mul_div_cancel_left₀ _ hZ.ne']
  rw [he] at hh
  simpa only [Finset.sum_div,div_mul_eq_mul_div] using hh

end Heisenberg.Exposure

end
end
end
end
end
end
end
end
end

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.Exposure
open Matrix
open scoped BigOperators
variable {T B V : Type*} [Fintype T] [Fintype B] [Fintype V]

lemma productWeight_coordinate (w : T → B → ℝ) (hw : ∀ t, ∑ b,w t b = 1)
    (t : T) (F : B → ℝ) :
    (∑ c : T → B,productWeight w c * F (c t)) = ∑ b,w t b * F b := by
  classical
  let w' : T → B → ℝ := Function.update w t (fun b => w t b * F b)
  have he : ∀ c,productWeight w c * F (c t) = productWeight w' c := by
    intro c
    have hh : (fun i => w' i (c i)) = Function.update (fun i => w i (c i)) t
        (w t (c t) * F (c t)) := by
      funext i
      by_cases hi : i = t <;> simp [w',hi]
    rw [productWeight,productWeight,hh,Finset.prod_update_of_mem (Finset.mem_univ t)]
    rw [←Finset.mul_prod_erase Finset.univ (fun i => w i (c i)) (Finset.mem_univ t)]
    rw [Finset.erase_eq]
    ring
  simp_rw [he,productWeight]
  rw [←Fintype.prod_sum]
  rw [Finset.prod_eq_single t]
  · simp [w']
  · intro i _ hi
    simpa [w',hi] using hw i
  · simp

lemma mean_residual_coordinate (w : T → Bool → ℝ) (hw : ∀ t, ∑ b,w t b=1)
    (M : T → Prop) [DecidablePred M] (base : T → Bool) (t : T) (F : Bool → ℝ) :
    (∑ c : T → Bool,productWeight w c * F (if M t then base t else c t)) =
      if M t then F (base t) else ∑ b,w t b * F b := by
  by_cases ht : M t
  · simp only [ite_eq_left ht,←Finset.sum_mul,productWeight_sum w hw,one_mul]
  · simp only [ite_eq_right ht]
    exact productWeight_coordinate w hw t F

end Heisenberg.Exposure

namespace Heisenberg.Exposure
open Heisenberg.Serial Heisenberg.MeshPair
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma residualBetween_mean {n : ℕ} (p : Fin n → ℝ) (M : Fin n → Prop)
    (base : Fin n → Bool) (D E : Set V) (a b : V) (t : Fin n) (x y : V) :
    (∑ c : Fin n → Bool,productWeight (fun i z => if z then p i else 1-p i) c *
      killedBetween D E (if residualCoins M base c t then Equiv.swap a b else 1) x y) =
      residualBetween D E (M t) (base t) a b (p t) x y := by
  have h := mean_residual_coordinate (fun i z => if z then p i else 1-p i)
    (by intro i; simp) M base t
    (fun z => killedBetween D E (if z then Equiv.swap a b else 1) x y)
  change (∑ c,productWeight _ c *
    (fun z => killedBetween D E (if z then Equiv.swap a b else 1) x y)
      (if M t then base t else c t)) = _
  have hu : @Finset.univ (Fin n → Bool)
    (@Pi.instFintype (Fin n) (fun _ => Bool) (fun a b => Classical.propDecidable (a=b))
      (Fin.fintype n) (fun _ => Bool.fintype)) = (Finset.univ : Finset (Fin n → Bool)) := by
    ext c
    simp
  rw [hu] at h
  refine h.trans ?_
  by_cases ht : M t
  · simp only [residualBetween,ite_eq_left ht]
  · simp [ht,residualBetween,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_comm]

omit [Fintype V] in

theorem killed_residual_cyclic (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (M : Fin (n+1) → Prop) (base : Fin (n+1) → Bool) (D : Fin (n+1) → Set V) :
    killedMean (productWeight (fun i z => if z then p i else 1-p i))
      (fun c => layerHistory (finRotate (n+1)) (fun i => Equiv.swap (a i) (b i))
        (residualCoins M base c)) {z | z.2∈D z.1} =
      cyclicKernel n (fun i => residualBetween (D i) (D (finRotate (n+1) i))
        (M i) (base i) (a i) (b i) (p i)) := by
  ext ⟨u,x⟩ ⟨t,y⟩
  simp only [killedMean,Set.mem_ofPred_eq,layerHistory,LayeredExchange.wiring_apply,Prod.mk.injEq,cyclicKernel]
  by_cases hu : u=finRotate (n+1) t
  · subst u
    simp only [true_and,ite_true]
    symm
    refine (residualBetween_mean p M base (D t) (D (finRotate (n+1) t)) (a t) (b t) t x y).symm.trans ?_
    by_cases hD : x∈D (finRotate (n+1) t) ∧ y∈D t
    · simp only [ite_eq_left hD]
      apply Finset.sum_congr rfl
      intro c _
      simp only [killedBetween,hD.1,hD.2,true_and]
    · simp only [ite_eq_right hD]
      apply Finset.sum_eq_zero
      intro c _
      have hn : ¬(y∈D t ∧ x∈D (finRotate (n+1) t) ∧ x=(if residualCoins M base c t then Equiv.swap (a t) (b t) else 1) y) :=
        fun h => hD ⟨h.2.1,h.1⟩
      simp only [killedBetween,ite_eq_right hn,mul_zero]
  · simp only [hu,false_and,ite_false,mul_zero,Finset.sum_const_zero,ite_self]

end Heisenberg.Exposure
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CutContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Filter Topology
open scoped RealInnerProductSpace Classical

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Hitting
variable {V : Type*} [Fintype V]
lemma hitting_zero_column {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) {i : V} (hi : i ∉ T) (hz : ∀ j, U j i = 0) :
    hitting U T i = 0 := by
  rw [←hitting_harmonic hU T hi]
  simp [backward,hz]
end Heisenberg.Hitting

namespace Heisenberg.Exposure
open Heisenberg.Serial Heisenberg.Hitting Heisenberg.MeshPair Heisenberg.Cycle
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma cutFactors_substochastic (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (P : Set (Fin (n+1)×V))
    (D : (Fin (n+1) → Bool) → Fin (n+1) → Set V) (base : Fin (n+1) → Bool) :
    ∀ i, Heisenberg.Hitting.DoublySubstochastic (cutFactors n a b p P D base i) := by
  intro i
  have h := residualBetween_substochastic (D base i) (D base (finRotate (n+1) i))
    (layerRevealed (fun j => Equiv.swap (a j) (b j))
      (MissingSet (layerHistory (finRotate (n+1)) (fun j => Equiv.swap (a j) (b j)) base) P) i)
    (base i) (a i) (b i) (p i) (hp i).1 (hp i).2
  exact ⟨h.nonneg,h.row,h.col⟩

end Heisenberg.Exposure

end
end

noncomputable section
open scoped Classical Fin.NatCast
namespace Heisenberg.Schedule
variable {m Q : ℕ} [NeZero m]

lemma run_succ (t : Fin m) (j : ℕ) : run t (j+1)=finRotate m (run t j) := by
  simp [run,Nat.cast_add,add_assoc]
lemma run_inj (t : Fin m) {n : ℕ} (hn : n ≤ m) : Set.InjOn (run t) (Set.Iio n) := by
  intro i hi j hj h
  have he : (↑i:Fin m)=(↑j:Fin m) := add_left_cancel h
  have hh := congrArg Fin.val he
  simpa only [Fin.val_natCast,Nat.mod_eq_of_lt (lt_of_lt_of_le hi hn),
    Nat.mod_eq_of_lt (lt_of_lt_of_le hj hn)] using hh

omit [NeZero m] in
lemma warm_le (t : Fin m) : warm t Q≤Q := Nat.sub_le ..

end Heisenberg.Schedule
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ScheduledResiduals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Fin.NatCast

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.Serial
open Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks
variable {V T X E : Type} [Fintype V] [DecidableEq V] [Fintype T]
  [PseudoMetricSpace X] [Fintype E]

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma product_snoc (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ) :
    product (n+1) K=K (Fin.last n)*product n (fun i=>K i.castSucc) := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [product,ih,product,Matrix.mul_assoc]
    rfl

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma prefix_product (K : ℕ → Matrix V V ℝ) (n : ℕ) :
    prefixMatrix K n=product n (fun i=>K i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixMatrix,product_snoc]
    simpa only [Fin.val_last,Fin.val_castSucc] using congrArg (K n * ·) ih

end Heisenberg.Serial

end
end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ReversedExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Cycle
open Equiv
variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma missingSet_inv (π : Perm V) (P : Set V) : MissingSet π⁻¹ P=MissingSet π P := by
  ext i
  simp only [MissingSet,Set.mem_ofPred_eq,ne_eq,classOf_eq_iff,Perm.sameCycle_inv]

omit [Fintype V] in
lemma colorSpace_inv (π : Perm V) (P : Set V) : colorSpace π⁻¹ P=colorSpace π P := by
  ext f
  simp only [colorSpace_mem]
  constructor
  · rintro ⟨h,hP⟩
    exact ⟨fun i=>(by simpa using (h (π i)).symm),hP⟩
  · rintro ⟨h,hP⟩
    exact ⟨fun i=>(by simpa using (h (π⁻¹ i)).symm),hP⟩

lemma missingCount_inv (π : Perm V) (P : Set V) : missingCount π⁻¹ P=missingCount π P := by
  have h : 2^missingCount π⁻¹ P=2^missingCount π P := by
    rw [←card_colorSpace,←card_colorSpace,colorSpace_inv]
  exact (Nat.pow_right_injective (by decide : 1<2)) h
end Heisenberg.Cycle

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.Bernoulli Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] [Fintype V] in
lemma layerHistory_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool) :
    layerHistory s.symm (fun j=>Equiv.swap (a (s.symm j)) (b (s.symm j))) (base ∘ s.symm)=
      (layerHistory s (fun j=>Equiv.swap (a j) (b j)) base)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  apply Equiv.ext
  rintro ⟨t,v⟩
  simp only [Equiv.Perm.mul_apply,layerHistory,wiring_apply,Function.comp_apply,
    Equiv.symm_apply_apply,Equiv.Perm.one_apply]
  cases base t <;> simp

omit [Fintype T] [Fintype V] in
lemma holeCut_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (t : T) :
    holeCut s.symm (fun j=>Equiv.swap (a (s.symm j)) (b (s.symm j))) (base ∘ s.symm) P t=
      holeCut s (fun j=>Equiv.swap (a j) (b j)) base P t := by
  simp only [holeCut,layerHistory_reverse,missingSet_inv]

omit [DecidableEq V] in
lemma layerWeight_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) :
    layerWeight s.symm (a ∘ s.symm) (b ∘ s.symm) P (base ∘ s.symm)=layerWeight s a b P base := by
  simp only [layerWeight,Function.comp_apply,layerHistory_reverse,missingCount_inv]

omit [Fintype V] [DecidableEq V] in
lemma coin_reverse (s : Equiv.Perm T) (p : T → ℝ) (base : T → Bool) :
    weight (p ∘ s.symm) (base ∘ s.symm)=weight p base := by
  unfold weight
  exact s.symm.prod_comp (fun i=>if base i then p i else 1-p i)

omit [DecidableEq V] in
lemma layerPartition_reverse (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V)) (p : T → ℝ) :
    layerPartition s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm)=layerPartition s a b P p := by
  unfold layerPartition
  let e : (T → Bool) ≃ (T → Bool) := Equiv.arrowCongr s (Equiv.refl Bool)
  conv_lhs => rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  change weight (p ∘ s.symm) (c ∘ s.symm)*layerWeight s.symm (a ∘ s.symm) (b ∘ s.symm) P (c ∘ s.symm)=_
  rw [coin_reverse,layerWeight_reverse]

omit [DecidableEq V] in
lemma layerMass_reverse (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V)) (p : T → ℝ)
    (base : T → Bool) :
    layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) (base ∘ s.symm)=layerMass s a b P p base := by
  rw [layerMass,layerMass,coin_reverse,layerWeight_reverse,layerPartition_reverse]

omit [Fintype T] [Fintype V] in
lemma revealed_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (t : T) :
    layerRevealed (fun j=>Equiv.swap (a (s.symm j)) (b (s.symm j)))
      (MissingSet (layerHistory s.symm (fun j=>Equiv.swap (a (s.symm j)) (b (s.symm j))) (base ∘ s.symm)) P) t ↔
    layerRevealed (fun j=>Equiv.swap (a j) (b j))
      (MissingSet (layerHistory s (fun j=>Equiv.swap (a j) (b j)) base) P) (s.symm t) := by
  rw [layerHistory_reverse,missingSet_inv]
  by_cases hab : a (s.symm t)=b (s.symm t)
  · simp [layerRevealed,hab]
  rw [layerRevealed_swap (fun j=>a (s.symm j)) (fun j=>b (s.symm j)) _ t hab,
    layerRevealed_swap a b _ (s.symm t) hab]
  have h₁ := missing_apply (layerHistory s (fun j=>Equiv.swap (a j) (b j)) base) P (s.symm t,a (s.symm t))
  have h₂ := missing_apply (layerHistory s (fun j=>Equiv.swap (a j) (b j)) base) P (s.symm t,b (s.symm t))
  simp only [layerHistory,wiring_apply,Equiv.apply_symm_apply] at h₁ h₂
  cases h : base (s.symm t) <;> simp [h] at h₁ h₂
  · exact or_congr h₁ h₂
  · exact (or_congr h₂ h₁).trans or_comm

omit [Fintype T] [Fintype V] in
lemma exposedStep_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (t : T) :
    exposedStep s.symm (a ∘ s.symm) (b ∘ s.symm) (base ∘ s.symm) P I (p ∘ s.symm) t=
      (exposedStep s a b base P I p (s.symm t)).transpose := by
  simp only [exposedStep,Function.comp_apply,holeCut_reverse]
  rw [revealed_reverse,residualBetween_transpose]
  simp

end Heisenberg.Exposure
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PeriodicLeakage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
lemma swap_classical {α : Type*} [h : DecidableEq α] (a b : α) :
    Equiv.swap a b = @Equiv.swap α (Classical.decEq α) a b := by
  have he : h=Classical.decEq α := Subsingleton.elim _ _
  cases he
  rfl

end

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Matrix
namespace Heisenberg.Schedule
variable {m : ℕ} [NeZero m]
lemma run_ne_start (t : Fin m) {j : ℕ} (hj : 0 < j) (hjm : j < m) : run t j≠t := by
  intro h
  have hh:=run_inj t (le_refl m) hjm (NeZero.pos m) (h.trans (run_zero t).symm)
  omega
end Heisenberg.Schedule
namespace Heisenberg.Serial
open Heisenberg.Schedule Heisenberg.Hitting
variable {V : Type} [Fintype V] [DecidableEq V]

lemma cyclic_backward_return_at (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (t : Fin (n+1)) (f : Fin (n+1) → V → ℝ)
    (hf : ∀ u,u≠t → (K u).transpose*ᵥ f (finRotate (n+1) u)=f u) :
    (product (n+1) (fun i=>K (run t i))).transpose*ᵥ f t=
      (K t).transpose*ᵥ f (finRotate (n+1) t) := by
  have hh := backward_profile n (fun i=>K (run t (i.val+1)))
    (fun i=>f (run t (i.val+1))) (by
      intro i
      simpa only [Fin.val_castSucc,Fin.val_succ,run_succ] using
        hf (run t (i.val+1)) (run_ne_start t (by omega) (by omega)))
  simp only [Fin.val_last,run_period,Fin.val_zero,Nat.zero_add,run_succ,run_zero] at hh
  rw [product,Matrix.transpose_mul,←Matrix.mulVec_mulVec]
  simp only [Fin.val_zero,run_zero,Fin.val_succ]
  change (K t).transpose*ᵥ ((product n (fun i=>K (run t (i.val+1)))).transpose*ᵥ f t)=_
  simp only [run_succ]
  rw [hh]

theorem cyclic_hitting_energy_at (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (hK : ∀ t,DoublySubstochastic (K t)) (t : Fin (n+1)) (J : Finset V) :
    let F := hitting (cyclicKernel n K) (targetsAt n t J)
    energy (cyclicKernel n K) F =
      energy (product (n+1) (fun i=>K (run t i))) (fun v=>F (t,v)) := by
  dsimp only
  let U:=cyclicKernel n K
  let F:=hitting U (targetsAt n t J)
  have hU:=cyclicKernel_substochastic n K hK
  have hf (u : Fin (n+1)) (hu : u≠t) :
      (K u).transpose*ᵥ (fun v=>F (finRotate (n+1) u,v))=(fun v=>F (u,v)) := by
    funext v
    rw [←cyclicKernel_backward]
    exact hitting_harmonic hU _ (by simp [hu])
  have hr:=cyclic_backward_return_at n K t (fun u v=>F (u,v)) hf
  have hr' (v : V) : backward (product (n+1) (fun i=>K (run t i))) (fun v=>F (t,v)) v=
      backward U F (t,v) := by
    rw [cyclicKernel_backward]
    exact congrFun hr v
  rw [energy_transpose]
  change (∑ z,F z*(F z-backward U F z))=energy _ _
  rw [Fintype.sum_prod_type,Finset.sum_eq_single t]
  · rw [energy_transpose]
    apply Finset.sum_congr rfl
    intro v _
    rw [hr']
  · intro u _ hu
    apply Finset.sum_eq_zero
    intro v _
    have hh:=hitting_harmonic hU (targetsAt n t J) (i:=(u,v)) (by simp [hu])
    change backward U F (u,v)=F (u,v) at hh
    rw [hh,sub_self,mul_zero]
  · simp

end Heisenberg.Serial

namespace Heisenberg.Exposure
open Heisenberg.Serial Heisenberg.Schedule Heisenberg.Hitting Heisenberg.MeshPair Heisenberg.Cycle
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cut_return_energy_at (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (P : Set (Fin (n+1)×V))
    (D : (Fin (n+1) → Bool) → Fin (n+1) → Set V) (t : Fin (n+1))
    (T : Finset P) (J : Finset V) (himage : T.image Subtype.val=targetsAt n t J)
    (hT : ∀ base j,j∈T → j.val.2∈D base j.val.1)
    (hQ : ∀ base,(MissingSet (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) base) P)ᶜ∩Pᶜ ⊆
      {z | z.2∈D base z.1}) :
    ∃ f : (Fin (n+1) → Bool) → V → ℝ,
      (∀ base j,0 ≤ f base j ∧ f base j ≤ 1) ∧
      (∀ base j,j∈J → f base j=1) ∧
      (∀ base j,j∉D base t → f base j=0) ∧
      (∑ c,layerMass (finRotate (n+1)) a b P p c *
        returnCount (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) c) P T) ≤ (J.card:ℝ)-
      ∑ base,layerMass (finRotate (n+1)) a b P p base *
        energy (product (n+1) (fun i=>cutFactors n a b p P D base (run t i))) (f base) := by
  let K:=cutFactors n a b p P D
  let F:=fun base=>hitting (cyclicKernel n (K base)) (targetsAt n t J)
  have hK:=cutFactors_substochastic n a b p hp P D
  have hU:=fun base=>cyclicKernel_substochastic n (K base) (hK base)
  have hTb (base : Fin (n+1) → Bool) {j : V} (hj : j∈J) : j∈D base t := by
    have ht : (t,j)∈T.image Subtype.val := by rw [himage]; simp [hj]
    obtain ⟨z,hz,he⟩:=Finset.mem_image.mp ht
    have hh:=hT base z hz
    simpa only [he] using hh
  refine ⟨fun base j=>F base (t,j),?_,?_,?_,?_⟩
  · intro base j
    exact ⟨(hitting_bounds (hU base) _).1 _,(hitting_bounds (hU base) _).2 _⟩
  · intro base j hj
    exact hitting_on (hU base) _ (by simp [hj])
  · intro base j hj
    apply hitting_zero_column (hU base) (targetsAt n t J)
    · simp only [mem_targetsAt,true_and]
      exact fun ht=>hj (hTb base ht)
    · intro z
      simp only [cyclicKernel]
      split_ifs
      · dsimp [K,cutFactors]
        simp only [residualBetween]
        split_ifs <;>  simp [killedBetween,hj,Matrix.add_apply,Matrix.smul_apply]
      · rfl
  · have hh:=averaged_layer_energy (finRotate (n+1)) a b p hp P
      (fun base=>{z | z.2∈D base z.1}) T hT hQ
    dsimp only at hh
    have hc : T.card=J.card := by
      have h:=congrArg Finset.card himage
      rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
      simpa [targetsAt,Finset.card_image_of_injective _ (fun _ _ h=>(Prod.mk.inj h).2)] using h
    rw [hc] at hh
    have hweight : ∀ base,layerMass (finRotate (n+1)) a b P p base=
        (productWeight (fun i z=>if z then p i else 1-p i) base *
          (2:ℝ)^missingCount (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) base) P)/
        (∑ c,productWeight (fun i z=>if z then p i else 1-p i) c *
          (2:ℝ)^missingCount (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) c) P) := by
      intro base
      simp only [layerMass,layerPartition,layerWeight,Heisenberg.Bernoulli.weight,productWeight,swap_classical]
      congr 1
      apply Finset.sum_congr
      · ext c; simp
      · intro c _; rfl
    simp only [hweight]
    convert hh using 2
    congr 1
    ext base
    congr 1
    rw [killed_residual_cyclic,himage]
    exact (cyclic_hitting_energy_at n (K base) (hK base) t J).symm

end Heisenberg.Exposure
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PolynomialLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical Fin.NatCast
namespace Heisenberg.Schedule
variable {m Q q : ℕ} [NeZero m] [NeZero Q]

lemma phaseHom_sub (h : Q∣m) (a b : Fin m) :
    ((a-b).val%Q)=((phaseHom h a-phaseHom h b).val) := by
  have hh:=congrArg Fin.val ((phaseHom h).map_sub a b)
  exact hh

lemma reverseIndex_next (j : Fin m) :
    (finRotate m).symm (reverseIndex q j)=reverseIndex q (finRotate m j) := by
  apply (finRotate m).injective
  simp only [Equiv.apply_symm_apply,finRotate_apply,reverseIndex,Equiv.coe_fn_mk]
  simp only [sub_add_eq_sub_sub,sub_add_cancel]

lemma reverseIndex_prev (hq : 0 < q) (j : Fin m) :
    (finRotate m).symm (reverseIndex q j)=((q-1:ℕ):Fin m)-j := by
  apply (finRotate m).injective
  simp only [Equiv.apply_symm_apply,finRotate_apply,reverseIndex,Equiv.coe_fn_mk]
  have h : ((q-1:ℕ):Fin m)+1=(q:Fin m) := by
    calc
      _ = ((q-1+1:ℕ):Fin m) := by simp only [Nat.cast_add,Nat.cast_one]
      _ = (q:Fin m) := by rw [Nat.sub_add_cancel hq]
  rw [sub_add_eq_add_sub,h]

lemma reverse_phase_spatial (hdiv : Q∣m) (hq : 0 < q) (hqQ : q ≤ Q)
    (j : Fin m) (hj : j.val%Q < q) :
    ((finRotate m).symm (reverseIndex q j)).val%Q=q-1-j.val%Q := by
  rw [reverseIndex_prev hq,phaseHom_sub hdiv]
  have hQm : Q ≤ m := Nat.le_of_dvd (NeZero.pos m) hdiv
  have hqm : q-1 < m := by omega
  have hqQ' : q-1 < Q := by omega
  have ha : phaseHom hdiv ((q-1:ℕ):Fin m)=((q-1:ℕ):Fin Q) := by
    simp [phaseHom,Fin.val_natCast,Nat.mod_eq_of_lt hqm]
  rw [ha,Fin.sub_val_of_le]
  · simp only [Fin.val_natCast,Nat.mod_eq_of_lt hqQ',phaseHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  · change j.val%Q ≤ (q-1)%Q
    rw [Nat.mod_eq_of_lt hqQ']
    omega

lemma reverse_phase_completion (hdiv : Q∣m) (hq : 0 < q) (hqQ : q ≤ Q)
    (j : Fin m) (hj : q ≤ j.val%Q) :
    q ≤ ((finRotate m).symm (reverseIndex q j)).val%Q := by
  rw [reverseIndex_prev hq,phaseHom_sub hdiv]
  have hQm : Q ≤ m := Nat.le_of_dvd (NeZero.pos m) hdiv
  have hqm : q-1 < m := by omega
  have hqQ' : q-1 < Q := by omega
  have ha : phaseHom hdiv ((q-1:ℕ):Fin m)=((q-1:ℕ):Fin Q) := by
    simp [phaseHom,Fin.val_natCast,Nat.mod_eq_of_lt hqm]
  rw [ha]
  have hh:=Fin.intCast_val_sub_eq_sub_add_ite ((q-1:ℕ):Fin Q) (phaseHom hdiv j)
  have hn : ¬phaseHom hdiv j ≤ ((q-1:ℕ):Fin Q) := by
    change ¬j.val%Q ≤ (q-1)%Q
    rw [Nat.mod_eq_of_lt hqQ']
    omega
  rw [ite_eq_right hn] at hh
  simp only [Fin.val_natCast,Nat.mod_eq_of_lt hqQ',phaseHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk] at hh
  change q ≤ (((q-1:ℕ):Fin Q)-(j.val:Fin Q)).val
  have hmod:=Nat.mod_lt j.val (NeZero.pos Q)
  omega

end Heisenberg.Schedule

end

noncomputable section
open scoped Classical BigOperators
open Matrix
namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma prefix_cons (K : ℕ → Matrix V V ℝ) (n : ℕ) :
    prefixMatrix K (n+1)=prefixMatrix (fun j=>K (j+1)) n*K 0 := by
  induction n with
  | zero => simp [prefixMatrix]
  | succ n ih =>
    rw [prefixMatrix,ih,prefixMatrix,Matrix.mul_assoc]

lemma prefix_congr (K L : ℕ → Matrix V V ℝ) (n : ℕ)
    (h : ∀ j,j < n → K j=L j) : prefixMatrix K n=prefixMatrix L n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prefixMatrix,prefixMatrix,h n (by omega),ih (fun j hj=>h j (by omega))]

lemma prefix_reverse (K : ℕ → Matrix V V ℝ) (n a : ℕ) :
    (prefixMatrix (fun j=>(K (a+n-1-j)).transpose) n).transpose=
      prefixMatrix (fun j=>K (a+j)) n := by
  induction n with
  | zero => simp [prefixMatrix]
  | succ n ih =>
    rw [prefix_cons,Matrix.transpose_mul,Matrix.transpose_transpose]
    have he : prefixMatrix (fun j=>(K (a+(n+1)-1-(j+1))).transpose) n=
        prefixMatrix (fun j=>(K (a+n-1-j)).transpose) n := by
      apply prefix_congr
      intro j hj
      congr 2
      omega
    rw [he,ih,prefixMatrix]
    congr 1

omit [DecidableEq V] in
lemma squareNorm_toLp (f : EuclideanSpace ℝ V) : squareNorm f.ofLp=‖f‖^2 := by
  simpa only [squareNorm,Real.norm_eq_abs,sq_abs] using (EuclideanSpace.norm_sq_eq f).symm

lemma energy_two_prefixes (K : ℕ → Matrix V V ℝ) (N u v : ℕ) (huv : u+v ≤ N)
    (hK : ∀ j,j < N → DoublySubstochastic (K j)) (f : EuclideanSpace ℝ V) :
    ((‖f‖^2-‖euclideanMap (prefixMatrix K u) f‖^2)+
      (‖f‖^2-‖euclideanMap (prefixMatrix (fun j=>(K (N-1-j)).transpose) v) f‖^2))/2 ≤
      Heisenberg.Hitting.energy (prefixMatrix K N) f.ofLp := by
  let A:=prefixMatrix K u
  let M:=prefixMatrix (fun j=>K (u+j)) (N-v-u)
  let B:=prefixMatrix (fun j=>K (N-v+j)) v
  have hM : DoublySubstochastic M := prefix_substochastic _ _ (fun j hj=>hK _ (by omega))
  have he : prefixMatrix K N=B*M*A := by
    have hN : N=(u+(N-v-u))+v := by omega
    conv_lhs => rw [hN,prefix_add,prefix_add]
    change prefixMatrix (fun j=>K (u+(N-v-u)+j)) v*(M*A)=B*M*A
    have hu : u+(N-v-u)=N-v := by omega
    rw [hu,Matrix.mul_assoc]
  have hB : B.transpose=prefixMatrix (fun j=>(K (N-1-j)).transpose) v := by
    have hh:=prefix_reverse K v (N-v)
    have hNv : N-v+v=N := by omega
    rw [hNv] at hh
    exact (congrArg Matrix.transpose hh).symm.trans (Matrix.transpose_transpose _)
  have hh:=two_ends A M B hM f.ofLp
  rw [←he,hB] at hh
  change (_+_)/2 ≤ _ at hh
  have heE : Heisenberg.Hitting.energy (prefixMatrix K N) f.ofLp=
      squareNorm f.ofLp-dot f.ofLp ((prefixMatrix K N)*ᵥ f.ofLp) := by
    simp [Heisenberg.Hitting.energy,squareNorm,dot,Matrix.mulVec,dotProduct,mul_sub,
      Finset.sum_sub_distrib,Finset.mul_sum,pow_two]
  rw [heE]
  convert hh using 1
  simp only [←squareNorm_toLp,A]
  rfl

end Heisenberg.MeshPair

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Matrix
namespace Heisenberg.Schedule
variable {m : ℕ} [NeZero m]

lemma reverse_run (q : ℕ) (t : Fin m) (j : ℕ) :
    reverseIndex q (run (reverseIndex q t) j)=t-(j:Fin m) := by
  simp only [reverseIndex,Equiv.coe_fn_mk,run]
  rw [sub_add_eq_sub_sub,sub_sub_cancel]

lemma reverse_predecessor (q : ℕ) (t : Fin m) (j : ℕ) (hj : j < m) :
    (finRotate m).symm (reverseIndex q (run (reverseIndex q t) j))=run t (m-1-j) := by
  rw [reverse_run,finRotate_symm_apply]
  have he : (m-1-j)+j+1=m := by omega
  have hh : ((m-1-j:ℕ):Fin m)+(j:Fin m)+1=0 := by
    calc
      _ = ((m-1-j+j+1:ℕ):Fin m) := by simp only [Nat.cast_add,Nat.cast_one]
      _ = 0 := by rw [he]; simp
  apply add_right_cancel (b:=(j:Fin m)+1)
  change (t-(j:Fin m)-1)+((j:Fin m)+1)=(t+((m-1-j:ℕ):Fin m))+((j:Fin m)+1)
  rw [←sub_add_eq_sub_sub,sub_add_cancel,add_assoc,←add_assoc _ (j:Fin m),hh,add_zero]

end Heisenberg.Schedule

namespace Heisenberg.Exposure
open Heisenberg.Schedule Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma layerSum_reverse (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V)) (p : T → ℝ)
    (F : (T → Bool) → ℝ) :
    (∑ c,layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) c*F (c ∘ s))=
      ∑ c,layerMass s a b P p c*F c := by
  let e : (T → Bool) ≃ (T → Bool) := Equiv.arrowCongr s (Equiv.refl Bool)
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  change layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) (c ∘ s.symm)*F ((c ∘ s.symm) ∘ s)=_
  rw [layerMass_reverse]
  congr 2
  funext i
  simp

omit [Fintype T] in
lemma reversed_period_sweep {m : ℕ} [NeZero m] (q : ℕ)
    (a b : Fin m → V) (P : Set (Fin m×V)) (p : Fin m → ℝ)
    (base : Fin m → Bool) (I : Set V) (t : Fin m) (v : ℕ) (hv : v ≤ m)
    (f : EuclideanSpace ℝ V) :
    exposedSweep (finRotate m).symm (a ∘ (finRotate m).symm) (b ∘ (finRotate m).symm)
      (base ∘ (finRotate m).symm) P I (p ∘ (finRotate m).symm)
      (fun j=>reverseIndex q (run (reverseIndex q t) j)) v f=
    euclideanMap (prefixMatrix
      (fun j=>(exposedStep (finRotate m) a b base P I p (run t (m-1-j))).transpose) v) f := by
  rw [exposedSweep_prefix]
  apply congrArg (fun K=>euclideanMap K f)
  apply prefix_congr
  intro j hj
  rw [exposedStep_reverse,reverse_predecessor q t j (lt_of_lt_of_le hj hv)]

end Heisenberg.Exposure

end
end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_TwoEndedReturns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace Heisenberg.Clocks

lemma factorial_lower_of_pos (R : ℕ) (hR : 1 ≤ R) :
    ((R:ℝ)/Real.exp 1)^R ≤ (R.factorial:ℝ) := by
  have hr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hs : (1:ℝ) ≤ Real.sqrt (2*Real.pi*R) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ Real.sqrt (2*Real.pi*R)*((R:ℝ)/Real.exp 1)^R :=
      le_mul_of_one_le_left (by positivity) hs
    _ ≤ _ := Stirling.le_factorial_stirling R

lemma geometric_le_recip (R : ℕ) : (1/2:ℝ)^R ≤ 1/(1+(R:ℝ)) := by
  have h : (1:ℝ)+R ≤ 2^R := by
    have := one_add_mul_le_pow (by norm_num : (-2:ℝ) ≤ 1) R
    norm_num at this ⊢
    linarith
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) h

theorem binomial_clock_tail (n R : ℕ) (B δ s : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hs : 0 ≤ s) (hR : 1 ≤ R)
    (hsmall : ((n+2+R:ℕ):ℝ)*δ ≤ 2*s)
    (hlarge : 8*B*Real.exp 1*s ≤ R) :
    ((n+2+R).choose R:ℝ)*(2*B*δ)^R ≤ 1/(1+(R:ℝ)) := by
  have hfact : 0 < (R.factorial:ℝ) := by positivity
  have hr : 0 < (R:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hR)
  calc
    _ ≤ (((n+2+R:ℕ):ℝ)^R/(R.factorial:ℝ))*(2*B*δ)^R :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div R (n+2+R)) (by positivity)
    _ = (((n+2+R:ℕ):ℝ)*(2*B*δ))^R/(R.factorial:ℝ) := by rw [mul_pow]; ring
    _ ≤ (4*B*s)^R/(R.factorial:ℝ) := by
      apply div_le_div_of_nonneg_right _ hfact.le
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    _ ≤ (4*B*s)^R/(((R:ℝ)/Real.exp 1)^R) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_lower_of_pos R hR)
    _ = (4*B*s/((R:ℝ)/Real.exp 1))^R := (div_pow ..).symm
    _ ≤ (1/2:ℝ)^R := by
      apply pow_le_pow_left₀ (by positivity)
      apply (div_le_iff₀ (by positivity : 0 < (R:ℝ)/Real.exp 1)).mpr
      rw [←mul_div_assoc]
      apply (le_div_iff₀ (Real.exp_pos 1)).mpr
      nlinarith
    _ ≤ _ := geometric_le_recip R

end Heisenberg.Clocks

end

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Matrix
namespace Heisenberg.Exposure
open Heisenberg.Serial Heisenberg.Schedule Heisenberg.Hitting Heisenberg.MeshPair Heisenberg.Cycle
variable {V : Type} [Fintype V] [DecidableEq V]

theorem period_return_two_ends (n q : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (P : Set (Fin (n+1)×V)) (I : Set V)
    (hP : ∀ z,z.2∉I → z∈P) (t : Fin (n+1)) (T : Finset P) (J : Finset V)
    (himage : T.image Subtype.val=targetsAt n t J) (hJ : ∀ j∈J,j∈I)
    (u v : ℕ) (huv : u+v ≤ n+1) (rF rB : ℝ)
    (hF : ∀ f : ((Fin (n+1) → Bool) → EuclideanSpace ℝ V),
      (∀ c j,0 ≤ (f c).ofLp j ∧ (f c).ofLp j ≤ 1) →
      (∀ c j,j∈J → (f c).ofLp j=1) →
      (∀ c j,j∉holeCut (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) c P t∩I → (f c).ofLp j=0) →
      rF ≤ ∑ c,layerMass (finRotate (n+1)) a b P p c *
        (‖f c‖^2-‖exposedSweep (finRotate (n+1)) a b c P I p (run t) u (f c)‖^2))
    (hB : ∀ f : ((Fin (n+1) → Bool) → EuclideanSpace ℝ V),
      (∀ c j,0 ≤ (f c).ofLp j ∧ (f c).ofLp j ≤ 1) →
      (∀ c j,j∈J → (f c).ofLp j=1) →
      (∀ c j,j∉holeCut (finRotate (n+1)).symm
        (fun i=>Equiv.swap (a ((finRotate (n+1)).symm i)) (b ((finRotate (n+1)).symm i))) c P t∩I → (f c).ofLp j=0) →
      rB ≤ ∑ c,layerMass (finRotate (n+1)).symm (a ∘ (finRotate (n+1)).symm)
        (b ∘ (finRotate (n+1)).symm) P (p ∘ (finRotate (n+1)).symm) c *
        (‖f c‖^2-‖exposedSweep (finRotate (n+1)).symm (a ∘ (finRotate (n+1)).symm)
          (b ∘ (finRotate (n+1)).symm) c P I (p ∘ (finRotate (n+1)).symm)
          (fun j=>reverseIndex q (run (reverseIndex q t) j)) v (f c)‖^2)) :
    (∑ c,layerMass (finRotate (n+1)) a b P p c *
      returnCount (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) c) P T) ≤
        (J.card:ℝ)-(rF+rB)/2 := by
  let s:=finRotate (n+1)
  let D:=fun c i=>holeCut s (fun j=>Equiv.swap (a j) (b j)) c P i∩I
  have hT : ∀ base j,j∈T → j.val.2∈D base j.val.1 := by
    intro c j hj
    have ht : j.val∈targetsAt n t J := himage ▸ Finset.mem_image.mpr ⟨j,hj,rfl⟩
    have hh:=(mem_targetsAt ..).mp ht
    refine ⟨?_,hJ _ hh.2⟩
    exact fun h=>Set.disjoint_left.mp (missing_disjoint_pins _ P) h j.property
  have hQ : ∀ base,(MissingSet (layerHistory s (fun i=>Equiv.swap (a i) (b i)) base) P)ᶜ∩Pᶜ ⊆
      {z | z.2∈D base z.1} := by
    intro c z hz
    exact ⟨hz.1,by by_contra h; exact hz.2 (hP z h)⟩
  obtain ⟨A,hA,hAJ,hAs,hret⟩:=cut_return_energy_at n a b p hp P D t T J himage hT hQ
  let f:=fun c=>WithLp.toLp 2 (A c)
  have hf : ∀ c j,0 ≤ (f c).ofLp j ∧ (f c).ofLp j ≤ 1 := hA
  have hfJ : ∀ c j,j∈J → (f c).ofLp j=1 := hAJ
  have hfs : ∀ c j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) c P t∩I → (f c).ofLp j=0 := hAs
  have hF' := hF f hf hfJ hfs
  have hB' := hB (fun c=>f (c ∘ s)) (fun c j=>hf _ _) (fun c j hj=>hfJ _ _ hj) (by
    intro c j hj
    apply hfs
    have he := holeCut_reverse s a b (c ∘ s) P t
    have hc : (c ∘ s) ∘ s.symm=c := by funext i; simp
    rw [hc] at he
    exact fun h=>hj (by rw [he]; exact h))
  have hbmean : (∑ c,layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) c *
      (‖f (c ∘ s)‖^2-‖exposedSweep s.symm (a ∘ s.symm) (b ∘ s.symm) c P I (p ∘ s.symm)
        (fun j=>reverseIndex q (run (reverseIndex q t) j)) v (f (c ∘ s))‖^2))=
      ∑ c,layerMass s a b P p c *
      (‖f c‖^2-‖euclideanMap (prefixMatrix
        (fun j=>(exposedStep s a b c P I p (run t (n+1-1-j))).transpose) v) (f c)‖^2) := by
    let e : ((Fin (n+1) → Bool)) ≃ ((Fin (n+1) → Bool)) := Equiv.arrowCongr s (Equiv.refl Bool)
    conv_lhs => rw [←e.sum_comp]
    apply Finset.sum_congr rfl
    intro c _
    change layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) (c ∘ s.symm) *
      (‖f ((c ∘ s.symm) ∘ s)‖^2-‖exposedSweep s.symm (a ∘ s.symm) (b ∘ s.symm) (c ∘ s.symm) P I (p ∘ s.symm)
        (fun j=>reverseIndex q (run (reverseIndex q t) j)) v (f ((c ∘ s.symm) ∘ s))‖^2)=_
    have hc : (c ∘ s.symm) ∘ s=c := by funext i; simp
    rw [hc,layerMass_reverse,reversed_period_sweep q a b P p c I t v (by omega)]
  rw [hbmean] at hB'
  have he : (rF+rB)/2 ≤ ∑ c,layerMass s a b P p c *
      energy (product (n+1) (fun i=>cutFactors n a b p P D c (run t i))) (A c) := by
    have hh : rF+rB ≤ (∑ c,layerMass s a b P p c *
      (‖f c‖^2-‖exposedSweep s a b c P I p (run t) u (f c)‖^2))+
      (∑ c,layerMass s a b P p c *(‖f c‖^2-‖euclideanMap (prefixMatrix
        (fun j=>(exposedStep s a b c P I p (run t (n+1-1-j))).transpose) v) (f c)‖^2)) := add_le_add hF' hB'
    apply (div_le_div_of_nonneg_right hh (by norm_num)).trans
    rw [←Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_le_sum
    intro c _
    rw [←mul_add,mul_div_assoc,exposedSweep_prefix]
    have hK : ∀ j,j < n+1 → Heisenberg.MatrixContraction.DoublySubstochastic (exposedStep s a b c P I p (run t j)) := by
      intro j _
      exact exposedStep_substochastic s a b c P I p hp _
    have ht:=energy_two_prefixes (fun j=>exposedStep s a b c P I p (run t j)) (n+1) u v huv hK (f c)
    apply mul_le_mul_of_nonneg_left _ (layerMass_nonneg s a b P p hp c)
    rw [prefix_product (fun j=>exposedStep s a b c P I p (run t j)) (n+1)] at ht
    exact ht
  linarith

end Heisenberg.Exposure

end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RegularPin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
attribute [-instance] instDecidableEqFin
namespace Heisenberg.Exposure
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.LatticeRegular Heisenberg.SparseWitness Heisenberg.Cycle

attribute [local irreducible] Pin.pinDensity LayeredExchange.layerWeight LayeredExchange.coinWiring cutAdmissible layerMass layerHistory MissingSet Return.HasHit localGrowth

attribute [local instance] OAI.regDecEq
lemma regularity_reverse {V : Type} [Fintype V] {m : ℕ} (s : Equiv.Perm (Fin m))
    (a b : Fin m → V) (P : Set (Fin m×V)) (rates : Fin m → ℝ)
    (F : Set V → Prop) (t : Fin m) :
    (∑ c,layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (rates ∘ s.symm) c *
      if F (holeCut s.symm (fun i=>Equiv.swap (a (s.symm i)) (b (s.symm i))) c P t) then (1:ℝ) else 0)=
    ∑ c,layerMass s a b P rates c *
      if F (holeCut s (fun i=>Equiv.swap (a i) (b i)) c P t) then (1:ℝ) else 0 := by
  have he : ∀ c,holeCut s.symm (fun i=>Equiv.swap (a (s.symm i)) (b (s.symm i))) c P t=
      holeCut s (fun i=>Equiv.swap (a i) (b i)) (c ∘ s) P t := by
    intro c
    have hh:=holeCut_reverse s a b (c ∘ s) P t
    have hc : (c ∘ s) ∘ s.symm=c := by funext i; simp
    rwa [hc] at hh
  simp_rw [he]
  exact layerSum_reverse s a b P rates (fun c=>if F (holeCut s (fun i=>Equiv.swap (a i) (b i)) c P t) then 1 else 0)

end Heisenberg.Exposure
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BootstrapMeshBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace Heisenberg.Bootstrap

lemma mesh_floor (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) (hδs : δ ≤ s/2) :
    0 < ⌊s/δ⌋₊ ∧ s/2 ≤ δ*(⌊s/δ⌋₊:ℝ) ∧ δ*(⌊s/δ⌋₊:ℝ) ≤ s := by
  have hsd : 0 ≤ s/δ := div_nonneg hs.le hδ.le
  have hfloor:=Nat.floor_le hsd
  have hceil:=Nat.lt_floor_add_one (s/δ)
  have hlow : s-δ < δ*(⌊s/δ⌋₊:ℝ) := by
    have hh:=(div_lt_iff₀ hδ).mp hceil
    nlinarith
  have hup : δ*(⌊s/δ⌋₊:ℝ) ≤ s := by
    have hh:=(le_div_iff₀ hδ).mp hfloor
    nlinarith
  refine ⟨?_,by linarith,hup⟩
  by_contra hn
  have he : ⌊s/δ⌋₊=0 := by omega
  rw [he,Nat.cast_zero,mul_zero] at hlow
  linarith

lemma round_clock_bound (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) (R : ℕ)
    (hδR : δ ≤ s/(R+2)) : ((⌊s/δ⌋₊+2+R:ℕ):ℝ)*δ ≤ 2*s := by
  have hh:=(le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hs.le hδ.le))
  have hR : (0:ℝ) < R+2 := by positivity
  have hsmall:=(le_div_iff₀ hR).mp hδR
  push_cast
  nlinarith

lemma mesh_remainder (p s δ ε : ℝ) (hp : 0 < p) (hs : 0 < s) (hδ : 0 < δ)
    (V q n k : ℕ) (hk : 1 ≤ k) (hn : (n:ℝ)*δ ≤ s)
    (heps : ε=p/(16*s*((V:ℝ)+1))) (hsmall : δ ≤ p/(16*s*((q:ℝ)^2+1))) :
    (n:ℝ)*(ε*δ*V+δ^2*q^2) ≤ p/4*k := by
  have hV : 0 < (V:ℝ)+1 := by positivity
  have hq : 0 < (q:ℝ)^2+1 := by positivity
  have h16 : 0 < 16*s := by positivity
  have hε : 0 < ε := heps ▸ div_pos hp (mul_pos h16 hV)
  have he : ε*(16*s*((V:ℝ)+1))=p := by rw [heps]; field_simp
  have hδq : δ*(16*s*((q:ℝ)^2+1)) ≤ p := (le_div_iff₀ (mul_pos h16 hq)).mp hsmall
  have hr1 : s*ε*V ≤ p/16 := by nlinarith [mul_nonneg hs.le hε.le]
  have hr2 : s*δ*q^2 ≤ p/16 := by nlinarith [mul_nonneg hs.le hδ.le]
  have h1:=mul_le_mul_of_nonneg_right hn (mul_nonneg hε.le (Nat.cast_nonneg V))
  have h2:=mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ δ*(q:ℝ)^2)
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

lemma leakage_arithmetic (p s δ F ρ tail : ℝ) (n R k : ℕ)
    (_hp : 0 < p) (hs : 0 < s) (_hδ : 0 < δ) (hF : 0 ≤ F)
    (ht : tail ≤ 1/(1+(R:ℝ))) (hn : s/2 ≤ δ*(n:ℝ))
    (herr : 2*(ρ+1/(1+(R:ℝ)))+8*F*(1+(R:ℝ))^((1:ℝ)/100)/s < p/4)
    (rem : ℝ) (hrem : rem ≤ p/4*k) :
    (1-p/2)*(k:ℝ) ≤ (k:ℝ)-2*((ρ+tail)*k)-
      2*(F*(1+(R:ℝ))^((1:ℝ)/100)*k)/((δ/2)*(n:ℝ))-rem := by
  have hnpos : 0 < δ*(n:ℝ) := lt_of_lt_of_le (by linarith) hn
  have hdpos : 0 < (δ/2)*(n:ℝ) := by nlinarith
  have hflow : 2*(F*(1+(R:ℝ))^((1:ℝ)/100)*k)/((δ/2)*(n:ℝ)) ≤
      (8*F*(1+(R:ℝ))^((1:ℝ)/100)/s)*(k:ℝ) := by
    rw [div_le_iff₀ hdpos]
    have hmul:=mul_le_mul_of_nonneg_left hn
      (by positivity : 0 ≤ 4*F*(1+(R:ℝ))^((1:ℝ)/100)*k/s)
    have hs0 : s≠0 := hs.ne'
    field_simp at hmul ⊢
    nlinarith
  have htail:=mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg k)
  have herror:=mul_le_mul_of_nonneg_right herr.le (Nat.cast_nonneg k)
  nlinarith

end Heisenberg.Bootstrap
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PeriodicReturnEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
namespace Heisenberg.Bootstrap
attribute [-instance] instDecidableEqFin
attribute [local irreducible] Pin.pinDensity LayeredExchange.layerWeight LayeredExchange.coinWiring Heisenberg.Exposure.layerMass Heisenberg.Exposure.layerHistory Heisenberg.Cycle.MissingSet Heisenberg.Return.HasHit Heisenberg.Exposure.exposedSweep
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular Heisenberg.Cycle

attribute [local instance] OAI.Heisenberg.Bootstrap.retDecEq
theorem periodic_return_estimate_oai (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ,∃ C≥0,∀ (p s : ℝ) (R : ℕ) (ρ : ℝ),0<p → 0<s → 1≤R →
      (2*(ρ+1/(1+(R:ℝ)))+8*C*(1+(R:ℝ))^((1:ℝ)/100)/s < p/4) →
      ∀ (B : Type) [Fintype B] [Nonempty B]
        (Λ F : Finset (Site (d+1))) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ)
        (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2),
        8*(4*(d+1)*(Fintype.card B)^2:ℕ)*Real.exp 1*s ≤ R →
        ∀ᶠ δ in 𝓝 (0:ℝ),0<δ →
        ∀ (N Q : ℕ) (_hQ : 0<Q) (_hqQ : q≤Q) (_hdiv : Q∣N+1)
          (a b : Fin (N+1) → Slots (B:=B) Λ)
          (_hab : ∀ j : Fin (N+1),j.val%Q<q →
            a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q))
          (_hsite : ∀ j : Fin (N+1),q≤j.val%Q → (a j).1.val=(b j).1.val)
          (rates : Fin (N+1) → ℝ) (_hp : ∀ j,0≤rates j ∧ rates j≤1)
          (_hrate : ∀ j : Fin (N+1),j.val%Q<q → rates j=δ/2)
          (P : Set (Fin (N+1)×Slots (B:=B) Λ))
          (_hP : ∀ z,z.2.1.val∉F → z∈P)
          (t : Fin (N+1)) (T : Finset P) (J : Finset (Slots (B:=B) Λ)),
          T.image Subtype.val=Heisenberg.Serial.targetsAt N t J → J.Nonempty →
          (∀ j∈J,j.1.val∈F) → (∀ j∈J,(t,j)∈P) →
          F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
          (∀ z u,0≤u → ((Finset.univ.filter (fun j : J=>dist j.val.1.val z≤u)).card:ℝ)≤L*(1+u)^((1:ℝ)/100)) →
          2*(⌊s/δ⌋₊+1)*Q ≤ N+1 →
          (∀ u x,(∑ c,layerMass (finRotate (N+1)) a b P rates c *
            (if ¬Regular (blocked Λ (holeCut (finRotate (N+1)) (fun i=>Equiv.swap (a i) (b i)) c P u))
              x R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0)) ≤ ρ) →
          (∑ c,layerMass (finRotate (N+1)) a b P rates c *
            returnCount (layerHistory (finRotate (N+1)) (fun i=>Equiv.swap (a i) (b i)) c) P T) ≤ p/2*J.card := by
  obtain ⟨M,C,hC,hflow⟩:=Heisenberg.Flow.indexed_prefix_leakage hd L hL
  refine ⟨M,C,hC,?_⟩
  intro p s R ρ hp hs hR1 herr B _ _ Λ F q _ edge a₀ b₀ ha₀ hb₀ hR
  let ar : ℕ → Slots (B:=B) Λ := fun j=>a₀ (q-1-j)
  let br : ℕ → Slots (B:=B) Λ := fun j=>b₀ (q-1-j)
  let er : Fin q ≃ Edges (B:=B) Step Λ := Fin.revPerm.trans edge
  have har (j : Fin q) : ar j=(er j).val.1 := by simpa [ar,er,Fin.rev,Nat.sub_sub,Nat.add_comm] using ha₀ j.rev
  have hbr (j : Fin q) : br j=(er j).val.2 := by simpa [br,er,Fin.rev,Nat.sub_sub,Nat.add_comm] using hb₀ j.rev
  let ε : ℝ:=p/(16*s*((Fintype.card (Slots (B:=B) Λ):ℝ)+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  have h1 : (0:ℝ)<s/2 := by positivity
  have h2 : (0:ℝ)<s/(R+2) := by positivity
  have h3 : (0:ℝ)<p/(16*s*((q:ℝ)^2+1)) := by positivity
  filter_upwards [hflow B Λ F q edge a₀ b₀ ha₀ hb₀ ε hε,
    hflow B Λ F q er ar br har hbr ε hε,
    (eventually_le_nhds (by norm_num : (0:ℝ)<2)),eventually_le_nhds h1,
    eventually_le_nhds h2,eventually_le_nhds h3] with δ hforward hback hδ2 hδs hδR hsmall
  intro hδ N Q hQ hqQ hdiv a b hab hsite rates hrates hrate P hP t T J hTJ hJpos hJF hJP hF hframe hg hroom hbad
  let : NeZero Q := ⟨hQ.ne'⟩
  let n:=⌊s/δ⌋₊
  have hn : 0<n := (mesh_floor s δ hs hδ hδs).1
  have hnd : s/2 ≤ δ*(n:ℝ) := (mesh_floor s δ hs hδ hδs).2.1
  have hdn : (n:ℝ)*δ ≤ s := by simpa only [mul_comm] using (mesh_floor s δ hs hδ hδs).2.2
  have htail : ((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R ≤ 1/(1+(R:ℝ)) :=
    Heisenberg.Clocks.binomial_clock_tail n R (4*(d+1)*(Fintype.card B)^2:ℕ) δ s
      (by positivity) hδ.le hs.le hR1 (round_clock_bound s δ hs hδ R hδR) hR
  have hremainder : (n:ℝ)*(ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2) ≤ p/4*J.card :=
    mesh_remainder p s δ ε hp hs hδ _ q n J.card
      (Finset.card_pos.mpr hJpos) hdn rfl hsmall
  have harith:=leakage_arithmetic p s δ C ρ
    (((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R) n R J.card hp hs hδ hC htail hnd herr
    ((n:ℝ)*(ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2)) hremainder
  have hc (u : Fin (N+1)) : Heisenberg.Schedule.cut u Q n ≤ (n+1)*Q := by
    have hh:=warm_le (Q:=Q) u
    dsimp only [Heisenberg.Schedule.cut]
    nlinarith
  have hroom' : Heisenberg.Schedule.cut t Q n+Heisenberg.Schedule.cut (reverseIndex q t) Q n ≤ N+1 := by
    have hct:=hc t
    have hcr:=hc (reverseIndex q t)
    dsimp only [n] at hct hcr ⊢
    nlinarith
  have hret:=period_return_two_ends N q a b rates hrates P {v | v.1.val∈F} hP t T J (by with_reducible convert hTJ using 1; congr! 20) hJF
    (Heisenberg.Schedule.cut t Q n) (Heisenberg.Schedule.cut (reverseIndex q t) Q n) hroom'
    ((1-p/2)*J.card) ((1-p/2)*J.card) ?_ ?_
  · with_reducible convert hret using 1 <;> first | (solve | ring) | congr! 20
  · intro f hf hfJ hfs
    apply harith.trans
    have hh:=hforward hδ hδ2 (Fin (N+1)) (N+1) Q (finRotate (N+1)) (Equiv.refl _) (fun _=>rfl)
      hQ hqQ hdiv a b hab hsite rates hrates hrate P t J f n R ρ hn (by omega)
      hF hframe ?_ hfJ hf hfs hg ?_
    · convert hh using 1 <;> first | rfl | (congr 2; first | rfl | exact Subsingleton.elim _ _)
    · intro c j hj
      refine ⟨?_,hJF j hj⟩
      exact fun h=>Set.disjoint_left.mp (missing_disjoint_pins _ P) h (hJP j hj)
    · intro i j
      exact hbad _ _
  · intro f hf hfJ hfs
    apply harith.trans
    have hh:=hback hδ hδ2 (Fin (N+1)) (N+1) Q (finRotate (N+1)).symm (reverseIndex q)
      (reverseIndex_next) hQ hqQ hdiv
      (a ∘ (finRotate (N+1)).symm) (b ∘ (finRotate (N+1)).symm) ?_ ?_
      (rates ∘ (finRotate (N+1)).symm) (fun j=>hrates _) ?_ P (reverseIndex q t) J f n R ρ hn (by omega)
      hF hframe ?_ hfJ hf ?_ hg ?_
    · convert hh using 1 <;> first | rfl | (congr 2; first | rfl | exact Subsingleton.elim _ _)
    · intro j hj
      have hh:=reverse_phase_spatial hdiv (NeZero.pos q) hqQ j hj
      have hj' : q-1-j.val%Q < q := by omega
      have ht:=hab ((finRotate (N+1)).symm (reverseIndex q j)) (by rw [hh]; exact hj')
      simpa only [Function.comp_apply,hh,ar,br] using ht
    · intro j hj
      exact hsite _ (reverse_phase_completion hdiv (NeZero.pos q) hqQ j hj)
    · intro j hj
      have hh:=reverse_phase_spatial hdiv (NeZero.pos q) hqQ j hj
      exact hrate _ (by rw [hh]; omega)
    · intro c j hj
      have ht : reverseIndex q (reverseIndex q t)=t := by exact sub_sub_cancel (q : Fin (N+1)) t
      rw [ht]
      refine ⟨?_,hJF j hj⟩
      exact fun h=>Set.disjoint_left.mp (missing_disjoint_pins _ P) h (hJP j hj)
    · have ht : reverseIndex q (reverseIndex q t)=t := by exact sub_sub_cancel (q : Fin (N+1)) t
      simp only [ht,Function.comp_apply]
      convert hfs using 1
    · intro i j
      have he:=regularity_reverse (finRotate (N+1)) a b P rates
        (fun D : Set (Slots (B:=B) Λ)=>¬Regular (blocked Λ D) j.val.1.val R M (1/(100*(d+1:ℝ))))
        (reverseIndex q (run (reverseIndex q t) (cut (reverseIndex q t) Q i.val)))
      have hx:=hbad (reverseIndex q (run (reverseIndex q t) (cut (reverseIndex q t) Q i.val))) j.val.1.val
      have hz:=he.le.trans (show _≤ρ from by convert hx using 1; congr! 20)
      simp only [Function.comp_apply]
      convert hz using 1 <;> congr! 20

end Heisenberg.Bootstrap
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.Bootstrap.periodic_return_estimate_oai := @OAI.Heisenberg.Bootstrap.periodic_return_estimate_oai
