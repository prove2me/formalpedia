-- Prove2me | solution 1 for OAI.ListChains.uniform_fillings_from_partial_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T02:38:29.339032+00:00
-- url     : https://prove2.me/submissions/853030e6-2ad1-4d57-9305-641e44f5625c

import Mathlib
import Definitions.Def_OAIQ66So019
import Theorems.Thm_OAI_ListChains_controlled_commuting_additivity

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIdempotentDiagrams
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteIdempotentDiagrams
section

variable {R T : Type*} [NonUnitalRing R] [AddCommGroup T]

variable {K m : Type*} [CommRing K] [Fintype m]

open Matrix
open scoped Matrix

lemma rankOne_idem (u l : m → K) (h : l ⬝ᵥ u = 1) :
    rankOne u l * rankOne u l = rankOne u l := by
  simp only [rankOne, vecMulVec_mul_vecMulVec, h, one_smul]

lemma rankOne_orthogonal (u l v a : m → K) (h : l ⬝ᵥ v = 0) :
    rankOne u l * rankOne v a = 0 := by
  simp only [rankOne, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

lemma rankOne_difference (z : Matrix m m K → T) (hz : OrthogonalAdditive z)
    (u v l a : m → K) (hlu : l ⬝ᵥ u = 1) (hlv : l ⬝ᵥ v = 0)
    (hau : a ⬝ᵥ u = 0) (hav : a ⬝ᵥ v = 1) :
    z (rankOne (u + v) l) - z (rankOne u l) =
      z (rankOne v a) - z (rankOne v (a - l)) := by
  have hl : l ⬝ᵥ (u + v) = 1 := by simp [dotProduct_add, hlu, hlv]
  have ha : (a - l) ⬝ᵥ v = 1 := by simp [sub_dotProduct, hav, hlv]
  have hcross : (a - l) ⬝ᵥ (u + v) = 0 := by
    simp [sub_dotProduct, dotProduct_add, hau, hav, hlu, hlv]
  have h₁ := hz (rankOne u l) (rankOne v a)
    (rankOne_idem _ _ hlu) (rankOne_idem _ _ hav)
    (rankOne_orthogonal _ _ _ _ hlv) (rankOne_orthogonal _ _ _ _ hau)
  have h₂ := hz (rankOne (u + v) l) (rankOne v (a - l))
    (rankOne_idem _ _ hl) (rankOne_idem _ _ ha)
    (rankOne_orthogonal _ _ _ _ hlv) (rankOne_orthogonal _ _ _ _ hcross)
  have heq : rankOne u l + rankOne v a =
      rankOne (u + v) l + rankOne v (a - l) := by
    ext i j
    simp only [rankOne, vecMulVec_apply, Matrix.add_apply, Pi.add_apply, Pi.sub_apply]
    ring
  have he : z (rankOne u l) + z (rankOne v a) =
      z (rankOne (u + v) l) + z (rankOne v (a - l)) := by
    rw [← h₁, ← h₂, heq]
  calc z (rankOne (u + v) l) - z (rankOne u l) =
      (z (rankOne (u + v) l) + z (rankOne v (a - l))) -
      (z (rankOne u l) + z (rankOne v (a - l))) := by abel
    _ = (z (rankOne u l) + z (rankOne v a)) -
      (z (rankOne u l) + z (rankOne v (a - l))) := by rw [← he]
    _ = z (rankOne v a) - z (rankOne v (a - l)) := by abel

lemma variation_constant (z : Matrix m m K → T) (hz : OrthogonalAdditive z)
    (u v w l a b : m → K)
    (hlu : l ⬝ᵥ u = 1) (hlv : l ⬝ᵥ v = 0) (hlw : l ⬝ᵥ w = 0)
    (hau : a ⬝ᵥ u = 0) (hav : a ⬝ᵥ v = 1) (haw : a ⬝ᵥ w = 0)
    (hbu : b ⬝ᵥ u = 0) (hbv : b ⬝ᵥ v = 0) (hbw : b ⬝ᵥ w = 1)
    (k : K) :
    z (rankOne ((u + k • v) + v) l) - z (rankOne (u + k • v) l) =
      z (rankOne ((u + w) + v) l) - z (rankOne (u + w) l) := by
  let a' := a - k • l + k • b
  have ha'v : a' ⬝ᵥ v = 1 := by
    simp [a', add_dotProduct, sub_dotProduct, smul_dotProduct, hav, hlv, hbv]
  have ha'u : a' ⬝ᵥ (u + k • v) = 0 := by
    simp [a', add_dotProduct, sub_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, hlu, hlv, hau, hav, hbu, hbv]
  have ha'w : a' ⬝ᵥ (u + w) = 0 := by
    simp [a', add_dotProduct, sub_dotProduct, dotProduct_add,
      smul_dotProduct, hlu, hlw, hau, haw, hbu, hbw]
  have h₁ := rankOne_difference z hz (u + k • v) v l a'
    (by simp [dotProduct_add, dotProduct_smul, hlu, hlv]) hlv ha'u ha'v
  have h₂ := rankOne_difference z hz (u + w) v l a'
    (by simp [dotProduct_add, hlu, hlw]) hlv ha'w ha'v
  exact h₁.trans h₂.symm

lemma nsmul_variation (p : ℕ) [CharP K p]
    (z : Matrix m m K → T) (hz : OrthogonalAdditive z)
    (u v w l a b : m → K)
    (hlu : l ⬝ᵥ u = 1) (hlv : l ⬝ᵥ v = 0) (hlw : l ⬝ᵥ w = 0)
    (hau : a ⬝ᵥ u = 0) (hav : a ⬝ᵥ v = 1) (haw : a ⬝ᵥ w = 0)
    (hbu : b ⬝ᵥ u = 0) (hbv : b ⬝ᵥ v = 0) (hbw : b ⬝ᵥ w = 1) :
    p • z (rankOne (u + v) l) = p • z (rankOne u l) := by
  let δ := z (rankOne ((u + w) + v) l) - z (rankOne (u + w) l)
  let c (n : ℕ) := z (rankOne (u + (n : K) • v) l)
  have hstep (n : ℕ) : c (n + 1) - c n = δ := by
    have h := variation_constant z hz u v w l a b
      hlu hlv hlw hau hav haw hbu hbv hbw (n : K)
    simpa [c, δ, Nat.cast_add, add_smul, add_assoc] using h
  have hc (n : ℕ) : c n = c 0 + n • δ := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hstep n
      rw [sub_eq_iff_eq_add] at h
      rw [h, ih, succ_nsmul]
      abel
  have hclose : c p = c 0 := by simp [c]
  have hzero : p • δ = 0 := by
    have h := hc p
    rw [hclose] at h
    exact (add_left_cancel (h.symm.trans (add_zero (c 0)).symm))
  have h₀ := hstep 0
  simp only [c, Nat.cast_zero, zero_smul, add_zero, zero_add,
    Nat.cast_one, one_smul] at h₀
  apply sub_eq_zero.mp
  rw [← nsmul_sub, h₀]
  exact hzero

lemma OrthogonalAdditive.transpose (z : Matrix m m K → T) (hz : OrthogonalAdditive z) :
    OrthogonalAdditive (fun M : Matrix m m K => z Mᵀ) := by
  intro E P hE hP hEP hPE
  change z (E + P)ᵀ = z Eᵀ + z Pᵀ
  rw [transpose_add]
  apply hz
  · simpa only [transpose_mul] using congrArg Matrix.transpose hE
  · simpa only [transpose_mul] using congrArg Matrix.transpose hP
  · simpa only [transpose_mul, transpose_zero] using congrArg Matrix.transpose hPE
  · simpa only [transpose_mul, transpose_zero] using congrArg Matrix.transpose hEP

variable [DecidableEq m]

@[simp] lemma diagonalUnit_idem (i : m) :
    (diagonalUnit i : Matrix m m K) * diagonalUnit i = diagonalUnit i :=
  rankOne_idem _ _ (by simp)

lemma diagonalUnit_orthogonal {i j : m} (h : i ≠ j) :
    (diagonalUnit i : Matrix m m K) * diagonalUnit j = 0 :=
  rankOne_orthogonal _ _ _ _ (by simp [h])

lemma nsmul_diagonal_eq (p : ℕ) [CharP K p]
    (z : Matrix m m K → T) (hz : OrthogonalAdditive z)
    (i j k : m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    p • z (diagonalUnit i) = p • z (diagonalUnit j) := by
  have hji := hij.symm
  have hki := hik.symm
  have hkj := hjk.symm
  have h₁ := nsmul_variation p (fun M : Matrix m m K => z Mᵀ) (OrthogonalAdditive.transpose z hz)
    (basisVector i) (basisVector j) (basisVector k)
    (basisVector i) (basisVector j) (basisVector k)
    (by simp) (by simp [hij]) (by simp [hik])
    (by simp [hji]) (by simp) (by simp [hjk])
    (by simp [hki]) (by simp [hkj]) (by simp)
  simp only [rankOne, transpose_vecMulVec] at h₁
  have h₂ := nsmul_variation p z hz
    (basisVector i) (basisVector j - basisVector i) (basisVector k)
    (basisVector i + basisVector j) (basisVector j) (basisVector k)
    (by simp [hji])
    (by simp [dotProduct_sub, hij, hji])
    (by simp [hik, hjk])
    (by simp [hji]) (by simp [dotProduct_sub, hji]) (by simp [hjk])
    (by simp [hki]) (by simp [dotProduct_sub, hkj, hki]) (by simp)
  have hv : (basisVector i : m → K) + (basisVector j - basisVector i) =
      basisVector j := by abel
  rw [hv] at h₂
  have h₃ := nsmul_variation p (fun M : Matrix m m K => z Mᵀ) (OrthogonalAdditive.transpose z hz)
    (basisVector j) (basisVector i) (basisVector k)
    (basisVector j) (basisVector i) (basisVector k)
    (by simp) (by simp [hji]) (by simp [hjk])
    (by simp [hij]) (by simp) (by simp [hik])
    (by simp [hkj]) (by simp [hki]) (by simp)
  simp only [rankOne, transpose_vecMulVec, add_comm (basisVector j) (basisVector i)] at h₃
  exact h₁.symm.trans (h₂.symm.trans h₃)

end

section

open Matrix
open scoped Matrix

variable {K R T : Type*} [CommRing K] [Ring R] [AddCommGroup T]

lemma orthogonal_sum_idem {A B : R} (hA : A * A = A) (hB : B * B = B)
    (hAB : A * B = 0) (hBA : B * A = 0) : (A + B) * (A + B) = A + B := by
  simp [add_mul, mul_add, hA, hB, hAB, hBA]

lemma orthogonalAdditive_one (z : Mat3 K → T) (hz : OrthogonalAdditive z) :
    z 1 = z (diagonalUnit 0) + z (diagonalUnit 1) + z (diagonalUnit 2) := by
  have h01 : (diagonalUnit 0 : Mat3 K) * diagonalUnit 1 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h10 : (diagonalUnit 1 : Mat3 K) * diagonalUnit 0 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h02 : (diagonalUnit 0 : Mat3 K) * diagonalUnit 2 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h20 : (diagonalUnit 2 : Mat3 K) * diagonalUnit 0 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h12 : (diagonalUnit 1 : Mat3 K) * diagonalUnit 2 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h21 : (diagonalUnit 2 : Mat3 K) * diagonalUnit 1 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h₁ := hz (diagonalUnit 0) (diagonalUnit 1)
    (diagonalUnit_idem _) (diagonalUnit_idem _) h01 h10
  have h₂ := hz (diagonalUnit 0 + diagonalUnit 1) (diagonalUnit 2)
    (orthogonal_sum_idem (diagonalUnit_idem _) (diagonalUnit_idem _) h01 h10)
    (diagonalUnit_idem _)
    (by simp only [add_mul, h02, h12, add_zero])
    (by simp only [mul_add, h20, h21, add_zero])
  rw [three_diagonal_sum] at h₂
  exact h₂.trans (congrArg (· + z (diagonalUnit 2)) h₁)

lemma ThreeCopies.mem_system (C : ThreeCopies K R) (i : Fin 3) (M : Mat3 K)
    (hM : M * M = M) : C.copy i M ∈ C.system := Or.inr ⟨i, M, hM, rfl⟩

lemma ThreeCopies.diagonal_mem (C : ThreeCopies K R) (i j : Fin 3) :
    C.copy i (diagonalUnit j) ∈ C.system := C.mem_system i _ (diagonalUnit_idem j)

lemma ThreeCopies.additive_copy (C : ThreeCopies K R) (z : R → T)
    (hz : OrthogonalAdditiveOn C.system z) (i : Fin 3) :
    OrthogonalAdditive (fun M => z (C.copy i M)) := by
  intro E P hE hP hEP hPE
  have hsum := C.mem_system i (E + P) (orthogonal_sum_idem hE hP hEP hPE)
  rw [map_add] at hsum
  have h := hz (C.copy i E) (C.copy i P) (C.mem_system i E hE)
    (C.mem_system i P hP) hsum
    (by rw [← map_mul, hEP, map_zero]) (by rw [← map_mul, hPE, map_zero])
  simpa only [map_add] using h

theorem ThreeCopies.annihilates_one (p : ℕ) [CharP K p]
    (C : ThreeCopies K R) (z : R → T) (hz : OrthogonalAdditiveOn C.system z) :
    p • z 1 = 0 := by
  have hcopy (i) := C.additive_copy z hz i
  have hcommon (i : Fin 3) :
      p • z (C.copy i (diagonalUnit 0)) = p • z (C.copy 0 (diagonalUnit 1)) := by
    have h := nsmul_diagonal_eq p (fun M => z (C.copy i M)) (hcopy i)
      0 1 2 (by decide) (by decide) (by decide)
    simpa only [C.common_second] using h
  have hsplit : z (C.copy 0 (diagonalUnit 0)) =
      z (C.copy 1 (diagonalUnit 0)) + z (C.copy 2 (diagonalUnit 0)) := by
    rw [C.partition]
    apply hz _ _ (C.diagonal_mem 1 0) (C.diagonal_mem 2 0)
    · rw [← C.partition]
      exact C.diagonal_mem 0 0
    · exact C.partition_orthogonal
    · exact C.partition_orthogonal'
  have hq : p • z (C.copy 0 (diagonalUnit 1)) =
      p • z (C.copy 0 (diagonalUnit 1)) + p • z (C.copy 0 (diagonalUnit 1)) := by
    calc p • z (C.copy 0 (diagonalUnit 1)) = p • z (C.copy 0 (diagonalUnit 0)) :=
           (hcommon 0).symm
         _ = p • z (C.copy 1 (diagonalUnit 0)) +
           p • z (C.copy 2 (diagonalUnit 0)) := by rw [hsplit, nsmul_add]
         _ = _ := by rw [hcommon, hcommon]
  have hzero : p • z (C.copy 0 (diagonalUnit 1)) = 0 := by
    exact (add_left_cancel ((add_zero _).trans hq)).symm
  have hzero₀ : p • z (C.copy 0 (diagonalUnit 0)) = 0 :=
    (hcommon 0).trans hzero
  have hzero₂ : p • z (C.copy 0 (diagonalUnit 2)) = 0 := by
    have h := nsmul_diagonal_eq p (fun M => z (C.copy 0 M)) (hcopy 0)
      0 2 1 (by decide) (by decide) (by decide)
    exact h.symm.trans hzero₀
  have hsum := orthogonalAdditive_one (fun M => z (C.copy 0 M)) (hcopy 0)
  rw [C.first_one] at hsum
  rw [hsum, nsmul_add, nsmul_add, hzero₀, hzero, hzero₂, add_zero, add_zero]

end

open Matrix
open scoped Matrix

end FiniteIdempotentDiagrams

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsMapChainComp
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*)

variable [Group G]

lemma FillsAt.mono {A B : Set G} {n : ℕ} {z : Chain G}
    (hz : FillsAt G A n z) (hAB : A ⊆ B) : FillsAt G B n z := by
  obtain ⟨w,hw,ha,hd⟩ := hz
  exact ⟨w,hw,controlledModule_mono G hAB ha,hd⟩

lemma FillsAt.add {B : Set G} {n : ℕ} {z z' : Chain G}
    (hz : FillsAt G B n z) (hz' : FillsAt G B n z') : FillsAt G B n (z+z') := by
  obtain ⟨w,hw,ha,hd⟩ := hz
  obtain ⟨w',hw',ha',hd'⟩ := hz'
  exact ⟨w+w',Submodule.add_mem _ hw hw',Submodule.add_mem _ ha ha',by rw [map_add,hd,hd']⟩

lemma FillsAt.neg {B : Set G} {n : ℕ} {z : Chain G}
    (hz : FillsAt G B n z) : FillsAt G B n (-z) := by
  obtain ⟨w,hw,ha,hd⟩ := hz
  exact ⟨-w,Submodule.neg_mem _ hw,Submodule.neg_mem _ ha,by rw [map_neg,hd]⟩

open scoped Pointwise

lemma subset_symmetricClosure (S : Set G) : S ⊆ symmetricClosure G S :=
  fun _ h => Set.mem_insert_of_mem _ (Or.inl h)

lemma isBound_symmetricClosure {S : Set G} (hS : S.Finite) :
    IsBound G (symmetricClosure G S) where
  finite := (hS.union hS.inv).insert 1
  one_mem := Set.mem_insert _ _
  inv_mem := by
    intro a ha
    rcases ha with rfl | ha | ha
    · simpa only [symmetricClosure,inv_one] using (Set.mem_insert (1 : G) (S ∪ S⁻¹))
    · exact Set.mem_insert_of_mem _ (Or.inr (by simpa using ha))
    · exact Set.mem_insert_of_mem _ (Or.inl ha)

lemma finite_common_bound {ι : Type*} [Finite ι] (B : ι → Set G)
    (hB : ∀ i, IsBound G (B i)) :
    ∃ C : Set G, IsBound G C ∧ ∀ i, B i ⊆ C := by
  let C := symmetricClosure G (⋃ i, B i)
  refine ⟨C,isBound_symmetricClosure G (Set.finite_iUnion fun i => (hB i).finite),?_⟩
  intro i
  exact Set.Subset.trans (Set.subset_iUnion B i) (subset_symmetricClosure G _)

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryPrefixOperators
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BinaryPrefixOperators

open FiniteIdempotentDiagrams

variable (K : Type*) [CommRing K]

lemma system_subset : (threeCopies K).system ⊆ idempotents K := by
  rintro E (rfl | ⟨i, M, hM, rfl⟩)
  · exact identity_mem K
  · exact Or.inr ⟨by rw [← map_mul, hM], i, M, rfl⟩

theorem finite_idempotents (p : ℕ) [CharP K p] {T : Type*} [AddCommGroup T]
    (z : algebra K → T) (hz : OrthogonalAdditiveOn (idempotents K) z) : p • z 1 = 0 := by
  apply (threeCopies K).annihilates_one p z
  intro E P hE hP hSum hEP hPE
  exact hz E P (system_subset K hE) (system_subset K hP) (system_subset K hSum) hEP hPE

theorem finite_idempotent_assignment (p : ℕ) [CharP K p]
    {T : Type*} [AddCommGroup T] (z : idempotents K → T) (hz : AssignmentAdditive K z) :
    p • z ⟨1, identity_mem K⟩ = 0 := by
  classical
  let z' : algebra K → T := fun E => if h : E ∈ idempotents K then z ⟨E, h⟩ else 0
  have hz' : OrthogonalAdditiveOn (idempotents K) z' := by
    intro E P hE hP hSum hEP hPE
    simp only [z', dite_eq_left hE, dite_eq_left hP, dite_eq_left hSum]
    exact hz ⟨E, hE⟩ ⟨P, hP⟩ hSum hEP hPE
  simpa only [z', dite_eq_left (identity_mem K)] using finite_idempotents K p z' hz'

end BinaryPrefixOperators

namespace ListChains
section

variable (G : Type*) [Group G]

lemma fillsAt_iff_mem_boundaries {B : Set G} {n : ℕ} {z : Chain G} :
    FillsAt G B n z ↔ z ∈ boundedBoundaries G B n := by
  simp only [FillsAt,boundedBoundaries,Submodule.mem_map,Submodule.mem_inf]
  constructor
  · rintro ⟨w,hd,ha,he⟩
    exact ⟨w,⟨hd,ha⟩,he⟩
  · rintro ⟨w,⟨hd,ha⟩,he⟩
    exact ⟨w,hd,ha,he⟩

lemma fillsAt_iff_quotient_zero {B : Set G} {n : ℕ} {z : Chain G} :
    FillsAt G B n z ↔ (boundedBoundaries G B n).mkQ z = 0 := by
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,fillsAt_iff_mem_boundaries]

theorem IdempotentSplittings.uniform_nsmul_fillings
    {K : Type*} [CommRing K] [Finite K] (p : ℕ) [CharP K p]
    {f g : G →* G} (F : IdempotentSplittings G K f)
    {A : Set G} (hA : IsBound G A) {n : ℕ} (hn : 0 < n)
    (H : ControlledNullBelow G g A n) :
    ∃ B : Set G, IsBound G B ∧ ∀ z, z ∈ degreeModule G n →
      z ∈ controlledModule G A → boundary G z = 0 →
      FillsAt G B n (p • mapChain G (f ∘ g) z) := by
  classical
  let I := BinaryPrefixOperators.idempotents K
  let : Fintype I := (BinaryPrefixOperators.idempotents_finite K).fintype
  let R := {r : I × I // r.1.val + r.2.val ∈ BinaryPrefixOperators.idempotents K ∧
    r.1.val*r.2.val = 0 ∧ r.2.val*r.1.val = 0}
  have hr (r : R) : ∃ B : Set G, IsBound G B ∧
      ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
      FillsAt G B n (mapChain G (fun x => F.map r.val.1 (g x) * F.map r.val.2 (g x)) z -
        mapChain G (F.map r.val.1 ∘ g) z - mapChain G (F.map r.val.2 ∘ g) z) := by
    exact controlled_commuting_additivity G g H.homotopy hn hA H.isBound
      H.degree (H.zero n le_rfl) H.controlled H.equation (F.map r.val.1) (F.map r.val.2)
      (F.commute r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2)
  choose B hB hfill using hr
  obtain ⟨C,hC,hBC⟩ := finite_common_bound G B hB
  refine ⟨C,hC,?_⟩
  intro z hzd hza hz
  let π := (boundedBoundaries G C n).mkQ
  let Z : I → Chain G ⧸ boundedBoundaries G C n := fun E => π (mapChain G (F.map E ∘ g) z)
  have hZ : BinaryPrefixOperators.AssignmentAdditive K Z := by
    intro E P hSum hEP hPE
    let r : R := ⟨(E,P),hSum,hEP,hPE⟩
    have hw := (hfill r z hzd hza hz).mono G (hBC r)
    have hfun : (fun x => F.map E (g x)*F.map P (g x)) =
        (F.map ⟨E.val+P.val,hSum⟩ ∘ g) := funext fun x => (F.addition E P hSum hEP hPE (g x)).symm
    change FillsAt G C n (mapChain G (fun x => F.map E (g x)*F.map P (g x)) z -
      mapChain G (F.map E ∘ g) z - mapChain G (F.map P ∘ g) z) at hw
    rw [hfun] at hw
    have he := (fillsAt_iff_quotient_zero G).mp hw
    change Z ⟨E.val+P.val,hSum⟩ = Z E + Z P
    apply sub_eq_zero.mp
    simpa only [map_sub,sub_add_eq_sub_sub] using he
  have hkill := BinaryPrefixOperators.finite_idempotent_assignment K p Z hZ
  apply (fillsAt_iff_quotient_zero G).mpr
  rw [map_nsmul]
  simpa only [Z,F.identity] using hkill

theorem uniform_fillings_from_partial_homotopy_oai
    {f g : G →* G} (F₂ : IdempotentSplittings G (ZMod 2) f)
    (F₃ : IdempotentSplittings G (ZMod 3) f)
    {A : Set G} (hA : IsBound G A) {n : ℕ} (hn : 0 < n)
    (H : ControlledNullBelow G g A n) :
    ∃ B : Set G, IsBound G B ∧ ∀ z, z ∈ degreeModule G n →
      z ∈ controlledModule G A → boundary G z = 0 →
      FillsAt G B n (mapChain G (f ∘ g) z) := by
  obtain ⟨B₂,hB₂,h₂⟩ := F₂.uniform_nsmul_fillings G 2 hA hn H
  obtain ⟨B₃,hB₃,h₃⟩ := F₃.uniform_nsmul_fillings G 3 hA hn H
  refine ⟨B₂ ∪ B₃,hB₂.union G hB₃,?_⟩
  intro z hzd hza hz
  have h := ((h₃ z hzd hza hz).mono G Set.subset_union_right).add G
    (((h₂ z hzd hza hz).mono G Set.subset_union_left).neg G)
  have he : 3 • mapChain G (f ∘ g) z + -(2 • mapChain G (f ∘ g) z) = mapChain G (f ∘ g) z := by
    simp only [succ_nsmul,zero_nsmul,zero_add]
    abel
  rwa [he] at h

end

end ListChains

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ListChains.uniform_fillings_from_partial_homotopy_oai.{u_1} := @OAI.ListChains.uniform_fillings_from_partial_homotopy_oai.{u_1}
