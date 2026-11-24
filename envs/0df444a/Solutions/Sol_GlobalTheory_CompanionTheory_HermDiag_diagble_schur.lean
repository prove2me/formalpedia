-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.diagble_schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:07.084626+00:00
-- url     : https://prove2.me/submissions/e4cb2beb-6e43-447d-8a59-8c166e47639e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_ct_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_of_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermDiag
variable {R : Type} [CommRing R]
variable {σ : R →+* R} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.CompanionTheory.HermDiag
theorem _root_.solution (hinv : ∀ a, σ (σ a) = a) (ih : ∀ h : Matrix ι ι R, Hm σ h → Diagble σ h)
    {h : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R} (hh : Hm σ h)
    (hu : IsUnit (h (Sum.inl ()) (Sum.inl ()))) : Diagble σ h := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  set a := h (Sum.inl ()) (Sum.inl ()) with ha
  have hfa : σ a = a := hh _ _
  have hfv : σ v = v := by
    have h1 : a * σ v = 1 := by
      have := congrArg σ hv
      rwa [map_mul, map_one, hfa] at this
    calc σ v = (a * v) * σ v := by rw [hv, one_mul]
      _ = (a * σ v) * v := by ring
      _ = v := by rw [h1, one_mul]
  let B : Matrix Unit ι R := h.toBlocks₁₂
  let C : Matrix ι Unit R := h.toBlocks₂₁
  let D : Matrix ι ι R := h.toBlocks₂₂
  have hA : h.toBlocks₁₁ = Matrix.diagonal fun _ : Unit => a := by
    ext i j
    cases i; cases j
    simp [Matrix.toBlocks₁₁, ha]
  have hblocks : h = Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) B C D := by
    rw [← hA]; exact (Matrix.fromBlocks_toBlocks h).symm
  have hCB : ∀ i, σ (B () i) = C i () := fun i => hh _ _
  have hCB' : ∀ i, σ (C i ()) = B () i := fun i => hh _ _
  have hD : ∀ i j, σ (D i j) = D j i := fun i j => hh _ _
  let p : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R := Matrix.fromBlocks 1 (-(v • B)) 0 1
  let p' : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R := Matrix.fromBlocks 1 (v • B) 0 1
  have hpp : p * p' = 1 := by
    simp only [p, p']
    rw [Matrix.fromBlocks_multiply]; simp
  have hpp' : p' * p = 1 := by
    simp only [p, p']
    rw [Matrix.fromBlocks_multiply]; simp
  let E : Matrix ι ι R := D - v • (C * B)
  have hE : Hm σ E := by
    intro i j
    simp only [E, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Finset.univ_unique,
      Finset.sum_singleton, smul_eq_mul, map_sub, map_mul, hfv, hD, hCB, hCB']
    simp only [PUnit.default_eq_unit]
    ring
  have hct : ct σ p = Matrix.fromBlocks 1 0 (-(v • C)) 1 := by
    ext (i | i) (j | j)
    · simp [p, ct_apply, Matrix.one_apply]
    · simp [p, ct_apply]
    · cases j; simp [p, ct_apply, hfv, hCB]
    · by_cases hij : i = j
      · subst hij; simp [p, ct_apply]
      · simp [p, ct_apply, Matrix.one_apply, hij, Ne.symm hij]
  have hcongr : ct σ p * h * p = Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) 0 0 E := by
    have hav : ∀ {c : Type} (X : Matrix Unit c R), (Matrix.diagonal fun _ : Unit => a) * (v • X) = X := by
      intro c X
      ext i j
      cases i
      rw [Matrix.diagonal_mul]
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (X () j) * hv
    have hva : ∀ {c : Type} (X : Matrix c Unit R), (v • X) * (Matrix.diagonal fun _ : Unit => a) = X := by
      intro c X
      ext i j
      cases j
      rw [Matrix.mul_diagonal]
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (X i ()) * hv
    rw [hct, hblocks]
    simp only [p]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hva, hav, E, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, sub_eq_add_neg, add_comm]
  apply diagble_of_congr hpp hpp'
  rw [hcongr]
  exact diagble_block hfa (ih E hE)
end GlobalTheory.CompanionTheory.HermDiag
