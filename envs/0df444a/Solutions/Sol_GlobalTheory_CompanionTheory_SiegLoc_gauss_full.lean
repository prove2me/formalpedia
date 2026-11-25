-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.gauss_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:39:52.358519+00:00
-- url     : https://prove2.me/submissions/19097833-f4a5-41c1-bb3f-dc9eebe9c25c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizableStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShiftStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardRangeMulQuotientBoundedLevelStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumDiagonalFactorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumCongrInvarianceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicityReductionDiagonalProdStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonalityStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeriesEqDens
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_gauss1
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_lft
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_mem_lev_iff
import Theorems.Thm_GlobalTheory_T_card_range_mul_quotient_bounded_level
import Theorems.Thm_GlobalTheory_T_hermitian_matrix_diagonalizable
import Theorems.Thm_GlobalTheory_T_matrix_gauss_sum_congr_invariance
import Theorems.Thm_GlobalTheory_T_matrix_gauss_sum_diagonal_factor
import Theorems.Thm_GlobalTheory_T_multiplicity_reduction_diagonal_prod
import Theorems.Thm_GlobalTheory_T_unramified_quotient_card
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.GaussRec.mk_lft



set_option autoImplicit false
noncomputable section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc
namespace GlobalTheory.CompanionTheory.SiegLoc
theorem _root_.solution {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) {m n : ℕ} (k : ℕ) (S : Matrix (Fin m) (Fin m) R) (hS : IsUnimod σ S)
    (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hB : B ∈ hermMod σ ϖ n k) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B)) := by
  obtain ⟨h, hh, rfl⟩ := hB
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR n h hh
  obtain ⟨p, p', e, hpp, hpp', he, hpe⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR m S hS.1
  have hq0 : (q : ℂ) ≠ 0 := by
    have := hR.one_lt
    exact_mod_cast (by omega : q ≠ 0)
  have hunit : ∀ l, e l ∉ lev ϖ 1 := by
    intro l hl
    have h1 : IsUnit p.det := Matrix.isUnit_det_of_right_inverse hpp
    have h2 : IsUnit (cT σ p).det := by
      have : cT σ p * cT σ p' = 1 := by
        have : cT σ (p' * p) = cT σ p * cT σ p' := by
          simp [cT, Matrix.transpose_mul, Matrix.map_mul]
        rw [← this, hpp']
        simp [cT]
      exact Matrix.isUnit_det_of_right_inverse this
    have h3 : IsUnit (Matrix.diagonal e).det := by
      rw [← hpe, Matrix.det_mul, Matrix.det_mul]
      exact (h2.mul hS.2).mul h1
    rw [Matrix.det_diagonal] at h3
    have h4 : IsUnit (e l) := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ l)) h3
    obtain ⟨c, hc⟩ := mem_lev_iff.1 hl
    rw [hc, pow_one] at h4
    exact hR.notUnit (isUnit_of_mul_isUnit_left h4)
  choose eI heI hcard hsum using fun i => GlobalTheory.T.card_range_mul_quotient_bounded_level R σ ϖ q ε hR ψ hψ (fun j a ha ha' => gauss1 hR hψ hε j a ha ha') k (d i) (hd i)
  rw [GlobalTheory.T.matrix_gauss_sum_congr_invariance R σ ϖ hR.fix_ϖ hR.inv k (ψ k) m n h _ g g' S _ p p' hgg hgg' hpp hpp' hgd hpe,
    GlobalTheory.T.matrix_gauss_sum_diagonal_factor R σ ϖ hR.fix_ϖ k (ψ k) m n d e,
    GlobalTheory.T.multiplicity_reduction_diagonal_prod R σ ϖ hR.fix_ϖ hR.inv k n h g g' d hgg hgg' hgd]
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hR.one_lt
  have hnu : (∏ i, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i))) = (q ^ 2) ^ (∑ i, eI i) := by
    rw [Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_pow_eq_pow_sum]
  rw [hnu, Nat.log_pow hq2]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) = ((q : ℂ) ^ (2 * k)) ^ (m * n) := by
    have hc : Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k
    have : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) = (q ^ (2 * k)) ^ (m * n) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ k) = _
      rw [Nat.card_fun, Nat.card_fun, hc]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [← pow_mul, mul_comm n m]
    rw [this]; push_cast; rfl
  rw [hM]
  have hc' : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
    rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [hc']
  simp only [fun i l => hsum i (e l) (he l) (hunit l), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_pow, Finset.prod_mul_distrib]
  rw [← pow_mul, ← pow_mul]
  congr 1
  have hx : ∀ x, (((ε : ℂ) / q) ^ eI x) ^ m = (((ε : ℂ) / q) ^ m) ^ eI x := fun x => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [hx]
  rw [Finset.prod_pow_eq_pow_sum]
end GlobalTheory.CompanionTheory.SiegLoc
