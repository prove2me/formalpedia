-- Prove2me | solution 1 for MassDataIdxCore.surjCore
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:31.52525+00:00
-- url     : https://prove2.me/submissions/b912dd20-dad5-4cb7-94fb-eb931360a5ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PairMatrixSecondSplit
import Theorems.Thm_MassDataIdxCore_cancel_l
import Theorems.Thm_MassDataIdxCore_tr_one
import Theorems.Thm_MassDataIdxCore_intV_iff
import Theorems.Thm_MassDataIdxCore_pairMatrix_firstSplit
import Theorems.Thm_MassDataIdxCore_pairMatrix_secondSplit
import Theorems.Thm_MassDataIdxCore_matrix_ext_split
import Theorems.Thm_MassDataIdxCore_firstSplit_apply
import Theorems.Thm_MassDataIdxCore_firstSplit_conj
import Theorems.Thm_MassDataIdxCore_firstSplit_mulVec
import Theorems.Thm_MassDataIdxCore_group_law_jacobian_eq
import Theorems.Thm_MassDataIdxCore_p_pinv
import Theorems.Thm_MassDataIdxCore_pinv_p
import Theorems.Thm_MassDataIdxCore_secondSplit_apply
import Theorems.Thm_MassDataIdxCore_secondSplit_conj
import Theorems.Thm_MassDataIdxCore_secondSplit_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
variable (θ : T ≃ₐ[K] K × K)
variable {θ} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap) (J : Matrix n n T) (P : GL n K)
include hs
namespace MassDataIdxCore
theorem _root_.solution (hJ : Formalism.UG.cT s J = J) (hJu : IsUnit J.det) : SurjCore O θ s J P := by
  intro A
  set Af := (A : Matrix n n O).map (algebraMap O K) with hAf
  set Afi := ((A⁻¹ : GL n O) : Matrix n n O).map (algebraMap O K) with hAfi
  have hAA : Af * Afi = 1 := by
    rw [hAf, hAfi, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hAiA : Afi * Af = 1 := by
    rw [hAf, hAfi, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hAint : IntM O Af := fun i j => ((A : Matrix n n O) i j).2
  have hAiint : IntM O Afi := fun i j => (((A⁻¹ : GL n O) : Matrix n n O) i j).2
  set J1 := J.map (t1 θ) with hJ1
  have hJ1u : IsUnit J1.det := by
    rw [hJ1]
    have h := RingHom.map_det (t1 θ) J
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]; exact hJu.map _
  set J1i := J1⁻¹
  have hJJ : J1 * J1i = 1 := Matrix.mul_nonsing_inv J1 hJ1u
  have hJiJ : J1i * J1 = 1 := Matrix.nonsing_inv_mul J1 hJ1u
  set Pm := (P : Matrix n n K)
  set Pi := ((P⁻¹ : GL n K) : Matrix n n K)
  have hPP : Pi * Pm = 1 := pinv_p P
  have hPP' : Pm * Pi = 1 := p_pinv P
  set g1 := Pm * Af * Pi
  set gi1 := Pm * Afi * Pi
  set g2 := J1iᵀ * gi1ᵀ * J1ᵀ
  set gi2 := J1iᵀ * g1ᵀ * J1ᵀ
  have c1 := cancel_l hPP; have c2 := cancel_l hPP'; have c3 := cancel_l hAA; have c4 := cancel_l hAiA
  have c5 := cancel_l hJJ; have c6 := cancel_l hJiJ
  have t1' := tr_one hPP; have t2' := tr_one hPP'; have t3' := tr_one hAA; have t4' := tr_one hAiA
  have t5' := tr_one hJJ; have t6' := tr_one hJiJ
  have c7 := cancel_l t1'; have c8 := cancel_l t2'; have c9 := cancel_l t3'; have c10 := cancel_l t4'
  have c11 := cancel_l t5'; have c12 := cancel_l t6'
  have hg : pm θ g1 g2 * pm θ gi1 gi2 = 1 := by
    apply matrix_ext_split θ
    · rw [Matrix.map_mul, pairMatrix_firstSplit, pairMatrix_firstSplit, Matrix.map_one _ (map_zero _) (map_one _)]
      simp only [g1, gi1, Matrix.mul_assoc, c1, c3, hPP', Matrix.one_mul]
    · rw [Matrix.map_mul, pairMatrix_secondSplit, pairMatrix_secondSplit, Matrix.map_one _ (map_zero _) (map_one _)]
      simp only [g2, gi2, g1, gi1, Matrix.transpose_mul, Matrix.mul_assoc, c1, c3, c7, c9, c12, c2, c4, c8, c10,
        c11, t1', t2', t3', t4', t5', t6', hPP, hPP', hAA, hAiA, hJJ, hJiJ, Matrix.mul_one]
  have hg' : pm θ gi1 gi2 * pm θ g1 g2 = 1 := by
    apply matrix_ext_split θ
    · rw [Matrix.map_mul, pairMatrix_firstSplit, pairMatrix_firstSplit, Matrix.map_one _ (map_zero _) (map_one _)]
      simp only [g1, gi1, Matrix.mul_assoc, c1, c4, hPP', Matrix.one_mul]
    · rw [Matrix.map_mul, pairMatrix_secondSplit, pairMatrix_secondSplit, Matrix.map_one _ (map_zero _) (map_one _)]
      simp only [g2, gi2, g1, gi1, Matrix.transpose_mul, Matrix.mul_assoc, c1, c3, c7, c9, c12, c2, c4, c8, c10,
        c11, t1', t2', t3', t4', t5', t6', hPP, hPP', hAA, hAiA, hJJ, hJiJ, Matrix.mul_one]
  let g : GL n T := ⟨pm θ g1 g2, pm θ gi1 gi2, hg, hg'⟩
  have hcT1 : (Formalism.UG.cT s (pm θ g1 g2)).map (t1 θ) = g2ᵀ := by
    ext i j; simp [Formalism.UG.cT, firstSplit_conj hs, pm, secondSplit_apply]
  have hcT2 : (Formalism.UG.cT s (pm θ g1 g2)).map (t2 θ) = g1ᵀ := by
    ext i j; simp [Formalism.UG.cT, secondSplit_conj hs, pm, firstSplit_apply]
  have hJ2 := group_law_jacobian_eq hs J hJ
  refine ⟨g, ?_, fun x => ?_, ?_⟩
  · show Formalism.UG.cT s (pm θ g1 g2) * J * pm θ g1 g2 = J
    apply matrix_ext_split θ
    · rw [Matrix.map_mul, Matrix.map_mul, hcT1, pairMatrix_firstSplit, ← hJ1]
      simp only [g2, g1, gi1, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, c1, c3, c7,
        c9, c12, c2, c4, c8, c10, c11, c5, c6, hPP, hPP', hAA, hAiA, hJJ, hJiJ, Matrix.mul_one]
    · rw [Matrix.map_mul, Matrix.map_mul, hcT2, pairMatrix_secondSplit, hJ2, ← hJ1]
      simp only [g2, g1, gi1, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, c1, c3, c7,
        c9, c12, c2, c4, c8, c10, c11, c5, c6, hPP, hPP', hAA, hAiA, hJJ, hJiJ, Matrix.mul_one]
  · have e1 : (fun i => t1 θ (((g : Matrix n n T) *ᵥ x) i)) = g1 *ᵥ fun j => t1 θ (x j) := by
      rw [firstSplit_mulVec]; show (pm θ g1 g2).map (t1 θ) *ᵥ _ = _; rw [pairMatrix_firstSplit]
    have e2 : (fun i => t2 θ (((g : Matrix n n T) *ᵥ x) i)) = g2 *ᵥ fun j => t2 θ (x j) := by
      rw [secondSplit_mulVec]; show (pm θ g1 g2).map (t2 θ) *ᵥ _ = _; rw [pairMatrix_secondSplit]
    have f1 : Pi * g1 = Af * Pi := by simp only [g1, Matrix.mul_assoc, c1]
    have f2 : (Pmᵀ * J1ᵀ) * g2 = Afiᵀ * (Pmᵀ * J1ᵀ) := by
      simp only [g2, gi1, Matrix.transpose_mul, Matrix.mul_assoc, c11, c12, c7, c8]
    show x ∈ Lat O θ J P ↔ (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P
    simp only [Lat, Set.mem_ofPred_eq]
    rw [e1, e2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hJ1]
    change _ ↔ IntV O ((Pi * g1) *ᵥ _) ∧ IntV O ((Pmᵀ * J1ᵀ * g2) *ᵥ _)
    have hti : IntM O Afiᵀ := fun i j => hAiint j i
    have htt : IntM O Afᵀ := fun i j => hAint j i
    rw [f1, f2, ← Matrix.mulVec_mulVec (M := Af) (N := Pi), ← Matrix.mulVec_mulVec (M := Afiᵀ) (N := Pmᵀ * J1ᵀ),
      intV_iff O hAint hAiint hAiA, intV_iff O hti htt t4']
  · show Pi * (pm θ g1 g2).map (t1 θ) * Pm = Af
    rw [pairMatrix_firstSplit]
    simp only [g1, Matrix.mul_assoc, c1, hPP, Matrix.mul_one]
end MassDataIdxCore
