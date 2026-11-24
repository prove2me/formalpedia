-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.exists_lower_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:21.836257+00:00
-- url     : https://prove2.me/submissions/215cb57d-1ac1-4604-b09d-b3eb9e2eb09d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational
import Theorems.Thm_GlobalTheory_Reg_CellChange_minors_iff
import Theorems.Thm_GlobalTheory_Reg_CellChange_upper_inv
import Theorems.Thm_GlobalTheory_Reg_CellChange_upper_mul_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.CellChange
open Matrix
namespace GlobalTheory.Reg.CellChange
theorem _root_.solution {κ : Type} [Field κ] {n : ℕ} (A : Matrix (Fin n) (Fin n) κ) (hA : IsUnit A.det) :
    ∃ l : Matrix (Fin n) (Fin n) (RatFunc κ), (∀ i j : Fin n, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧
      ∀ k (hk : k ≤ n), IsUnit ((A.map (algebraMap κ (RatFunc κ)) * l).submatrix
        (Fin.castLE hk) (Fin.castLE hk)).det := by
  have key : ∀ M : Matrix (Fin n) (Fin n) (Polynomial κ),
      (∀ k (hk : k ≤ n), (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      ∀ k (hk : k ≤ n), IsUnit ((M.map (algebraMap _ (RatFunc κ))).submatrix
        (Fin.castLE hk) (Fin.castLE hk)).det := by
    intro M hM k hk
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (hM k hk)
  obtain ⟨l, b, h0, h1, hb, hu, h⟩ := (minors_iff _).1 (key (Matrix.charmatrix (-A⁻¹)) (fun k hk => by
    have : (Matrix.charmatrix (-A⁻¹)).submatrix (Fin.castLE hk) (Fin.castLE hk) =
        Matrix.charmatrix ((-A⁻¹).submatrix (Fin.castLE hk) (Fin.castLE hk)) := by
      ext i j : 2
      simp [Matrix.charmatrix_apply, Matrix.diagonal_apply]
    rw [this]
    exact (Matrix.charpoly_monic _).ne_zero))
  obtain ⟨u, c, hu0, hu1, hc, hcu, h'⟩ := (minors_iff _).1
    (key (1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C) (fun k hk h2 => by
      have h3 := congrArg (Polynomial.evalRingHom (0 : κ)) h2
      rw [RingHom.map_det, map_zero] at h3
      have : (Polynomial.evalRingHom (0 : κ)).mapMatrix ((1 + (Polynomial.X : Polynomial κ) •
          A.map Polynomial.C).submatrix (Fin.castLE hk) (Fin.castLE hk)) = 1 := by
        ext i j
        simp [Matrix.one_apply, apply_ite]
      rw [this, Matrix.det_one] at h3
      exact one_ne_zero h3))
  obtain ⟨hbi, hbu, hbb⟩ := upper_inv b hb hu
  refine ⟨l, h0, h1, (minors_iff _).2 ⟨u, c * b⁻¹, hu0, hu1, hc.mul hbi, upper_mul_diag _ _ hc hcu hbi hbu, ?_⟩⟩
  have e1 : A.map Polynomial.C * Matrix.charmatrix (-A⁻¹) = 1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C := by
    rw [Matrix.charmatrix, Matrix.mul_sub, map_neg, Matrix.mul_neg, RingHom.mapMatrix_apply, ← Matrix.map_mul,
      Matrix.mul_nonsing_inv _ hA, sub_neg_eq_add, add_comm, Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j : 2
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
  have e2 : A.map (algebraMap κ (RatFunc κ)) = (A.map Polynomial.C).map (algebraMap _ (RatFunc κ)) := by
    ext i j
    exact IsScalarTower.algebraMap_apply κ (Polynomial κ) (RatFunc κ) (A i j)
  rw [← Matrix.mul_assoc, ← h', ← e1, Matrix.map_mul, h, ← e2, Matrix.mul_assoc, Matrix.mul_assoc, hbb,
    Matrix.mul_one]
end GlobalTheory.Reg.CellChange
