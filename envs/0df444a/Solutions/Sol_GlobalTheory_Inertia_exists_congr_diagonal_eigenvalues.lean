-- Prove2me | solution 1 for GlobalTheory.Inertia.exists_congr_diagonal_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:06.993462+00:00
-- url     : https://prove2.me/submissions/38090062-d779-4ab3-ae72-6fda33b28877

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    ∃ P : Matrix n n ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun k => (hG.eigenvalues k : ℂ) := by
  have h := hG.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  set U : Matrix n n ℂ := (hG.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hdet : U.det ≠ 0 := by
    have h1 : star U * U = 1 := Unitary.coe_star_mul_self _
    have h2 := congrArg det h1
    rw [det_mul, det_one] at h2
    exact right_ne_zero_of_mul_eq_one h2
  have hm : (U.map conj).det = conj U.det := (RingHom.map_det (starRingEnd ℂ) U).symm
  refine ⟨U.map conj, hm ▸ (map_ne_zero _).2 hdet, ?_⟩
  have h3 : (U.map conj).map conj = U := by
    ext a b
    simp
  rw [h3]
  exact h
end GlobalTheory.Inertia
