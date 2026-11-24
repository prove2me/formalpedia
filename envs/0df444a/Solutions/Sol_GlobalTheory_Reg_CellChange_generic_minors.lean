-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.generic_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:54.064448+00:00
-- url     : https://prove2.me/submissions/068d7c11-9bf7-4e84-82da-a2e5e5ce52f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational
import Theorems.Thm_GlobalTheory_Reg_CellChange_exists_lower_minors
import Theorems.Thm_GlobalTheory_Reg_CellChange_lowM_map
import Theorems.Thm_GlobalTheory_Reg_CellChange_lowM_of_lower

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
theorem _root_.solution {κ T : Type} [Field κ] {r : T → ℕ} (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ)
    (hA : ∀ τ, IsUnit (A τ).det) (τ : T) (k : ℕ) (hk : k ≤ r τ) :
    (((A τ).map (algebraMap κ (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) *
      lowM MvPolynomial.X τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  choose l h0 h1 hm using fun τ => exists_lower_minors (A τ) (hA τ)
  intro h
  let φ : MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ →ₐ[κ] RatFunc κ :=
    MvPolynomial.aeval (fun v => l v.1 v.2.1.2 v.2.1.1)
  have h2 := congrArg φ.toRingHom h
  rw [RingHom.map_det, map_zero, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, lowM_map] at h2
  apply (hm τ k hk).ne_zero
  rw [← h2, ← lowM_of_lower l τ (h0 τ) (h1 τ)]
  congr 3
  · ext i j
    exact (φ.commutes _).symm
  · congr 1
    funext v
    simp [φ]
end GlobalTheory.Reg.CellChange
