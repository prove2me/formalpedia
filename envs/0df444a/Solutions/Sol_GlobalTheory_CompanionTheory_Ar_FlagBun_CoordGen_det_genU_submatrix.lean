-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.det_genU_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:32:59.112147+00:00
-- url     : https://prove2.me/submissions/23585335-e309-4723-97f3-692db843dedc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_det_mul_eq_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_map_mul_flagMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}
variable {E : Type} [AddCommGroup E] [Module Ω E] {n : S → ℕ}
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
theorem _root_.solution (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) {d : ℕ} (hd : d ≤ r s)
    (R : Fin d → Fin (r s)) :
    ((genU Ω r s).submatrix R (Fin.castLE hd)).det =
      ∑ f : Fin d → Fin (n s), (∏ i, algebraMap Ω (GenField Ω r) (B (R i) (f i))) *
        ((flagMat φ c s).submatrix f (Fin.castLE hd)).det := by
  classical
  have h : (genU Ω r s).submatrix R (Fin.castLE hd) =
      ((B.map (algebraMap Ω (GenField Ω r))).submatrix R id) *
        ((flagMat φ c s).submatrix id (Fin.castLE hd)) := by
    rw [← map_mul_flagMat φ c s B hB]
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul_eq_sum]
  simp [Matrix.submatrix_submatrix]
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
