-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.exists_minor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:51:06.449927+00:00
-- url     : https://prove2.me/submissions/057986d7-2ba6-41dd-ad11-4bba88c587d1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_genU_self
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_det_genU_rows
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_det_genU_submatrix

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
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) (k : Fin (r s)) :
    ∃ f : Fin ((k : ℕ) + 1) → Fin (n s), ((flagMat φ c s).submatrix f (Fin.castLE k.2)).det ≠ 0 := by
  by_contra hall
  push_neg at hall
  have h1 := det_genU_submatrix φ c s B hB k.2
    (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then k else Fin.castLE k.2 i)
  rw [det_genU_rows s k k le_rfl, genU_self, Finset.sum_eq_zero (fun f _ => by rw [hall f, mul_zero])] at h1
  exact one_ne_zero h1
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
