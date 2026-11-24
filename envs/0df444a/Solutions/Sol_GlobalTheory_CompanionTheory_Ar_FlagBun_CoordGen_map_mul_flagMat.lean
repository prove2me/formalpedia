-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.map_mul_flagMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:27.947886+00:00
-- url     : https://prove2.me/submissions/68a7cfad-f49b-4053-8a8b-a69f6da6dc7b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios

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
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) :
    B.map (algebraMap Ω (GenField Ω r)) * flagMat φ c s = genU Ω r s := by
  have h : Matrix.of (fun j l => algebraMap Ω (GenField Ω r) (φ s j (c s l))) =
      (Matrix.of (fun j l => φ s j (c s l))).map (algebraMap Ω (GenField Ω r)) := by
    ext j l
    simp
  rw [flagMat, h, ← Matrix.mul_assoc, ← Matrix.map_mul, hB]
  simp
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
