-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.image_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:56:15.529583+00:00
-- url     : https://prove2.me/submissions/d664ce39-9537-476a-821d-d43bf7658f64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution (f : ℕ → W) (N m : ℕ) :
    (fun i : Fin N => f i) '' {a : Fin N | m ≤ (a : ℕ)} = f '' {a | m ≤ a ∧ a < N} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ⟨ha, a.2⟩, rfl⟩
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨a, h2⟩, h1, rfl⟩
end GlobalTheory.FlagPts.SphericalEisensteinCover
