-- Prove2me | solution 1 for GlobalTheory.HermLat.isLatMod_top_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:29:11.926674+00:00
-- url     : https://prove2.me/submissions/5caa43c3-385d-4bfa-9686-73492b096d14

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism.HermitianLatticeCounting.S6
open GlobalTheory GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.HermLat
namespace _root_.GlobalTheory.HermLat
theorem _root_.solution (M : Submodule R V) :
    _root_.GlobalTheory.HermLat.IsLatMod M (⊤ : Submodule K V) ⊥ ↔ Submodule.IsLattice K M := by
  unfold _root_.GlobalTheory.HermLat.IsLatMod
  constructor
  · rintro ⟨⟨N, hN, rfl⟩, hs⟩
    simp only [_root_.GlobalTheory.HermLat.rs, Submodule.restrictScalars_bot, sup_bot_eq] at hs ⊢
    exact { fg := hN, span_eq_top := hs }
  · intro hM
    exact ⟨⟨M, hM.fg, by simp⟩, hM.span_eq_top⟩
end _root_.GlobalTheory.HermLat
end GlobalTheory.HermLat
