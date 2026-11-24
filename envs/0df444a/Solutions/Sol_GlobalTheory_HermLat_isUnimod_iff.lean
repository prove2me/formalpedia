-- Prove2me | solution 1 for GlobalTheory.HermLat.isUnimod_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:54:55.758805+00:00
-- url     : https://prove2.me/submissions/fb6c7689-8754-45b2-85bc-e69b718de6a6

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Theorems.Thm_GlobalTheory_HermLat_isLatMod_top_bot_iff
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
theorem _root_.solution (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (M : Submodule R V) :
    _root_.GlobalTheory.HermLat.IsUnimod H M ↔ Submodule.IsLattice K M ∧ _root_.Formalism.HermitianLatticesTheory.IsUnimodular H.B.flip M := by
  unfold _root_.GlobalTheory.HermLat.IsUnimod _root_.GlobalTheory.HermLat.IsUnimodMod
  rw [_root_.GlobalTheory.HermLat.isLatMod_top_bot_iff]
  unfold _root_.Formalism.HermitianLatticesTheory.IsUnimodular _root_.GlobalTheory.HermLat.dual
  constructor
  · rintro ⟨hM, hd⟩
    refine ⟨hM, ?_⟩
    rw [hM.span_eq_top] at hd
    simpa using hd
  · rintro ⟨hM, hd⟩
    refine ⟨hM, ?_⟩
    rw [hM.span_eq_top]
    simpa using hd
end _root_.GlobalTheory.HermLat
end GlobalTheory.HermLat
