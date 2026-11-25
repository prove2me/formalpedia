-- Prove2me | solution 1 for GlobalTheory.HermLat.isIntegralLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:14.754039+00:00
-- url     : https://prove2.me/submissions/1b4863c2-3e9a-4d5c-94a3-b2e35b1c139c

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
theorem _root_.solution (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (M : Submodule R V) :
    _root_.GlobalTheory.HermLat.IsIntegralLat H M ↔ ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule R K) := by
  unfold _root_.GlobalTheory.HermLat.IsIntegralLat _root_.Formalism.HermitianLatticesTheory.IsIntegralLat
  simp only [LinearMap.flip_apply]
  exact ⟨fun h x hx y hy => h y hy x hx, fun h x hx y hy => h y hy x hx⟩
end _root_.GlobalTheory.HermLat
end GlobalTheory.HermLat
