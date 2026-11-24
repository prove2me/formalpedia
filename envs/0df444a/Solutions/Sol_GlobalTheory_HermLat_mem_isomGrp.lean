-- Prove2me | solution 1 for GlobalTheory.HermLat.mem_isomGrp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:53:38.070107+00:00
-- url     : https://prove2.me/submissions/3256ffd9-fdc8-4c1c-b747-2316e9e9987b

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
theorem _root_.solution (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (s : V ≃ₗ[K] V) :
    s ∈ _root_.GlobalTheory.HermLat.isomGrp H ↔ ∀ x y, H.B (s x) (s y) = H.B x y := by
  unfold _root_.GlobalTheory.HermLat.isomGrp _root_.Formalism.HermitianLatticesTheory.isom
  change (∀ x y : V, H.B.flip (s x) (s y) = H.B.flip x y) ↔ _
  simp only [LinearMap.flip_apply]
  exact forall_swap
end _root_.GlobalTheory.HermLat
end GlobalTheory.HermLat
