-- Prove2me | solution 1 for GlobalTheory.HermLat.mem_perp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:53:34.637817+00:00
-- url     : https://prove2.me/submissions/78782b22-21ce-4057-8029-b33a4ef59aab

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
theorem _root_.solution (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (S : Submodule K V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.perp H S ↔ ∀ x ∈ S, H.B y x = 0 := by
  simp [_root_.GlobalTheory.HermLat.perp, Submodule.mem_iInf]
end _root_.GlobalTheory.HermLat
end GlobalTheory.HermLat
