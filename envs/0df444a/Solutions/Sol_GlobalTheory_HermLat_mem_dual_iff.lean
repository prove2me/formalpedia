-- Prove2me | solution 1 for GlobalTheory.HermLat.mem_dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:14:58.662482+00:00
-- url     : https://prove2.me/submissions/559eced7-4515-4191-8785-4cd267e046cf

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
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
theorem _root_.solution (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (M : Submodule R V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.dual H M ↔
      y ∈ Submodule.span K (M : Set V) ∧ ∀ x ∈ M, H.B y x ∈ (1 : Submodule R K) := by
  simp only [_root_.GlobalTheory.HermLat.dual, _root_.GlobalTheory.HermLat.rs, Submodule.mem_inf,
    Submodule.restrictScalars_mem, _root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual, LinearMap.flip_apply]
end _root_.GlobalTheory.HermLat
end GlobalTheory.HermLat
