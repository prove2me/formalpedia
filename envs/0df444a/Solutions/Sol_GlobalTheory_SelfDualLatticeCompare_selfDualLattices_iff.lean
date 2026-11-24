-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeCompare.selfDualLattices_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:01:40.839122+00:00
-- url     : https://prove2.me/submissions/c938d858-da94-4eb9-ac14-a0a401411b93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_unram_iff
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_isSDLat_iff
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_conclusion_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.SelfDualLatticeCompare
namespace GlobalTheory.SelfDualLatticeCompare
theorem _root_.solution :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.SelfDualLattices ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas := by
  refine forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun σ => forall_congr' fun h => forall_congr' fun M => forall_congr' fun J => ?_
  rw [imp.swap]
  refine forall_congr' fun _ => forall_congr' fun hJ => forall_congr' fun v => ?_
  refine imp_congr (unram_iff v) (forall_congr' fun L => ?_)
  exact imp_congr (isSDLat_iff σ J v L) (conclusion_iff σ J v h hJ L)
end GlobalTheory.SelfDualLatticeCompare
