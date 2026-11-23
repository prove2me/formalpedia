-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocInf.isOpen_posU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:32.982164+00:00
-- url     : https://prove2.me/submissions/99725ca2-0f22-452d-ae58-5939977b0b0e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInf_isOpen_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInf
namespace GlobalTheory.CompanionTheory.SW.LocInf
theorem _root_.solution (ι : Type) [Fintype ι] : IsOpen (posU ι : Set (ι → ℝ)ˣ) :=
  (isOpen_pos ι).preimage Units.continuous_val
end GlobalTheory.CompanionTheory.SW.LocInf
