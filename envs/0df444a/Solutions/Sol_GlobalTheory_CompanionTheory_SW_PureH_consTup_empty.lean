-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PureH.consTup_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:46.527427+00:00
-- url     : https://prove2.me/submissions/9ebf5c1e-7c9e-46a4-90d3-512e8466cf37

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PureH
namespace GlobalTheory.CompanionTheory.SW.PureH
theorem _root_.solution {K : Type} [Zero K] [One K] {M : ℕ} (X : Fin 0 → Fin M → K) :
    (consTup X : Fin (0 + 1) → Fin (M + 1) → K) = fun _ : Fin 1 => Fin.cons 1 (fun _ => 0) := by
  funext a
  induction a using Fin.cases with
  | zero => simp [consTup]
  | succ a => exact a.elim0
end GlobalTheory.CompanionTheory.SW.PureH
