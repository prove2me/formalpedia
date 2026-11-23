-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PureH.map_consTup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:06.826347+00:00
-- url     : https://prove2.me/submissions/01b57d10-c9ea-4d7a-988f-a3453ea7a336

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
theorem _root_.solution {K L : Type} [Zero K] [One K] [Zero L] [One L] (f : K → L) (h0 : f 0 = 0)
    (h1 : f 1 = 1) {M n : ℕ} (X : Fin n → Fin M → K) :
    (fun a i => f (consTup X a i)) = consTup (fun a i => f (X a i)) := by
  funext a i
  induction a using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simp [consTup, h1]
    | succ i => simp [consTup, h0]
  | succ a =>
    induction i using Fin.cases with
    | zero => simp [consTup, h0]
    | succ i => simp [consTup]
end GlobalTheory.CompanionTheory.SW.PureH
