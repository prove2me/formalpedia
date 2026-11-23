-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.InfScale.eInf_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:27.057534+00:00
-- url     : https://prove2.me/submissions/80e53949-dbe2-4eb0-8487-5e22e34a7f3e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.InfScale
open GlobalTheory.CompanionTheory.SW.LocInf
namespace GlobalTheory.CompanionTheory.Equi.InfScale
theorem _root_.solution {F : Type} [Field F] [NumberField F] (h : IsTotallyReal F) (θ : ℝ →+* Ainf F) (t : ℝ)
    (w : InfinitePlace F) : eInf F h (θ t) w = t := by
  have key : ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
      ((eInf F h).toRingHom.comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  exact congrArg (fun f : ℝ →+* ℝ => f t) key
end GlobalTheory.CompanionTheory.Equi.InfScale
