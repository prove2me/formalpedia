-- Prove2me | solution 1 for GlobalTheory.HolHom.differentiableAt_partial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:27:46.994433+00:00
-- url     : https://prove2.me/submissions/f154b3be-afa3-4458-9d49-0dba0d1cfede

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {S : Scheme.{0}} {G : Over S} {g : ℕ}
namespace GlobalTheory.HolHom
theorem _root_.solution {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [FiniteDimensional ℂ V] {F : P × V → ℂ} {s : Set (P × V)} (hs : IsOpen s) (hF : DifferentiableOn ℂ F s) {b : P}
    (hb : (b, 0) ∈ s) : DifferentiableAt ℂ (fun b => fderiv ℂ (fun z => F (b, z)) 0) b := by
  have h1 : DifferentiableAt ℂ (fderiv ℂ F) (b, 0) :=
    (SCV.differentiableOn_fderiv hs hF).differentiableAt (hs.mem_nhds hb)
  have h2 : DifferentiableAt ℂ (fun b : P => (fderiv ℂ F (b, 0)).comp (ContinuousLinearMap.inr ℂ P V)) b :=
    (h1.comp b (f := fun b : P => (b, (0 : V))) (by fun_prop)).clm_comp (differentiableAt_const _)
  refine h2.congr_of_eventuallyEq ?_
  have h3 : ContinuousAt (fun b : P => (b, (0 : V))) b := by fun_prop
  filter_upwards [h3.eventually (hs.mem_nhds hb)] with b' hb'
  exact ((hF.differentiableAt (hs.mem_nhds hb')).hasFDerivAt.comp 0 (hasFDerivAt_prodMk_right b' (0 : V))).fderiv
end GlobalTheory.HolHom
