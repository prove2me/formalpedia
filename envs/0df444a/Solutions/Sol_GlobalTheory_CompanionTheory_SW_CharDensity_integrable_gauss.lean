-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.integrable_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:47.576686+00:00
-- url     : https://prove2.me/submissions/9298175c-066a-4ff8-a185-5d29a12e49b5

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharDensity
open scoped FourierTransform
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.CharDensity
theorem _root_.solution {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V => Real.exp (-b * ‖x‖ ^ 2)) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V)
    (b := (b : ℂ)) (by simpa using hb) 0 0
  have h2 := h.norm
  refine h2.congr (Eventually.of_forall fun x => ?_)
  simp [Complex.norm_exp, ← Complex.ofReal_pow]
end GlobalTheory.CompanionTheory.SW.CharDensity
