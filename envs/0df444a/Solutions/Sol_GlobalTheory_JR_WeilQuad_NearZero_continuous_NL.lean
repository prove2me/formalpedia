-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.NearZero.continuous_NL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:10:20.411788+00:00
-- url     : https://prove2.me/submissions/10901eac-ae02-4a28-8170-5d970c7546d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleTraceAddCharNormEqOneNearZero
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NearZero_finite_K_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NearZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad.NearZero
theorem _root_.solution [Unram F E] (A : Et F E) (hK : IsField A.K) :
    Continuous (fun y : A.L => A.NL y) := by
  letI : Field A.K := hK.toField
  have := finite_K_L A
  let b := Module.Free.chooseBasis A.K A.L
  have hfun : (fun y : A.L => A.NL y) = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [hfun]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  let φ : A.L →ₗ[A.K] A.K := (LinearMap.proj j : (_ → A.K) →ₗ[A.K] A.K) ∘ₗ
    (LinearMap.proj i : (_ → _ → A.K) →ₗ[A.K] _) ∘ₗ (Algebra.leftMulMatrix b).toLinearMap
  have hφ : Continuous (φ.restrictScalars F) := IsModuleTopology.continuous_of_linearMap _
  exact hφ
end GlobalTheory.JR.WeilQuad.NearZero
