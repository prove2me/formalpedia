-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.continuous_diagUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:33:46.286775+00:00
-- url     : https://prove2.me/submissions/7b69719e-ff95-4de4-b19d-3fad468699f8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionSiegel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
variable (n : ℕ)
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution :
    Continuous (diagUnits n : (Fin n → IdeleGroup K) → AdelicGLn.AdelicGL K n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp (continuous_apply i))
  · change Continuous fun d : Fin n → IdeleGroup K => diagonal fun i => (((d i)⁻¹ : IdeleGroup K) : 𝔸[K])
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp ((continuous_apply i).inv))
end GroundTheory.Automorphic.Reduction
