-- Prove2me | solution 1 for GroundTheory.Automorphic.contDiffAt_prodExpCoord_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:59.428854+00:00
-- url     : https://prove2.me/submissions/9ad9050c-44bb-4ff9-8954-592fd9e0f510

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_prodExpVal_zero
import Theorems.Thm_GroundTheory_Automorphic_contDiffOn_prodExpCoord
import Theorems.Thm_GroundTheory_Automorphic_isOpen_prodExpCoord_domain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffAt ℝ ∞ (prodExpCoord b) 0 :=
  (contDiffOn_prodExpCoord b).contDiffAt ((isOpen_prodExpCoord_domain b).mem_nhds
    (by simp [prodExpVal_zero, one_mem_expPartialHomeomorph_target]))
end GroundTheory.Automorphic
