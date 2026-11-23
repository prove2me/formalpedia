-- Prove2me | solution 1 for GroundTheory.Automorphic.contDiffOn_prodExpCoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:36.713875+00:00
-- url     : https://prove2.me/submissions/91a28687-0ba8-485c-b609-16602e8136e0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_contDiff_prodExpVal
import Theorems.Thm_GroundTheory_Automorphic_contDiffOn_logCoord

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
    ContDiffOn ℝ ∞ (prodExpCoord b)
      {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} :=
  (contDiffOn_logCoord b).comp (contDiff_prodExpVal _).contDiffOn (fun _ ht => ht)
end GroundTheory.Automorphic
