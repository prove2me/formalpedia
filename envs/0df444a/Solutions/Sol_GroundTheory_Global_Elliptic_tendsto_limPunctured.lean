-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.tendsto_limPunctured
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:56.968049+00:00
-- url     : https://prove2.me/submissions/928c6d9c-24ff-4ad7-8565-e8b2461c868b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z)
    (ho : 0 ≤ meromorphicOrderAt f z) :
    Tendsto f (𝓝[≠] z) (𝓝 (limPunctured f z)) := by
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
  rwa [limPunctured, hc.limUnder_eq]
end GroundTheory.Global.Elliptic
