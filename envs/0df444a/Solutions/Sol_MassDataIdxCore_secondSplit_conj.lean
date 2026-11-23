-- Prove2me | solution 1 for MassDataIdxCore.secondSplit_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:22.357402+00:00
-- url     : https://prove2.me/submissions/937a21e3-a9c9-40f5-9d63-a10db6ebcbfe

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
import Theorems.Thm_MassDataIdxCore_firstSplit_apply
import Theorems.Thm_MassDataIdxCore_secondSplit_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K)
variable {θ} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap)
include hs
namespace MassDataIdxCore
theorem _root_.solution (t : T) : t2 θ (s t) = t1 θ t := by
  rw [firstSplit_apply, secondSplit_apply, hs]
  rfl
end MassDataIdxCore
