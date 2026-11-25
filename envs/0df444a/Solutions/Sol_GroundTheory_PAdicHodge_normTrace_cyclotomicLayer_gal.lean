-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_cyclotomicLayer_gal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:30.381798+00:00
-- url     : https://prove2.me/submissions/db83b9a9-6c59-4847-8810-3d259748f7de

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cyclotomicLayer_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
omit [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    normTrace (cyclotomicLayer K n) (σ y) = σ (normTrace (cyclotomicLayer K n) y) :=
  normTrace_cyclotomicLayer_map K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) n y
end GroundTheory.PAdicHodge
