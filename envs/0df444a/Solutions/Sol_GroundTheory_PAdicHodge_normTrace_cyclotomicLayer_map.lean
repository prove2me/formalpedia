-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_cyclotomicLayer_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:09.127949+00:00
-- url     : https://prove2.me/submissions/f16cfa2b-9b1e-4b10-932d-e0279f185894

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_map
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_map_of_map_eq


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
theorem _root_.solution (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) (n : ℕ) (y : PadicAlgCl p) :
    normTrace (cyclotomicLayer K n) (σ y) = σ (normTrace (cyclotomicLayer K n) y) :=
  normTrace_map_of_map_eq _ σ (cyclotomicLayer_map K σ hσ n) y
end GroundTheory.PAdicHodge
