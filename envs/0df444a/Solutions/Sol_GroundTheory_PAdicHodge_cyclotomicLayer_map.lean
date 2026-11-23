-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclotomicLayer_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:40.372825+00:00
-- url     : https://prove2.me/submissions/de615b5c-88b4-42e9-991f-cc7ae3fd77fc

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_map


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
theorem _root_.solution (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : ∀ x ∈ K, σ x = x)
    (n : ℕ) :
    (cyclotomicLayer K n).map (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) = cyclotomicLayer K n := by
  rw [cyclotomicLayer, IntermediateField.map_sup, cycl_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change σ y ∈ K
    rw [hσ y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, hσ x hx⟩
end GroundTheory.PAdicHodge
