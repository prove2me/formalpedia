-- Prove2me | solution 1 for OAI.DimensionTen.main_pair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T11:00:56.443983+00:00
-- url     : https://prove2.me/submissions/91686d55-159a-475f-88ba-ba77b152fd27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DimensionTenPair
import Theorems.Thm_OAI_DimensionTen_not_entanglementBreaking_of_range_criterion
import Theorems.Thm_OAI_DimensionTen_phiOne_ppt
import Theorems.Thm_OAI_DimensionTen_phiTwo_ppt
import Theorems.Thm_OAI_DimensionTen_compositeChoi_ne_zero
import Theorems.Thm_OAI_DimensionTen_compositeChoi_range_criterion

open Matrix Complex
open scoped Matrix ComplexOrder
open OAI.DimensionTen

theorem solution :
    ∃ Φ₁ Φ₂ : Mat 10 → Mat 10,
      Φ₁ = phiOne ∧ Φ₂ = phiTwo ∧ PPT Φ₁ ∧ PPT Φ₂ ∧
      (let Z := choi (Φ₂ ∘ Φ₁)
       Z ≠ 0 ∧
       (∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
         Z *ᵥ w = productVector u v → u = 0 ∨ v = 0) ∧
       ¬ EntanglementBreaking (Φ₂ ∘ Φ₁)) := by
  refine ⟨phiOne, phiTwo, rfl, rfl, phiOne_ppt, phiTwo_ppt, ?_⟩
  refine ⟨compositeChoi_ne_zero, compositeChoi_range_criterion, ?_⟩
  exact not_entanglementBreaking_of_range_criterion (phiTwo ∘ phiOne)
    compositeChoi_ne_zero compositeChoi_range_criterion
