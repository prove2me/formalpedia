-- Prove2me | solution 1 for MazurRapoportAppendix.SpecialFibreComponentTable.mem_range_intersectionAlpha_iff_comp_of_inter_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/261042d1-cdf0-5d00-a135-8575c361b60a

import Mathlib
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MazurRapoportAppendix_SpecialFibreComponentTable_mem_range_intersectionAlpha_iff_comp_of_inter_equiv

set_option autoImplicit false

open MazurRapoportAppendix
open scoped BigOperators

theorem solution
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (t : SpecialFibreComponentTable ι) (t' : SpecialFibreComponentTable ι') (Φ : ι ≃ ι')
    (hΦ : ∀ a b, t'.inter (Φ a) (Φ b) = t.inter a b) (f : ι' → ℤ) :
    f ∈ (intersectionAlpha t').range ↔ (f ∘ Φ) ∈ (intersectionAlpha t).range := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c ∘ Φ, ?_⟩
    funext j
    simp only [intersectionAlpha_apply, Function.comp_apply]
    rw [← Φ.sum_comp (fun i' => c i' * t'.inter i' (Φ j))]
    exact Finset.sum_congr rfl fun i _ => by rw [hΦ]
  · rintro ⟨c, hc⟩
    refine ⟨c ∘ Φ.symm, ?_⟩
    funext j'
    have h := congrFun hc (Φ.symm j')
    simp only [intersectionAlpha_apply, Function.comp_apply, Equiv.apply_symm_apply] at h ⊢
    rw [← h, ← Φ.sum_comp (fun i' => c (Φ.symm i') * t'.inter i' j')]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Equiv.symm_apply_apply, ← hΦ i (Φ.symm j'), Equiv.apply_symm_apply]

end S_MazurRapoportAppendix_SpecialFibreComponentTable_mem_range_intersectionAlpha_iff_comp_of_inter_equiv
end P2MW
export P2MW.S_MazurRapoportAppendix_SpecialFibreComponentTable_mem_range_intersectionAlpha_iff_comp_of_inter_equiv (solution)
