-- Prove2me | solution 1 for GlobalTheory.PlaceExt.ext_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:13.820437+00:00
-- url     : https://prove2.me/submissions/61eb8ab5-e363-4783-8502-33cfa301bdb1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
import Theorems.Thm_GlobalTheory_PlaceExt_wt_eq_of_min
import Theorems.Thm_GlobalTheory_PlaceExt_le_val_pow_mul
import Theorems.Thm_GlobalTheory_PlaceExt_min_eq_of_le_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.PlaceExt
variable {L A : Type*} [Field L] [CommRing A]
variable (ι : L →+* A) (S : Subring A) (π : L) (w : AddValuation L (WithTop ℤ))
namespace GlobalTheory.PlaceExt
theorem _root_.solution (hw : 1 ≤ w π)
    (happ : ∀ (x : A) (m : ℕ), ∃ l, ∃ b ∈ S, x - ι l = ι π ^ m * b)
    (u u' : AddValuation A (WithTop ℤ)) (hu : ∀ l, u (ι l) = w l) (hu' : ∀ l, u' (ι l) = w l)
    (h0 : ∀ b ∈ S, 0 ≤ u b) (h0' : ∀ b ∈ S, 0 ≤ u' b) : u = u' := by
  apply AddValuation.ext
  intro x
  apply wt_eq_of_min
  intro m
  obtain ⟨l, b, hb, hx⟩ := happ x m
  rw [min_eq_of_le_sub u (y := ι l), min_eq_of_le_sub u' (y := ι l), hu, hu']
  · rw [hx]; exact le_val_pow_mul u' (by rwa [hu']) (h0' b hb) m
  · rw [hx]; exact le_val_pow_mul u (by rwa [hu]) (h0 b hb) m
end GlobalTheory.PlaceExt
