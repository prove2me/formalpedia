-- Prove2me | solution 1 for GlobalTheory.PlaceRestrict.exists_orders
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:06:37.856446+00:00
-- url     : https://prove2.me/submissions/f3db1dc7-99e4-4ff6-a6a0-452f488b87c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_ne_zero_of_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_weak_approx_orders


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.PlaceRestrict
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
namespace GlobalTheory.PlaceRestrict
theorem _root_.solution {Ω X : Type} [Field Ω] (S : Set X) (hS : S.Finite)
    (v : X → AddValuation Ω (WithTop ℤ)) (hinj : Set.InjOn v S)
    (hn : ∀ w ∈ S, IsNormDiscrete (v w)) (n : X → ℤ) :
    ∃ g : Ω, g ≠ 0 ∧ ∀ w ∈ S, v w g = n w := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨w0, hw0⟩
  · exact ⟨1, one_ne_zero, by simp⟩
  haveI := hS.fintype
  let e := (Fintype.equivFin S).symm
  obtain ⟨g, hg⟩ := weak_approx_orders (fun i => v (e i)) (fun i => (hn _ (e i).2).1)
    (fun i => (hn _ (e i).2).2)
    (fun i j hij h => hij (e.injective (Subtype.ext (hinj (e i).2 (e j).2 h)))) (fun i => n (e i))
  have hg' : ∀ w ∈ S, v w g = n w := fun w hw => by
    have := hg (e.symm ⟨w, hw⟩)
    simpa using this
  exact ⟨g, wa_ne_zero_of_coe _ (hg' w0 hw0), hg'⟩
end GlobalTheory.PlaceRestrict
