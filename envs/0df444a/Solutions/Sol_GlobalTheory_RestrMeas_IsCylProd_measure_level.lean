-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsCylProd.measure_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:30.068164+00:00
-- url     : https://prove2.me/submissions/77594d00-94bb-46c5-959f-de149e62a70a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
import Theorems.Thm_GlobalTheory_RestrMeas_cyl_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type}
variable {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v} {K K' : ∀ v, Set (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}
namespace GlobalTheory.RestrMeas
namespace IsCylProd
theorem _root_.solution (h : IsCylProd pa pf K μa μf μ) (hK : ∀ v, MeasurableSet (K v))
    {A : ∀ w, Set (Ya w)} (hA : ∀ w, MeasurableSet (A w)) :
    μ {x | (∀ w, pa w x ∈ A w) ∧ ∀ v, pf v x ∈ K v} = (∏ w, μa w (A w)) * ∏ᶠ v, μf v (K v) := by
  obtain ⟨S, hS⟩ := exists_finset_of_eventually h.1
  rw [← cyl_self S, h.2 S hS A K hA fun v _ => hK v, finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  exact fun v hv => by_contra fun h' => hv (hS v h')
end IsCylProd
end GlobalTheory.RestrMeas
