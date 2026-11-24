-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsHaarProd.map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:25.439824+00:00
-- url     : https://prove2.me/submissions/0bf4b638-a1e6-44b2-855c-ef330548a0ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually

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
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}
variable [BorelSpace X] [∀ w, BorelSpace (Ya w)] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X]
variable [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)]
variable [∀ w, SecondCountableTopology (Ya w)] [∀ v, IsTopologicalGroup (Yf v)] [∀ v, LocallyCompactSpace (Yf v)]
  [∀ v, SecondCountableTopology (Yf v)]
variable {X' : Type} [Group X'] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] [IsTopologicalGroup X']
  [LocallyCompactSpace X'] [SecondCountableTopology X']
omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)] [∀ w, BorelSpace (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)] [∀ w, SecondCountableTopology (Ya w)]
  [∀ v, IsTopologicalGroup (Yf v)] [∀ v, LocallyCompactSpace (Yf v)] [∀ v, SecondCountableTopology (Yf v)]
  [∀ v, BorelSpace (Yf v)] [LocallyCompactSpace X'] [SecondCountableTopology X']
namespace GlobalTheory.RestrMeas
namespace IsHaarProd
theorem _root_.solution {pa' : ∀ w, X' →* Ya w} {pf' : ∀ v, X' →* Yf v} {ν : Measure X'}
    (h : IsHaarProd pa' pf' K μa μf ν) (e : X' ≃ₜ* X) (ea : ∀ w x, pa w (e x) = pa' w x)
    (ef : ∀ v x, pf v (e x) = pf' v x) : IsHaarProd pa pf K μa μf (ν.map e) :=
  haveI := h.2.2.1
  ⟨h.1, h.2.1, e.isHaarMeasure_map _, h.2.2.2.map e.toHomeomorph.toMeasurableEquiv ea ef⟩
end IsHaarProd
end GlobalTheory.RestrMeas
