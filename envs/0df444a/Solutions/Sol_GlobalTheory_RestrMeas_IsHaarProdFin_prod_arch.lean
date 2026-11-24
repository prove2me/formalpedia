-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsHaarProdFin.prod_arch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:31.668871+00:00
-- url     : https://prove2.me/submissions/12fb7479-e8b2-4644-878b-a1ad5eaebc87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
import Theorems.Thm_GlobalTheory_RestrMeas_isHaarProdFin_iff

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
omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, T2Space (Ya w)] [∀ v, IsTopologicalGroup (Yf v)]
  [∀ v, LocallyCompactSpace (Yf v)] [∀ v, SecondCountableTopology (Yf v)] [∀ v, BorelSpace (Yf v)]
namespace GlobalTheory.RestrMeas
namespace IsHaarProdFin
theorem _root_.solution {pf' : ∀ v, X' →* Yf v} {ν : Measure X'} (h : IsHaarProdFin pf' K μf ν)
    [ha : ∀ w, (μa w).IsHaarMeasure] (e : ((∀ w, Ya w) × X') ≃ₜ* X)
    (ea : ∀ w p, pa w (e p) = p.1 w) (ef : ∀ v p, pf v (e p) = pf' v p.2) :
    IsHaarProd pa pf K μa μf (((Measure.pi μa).prod ν).map e) := by
  obtain ⟨h2, h3, h4, h5⟩ := isHaarProdFin_iff.1 h
  refine ⟨ha, h2, e.isHaarMeasure_map _, h4, fun S hS A B hA hB => ?_⟩
  have e2 : e ⁻¹' cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B =
      univ.pi A ×ˢ {x | (∀ v ∈ S, pf' v x ∈ B v) ∧ ∀ v ∉ S, pf' v x ∈ K v} := by
    ext p
    simp [mem_cyl, ea, ef]
  rw [show ((Measure.pi μa).prod ν).map e = ((Measure.pi μa).prod ν).map e.toHomeomorph.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply]
  erw [e2]
  rw [Measure.prod_prod, h5 S hS B hB, Measure.pi_pi]
end IsHaarProdFin
end GlobalTheory.RestrMeas
