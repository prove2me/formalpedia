-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsHaarProd.prod_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:30.87774+00:00
-- url     : https://prove2.me/submissions/66f68536-33b4-4812-8ae7-80fd2276d070

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
namespace GlobalTheory.RestrMeas
namespace IsHaarProd
theorem _root_.solution {S : Finset V} {pa' : ∀ w, X' →* Ya w} {pf' : ∀ v : {v // v ∉ S}, X' →* Yf v}
    {ν : Measure X'} (h : IsHaarProd pa' pf' (fun v => K v) μa (fun v => μf v) ν) [hf : ∀ v, (μf v).IsHaarMeasure]
    (hK : ∀ v, IsOpen (K v : Set (Yf v))) (e : ((∀ v : S, Yf v) × X') ≃ₜ* X)
    (ea : ∀ w p, pa w (e p) = pa' w p.2) (eS : ∀ (v : S) p, pf v (e p) = p.1 v)
    (ef : ∀ (v : {v // v ∉ S}) p, pf v (e p) = pf' v p.2) :
    IsHaarProd pa pf K μa μf (((Measure.pi fun v : S => μf v).prod ν).map e) := by
  classical
  obtain ⟨h1, -, h3, h4⟩ := h
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually h4.1
  have hS' : ∀ T : Finset V, S ∪ S₀.map (Function.Embedding.subtype _) ⊆ T →
      ∀ v : {v // v ∉ S}, v.1 ∉ T → μf v (K v) = 1 := fun T hT v hv =>
    hS v fun h' => hv (hT (Finset.mem_union_right _ (Finset.mem_map_of_mem _ h')))
  refine ⟨h1, hf, e.isHaarMeasure_map _, isCylProd_of_large (fun v => (hK v).measurableSet)
    (S ∪ S₀.map (Function.Embedding.subtype _))
    (fun v hv => hS' _ le_rfl ⟨v, fun h' => hv (Finset.mem_union_left _ h')⟩ hv) (fun _ _ => rfl)
    fun T hT A B hA hB => ?_⟩
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  have e1 := h4.2 (T.subtype _) (fun v hv => hS' T hT v (by simpa using hv)) A (fun v => B v) hA
    fun v hv => hB v (by simpa using hv)
  have e2 : e ⁻¹' cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) T A B =
      (univ.pi fun v : S => B v) ×ˢ cyl (fun w => pa' w) (fun v => pf' v) (fun v => (K v : Set (Yf v)))
        (T.subtype _) A fun v => B v := by
    ext p
    simp only [mem_preimage, mem_cyl, mem_prod, mem_univ_pi, Finset.mem_subtype, ea, ← eS, ← ef]
    refine ⟨fun ⟨a, b, c⟩ => ⟨fun v => b v (hST v.2), a, fun v hv => b v hv, fun v hv => c v hv⟩,
      fun ⟨a, b, c, d⟩ => ⟨b, fun v hv => ?_, fun v hv => d ⟨v, fun h' => hv (hST h')⟩ hv⟩⟩
    by_cases h' : v ∈ S
    exacts [a ⟨v, h'⟩, c ⟨v, h'⟩ hv]
  rw [show ((Measure.pi fun v : S => μf v).prod ν).map e =
      ((Measure.pi fun v : S => μf v).prod ν).map e.toHomeomorph.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply]
  erw [e2]
  rw [Measure.prod_prod, e1, Measure.pi_pi, mul_left_comm, Finset.prod_coe_sort S fun v => μf v (B v),
    Finset.prod_subtype_eq_prod_filter fun v => μf v (B v), ← Finset.prod_filter_mul_prod_filter_not T (· ∈ S),
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hST]
end IsHaarProd
end GlobalTheory.RestrMeas
