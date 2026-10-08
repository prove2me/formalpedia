-- Prove2me | solution 1 for ModelRiskOT.PrimalOpt.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T02:19:56.027282+00:00
-- url     : https://prove2.me/submissions/f569db67-b407-4771-aba5-e393df1159da

import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ModelRiskOT_PrimalOpt_PrimalFeasibleMono

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace PrimalOptCodex
open ModelRiskOT.Duality

noncomputable def repairPair {S : Type*} (K : Set (S × S)) (p : S × S) : S × S := by
  classical
  exact if p ∈ K then p else (p.1,p.1)

lemma repairPair_first {S : Type*} (K : Set (S × S)) (p : S × S) :
    (repairPair K p).1 = p.1 := by
  classical
  by_cases h : p ∈ K <;> simp [repairPair,h]

lemma repairPair_aemeasurable {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (π : Measure (S × S))
    (K : Set (S × S)) (hK : NullMeasurableSet K π) : AEMeasurable (repairPair K) π := by
  classical
  have hn : NullMeasurable (repairPair K) π := by
    change @Measurable (NullMeasurableSpace (S × S) π) (S × S) inferInstance inferInstance _
    exact Measurable.ite hK measurable_id.nullMeasurable
      (measurable_fst.prodMk measurable_fst).nullMeasurable
  exact hn.aemeasurable

lemma repairPair_probability {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (π : Measure (S × S)) [IsProbabilityMeasure π]
    (K : Set (S × S)) (hK : NullMeasurableSet K π) :
    IsProbabilityMeasure (π.map (repairPair K)) :=
  Measure.isProbabilityMeasure_map (repairPair_aemeasurable π K hK)

lemma repairPair_first_marginal {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (π : Measure (S × S))
    (K : Set (S × S)) (hK : NullMeasurableSet K π) :
    (π.map (repairPair K)).map Prod.fst = π.map Prod.fst := by
  rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
    (repairPair_aemeasurable π K hK)]
  congr 1
  funext p
  exact repairPair_first K p

lemma repairPair_cost_le {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (π : Measure (S × S))
    (K : Set (S × S)) (hK : NullMeasurableSet K π)
    (c : S → S → ℝ) (hc : AssumptionA1 c) :
    (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂(π.map (repairPair K))) ≤
      ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π := by
  classical
  rw [lintegral_map' hc.lsc.measurable.ennreal_ofReal.aemeasurable
    (repairPair_aemeasurable π K hK)]
  apply lintegral_mono
  intro p
  by_cases h : p ∈ K
  · simp [repairPair,h]
  · simp [repairPair,h,(hc.eq_zero_iff p.1 p.1).mpr rfl]

lemma repairPair_good_mass {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (π : Measure (S × S))
    (K : Set (S × S)) (hK : NullMeasurableSet K π) :
    π K ≤ (π.map (repairPair K)) K := by
  classical
  apply (measure_mono (show K ⊆ repairPair K ⁻¹' K from ?_)).trans
    (Measure.le_map_apply (repairPair_aemeasurable π K hK) K)
  intro p hp
  simpa [repairPair,hp] using hp

lemma repairPair_event_loss {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (π : Measure (S × S))
    (K : Set (S × S)) (hK : NullMeasurableSet K π) (B : Set (S × S))
    (hB : MeasurableSet B) :
    π B ≤ (π.map (repairPair K)) B + π Kᶜ := by
  classical
  have hs : B ⊆ (repairPair K ⁻¹' B) ∪ Kᶜ := by
    intro p hp
    by_cases h : p ∈ K
    · exact Or.inl (by simpa [repairPair,h] using hp)
    · exact Or.inr h
  have h : π B ≤ π (repairPair K ⁻¹' B) + π Kᶜ :=
    (measure_mono hs).trans (measure_union_le _ _)
  rw [← Measure.map_apply_of_aemeasurable (repairPair_aemeasurable π K hK) hB] at h
  exact h

lemma repairPair_cost_zero_off {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (π : Measure (S × S))
    (K : Set (S × S)) (hK : NullMeasurableSet K π)
    (hK' : NullMeasurableSet K (π.map (repairPair K)))
    (c : S → S → ℝ) (hc : AssumptionA1 c) :
    (∫⁻ p in Kᶜ, ENNReal.ofReal (c p.1 p.2) ∂(π.map (repairPair K))) = 0 := by
  classical
  rw [← lintegral_indicator₀ hK'.compl]
  have hm := hc.lsc.measurable.ennreal_ofReal.aemeasurable.indicator₀ hK'.compl
  rw [lintegral_map' hm (repairPair_aemeasurable π K hK)]
  have he (p : S × S) : (Kᶜ.indicator (fun q ↦ ENNReal.ofReal (c q.1 q.2))) (repairPair K p) = 0 := by
    by_cases h : p ∈ K
    · simp [repairPair,h]
    · simp [repairPair,h,(hc.eq_zero_iff p.1 p.1).mpr rfl]
  simp_rw [he]
  simp

end PrimalOptCodex


set_option autoImplicit false
open MeasureTheory ModelRiskOT.Duality
namespace PrimalOptCodex

lemma extIntegral_mono {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → EReal) (hfg : f ≤ᵐ[μ] g) : extIntegral μ f ≤ extIntegral μ g := by
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (hfg.mono fun _ h ↦ EReal.toENNReal_le_toENNReal h))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (hfg.mono fun _ h ↦
        EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr h)))

lemma extIntegral_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (T : X → Y) (hT : Measurable T) (f : Y → EReal)
    (hf : AEMeasurable f (μ.map T)) :
    extIntegral (μ.map T) f = extIntegral μ (fun x ↦ f (T x)) := by
  unfold extIntegral
  rw [lintegral_map' (f := fun y ↦ (f y).toENNReal)
      (measurable_ereal_toENNReal.comp_aemeasurable hf) hT.aemeasurable,
    lintegral_map' (f := fun y ↦ (-f y).toENNReal)
      (measurable_ereal_toENNReal.comp_aemeasurable hf.neg) hT.aemeasurable]

end PrimalOptCodex


set_option autoImplicit false
open MeasureTheory ModelRiskOT.PrimalOpt ModelRiskOT.Duality
namespace PrimalOptCodex
theorem improving_plan_complete {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (f : S → ℝ) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA2 : AssumptionA2 f μ)
    (π : Measure (S × S)) (hπ : π ∈ ModelRiskOT.Duality.primalFeasible c μ δ) :
    ∃ π' ∈ primalFeasibleMono c f μ δ,
      ∫⁻ p, ENNReal.ofReal (f p.2) ∂π ≤ ∫⁻ p, ENNReal.ofReal (f p.2) ∂π' ∧
      ∫⁻ p, ENNReal.ofReal (-f p.2) ∂π' ≤ ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ∧
      ModelRiskOT.Duality.primalObj f π ≤ ModelRiskOT.Duality.primalObj f π' := by
  classical
  let K : Set (S × S) := {p | f p.1 ≤ f p.2}
  have hf : Measurable f := hA2.usc.measurable
  have hK : MeasurableSet K := measurableSet_le (hf.comp measurable_fst) (hf.comp measurable_snd)
  let R := repairPair K
  have hR : Measurable R := Measurable.ite hK measurable_id
    (measurable_fst.prodMk measurable_fst)
  have hpay (p : S × S) : f p.2 ≤ f (R p).2 := by
    by_cases hp : p ∈ K
    · simp [R,repairPair,hp]
    · have hh : f p.2 < f p.1 := lt_of_not_ge hp
      simpa [R,repairPair,hp] using hh.le
  have hfirst (p : S × S) : f p.1 ≤ f (R p).2 := by
    by_cases hp : p ∈ K
    · have hh : f p.1 ≤ f p.2 := hp
      simpa [R,repairPair,hp] using hh
    · simp [R,repairPair,hp]
  have hgood (p : S × S) : R p ∈ K := by
    change f (R p).1 ≤ f (R p).2
    rw [show (R p).1 = p.1 from repairPair_first K p]
    exact hfirst p
  let q := π.map R
  let : IsProbabilityMeasure π := hπ.1
  have hq : q ∈ ModelRiskOT.Duality.primalFeasible c μ δ := by
    refine ⟨repairPair_probability π K hK.nullMeasurableSet,?_,?_⟩
    · exact (repairPair_first_marginal π K hK.nullMeasurableSet).trans hπ.2.1
    · exact (repairPair_cost_le π K hK.nullMeasurableSet c hA1).trans hπ.2.2
  have hmass : q K = 1 := by
    change (π.map R) K = 1
    rw [Measure.map_apply hR hK]
    have he : R ⁻¹' K = Set.univ := by ext p; simp [hgood p]
    rw [he]
    simp
  refine ⟨q,⟨hq,hmass⟩,?_,?_,?_⟩
  · change (∫⁻ p, ENNReal.ofReal (f p.2) ∂π) ≤ ∫⁻ p, ENNReal.ofReal (f p.2) ∂(π.map R)
    rw [lintegral_map (show Measurable (fun p : S × S ↦ ENNReal.ofReal (f p.2)) from
      (hf.comp measurable_snd).ennreal_ofReal) hR]
    apply lintegral_mono
    intro p
    exact ENNReal.ofReal_le_ofReal (hpay p)
  · change (∫⁻ p, ENNReal.ofReal (-f p.2) ∂(π.map R)) ≤ _
    rw [lintegral_map (show Measurable (fun p : S × S ↦ ENNReal.ofReal (-f p.2)) from
      (hf.comp measurable_snd).neg.ennreal_ofReal) hR]
    calc
      _ ≤ ∫⁻ p, ENNReal.ofReal (-f p.1) ∂π := by
        apply lintegral_mono
        intro p
        exact ENNReal.ofReal_le_ofReal (neg_le_neg (hfirst p))
      _ = _ := by rw [← lintegral_map (show Measurable (fun x : S ↦ ENNReal.ofReal (-f x)) from
        hf.neg.ennreal_ofReal) measurable_fst,hπ.2.1]
  · change extIntegral π (fun p : S × S ↦ (f p.2 : EReal)) ≤
      extIntegral (π.map R) (fun p : S × S ↦ (f p.2 : EReal))
    rw [extIntegral_map π R hR (fun p : S × S ↦ (f p.2 : EReal))
      ((measurable_coe_real_ereal.comp (hf.comp measurable_snd)).aemeasurable)]
    apply extIntegral_mono
    exact Filter.Eventually.of_forall fun p ↦ EReal.coe_le_coe_iff.mpr (hpay p)


end PrimalOptCodex


set_option autoImplicit false
open MeasureTheory ModelRiskOT.PrimalOpt
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (f : S → ℝ) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA2 : AssumptionA2 f μ)
    (π : Measure (S × S)) (hπ : π ∈ ModelRiskOT.Duality.primalFeasible c μ δ) :
    ∃ π' ∈ primalFeasibleMono c f μ δ,
      ∫⁻ p, ENNReal.ofReal (f p.2) ∂π ≤ ∫⁻ p, ENNReal.ofReal (f p.2) ∂π' ∧
      ∫⁻ p, ENNReal.ofReal (-f p.2) ∂π' ≤ ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ∧
      ModelRiskOT.Duality.primalObj f π ≤ ModelRiskOT.Duality.primalObj f π' := by
  exact PrimalOptCodex.improving_plan_complete c f μ δ hδ hA1 hA2 π hπ

#print axioms solution
