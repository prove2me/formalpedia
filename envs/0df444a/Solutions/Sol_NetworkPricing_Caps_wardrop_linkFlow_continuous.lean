-- Prove2me | solution 1 for NetworkPricing.Caps.wardrop_linkFlow_continuous
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:03:36.266093+00:00
-- url     : https://prove2.me/submissions/d7604eaf-6de9-418e-a181-d45aa93cc943

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model

open KellyStochasticNetworks NetworkPricing.Caps
open Filter Topology Set

theorem solution {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t)) :
    ∀ e : Fin J, ContinuousOn (fun t : Fin J → ℝ => linkFlow I.A (flow t) e) {t | 0 ≤ t} := by
  obtain ⟨hA, hr, hanti, hcont, hu0, hmono, hconv, hdiff, hl0⟩ := hI
  have hlfc : Continuous (fun f : Fin R → ℝ => linkFlow I.A f) := by
    unfold linkFlow
    exact continuous_pi fun e => continuous_finset_sum _ fun q _ =>
      continuous_const.mul (continuous_apply q)
  have hdemc : ∀ k, Continuous (fun f : Fin R → ℝ => I.demand f k) := by
    intro k
    unfold Instance.demand
    exact continuous_finset_sum _ fun q _ => continuous_apply q
  -- feasible flows lie in a box
  let B : Fin R → ℝ := fun q => I.r (I.com q)
  have hbox : ∀ f, I.Feasible f → f ∈ Icc 0 B := by
    intro f hf
    refine ⟨fun q => hf.1 q, fun q => ?_⟩
    have h1 : f q ≤ I.demand f (I.com q) := by
      unfold Instance.demand
      exact Finset.single_le_sum (f := f) (fun q' _ => hf.1 q')
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    exact h1.trans (hf.2 _)
  have h0feas : I.Feasible 0 := by
    refine ⟨fun q => le_rfl, fun k => ?_⟩
    simp [Instance.demand, hr k]
  -- the potential, rewritten
  have hpot : ∀ t f, I.potential t f = ∑ k, I.U k (I.demand f k)
      - ∑ e, ((∫ y in (0:ℝ)..(linkFlow I.A f e), I.ℓ e y) + linkFlow I.A f e * t e) := by
    intro t f
    unfold Instance.potential
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [intervalIntegral.integral_add ((hdiff e).continuous.intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  -- continuity of U_k on [0, r_k]
  have hUc : ∀ k, ContinuousOn (I.U k) (Icc 0 (I.r k)) := by
    intro k
    have h := intervalIntegral.continuousOn_primitive_interval' (μ := MeasureTheory.volume)
      (b₁ := 0) (b₂ := I.r k) (a := 0)
      ((hcont k).mono (by rw [uIcc_of_le (hr k)])).intervalIntegrable
      (by rw [uIcc_of_le (hr k)]; exact ⟨le_rfl, hr k⟩)
    rw [uIcc_of_le (hr k)] at h
    exact h
  have hLc : ∀ e, Continuous (fun a : ℝ => ∫ y in (0:ℝ)..a, I.ℓ e y) := by
    intro e
    exact intervalIntegral.continuous_primitive
      (fun a b => (hdiff e).continuous.intervalIntegrable a b) 0
  -- joint continuity of the potential along sequences of feasible flows
  have hpt : ∀ (tn : ℕ → Fin J → ℝ) (fn : ℕ → Fin R → ℝ) (t0 : Fin J → ℝ) (g : Fin R → ℝ),
      Tendsto tn atTop (𝓝 t0) → Tendsto fn atTop (𝓝 g) → (∀ᶠ n in atTop, I.Feasible (fn n)) →
      Tendsto (fun n => I.potential (tn n) (fn n)) atTop (𝓝 (I.potential t0 g)) := by
    intro tn fn t0 g htn hfn hfeas
    simp only [hpot]
    have hlf : Tendsto (fun n => linkFlow I.A (fn n)) atTop (𝓝 (linkFlow I.A g)) :=
      (hlfc.tendsto g).comp hfn
    apply Tendsto.sub
    · apply tendsto_finsetSum
      intro k _
      have hd : Tendsto (fun n => I.demand (fn n) k) atTop (𝓝 (I.demand g k)) :=
        ((hdemc k).tendsto g).comp hfn
      have hmem : ∀ᶠ n in atTop, I.demand (fn n) k ∈ Icc 0 (I.r k) := by
        filter_upwards [hfeas] with n hn
        exact ⟨Finset.sum_nonneg (fun q _ => hn.1 q), hn.2 k⟩
      have hgmem : I.demand g k ∈ Icc 0 (I.r k) :=
        isClosed_Icc.mem_of_tendsto hd hmem
      exact ((hUc k) _ hgmem).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hd, hmem⟩)
    · apply tendsto_finsetSum
      intro e _
      have hle : Tendsto (fun n => linkFlow I.A (fn n) e) atTop (𝓝 (linkFlow I.A g e)) :=
        ((continuous_apply e).tendsto _).comp hlf
      have hte : Tendsto (fun n => tn n e) atTop (𝓝 (t0 e)) :=
        ((continuous_apply e).tendsto _).comp htn
      exact (((hLc e).tendsto _).comp hle).add (hle.mul hte)
  -- closedness of the Wardrop correspondence
  have hclosed : ∀ (tn : ℕ → Fin J → ℝ) (fn : ℕ → Fin R → ℝ) (t0 : Fin J → ℝ) (g : Fin R → ℝ),
      Tendsto tn atTop (𝓝 t0) → Tendsto fn atTop (𝓝 g) →
      (∀ᶠ n in atTop, I.IsWardropFlow (tn n) (fn n)) → I.IsWardropFlow t0 g := by
    intro tn fn t0 g htn hfn hW
    have hfeas : ∀ᶠ n in atTop, I.Feasible (fn n) := hW.mono fun n hn => hn.1
    have hgf : I.Feasible g := by
      refine ⟨fun q => ?_, fun k => ?_⟩
      · exact ge_of_tendsto (((continuous_apply q).tendsto g).comp hfn)
          (hfeas.mono fun n hn => hn.1 q)
      · exact le_of_tendsto (((hdemc k).tendsto g).comp hfn) (hfeas.mono fun n hn => hn.2 k)
    refine ⟨hgf, fun h hh => ?_⟩
    have h1 := hpt tn (fun _ => h) t0 h htn tendsto_const_nhds (Eventually.of_forall fun _ => hh)
    have h2 := hpt tn fn t0 g htn hfn hfeas
    exact le_of_tendsto_of_tendsto h1 h2 (hW.mono fun n hn => hn.2 h hh)
  intro e t0 ht0
  have main : Tendsto (fun t => linkFlow I.A (flow t)) (𝓝[{t : Fin J → ℝ | 0 ≤ t}] t0)
      (𝓝 (linkFlow I.A (flow t0))) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    classical
    let z : ℕ → Fin R → ℝ := fun n => if 0 ≤ ns n then flow (ns n) else 0
    have hz : ∀ n, z n ∈ Icc 0 B := by
      intro n
      by_cases h : 0 ≤ ns n
      · simp only [z, if_pos h]; exact hbox _ (hflow _ h).1
      · simp only [z, if_neg h]; exact hbox _ h0feas
    obtain ⟨g, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hz
    refine ⟨φ, ?_⟩
    have hns' : Tendsto ns atTop (𝓝 t0) := tendsto_nhdsWithin_iff.mp hns |>.1
    have hin : ∀ᶠ n in atTop, 0 ≤ ns n := tendsto_nhdsWithin_iff.mp hns |>.2
    have hin' : ∀ᶠ n in atTop, 0 ≤ ns (φ n) := hφ.tendsto_atTop.eventually hin
    have heq : ∀ᶠ n in atTop, z (φ n) = flow (ns (φ n)) := by
      filter_upwards [hin'] with n hn
      simp only [z, if_pos hn]
    have hW : I.IsWardropFlow t0 g := by
      refine hclosed (ns ∘ φ) (z ∘ φ) t0 g (hns'.comp hφ.tendsto_atTop) hlim ?_
      filter_upwards [hin', heq] with n hn hn'
      simp only [Function.comp, hn']
      exact hflow _ hn
    have hg : linkFlow I.A g = linkFlow I.A (flow t0) := hU t0 ht0 g (flow t0) hW (hflow t0 ht0)
    rw [← hg]
    refine ((hlfc.tendsto g).comp hlim).congr' ?_
    filter_upwards [heq] with n hn
    simp only [Function.comp, hn]
  exact ((continuous_apply e).tendsto _).comp main
