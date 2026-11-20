-- Prove2me | solution 1 for IsCadlag.not_accPt_largeLeftJumpSet
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:01:55.138255+00:00
-- url     : https://prove2.me/submissions/d3b65dd0-0f06-4f5d-9fa9-3ccb5fb39d68

import Definitions.Def_BrownianMotion_StochasticIntegral_Cadlag_F000

open Filter TopologicalSpace Bornology
open scoped Topology ENNReal

variable {ι E : Type*} [TopologicalSpace ι]

theorem AuxCad.leftLim_cases [LinearOrder ι] [OrderTopology ι] [TopologicalSpace E]
    (f : ι → E) (s : ι) :
    Function.leftLim f s = f s ∨ Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)) := by
  by_cases h1 : 𝓝[<] s = ⊥
  · exact Or.inl (leftLim_eq_of_eq_bot f h1)
  by_cases h2 : ∃ y, Tendsto f (𝓝[<] s) (𝓝 y)
  · right
    haveI : Nonempty E := ⟨f s⟩
    have ht : ‹TopologicalSpace ι› = Preorder.topology ι :=
      OrderTopology.topology_eq_generate_intervals
    have h2' := h2
    clear h2
    revert h1 h2'
    subst ht
    letI : TopologicalSpace ι := Preorder.topology ι
    intro h1 h2'
    have e : Function.leftLim f s = limUnder (𝓝[<] s) f := by
      simp only [Function.leftLim, h1, h2', not_true, or_self, if_false]
    rw [e]
    exact tendsto_nhds_limUnder h2'
  · exact Or.inl (leftLim_eq_of_not_tendsto f h2)

theorem _root_.solution [LinearOrder ι] [OrderTopology ι] [UniformSpace E]
    {f : ι → E} (hf : IsCadlag f) {v : Set (E × E)} (hv : v ∈ uniformity E) (t : ι) :
    ¬ AccPt t (𝓟 (largeLeftJumpSet f v)) := by
  obtain ⟨u, hu, huv⟩ := comp_mem_uniformity_sets hv
  obtain ⟨w, hw, hwc, hwsub⟩ := mem_uniformity_isClosed (Filter.inter_mem hu (symm_le_uniformity hu))
  -- core: on an open set I where f stays w-close to c, no large jumps
  have core : ∀ (c : E) (I : Set ι), IsOpen I → (∀ x ∈ I, (c, f x) ∈ w) →
      ∀ s ∈ I, s ∉ largeLeftJumpSet f v := by
    intro c I hI hc s hs hmem
    apply hmem
    rcases AuxCad.leftLim_cases f s with h | h
    · simp only [h]
      exact refl_mem_uniformity hv
    · have hcl : IsClosed {y | (c, y) ∈ w} :=
        hwc.preimage (Continuous.prodMk continuous_const continuous_id)
      have hev : ∀ᶠ x in 𝓝[<] s, f x ∈ {y | (c, y) ∈ w} :=
        Filter.mem_of_superset (nhdsWithin_le_nhds (hI.mem_nhds hs)) fun x hx => hc x hx
      have hL : (c, Function.leftLim f s) ∈ w := by
        by_cases hb : 𝓝[<] s = ⊥
        · have := leftLim_eq_of_eq_bot f hb
          rw [this]; exact hc s hs
        · haveI : (𝓝[<] s).NeBot := ⟨hb⟩
          exact hcl.mem_of_tendsto h hev
      have h1 : (f s, c) ∈ u := ((hwsub (hc s hs)).2 : _)
      have h2 : (c, Function.leftLim f s) ∈ u := (hwsub hL).1
      exact huv ⟨c, h1, h2⟩
  have hsplit : 𝓝[≠] t = 𝓝[<] t ⊔ 𝓝[>] t := by
    rw [← nhdsWithin_union, Set.Iio_union_Ioi]
  suffices key : (largeLeftJumpSet f v)ᶜ ∈ 𝓝[≠] t by
    intro hacc
    exact (show NeBot (𝓝[≠] t ⊓ 𝓟 (largeLeftJumpSet f v)) from hacc).ne
      (inf_principal_eq_bot.2 key)
  rw [hsplit, Filter.mem_sup]
  constructor
  · obtain ⟨l, hl⟩ := hf.left_limit t
    have hev : ∀ᶠ x in 𝓝[<] t, (l, f x) ∈ w := hl (mem_nhds_left l hw)
    by_cases hbot : ∃ a, a < t
    · obtain ⟨a, hat⟩ := hbot
      obtain ⟨b, hb, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hat).1 hev
      have hb' : Set.Ioo b t ∈ 𝓝[<] t := Ioo_mem_nhdsLT hb
      filter_upwards [hb'] with s hs
      exact core l (Set.Ioo b t) isOpen_Ioo (fun x hx => hsub hx) s hs
    · push Not at hbot
      have : 𝓝[<] t = ⊥ := by
        rw [← nhdsWithin_empty t]; congr 1; ext x; simp [hbot x]
      rw [this]; exact Filter.mem_bot
  · have hr : Tendsto f (𝓝[>] t) (𝓝 (f t)) :=
      (hf.right_continuous t).tendsto
    have hev : ∀ᶠ x in 𝓝[>] t, (f t, f x) ∈ w := hr (mem_nhds_left (f t) hw)
    by_cases htop : ∃ a, t < a
    · obtain ⟨a, hta⟩ := htop
      obtain ⟨b, hb, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hta).1 hev
      have hb' : Set.Ioo t b ∈ 𝓝[>] t := Ioo_mem_nhdsGT hb
      filter_upwards [hb'] with s hs
      exact core (f t) (Set.Ioo t b) isOpen_Ioo (fun x hx => hsub hx) s hs
    · push Not at htop
      have : 𝓝[>] t = ⊥ := by
        rw [← nhdsWithin_empty t]; congr 1; ext x; simp [htop x]
      rw [this]; exact Filter.mem_bot
