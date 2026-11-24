-- Prove2me | solution 1 for GlobalTheory.SBProd.exists_sum_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:31.00452+00:00
-- url     : https://prove2.me/submissions/eebe833e-ceda-4c70-88e2-09501bc99dc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzProductDecomposition
import Theorems.Thm_GlobalTheory_SBProd_exists_compact_clopen_nhd
import Theorems.Thm_GlobalTheory_SBProd_isLocallyConstant_filter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.SBProd
namespace GlobalTheory.SBProd
theorem _root_.solution (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (κ κ' : Type) [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → X) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (κ ⊕ κ' → X)) :
    ∃ (ι : Type) (_ : Fintype ι) (g₁ : ι → (κ → X) → ℂ) (g₂ : ι → (κ' → X) → ℂ),
      (∀ i, g₁ i ∈ GlobalTheory.WeilM.SB (κ → X)) ∧ (∀ i, g₂ i ∈ GlobalTheory.WeilM.SB (κ' → X)) ∧
      g = ∑ i, fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr) := by
  obtain ⟨hlc, hcs⟩ := hg
  let e : (κ ⊕ κ' → X) ≃ₜ (κ → X) × (κ' → X) := Homeomorph.sumArrowHomeomorphProdArrow
  let h : (κ → X) × (κ' → X) → ℂ := g ∘ e.symm
  have hgh : ∀ z, g z = h (z ∘ Sum.inl, z ∘ Sum.inr) := fun z => by
    have : (z ∘ Sum.inl, z ∘ Sum.inr) = e z := rfl
    simp [h, this]
  have hlc' : IsLocallyConstant h := hlc.comp_continuous e.symm.continuous
  have hcs' : HasCompactSupport h := hcs.comp_homeomorph e.symm
  have key : ∀ p : (κ → X) × (κ' → X), ∃ U : Set (κ → X), ∃ V : Set (κ' → X), IsClopen U ∧ IsCompact U ∧
      IsClopen V ∧ IsCompact V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧ ∀ a ∈ U, ∀ b ∈ V, h (a, b) = h p := by
    rintro ⟨a₀, b₀⟩
    obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ :=
      isOpen_prod_iff.1 (hlc'.isOpen_fiber (h (a₀, b₀))) a₀ b₀ rfl
    obtain ⟨U, hU, hUc, haU, hUu⟩ := exists_compact_clopen_nhd hu hpu
    obtain ⟨V, hV, hVc, hbV, hVv⟩ := exists_compact_clopen_nhd hv hpv
    exact ⟨U, V, hU, hUc, hV, hVc, haU, hbV, fun a ha b hb => huv (mk_mem_prod (hUu ha) (hVv hb))⟩
  choose U V hU hUc hV hVc hpU hpV hconst using key
  obtain ⟨F, hF⟩ := hcs'.isCompact.elim_finite_subcover (fun p => U p ×ˢ V p)
    (fun p => (hU p).isOpen.prod (hV p).isOpen) (fun q _ => mem_iUnion.2 ⟨q, hpU q, hpV q⟩)
  let σ : (κ → X) → Finset F := fun a => Finset.univ.filter (fun i : F => a ∈ U i)
  let τ : (κ' → X) → Finset F := fun b => Finset.univ.filter (fun i : F => b ∈ V i)
  have hσ : IsLocallyConstant σ := isLocallyConstant_filter _ (fun i : F => U i) fun i => hU i
  have hτ : IsLocallyConstant τ := isLocallyConstant_filter _ (fun i : F => V i) fun i => hV i
  let c : Finset F → Finset F → ℂ := fun S T =>
    if hx : (S ∩ T).Nonempty then h (hx.choose : (κ → X) × (κ' → X)) else 0
  refine ⟨Finset F × Finset F, inferInstance,
    fun x a => if σ a = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0,
    fun x b => if τ b = x.2 ∧ x.2.Nonempty then 1 else 0, ?_, ?_, ?_⟩
  · intro x
    refine ⟨hσ.comp fun s => if s = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0, ?_⟩
    by_cases hx : x.1.Nonempty
    · obtain ⟨i, hi⟩ := hx
      refine HasCompactSupport.intro (hUc i) fun a ha => if_neg fun hs => ha ?_
      rw [← hs.1] at hi
      simpa [σ] using hi
    · exact HasCompactSupport.intro isCompact_empty fun a _ => if_neg fun hs => hx hs.2
  · intro x
    refine ⟨hτ.comp fun s => if s = x.2 ∧ x.2.Nonempty then (1 : ℂ) else 0, ?_⟩
    by_cases hx : x.2.Nonempty
    · obtain ⟨i, hi⟩ := hx
      refine HasCompactSupport.intro (hVc i) fun b hb => if_neg fun hs => hb ?_
      rw [← hs.1] at hi
      simpa [τ] using hi
    · exact HasCompactSupport.intro isCompact_empty fun b _ => if_neg fun hs => hx hs.2
  · funext z
    rw [Finset.sum_apply, hgh z]
    generalize z ∘ Sum.inl = a
    generalize z ∘ Sum.inr = b
    rw [Fintype.sum_eq_single (σ a, τ b)]
    · by_cases hst : (σ a ∩ τ b).Nonempty
      · have hs : (σ a).Nonempty := hst.mono Finset.inter_subset_left
        have ht : (τ b).Nonempty := hst.mono Finset.inter_subset_right
        have hmem := Finset.mem_inter.1 hst.choose_spec
        simp only [σ, τ, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        have hc : c (σ a) (τ b) = h (hst.choose : (κ → X) × (κ' → X)) := dif_pos hst
        simp only [true_and, hs, ht, and_self, if_true, hc, mul_one]
        exact hconst _ a hmem.1 b hmem.2
      · have hc : c (σ a) (τ b) = 0 := dif_neg hst
        simp only [hc, ite_self, zero_mul]
        by_contra hne
        obtain ⟨i, hi, hab⟩ := mem_iUnion₂.1 (hF (subset_tsupport h hne))
        exact hst ⟨⟨i, hi⟩, Finset.mem_inter.2 ⟨by simpa [σ] using hab.1, by simpa [τ] using hab.2⟩⟩
    · intro x hx
      by_cases h1 : σ a = x.1
      · have h2 : τ b ≠ x.2 := fun h2 => hx (Prod.ext h1.symm h2.symm)
        simp [h2]
      · simp [h1]
end GlobalTheory.SBProd
