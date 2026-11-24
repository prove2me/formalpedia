-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Span.sb_eq_sum_coset_indicators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:33:36.431996+00:00
-- url     : https://prove2.me/submissions/10465bc3-1946-4e12-b7de-8b159b1209a8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SbEqSumCosetIndicators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Span
namespace GlobalTheory.CompanionTheory.SW.Span
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ)
      (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∀ L' : AddSubgroup V,
      IsOpen (L' : Set V) → (∀ x, ∀ l ∈ L', φ (x + l) = φ x) →
      ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L'} (fun _ => (1 : ℂ)) x := by
  intro V _ _ _ χ μ h φ hφ L' hL' hinv
  classical
  haveI : IsTopologicalAddGroup V := h.1
  obtain ⟨t, ht⟩ := hφ.2.isCompact.elim_finite_subcover (fun a : V => {y | y - a ∈ L'})
    (fun a => hL'.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [L'.zero_mem]⟩)
  let T : Finset (V ⧸ L') := t.image (QuotientAddGroup.mk : V → V ⧸ L')
  refine ⟨T.image Quotient.out, fun x => ?_⟩
  rw [Finset.sum_image (fun a _ b _ hab => Quotient.out_injective hab)]
  have key : ∀ q : V ⧸ L', x - q.out ∈ L' ↔ q = (x : V ⧸ L') := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
  have hval : φ ((x : V ⧸ L').out) = φ x := by
    have hm : x - ((x : V ⧸ L')).out ∈ L' := (key _).2 rfl
    have := hinv ((x : V ⧸ L')).out _ hm
    rw [← this]
    congr 1
    abel
  have hterm : ∀ q : V ⧸ L', φ q.out * Set.indicator {y | y - q.out ∈ L'} (fun _ => (1 : ℂ)) x
      = if q = (x : V ⧸ L') then φ x else 0 := by
    intro q
    by_cases hq : q = (x : V ⧸ L')
    · subst hq
      rw [if_pos rfl, Set.indicator_of_mem (show x ∈ {y | y - ((x : V ⧸ L')).out ∈ L'} from (key _).2 rfl),
        hval, mul_one]
    · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {y | y - q.out ∈ L'} from fun hx => hq ((key _).1 hx)),
        mul_zero]
  simp only [hterm, Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ hne
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hx
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    exact hxa
end GlobalTheory.CompanionTheory.SW.Span
