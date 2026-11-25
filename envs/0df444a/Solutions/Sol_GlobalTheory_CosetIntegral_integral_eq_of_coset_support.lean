-- Prove2me | solution 1 for GlobalTheory.CosetIntegral.integral_eq_of_coset_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:37:48.724819+00:00
-- url     : https://prove2.me/submissions/36cfad7a-0c5f-4253-9d94-7c40e401a89c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralSumIndicatorTranslate
import Theorems.Thm_GlobalTheory_CosetIntegral_integral_sum_indicator_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CosetIntegral
namespace GlobalTheory.CosetIntegral
theorem _root_.solution
    (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R]
    [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] [Group S]
    [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S]
    (i : S →* R) (hi : Topology.IsClosedEmbedding i) (μ : Measure R) (ν : Measure S)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (R₀ : Subgroup R) (hR₀o : IsOpen (R₀ : Set R)) (_hR₀c : IsCompact (R₀ : Set R))
    (hμ : μ R₀ = 1) (hν : ν (i ⁻¹' R₀) = 1) (h : R → ℂ)
    (hinv : ∀ k ∈ R₀, ∀ g, h (k * g) = h g)
    (hsupp : ∀ g, h g ≠ 0 → ∃ k ∈ R₀, ∃ s, g = k * i s)
    (hcs : HasCompactSupport (fun s => h (i s))) :
    ∫ g, h g ∂μ = ∫ s, h (i s) ∂ν := by
  classical
  let S₀ : Subgroup S := R₀.comap i
  have hS₀o : IsOpen (i ⁻¹' (R₀ : Set R)) := hR₀o.preimage hi.continuous
  have hconst : ∀ g r, g * (i r)⁻¹ ∈ R₀ → h (i r) = h g := by
    intro g r hg
    have := hinv _ hg (i r)
    simpa using this.symm
  let U : S → Set S := fun s => (fun x => x * s⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))
  have hUo : ∀ s, IsOpen (U s) := fun s => hS₀o.preimage (continuous_mul_right _)
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover U hUo
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [U, R₀.one_mem]⟩)
  let mk : S → Quotient (QuotientGroup.rightRel S₀) := fun s => Quotient.mk _ s
  let T := t.image mk
  have hrel : ∀ a b : S, mk a = mk b ↔ i b * (i a)⁻¹ ∈ R₀ := fun a b => by
    simp only [mk, Quotient.eq, QuotientGroup.rightRel_apply, S₀, Subgroup.mem_comap,
      map_mul, map_inv]
  have hout : ∀ q, mk q.out = q := fun q => Quotient.out_eq q
  have hsuppT : ∀ x, h (i x) ≠ 0 → mk x ∈ T := by
    intro x hx
    have hx' : x ∈ tsupport (fun s => h (i s)) := subset_tsupport _ hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx')
    refine Finset.mem_image.2 ⟨s, hs, (hrel s x).2 ?_⟩
    simpa [U] using hxs
  have hrep : ∀ x, h (i (mk x).out) = h (i x) := by
    intro x
    apply hconst
    exact (hrel _ x).1 (hout _)

  have hR : (fun g => h g) = fun g => ∑ q ∈ T,
      ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R)).indicator (fun _ => h (i q.out)) g := by
    funext g
    by_cases hg : h g = 0
    · rw [hg]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      by_cases hm : g ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))
      · rw [Set.indicator_of_mem hm, hconst g _ hm, hg]
      · rw [Set.indicator_of_notMem hm]
    · obtain ⟨k, hk, s, rfl⟩ := hsupp g hg
      have hs : h (i s) ≠ 0 := by rwa [hinv k hk] at hg
      have hmem : ∀ q, (k * i s ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))) ↔ mk s = q := by
        intro q
        have e : mk s = q ↔ i s * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out s, hout q, eq_comm]
        rw [e]
        simp only [Set.mem_preimage, SetLike.mem_coe, mul_assoc]
        exact Subgroup.mul_mem_cancel_left R₀ hk
      simp only [Set.indicator, hmem, Finset.sum_ite_eq, if_pos (hsuppT s hs), hrep, hinv k hk]
  have hS : (fun x => h (i x)) = fun x => ∑ q ∈ T,
      ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))).indicator (fun _ => h (i q.out)) x := by
    funext x
    have hmem : ∀ q, x ∈ ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))) ↔ mk x = q := by
      intro q
      have e : mk x = q ↔ i x * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out x, hout q, eq_comm]
      rw [e]
      simp
    simp only [Set.indicator, hmem, Finset.sum_ite_eq]
    split_ifs with hx
    · rw [hrep]
    · by_contra hne
      exact hx (hsuppT x hne)
  rw [hR, hS, integral_sum_indicator_translate μ _ hR₀o hμ,
    integral_sum_indicator_translate ν _ hS₀o hν]
end GlobalTheory.CosetIntegral
