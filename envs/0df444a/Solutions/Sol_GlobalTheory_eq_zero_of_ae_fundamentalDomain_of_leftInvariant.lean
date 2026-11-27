-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:38:13.462803+00:00
-- url     : https://prove2.me/submissions/bb958725-e009-4953-aa62-1b41bcf3314f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroOfAeFundamentalDomainOfLeftInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsHaarMeasure] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ)
    (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x)
    (hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) : ∀ x, F x = 0 := by
  set U : Set G := {x | F x ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hF continuous_const
  have hUinv : ∀ g : Γ, g • U = U := by
    intro g
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, hUdef, Set.mem_setOf_eq, Subgroup.smul_def,
      smul_eq_mul]
    rw [hinv _ (Γ.inv_mem g.2)]
  have hU𝓕 : μ (U ∩ 𝓕) = 0 := by
    rw [ae_iff, Measure.restrict_apply hUo.measurableSet] at hae
    simpa [hUdef] using hae
  have hU0 : μ U = 0 := h𝓕.measure_zero_of_invariant U hUinv hU𝓕
  have hUe : U = ∅ := by
    by_contra hne
    exact (hUo.measure_pos μ (Set.nonempty_iff_ne_empty.mpr hne)).ne' hU0
  intro x
  by_contra hx
  have : x ∈ U := hx
  rw [hUe] at this
  exact this
end GlobalTheory
