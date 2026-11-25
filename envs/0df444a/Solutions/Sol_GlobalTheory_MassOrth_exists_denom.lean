-- Prove2me | solution 1 for GlobalTheory.MassOrth.exists_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:21.835408+00:00
-- url     : https://prove2.me/submissions/6fead646-e1ff-4e42-bc0a-4c2208cfa83f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Theorems.Thm_GlobalTheory_MassOrth_coe_starInt
import Theorems.Thm_GlobalTheory_MassOrth_mem_hcompl_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MassOrth
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.MassOrth
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {k : K} (hk : k ∈ biInt (w.valuation K)) :
    ∃ s ∈ hcompl (K := K) w.asIdeal, ∃ a : 𝓞 K, algebraMap (𝓞 K) K s * k = algebraMap (𝓞 K) K a := by
  let D : Ideal (𝓞 K) := (1 : Submodule (𝓞 K) K).comap (LinearMap.toSpanSingleton (𝓞 K) K k)
  have hD : ∀ s, s ∈ D ↔ ∃ a : 𝓞 K, algebraMap (𝓞 K) K s * k = algebraMap (𝓞 K) K a := by
    intro s
    simp only [D, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one,
      Algebra.smul_def, eq_comm]
  obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer k hk.1
  obtain ⟨n', d', hnd'⟩ := w.exists_primeCompl_mul_eq_of_integer (star k) hk.2
  have h1 : ¬ D ≤ w.asIdeal := fun h => d.2 (h ((hD d).2 ⟨n, by rw [mul_comm]; exact hnd⟩))
  have hss : ∀ s : 𝓞 K, starInt (starInt s) = s := fun s =>
    RingOfIntegers.coe_injective (by rw [coe_starInt, coe_starInt, star_star])
  have h2 : ¬ D ≤ w.asIdeal.comap starInt := fun h => d'.2 (by
    have := h ((hD (starInt (d' : 𝓞 K))).2 ⟨starInt n', by
      rw [coe_starInt, coe_starInt, ← hnd', star_mul, star_star]⟩)
    rwa [Ideal.mem_comap, hss] at this)
  have h3 : ¬ ((D : Set (𝓞 K)) ⊆ w.asIdeal ∪ (w.asIdeal.comap starInt : Ideal (𝓞 K))) := by
    rw [Ideal.subset_union]; tauto
  obtain ⟨s, hs, hs'⟩ := Set.not_subset.1 h3
  refine ⟨s, (mem_hcompl_iff _ w.isPrime s).2 ⟨fun h => hs' (Or.inl h), fun h => hs' (Or.inr h)⟩,
    (hD s).1 hs⟩
end GlobalTheory.MassOrth
