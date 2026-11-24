-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.eq_or_eq_bar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:51.622063+00:00
-- url     : https://prove2.me/submissions/982783ee-8018-42c4-8319-44a69649b88d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
local notation "cc" => IsCMField.complexConj E
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {w P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over w v) (hP : Over P v) :
    P = w ∨ P = bar w := by
  have hsub : (P.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ (bar w).asIdeal := fun x hx => by
    let y : 𝓞 E := x * RingOfIntegers.mapRingEquiv (cc).toRingEquiv x
    have hy : (y : E) ∈ maximalRealSubfield E := by
      rw [← IsCMField.complexConj_eq_self_iff]
      change cc ((x : E) * cc (x : E)) = (x : E) * cc (x : E)
      rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]
    have hint : IsIntegral ℤ (⟨y, hy⟩ : maximalRealSubfield E) :=
      (isIntegral_algebraMap_iff (algebraMap (maximalRealSubfield E) E).injective).1 y.isIntegral_coe
    obtain ⟨a, hn⟩ : ∃ a : OF E, algebraMap (OF E) (𝓞 E) a = y := ⟨⟨_, hint⟩, RingOfIntegers.ext rfl⟩
    have h1 : a ∈ v.asIdeal := by
      rw [← hP, Ideal.mem_comap, hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [← h, Ideal.mem_comap, hn] at h1
    exact w.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h | h
  · exact Or.inl (HeightOneSpectrum.ext (P.isMaximal.eq_of_le w.isPrime.ne_top h))
  · exact Or.inr (HeightOneSpectrum.ext (P.isMaximal.eq_of_le (bar w).isPrime.ne_top h))
end GlobalTheory.CMVal.ValEx
