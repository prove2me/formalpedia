-- Prove2me | solution 1 for GlobalTheory.RegularNormal.StableDvd.isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:55:00.688949+00:00
-- url     : https://prove2.me/submissions/5347b8f3-7724-410c-9eea-8892c0875bc3

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.RegularNormal
namespace GlobalTheory.RegularNormal
namespace StableDvd
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A] (h : StableDvd A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro y hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) y
  set K := FractionRing A
  set y : K := algebraMap A K a / algebraMap A K b with hydef
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 := by
    simpa using hb0
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  obtain ⟨d, hd, hdN⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors A)
    hy.fg_adjoin_singleton
  let I : Ideal A :=
    { carrier := {r | ∀ z ∈ Algebra.adjoin A {y}, ∃ s : A, algebraMap A K s = r • z}
      zero_mem' := fun z _ => ⟨0, by simp⟩
      add_mem' := by
        intro r r' hr hr' z hz
        obtain ⟨s, hs⟩ := hr z hz
        obtain ⟨s', hs'⟩ := hr' z hz
        exact ⟨s + s', by rw [map_add, hs, hs', add_smul]⟩
      smul_mem' := by
        intro c r hr z hz
        obtain ⟨s, hs⟩ := hr z hz
        exact ⟨c * s, by rw [map_mul, hs, smul_eq_mul, mul_smul, Algebra.smul_def c]⟩ }
  have hyN : y ∈ Algebra.adjoin A {y} := Algebra.self_mem_adjoin_singleton A y
  have hdI : d ∈ I := fun z hz => hdN z hz
  have hI : I ≠ ⊥ := fun h0 => nonZeroDivisors.ne_zero hd (by simpa [h0] using hdI)
  obtain ⟨c, hc⟩ := h a b I hb0 hI (by
    intro r hr
    obtain ⟨s, hs⟩ := hr y hyN
    refine ⟨s, fun z hz => ?_, hinj ?_⟩
    · obtain ⟨t, ht⟩ := hr (y * z) (mul_mem hyN hz)
      refine ⟨t, ?_⟩
      rw [ht, Algebra.smul_def s, hs, smul_mul_assoc]
    · rw [map_mul, map_mul, hs, Algebra.smul_def, hydef, mul_left_comm, mul_div_cancel₀ _ hbK, mul_comm])
  refine ⟨c, ?_⟩
  rw [hydef, hc, map_mul, mul_div_cancel_left₀ _ hbK]
end StableDvd
end GlobalTheory.RegularNormal
