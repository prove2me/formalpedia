-- Prove2me | solution 1 for GlobalTheory.NormValuation.exponent_relNorm_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:32.477738+00:00
-- url     : https://prove2.me/submissions/5b123907-e0bc-4892-b304-f8dd21a47dca

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMul
import Theorems.Thm_GlobalTheory_NormValuation_exponent_pow
import Theorems.Thm_GlobalTheory_NormValuation_exponent_self
import Theorems.Thm_GlobalTheory_NormValuation_exponent_prime_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
noncomputable section
open GlobalTheory GlobalTheory.NormValuation
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
namespace GlobalTheory.NormValuation
theorem _root_.solution (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p ≠ ⊥) :
    (exponent v (Ideal.relNorm (𝓞 E) p) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w p : ℤ) := by
  have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp inferInstance
  have hq : p.under (𝓞 E) ≠ ⊥ := Ideal.under_ne_bot (𝓞 E) hp
  have : (p.under (𝓞 E)).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq inferInstance
  rw [Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 E)), exponent_pow v hq]
  by_cases h : p.under (𝓞 E) = v.asIdeal
  · let w0 : HeightOneSpectrum (𝓞 K) := ⟨p, inferInstance, hp⟩
    have hw0 : w0 ∈ s := (hs w0).2 h
    rw [Finset.sum_eq_single w0]
    · rw [h, exponent_self, exponent_self]
      simp [w0]
    · intro w _ hw
      rw [exponent_prime_of_ne w p hp, Nat.cast_zero, mul_zero]
      intro he
      exact hw (HeightOneSpectrum.ext he.symm)
    · intro h'; exact absurd hw0 h'
  · rw [exponent_prime_of_ne v _ hq h, mul_zero, Nat.cast_zero]
    refine (Finset.sum_eq_zero fun w hw => ?_).symm
    rw [exponent_prime_of_ne w p hp, Nat.cast_zero, mul_zero]
    intro he
    apply h
    rw [← (hs w).1 hw, he]
end GlobalTheory.NormValuation
