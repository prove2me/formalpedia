-- Prove2me | solution 1 for GlobalTheory.NormValuation.exponent_relNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:01.855187+00:00
-- url     : https://prove2.me/submissions/98613a36-650c-4152-ac9d-6170e29faec9

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMul
import Theorems.Thm_GlobalTheory_NormValuation_exponent_mul
import Theorems.Thm_GlobalTheory_NormValuation_exponent_top
import Theorems.Thm_GlobalTheory_NormValuation_exponent_relNorm_prime

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
    (I : Ideal (𝓞 K)) : I ≠ ⊥ →
    (exponent v (Ideal.relNorm (𝓞 E) I) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w I : ℤ) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff.1 hx, Ideal.relNorm_top, exponent_top]
    simp [exponent_top]
  | h₃ a p ha hp ih =>
    intro _
    have : p.IsPrime := Ideal.isPrime_of_prime hp
    have hp0 : p ≠ ⊥ := hp.ne_zero
    rw [map_mul, exponent_mul v (Ideal.relNorm_eq_bot_iff.not.2 hp0)
      (Ideal.relNorm_eq_bot_iff.not.2 ha), Nat.cast_add, exponent_relNorm_prime v s hs p hp0, ih ha,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [exponent_mul w hp0 ha, Nat.cast_add, mul_add]
end GlobalTheory.NormValuation
