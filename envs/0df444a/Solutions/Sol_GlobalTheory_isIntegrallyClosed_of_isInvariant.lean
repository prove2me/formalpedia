-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:47.790177+00:00
-- url     : https://prove2.me/submissions/305ed63a-028d-4fd8-98ed-52a33b766a4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution (B : Type*) [CommRing B] [Algebra B A]
    [FaithfulSMul B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    [IsDomain A] [IsIntegrallyClosed A] : IsDomain B ∧ IsIntegrallyClosed B := by
  have hinj : Function.Injective (algebraMap B A) := FaithfulSMul.algebraMap_injective B A
  haveI : IsDomain B := hinj.isDomain _
  refine ⟨inferInstance, ?_⟩
  rw [isIntegrallyClosed_iff (FractionRing B)]
  intro x hx
  have hinj' : Function.Injective ((algebraMap A (FractionRing A)).comp (algebraMap B A)) :=
    (IsFractionRing.injective A (FractionRing A)).comp hinj
  let φ : FractionRing B →+* FractionRing A := IsFractionRing.lift hinj'
  have hφ : ∀ b : B, φ (algebraMap B _ b) = algebraMap A _ (algebraMap B A b) :=
    fun b ↦ IsFractionRing.lift_algebraMap hinj' b
  have hint : IsIntegral A (φ x) :=
    hx.map_of_comp_eq (algebraMap B A) φ (RingHom.ext fun b ↦ (hφ b).symm)
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing A)).mp ‹_› hint
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
  have hb0 : algebraMap B A b ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap B (FractionRing B) b ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have hb2 : algebraMap A (FractionRing A) (algebraMap B A b) ≠ 0 := by simpa using hb0
  have hcb : c * algebraMap B A b = algebraMap B A a := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, hc, map_div₀, hφ, hφ, div_mul_cancel₀ _ hb2]
  have hfix : ∀ g : G, g • c = c := fun g ↦ by
    apply mul_right_cancel₀ hb0
    have := congrArg (g • ·) hcb
    simp only [smul_mul', smul_algebraMap] at this
    rw [this, hcb]
  obtain ⟨d, rfl⟩ := Algebra.IsInvariant.isInvariant (A := B) c hfix
  refine ⟨d, ?_⟩
  rw [eq_div_iff hb1, ← map_mul]
  congr 1
  apply hinj
  rw [map_mul, hcb]
end GlobalTheory
