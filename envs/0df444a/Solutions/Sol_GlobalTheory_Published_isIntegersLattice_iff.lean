-- Prove2me | solution 1 for GlobalTheory.Published.isIntegersLattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:31.315448+00:00
-- url     : https://prove2.me/submissions/7c6195c6-dde6-4f6e-8b9a-4bc51b5e804a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
import Theorems.Thm_GlobalTheory_Published_mem_adjoin_sqrtNegNat_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {p : ℕ} {K : Type} [Field K] [NumberField K]
variable [Algebra K ℂ]
namespace GlobalTheory.Published
theorem _root_.solution (hp : 0 < p) (h2 : Module.finrank ℚ K = 2) {x : K}
    (hx : x ^ 2 = -(p : K)) (L : PeriodPair) :
    IsIntegersLattice p L ↔ IsIdealLattice (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) L := by
  let ψ : K →ₐ[ℤ] ℂ := (algebraMap K ℂ).toIntAlgHom
  have key : ∀ z : ℂ, (z ∈ ℚ⟮sqrtNegNat p⟯ ∧ IsIntegral ℤ z) ↔
      z ∈ algebraMap K ℂ '' (((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
    intro z
    rw [mem_adjoin_sqrtNegNat_iff hp h2 hx z, Units.val_one]
    constructor
    · rintro ⟨⟨y, rfl⟩, hz⟩
      have hy : IsIntegral ℤ y :=
        (isIntegral_algHom_iff ψ (algebraMap K ℂ).injective).mp hz
      refine ⟨y, ?_, rfl⟩
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hy
      refine ⟨⟨_, rfl⟩, ?_⟩
      exact (isIntegral_algHom_iff ψ (algebraMap K ℂ).injective).mpr r.isIntegral_coe
  unfold IsIntegersLattice IsIdealLattice
  constructor
  · intro h
    ext z
    exact (h z).trans (key z)
  · intro h z
    rw [key z]
    exact Set.ext_iff.mp h z
end GlobalTheory.Published
