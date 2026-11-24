-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.val_le_of_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:20.939273+00:00
-- url     : https://prove2.me/submissions/7f963541-cbe7-44c1-b3d3-5ed091687e05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes
import Theorems.Thm_GlobalTheory_UnRep_NormOne_val_le_of_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.UnRep.NormOne
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (N D D₁ D₂ k n : ℕ) (hD0 : 0 < D)
    (hM : D * n = D₁ * D₂) (h1 : D₁ ∣ N ^ k) (hN : (N : 𝓞 E) ∉ P.asIdeal) (hD : (D : 𝓞 E) ∈ P.asIdeal)
    (α β p b : 𝓞 E) (hab : p * D₂ + b = 1) :
    P.valuation E ((((p * D₂ * α + b : 𝓞 E) : E) / ((p * D₂ * β + b : 𝓞 E) : E) - 1) / D) ≤ 1 := by
  have hP := P.isPrime
  have hM' : (D : 𝓞 E) * n = D₁ * D₂ := by exact_mod_cast hM
  have hD₁ : (D₁ : 𝓞 E) ∉ P.asIdeal := by
    intro h
    obtain ⟨e, he⟩ := h1
    apply hN
    apply hP.mem_of_pow_mem k
    have : (N : 𝓞 E) ^ k = D₁ * e := by exact_mod_cast he
    rw [this]; exact Ideal.mul_mem_right _ _ h
  have hD₂ : (D₂ : 𝓞 E) ∈ P.asIdeal := by
    have : (D₁ : 𝓞 E) * D₂ ∈ P.asIdeal := hM' ▸ Ideal.mul_mem_right _ _ hD
    exact (hP.mem_or_mem this).resolve_left hD₁
  have hβ : p * D₂ * β + b ∉ P.asIdeal := by
    intro h
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 E) = (p * D₂ * β + b) + D₂ * (p * (1 - β)) := by linear_combination -hab
    rw [this]
    exact add_mem h (Ideal.mul_mem_right _ _ hD₂)
  have hβ0 : ((p * D₂ * β + b : 𝓞 E) : E) ≠ 0 := by
    intro h
    apply hβ
    have : (p * D₂ * β + b : 𝓞 E) = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD0.ne'
  have hME : (D : E) * n = D₁ * D₂ := by exact_mod_cast hM
  refine val_le_of_mul P _ ((n * p * (α - β) : 𝓞 E) : E) (D₁ * (p * D₂ * β + b))
    (fun h => (hP.mem_or_mem h).elim hD₁ hβ) ?_ (P.valuation_le_one _)
  rw [RingOfIntegers.coe_eq_algebraMap] at hβ0
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_sub, map_natCast] at hβ0 ⊢
  field_simp
  linear_combination (-(algebraMap (𝓞 E) E p) * (algebraMap (𝓞 E) E α - algebraMap (𝓞 E) E β)) * hME
end GlobalTheory.UnRep.NormOne
