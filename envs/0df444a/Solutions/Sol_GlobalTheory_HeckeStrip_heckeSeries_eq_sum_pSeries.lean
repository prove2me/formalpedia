-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.heckeSeries_eq_sum_pSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:37:38.431525+00:00
-- url     : https://prove2.me/submissions/e99d877f-6410-49d8-897d-c2c725f9628e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_HeckeStrip_tsum_ideal_eq_sum_classGroup_of_summable
import Theorems.Thm_GlobalTheory_HeckeStrip_classPartFun_add
import Theorems.Thm_GlobalTheory_HeckeStrip_classPartFun_unit
import Theorems.Thm_GlobalTheory_HeckeStrip_pSeries_classPartFun
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_Mem_summable_norm_absNorm_cpow
import Theorems.Thm_GlobalTheory_exists_integral_ideal_in_class_coprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
namespace GlobalTheory.HeckeStrip
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (I : Type) [Fintype I] (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b) → (∀ a : Ideal (𝓞 K), a ≠ ⊥ → a ⊔ m = ⊤ → ‖X a‖ = 1) → (∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = GlobalTheory.HeckeStrip.wt φ n (β : K)) → ∃ (r : ℕ) (c : Fin r → ℂ) (B : Fin r → ℕ) (M : Fin r → Ideal (𝓞 K)) (F : Fin r → 𝓞 K → ℂ), (∀ k, 0 < B k) ∧ (∀ k, M k ≠ ⊥) ∧ (∀ k (α μ : 𝓞 K), μ ∈ M k → F k (α + μ) = F k α) ∧ (∀ k (u : (𝓞 K)ˣ) (α : 𝓞 K), F k ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F k α * GlobalTheory.HeckeStrip.wt φ n (α : K)) ∧ ∀ s : ℂ, 1 < s.re → ∑' a : Ideal (𝓞 K), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s) = ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * GlobalTheory.HeckeStrip.pSeries (F k) φ n s := by
  intro K _ _ I _ φ n m X hm hX0 hmul hnorm hzero hβ
  choose b hb hbm using GlobalTheory.exists_integral_ideal_in_class_coprime K m hm
  have hbij : Function.Bijective (fun c => ClassGroup.mk0 (b c)) := by
    have e : (fun c => ClassGroup.mk0 (b c)) = id := funext hb
    rw [e]; exact Function.bijective_id
  have hb0 : ∀ c, (b c : Ideal (𝓞 K)) ≠ ⊥ := fun c => nonZeroDivisors.coe_ne_zero (b c)
  have hXb : ∀ c, X (b c) ≠ 0 := fun c h => by
    have := hnorm _ (hb0 c) (hbm c)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hNb : ∀ c, Ideal.absNorm (b c : Ideal (𝓞 K)) ≠ 0 := fun c h => hb0 c (Ideal.absNorm_eq_zero_iff.mp h)
  let e := Fintype.equivFin (ClassGroup (𝓞 K))
  refine ⟨Fintype.card (ClassGroup (𝓞 K)), fun k => (X (b (e.symm k)))⁻¹,
    fun k => Ideal.absNorm (b (e.symm k) : Ideal (𝓞 K)), fun k => m * (b (e.symm k) : Ideal (𝓞 K)),
    fun k => classPartFun φ n m X (b (e.symm k)), fun k => Nat.pos_of_ne_zero (hNb _),
    fun k => mul_ne_zero hm (hb0 _), fun k α μ hμ => classPartFun_add hmul hzero hβ _ hμ,
    fun k u α => classPartFun_unit hβ _ u α, fun s hs => ?_⟩
  have hXle : ∀ J, ‖X J‖ ≤ 1 := by
    intro J
    by_cases h0 : J = ⊥
    · rw [h0, hX0, norm_zero]; exact zero_le_one
    by_cases hc : J ⊔ m = ⊤
    · rw [hnorm J h0 hc]
    · rw [hzero J hc, norm_zero]; exact zero_le_one
  have hsum : Summable fun J : Ideal (𝓞 K) => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) :=
    (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs).of_norm_bounded fun J => by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hXle J)
  have hH : ∀ c (J : Ideal (𝓞 K)), J ≠ ⊥ →
      (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
        (X (J * (b c : Ideal (𝓞 K))) * ((Ideal.absNorm (J * (b c : Ideal (𝓞 K))) : ℕ) : ℂ) ^ (-s)) =
      X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) := by
    intro c J _
    have hpow : ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
        ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 1 := by
      rw [Complex.cpow_neg, mul_inv_cancel₀]
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Nat.cast_ne_zero.mpr (hNb c))
    rw [hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    calc (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
          (X J * X (b c) * (((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) *
            ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)))
        = X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) * ((X (b c))⁻¹ * X (b c)) *
          (((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
            ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) := by ring
      _ = X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) := by rw [inv_mul_cancel₀ (hXb c), hpow, mul_one, mul_one]
  rw [tsum_ideal_eq_sum_classGroup_of_summable b (fun J => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s))
    (fun c J => (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
      (X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s))) hbij (by simp only [hX0, zero_mul]) hsum hH]
  refine (Equiv.sum_comp e.symm _).symm.trans (Finset.sum_congr rfl fun k _ => ?_)
  beta_reduce
  rw [tsum_mul_left, pSeries_classPartFun hβ]
end GlobalTheory.HeckeStrip
