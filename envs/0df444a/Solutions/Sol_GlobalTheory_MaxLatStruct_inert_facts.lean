-- Prove2me | solution 1 for GlobalTheory.MaxLatStruct.inert_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:15.699983+00:00
-- url     : https://prove2.me/submissions/3c2ab3e2-1591-47f3-af4a-427892c03e85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Theorems.Thm_GlobalTheory_MaxLatStruct_finite_field_invol

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
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct
namespace GlobalTheory.MaxLatStruct
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) {σ : 𝓞 K →+* 𝓞 K}
    (hσ : ∀ r, algebraMap (𝓞 K) K (σ r) = star (algebraMap (𝓞 K) K r)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hin : ∀ r, σ r ∈ P ↔ r ∈ P) :
    (2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2) ∧
      ∀ a b : 𝓞 K, a ∉ P → σ a * b = σ b * a → ∃ w, σ w * w * a + b ∈ P := by
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hσσ : ∀ r, σ (σ r) = r := fun r => hinj (by rw [hσ, hσ, star_star])
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have : Finite (𝓞 K ⧸ P) := P.finiteQuotientOfFreeOfNeBot hP0
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let τ : 𝓞 K ⧸ P →+* 𝓞 K ⧸ P := Ideal.quotientMap P σ fun r hr => (hin r).2 hr
  have hτ : ∀ r, τ (Ideal.Quotient.mk P r) = Ideal.Quotient.mk P (σ r) := fun r => rfl
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  have ht' : t = σ θ := hinj (by rw [ht, hσ])
  obtain ⟨⟨q, hq2, hq⟩, hN⟩ := finite_field_invol τ
    (fun a => by obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a; rw [hτ, hτ, hσσ])
    (Ideal.Quotient.mk P θ)
    (by rw [hτ, ← map_sub, Ne, Ideal.Quotient.eq_zero_iff_mem, ← ht']; exact hθ)
  have hn : Ideal.absNorm P = q ^ 2 := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq]
  have hqq : qIn P = q := by rw [qIn, hn, Nat.sqrt_eq']
  refine ⟨by rw [hqq]; exact ⟨hq2, hn⟩, fun a b ha hab => ?_⟩
  have ha0 : Ideal.Quotient.mk P a ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have ha1 : Ideal.Quotient.mk P (σ a) ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, hin]
  have hab' := congrArg (Ideal.Quotient.mk P) hab
  rw [map_mul, map_mul] at hab'
  obtain ⟨w, hw⟩ := hN (-(Ideal.Quotient.mk P b / Ideal.Quotient.mk P a)) (by
    rw [map_neg, map_div₀, hτ, hτ, neg_inj, div_eq_div_iff ha1 ha0, ← hab', mul_comm])
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨w, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_mul, map_mul, ← hτ, hw, neg_mul, div_mul_cancel₀ _ ha0,
    neg_add_cancel]
end GlobalTheory.MaxLatStruct
