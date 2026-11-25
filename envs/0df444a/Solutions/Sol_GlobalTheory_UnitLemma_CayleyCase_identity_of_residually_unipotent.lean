-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:44:00.759589+00:00
-- url     : https://prove2.me/submissions/361442d5-35f9-4db1-8510-8a60d04556e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_sub_inv_mem
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_mem_adjoin_both
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_stable_iff
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_mem_adjoin_of_mem
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_exists_stable_lat
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_val_res_eq
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_separable_of_adjoin
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_exists_eps
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_cayley_selfadj
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_lift_factor
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_eval_neg_isUnit
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_stSum_withG
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_kapSum_withG
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_prod_P


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K,
    B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ,
    algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 →
    (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧
      Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) →
    InvAlg.Identity B₁ B₂ := by
  intro hL K hodd B₁ B₂ hu₁ hu₂ hsep s hs ⟨Q, hQ, hQr⟩
  have hinj := IsFractionRing.injective K.O K.E
  obtain ⟨ε, hεu, hεc⟩ := exists_eps K
  obtain ⟨Q₁, Q₂, hQQ, e₁, e₂, a₁, a₂, hm⟩ := lift_factor B₁ B₂ hsep Q hQ
  have hQs := eval_neg_isUnit hodd Q s hQr
  have hQs₁ : IsUnit (Q₁.eval (-(s : K.O))) := by
    rw [hQQ, eval_mul] at hQs; exact isUnit_of_mul_isUnit_left hQs
  have hQs₂ : IsUnit (Q₂.eval (-(s : K.O))) := by
    rw [hQQ, eval_mul] at hQs; exact isUnit_of_mul_isUnit_right hQs
  have hm₁ : Q₁.Monic := monic_of_injective hinj (e₁ ▸ LinearMap.charpoly_monic _)
  have hm₂ : Q₂.Monic := monic_of_injective hinj (e₂ ▸ LinearMap.charpoly_monic _)
  obtain ⟨w₁, -, hw₁⟩ := sub_inv_mem B₁.g (-(s : K.O)) Q₁ a₁ hQs₁
  obtain ⟨w₂, -, hw₂⟩ := sub_inv_mem B₂.g (-(s : K.O)) Q₂ a₂ hQs₂
  rw [map_neg, sub_neg_eq_add] at hw₁ hw₂
  set Y₁ := algebraMap K.O B₁.A ε * (B₁.g - algebraMap K.O B₁.A s) * w₁ with hY₁d
  set Y₂ := algebraMap K.O B₂.A ε * (B₂.g - algebraMap K.O B₂.A s) * w₂ with hY₂d
  have hY₁ : Y₁ * (B₁.g + algebraMap K.O B₁.A s) = algebraMap K.O B₁.A ε * (B₁.g - algebraMap K.O B₁.A s) := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A ε * (B₁.g - algebraMap K.O B₁.A s)) * hw₁
  have hY₂ : Y₂ * (B₂.g + algebraMap K.O B₂.A s) = algebraMap K.O B₂.A ε * (B₂.g - algebraMap K.O B₂.A s) := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A ε * (B₂.g - algebraMap K.O B₂.A s)) * hw₂
  have adj₁ := mem_adjoin_both B₁.g Y₁ (s : K.O) ε Q₁ hm₁ a₁ hQs₁ s.isUnit hεu hodd hY₁
  have adj₂ := mem_adjoin_both B₂.g Y₂ (s : K.O) ε Q₂ hm₂ a₂ hQs₂ s.isUnit hεu hodd hY₂
  have aQ : aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) Q = 0 := by
    have f1 := aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    have f2 := aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    refine Prod.ext ?_ ?_
    · change AlgHom.fst K.O B₁.A B₂.A _ = 0
      rw [← f1]; change aeval B₁.g Q = 0
      rw [hQQ, map_mul, a₁, zero_mul]
    · change AlgHom.snd K.O B₁.A B₂.A _ = 0
      rw [← f2]; change aeval B₂.g Q = 0
      rw [hQQ, map_mul, a₂, mul_zero]
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * ((B₁.g, B₂.g) + algebraMap K.O (B₁.A × B₂.A) s) =
      algebraMap K.O (B₁.A × B₂.A) ε * ((B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) s) :=
    Prod.ext hY₁ hY₂
  have adjP := mem_adjoin_both ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) (s : K.O) ε Q hm aQ hQs s.isUnit hεu hodd hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := cayley_selfadj B₁ (s : K.O) ε Y₁ hu₁ hs hεc w₁ hw₁ hY₁
  have sa₂ := cayley_selfadj B₂ (s : K.O) ε Y₂ hu₂ hs hεc w₂ hw₂ hY₂
  have hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable := by
    have := Orbit.prod_P B₁ B₂
    rw [← this] at hsep; exact hsep
  have hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable := by
    rw [← Orbit.prod_P]
    have := separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂)
      (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP
    exact this
  have hId := hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC

  have hr : resultant B₁.P B₂.P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero
  have hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero
  obtain ⟨M₁, l₁, s₁⟩ := exists_stable_lat (E := K.E) B₁.g ⟨Q₁, hm₁, a₁⟩
  obtain ⟨M₂, l₂, s₂⟩ := exists_stable_lat (E := K.E) B₂.g ⟨Q₂, hm₂, a₂⟩
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P) :=
    val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂
  unfold InvAlg.Identity at hId ⊢
  rw [kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂] at hId
  change (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _
  rw [hv]
  exact hId
end GlobalTheory.UnitLemma.CayleyCase
