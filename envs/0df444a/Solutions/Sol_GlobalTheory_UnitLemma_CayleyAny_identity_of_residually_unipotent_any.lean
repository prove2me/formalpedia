-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:52.399458+00:00
-- url     : https://prove2.me/submissions/4d90f07d-5eb0-49d3-abb8-471c149c97c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_CayleyAny_mem_adjoin_both__1374612a08f4
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyAny_isUnit_of_conj
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyAny_mobius_selfadj
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_exists_stable_lat
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_kapSum_withG
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_lift_factor
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_mem_adjoin_of_mem
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_separable_of_adjoin
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_stSum_withG
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_stable_iff
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_sub_inv_mem
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_val_res_eq
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_prod_P
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyAny
open GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CayleyAny
theorem _root_.solution : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K),
    B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ,
    algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 →
    (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧
      Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) →
    InvAlg.Identity B₁ B₂ := by
  intro hL K B₁ B₂ hu₁ hu₂ hsep s hs ⟨Q, hQ, hQr⟩
  have hinj := IsFractionRing.injective K.O K.E

  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  have hyx : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
  have hxu : IsUnit x := by
    by_contra hx
    have hy : ¬ IsUnit y := fun hy => hx (isUnit_of_conj K x y hxy hy)
    exact hm (Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx) ((IsLocalRing.mem_maximalIdeal _).2 hy))
  have hyu : IsUnit y := isUnit_of_conj K y x hyx hxu
  have hxyu : IsUnit (x - y) := by
    by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  set yi : K.O := ↑hyu.unit⁻¹ with hyi
  have hyyi : y * yi = 1 := hyu.mul_val_inv
  set ξ : K.O := (s : K.O) * x * yi with hξd
  have hξu : IsUnit ξ := (s.isUnit.mul hxu).mul (hyu.unit⁻¹).isUnit
  have hξn : algebraMap K.O K.E ξ * K.c (algebraMap K.O K.E ξ) = 1 := by
    obtain ⟨w, hw⟩ := K.c_int yi
    have e1 : algebraMap K.O K.E x * algebraMap K.O K.E w = 1 := by
      have := congrArg K.c (congrArg (algebraMap K.O K.E) hyyi)
      rw [map_mul, map_mul, hyx, hw, map_one, map_one] at this
      exact this
    have e2 : algebraMap K.O K.E y * algebraMap K.O K.E yi = 1 := by
      rw [← map_mul, hyyi, map_one]
    rw [hξd, map_mul, map_mul, map_mul, map_mul, hxy, hw]
    linear_combination (algebraMap K.O K.E x * algebraMap K.O K.E w * algebraMap K.O K.E y *
      algebraMap K.O K.E yi) * hs + (algebraMap K.O K.E y * algebraMap K.O K.E yi) * e1 + e2
  have hQξ : IsUnit (Q.eval ξ) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval₂_hom, ← eval_map, hQr]
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    apply pow_ne_zero
    intro h0
    apply hm
    set r := IsLocalRing.residue K.O
    have hs0 : r (s : K.O) ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 s.isUnit
    have h3 : r (y * yi) = 1 := by rw [hyyi, map_one]
    rw [map_mul] at h3
    have h4 : r (s : K.O) * (r x - r y) = 0 := by
      rw [hξd, map_mul, map_mul] at h0
      linear_combination r y * h0 - (r (s : K.O) * r x) * h3
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    exact (mul_eq_zero.1 h4).resolve_left hs0
  have hab : IsUnit (ξ * y - x * ξ) := by
    rw [show ξ * y - x * ξ = -(ξ * (x - y)) by ring]
    exact (hξu.mul hxyu).neg
  obtain ⟨Q₁, Q₂, hQQ, e₁, e₂, a₁, a₂, hmQ⟩ := lift_factor B₁ B₂ hsep Q hQ
  have hQs₁ : IsUnit (Q₁.eval ξ) := by
    rw [hQQ, eval_mul] at hQξ; exact isUnit_of_mul_isUnit_left hQξ
  have hQs₂ : IsUnit (Q₂.eval ξ) := by
    rw [hQQ, eval_mul] at hQξ; exact isUnit_of_mul_isUnit_right hQξ
  have hm₁ : Q₁.Monic := monic_of_injective hinj (e₁ ▸ LinearMap.charpoly_monic _)
  have hm₂ : Q₂.Monic := monic_of_injective hinj (e₂ ▸ LinearMap.charpoly_monic _)
  obtain ⟨w₁, -, hw₁⟩ := sub_inv_mem B₁.g ξ Q₁ a₁ hQs₁
  obtain ⟨w₂, -, hw₂⟩ := sub_inv_mem B₂.g ξ Q₂ a₂ hQs₂
  set Y₁ := (algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ) * w₁ with hY₁d
  set Y₂ := (algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ) * w₂ with hY₂d
  have hY₁ : Y₁ * (B₁.g - algebraMap K.O B₁.A ξ) =
      algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ) * hw₁
  have hY₂ : Y₂ * (B₂.g - algebraMap K.O B₂.A ξ) =
      algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ) * hw₂
  have hY₁' : Y₁ * (B₁.g - algebraMap K.O B₁.A ξ) = algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A (x * ξ) := by
    rw [map_mul (algebraMap K.O B₁.A) x ξ]; exact hY₁
  have hY₂' : Y₂ * (B₂.g - algebraMap K.O B₂.A ξ) = algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A (x * ξ) := by
    rw [map_mul (algebraMap K.O B₂.A) x ξ]; exact hY₂
  have adj₁ := mem_adjoin_both' B₁.g Y₁ ξ y (x * ξ) Q₁ hm₁ a₁ hQs₁ hab hY₁'
  have adj₂ := mem_adjoin_both' B₂.g Y₂ ξ y (x * ξ) Q₂ hm₂ a₂ hQs₂ hab hY₂'
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
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * ((B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) ξ) =
      algebraMap K.O (B₁.A × B₂.A) y * (B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) (x * ξ) :=
    Prod.ext hY₁' hY₂'
  have adjP := mem_adjoin_both' ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) ξ y (x * ξ) Q hmQ aQ hQξ hab hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := mobius_selfadj B₁ x y ξ Y₁ hu₁ hxy hξn w₁ hw₁ hY₁
  have sa₂ := mobius_selfadj B₂ x y ξ Y₂ hu₂ hxy hξn w₂ hw₂ hY₂
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
end GlobalTheory.UnitLemma.CayleyAny
