-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:01:27.634831+00:00
-- url     : https://prove2.me/submissions/ac1a0683-c281-455f-9931-9bbd15429ae3

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_eval_pow_of_commute
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_commute_alg
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_eq_zero_of_eval
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_polF_qdet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_eval_map_hom
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_prod_smul_ofFn
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_commute_qdet_om
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_commute_coeff_om
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_root
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_neg_sub_algebra_map_smul_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
theorem _root_.solution (H : QdetTens) : CayleyHam := by
  intro n M χ hM
  obtain ⟨k, hk⟩ := hM
  obtain ⟨pB, hB⟩ := polF_qdet M.E (cn n)
  let L := liftL M.V (Fin n)
  let pC := pB.map (L : Module.End ℂ M.V →+* Module.End ℂ (Fin n → M.V))
  have hC : ∀ y : ℂ, pC.eval (algebraMap ℂ _ y) = (qdet M.E (y + cn n)).compLeft (Fin n) := fun y => by
    have h := eval_map_hom (L : Module.End ℂ M.V →+* Module.End ℂ (Fin n → M.V)) pB (algebraMap ℂ _ y)
    have hL : (L : Module.End ℂ M.V →+* Module.End ℂ (Fin n → M.V)) (algebraMap ℂ _ y) = algebraMap ℂ _ y :=
      L.commutes y
    rw [hL, hB] at h
    exact h
  have hroot := root H M (cn n) pC hC
  let Q0 : ℂ[X] := (List.ofFn fun i => X + C (χ i)).prod
  let Q : (Module.End ℂ (Fin n → M.V))[X] := Q0.map (algebraMap ℂ _)
  have hQ : ∀ x, Q.eval x = (List.ofFn fun i => x + algebraMap ℂ _ (χ i)).prod := by
    intro x
    rw [eval_map_algebraMap, map_list_prod]
    simp [List.map_ofFn, Function.comp_def]
  have hQy : ∀ y : ℂ, Q.eval (algebraMap ℂ _ y) = Formalism.QuantumDeterminants.capP χ y • (1 : Module.End ℂ (Fin n → M.V)) := by
    intro y
    rw [hQ]
    simp only [← map_add]
    rw [← Algebra.algebraMap_eq_smul_one]
    have h := map_list_prod (algebraMap ℂ (Module.End ℂ (Fin n → M.V))) (List.ofFn fun i => y + χ i)
    rw [List.map_ofFn] at h
    simp only [Function.comp_def] at h
    rw [← h, List.prod_ofFn]
    rfl
  have hDy : ∀ y : ℂ, (pC - Q).eval (algebraMap ℂ _ y) =
      L (qdet M.E (y + cn n) - Formalism.QuantumDeterminants.capP χ y • (1 : Module.End ℂ M.V)) := by
    intro y
    rw [eval_sub, hC, hQy, map_sub, map_smul, map_one]
    rfl
  have hDk : (pC - Q) ^ k = 0 := eq_zero_of_eval _ fun y => by
    rw [eval_pow_of_commute _ _ (fun j => commute_alg _ y), hDy, ← map_pow]
    have h := hk y
    have h' : (qdet M.E (y + cn n) - Formalism.QuantumDeterminants.capP χ y • (1 : Module.End ℂ M.V)) ^ k = 0 := h
    rw [h', map_zero]
  have hCom : ∀ j, Commute ((pC - Q).coeff j) (-om M - algebraMap ℂ _ (cn n)) := by
    intro j
    have h1 : Commute (pC.coeff j) (om M) := commute_coeff_om M pC
      (fun y => by rw [hC]; exact commute_qdet_om M _) j
    have h2 : Commute (pC.coeff j) (-om M - algebraMap ℂ _ (cn n)) :=
      h1.neg_right.sub_right (commute_alg _ _)
    have h3 : ∀ z, Commute (algebraMap ℂ (Module.End ℂ (Fin n → M.V)) (Q0.coeff j)) z :=
      fun z => Algebra.commutes _ z
    rw [coeff_sub]
    refine h2.sub_left ?_
    simp only [Q, coeff_map]
    exact h3 _
  have hz := congrArg (eval (-om M - algebraMap ℂ _ (cn n))) hDk
  rw [eval_pow_of_commute _ _ hCom, eval_zero, eval_sub, hroot, hQ, zero_sub] at hz
  have hf : (fun i => -om M - algebraMap ℂ _ (cn n) + algebraMap ℂ _ (χ i)) =
      fun i => (-1 : ℂ) • (om M - (χ i - cn n) • (1 : Module.End ℂ (Fin n → M.V))) := by
    funext i
    rw [neg_sub_algebra_map_smul_identity]
  rw [hf, prod_smul_ofFn, ← neg_smul, _root_.smul_pow] at hz
  exact ⟨k, (smul_eq_zero.1 hz).resolve_left
    (pow_ne_zero _ (neg_ne_zero.2 (pow_ne_zero _ (by norm_num))))⟩
end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
