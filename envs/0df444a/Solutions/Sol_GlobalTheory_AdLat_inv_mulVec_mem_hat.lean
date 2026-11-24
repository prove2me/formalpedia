-- Prove2me | solution 1 for GlobalTheory.AdLat.inv_mulVec_mem_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:19.645108+00:00
-- url     : https://prove2.me/submissions/b0f5c103-0975-4479-af2a-ad9e5f0fd707

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_det_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_cramer_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_algEquiv_mem_one
import Theorems.Thm_GlobalTheory_AdLat_adCoord_sum
import Theorems.Thm_GlobalTheory_AdLat_adelicCompletion_fractionalIdeal_properties
import Theorems.Thm_GlobalTheory_AdLat_galoisAut_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_mem_adelicCompletion_mul_inv_fractionalIdeal
import Theorems.Thm_GlobalTheory_AdLat_mem_hat_pseudoBasis_iff
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_exists_pseudoBasis_adapted


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (c : E ≃ₐ[F] E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ z ∈ (hat F (L : Set (Fin n → E))), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E)))) → (g : Matrix (Fin n) (Fin n) (RA F E)).det * sg (FiniteAdeleRing (𝓞 F) F) c (g : Matrix (Fin n) (Fin n) (RA F E)).det = 1 → ∀ z ∈ (hat F (L : Set (Fin n → E))), ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L g c hfg hsp hg hdet z hz
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG
  let k : Matrix (Fin n) (Fin n) (RA F E) := Q * G * P
  have hPk : P * k = G * P := by
    simp only [k, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : k.det = G.det := by
    have : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    simp only [k, Matrix.det_mul]
    linear_combination G.det * this
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hg _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  have hd : G.det ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    have := det_mem_adelicCompletionOfElementSet F cI (fun j => (cI j)⁻¹) k hk
    rwa [← Finset.prod_mul_distrib, Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i),
      hkdet] at this
  have hd' := galoisAut_mem_adelicCompletionOfElementSet F c (algEquiv_mem_one F c) hd
  have hw : ∀ a, (Q *ᵥ z) a ∈ hat1 F (cI a : Set E) := by
    rw [← key', Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    exact hz
  have hu : P *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c G.det • k.cramer (Q *ᵥ z)) ∈
      hat F (L : Set (Fin n → E)) := by
    rw [key']
    intro a
    have := (adelicCompletion_fractionalIdeal_properties F E).1 1 (cI a) _ hd' _ (cramer_mem_adelicCompletionOfElementSet F cI hc k hk _ hw a)
    rwa [one_mul] at this
  have hz' : G *ᵥ (P *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c G.det • k.cramer (Q *ᵥ z))) = z := by
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_cramer, smul_smul, hkdet, mul_comm, hdet, one_smul, Matrix.mulVec_mulVec, hPQ,
      Matrix.one_mulVec]
  rw [← hz', Matrix.mulVec_mulVec, hG, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]
  exact hu
end GlobalTheory.AdLat
