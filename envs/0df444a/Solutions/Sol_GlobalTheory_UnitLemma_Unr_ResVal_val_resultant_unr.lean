-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:21.288329+00:00
-- url     : https://prove2.me/submissions/ead327da-4f6f-4f19-9a83-6779ce6a6de5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerMapIsIntegralUnramifiedInvolutionExStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGeneratesUnramifiedExtResidueFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_int_lift
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_val_norm
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_res_gen
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_res_mult
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_val_neg_one_pow
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_val_mul_unit
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_norm_res
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_charpoly_subsingleton
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_aeval_P
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_norm_tower
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_monic_dvd_pow
import Theorems.Thm_GlobalTheory_T_separable_charpoly_invAlgBaseChangeUnramified
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_charpoly_dvd_map_of_aeval_eq_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormValU_val_norm
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_Orbit_exists_monic_map_eq_charpoly__518c0881fa8f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResVal
namespace GlobalTheory.UnitLemma.Unr.ResVal
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B₁ B₂ : InvAlg K) (ψ₁ : K'.E →+* B₁.A) (ψ₂ : K'.E →+* B₂.A) (h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e) (h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e)) (h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e) (h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e)), (∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → (B₁.P * B₂.P).Separable → ∀ s : K'.O, (∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B₁ ψ₁ h₁ h₁').P * (overExt φ B₂ ψ₂ h₂ h₂').P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree) → val K.O (resultant B₁.P B₂.P) = d * val K'.O (resultant (overExt φ B₁ ψ₁ h₁ h₁').P (overExt φ B₂ ψ₂ h₂ h₂').P) := by
  intro K K' d φ hU _ B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO hsep s ⟨Q, hQ, hQr⟩
  set B₁' := overExt φ B₁ ψ₁ h₁ h₁' with hB₁'
  set B₂' := overExt φ B₂ ψ₂ h₂ h₂' with hB₂'
  by_cases t₁ : Subsingleton B₁.A
  · have e1 : B₁.P = 1 := charpoly_subsingleton B₁.g
    haveI : Subsingleton B₁'.A := t₁
    have e1' : B₁'.P = 1 := charpoly_subsingleton (E := K'.E) (A := B₁'.A) B₁'.g
    simp [e1, e1', val]
  by_cases t₂ : Subsingleton B₂.A
  · have e2 : B₂.P = 1 := charpoly_subsingleton B₂.g
    haveI : Subsingleton B₂'.A := t₂
    have e2' : B₂'.P = 1 := charpoly_subsingleton (E := K'.E) (A := B₂'.A) B₂'.g
    simp [e2, e2', val]
  haveI : Nontrivial B₁.A := not_subsingleton_iff_nontrivial.1 t₁
  haveI : Nontrivial B₂.A := not_subsingleton_iff_nontrivial.1 t₂
  have hPm₁ : B₁'.P.Monic := LinearMap.charpoly_monic _
  have hPm₂ : B₂'.P.Monic := LinearMap.charpoly_monic _
  have hinj' := IsFractionRing.injective K'.O K'.E
  have hinj := IsFractionRing.injective K.O K.E
  have hQm : Q.Monic := monic_of_injective hinj' (by rw [hQ]; exact hPm₁.mul hPm₂)
  obtain ⟨r₁, hr₁⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K'.E hQm
    (show B₁'.P ∣ Q.map (algebraMap K'.O K'.E) by rw [hQ]; exact dvd_mul_right _ _)
  obtain ⟨r₂, hr₂⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K'.E hQm
    (show B₂'.P ∣ Q.map (algebraMap K'.O K'.E) by rw [hQ]; exact dvd_mul_left _ _)
  rw [hPm₁.leadingCoeff, C_1, mul_one] at hr₁
  rw [hPm₂.leadingCoeff, C_1, mul_one] at hr₂
  have hr₁m : r₁.Monic := monic_of_injective hinj' (by rw [hr₁]; exact hPm₁)
  have hr₂m : r₂.Monic := monic_of_injective hinj' (by rw [hr₂]; exact hPm₂)
  have hQr₁₂ : Q = r₁ * r₂ := Polynomial.map_injective _ hinj' (by rw [hQ, Polynomial.map_mul, hr₁, hr₂])
  have hres : ∀ r : K'.O[X], r.Monic → r ∣ Q →
      r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree := by
    intro r hr hrQ
    have := monic_dvd_pow _ _ _ (hr.map _) (hQr ▸ Polynomial.map_dvd _ hrQ)
    rwa [hr.natDegree_map] at this
  have hr₁r := hres r₁ hr₁m (by rw [hQr₁₂]; exact dvd_mul_right _ _)
  have hr₂r := hres r₂ hr₂m (by rw [hQr₁₂]; exact dvd_mul_left _ _)
  obtain ⟨φO, hφO, hint⟩ := int_lift K K' d φ hU
  have hφc : (algebraMap K'.O K'.E).comp φO = φ.comp (algebraMap K.O K.E) := RingHom.ext hφO
  have hg₂ : IsIntegral K.O B₂.g := by
    letI : Algebra K.O K'.O := φO.toAlgebra
    letI : Algebra K'.O B₂.A := (ψ₂.comp (algebraMap K'.O K'.E)).toAlgebra
    haveI : IsScalarTower K.O K'.O B₂.A := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap K.O B₂.A x = ψ₂ (algebraMap K'.O K'.E (φO x))
      rw [hφO, h₂, ← IsScalarTower.algebraMap_apply]
    haveI : Algebra.IsIntegral K.O K'.O := hint
    have h2 : IsIntegral K'.O B₂.g := ⟨r₂, hr₂m, by
      change eval₂ (ψ₂.comp (algebraMap K'.O K'.E)) B₂.g r₂ = 0
      rw [← eval₂_map, hr₂]
      exact aeval_P B₂'⟩
    exact isIntegral_trans (R := K.O) _ h2
  have hs₂ : B₂.P.Separable := hsep.of_mul_right
  obtain ⟨p₂, hp₂m, hp₂⟩ := GlobalTheory.UnitLemma.Orbit.exists_monic_map_eq_charpoly₂ B₂ hs₂ hg₂
  have hs₂' : B₂'.P.Separable := GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified K K' d φ hU B₂ ψ₂ h₂ h₂' hs₂
  have hcomp : ∀ (A : Type) [CommRing A] [Algebra K.E A] [Algebra K.O A] [IsScalarTower K.O K.E A] (ψ : K'.E →+* A),
      (∀ e, ψ (φ e) = algebraMap K.E A e) → (ψ.comp (algebraMap K'.O K'.E)).comp φO = algebraMap K.O A := by
    intro A _ _ _ _ ψ hψ
    ext x
    simp [hφO, hψ, ← IsScalarTower.algebraMap_apply]
  have hf0 : aeval B₂'.g (p₂.map φO) = 0 := by
    change eval₂ (ψ₂.comp (algebraMap K'.O K'.E)) B₂.g (p₂.map φO) = 0
    rw [eval₂_map, hcomp B₂.A ψ₂ h₂, ← aeval_def, ← aeval_map_algebraMap K.E, hp₂]
    exact aeval_P B₂
  obtain ⟨c', hc'⟩ := GlobalTheory.UnitLemma.Orbit.charpoly_dvd_map_of_aeval_eq_zero B₂' hs₂' _ hf0
  have hfm : (p₂.map φO).Monic := hp₂m.map _
  have hc'm : c'.Monic := hPm₂.of_mul_monic_left (by rw [← hc']; exact hfm.map _)
  obtain ⟨c₂, hc₂⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K'.E hfm
    (show c' ∣ (p₂.map φO).map (algebraMap K'.O K'.E) from ⟨B₂'.P, by rw [hc', mul_comm]⟩)
  rw [hc'm.leadingCoeff, C_1, mul_one] at hc₂
  have hfrc : p₂.map φO = r₂ * c₂ :=
    Polynomial.map_injective _ hinj' (by rw [hc', Polynomial.map_mul, hr₂, hc₂])
  have hgen := res_gen K K' d φ hU (B₁.prod B₂) (ψ₁.prod ψ₂) (fun e => Prod.ext (h₁ e) (h₂ e)) (show Nontrivial (B₁.A × B₂.A) from inferInstance)
    hO s Q hQm (by
      show (eval₂ ((ψ₁.prod ψ₂).comp (algebraMap K'.O K'.E)) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q : B₁.A × B₂.A) = 0
      refine Prod.ext ?_ ?_
      · change (RingHom.fst B₁.A B₂.A) (eval₂ ((ψ₁.prod ψ₂).comp (algebraMap K'.O K'.E)) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q) = 0
        rw [hom_eval₂]
        change eval₂ (ψ₁.comp (algebraMap K'.O K'.E)) B₁.g Q = 0
        rw [← eval₂_map, hQ, eval₂_mul]
        have h0 : eval₂ ψ₁ B₁.g B₁'.P = 0 := aeval_P B₁'
        rw [h0, zero_mul]
      · change (RingHom.snd B₁.A B₂.A) (eval₂ ((ψ₁.prod ψ₂).comp (algebraMap K'.O K'.E)) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q) = 0
        rw [hom_eval₂]
        change eval₂ (ψ₂.comp (algebraMap K'.O K'.E)) B₂.g Q = 0
        rw [← eval₂_map, hQ, eval₂_mul]
        have h0 : eval₂ ψ₂ B₂.g B₂'.P = 0 := aeval_P B₂'
        rw [h0, mul_zero]) hQr
  have hdeg : p₂.natDegree = d * r₂.natDegree := by
    have a1 : p₂.natDegree = Module.finrank K.E B₂.A := by
      rw [← natDegree_map_eq_of_injective hinj p₂, hp₂]; exact LinearMap.charpoly_natDegree _
    have a2 : r₂.natDegree = @Module.finrank K'.E B₂.A _ _ ψ₂.toAlgebra.toModule := by
      rw [← natDegree_map_eq_of_injective hinj' r₂, hr₂]; exact LinearMap.charpoly_natDegree _
    rw [a1, a2, ← hU.2.2.2.2]
    letI : Algebra K.E K'.E := φ.toAlgebra
    letI : Algebra K'.E B₂.A := ψ₂.toAlgebra
    haveI : IsScalarTower K.E K'.E B₂.A := IsScalarTower.of_algebraMap_eq fun e => (h₂ e).symm
    exact (Module.finrank_mul_finrank K.E K'.E B₂.A).symm
  have hmap : p₂.map (φ.comp (algebraMap K.O K.E)) = (r₂ * c₂).map (algebraMap K'.O K'.E) := by
    rw [← hfrc, Polynomial.map_map, hφc]
  have hnr := res_mult K K' d φ hU s hgen p₂ r₂ c₂ hp₂m hr₂m hr₂r hdeg hmap
  have hu : IsUnit (resultant c₂ r₁) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← resultant_map_map, hr₁r,
      resultant_X_sub_C_pow_right _ _ _ _ natDegree_map_le]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (pow_ne_zero _ hnr)
  obtain ⟨k₁, hk₁⟩ := norm_res B₁.g B₂.P (LinearMap.charpoly_monic _)
  have hk₁' : Algebra.norm K.E (aeval B₁.g B₂.P) = (-1) ^ k₁ * resultant B₂.P B₁.P := hk₁
  obtain ⟨k₂, hk₂⟩ := norm_res (E := K'.E) (A := B₁'.A) B₁'.g ((p₂.map φO).map (algebraMap K'.O K'.E)) (hfm.map _)
  have e : (aeval B₁'.g ((p₂.map φO).map (algebraMap K'.O K'.E)) : B₁.A) = aeval B₁.g B₂.P := by
    change eval₂ ψ₁ B₁.g ((p₂.map φO).map (algebraMap K'.O K'.E)) = _
    rw [Polynomial.map_map, eval₂_map, ← hp₂, aeval_map_algebraMap, aeval_def, ← RingHom.comp_assoc,
      hcomp B₁.A ψ₁ h₁]
  have hk₂' : @Algebra.norm K'.E B₁.A _ _ ψ₁.toAlgebra (aeval B₁.g B₂.P) =
      (-1) ^ k₂ * resultant (B₂'.P * c₂.map (algebraMap K'.O K'.E)) B₁'.P := by
    rw [← e, hc₂, ← hc']; exact hk₂
  have hmul := resultant_mul_left B₂'.P (c₂.map (algebraMap K'.O K'.E)) B₁'.P B₁'.P.natDegree le_rfl
  rw [← hPm₂.natDegree_mul (by rw [hc₂]; exact hc'm)] at hmul
  have hcu : resultant (c₂.map (algebraMap K'.O K'.E)) B₁'.P = algebraMap K'.O K'.E (resultant c₂ r₁) := by
    rw [← hr₁, natDegree_map_eq_of_injective hinj', natDegree_map_eq_of_injective hinj', resultant_map_map]
  calc val K.O (resultant B₁.P B₂.P) = val K.O (resultant B₂.P B₁.P) := by
        rw [resultant_comm, val_neg_one_pow]
    _ = val K.O (Algebra.norm K.E (aeval B₁.g B₂.P)) := by rw [hk₁', val_neg_one_pow]
    _ = d * val K'.O (@Algebra.norm K'.E B₁.A _ _ ψ₁.toAlgebra (aeval B₁.g B₂.P)) := by
        rw [norm_tower φ B₁ ψ₁ h₁, val_norm K K' d φ hU]
    _ = d * val K'.O (resultant B₂'.P B₁'.P) := by
        rw [hk₂', val_neg_one_pow, hmul, hcu, val_mul_unit _ _ hu]
    _ = d * val K'.O (resultant B₁'.P B₂'.P) := by
        rw [resultant_comm B₂'.P, val_neg_one_pow]
end GlobalTheory.UnitLemma.Unr.ResVal
