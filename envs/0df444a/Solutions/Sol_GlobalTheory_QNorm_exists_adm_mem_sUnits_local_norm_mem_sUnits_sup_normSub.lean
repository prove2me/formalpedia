-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:56:13.271302+00:00
-- url     : https://prove2.me/submissions/adf0fb65-df32-48ba-b620-1e5967fbdec7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenNormsOfUnitNonsquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits_sup_of_local_orders
import Theorems.Thm_GlobalTheory_QNorm_exists_norm_uniformizer_of_split
import Theorems.Thm_GlobalTheory_QNorm_admitted_mono
import Theorems.Thm_GlobalTheory_QNorm_evenNorms_of_odd_place
import Theorems.Thm_GlobalTheory_QNorm_exists_admissible_superset_finite_places
import Theorems.Thm_GlobalTheory_QNorm_exists_isQuad
import Theorems.Thm_GlobalTheory_QNorm_exists_superset_mem_sUnits
import Theorems.Thm_GlobalTheory_QNorm_mem_normSub
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits
import Theorems.Thm_GlobalTheory_QNorm_places_over


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ), ¬ IsSquare (δ : F) →
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), admitted F S ∧ δ ∈ sUnits F S ∧ ∀ t : Fˣ,
        (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
          t ∈ normSub (algebraMap F (v.adicCompletion F)) (δ : F)) →
        t ∈ sUnits F S ⊔ normSub (RingHom.id F) (δ : F) := by
  classical
  intro F _ _ δ hδ
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := exists_isQuad F δ hδ
  obtain ⟨T, -, hT⟩ := exists_admissible_superset_finite_places E ∅
  obtain ⟨S₁, hS₁, hS₁'⟩ := exists_superset_mem_sUnits F {δ} (T.image (fun w => w.under (𝓞 F)))
  obtain ⟨S, hS, hadm⟩ := exists_admissible_superset_finite_places F S₁
  have hδS : δ ∈ sUnits F S := hS₁' S hS δ (by simp)
  obtain ⟨SE, hSE⟩ := (places_over F E).1 S
  have hadmE : admitted E SE := hT.mono (fun w hw =>
    (hSE w).2 (hS (hS₁ (Finset.mem_image_of_mem _ hw))))
  refine ⟨S, hadm, hδS, fun t ht => ?_⟩
  refine mem_sUnits_sup_of_local_orders S _ t (fun v hv => ?_)
  have ht0 : v.valuation F (t : F) ≠ 0 := by simp
  by_cases hsq : IsSquare (algebraMap F (v.adicCompletion F) δ)
  · obtain ⟨a, b, h1, h2⟩ := exists_norm_uniformizer_of_split hq S SE hadm hadmE hSE
      ((mem_sUnits F S δ).1 hδS) v hv hsq
    have h0 : a ^ 2 - δ * b ^ 2 ≠ 0 := by
      intro h
      rw [h, map_zero] at h1
      exact WithZero.exp_ne_zero h1.symm
    refine ⟨(Units.mk0 _ h0) ^ (-(WithZero.log (v.valuation F (t : F)))),
      Subgroup.zpow_mem _ ((mem_normSub _ _ _).2 ⟨a, b, rfl⟩) _, ?_, ?_⟩
    · rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, h1, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log ht0]
    · intro u hu huv
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, h2 u hu huv, one_zpow]
  · obtain ⟨h2, π, hπ, hπ'⟩ := hadm v hv
    have hval : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
      fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    have hev := evenNorms_of_odd_place F v
      (by have := hval 2; rwa [map_ofNat, h2] at this) _
      ((hval _).trans ((mem_sUnits F S δ).1 hδS v hv)) hsq
    obtain ⟨a, b, hab⟩ := ht v hv
    obtain ⟨m, hm⟩ := hev a b (by
      by_contra hc
      push Not at hc
      rw [hc.1, hc.2] at hab
      simp at hab)
    rw [← hab, hval] at hm
    have hπ0 : π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    refine ⟨((Units.mk0 _ hπ0) ^ (-m)) ^ 2, ⟨π ^ (-m), 0, by simp⟩, ?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow,
        map_zpow₀, hπ, hm, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul]
      simp
    · intro u hu huv
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow,
        map_zpow₀, hπ' u hu huv, one_zpow, one_pow]
end GlobalTheory.QNorm
