-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_idele_not_mul_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:40.870694+00:00
-- url     : https://prove2.me/submissions/ba9a3c8b-71d7-4a9a-89a8-353800c90a6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNorm
import Theorems.Thm_GlobalTheory_QNorm_exists_adele_finite_component
import Theorems.Thm_GlobalTheory_QNorm_exists_infiniteAdele_real_component
import Theorems.Thm_GlobalTheory_QNorm_adeleOn_snd_of_mem
import Theorems.Thm_GlobalTheory_QNorm_adeleOn_snd_of_notMem
import Theorems.Thm_GlobalTheory_QNorm_adeleOn_mul_inv
import Theorems.Thm_GlobalTheory_QNorm_div_mem_normSub
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_QNorm_normSub_id_le_locNorm
import Theorems.Thm_GlobalTheory_QNorm_sUnits_sup_locNorm_ne_top
import Theorems.Thm_GlobalTheory_T_exists_admissible_localNorm_mem_sUnits_sup_globalNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  intro F _ _ δ hsq
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hsq IsSquare.zero
  obtain ⟨S, hS, hδ, hadj⟩ := GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm F (Units.mk0 δ hδ0) hsq
  have hne := sUnits_sup_locNorm_ne_top F (Units.mk0 δ hδ0) S hS hδ hsq
  simp only [Units.val_mk0] at hadj hne
  obtain ⟨z, hz⟩ : ∃ z : Fˣ, z ∉ sUnits F S ⊔ locNorm F δ S := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_top_iff' _ |>.2 hcon)
  refine ⟨Units.mkOfMulEqOne _ _ (adeleOn_mul_inv F S z.ne_zero), fun t x y h => hz ?_⟩
  replace h : adeleOn F S z = algebraMap F (AdeleRing (𝓞 F) F) t *
      (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := h
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at h
    have h1 : algebraMap F (InfiniteAdeleRing F) z = 0 := congrArg Prod.fst h
    exact z.ne_zero ((map_eq_zero _).1 h1)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F,
      (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) t *
        (a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) := by
    intro v
    obtain ⟨e, he, he'⟩ := exists_adele_finite_component F v
    refine ⟨e x, e y, ?_⟩
    rw [← he, h, map_mul, map_sub, map_mul, map_pow, map_pow, he', he']
  have h1 : Units.mk0 t ht ∈ sUnits F S ⊔ locNorm F δ S := by
    refine sup_le_sup_left (normSub_id_le_locNorm F δ S) _ (hadj _ fun v hv => ?_)
    obtain ⟨a, b, hab⟩ := hfin v
    rw [adeleOn_snd_of_notMem F S _ hv] at hab
    have h2 := div_mem_normSub (algebraMap F (v.adicCompletion F)) δ 1 (Units.mk0 t ht) a b
      (by simpa using hab)
    rwa [one_div, inv_mem_iff] at h2
  have h2 : z / Units.mk0 t ht ∈ locNorm F δ S := by
    refine ⟨Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_,
      Subgroup.mem_iInf.2 fun σ => ?_⟩
    · obtain ⟨a, b, hab⟩ := hfin v
      rw [adeleOn_snd_of_mem F S _ hv] at hab
      exact div_mem_normSub _ δ z (Units.mk0 t ht) a b hab
    · obtain ⟨e, he⟩ := exists_infiniteAdele_real_component F σ
      refine div_mem_normSub σ δ z (Units.mk0 t ht) (e x.1) (e y.1) ?_
      have h3 : algebraMap F (InfiniteAdeleRing F) z = algebraMap F (InfiniteAdeleRing F) t *
          (x.1 ^ 2 - algebraMap F (InfiniteAdeleRing F) δ * y.1 ^ 2) := congrArg Prod.fst h
      have h4 := congrArg e h3
      rwa [map_mul, map_sub, map_mul, map_pow, map_pow, he, he, he] at h4
  have h3 := mul_mem (Subgroup.mem_sup_right (S := sUnits F S) h2) h1
  rwa [div_mul_cancel] at h3
end GlobalTheory.QNorm
