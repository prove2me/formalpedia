-- Prove2me | solution 1 for GlobalTheory.QNorm.index_locSq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:50.959611+00:00
-- url     : https://prove2.me/submissions/24ebc941-15dc-4855-a3eb-1317f78c6f71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdAbsNormPowValuationTwoLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardRingHomRealEqNrRealPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
import Theorems.Thm_GlobalTheory_QNorm_index_sqSub_real_dvd_two
import Theorems.Thm_GlobalTheory_QNorm_exists_valuation_two_eq_exp
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_T_index_unitsSquareUnderRingHom_adicCompletion_le
import Theorems.Thm_GlobalTheory_T_prod_absNorm_pow_valuation_two_le
import Theorems.Thm_P2M_GlobalTheory_T_card_ringHom_real_eq_nrRealPlaces__cec122734711
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
private theorem index_biInf_ne_zero_and_le_prod {G ι : Type} [Group G] [DecidableEq ι] (S : Finset ι)
    (f : ι → Subgroup G) :
    (∀ i ∈ S, (f i).index ≠ 0) →
      (⨅ i ∈ S, f i).index ≠ 0 ∧ (⨅ i ∈ S, f i).index ≤ ∏ i ∈ S, (f i).index := by
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp
  · intro a s ha ih hf
    rw [Finset.iInf_insert, Finset.prod_insert ha]
    obtain ⟨h0, hle⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha0 := hf a (Finset.mem_insert_self a s)
    exact ⟨Subgroup.index_inf_ne_zero ha0 h0,
      Subgroup.index_inf_le.trans (Nat.mul_le_mul_left _ hle)⟩
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  classical
  choose e he using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_two_eq_exp v
  have hP := GlobalTheory.T.prod_absNorm_pow_valuation_two_le F S e (fun v _ => he v)
  have hN : ∀ v : HeightOneSpectrum (𝓞 F),
      (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e v :=
    fun v => GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le F v (e v) (he v)
  obtain ⟨hF0, hFle⟩ := index_biInf_ne_zero_and_le_prod S (fun v => sqSub (algebraMap F (v.adicCompletion F)))
    (fun v _ => (hN v).1)
  have hR2 : ∀ σ : F →+* ℝ, (sqSub σ).index ≤ 2 := fun σ =>
    Nat.le_of_dvd two_pos (index_sqSub_real_dvd_two σ)
  obtain ⟨hR0, hRle⟩ := index_biInf_ne_zero_and_le_prod (Finset.univ : Finset (F →+* ℝ)) (fun σ => sqSub σ)
    (fun σ _ => ne_zero_of_dvd_ne_zero two_ne_zero (index_sqSub_real_dvd_two σ))
  have hRu : (⨅ σ : F →+* ℝ, sqSub σ) = ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    simp
  have hloc : locSq F S = (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))) ⊓
      ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    rw [← hRu]
    rfl
  rw [hloc]
  refine ⟨Subgroup.index_inf_ne_zero hF0 hR0, ?_⟩
  have hF : (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))).index ≤
      4 ^ S.card * 2 ^ Module.finrank ℚ F := by
    refine hFle.trans ?_
    calc ∏ v ∈ S, (sqSub (algebraMap F (v.adicCompletion F))).index
        ≤ ∏ v ∈ S, (4 * Ideal.absNorm v.asIdeal ^ e v) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun v _ => (hN v).2)
      _ = 4 ^ S.card * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 4 ^ S.card * 2 ^ Module.finrank ℚ F := Nat.mul_le_mul_left _ hP
  have hR : (⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ).index ≤
      2 ^ InfinitePlace.nrRealPlaces F := by
    refine hRle.trans ?_
    calc ∏ σ ∈ (Finset.univ : Finset (F →+* ℝ)), (sqSub σ).index
        ≤ ∏ _σ ∈ (Finset.univ : Finset (F →+* ℝ)), 2 :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun σ _ => hR2 σ)
      _ = 2 ^ InfinitePlace.nrRealPlaces F := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card, GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces' F]
  refine Subgroup.index_inf_le.trans ((Nat.mul_le_mul hF hR).trans (le_of_eq ?_))
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    ← InfinitePlace.card_add_two_mul_card_eq_rank, show (4 : ℕ) = 2 ^ 2 by norm_num]
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring
end GlobalTheory.QNorm
