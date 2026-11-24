-- Prove2me | solution 1 for GlobalTheory.QNorm.two_pow_le_index_locNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:51.993273+00:00
-- url     : https://prove2.me/submissions/2e3d842c-47e6-4b77-990e-045544b03a44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowCardLeIndexIInfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquaresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtension
import Theorems.Thm_GlobalTheory_QNorm_norm_of_isSquare_mul
import Theorems.Thm_GlobalTheory_QNorm_mem_normSub_real_of_pos
import Theorems.Thm_GlobalTheory_QNorm_locSq_le_locNorm_of_delta
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_QNorm_sqSub_le_normSub
import Theorems.Thm_GlobalTheory_T_exists_approx_mod_local_squares
import Theorems.Thm_GlobalTheory_T_exists_local_nonnorm_of_nonsquare_adicCompletion
import Theorems.Thm_GlobalTheory_T_index_unitsLocalSquaresFiniteRealPlaces_le
import Theorems.Thm_GlobalTheory_T_two_pow_card_le_index_iInf_of_independent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))),
      δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧
        2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by
  intro F _ _ δ S hδ
  classical
  have h0 : (locNorm F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le F S).1
      (Subgroup.index_dvd_of_le (locSq_le_locNorm_of_delta F δ S))
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ)} with hA
  set B : Set (F →+* ℝ) := {σ | σ δ < 0} with hB
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  have hBf : B.Finite := Set.toFinite _
  letI : Fintype A := hAf.fintype
  letI : Fintype B := hBf.fintype
  let K : A ⊕ B → Subgroup Fˣ := Sum.elim
    (fun v => normSub (algebraMap F (v.1.adicCompletion F)) δ) (fun σ => normSub σ.1 δ)
  have hle : locNorm F δ S ≤ ⨅ i, K i := by
    refine le_iInf ?_
    rintro (v | σ)
    · exact inf_le_left.trans (iInf₂_le v.1 v.2.1)
    · exact inf_le_right.trans (iInf_le _ σ.1)
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card (A ⊕ B) = tFin F δ S + tReal F δ := by
    rw [Fintype.card_sum, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (GlobalTheory.T.two_pow_card_le_index_iInf_of_independent Fˣ (A ⊕ B) K ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  rintro (v | σ)
  · obtain ⟨y, hy0, hy⟩ := GlobalTheory.T.exists_local_nonnorm_of_nonsquare_adicCompletion F v.1 (algebraMap F _ δ) (by simpa using hδ) v.2.2
    obtain ⟨x, hx0, hxv, hxσ⟩ := GlobalTheory.T.exists_approx_mod_local_squares F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1 y)
      (fun _ => 1) (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simpa using hy0
        · simp [Function.update_of_ne hw]) (by simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      have h1 := hxv v.1 v.2.1
      rw [Function.update_self] at h1
      exact hy (norm_of_isSquare_mul (by simpa using hx0) h1 hm)
    · rintro (w | τ) hj
      · have hw : w.1 ≠ v.1 := fun h => hj (congrArg Sum.inl (Subtype.ext h))
        have h1 := hxv w.1 w.2.1
        rw [Function.update_of_ne hw, mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · exact mem_normSub_real_of_pos _ _ _ (by simpa using hxσ τ.1)
  · obtain ⟨x, hx0, hxv, hxσ⟩ := GlobalTheory.T.exists_approx_mod_local_squares F S (fun _ => 1)
      (fun τ => if τ = σ.1 then -1 else 1) (by simp) (by
        intro τ
        split_ifs <;> simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · rintro ⟨a, b, hab⟩
      have h1 := hxσ σ.1
      have h2 : σ.1 δ < 0 := σ.2
      simp only [if_true] at h1
      have h3 : σ.1 x = a ^ 2 - σ.1 δ * b ^ 2 := hab
      nlinarith [sq_nonneg a, mul_nonneg (neg_nonneg.2 h2.le) (sq_nonneg b)]
    · rintro (w | τ) hj
      · have h1 := hxv w.1 w.2.1
        rw [mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · have hw : τ.1 ≠ σ.1 := fun h => hj (congrArg Sum.inr (Subtype.ext h))
        exact mem_normSub_real_of_pos _ _ _ (by simpa [hw] using hxσ τ.1)
end GlobalTheory.QNorm
