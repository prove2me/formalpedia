-- Prove2me | solution 1 for GlobalTheory.GaugeDeriv.pderiv_hM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:54.065057+00:00
-- url     : https://prove2.me/submissions/a4b8ab8e-2a87-44a2-a148-66c47541ab5a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegral
import Theorems.Thm_GlobalTheory_GaugeDeriv_hPullW_eq
import Theorems.Thm_GlobalTheory_GaugeDeriv_hasSubst_linForm
import Theorems.Thm_GlobalTheory_GaugeDeriv_pderiv_hPullW
import Theorems.Thm_GlobalTheory_GaugeDeriv_constantCoeff_upG
import Theorems.Thm_GlobalTheory_GaugeDeriv_hPullW_toLeaf
import Theorems.Thm_GlobalTheory_GaugeDeriv_odd_val_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
namespace GlobalTheory.GaugeDeriv
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
variable {V : VF C} {d : ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]
private theorem hPullW_add (H H' : MvPowerSeries (WV I) C) (e : ι → WV I → C)
    (e' : ι' → WV I → C) :
    hPullW (H + H') e e' = hPullW H e e' + hPullW H' e e' := by
  rw [hPullW_eq, hPullW_eq, hPullW_eq, MvPowerSeries.subst_add (hasSubst_linForm e e')]
private theorem hPullW_sum_smul {κ : Type} [Fintype κ] (c : κ → C) (F : κ → MvPowerSeries (WV I) C)
    (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW (∑ q, c q • F q) e e' = ∑ q, c q • hPullW (F q) e e' := by
  simp only [hPullW_eq]
  rw [GlobalTheory.FormalCalc.subst_sum' (hasSubst_linForm e e')]
  simp only [MvPowerSeries.subst_smul (hasSubst_linForm e e')]
end GlobalTheory.GaugeDeriv
end
end

set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.GaugeDeriv
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
variable {V : VF C} {d : ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]
namespace GlobalTheory.GaugeDeriv
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → ∀ b : ι', ∃ γ : MvPowerSeries (WV I) C, (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧ MvPowerSeries.pderiv C (Sum.inr b) (X.hM g a i e v') = MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • hPullW (upG g ((S g).ze (t g) κ)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  intro C _ V d _ I J _ _ X hAlt g a i hi hid S t ht ι ι' _ _ e v' he hvint hv b
  have hΦ : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_upG w.1 ((ht w.1).1 w.2))
  have hLs := hasSubst_linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))
  have hK : ∀ k : I (1 - g), ∃ γ : MvPowerSeries (WV I) C,
      (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧
      v' b k • hPullW (dVar (⟨1 - g, k⟩ : WV I) (X.hL g a (a + (i : ZMod d))))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
        v' b k • hPullW (∑ κ : J g, X.pair g κ k • upG g ((S g).ze (t g) κ))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) +
        v' b k • hPullW (MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) γ)
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
    intro k
    by_cases hk : (X.G (1 - g)).ty (Sum.inl k) = a + (i : ZMod d)
    · obtain ⟨K, ⟨γ, hγ, rfl⟩, hEq⟩ :=
        X.C_eq hAlt g a (a + (i : ZMod d)) (odd_val_sub a hi hid) S t ht k hk
      refine ⟨γ, hγ, ?_⟩
      rw [sub_eq_iff_eq_add'] at hEq
      rw [hEq, hPullW_add, hPullW_toLeaf X.G g a _ e v' he hv,
        hPullW_toLeaf X.G g a _ e v' he hv, smul_add]
    · refine ⟨0, fun μ => ?_, ?_⟩
      · rw [map_zero]
        exact VF.Ge.zero 0
      · rw [hv b k hk]
        simp only [zero_smul, add_zero]
  choose γ hγint hγeq using hK
  refine ⟨∑ k, v' b k • γ k, ?_, ?_⟩
  · intro μ
    rw [map_sum]
    refine VF.Ge.sum (fun k _ => ?_)
    simp only [map_smul, smul_eq_mul]
    exact VF.Ge.mul_int (hvint b k) (hγint k μ)
  · unfold RowData.hM
    rw [pderiv_hPullW (X.hL g a (a + (i : ZMod d))) (fun c => toW g (e c)) (1 - g) v' b,
      Finset.sum_congr rfl (fun k _ => hγeq k), Finset.sum_add_distrib]
    refine (add_comm _ _).trans ?_
    congr 1
    · simp only [hPullW_eq]
      have hΨ : MvPowerSeries.HasSubst (fun w : WV I =>
          MvPowerSeries.subst (linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)))
            (upG w.1 (t w.1 w.2))) := by
        have h := hΦ.comp hLs
        simp only [MvPowerSeries.substAlgHom_apply] at h
        exact h
      rw [GlobalTheory.FormalCalc.subst_sum' hΨ]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [MvPowerSeries.subst_smul hΨ, MvPowerSeries.subst_comp_subst_apply hΦ hLs]
    · simp only [hPullW_sum_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun κ _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [mul_comm]
end GlobalTheory.GaugeDeriv
