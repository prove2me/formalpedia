-- Prove2me | solution 1 for GlobalTheory.GaugeDeriv.hPullW_toLeaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:25.817645+00:00
-- url     : https://prove2.me/submissions/e2cf1ad5-69ad-4c96-98ad-a1d082692f21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegral
import Theorems.Thm_GlobalTheory_GaugeDeriv_hPullW_eq
import Theorems.Thm_GlobalTheory_GaugeDeriv_constantCoeff_linForm
import Theorems.Thm_GlobalTheory_subst_eq_of_coeff_eq_of_killed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.GaugeDeriv
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
variable {V : VF C} {d : ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]
namespace GlobalTheory.GaugeDeriv
theorem _root_.solution (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (a a' : ZMod d)
    (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b k, (G (1 - g)).ty (Sum.inl k) ≠ a' → v' b k = 0) (F : MvPowerSeries (WV I) C) :
    hPullW (toLeaf G g a a' F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
      hPullW F (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  rw [hPullW_eq, hPullW_eq]
  apply GlobalTheory.subst_eq_of_coeff_eq_of_killed C (WV I) (ι ⊕ ι') (OnLeafV G g a a')
  · exact constantCoeff_linForm _ _
  · rintro ⟨w1, w2⟩ hw
    have h1 : ∀ c, toW g (e c) ⟨w1, w2⟩ = 0 := by
      intro c
      by_cases h : w1 = g
      · subst h
        simp only [toW]
        exact he c w2 (fun hty => hw (Or.inl ⟨rfl, hty⟩))
      · simp [toW, h]
    have h2 : ∀ b, toW (1 - g) (v' b) ⟨w1, w2⟩ = 0 := by
      intro b
      by_cases h : w1 = 1 - g
      · subst h
        simp only [toW]
        exact hv b w2 (fun hty => hw (Or.inr ⟨rfl, hty⟩))
      · simp [toW, h]
    simp [linForm, h1, h2]
  · intro μ hμ
    rw [show MvPowerSeries.coeff μ (toLeaf G g a a' F) = toLeaf G g a a' F μ from rfl]
    unfold toLeaf
    exact if_pos hμ
end GlobalTheory.GaugeDeriv
