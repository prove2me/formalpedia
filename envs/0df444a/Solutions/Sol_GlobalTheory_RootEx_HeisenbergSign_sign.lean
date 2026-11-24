-- Prove2me | solution 1 for GlobalTheory.RootEx.HeisenbergSign.sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:46:59.738629+00:00
-- url     : https://prove2.me/submissions/99a4bba2-26f8-4155-b15b-7467f28977e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeHeisenbergVariableSign
import Theorems.Thm_GlobalTheory_RootEx_HeisenbergSign_colE_inv_eq
import Theorems.Thm_GlobalTheory_RootEx_HeisenbergSign_mat_add_gCol
import Theorems.Thm_GlobalTheory_RootEx_Exchange_affPt_eq
import Theorems.Thm_GlobalTheory_RootEx_Exchange_col_colE_inv_mul
import Theorems.Thm_GlobalTheory_RootEx_Exchange_om_colE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_opE_colE
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.HeisenbergSign
namespace GlobalTheory.RootEx.HeisenbergSign
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) (β : n → k) (r : n) (i : Fin (c + 1)), i.val + 1 = ρ + 1 → ((1 - ((colE c (ρ + 1) β).val - 1)) * affPt (ρ + 1) x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (Sum.inl r) (Sum.inr i) = -β r) ∧ ∀ (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (β : n → k), (∀ x, om μ 1 (colE c (ρ + 1) β) Φ.1 x = Φ.1 ((1 - ((colE c (ρ + 1) β).val - 1)) * x)) ∧ ∀ x₀, fl ψ ν μ ρ Φ.1 x₀ β = opE ψ ν (ρ + 1) (fun x => Φ.1 (x + colM c (ρ + 1) (-β))) x₀ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ρ _ hρc
  refine ⟨fun x₀ e β r i hi => ?_, fun ψ ν _ hψ μ Φ β => ⟨fun x => ?_, fun x₀ => ?_⟩⟩
  ·
    have hi' : i = Fin.castSucc (⟨ρ, hρc⟩ : Fin c) := Fin.ext (by simp; omega)
    subst hi'
    have h := congrFun (Exchange.col_colE_inv_mul (n' := n') (⟨ρ, hρc⟩ : Fin c) β x₀ e) r
    simp only at h
    rw [← colE_inv_eq]
    exact neg_eq_iff_eq_neg.mp h
  · rw [Exchange.om_colE, colE_inv_eq]
  ·
    have hch : ∀ (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (p : ℕ) (ξ : n → k),
        ch (y + colM c p ξ) = ch y := by
      intro y p ξ
      simp [ch, colM]
    have hmem : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
    have key := Exchange.opE_colE hψ ν μ (⟨ρ, hρc⟩ : Fin c) (⟨ρ, hρc⟩ : Fin c)
      (χ := fun _ => (1 : ℂ)) continuous_const hmem.1.continuous x₀ β
    dsimp only at key
    refine Eq.trans ?_ (key.trans ?_)
    · simp [fl]
    · rw [opE]
      congr 1
      funext e
      rw [mat_add_gCol, ← Exchange.affPt_eq]
      simp only [Exchange.big, one_mul, hch]
end GlobalTheory.RootEx.HeisenbergSign
