-- Prove2me | solution 1 for GlobalTheory.RootEx.ColumnSupport.opE_colE_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:59.724951+00:00
-- url     : https://prove2.me/submissions/efe78b4e-c183-47f2-91cc-1c0a601f2720

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ColEInvMulAffPt
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_inv_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ColumnSupport
open MeasureTheory ValuativeRel Matrix
namespace GlobalTheory.RootEx.ColumnSupport
namespace _root_.GlobalTheory.RootEx.ColumnSupport
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ), ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∃ K : Set (n → k), IsCompact K ∧ ∀ β, β ∉ K → ∀ χ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => χ y * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.colE c (p + 1) β) Φ y) = 0 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp ψ ν μ Φ hΦ
  have hcs : HasCompactSupport Φ := (show IsLocallyConstant Φ ∧ HasCompactSupport Φ from hΦ).2
  let q : Fin (c + 1) := ⟨p, by omega⟩
  refine ⟨(fun z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => fun r => -z (Sum.inl r) (Sum.inr q)) '' tsupport Φ,
    hcs.isCompact.image (continuous_pi fun r => (continuous_apply_apply _ _).neg), ?_⟩
  intro β hβ χ
  funext x
  unfold _root_.GlobalTheory.RootEx.opE
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
  have hentry : ∀ r, ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e) (Sum.inl r) (Sum.inr q) = -β r := by
    intro r
    rw [_root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp [q, Matrix.mul_apply, Fintype.sum_sum_type, _root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, _root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.RootEx.ExchangeSupport.colM, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨p, hp⟩ (fun b _ hb => if_neg (fun h => hb (Fin.ext h))) (by simp)]
    simp
  have hzero : Φ ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e * ((1 : GL (n' ⊕ Fin (c + 1)) k) : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) = 0 := by
    by_contra h
    apply hβ
    refine ⟨_, subset_tsupport _ h, ?_⟩
    funext r
    simp only [Units.val_one, Matrix.mul_one]
    rw [hentry r, neg_neg]
  unfold _root_.GlobalTheory.SplitWeil.om
  simp only [Pi.zero_apply]
  rw [hzero]
  simp
end _root_.GlobalTheory.RootEx.ColumnSupport
end GlobalTheory.RootEx.ColumnSupport
