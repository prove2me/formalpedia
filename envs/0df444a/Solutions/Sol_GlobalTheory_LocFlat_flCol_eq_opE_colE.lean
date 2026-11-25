-- Prove2me | solution 1 for GlobalTheory.LocFlat.flCol_eq_opE_colE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:42.896435+00:00
-- url     : https://prove2.me/submissions/fe92ec1c-f8bc-44e7-a7e4-19270eccd52b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslate
import Theorems.Thm_GlobalTheory_LocFlat_ColTranslate_colE_neg_inv
import Theorems.Thm_GlobalTheory_LocFlat_ColTranslate_affPt_add_colAt
import Theorems.Thm_GlobalTheory_LocFlat_ColTranslate_ch_add_colAt
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
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.LocFlat
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat.ColTranslate
namespace GlobalTheory.LocFlat
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix n (n' ⊕ Unit) k, GlobalTheory.LocFlat.flCol ψ ν p Φ x = opE ψ ν p (fun z => Φ ((colE c p fun r => x r (Sum.inr ())).val * z)) x.toCols₁ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1 hpc Φ hΦ x
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp; omega⟩
  have hcont : Continuous Φ := hΦ.1.continuous
  have h1 := opE_colE hψ ν 1 q q (χ := fun _ => (1 : ℂ)) continuous_const hcont x.toCols₁
    (-fun r => x r (Sum.inr ()))
  simp only [om_colE, colE_neg_inv, one_mul, neg_neg] at h1
  refine Eq.trans ?_ h1.symm
  rw [flCol]
  unfold opE
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only
  rw [← affPt_add_colAt, big, ch_add_colAt, one_mul]
end GlobalTheory.LocFlat
