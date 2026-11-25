-- Prove2me | solution 1 for GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:00:14.055309+00:00
-- url     : https://prove2.me/submissions/b67926b7-be65-4a3e-94a2-a8db78e2aeee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatNeZeroOfMemR
import Theorems.Thm_GlobalTheory_FlatSourceStable_om_ne_zero
import Theorems.Thm_GlobalTheory_RootExSource_opE_om_source
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_pos
import Theorems.Thm_GlobalTheory_RootEx_Radical_exists_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_opE_om_embX
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.FlatSourceStable
namespace GlobalTheory.FlatSourceStable
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ) (g : GL (n' ⊕ Fin (c + 1 + 1)) k) (h : GL (n ⊕ Fin (c + 1)) k), flat ψ ν μ Φ g h ≠ 0 → ∀ r ∈ R k n' (c + 1 + 1) 1, flat ψ ν μ Φ (r * g) h ≠ 0 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ψ ν _ μ Φ g h h0 r hr
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hr
  unfold flat at h0 ⊢
  have e : om μ (embX (c + 1 + 1) x * u * g) h Φ =
      om μ (embX (c + 1 + 1) x) 1 (om μ u 1 (om μ g h Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, one_mul]
  rw [e, (GlobalTheory.RootEx.opE_om_embX k n n' (c + 1) 1 le_rfl (by omega) ψ ν μ _).2 x,
    GlobalTheory.RootExSource.opE_om_source k n n' (c + 1) 1 le_rfl (by omega) ψ ν μ _ u hu]
  refine smul_ne_zero ?_ (om_ne_zero μ _ _ (smul_ne_zero (Circle.coe_ne_zero _) h0))
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (nabs_pos k _) _).ne'
end GlobalTheory.FlatSourceStable
