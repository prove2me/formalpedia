-- Prove2me | solution 1 for GlobalTheory.RankFibre.integrable_fibre_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:24.142269+00:00
-- url     : https://prove2.me/submissions/a037af66-02d4-4c16-a393-652c93679c41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableFullRankFibre
import Theorems.Thm_GlobalTheory_RankFibre_X0_mul_X0_transpose
import Theorems.Thm_GlobalTheory_RankFibre_isUnit_of_rank_mul_X0
import Theorems.Thm_GlobalTheory_GodementJacquet_isLocallyConstant_char_det
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_isLocallyConstant_nabs
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.RankFibre
namespace GlobalTheory.RankFibre
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), MeasureTheory.Integrable (fun g : GL (Fin a) k => Φ (g.val * GlobalTheory.SplitFlip.X0 k finSumFinEquiv) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  intro k _ _ _ _ _ _ a b ν hν Φ hΦ
  obtain ⟨⟨hl, hK⟩, hrk⟩ := hΦ
  set X0 := GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)) with hX0
  have hc1 : IsLocallyConstant fun g : GL (Fin a) k => Φ (g.val * X0) :=
    hl.comp_continuous (Units.continuous_val.matrix_mul continuous_const)
  have hc2 := GlobalTheory.GodementJacquet.isLocallyConstant_char_det (k := k) (n := Fin a) hν
  have hc3 : IsLocallyConstant fun g : GL (Fin a) k =>
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) :=
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp
      fun x => ((x : ℝ) : ℂ) ^ (((a + b : ℕ) : ℂ) / 2)
  have hcont := ((hc1.mul hc2).mul hc3).continuous

  set D : Set (Matrix (Fin a) (Fin a) k) := {A | Φ (A * X0) ≠ 0} with hD
  have hDc : IsClosed D := by
    exact (hl.isOpen_fiber 0).isClosed_compl.preimage
      (show Continuous fun A : Matrix (Fin a) (Fin a) k => A * X0 from continuous_id.matrix_mul continuous_const)
  have hDsub : D ⊆ (fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ) '' tsupport Φ := by
    intro A hA
    refine ⟨A * X0, subset_tsupport _ hA, ?_⟩
    show A * X0 * X0ᵀ = A
    rw [Matrix.mul_assoc, hX0, X0_mul_X0_transpose, Matrix.mul_one]
  have hDcpt : IsCompact D :=
    (hK.image (show Continuous fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ from
      continuous_id.matrix_mul continuous_const)).of_isClosed_subset hDc hDsub
  have hDr : D ⊆ Set.range fun g : GL (Fin a) k => g.val := by
    intro A hA
    have hr : (A * X0).rank = a := by
      by_contra hne
      exact hA (hrk _ hne)
    exact ⟨(isUnit_of_rank_mul_X0 A hr).unit, rfl⟩
  have hS : IsCompact ((fun g : GL (Fin a) k => g.val) ⁻¹' D) :=
    GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.isCompact_preimage' hDcpt hDr
  have hcs : HasCompactSupport fun g : GL (Fin a) k => Φ (g.val * X0) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) := by
    refine HasCompactSupport.intro hS fun g hg => ?_
    have : Φ (g.val * X0) = 0 := not_not.1 hg
    simp [this]
  exact hcont.integrable_of_hasCompactSupport hcs
end GlobalTheory.RankFibre
