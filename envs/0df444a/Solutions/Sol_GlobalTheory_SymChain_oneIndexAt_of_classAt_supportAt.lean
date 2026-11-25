-- Prove2me | solution 1 for GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:12.12052+00:00
-- url     : https://prove2.me/submissions/0202ccda-7928-4bb3-a77e-3bc311cfe81c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainOneIndexAtOfClassSupport
import Theorems.Thm_GlobalTheory_RootEx_Radical_exists_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_opE_om_embX
import Theorems.Thm_GlobalTheory_RootEx_opE_om_target_unipotent
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain
namespace GlobalTheory.SymChain
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hC hS j c H p hp1 hpc h hE
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨r, hr, u, hu, rfl⟩ := hC j c H p hp1 hpc h hE
  obtain ⟨γ, g, hg, rfl⟩ := Radical.exists_of_mem_R hr
  have hmul : ∀ (a b : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k) (Ψ : type_of% ((S.T t).Phi j c H)),
      om (S.μ (j + 1)) 1 (a * b) Ψ = om (S.μ (j + 1)) 1 a (om (S.μ (j + 1)) 1 b Ψ) :=
    fun a b Ψ => by rw [← om_mul, one_mul]
  have hne : opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) ≠ 0 := by
    intro h0
    apply hE
    rw [mul_assoc, hmul, (opE_om_embX k _ _ c p hp1 hpc S.ψ ν _ _).1, hmul,
      opE_om_target_unipotent k _ _ c p hp1 hpc S.ψ ν _ _ g hg, h0]
    funext y
    simp [om]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) x₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  classical
  obtain ⟨e, he⟩ : ∃ e, om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H) (affPt p x₀ e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hx₀
    simp [opE, hc]
  have hΦ : (S.T t).Phi j c H ((u⁻¹).val * affPt p x₀ e) ≠ 0 := by
    intro h0
    apply he
    simp only [om, Units.val_one, Matrix.mul_one, h0, mul_zero]
  obtain ⟨r', hr', u', hu', rfl⟩ := hS j c H p hp1 hpc u hu x₀ e hΦ
  exact ⟨embX c γ * g * r', mul_mem hr hr', u', hu', by group⟩
end GlobalTheory.SymChain
