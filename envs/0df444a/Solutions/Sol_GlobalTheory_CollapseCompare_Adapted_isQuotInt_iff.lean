-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.Adapted.isQuotInt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:49.694837+00:00
-- url     : https://prove2.me/submissions/929cd9e9-a527-4ff5-96de-024e92c4ca33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
import Theorems.Thm_GlobalTheory_CollapseCompare_cjG_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.CollapseCompare
namespace Adapted
theorem _root_.solution {t : GL (n ⊕ Fin c) k} (ht : Adapted t) {ν ν₀ : Measure k} {r : ℝ≥0} (hr : r ≠ 0)
    (H : ∀ F : GL (n ⊕ Fin c) k → ℂ,
        ∫ u : N k n c 1, F (t * u * t⁻¹) ∂(volN ν₀ n c 1) = (r : ℝ) • ∫ u : N k n c 1, F u ∂(volN ν n c 1))
    (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ) :
    IsQuotInt ν₀ (r⁻¹ • μX) (μG.map (cjG t).symm) 1 (fun h => f (cjG t h)) z ↔ IsQuotInt ν μX μG 1 f z := by
  haveI := secondCountable k
  haveI := t2Space k
  have h1 : ∀ (F : GL (n ⊕ Fin c) k → ℂ) h,
      ∫ g, (∫ u : N k n c 1, F (cjG t (embX c g * (u : GL (n ⊕ Fin c) k) * h)) ∂(volN ν₀ n c 1)) ∂(r⁻¹ • μX) =
      ∫ g, (∫ u : N k n c 1, F (embX c g * (u : GL (n ⊕ Fin c) k) * cjG t h) ∂(volN ν n c 1)) ∂μX := fun F h => by
    have : ∀ g, ∫ u : N k n c 1, F (cjG t (embX c g * (u : GL (n ⊕ Fin c) k) * h)) ∂(volN ν₀ n c 1) =
        (r : ℝ) • ∫ u : N k n c 1, F (embX c g * (u : GL (n ⊕ Fin c) k) * cjG t h) ∂(volN ν n c 1) := fun g => by
      rw [← H fun x => F (embX c g * x * cjG t h)]
      simp only [map_mul, cjG_apply, ht.comm]
    simp only [this]
    rw [integral_smul_nnreal_measure, integral_smul, NNReal.smul_def, smul_smul]
    simp [hr]
  have h2 : ∀ F : GL (n ⊕ Fin c) k → ℂ, ∫ h, F (cjG t h) ∂(μG.map (cjG t).symm) = ∫ h, F h ∂μG := fun F => by
    refine (integral_map_equiv (cjG t).symm.toHomeomorph.toMeasurableEquiv _).trans ?_
    congr 1
    funext h
    exact congrArg F ((cjG t).apply_symm_apply h)
  have h3 : ∀ (e : GL (n ⊕ Fin c) k ≃ₜ* GL (n ⊕ Fin c) k), ∀ F ∈ SB (GL (n ⊕ Fin c) k),
      (fun h => F (e h)) ∈ SB (GL (n ⊕ Fin c) k) := fun e F hF =>
    ⟨hF.1.comp_continuous e.continuous, hF.2.comp_homeomorph e.toHomeomorph⟩
  constructor
  · rintro ⟨F₀, hF, ha, hb⟩
    obtain ⟨F, rfl⟩ : ∃ F : GL (n ⊕ Fin c) k → ℂ, F₀ = fun h => F (cjG t h) :=
      ⟨fun h => F₀ ((cjG t).symm h), by simp⟩
    refine ⟨F, by simpa using h3 (cjG t).symm _ hF, fun h => ?_, hb.trans (h2 F)⟩
    obtain ⟨h, rfl⟩ := (cjG t).surjective h
    exact (ha h).trans (h1 F h)
  · rintro ⟨F, hF, ha, hb⟩
    exact ⟨_, h3 (cjG t) F hF, fun h => (ha _).trans (h1 F h).symm, hb.trans (h2 F).symm⟩
end Adapted
end GlobalTheory.CollapseCompare
