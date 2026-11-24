-- Prove2me | solution 1 for GlobalTheory.SplitDict.pf_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:41.725968+00:00
-- url     : https://prove2.me/submissions/bcae6daf-2c98-489e-a0b2-640c92da472d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_GlobalTheory_SplitDict_pf_mem_SB
import Theorems.Thm_GlobalTheory_SplitDict_pf_pf
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitDict
theorem _root_.solution (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c) :
    Set.BijOn (pf ψ (Measure.pi fun _ => m)) {f | f ∈ SB (T × (n → k))} {f | f ∈ SB (T × (n → k))} := by
  haveI := secondCountable k
  set C : ℂ := (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) with hC
  have hC0 : C ≠ 0 := by
    have h1 : 0 < m.real (𝒪[k] : Set k) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos ((isOpen_int k).measure_ne_zero m ⟨0, by simp⟩)
        (isCompact_int k).measure_lt_top.ne
    have h2 := nabs_pos k c
    rw [hC]
    exact Complex.ofReal_ne_zero.mpr (pow_pos (mul_pos (pow_pos h1 2) h2) _).ne'
  have hsmul : ∀ (a : ℂ) (g : T × (n → k) → ℂ), pf ψ (Measure.pi fun _ : n => m) (a • g) = a • pf ψ (Measure.pi fun _ : n => m) g := by
    intro a g
    funext z
    simp only [pf, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul a _
  have hpp : ∀ g ∈ SB (T × (n → k)), ∀ z, pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g) z = C * g (z.1, -z.2) :=
    fun g hg z => pf_pf m h hg z
  refine ⟨fun g hg => pf_mem_SB (Measure.pi fun _ : n => m) h hg, fun g hg g' hg' hgg => ?_, fun g hg => ?_⟩
  · funext z
    have e1 := hpp g hg (z.1, -z.2)
    have e2 := hpp g' hg' (z.1, -z.2)
    rw [hgg] at e1
    simp only [neg_neg, Prod.mk.eta] at e1 e2
    exact mul_left_cancel₀ hC0 (e1.symm.trans e2)
  · have h2 := pf_mem_SB (Measure.pi fun _ : n => m) h (pf_mem_SB (Measure.pi fun _ : n => m) h hg)
    refine ⟨(C ^ 2)⁻¹ • pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g)), (SB _).smul_mem _ (pf_mem_SB (Measure.pi fun _ : n => m) h h2), ?_⟩
    rw [hsmul]
    funext z
    rw [Pi.smul_apply, hpp _ h2, hpp _ hg]
    simp only [neg_neg, Prod.mk.eta, smul_eq_mul]
    field_simp
end GlobalTheory.SplitDict
