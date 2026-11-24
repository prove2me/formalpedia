-- Prove2me | solution 1 for GlobalTheory.T.hermitianTraceDual_integers_eq_uniformizer_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:30.313141+00:00
-- url     : https://prove2.me/submissions/41173354-936f-4222-9d9a-7793a824862a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianTraceDualIntegersEqUniformizerPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianTraceDualIntegersEqUniformizerPowStatement
import Theorems.Thm_GlobalTheory_JR_DualLattice_dual_eq_zpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → IsField A.L → ∀ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) → (∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O) → ∀ a : A.Kˣ, ∃ e : ℤ, {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((ϖ ^ e : A.Kˣ) : A.K) * z} := by
  first | exact @GlobalTheory.JR.DualLattice.dual_eq_zpow | exact GlobalTheory.JR.DualLattice.dual_eq_zpow | (intros; apply GlobalTheory.JR.DualLattice.dual_eq_zpow <;> assumption)
end _root_.GlobalTheory.T
