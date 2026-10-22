-- Prove2me | solution 1 for JHolomorphic.integrable_smul_of_integrableOn_compact
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:45:37.557509+00:00
-- url     : https://prove2.me/submissions/6088c451-8f40-4584-a449-d4cddf193355

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- A real function that is continuous on `U` and has compact support in `U`, times a map that is
integrable on every compact subset of `U`, is integrable on `ℂ`. -/
theorem integrable_smul_of_integrableOn_compact_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {f : ℂ → E} (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K)
    {g : ℂ → ℝ} (hg : ContinuousOn g U) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    Integrable (fun z => g z • f z) := by
  refine (integrableOn_iff_integrable_of_support_subset (s := tsupport g) ?_).mp
    ((hf _ hgU hgc.isCompact).continuousOn_smul (hg.mono hgU) hgc.isCompact)
  intro z hz
  apply subset_tsupport
  intro h0
  exact hz (by simp [h0])

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {f : ℂ → E} (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K)
    {g : ℂ → ℝ} (hg : ContinuousOn g U) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    Integrable (fun z => g z • f z) :=
  integrable_smul_of_integrableOn_compact_aux hf hg hgc hgU
