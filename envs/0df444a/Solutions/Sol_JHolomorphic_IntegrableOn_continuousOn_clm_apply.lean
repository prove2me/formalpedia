-- Prove2me | solution 1 for JHolomorphic.IntegrableOn.continuousOn_clm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:59:21.876063+00:00
-- url     : https://prove2.me/submissions/065027eb-a2ad-4908-8dab-9d4340ea9d93

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- If `A` is a continuous family of linear maps on a compact set `K` and `f` is integrable on
`K`, then `z ↦ A(z) f(z)` is integrable on `K`. -/
theorem IntegrableOn.continuousOn_clm_apply_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {K : Set ℂ} (hK : IsCompact K) {A : ℂ → E →L[ℝ] F}
    (hA : ContinuousOn A K) {f : ℂ → E} (hf : IntegrableOn f K) :
    IntegrableOn (fun z => A z (f z)) K := by
  let b := Module.finBasis ℝ (E →L[ℝ] F)
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ (E →L[ℝ] F)) → (E →L[ℝ] F) →L[ℝ] ℝ,
      ∀ k L, c k L = b.repr L k :=
    ⟨fun k => LinearMap.toContinuousLinearMap (b.coord k), fun k L => by simp⟩
  have hexp : ∀ z, A z (f z) = ∑ k, c k (A z) • b k (f z) := by
    intro z
    calc A z (f z) = (∑ k, b.repr (A z) k • b k) (f z) := by rw [b.sum_repr]
      _ = ∑ k, c k (A z) • b k (f z) := by
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hc]
  simp_rw [hexp]
  exact integrable_finset_sum _ fun k _ =>
    IntegrableOn.continuousOn_smul ((b k).integrable_comp hf)
      ((c k).continuous.comp_continuousOn hA) hK

end JHolomorphic

open JHolomorphic JHolomorphic.IntegrableOn

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {K : Set ℂ} (hK : IsCompact K) {A : ℂ → E →L[ℝ] F}
    (hA : ContinuousOn A K) {f : ℂ → E} (hf : IntegrableOn f K) :
    IntegrableOn (fun z => A z (f z)) K :=
  IntegrableOn.continuousOn_clm_apply_aux hK hA hf
