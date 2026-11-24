-- Prove2me | solution 1 for GlobalTheory.lattice_sum_dilate_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:48.347896+00:00
-- url     : https://prove2.me/submissions/7594e66f-fec5-4f67-b124-4c9fa521d207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ZlatticeTsumDilateSubIntegralLeRapidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptotic
import Theorems.Thm_GlobalTheory_integral_div_covolume_eq_of_haar
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_T_zlattice_tsum_dilate_sub_integral_le_rapid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  intro V _ _ _ _ _ μ _ L _ _ f hf hs A
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] V := toEuclidean.symm
  let ν : Measure V := (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))).map e
  have : ν.IsAddHaarMeasure := ContinuousLinearEquiv.isAddHaarMeasure_map e _
  have hmp : MeasurePreserving e volume ν := ⟨e.continuous.measurable, rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.zlattice_tsum_dilate_sub_integral_le_rapid _ (ZLattice.comap ℝ L e.toLinearMap) (f ∘ e)
    (hf.comp e.contDiff) (hs.comp_homeomorph e.toHomeomorph) A
  refine ⟨C, fun x₀ t ht ht1 => ?_⟩
  have h := hC (e.symm x₀) t ht ht1
  rw [ZLattice.covolume_comap L ν volume hmp, finrank_euclideanSpace_fin] at h
  have hi : ∫ x, (f ∘ e) x = ∫ x, f x ∂ν :=
    (hmp.integral_comp e.toHomeomorph.measurableEmbedding f)
  have hsum : ∑' l : ZLattice.comap ℝ L e.toLinearMap,
      (f ∘ e) (t • ((l : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) + e.symm x₀)) =
      ∑' l : L, f (t • ((l : V) + x₀)) := by
    let q : ZLattice.comap ℝ L e.toLinearMap ≃ L :=
      e.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
    rw [← q.tsum_eq]
    refine tsum_congr fun l => ?_
    have : ((q l : L) : V) = e l := rfl
    simp [this]
  rw [hi, hsum] at h
  rw [integral_div_covolume_eq_of_haar μ ν L f]
  exact h
end GlobalTheory
