-- Prove2me | solution 1 for GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:16.553128+00:00
-- url     : https://prove2.me/submissions/f6d8cf34-1385-47e5-86dc-027e1c9f723a

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddHaarProperSubmoduleEqZeroModuleTopology

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open Set Pointwise Metric
open GlobalTheory GlobalTheory.HaarNullSub
namespace GlobalTheory.HaarNullSub
theorem _root_.solution (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V]
    [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    (hμ : μ.IsAddHaarMeasure) (s : Submodule F V) (hs : s ≠ ⊤) : μ (s : Set V) = 0 := by
  haveI := hμ
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : ContinuousSMul F V := inferInstance

  let e₀ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hc : Continuous e₀ := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
  have hc' : Continuous e₀.symm := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap
  let h : V ≃ₜ (Fin (Module.finrank F V) → F) :=
    { e₀.toEquiv with continuous_toFun := hc, continuous_invFun := hc' }

  have hcl : IsClosed (s : Set V) := by
    have h1 : IsClosed ((s.map e₀.toLinearMap : Submodule F _) : Set (Fin (Module.finrank F V) → F)) :=
      Submodule.closed_of_finiteDimensional _
    have h2 : (s : Set V) = h ⁻¹' ((s.map e₀.toLinearMap : Submodule F _) : Set _) := by
      ext v
      simp [h, Submodule.mem_map]
    rw [h2]; exact h1.preimage h.continuous

  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hs
  obtain ⟨c, c0, c1⟩ := NormedField.exists_norm_lt_one F
  let u : ℕ → V := fun n => c ^ n • x
  have hu : Tendsto u atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one c1
    simpa [u] using this.smul_const x
  have hC : IsCompact (insert 0 (range u)) := hu.isCompact_insert_range

  have hdisj : ∀ A ⊆ (s : Set V), Pairwise (Function.onFun Disjoint fun n => {u n} + A) := by
    intro A hA m n hmn
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨_, rfl, a, ha, rfl⟩ ⟨_, rfl, b, hb, hab⟩
    apply hx
    have hne : c ^ m - c ^ n ≠ 0 := by
      intro h0
      apply hmn
      have : ‖c‖ ^ m = ‖c‖ ^ n := by rw [← norm_pow, ← norm_pow, sub_eq_zero.mp h0]
      exact pow_right_injective₀ c0 (ne_of_lt c1) this.symm |>.symm
    have hmem : (c ^ m - c ^ n) • x ∈ s := by
      have : (c ^ m - c ^ n) • x = b - a := by
        simp only [u] at hab
        rw [sub_smul, show c ^ m • x = c ^ n • x + b - a by rw [hab]; abel]; abel
      rw [this]; exact s.sub_mem (hA hb) (hA ha)
    exact (Submodule.smul_mem_iff s hne).mp hmem

  have key : ∀ R : ℝ, μ ((s : Set V) ∩ h ⁻¹' closedBall 0 R) = 0 := by
    intro R
    set A := (s : Set V) ∩ h ⁻¹' closedBall 0 R with hAdef
    have hAc : IsCompact A := by
      have hK : IsCompact (h ⁻¹' closedBall 0 R) := by
        rw [← h.image_symm]
        exact (isCompact_closedBall (0 : Fin (Module.finrank F V) → F) R).image h.symm.continuous
      exact hK.inter_left hcl
    have hAm : MeasurableSet A := hcl.measurableSet.inter (isClosed_closedBall.preimage h.continuous).measurableSet
    by_contra hne
    apply lt_irrefl (⊤ : ENNReal)
    calc
      (⊤ : ENNReal) = ∑' _ : ℕ, μ A := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
      _ = ∑' n : ℕ, μ ({u n} + A) := by
        congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
      _ = μ (⋃ n, {u n} + A) := Eq.symm <| measure_iUnion (hdisj A inter_subset_left) fun n => by
        simpa only [image_add_left, singleton_add] using (measurable_const_add (-u n)) hAm
      _ ≤ μ (insert 0 (range u) + A) := by
        apply measure_mono
        refine iUnion_subset fun n => add_subset_add ?_ Subset.rfl
        exact singleton_subset_iff.mpr (mem_insert_of_mem _ (mem_range_self n))
      _ < ⊤ := (hC.add hAc).measure_lt_top
  rw [← nonpos_iff_eq_zero]
  calc
    μ (s : Set V) ≤ ∑' n : ℕ, μ ((s : Set V) ∩ h ⁻¹' closedBall 0 n) := by
      conv_lhs => rw [← inter_univ (s : Set V), ← preimage_univ (f := h), ← iUnion_closedBall_nat 0,
        preimage_iUnion, inter_iUnion]
      exact measure_iUnion_le _
    _ = 0 := by simp only [key, tsum_zero]
end GlobalTheory.HaarNullSub
