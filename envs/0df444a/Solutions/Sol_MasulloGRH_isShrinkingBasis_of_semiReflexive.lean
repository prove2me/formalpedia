-- Prove2me | solution 1 for MasulloGRH.isShrinkingBasis_of_semiReflexive
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:49:42.735716+00:00
-- url     : https://prove2.me/submissions/765878a3-8d1b-42a3-b24d-1eb0a7724f88

import Definitions.Def_MasulloGRH_SchauderBases
import Theorems.Thm_LocallyConvexDuality_isVonNBounded_uniformConvergenceCLM_of_pointwise

set_option autoImplicit false

open MasulloGRH

namespace Sol_MasulloGRH_isShrinkingBasis_of_semiReflexive

open Topology Filter Set

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

theorem partialSum_apply (φ : StrongDual ℂ E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (k : ℕ)
    (u : E) :
    (∑ m ∈ Finset.range (k + 1), φ (x m) • f m) u = φ (basicProjection x f k u) := by
  simp only [basicProjection, map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

omit [Module ℂ E] in
theorem completeSpace_of_isCompleteTVS [IsTopologicalAddGroup E] (hc : IsCompleteTVS E) :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  refine ⟨fun {F} hF => hc.2 F ⟨hF.1, fun U hU => ?_⟩⟩
  have hmem : (fun p : E × E => p.2 + -p.1) ⁻¹' U ∈ uniformity E := preimage_mem_comap hU
  obtain ⟨A, hA, hAA⟩ := Filter.mem_prod_same_iff.1 (hF.2 hmem)
  refine ⟨A, hA, fun a ha b hb => ?_⟩
  have h := hAA (Set.mk_mem_prod hb ha)
  simpa [sub_eq_add_neg] using h

theorem isVonNBounded_projections [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E]
    (hc : IsCompleteTVS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hx : ∀ u, Tendsto (fun k => basicProjection x f k u) atTop (𝓝 u))
    (S : Set E) (hS : Bornology.IsVonNBounded ℂ S) :
    Bornology.IsVonNBounded ℂ {v | ∃ k, ∃ u ∈ S, v = basicProjection x f k u} := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := completeSpace_of_isCompleteTVS hc
  let P : ℕ → E →L[ℂ] E := fun k => ∑ m ∈ Finset.range (k + 1), (f m).smulRight (x m)
  have hP : ∀ k u, P k u = basicProjection x f k u := by
    intro k u
    simp [P, basicProjection]
  have hH := LocallyConvexDuality.isVonNBounded_uniformConvergenceCLM_of_pointwise
    (𝕜 := ℂ) (E := E) (F := E) {S} (by simpa using hS) (Set.range P) (by
      intro u
      refine (Filter.Tendsto.isVonNBounded_range ℂ (hx u)).subset ?_
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (hP k u).symm⟩)
  have h2 := UniformConvergenceCLM.isVonNBounded_image2_apply hH (Set.mem_singleton S)
  refine h2.subset ?_
  rintro v ⟨k, u, hu, rfl⟩
  refine ⟨UniformConvergenceCLM.ofFun (RingHom.id ℂ) E {S} (P k), ⟨P k, ⟨k, rfl⟩, rfl⟩, u, hu, ?_⟩
  exact hP k u

theorem eventually_fixed (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hb : ∀ m n, f m (x n) = if m = n then 1 else 0) (ψ : StrongDual ℂ E)
    (hψ : ψ ∈ Submodule.span ℂ (Set.range f)) :
    ∃ K, ∀ k ≥ K, ∀ u, ψ (basicProjection x f k u) = ψ u := by
  induction hψ using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨m, rfl⟩ := hg
    refine ⟨m, fun k hk u => ?_⟩
    simp only [basicProjection, map_sum, map_smul, hb, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_range]
    rw [if_pos (by omega)]
  | zero => exact ⟨0, fun _ _ _ => by simp⟩
  | add a b _ _ ha hb' =>
    obtain ⟨K1, h1⟩ := ha
    obtain ⟨K2, h2⟩ := hb'
    exact ⟨max K1 K2, fun k hk u => by
      simp [h1 k (le_of_max_le_left hk) u, h2 k (le_of_max_le_right hk) u]⟩
  | smul c a _ ha =>
    obtain ⟨K, h⟩ := ha
    exact ⟨K, fun k hk u => by simp [h k hk u]⟩

theorem mem_closure_span [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    (hsr : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃ u : E, ∀ g : StrongDual ℂ E, φ g = g u)
    (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) (φ : StrongDual ℂ E) :
    φ ∈ closure (Submodule.span ℂ (Set.range f) : Set (StrongDual ℂ E)) := by
  have : LocallyConvexSpace ℝ (StrongDual ℂ E) :=
    ContinuousLinearMap.instLocallyConvexSpace (R := ℝ) (E := E) (F := ℂ) (σ := RingHom.id ℂ)
  have := IsScalarTower.continuousSMul (M := ℝ) (α := StrongDual ℂ E) ℂ
  set M := Submodule.span ℂ (Set.range f)
  by_contra hφ
  have hconv : Convex ℝ (closure (M : Set (StrongDual ℂ E))) :=
    (M.restrictScalars ℝ).convex.closure
  obtain ⟨Φ, u, hΦ, hu⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hconv isClosed_closure hφ
  have hzero : ∀ m, Φ (f m) = 0 := by
    intro m
    by_contra hne
    have hmem : ∀ t : ℂ, t • f m ∈ closure (M : Set (StrongDual ℂ E)) := fun t =>
      subset_closure (M.smul_mem t (Submodule.subset_span ⟨m, rfl⟩))
    have h := hΦ _ (hmem (((|u| + 1 : ℝ) : ℂ) / Φ (f m)))
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h
    simp only [RCLike.re_to_complex, Complex.ofReal_re] at h
    linarith [le_abs_self u]
  obtain ⟨w, hw⟩ := hsr Φ
  have hw0 : w = 0 := by
    have h1 := hx.expansion w
    have h2 : ∀ k, basicProjection x f k w = 0 := by
      intro k
      exact Finset.sum_eq_zero fun m _ => by rw [← hw, hzero, zero_smul]
    simp only [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have h0 := hΦ 0 (subset_closure M.zero_mem)
  rw [hw, hw0] at hu h0
  simp at hu h0
  linarith

end Sol_MasulloGRH_isShrinkingBasis_of_semiReflexive

open Topology Filter

open Sol_MasulloGRH_isShrinkingBasis_of_semiReflexive in
theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (hc : IsCompleteTVS E)
    (hsr : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! u : E, ∀ g : StrongDual ℂ E, φ g = g u)
    (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) :
    IsShrinkingBasis x f := by
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := hE
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : PolynormableSpace ℂ E := hp.toPolynormableSpace
  unfold IsShrinkingBasis IsDualSchauderBasis
  refine ⟨hx.biorthogonal, fun φ => ?_⟩
  rw [← tendsto_sub_nhds_zero_iff]
  refine (ContinuousLinearMap.hasBasis_nhds_zero).tendsto_right_iff.2 ?_
  rintro ⟨S, V⟩ ⟨hS, hV⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  set C := S ∪ {v | ∃ k, ∃ u ∈ S, v = basicProjection x f k u} with hCdef
  have hC : Bornology.IsVonNBounded ℂ C :=
    hS.union (isVonNBounded_projections hc x f hx.expansion S hS)
  have hN : {χ : StrongDual ℂ E | ∀ v ∈ C, χ v ∈ Metric.ball (0 : ℂ) (ε / 2)} ∈
      𝓝 (0 : StrongDual ℂ E) :=
    (ContinuousLinearMap.hasBasis_nhds_zero).mem_of_mem
      (i := (C, Metric.ball (0 : ℂ) (ε / 2))) ⟨hC, Metric.ball_mem_nhds _ (by linarith)⟩
  have hcl := mem_closure_span (fun Φ => (hsr Φ).exists) x f hx φ
  have hN' : (fun χ : StrongDual ℂ E => χ - φ) ⁻¹'
      {χ : StrongDual ℂ E | ∀ v ∈ C, χ v ∈ Metric.ball (0 : ℂ) (ε / 2)} ∈ 𝓝 φ := by
    apply (continuous_sub_right φ).continuousAt.preimage_mem_nhds
    simpa using hN
  obtain ⟨ψ, hψN, hψM⟩ := mem_closure_iff_nhds.1 hcl _ hN'
  obtain ⟨K, hK⟩ := eventually_fixed x f hx.biorthogonal ψ hψM
  filter_upwards [eventually_ge_atTop K] with k hk
  intro u hu
  apply hεV
  rw [ContinuousLinearMap.sub_apply, partialSum_apply]
  have h1 := hψN (basicProjection x f k u) (Or.inr ⟨k, u, hu, rfl⟩)
  have h2 := hψN u (Or.inl hu)
  have h3 := hK k hk u
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right,
    ContinuousLinearMap.sub_apply] at h1 h2 ⊢
  calc ‖φ (basicProjection x f k u) - φ u‖
      = ‖(ψ u - φ u) - (ψ (basicProjection x f k u) - φ (basicProjection x f k u))‖ := by
        rw [h3]; congr 1; ring
    _ ≤ ‖ψ u - φ u‖ + ‖ψ (basicProjection x f k u) - φ (basicProjection x f k u)‖ :=
        norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h2 h1
    _ = ε := by ring
