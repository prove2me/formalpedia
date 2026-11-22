-- Prove2me | solution 1 for MasulloGRH.indTensor_le_projTensor_le_epsTensor
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:59:38.732005+00:00
-- url     : https://prove2.me/submissions/c176c7b6-1504-4d3a-8ac4-38ab03015a79

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace Sol_MasulloGRH_indTensor_le_projTensor_le_epsTensor

open MasulloGRH Set

variable {E F : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The functional `x' ⊗ y'` as a linear map on `E ⊗ F`. -/
noncomputable def tfLin (ab : StrongDual ℂ E × StrongDual ℂ F) : E ⊗[ℂ] F →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
    TensorProduct.map (ab.1 : E →ₗ[ℂ] ℂ) (ab.2 : F →ₗ[ℂ] ℂ)

theorem tfLin_apply (ab : StrongDual ℂ E × StrongDual ℂ F) (u : E ⊗[ℂ] F) :
    tfLin ab u = tensorFunctional E F ab u := rfl

theorem tensorFunctional_tmul (ab : StrongDual ℂ E × StrongDual ℂ F) (x : E) (y : F) :
    tensorFunctional E F ab (x ⊗ₜ[ℂ] y) = ab.1 x * ab.2 y := by
  simp [tensorFunctional]

theorem tensorFunctional_zero (ab : StrongDual ℂ E × StrongDual ℂ F) :
    tensorFunctional E F ab 0 = 0 := by
  rw [← tfLin_apply, map_zero]

theorem tensorFunctional_add (ab : StrongDual ℂ E × StrongDual ℂ F) (u v : E ⊗[ℂ] F) :
    tensorFunctional E F ab (u + v) = tensorFunctional E F ab u + tensorFunctional E F ab v := by
  simp only [← tfLin_apply, map_add]

/-- An equicontinuous set of continuous linear functionals on a topological vector space is
pointwise bounded. -/
theorem exists_bound_of_equicontinuous [ContinuousSMul ℂ E] (A : Set (StrongDual ℂ E))
    (hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ))) (x : E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ A, ‖a x‖ ≤ M := by
  have h0 := Metric.equicontinuousAt_iff_right.mp (hA 0) 1 one_pos
  have hc : Tendsto (fun c : ℂ => c • x) (𝓝 0) (𝓝 (0 : E)) := by
    have : Continuous (fun c : ℂ => c • x) := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have h1 := hc.eventually h0
  obtain ⟨c, hc1, hc0⟩ := ((h1.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (a := (0 : ℂ)) (s := {0}ᶜ))).exists
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  refine ⟨1 / ‖c‖, by positivity, fun a ha => ?_⟩
  have h2 := hc1 ⟨a, ha⟩
  simp only [map_zero, map_smul, dist_zero_left, smul_eq_mul, norm_mul] at h2
  rw [le_div_iff₀ hcpos]
  linarith [mul_comm ‖c‖ ‖a x‖]

/-- For equicontinuous `A ⊆ E'`, `B ⊆ F'` the functions `(x', y') ↦ (x' ⊗ y')(u)` are bounded on
`A × B`. -/
theorem bddAbove_tensorFunctional [ContinuousSMul ℂ E] [ContinuousSMul ℂ F]
    (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F))
    (hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ)))
    (hB : Equicontinuous (fun b : B => ((b : StrongDual ℂ F) : F → ℂ))) (u : E ⊗[ℂ] F) :
    ∃ M : ℝ, ∀ ab ∈ A ×ˢ B, ‖tensorFunctional E F ab u‖ ≤ M := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, fun ab _ => by rw [tensorFunctional_zero, norm_zero]⟩
  | tmul x y =>
    obtain ⟨M, hM0, hM⟩ := exists_bound_of_equicontinuous A hA x
    obtain ⟨N, hN0, hN⟩ := exists_bound_of_equicontinuous B hB y
    refine ⟨M * N, fun ab hab => ?_⟩
    rw [tensorFunctional_tmul, norm_mul]
    exact mul_le_mul (hM _ hab.1) (hN _ hab.2) (norm_nonneg _) hM0
  | add u v hu hv =>
    obtain ⟨M, hM⟩ := hu
    obtain ⟨N, hN⟩ := hv
    refine ⟨M + N, fun ab hab => ?_⟩
    rw [tensorFunctional_add]
    exact (norm_add_le _ _).trans (add_le_add (hM ab hab) (hN ab hab))

/-- The seminorm `u ↦ sup_{(x', y') ∈ A × B} |(x' ⊗ y')(u)|` on `E ⊗ F`. -/
noncomputable def epsSeminorm (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)) :
    Seminorm ℂ (E ⊗[ℂ] F) :=
  ⨆ ab : (A ×ˢ B : Set (StrongDual ℂ E × StrongDual ℂ F)),
    (normSeminorm ℂ ℂ).comp (tfLin (ab : StrongDual ℂ E × StrongDual ℂ F))

theorem epsSeminorm_apply [ContinuousSMul ℂ E] [ContinuousSMul ℂ F]
    (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F))
    (hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ)))
    (hB : Equicontinuous (fun b : B => ((b : StrongDual ℂ F) : F → ℂ))) (u : E ⊗[ℂ] F) :
    epsSeminorm A B u =
      ⨆ ab : (A ×ˢ B : Set (StrongDual ℂ E × StrongDual ℂ F)),
        ‖tensorFunctional E F (ab : StrongDual ℂ E × StrongDual ℂ F) u‖ := by
  unfold epsSeminorm
  refine Seminorm.iSup_apply (Seminorm.bddAbove_range_iff.mpr fun v => ?_)
  obtain ⟨M, hM⟩ := bddAbove_tensorFunctional A B hA hB v
  exact ⟨M, forall_mem_range.mpr fun ab => hM ab ab.2⟩

theorem le_epsSeminorm [ContinuousSMul ℂ E] [ContinuousSMul ℂ F]
    (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F))
    (hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ)))
    (hB : Equicontinuous (fun b : B => ((b : StrongDual ℂ F) : F → ℂ))) (u : E ⊗[ℂ] F)
    (ab : StrongDual ℂ E × StrongDual ℂ F) (hab : ab ∈ A ×ˢ B) :
    ‖tensorFunctional E F ab u‖ ≤ epsSeminorm A B u := by
  rw [epsSeminorm_apply A B hA hB]
  obtain ⟨M, hM⟩ := bddAbove_tensorFunctional A B hA hB u
  exact le_ciSup (f := fun ab : (A ×ˢ B : Set (StrongDual ℂ E × StrongDual ℂ F)) =>
    ‖tensorFunctional E F (ab : StrongDual ℂ E × StrongDual ℂ F) u‖)
    ⟨M, forall_mem_range.mpr fun ab => hM ab ab.2⟩ ⟨ab, hab⟩

theorem epsSeminorm_le [ContinuousSMul ℂ E] [ContinuousSMul ℂ F]
    (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F))
    (hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ)))
    (hB : Equicontinuous (fun b : B => ((b : StrongDual ℂ F) : F → ℂ))) (u : E ⊗[ℂ] F)
    {r : ℝ} (hr : 0 ≤ r) (h : ∀ ab ∈ A ×ˢ B, ‖tensorFunctional E F ab u‖ ≤ r) :
    epsSeminorm A B u ≤ r := by
  rw [epsSeminorm_apply A B hA hB]
  exact Real.iSup_le (fun ab => h ab ab.2) hr

variable (E F) in
/-- The family of sets on which the injective topology is the topology of uniform convergence. -/
def epsFamily : Set (Set (StrongDual ℂ E × StrongDual ℂ F)) :=
  {S : Set (StrongDual ℂ E × StrongDual ℂ F) |
    ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)),
      Equicontinuous (fun a : A => (a : E → ℂ)) ∧
      Equicontinuous (fun b : B => (b : F → ℂ)) ∧ S = A ×ˢ B}

variable (E F) in
/-- The canonical map `E ⊗ F → (E' × F' → ℂ)`, as an additive map into the space of functions
with the topology of uniform convergence on the sets `A × B`. -/
noncomputable def epsEmb :
    E ⊗[ℂ] F →+ UniformOnFun (StrongDual ℂ E × StrongDual ℂ F) ℂ (epsFamily E F) where
  toFun u := UniformOnFun.ofFun (epsFamily E F) (fun ab => tensorFunctional E F ab u)
  map_zero' := by
    apply congrArg (UniformOnFun.ofFun (epsFamily E F))
    funext ab
    exact tensorFunctional_zero ab
  map_add' u v := by
    apply congrArg (UniformOnFun.ofFun (epsFamily E F))
    funext ab
    exact tensorFunctional_add ab u v

theorem epsTensorTopology_eq :
    epsTensorTopology E F = TopologicalSpace.induced (epsEmb E F) inferInstance := rfl

/-- Convergence in the injective topology. -/
theorem tendsto_eps_iff {α : Type*} (l : Filter α) (g : α → E ⊗[ℂ] F) (u₀ : E ⊗[ℂ] F) :
    Tendsto g l (@nhds _ (epsTensorTopology E F) u₀) ↔
      ∀ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)),
        Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ)) →
        Equicontinuous (fun b : B => ((b : StrongDual ℂ F) : F → ℂ)) →
        ∀ ε > 0, ∀ᶠ n in l, ∀ ab ∈ A ×ˢ B,
          dist (tensorFunctional E F ab u₀) (tensorFunctional E F ab (g n)) < ε := by
  rw [epsTensorTopology_eq, nhds_induced, tendsto_comap_iff,
    UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  constructor
  · intro h A B hA hB ε hε
    exact Metric.tendstoUniformlyOn_iff.mp (h (A ×ˢ B) ⟨A, B, hA, hB, rfl⟩) ε hε
  · rintro h S ⟨A, B, hA, hB, rfl⟩
    exact Metric.tendstoUniformlyOn_iff.mpr (h A B hA hB)

/-- The injective topology on `E ⊗ F` is defined by the seminorms `epsSeminorm A B`, where `A`, `B`
run through the equicontinuous subsets of `E'`, `F'`. -/
theorem eps_isLocallyConvex [ContinuousSMul ℂ E] [ContinuousSMul ℂ F] :
    IsLocallyConvexTopology (E ⊗[ℂ] F) (epsTensorTopology E F) := by
  let ι : Type u := {AB : Set (StrongDual ℂ E) × Set (StrongDual ℂ F) //
    Equicontinuous (fun a : AB.1 => ((a : StrongDual ℂ E) : E → ℂ)) ∧
    Equicontinuous (fun b : AB.2 => ((b : StrongDual ℂ F) : F → ℂ))}
  have hne : Nonempty ι := by
    refine ⟨⟨(∅, ∅), ?_, ?_⟩⟩
    · intro x U _
      exact Filter.Eventually.of_forall fun z a => a.2.elim
    · intro x U _
      exact Filter.Eventually.of_forall fun z a => a.2.elim
  let q : SeminormFamily ℂ (E ⊗[ℂ] F) ι := fun i => epsSeminorm i.1.1 i.1.2
  refine ⟨ι, hne, q, ?_⟩
  let _ : TopologicalSpace (E ⊗[ℂ] F) := epsTensorTopology E F
  have hgrp : IsTopologicalAddGroup (E ⊗[ℂ] F) := by
    have h := topologicalAddGroup_induced (epsEmb E F)
    exact h
  refine (q.withSeminorms_iff_nhds_eq_iInf).mpr ?_
  refine le_antisymm (le_iInf fun i => ?_) ?_
  · -- every `q i` is continuous at `0`
    rw [← tendsto_iff_comap]
    have h := (tendsto_eps_iff (𝓝 (0 : E ⊗[ℂ] F)) id 0).mp tendsto_id
      i.1.1 i.1.2 i.2.1 i.2.2
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [h (ε / 2) (half_pos hε)] with u hu
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
    refine (epsSeminorm_le _ _ i.2.1 i.2.2 u (half_pos hε).le fun ab hab => ?_).trans_lt
      (half_lt_self hε)
    have h3 := hu ab hab
    rw [tensorFunctional_zero, dist_zero_left] at h3
    exact h3.le
  · -- the identity is continuous at `0` from the seminorm topology to the injective topology
    have h : Tendsto id (⨅ i, comap (q i) (𝓝 (0 : ℝ))) (𝓝 (0 : E ⊗[ℂ] F)) := by
      refine (tendsto_eps_iff _ _ _).mpr ?_
      intro A B hA hB ε hε
      have hmem : {u | q ⟨(A, B), hA, hB⟩ u < ε} ∈ ⨅ i, comap (q i) (𝓝 (0 : ℝ)) :=
        mem_iInf_of_mem (f := fun i => comap (q i) (𝓝 (0 : ℝ))) ⟨(A, B), hA, hB⟩
          (preimage_mem_comap (Iio_mem_nhds hε))
      filter_upwards [hmem] with u hu ab hab
      rw [tensorFunctional_zero, dist_zero_left]
      exact (le_epsSeminorm A B hA hB u ab hab).trans_lt hu
    exact h

/-- The canonical bilinear map `E × F → E ⊗_ε F` is (jointly) continuous. -/
theorem continuous_tmul_eps [ContinuousSMul ℂ E] [ContinuousSMul ℂ F] :
    @Continuous (E × F) (E ⊗[ℂ] F) _ (epsTensorTopology E F) (fun p => p.1 ⊗ₜ[ℂ] p.2) := by
  let _ : TopologicalSpace (E ⊗[ℂ] F) := epsTensorTopology E F
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  refine (tendsto_eps_iff _ _ _).mpr ?_
  intro A B hA hB ε hε
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_equicontinuous A hA x₀
  obtain ⟨N, hN0, hN⟩ := exists_bound_of_equicontinuous B hB y₀
  have hMN : 0 < M + N + 2 := by linarith
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ * (M + N + 2) ≤ ε := by
    refine ⟨min 1 (ε / (M + N + 2)), lt_min one_pos (div_pos hε hMN), min_le_left _ _, ?_⟩
    have h := min_le_right 1 (ε / (M + N + 2))
    rwa [le_div_iff₀ hMN] at h
  have hx := Metric.equicontinuousAt_iff_right.mp (hA x₀) δ hδ0
  have hy := Metric.equicontinuousAt_iff_right.mp (hB y₀) δ hδ0
  filter_upwards [hx.prod_nhds hy] with p hp ab hab
  obtain ⟨hp1, hp2⟩ := hp
  have h1 := hp1 ⟨ab.1, hab.1⟩
  have h2 := hp2 ⟨ab.2, hab.2⟩
  rw [dist_eq_norm] at h1 h2
  rw [tensorFunctional_tmul, tensorFunctional_tmul, dist_eq_norm]
  have key : ab.1 x₀ * ab.2 y₀ - ab.1 p.1 * ab.2 p.2 =
      ab.1 x₀ * (ab.2 y₀ - ab.2 p.2) + (ab.1 x₀ - ab.1 p.1) * ab.2 y₀ -
        (ab.1 x₀ - ab.1 p.1) * (ab.2 y₀ - ab.2 p.2) := by ring
  rw [key]
  have e1 : ‖ab.1 x₀ * (ab.2 y₀ - ab.2 p.2)‖ ≤ M * δ := by
    rw [norm_mul]
    exact mul_le_mul (hM _ hab.1) h2.le (norm_nonneg _) hM0
  have e2 : ‖(ab.1 x₀ - ab.1 p.1) * ab.2 y₀‖ ≤ δ * N := by
    rw [norm_mul]
    exact mul_le_mul h1.le (hN _ hab.2) (norm_nonneg _) hδ0.le
  have e3 : ‖(ab.1 x₀ - ab.1 p.1) * (ab.2 y₀ - ab.2 p.2)‖ ≤ δ * 1 := by
    rw [norm_mul]
    exact mul_le_mul h1.le (h2.le.trans hδ1) (norm_nonneg _) hδ0.le
  have e4 := (norm_sub_le (ab.1 x₀ * (ab.2 y₀ - ab.2 p.2) + (ab.1 x₀ - ab.1 p.1) * ab.2 y₀)
    ((ab.1 x₀ - ab.1 p.1) * (ab.2 y₀ - ab.2 p.2))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  linarith

end Sol_MasulloGRH_indTensor_le_projTensor_le_epsTensor

open MasulloGRH in
open Sol_MasulloGRH_indTensor_le_projTensor_le_epsTensor in
theorem solution (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F) :
    indTensorTopology E F ≤ projTensorTopology E F ∧
      projTensorTopology E F ≤ epsTensorTopology E F := by
  refine ⟨?_, ?_⟩
  · -- a jointly continuous map is separately continuous
    refine sInf_le_sInf fun t ht => ⟨ht.1, fun x => ?_, fun y => ?_⟩
    · exact @Continuous.comp F (E × F) (E ⊗[ℂ] F) _ _ t _ _ ht.2
        (continuous_const.prodMk continuous_id)
    · exact @Continuous.comp E (E × F) (E ⊗[ℂ] F) _ _ t _ _ ht.2
        (continuous_id.prodMk continuous_const)
  · -- the injective topology is locally convex and makes `⊗` continuous
    obtain ⟨⟨_, _, p, hp⟩, _⟩ := hE
    obtain ⟨⟨_, _, p', hp'⟩, _⟩ := hF
    have : ContinuousSMul ℂ E := hp.continuousSMul
    have : ContinuousSMul ℂ F := hp'.continuousSMul
    exact sInf_le ⟨eps_isLocallyConvex, continuous_tmul_eps⟩
