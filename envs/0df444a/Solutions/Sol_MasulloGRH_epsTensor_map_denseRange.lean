-- Prove2me | solution 1 for MasulloGRH.epsTensor_map_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:30:34.670825+00:00
-- url     : https://prove2.me/submissions/e15097d9-ab41-4fdc-ae85-7753db69a662

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace Sol_MasulloGRH_epsTensor_map_denseRange

open MasulloGRH Set

section basic

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

end basic

section main

variable {E₁ E₂ : Type u} {F₁ F₂ : Type v}
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]

/-- If `T₁`, `T₂` are continuous linear maps with dense range into topological vector spaces
`F₁`, `F₂`, then `T₁ ⊗ T₂` has dense range in `F₁ ⊗_ε F₂`. -/
theorem eps_map_denseRange [ContinuousSMul ℂ F₁] [ContinuousSMul ℂ F₂]
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂) (d₁ : DenseRange T₁) (d₂ : DenseRange T₂) :
    @DenseRange (F₁ ⊗[ℂ] F₂) (epsTensorTopology F₁ F₂) (E₁ ⊗[ℂ] E₂)
      (TensorProduct.map T₁.toLinearMap T₂.toLinearMap) := by
  let _ : TopologicalSpace (F₁ ⊗[ℂ] F₂) := epsTensorTopology F₁ F₂
  -- `F₁ ⊗_ε F₂` is a topological additive group
  have hgrp : IsTopologicalAddGroup (F₁ ⊗[ℂ] F₂) := by
    have h := topologicalAddGroup_induced (epsEmb F₁ F₂)
    exact h
  have hcont : Continuous (fun p : F₁ × F₂ => p.1 ⊗ₜ[ℂ] p.2) := continuous_tmul_eps
  -- the closure of the range of `T₁ ⊗ T₂` is an additive subgroup
  let R : AddSubgroup (F₁ ⊗[ℂ] F₂) :=
    (LinearMap.range (TensorProduct.map T₁.toLinearMap T₂.toLinearMap)).toAddSubgroup
  have hK : ∀ w : F₁ ⊗[ℂ] F₂, w ∈ R.topologicalClosure := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact R.topologicalClosure.zero_mem
    | tmul y₁ y₂ =>
      -- `(y₁, y₂)` is a limit of pairs `(T₁ x₁, T₂ x₂)` and `⊗` is continuous
      have hd : DenseRange (Prod.map T₁ T₂) := d₁.prodMap d₂
      have h1 : (y₁, y₂) ∈ closure (range (Prod.map T₁ T₂)) := hd (y₁, y₂)
      have hmaps : MapsTo (fun p : F₁ × F₂ => p.1 ⊗ₜ[ℂ] p.2) (range (Prod.map T₁ T₂))
          (R : Set (F₁ ⊗[ℂ] F₂)) := by
        rintro _ ⟨⟨x₁, x₂⟩, rfl⟩
        exact ⟨x₁ ⊗ₜ[ℂ] x₂, rfl⟩
      exact map_mem_closure (f := fun p : F₁ × F₂ => p.1 ⊗ₜ[ℂ] p.2) (x := (y₁, y₂))
        (t := (R : Set (F₁ ⊗[ℂ] F₂))) hcont h1 hmaps
    | add v w hv hw => exact R.topologicalClosure.add_mem hv hw
  intro w
  exact hK w

end main

end Sol_MasulloGRH_epsTensor_map_denseRange

open MasulloGRH in
open Sol_MasulloGRH_epsTensor_map_denseRange in
theorem solution (E₁ E₂ : Type u) (F₁ F₂ : Type v)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂) (hF₁ : IsHLCS F₁) (hF₂ : IsHLCS F₂)
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂)
    (h₁ : Topology.IsEmbedding T₁) (h₂ : Topology.IsEmbedding T₂)
    (d₁ : DenseRange T₁) (d₂ : DenseRange T₂) :
    @DenseRange (F₁ ⊗[ℂ] F₂) (epsTensorTopology F₁ F₂) (E₁ ⊗[ℂ] E₂)
      (TensorProduct.map T₁.toLinearMap T₂.toLinearMap) := by
  obtain ⟨⟨_, _, q₁, hq₁⟩, -⟩ := hF₁
  obtain ⟨⟨_, _, q₂, hq₂⟩, -⟩ := hF₂
  have : ContinuousSMul ℂ F₁ := hq₁.continuousSMul
  have : ContinuousSMul ℂ F₂ := hq₂.continuousSMul
  exact eps_map_denseRange T₁ T₂ d₁ d₂
