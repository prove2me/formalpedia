-- Prove2me | solution 1 for MasulloGRH.epsTensor_map_isEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:25:49.634802+00:00
-- url     : https://prove2.me/submissions/1dda2c95-4475-447d-986d-dddb17c1bf1d

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace Sol_MasulloGRH_epsTensor_map_isEmbedding

open MasulloGRH Set
open scoped NNReal

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

variable (E F) in
/-- The family of sets on which the injective topology is the topology of uniform convergence. -/
def epsFamily : Set (Set (StrongDual ℂ E × StrongDual ℂ F)) :=
  {S : Set (StrongDual ℂ E × StrongDual ℂ F) |
    ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)),
      Equicontinuous (fun a : A => (a : E → ℂ)) ∧
      Equicontinuous (fun b : B => (b : F → ℂ)) ∧ S = A ×ˢ B}

variable (E F) in
/-- The canonical map `E ⊗ F → (E' × F' → ℂ)` into the space of functions with the topology of
uniform convergence on the sets `A × B`. -/
noncomputable def epsEmb (u : E ⊗[ℂ] F) :
    UniformOnFun (StrongDual ℂ E × StrongDual ℂ F) ℂ (epsFamily E F) :=
  UniformOnFun.ofFun (epsFamily E F) (fun ab => tensorFunctional E F ab u)

theorem epsTensorTopology_eq :
    epsTensorTopology E F = TopologicalSpace.induced (epsEmb E F) inferInstance := rfl

/-- Convergence in the injective topology: uniform convergence of `(x', y') ↦ (x' ⊗ y')(u)` on the
products `A × B` of equicontinuous sets. -/
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

end basic

section single

variable {E : Type u} {F : Type v} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The transposes `y' ∘ T` of an equicontinuous set of functionals under a continuous linear map
`T` form an equicontinuous set. -/
theorem equicontinuous_image_comp (T : E →L[ℂ] F) (B : Set (StrongDual ℂ F))
    (hB : Equicontinuous (fun b : B => ((b : StrongDual ℂ F) : F → ℂ))) :
    Equicontinuous (fun a : ((fun b : StrongDual ℂ F => b.comp T) '' B : Set (StrongDual ℂ E)) =>
      ((a : StrongDual ℂ E) : E → ℂ)) := by
  intro x₀ U hU
  have h := (T.continuous.tendsto x₀).eventually (hB (T x₀) U hU)
  filter_upwards [h] with x hx
  rintro ⟨a, b, hb, rfl⟩
  exact hx ⟨b, hb⟩

/-- An equicontinuous set of linear functionals on a space whose topology is defined by the
seminorms `p i` is dominated by a multiple of a finite supremum of the `p i`. -/
theorem exists_bound_of_equicontinuous {ι : Type*} {p : SeminormFamily ℂ E ι}
    (hp : WithSeminorms p) (A : Set (StrongDual ℂ E))
    (hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ))) :
    ∃ (s : Finset ι) (C : ℝ≥0), ∀ a ∈ A, ∀ x, ‖a x‖ ≤ (C • s.sup p) x := by
  have h0 := Metric.equicontinuousAt_iff_right.mp (hA 0) 1 one_pos
  obtain ⟨s, r, hr, hsub⟩ := (hp.mem_nhds_iff _ _).mp h0
  refine ⟨s, ⟨r⁻¹, (inv_pos.mpr hr).le⟩, fun a ha x => ?_⟩
  have key : ∀ c : ℝ, (s.sup p) x < c → ‖a x‖ ≤ r⁻¹ * c := by
    intro c hc
    have hc0 : 0 < c := (apply_nonneg (s.sup p) x).trans_lt hc
    have hrc : 0 < r / c := div_pos hr hc0
    have hmem : ((r / c : ℝ) : ℂ) • x ∈ (s.sup p).ball 0 r := by
      rw [Seminorm.mem_ball_zero, map_smul_eq_mul, Complex.norm_real,
        Real.norm_of_nonneg hrc.le]
      calc r / c * (s.sup p) x < r / c * c := mul_lt_mul_of_pos_left hc hrc
        _ = r := div_mul_cancel₀ r hc0.ne'
    have h1 : dist (a 0) (a (((r / c : ℝ) : ℂ) • x)) < 1 := hsub hmem ⟨a, ha⟩
    rw [map_zero, dist_zero_left, map_smul, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hrc.le] at h1
    have h2 : ‖a x‖ < c / r := by
      rw [lt_div_iff₀ hr]
      have h3 : r / c * ‖a x‖ * c < 1 * c := mul_lt_mul_of_pos_right h1 hc0
      have h4 : r / c * ‖a x‖ * c = ‖a x‖ * r := by
        field_simp
      linarith
    rw [inv_mul_eq_div]
    exact h2.le
  have hfin : ‖a x‖ ≤ r⁻¹ * (s.sup p) x := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h5 := key ((s.sup p) x + r * ε) (by linarith [mul_pos hr hε])
    have h6 : r⁻¹ * ((s.sup p) x + r * ε) = r⁻¹ * (s.sup p) x + ε := by
      field_simp
    linarith
  exact hfin

/-- The continuous linear functionals dominated by a continuous seminorm form an equicontinuous
set. -/
theorem equicontinuous_of_le_seminorm [IsTopologicalAddGroup F] (Q : Seminorm ℂ F)
    (hQ : Continuous Q) :
    Equicontinuous (fun b : ({b : StrongDual ℂ F | ∀ y, ‖b y‖ ≤ Q y} : Set (StrongDual ℂ F)) =>
      ((b : StrongDual ℂ F) : F → ℂ)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have ht : Tendsto (fun x => Q (x₀ - x)) (𝓝 x₀) (𝓝 0) := by
    have hc : Continuous (fun x : F => Q (x₀ - x)) :=
      hQ.comp (continuous_const.sub continuous_id)
    have h := hc.tendsto x₀
    rw [sub_self, map_zero] at h
    exact h
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with x hx
  rintro ⟨b, hb⟩
  rw [dist_eq_norm, ← map_sub]
  exact (hb _).trans_lt hx

/-- **Hahn–Banach for equicontinuous sets.** Let `T : E → F` be a linear topological embedding into
a locally convex space.  Every equicontinuous set `A` of continuous linear functionals on `E` is
contained in the set of restrictions `y' ∘ T` of an equicontinuous set `B` of continuous linear
functionals on `F`. -/
theorem exists_equicontinuous_extension {ι : Type*} {q : SeminormFamily ℂ F ι}
    (hq : WithSeminorms q) (T : E →L[ℂ] F) (hT : Topology.IsEmbedding T)
    (A : Set (StrongDual ℂ E))
    (hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ))) :
    ∃ B : Set (StrongDual ℂ F),
      Equicontinuous (fun b : B => ((b : StrongDual ℂ F) : F → ℂ)) ∧
      ∀ a ∈ A, ∃ b ∈ B, b.comp T = a := by
  have hgrp : IsTopologicalAddGroup F := hq.topologicalAddGroup
  -- the topology of `E` is defined by the seminorms `q i ∘ T`
  have hind : Topology.IsInducing (T : E →ₗ[ℂ] F) := hT.isInducing
  have hp : WithSeminorms (q.comp (T : E →ₗ[ℂ] F)) := hind.withSeminorms hq
  obtain ⟨s, C, hbound⟩ := exists_bound_of_equicontinuous hp A hA
  let Q : Seminorm ℂ F := C • s.sup q
  have hQ : Continuous Q :=
    Continuous.const_smul (Seminorm.continuous_finsetSup fun i _ => hq.continuous_seminorm i) C
  refine ⟨{b : StrongDual ℂ F | ∀ y, ‖b y‖ ≤ Q y}, equicontinuous_of_le_seminorm Q hQ,
    fun a ha => ?_⟩
  -- the functional `T x ↦ a x` on the range of `T`
  have hTinj : Function.Injective (T : E →ₗ[ℂ] F) := hT.injective
  let e : E ≃ₗ[ℂ] LinearMap.range (T : E →ₗ[ℂ] F) := LinearEquiv.ofInjective _ hTinj
  let f : Module.Dual ℂ (LinearMap.range (T : E →ₗ[ℂ] F)) := (a : E →ₗ[ℂ] ℂ) ∘ₗ e.symm.toLinearMap
  have hf : ∀ y : LinearMap.range (T : E →ₗ[ℂ] F), ‖f y‖ ≤ Q y := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 : f (e x) = a x := by
      simp [f]
    rw [h1]
    have h2 := hbound a ha x
    rw [← SeminormFamily.finset_sup_comp, ← Seminorm.smul_comp] at h2
    exact h2
  obtain ⟨g, hg, hgQ⟩ := Module.Dual.exists_extension_of_le_seminorm _ f hf
  have hgc : Continuous g :=
    hq.continuous_normedSpace_rng ℂ g ⟨s, C, fun y => hgQ y⟩
  refine ⟨⟨g, hgc⟩, hgQ, ?_⟩
  ext x
  have h3 := hg (e x)
  have h4 : f (e x) = a x := by
    simp [f]
  rw [h4] at h3
  exact h3

end single

section main

variable {E₁ E₂ : Type u} {F₁ F₂ : Type v}
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]

/-- `(y₁' ⊗ y₂')((T₁ ⊗ T₂) u) = ((y₁' ∘ T₁) ⊗ (y₂' ∘ T₂))(u)`. -/
theorem tensorFunctional_map (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂)
    (ab : StrongDual ℂ F₁ × StrongDual ℂ F₂) (u : E₁ ⊗[ℂ] E₂) :
    tensorFunctional F₁ F₂ ab (TensorProduct.map T₁.toLinearMap T₂.toLinearMap u) =
      tensorFunctional E₁ E₂ (ab.1.comp T₁, ab.2.comp T₂) u := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, tensorFunctional_zero, tensorFunctional_zero]
  | tmul x y =>
    rw [TensorProduct.map_tmul, tensorFunctional_tmul, tensorFunctional_tmul]
    rfl
  | add v w hv hw => rw [map_add, tensorFunctional_add, tensorFunctional_add, hv, hw]

theorem eps_map_isEmbedding {ι κ : Type*} {q₁ : SeminormFamily ℂ F₁ ι} (hq₁ : WithSeminorms q₁)
    {q₂ : SeminormFamily ℂ F₂ κ} (hq₂ : WithSeminorms q₂)
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂)
    (h₁ : Topology.IsEmbedding T₁) (h₂ : Topology.IsEmbedding T₂) :
    @Topology.IsEmbedding (E₁ ⊗[ℂ] E₂) (F₁ ⊗[ℂ] F₂) (epsTensorTopology E₁ E₂)
      (epsTensorTopology F₁ F₂) (TensorProduct.map T₁.toLinearMap T₂.toLinearMap) := by
  have hinj : Function.Injective (TensorProduct.map T₁.toLinearMap T₂.toLinearMap) :=
    TensorProduct.map_injective_of_flat_flat _ _ h₁.injective h₂.injective
  refine @Topology.IsEmbedding.mk _ _ (epsTensorTopology E₁ E₂) (epsTensorTopology F₁ F₂) _
    (@Topology.IsInducing.mk _ _ (epsTensorTopology E₁ E₂) (epsTensorTopology F₁ F₂) _ ?_) hinj
  refine TopologicalSpace.ext_nhds fun u => ?_
  rw [@nhds_induced _ _ (epsTensorTopology F₁ F₂)]
  refine le_antisymm ?_ ?_
  · -- `T₁ ⊗ T₂` is continuous
    rw [← tendsto_iff_comap, tendsto_eps_iff]
    intro A B hA hB ε hε
    have h := (tendsto_eps_iff (@nhds _ (epsTensorTopology E₁ E₂) u) id u).mp tendsto_id
      _ _ (equicontinuous_image_comp T₁ A hA) (equicontinuous_image_comp T₂ B hB) ε hε
    filter_upwards [h] with v hv ab hab
    rw [tensorFunctional_map, tensorFunctional_map]
    exact hv (ab.1.comp T₁, ab.2.comp T₂) ⟨mem_image_of_mem _ hab.1, mem_image_of_mem _ hab.2⟩
  · -- the injective topology of `E₁ ⊗ E₂` is coarser than the induced one
    refine tendsto_id'.mp ?_
    rw [tendsto_eps_iff]
    intro A B hA hB ε hε
    obtain ⟨A', hA', hAext⟩ := exists_equicontinuous_extension hq₁ T₁ h₁ A hA
    obtain ⟨B', hB', hBext⟩ := exists_equicontinuous_extension hq₂ T₂ h₂ B hB
    have h := (tendsto_eps_iff
      (comap (TensorProduct.map T₁.toLinearMap T₂.toLinearMap)
        (@nhds _ (epsTensorTopology F₁ F₂) (TensorProduct.map T₁.toLinearMap T₂.toLinearMap u)))
      (TensorProduct.map T₁.toLinearMap T₂.toLinearMap)
      (TensorProduct.map T₁.toLinearMap T₂.toLinearMap u)).mp tendsto_comap A' B' hA' hB' ε hε
    filter_upwards [h] with v hv ab hab
    obtain ⟨a', ha', ha'e⟩ := hAext ab.1 hab.1
    obtain ⟨b', hb', hb'e⟩ := hBext ab.2 hab.2
    have h7 := hv (a', b') ⟨ha', hb'⟩
    rw [tensorFunctional_map, tensorFunctional_map] at h7
    simp only [ha'e, hb'e] at h7
    exact h7

end main

end Sol_MasulloGRH_epsTensor_map_isEmbedding

open MasulloGRH in
open Sol_MasulloGRH_epsTensor_map_isEmbedding in
theorem solution (E₁ E₂ : Type u) (F₁ F₂ : Type v)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂) (hF₁ : IsHLCS F₁) (hF₂ : IsHLCS F₂)
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂)
    (h₁ : Topology.IsEmbedding T₁) (h₂ : Topology.IsEmbedding T₂) :
    @Topology.IsEmbedding (E₁ ⊗[ℂ] E₂) (F₁ ⊗[ℂ] F₂) (epsTensorTopology E₁ E₂)
      (epsTensorTopology F₁ F₂) (TensorProduct.map T₁.toLinearMap T₂.toLinearMap) := by
  obtain ⟨⟨_, _, q₁, hq₁⟩, -⟩ := hF₁
  obtain ⟨⟨_, _, q₂, hq₂⟩, -⟩ := hF₂
  exact eps_map_isEmbedding hq₁ hq₂ T₁ T₂ h₁ h₂
