-- Prove2me | solution 1 for MasulloGRH.weakDual_isNuclear
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:26:54.966582+00:00
-- url     : https://prove2.me/submissions/6706d1fd-52ef-428c-92a0-05fe39ad7c1f

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_indTensor_le_projTensor_le_epsTensor

open Topology
set_option autoImplicit false
universe u

namespace Sol_MasulloGRH_weakDual_isNuclear

open MasulloGRH TensorProduct Filter Set

section general

variable {E F : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The functional `x' ⊗ y'` as a linear map on `E ⊗ F`. -/
noncomputable def tfLin (ab : StrongDual ℂ E × StrongDual ℂ F) : E ⊗[ℂ] F →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
    TensorProduct.map (ab.1 : E →ₗ[ℂ] ℂ) (ab.2 : F →ₗ[ℂ] ℂ)

theorem tfLin_apply (ab : StrongDual ℂ E × StrongDual ℂ F) (u : E ⊗[ℂ] F) :
    tfLin ab u = tensorFunctional E F ab u := rfl

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

/-- The injective topology is a group topology. -/
theorem eps_isTopologicalAddGroup :
    @IsTopologicalAddGroup (E ⊗[ℂ] F) (epsTensorTopology E F) _ := by
  let _ : TopologicalSpace (E ⊗[ℂ] F) := epsTensorTopology E F
  have h := topologicalAddGroup_induced (epsEmb E F)
  exact h

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

/-- A singleton of continuous linear functionals is equicontinuous. -/
theorem equicontinuous_singleton (x' : StrongDual ℂ E) :
    Equicontinuous (fun a : ({x'} : Set (StrongDual ℂ E)) => ((a : StrongDual ℂ E) : E → ℂ)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have h := Metric.tendsto_nhds.mp (x'.continuous.tendsto x₀) ε hε
  filter_upwards [h] with x hx
  rintro ⟨a, ha⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  rw [dist_comm]
  exact hx

/-- The set of continuous linear functionals dominated by a continuous seminorm is
equicontinuous. -/
theorem equicontinuous_of_le_seminorm [IsTopologicalAddGroup F] (q : Seminorm ℂ F)
    (hq : Continuous q) :
    Equicontinuous (fun b : {b : StrongDual ℂ F | ∀ y, ‖b y‖ ≤ q y} =>
      ((b : StrongDual ℂ F) : F → ℂ)) := by
  intro y₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hc : Continuous fun y : F => q (y₀ - y) := hq.comp (continuous_const.sub continuous_id)
  have h0 : Tendsto (fun y : F => q (y₀ - y)) (𝓝 y₀) (𝓝 0) := by
    have h := hc.tendsto y₀
    simpa using h
  filter_upwards [h0.eventually (Iio_mem_nhds hε)] with y hy
  rintro ⟨b, hb⟩
  rw [dist_eq_norm, ← map_sub]
  exact (hb (y₀ - y)).trans_lt hy

/-- The slice map `φ ⊗ id : E ⊗ F → F`, `x ⊗ y ↦ φ(x) y`. -/
noncomputable def sliceRight (φ : E →ₗ[ℂ] ℂ) : E ⊗[ℂ] F →ₗ[ℂ] F :=
  (TensorProduct.lid ℂ F).toLinearMap ∘ₗ LinearMap.rTensor F φ

theorem sliceRight_tmul (φ : E →ₗ[ℂ] ℂ) (x : E) (y : F) :
    sliceRight φ (x ⊗ₜ[ℂ] y) = φ x • y := by
  simp [sliceRight]

theorem apply_sliceRight (φ : StrongDual ℂ E) (ψ : StrongDual ℂ F) (u : E ⊗[ℂ] F) :
    ψ (sliceRight (φ : E →ₗ[ℂ] ℂ) u) = tensorFunctional E F (φ, ψ) u := by
  induction u using TensorProduct.induction_on with
  | zero => simp [tensorFunctional]
  | tmul x y => simp [sliceRight, tensorFunctional]
  | add v w hv hw => simp only [map_add, hv, hw, tensorFunctional_add]

end general

/-- **Hahn–Banach** for one vector: a seminorm is attained at a given vector by a linear
functional dominated by it. -/
theorem exists_dual_le_seminorm {F : Type*} [AddCommGroup F] [Module ℂ F] (q : Seminorm ℂ F)
    (z : F) : ∃ g : F →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ q y) ∧ ‖g z‖ = q z := by
  by_cases hz : q z = 0
  · exact ⟨0, fun y => by simp, by simp [hz]⟩
  · have hz0 : z ≠ 0 := fun h => hz (by rw [h, map_zero])
    let f : Module.Dual ℂ (ℂ ∙ z) :=
      ((q z : ℝ) : ℂ) • (LinearEquiv.coord ℂ F z hz0).toLinearMap
    have hf : ∀ y : (ℂ ∙ z), ‖f y‖ ≤ q y := by
      intro y
      have hy := LinearEquiv.coord_apply_smul ℂ F z hz0 y
      have h1 : ‖f y‖ = q z * ‖LinearEquiv.coord ℂ F z hz0 y‖ := by
        simp [f, abs_of_nonneg (apply_nonneg q z)]
      have h3 : q (y : F) = ‖LinearEquiv.coord ℂ F z hz0 y‖ * q z := by
        rw [← map_smul_eq_mul, hy]
      rw [h1, h3, mul_comm]
    obtain ⟨g, hg, hgq⟩ := Module.Dual.exists_extension_of_le_seminorm (ℂ ∙ z) f (p := q) hf
    refine ⟨g, hgq, ?_⟩
    have h2 := hg ⟨z, Submodule.mem_span_singleton_self z⟩
    simp only at h2
    rw [h2]
    simp [f, LinearEquiv.coord_self, abs_of_nonneg (apply_nonneg q z)]

/-- A linear functional dominated by a continuous seminorm is continuous. -/
theorem continuous_of_le_seminorm {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] (q : Seminorm ℂ F) (hq : Continuous q) (g : F →ₗ[ℂ] ℂ)
    (hg : ∀ y, ‖g y‖ ≤ q y) : Continuous g := by
  refine continuous_of_continuousAt_zero g.toAddMonoidHom ?_
  have h0 : Tendsto q (𝓝 0) (𝓝 0) := by simpa using hq.tendsto 0
  show Tendsto g (𝓝 0) (𝓝 (g 0))
  rw [map_zero]
  exact squeeze_zero_norm hg h0

/-- A linear map over a field has a generalized inverse. -/
theorem exists_genInv {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (R : V →ₗ[ℂ] V') : ∃ σ : V' →ₗ[ℂ] V, ∀ v, R (σ (R v)) = R v := by
  obtain ⟨τ, hτ⟩ := R.rangeRestrict.exists_rightInverse_of_surjective R.range_rangeRestrict
  obtain ⟨π, hπ⟩ := (LinearMap.range R).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  refine ⟨τ ∘ₗ π, fun v => ?_⟩
  have h1 : π (R v) = R.rangeRestrict v := LinearMap.congr_fun hπ (R.rangeRestrict v)
  have h2 : R.rangeRestrict (τ (R.rangeRestrict v)) = R.rangeRestrict v :=
    LinearMap.congr_fun hτ (R.rangeRestrict v)
  rw [LinearMap.comp_apply, h1]
  exact congrArg Subtype.val h2

section slice

variable {E F : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- For a continuous linear functional `φ` on `E` and a locally convex space `F`, the slice map
`φ ⊗ id : E ⊗_ε F → F` is continuous. -/
theorem continuous_sliceRight {κ : Type*} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q)
    (φ : StrongDual ℂ E) :
    @Continuous (E ⊗[ℂ] F) F (epsTensorTopology E F) _ (sliceRight (φ : E →ₗ[ℂ] ℂ)) := by
  let _ : TopologicalSpace (E ⊗[ℂ] F) := epsTensorTopology E F
  have hgrp : IsTopologicalAddGroup (E ⊗[ℂ] F) := eps_isTopologicalAddGroup
  have hF : IsTopologicalAddGroup F := hq.topologicalAddGroup
  refine continuous_of_continuousAt_zero (sliceRight (φ : E →ₗ[ℂ] ℂ)).toAddMonoidHom ?_
  show Tendsto (sliceRight (φ : E →ₗ[ℂ] ℂ)) (𝓝 0) (𝓝 (sliceRight (φ : E →ₗ[ℂ] ℂ) 0))
  rw [map_zero, hq.tendsto_nhds _ 0]
  intro j ε hε
  have hqc : Continuous (q j) := hq.continuous_seminorm j
  have h := (tendsto_eps_iff (𝓝 (0 : E ⊗[ℂ] F)) id 0).mp tendsto_id {φ}
    {b : StrongDual ℂ F | ∀ y, ‖b y‖ ≤ q j y} (equicontinuous_singleton φ)
    (equicontinuous_of_le_seminorm (q j) hqc) ε hε
  filter_upwards [h] with u hu
  rw [sub_zero]
  obtain ⟨g, hg1, hg2⟩ := exists_dual_le_seminorm (q j) (sliceRight (φ : E →ₗ[ℂ] ℂ) u)
  have hgc : Continuous g := continuous_of_le_seminorm (q j) hqc g hg1
  have h3 := hu (φ, (⟨g, hgc⟩ : StrongDual ℂ F)) ⟨rfl, hg1⟩
  rw [tensorFunctional_zero, dist_zero_left, ← apply_sliceRight] at h3
  rw [← hg2]
  exact h3

end slice

section weak

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- The weak dual is a Hausdorff locally convex space. -/
theorem weakDual_isHLCS : IsHLCS (WeakDual ℂ E) :=
  ⟨⟨E, ⟨0⟩, (topDualPairing ℂ E).toSeminormFamily,
    LinearMap.weakBilin_withSeminorms (topDualPairing ℂ E)⟩, inferInstance⟩

variable {E}

/-- Evaluation at a point, as a continuous linear functional on the weak dual. -/
noncomputable def evalL (x : E) : StrongDual ℂ (WeakDual ℂ E) where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := WeakDual.eval_continuous x

theorem evalL_apply (x : E) (f : WeakDual ℂ E) : evalL x f = f x := rfl


/-- The key estimate.  Let `p` be a seminorm on `E'_σ ⊗ F` such that `(f, y) ↦ p (f ⊗ y)` is
continuous on `E'_σ × F`, where `F` is locally convex.  Then `p` is continuous for the injective
topology. -/
theorem seminorm_continuous_eps {F : Type u} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    {κ : Type*} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q)
    (p : Seminorm ℂ (WeakDual ℂ E ⊗[ℂ] F))
    (hp : Continuous (fun xy : WeakDual ℂ E × F => p (xy.1 ⊗ₜ[ℂ] xy.2))) :
    @Continuous (WeakDual ℂ E ⊗[ℂ] F) ℝ (epsTensorTopology (WeakDual ℂ E) F) _ p := by
  classical
  have hsmul : ContinuousSMul ℂ F := hq.continuousSMul
  -- Step 1: `p (f ⊗ y) < 1` on a product neighbourhood `U × V` of `(0, 0)`
  have h00 : {xy : WeakDual ℂ E × F | p (xy.1 ⊗ₜ[ℂ] xy.2) < 1} ∈
      𝓝 ((0 : WeakDual ℂ E), (0 : F)) := by
    have h := hp.tendsto ((0 : WeakDual ℂ E), (0 : F))
    simp only [TensorProduct.zero_tmul, map_zero] at h
    exact h (Iio_mem_nhds one_pos)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp h00
  -- Step 2: `U` contains the annihilator of a finite set `s ⊆ E`
  obtain ⟨s, r, hr, hsU⟩ :=
    ((LinearMap.weakBilin_withSeminorms (topDualPairing ℂ E)).mem_nhds_iff 0 U).mp hU
  have hU' : ∀ f : WeakDual ℂ E, (∀ x ∈ s, evalL x f = 0) → f ∈ U := by
    intro f hf
    refine hsU (Iff.mpr (Seminorm.mem_ball_zero _)
      (Seminorm.finset_sup_apply_lt hr fun x hx => ?_))
    have h1 : (topDualPairing ℂ E).toSeminormFamily x f = ‖evalL x f‖ := rfl
    refine lt_of_eq_of_lt h1 ?_
    rw [hf x hx, norm_zero]
    exact hr
  -- Step 3: `p (k ⊗ y) = 0` whenever `k` vanishes on `s`
  have hK : ∀ k : WeakDual ℂ E, (∀ x ∈ s, evalL x k = 0) → ∀ y : F, p (k ⊗ₜ[ℂ] y) = 0 := by
    intro k hk y
    have hc : Tendsto (fun c : ℂ => c • y) (𝓝 0) (𝓝 (0 : F)) := by
      have : Continuous (fun c : ℂ => c • y) := continuous_id.smul continuous_const
      simpa using this.tendsto 0
    obtain ⟨c, hcV, hc0⟩ := (((hc.eventually hV).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (a := (0 : ℂ)) (s := {0}ᶜ))).exists
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    by_contra hne
    have hpos : 0 < p (k ⊗ₜ[ℂ] y) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hne)
    have hmem : ((((‖c‖ * p (k ⊗ₜ[ℂ] y))⁻¹ : ℝ) : ℂ) • k, c • y) ∈ U ×ˢ V := by
      refine ⟨hU' _ fun x hx => ?_, hcV⟩
      rw [map_smul, hk x hx, smul_zero]
    have h1 : p (((((‖c‖ * p (k ⊗ₜ[ℂ] y))⁻¹ : ℝ) : ℂ) • k) ⊗ₜ[ℂ] (c • y)) < 1 := hUV hmem
    simp only [TensorProduct.smul_tmul_smul, map_smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs] at h1
    rw [abs_of_pos (inv_pos.mpr (mul_pos hcpos hpos)), mul_assoc,
      inv_mul_cancel₀ (mul_pos hcpos hpos).ne'] at h1
    exact lt_irrefl _ h1
  -- Step 4: a finite family `g a ∈ E'`, `a ∈ s`, with `f - ∑ a, f a • g a` vanishing on `s`
  let R : WeakDual ℂ E →ₗ[ℂ] (s → ℂ) :=
    LinearMap.pi fun a => (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ)
  obtain ⟨σ, hσ⟩ := exists_genInv R
  let g : s → WeakDual ℂ E := fun a => σ (Pi.single a 1)
  have hdec : ∀ f : WeakDual ℂ E, ∀ x ∈ s,
      evalL x (f - ∑ a : s, evalL (a : E) f • g a) = 0 := by
    intro f x hx
    have h1 : ∑ a : s, evalL (a : E) f • g a = σ (R f) := by
      have h2 : R f = ∑ a : s, evalL (a : E) f • (Pi.single a 1 : s → ℂ) := by
        ext b
        simp [R, Finset.sum_apply, Pi.single_apply]
      rw [h2, map_sum]
      exact Finset.sum_congr rfl fun a _ => (map_smul σ _ _).symm
    have h3 : evalL x (σ (R f)) = evalL x f := congrFun (hσ f) ⟨x, hx⟩
    rw [h1, map_sub, h3, sub_self]
  -- Step 5: `p (u - T u) = 0`, where `T u = ∑ a, g a ⊗ (ev_a ⊗ id) u`
  have hT : ∀ u : WeakDual ℂ E ⊗[ℂ] F,
      p (u - ∑ a : s, g a ⊗ₜ[ℂ] sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) u) = 0 := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul f y =>
      have h1 : f ⊗ₜ[ℂ] y - ∑ a : s, g a ⊗ₜ[ℂ]
            sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) (f ⊗ₜ[ℂ] y) =
          (f - ∑ a : s, evalL (a : E) f • g a) ⊗ₜ[ℂ] y := by
        rw [TensorProduct.sub_tmul, TensorProduct.sum_tmul]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sliceRight_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rfl
      rw [h1]
      exact hK _ (hdec f) y
    | add u v hu hv =>
      have h1 : (u + v) - ∑ a : s, g a ⊗ₜ[ℂ]
            sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) (u + v) =
          (u - ∑ a : s, g a ⊗ₜ[ℂ] sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) u) +
          (v - ∑ a : s, g a ⊗ₜ[ℂ] sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) v) := by
        simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
        abel
      rw [h1]
      refine le_antisymm ((map_add_le_add p _ _).trans ?_) (apply_nonneg _ _)
      rw [hu, hv, add_zero]
  -- Step 6: the bound `p u ≤ ∑ a, p (g a ⊗ (ev_a ⊗ id) u)`
  have hbound : ∀ u : WeakDual ℂ E ⊗[ℂ] F,
      p u ≤ ∑ a : s, p (g a ⊗ₜ[ℂ] sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) u) := by
    intro u
    have h1 : p u ≤ p (u - ∑ a : s, g a ⊗ₜ[ℂ]
          sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) u) +
        p (∑ a : s, g a ⊗ₜ[ℂ] sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) u) := by
      have h2 := map_add_le_add p (u - ∑ a : s, g a ⊗ₜ[ℂ]
          sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) u)
        (∑ a : s, g a ⊗ₜ[ℂ] sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) u)
      rwa [sub_add_cancel] at h2
    rw [hT u, zero_add] at h1
    exact h1.trans (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _)
  -- Step 7: continuity for the injective topology
  let _ : TopologicalSpace (WeakDual ℂ E ⊗[ℂ] F) := epsTensorTopology (WeakDual ℂ E) F
  have hgrp : IsTopologicalAddGroup (WeakDual ℂ E ⊗[ℂ] F) := eps_isTopologicalAddGroup
  refine Seminorm.continuous_of_continuousAt_zero ?_
  have hsum : Continuous (fun u : WeakDual ℂ E ⊗[ℂ] F =>
      ∑ a : s, p (g a ⊗ₜ[ℂ] sliceRight (evalL (a : E) : WeakDual ℂ E →ₗ[ℂ] ℂ) u)) := by
    refine continuous_finsetSum _ fun a _ => ?_
    have h1 : Continuous (fun y : F => p (g a ⊗ₜ[ℂ] y)) :=
      hp.comp (continuous_const.prodMk continuous_id)
    exact h1.comp (continuous_sliceRight hq (evalL (a : E)))
  have h0 := hsum.tendsto 0
  simp only [map_zero, TensorProduct.tmul_zero, Finset.sum_const_zero] at h0
  show Tendsto p (𝓝 0) (𝓝 (p 0))
  rw [map_zero]
  exact squeeze_zero (fun u => apply_nonneg p u) hbound h0

end weak

end Sol_MasulloGRH_weakDual_isNuclear

open MasulloGRH TensorProduct in
open Sol_MasulloGRH_weakDual_isNuclear in
theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) : IsNuclear (WeakDual ℂ E) := by
  have hN : IsHLCS (WeakDual ℂ E) := weakDual_isHLCS E
  refine ⟨hN, fun F _ _ _ hF => ?_⟩
  refine le_antisymm (indTensor_le_projTensor_le_epsTensor (WeakDual ℂ E) F hN hF).2 ?_
  obtain ⟨⟨κ, _, q, hq⟩, _⟩ := hF
  refine le_sInf ?_
  rintro t ⟨⟨ι, _, P, hP⟩, hcont⟩
  rw [← continuous_id_iff_le]
  have hgrp : @IsTopologicalAddGroup (WeakDual ℂ E ⊗[ℂ] F)
      (epsTensorTopology (WeakDual ℂ E) F) _ := eps_isTopologicalAddGroup
  refine @WithSeminorms.continuous_of_continuous_comp ℂ ℂ (WeakDual ℂ E ⊗[ℂ] F)
    (WeakDual ℂ E ⊗[ℂ] F) ι _ _ _ _ _ _ (RingHom.id ℂ) _ P
    (epsTensorTopology (WeakDual ℂ E) F) hgrp t hP LinearMap.id fun i => ?_
  have h1 : @Continuous (WeakDual ℂ E ⊗[ℂ] F) ℝ t _ (P i) :=
    hP.continuous_seminorm i
  have h2 : Continuous (fun xy : WeakDual ℂ E × F => P i (xy.1 ⊗ₜ[ℂ] xy.2)) :=
    @Continuous.comp (WeakDual ℂ E × F) (WeakDual ℂ E ⊗[ℂ] F) ℝ _ t _ _ _ h1 hcont
  exact seminorm_continuous_eps hq (P i) h2
