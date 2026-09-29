-- Prove2me | solution 1 for HairerSPDE.exists_memLp_representer_of_bounded_eval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T00:08:29.421851+00:00
-- url     : https://prove2.me/submissions/f2a2e784-baa6-46d5-896e-fa1bb8fd677a

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (C : ℝ) (hC : ∀ L : StrongDual ℝ B, |L h| ≤ C * (eLpNorm (fun x => L x) 2 μ).toReal) :
    ∃ h' : B → ℝ, Measurable h' ∧ MemLp h' 2 μ ∧
      (∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h) ∧
      (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0) := by
  classical
  have hLmem : ∀ L : StrongDual ℝ B, MemLp (fun x => L x) 2 μ :=
    fun L => IsGaussian.memLp_dual μ L 2 (by simp)
  let J : StrongDual ℝ B →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun L => (hLmem L).toLp _
      map_add' := fun L₁ L₂ => by
        show (hLmem (L₁ + L₂)).toLp _ = (hLmem L₁).toLp _ + (hLmem L₂).toLp _
        have hfg : (fun x => (L₁ + L₂) x) =ᵐ[μ] ((fun x => L₁ x) + (fun x => L₂ x)) := by
          filter_upwards with x
          simp
        have hc := MemLp.toLp_congr (hLmem (L₁ + L₂)) ((hLmem L₁).add (hLmem L₂)) hfg
        rw [hc, MemLp.toLp_add]
      map_smul' := fun c L => by
        show (hLmem (c • L)).toLp _ = c • (hLmem L).toLp _
        have hfg : (fun x => (c • L) x) =ᵐ[μ] (c • (fun x => L x)) := by
          filter_upwards with x
          simp
        have hc := MemLp.toLp_congr (hLmem (c • L)) ((hLmem L).const_smul c) hfg
        rw [hc, MemLp.toLp_const_smul] }
  have hJnorm : ∀ L : StrongDual ℝ B, ‖J L‖ = (eLpNorm (fun x => L x) 2 μ).toReal :=
    fun L => Lp.norm_toLp _ (hLmem L)
  let ev : StrongDual ℝ B →ₗ[ℝ] ℝ :=
    { toFun := fun L => L h
      map_add' := fun L₁ L₂ => by simp
      map_smul' := fun c L => by simp }
  have hker : LinearMap.ker J ≤ LinearMap.ker ev := by
    intro L hJL
    rw [LinearMap.mem_ker] at hJL ⊢
    have hnorm0 : ‖J L‖ = 0 := by rw [hJL]; simp
    have h0 : (eLpNorm (fun x => L x) 2 μ).toReal = 0 := by
      rw [← hJnorm L]; exact hnorm0
    have hle := hC L
    rw [h0, mul_zero] at hle
    have habs : |L h| = 0 := le_antisymm hle (abs_nonneg _)
    exact abs_eq_zero.mp habs
  let lift := (LinearMap.ker J).liftQ ev hker
  let F0 : LinearMap.range J →ₗ[ℝ] ℝ :=
    lift.comp J.quotKerEquivRange.symm.toLinearMap
  have hF0 : ∀ L : StrongDual ℝ B, F0 ⟨J L, ⟨L, rfl⟩⟩ = L h := by
    intro L
    have hmem : J L ∈ LinearMap.range J := ⟨L, rfl⟩
    have hev : ev L = L h := rfl
    have h1 : J.quotKerEquivRange.symm ⟨J L, hmem⟩ = (LinearMap.ker J).mkQ L :=
      LinearMap.quotKerEquivRange_symm_apply_image J L hmem
    have h1' : J.quotKerEquivRange.symm.toLinearMap ⟨J L, hmem⟩
        = (LinearMap.ker J).mkQ L := h1
    show (lift.comp J.quotKerEquivRange.symm.toLinearMap) ⟨J L, hmem⟩ = L h
    rw [LinearMap.comp_apply, h1', Submodule.mkQ_apply, Submodule.liftQ_apply, hev]
  have hbound : ∀ s : LinearMap.range J, ‖F0 s‖ ≤ |C| * ‖s‖ := by
    rintro ⟨_, ⟨L, rfl⟩⟩
    have hle := hC L
    have ht : 0 ≤ (eLpNorm (fun x => L x) 2 μ).toReal := ENNReal.toReal_nonneg
    have hCC : C * (eLpNorm (fun x => L x) 2 μ).toReal ≤
        |C| * (eLpNorm (fun x => L x) 2 μ).toReal :=
      mul_le_mul_of_nonneg_right (le_abs_self C) ht
    have habs : |L h| ≤ |C| * (eLpNorm (fun x => L x) 2 μ).toReal :=
      le_trans hle hCC
    rw [hF0 L, Real.norm_eq_abs]
    show |L h| ≤ |C| * ‖J L‖
    rw [hJnorm]
    exact habs
  let Fcont : StrongDual ℝ (LinearMap.range J) := F0.mkContinuous |C| hbound
  obtain ⟨G, hGext, -⟩ := exists_extension_norm_eq _ Fcont
  have hGval : ∀ L : StrongDual ℝ B, G (J L) = L h := by
    intro L
    have h1 := hGext (⟨J L, ⟨L, rfl⟩⟩ : LinearMap.range J)
    have h2 : ∀ s : LinearMap.range J, Fcont s = F0 s := fun s => rfl
    rw [h2, hF0] at h1
    exact h1
  let q : Lp ℝ 2 μ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm G
  have hRiesz : ∀ v : Lp ℝ 2 μ, G v = ⟪q, v⟫_ℝ := by
    intro v
    have h := InnerProductSpace.toDual_symm_apply (x := v) (y := G)
    exact h.symm
  -- Closed span and its projection.
  set R : Submodule ℝ (Lp ℝ 2 μ) :=
    Submodule.topologicalClosure (LinearMap.range J) with hRdef
  haveI : CompleteSpace R := by rw [hRdef]; infer_instance
  have hmemR : ∀ L : StrongDual ℝ B, (J L : Lp ℝ 2 μ) ∈ R :=
    fun L => Submodule.le_topologicalClosure _ ⟨L, rfl⟩
  have hproj_mem : R.starProjection q ∈ R :=
    Submodule.starProjection_apply_mem R q
  have hproj_inner : ∀ L : StrongDual ℝ B, ⟪R.starProjection q, J L⟫_ℝ = L h := by
    intro L
    have hGL : ⟪q, J L⟫_ℝ = L h := by rw [← hRiesz]; exact hGval L
    have h0 := Submodule.starProjection_inner_eq_zero (K := R) q (J L) (hmemR L)
    rw [inner_sub_left] at h0
    have heq : ⟪q, J L⟫_ℝ = ⟪R.starProjection q, J L⟫_ℝ :=
      sub_eq_zero.mp h0
    rw [← heq]; exact hGL
  -- Measurable representative of the projection.
  let pLp : Lp ℝ 2 μ := R.starProjection q
  have hmemLp_p : MemLp (⇑pLp) 2 μ := Lp.memLp pLp
  have haes : AEStronglyMeasurable (⇑pLp) μ := Lp.aestronglyMeasurable pLp
  refine ⟨haes.mk _, haes.measurable_mk, (memLp_congr_ae haes.ae_eq_mk).mp hmemLp_p, ?_, ?_⟩
  · intro L
    have hJL_ae : (⇑(J L) : B → ℝ) =ᵐ[μ] (fun x => L x) :=
      MemLp.coeFn_toLp (hLmem L)
    have hp_ae : (⇑pLp : B → ℝ) =ᵐ[μ] haes.mk _ := haes.ae_eq_mk
    have hint_ae : (fun x => haes.mk _ x * L x) =ᵐ[μ] (fun x => ⇑pLp x * ⇑(J L) x) :=
      (hp_ae.symm.mul hJL_ae.symm)
    have hinner_eq : (⟪pLp, J L⟫_ℝ : ℝ) = ∫ a, ⇑pLp a * ⇑(J L) a ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards with a
      rw [Real.inner_apply]
    have hLp : (⟪pLp, J L⟫_ℝ : ℝ) = L h := hproj_inner L
    calc ∫ x, haes.mk _ x * L x ∂μ
        = ∫ a, ⇑pLp a * ⇑(J L) a ∂μ := integral_congr_ae hint_ae
      _ = (⟪pLp, J L⟫_ℝ : ℝ) := hinner_eq.symm
      _ = L h := hLp
  · intro g hg hgorth
    let gLp : Lp ℝ 2 μ := hg.toLp g
    have hg_ae : (⇑gLp : B → ℝ) =ᵐ[μ] g := MemLp.coeFn_toLp hg
    have hp_ae : (⇑pLp : B → ℝ) =ᵐ[μ] haes.mk _ := haes.ae_eq_mk
    have hint_ae : (fun x => haes.mk _ x * g x) =ᵐ[μ] (fun x => ⇑pLp x * ⇑gLp x) :=
      (hp_ae.symm.mul hg_ae.symm)
    have hinner_eq : (⟪pLp, gLp⟫_ℝ : ℝ) = ∫ a, ⇑pLp a * ⇑gLp a ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards with a
      rw [Real.inner_apply]
    -- gLp is orthogonal to every J L.
    have hgL_inner : ∀ L : StrongDual ℝ B, (⟪gLp, J L⟫_ℝ : ℝ) = 0 := by
      intro L
      have hJL_ae : (⇑(J L) : B → ℝ) =ᵐ[μ] (fun x => L x) :=
        MemLp.coeFn_toLp (hLmem L)
      have hae : (fun x => ⇑gLp x * ⇑(J L) x) =ᵐ[μ] (fun x => g x * L x) :=
        (hg_ae.mul hJL_ae)
      have hdef : (⟪gLp, J L⟫_ℝ : ℝ) = ∫ a, ⇑gLp a * ⇑(J L) a ∂μ := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards with a
        rw [Real.inner_apply]
      rw [hdef, integral_congr_ae hae]
      exact hgorth L
    -- Hence gLp is orthogonal to the closed span R.
    have hgR : gLp ∈ Rᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      have hS : (LinearMap.range J : Set (Lp ℝ 2 μ)) ⊆ {u | ⟪gLp, u⟫_ℝ = 0} := by
        intro w hw
        obtain ⟨L, rfl⟩ := hw
        simp only [Set.mem_setOf_eq]
        exact hgL_inner L
      have hclosed : IsClosed {u : Lp ℝ 2 μ | ⟪gLp, u⟫_ℝ = 0} := by
        have hcont : Continuous (fun u : Lp ℝ 2 μ => ⟪gLp, u⟫_ℝ) :=
          (continuous_const).inner continuous_id
        exact isClosed_singleton.preimage hcont
      have hsub : (R : Set (Lp ℝ 2 μ)) ⊆ {u | ⟪gLp, u⟫_ℝ = 0} := by
        rw [hRdef, Submodule.topologicalClosure_coe]
        exact closure_minimal hS hclosed
      exact hsub hu
    have horth : (⟪pLp, gLp⟫_ℝ : ℝ) = 0 := by
      have h1 : (⟪gLp, pLp⟫_ℝ : ℝ) = 0 :=
        (Submodule.mem_orthogonal' R gLp).mp hgR pLp hproj_mem
      rw [real_inner_comm] at h1
      exact h1
    calc ∫ x, haes.mk _ x * g x ∂μ
        = ∫ a, ⇑pLp a * ⇑gLp a ∂μ := integral_congr_ae hint_ae
      _ = (⟪pLp, gLp⟫_ℝ : ℝ) := hinner_eq.symm
      _ = 0 := horth
