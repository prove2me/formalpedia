-- Prove2me | solution 1 for MasulloGRH.continuous_bilinear_seminorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:17:54.066806+00:00
-- url     : https://prove2.me/submissions/3c9baf77-a6cb-466c-b035-164ebad9d081

import Definitions.Def_MasulloGRH_LocallyConvex

open MasulloGRH Set Filter Topology Bornology
universe u

-- Unit-ball rescaling adapted from the campaign proof of projective tensor associativity.
/-- A positively homogeneous function bounded by `C` on the open unit ball of a seminorm `s`
is bounded by `C * s`. -/
theorem homog_bound {X : Type*} [AddCommGroup X] [Module ℂ X] (s : Seminorm ℂ X) (f : X → ℝ)
    (hf : ∀ (c : ℝ) (x : X), 0 < c → f ((c : ℂ) • x) = c * f x) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, s x < 1 → f x ≤ C) (x : X) : f x ≤ C * s x := by
  by_contra hlt
  rw [not_le] at hlt
  have hs0 : 0 ≤ s x := apply_nonneg s x
  have hdpos : 0 < f x - C * s x := by linarith
  have hC1 : 0 < C + 1 := by linarith
  have hεpos : 0 < (f x - C * s x) / (C + 1) := div_pos hdpos hC1
  set ε := (f x - C * s x) / (C + 1) with hε
  have hb : 0 < s x + ε := by linarith
  have hsx : s ((((s x + ε)⁻¹ : ℝ) : ℂ) • x) < 1 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hb.le),
      inv_mul_lt_iff₀ hb]
    linarith
  have h1 := h _ hsx
  rw [hf _ _ (inv_pos.2 hb), inv_mul_le_iff₀ hb] at h1
  have h3 : C * ε < f x - C * s x := by
    have : ε * (C + 1) = f x - C * s x := by
      rw [hε]; field_simp
    nlinarith
  nlinarith

/-- A `0`-neighbourhood of a locally convex space contains the open unit ball of a continuous
seminorm. -/
theorem exists_seminorm_ball_subset {X : Type u} [AddCommGroup X] [Module ℂ X]
    [t : TopologicalSpace X] (h : IsLocallyConvexTopology X t) {U : Set X}
    (hU : U ∈ 𝓝 (0 : X)) :
    ∃ p : Seminorm ℂ X, Continuous p ∧ ∀ x, p x < 1 → x ∈ U := by
  obtain ⟨ι, _, P, hP⟩ := h
  have hadd : IsTopologicalAddGroup X := hP.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ X := hP.continuousSMul
  obtain ⟨⟨s, ρ⟩, hρ, hsub⟩ := hP.hasBasis_zero_ball.mem_iff.1 hU
  have hρ : 0 < ρ := hρ
  obtain ⟨p0, hp0⟩ : ∃ p : Seminorm ℂ X, p = s.sup P := ⟨_, rfl⟩
  have hsub : p0.ball 0 ρ ⊆ U := by rw [hp0]; exact hsub
  have hsc : Continuous p0 := by
    rw [hp0]
    exact Seminorm.continuous (r := ρ) (hP.hasBasis_zero_ball.mem_of_mem (i := (s, ρ)) hρ)
  let c : NNReal := ⟨ρ⁻¹, (inv_pos.2 hρ).le⟩
  have hval : ∀ x, (c • p0) x = ρ⁻¹ * p0 x := by
    intro x
    rw [smul_apply, NNReal.smul_def]
    rfl
  refine ⟨c • p0, ?_, ?_⟩
  · have : (fun x => (c • p0) x) = fun x => ρ⁻¹ * p0 x := funext hval
    change Continuous (fun x => (c • p0) x)
    rw [this]
    exact continuous_const.mul hsc
  · intro x hx
    apply hsub
    rw [Seminorm.mem_ball_zero]
    rw [hval, inv_mul_lt_iff₀ hρ] at hx
    simpa using hx

theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsLocallyConvexTopology E ‹TopologicalSpace E›)
    (hF : IsLocallyConvexTopology F ‹TopologicalSpace F›)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (hB : Continuous (fun p : E × F => B p.1 p.2)) :
    ∃ (p : Seminorm ℂ E) (r : Seminorm ℂ F), Continuous p ∧ Continuous r ∧
      ∀ x y, ‖B x y‖ ≤ p x * r y := by
  have hmem : {z : E × F | ‖B z.1 z.2‖ < 1} ∈ 𝓝 ((0,0) : E × F) :=
    (isOpen_lt hB.norm continuous_const).mem_nhds (by simp)
  rw [nhds_prod_eq] at hmem
  obtain ⟨U,hU,V,hV,hUV⟩ := Filter.mem_prod_iff.mp hmem
  obtain ⟨p,hp,hU'⟩ := exists_seminorm_ball_subset hE hU
  obtain ⟨q,hq,hV'⟩ := exists_seminorm_ball_subset hF hV
  refine ⟨p,q,hp,hq,fun x y => ?_⟩
  refine homog_bound q (fun y => ‖B x y‖) (fun c y hc => ?_) (p x) (apply_nonneg p x) ?_ y
  · rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc.le]
  · intro y hy
    have h := homog_bound p (fun x => ‖B x y‖) (fun c a hc => by
      rw [map_smul,LinearMap.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hc.le]) 1 zero_le_one
        (fun a ha => le_of_lt (show ‖B a y‖ < 1 from
          hUV (mk_mem_prod (hU' a ha) (hV' y hy)))) x
    simpa using h

