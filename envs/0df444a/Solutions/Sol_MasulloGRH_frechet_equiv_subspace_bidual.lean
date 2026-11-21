-- Prove2me | solution 1 for MasulloGRH.frechet_equiv_subspace_bidual
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:13:58.49389+00:00
-- url     : https://prove2.me/submissions/f7980fc5-cdce-404e-900b-45fb42ff9d2a

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Set Filter Topology Bornology

universe u

namespace BidualEmbedding

/-- A Fréchet space is a Baire space. -/
theorem baireSpace_of_isFrechet {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : IsFrechet E) : BaireSpace E := by
  obtain ⟨⟨ι, _, p, hp⟩, ⟨_, hcomp⟩, hmet⟩ := h
  have hadd : IsTopologicalAddGroup E := hp.topologicalAddGroup
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : CompleteSpace E := by
    refine ⟨fun {f} hf => hcomp f ⟨hf.1, fun U hU => ?_⟩⟩
    have hmem : {p : E × E | p.2 - p.1 ∈ U} ∈ uniformity E := by
      rw [uniformity_eq_comap_nhds_zero E]
      exact preimage_mem_comap hU
    obtain ⟨t, ht, hts⟩ := mem_prod_same_iff.1 (hf.2 hmem)
    exact ⟨t, ht, fun x hx y hy => hts (mk_mem_prod hy hx)⟩
  infer_instance

/-- A continuous seminorm is bounded on a von Neumann bounded set. -/
theorem seminorm_bounded_on {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (q : Seminorm ℂ E) (hq : Continuous q) {B : Set E} (hB : IsVonNBounded ℂ B) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ B, q x ≤ M := by
  have hq1 : {x : E | q x < 1} ∈ 𝓝 (0 : E) :=
    (isOpen_lt hq continuous_const).mem_nhds (by simp)
  obtain ⟨ρ, hρ⟩ := absorbs_iff_norm.1 (hB hq1)
  refine ⟨max ρ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  have hnorm : ‖((max ρ 1 : ℝ) : ℂ)‖ = max ρ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_trans zero_le_one (le_max_right _ _))]
  obtain ⟨y, hy, rfl⟩ := hρ ((max ρ 1 : ℝ) : ℂ) (by rw [hnorm]; exact le_max_left _ _) hx
  have hy' : q y < 1 := hy
  change q (((max ρ 1 : ℝ) : ℂ) • y) ≤ max ρ 1
  rw [map_smul_eq_mul, hnorm]
  nlinarith [le_max_right ρ 1, apply_nonneg q y]

/-- **Banach–Steinhaus.**  In a barrelled space a strongly bounded set of functionals is
equicontinuous at `0`. -/
theorem equicontinuous_of_bounded {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    (S : Set (StrongDual ℂ E)) (hS : IsVonNBounded ℂ S) {δ : ℝ} (hδ : 0 < δ) :
    {x : E | ∀ f ∈ S, ‖f x‖ < δ} ∈ 𝓝 (0 : E) := by
  have H : ∀ x : E, IsVonNBounded ℂ (range fun i : S => (i : StrongDual ℂ E) x) := by
    intro x
    refine (ContinuousLinearMap.isVonNBounded_image2_apply hS
      (Bornology.isVonNBounded_singleton (𝕜 := ℂ) x)).subset ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨i.1, i.2, x, rfl, rfl⟩
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hue := PolynormableSpace.banach_steinhaus (𝕜₁ := ℂ) (𝕜₂ := ℂ)
    (𝓕 := fun i : S => (i : E →L[ℂ] ℂ)) H
  have heq := hue.equicontinuous 0 {p : ℂ × ℂ | dist p.1 p.2 < δ} (Metric.dist_mem_uniformity hδ)
  refine mem_of_superset heq fun x hx f hf => ?_
  have := hx ⟨f, hf⟩
  simpa [dist_eq_norm] using this

/-- **Hahn–Banach.**  A continuous seminorm is attained by a functional it dominates. -/
theorem exists_dual_eq_seminorm {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] (q : Seminorm ℂ E) (hq : Continuous q) (x : E) :
    ∃ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) ∧ ‖f x‖ = q x := by
  by_cases hx0 : q x = 0
  · exact ⟨0, fun y => by simp, by simp [hx0]⟩
  have hx : x ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  let f₀ : Module.Dual ℂ (Submodule.span ℂ ({x} : Set E)) :=
    ((q x : ℝ) : ℂ) • LinearEquiv.coord ℂ E x hx
  have hf₀ : ∀ s : Submodule.span ℂ ({x} : Set E), ‖f₀ s‖ ≤ q s := by
    intro s
    have hs : (LinearEquiv.coord ℂ E x hx s) • x = s := LinearEquiv.coord_apply_smul ℂ E x hx s
    have h1 : q (s : E) = ‖LinearEquiv.coord ℂ E x hx s‖ * q x := by
      rw [← hs, map_smul_eq_mul]
    have h2 : ‖f₀ s‖ = q x * ‖LinearEquiv.coord ℂ E x hx s‖ := by
      simp only [f₀, LinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (apply_nonneg q x)]
      rfl
    rw [h1, h2, mul_comm]
  obtain ⟨g, hg, hgq⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm _ f₀ hq hf₀
  refine ⟨g, hgq, ?_⟩
  have h3 := hg ⟨x, Submodule.mem_span_singleton_self x⟩
  have h4 : f₀ ⟨x, Submodule.mem_span_singleton_self x⟩ = ((q x : ℝ) : ℂ) := by
    change ((q x : ℝ) : ℂ) *
      (LinearEquiv.coord ℂ E x hx) ⟨x, Submodule.mem_span_singleton_self x⟩ = _
    rw [LinearEquiv.coord_self, mul_one]
  rw [h4] at h3
  have h5 : g x = ((q x : ℝ) : ℂ) := h3
  rw [h5, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x)]

end BidualEmbedding

open BidualEmbedding

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    ∃ V : Submodule ℂ (StrongDual ℂ (StrongDual ℂ E)), Nonempty (E ≃L[ℂ] V) := by
  have hBaire : BaireSpace E := baireSpace_of_isFrechet hE
  obtain ⟨⟨ι, _, p, hp⟩, ⟨hT2, -⟩, -⟩ := hE
  have hadd : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hp.continuousSMul
  have hpoly : PolynormableSpace ℂ E := hp.toPolynormableSpace
  -- the evaluation map into the strong bidual
  let J : E →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ E) :=
    { toFun := fun x =>
        { toFun := fun f => f x
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          cont := continuous_eval_const x }
      map_add' := fun x y => by ext f; simp
      map_smul' := fun c x => by ext f; simp }
  have hJapp : ∀ (x : E) (f : StrongDual ℂ E), J x f = f x := fun _ _ => rfl
  have hAG : IsTopologicalAddGroup (StrongDual ℂ (StrongDual ℂ E)) := inferInstance
  have hCA : ContinuousAdd (StrongDual ℂ (StrongDual ℂ E)) := hAG.toContinuousAdd
  -- `J` is injective: the dual separates points
  have hJinj : Function.Injective J := by
    refine (injective_iff_map_eq_zero J).2 fun x hx => ?_
    by_contra hne
    obtain ⟨⟨s, r⟩, hr, hxs⟩ : ∃ sr : Finset ι × ℝ, 0 < sr.2 ∧ x ∉ (sr.1.sup p).ball 0 sr.2 := by
      have hopen : ({x}ᶜ : Set E) ∈ 𝓝 (0 : E) :=
        isOpen_compl_singleton.mem_nhds (fun h => hne (mem_singleton_iff.1 h).symm)
      obtain ⟨sr, hsr, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.1 hopen
      exact ⟨sr, hsr, fun h => hsub h rfl⟩
    have hqc : Continuous ⇑(s.sup p : Seminorm ℂ E) :=
      Seminorm.continuous (r := r) (hp.hasBasis_zero_ball.mem_of_mem (i := (s, r)) hr)
    obtain ⟨f, -, hfx⟩ := exists_dual_eq_seminorm (s.sup p) hqc x
    have h0 : f x = 0 := by rw [← hJapp, hx]; rfl
    rw [h0, norm_zero] at hfx
    apply hxs
    rw [Seminorm.mem_ball_zero, ← hfx]
    exact hr
  -- `J` is continuous: bounded sets of the strong dual are equicontinuous
  have hJcont : Continuous J := by
    refine continuous_of_continuousAt_zero J.toAddMonoidHom ?_
    intro N hN
    have hN' : N ∈ 𝓝 (0 : StrongDual ℂ (StrongDual ℂ E)) := by simpa using hN
    obtain ⟨⟨S, W⟩, ⟨hS, hW⟩, hsub⟩ := ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.1 hN'
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hW
    refine mem_map.2 (mem_of_superset (equicontinuous_of_bounded S hS hδ) fun x hx => ?_)
    change J x ∈ N
    refine hsub fun f hf => hball ?_
    rw [mem_ball_zero_iff]
    exact hx f hf
  -- `J` is open onto its range: polars of seminorm balls are strongly bounded
  have hJopen : ∀ U ∈ 𝓝 (0 : E), ∃ N ∈ 𝓝 (0 : StrongDual ℂ (StrongDual ℂ E)),
      ∀ x, J x ∈ N → x ∈ U := by
    intro U hU
    obtain ⟨⟨s, r⟩, hr, hsubU⟩ := hp.hasBasis_zero_ball.mem_iff.1 hU
    have hr : 0 < r := hr
    have hqc : Continuous ⇑(s.sup p : Seminorm ℂ E) :=
      Seminorm.continuous (r := r) (hp.hasBasis_zero_ball.mem_of_mem (i := (s, r)) hr)
    let S : Set (StrongDual ℂ E) := {f | ∀ y, ‖f y‖ ≤ (s.sup p) y}
    have hS : IsVonNBounded ℂ S := by
      rw [ContinuousLinearMap.isVonNBounded_iff]
      intro B hB
      obtain ⟨M, -, hM⟩ := seminorm_bounded_on (s.sup p) hqc hB
      rw [NormedSpace.isVonNBounded_iff]
      refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := M)).subset ?_
      rintro _ ⟨f, hf, y, hy, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact (hf y).trans (hM y hy)
    refine ⟨{φ | ∀ f ∈ S, φ f ∈ Metric.ball (0 : ℂ) r},
      ContinuousLinearMap.hasBasis_nhds_zero.mem_of_mem
        (i := (S, Metric.ball (0 : ℂ) r)) ⟨hS, Metric.ball_mem_nhds 0 hr⟩, fun x hx => ?_⟩
    obtain ⟨f, hfS, hfx⟩ := exists_dual_eq_seminorm (s.sup p) hqc x
    have h1 := hx f hfS
    rw [hJapp, mem_ball_zero_iff, hfx] at h1
    exact hsubU (by rw [Seminorm.mem_ball_zero]; exact h1)
  -- assemble the continuous linear equivalence onto the range
  let e : E ≃ₗ[ℂ] LinearMap.range J := LinearEquiv.ofInjective J hJinj
  have he : ∀ x, ((e x : LinearMap.range J) : StrongDual ℂ (StrongDual ℂ E)) = J x :=
    fun _ => rfl
  refine ⟨LinearMap.range J, ⟨{ e with
    continuous_toFun := Continuous.subtype_mk hJcont _
    continuous_invFun := ?_ }⟩⟩
  refine continuous_iff_continuousAt.2 fun v => ?_
  intro U hU
  have hU' : {x : E | e.symm v + x ∈ U} ∈ 𝓝 (0 : E) := by
    have hc : ContinuousAt (fun x : E => e.symm v + x) 0 :=
      (continuous_const.add continuous_id).continuousAt
    apply hc.preimage_mem_nhds
    simpa using hU
  obtain ⟨N, hN, hNU⟩ := hJopen _ hU'
  have hpre : {w : LinearMap.range J |
      (w : StrongDual ℂ (StrongDual ℂ E)) + -(v : StrongDual ℂ (StrongDual ℂ E)) ∈ N} ∈ 𝓝 v := by
    have hc : ContinuousAt (fun w : LinearMap.range J =>
        (w : StrongDual ℂ (StrongDual ℂ E)) + -(v : StrongDual ℂ (StrongDual ℂ E))) v :=
      (continuous_subtype_val.add continuous_const).continuousAt
    apply hc.preimage_mem_nhds
    have hz : (v : StrongDual ℂ (StrongDual ℂ E)) + -(v : StrongDual ℂ (StrongDual ℂ E)) = 0 :=
      ContinuousLinearMap.ext fun f => by simp
    rw [hz]
    exact hN
  refine mem_map.2 (mem_of_superset hpre fun w hw => ?_)
  change e.symm w ∈ U
  have h1 : J (e.symm w - e.symm v) =
      (w : StrongDual ℂ (StrongDual ℂ E)) + -(v : StrongDual ℂ (StrongDual ℂ E)) := by
    rw [map_sub, ← he, ← he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      sub_eq_add_neg]
  have h2 : e.symm v + (e.symm w - e.symm v) ∈ U := hNU _ (by rw [h1]; exact hw)
  have h3 : e.symm v + (e.symm w - e.symm v) = e.symm w := by abel
  rw [h3] at h2
  exact h2
