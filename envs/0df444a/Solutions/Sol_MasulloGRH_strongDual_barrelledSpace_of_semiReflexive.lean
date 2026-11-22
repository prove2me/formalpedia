-- Prove2me | solution 1 for MasulloGRH.strongDual_barrelledSpace_of_semiReflexive
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T10:47:19.148311+00:00
-- url     : https://prove2.me/submissions/9592eeef-200c-45eb-9b8c-4a96c0a8ac47

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strongDual_isHLCS
import Theorems.Thm_MasulloGRH_bounded_iff_weakly_bounded

set_option autoImplicit false

open MasulloGRH Topology Filter Uniformity Pointwise ComplexConjugate


namespace BarAux

universe u

lemma lc_tvs {E : Type u} [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E]
    (h : IsLocallyConvexTopology E t) : IsTopologicalAddGroup E ∧ ContinuousSMul ℂ E := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact ⟨hp.topologicalAddGroup, hp.continuousSMul⟩

lemma frechet_baire {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : IsFrechet E) : BaireSpace E := by
  obtain ⟨hlc, ⟨hT2, hc⟩, hm⟩ := h
  obtain ⟨h1, h2⟩ := lc_tvs hlc
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace E := by
    refine ⟨fun {f} hf => ?_⟩
    apply hc f
    refine ⟨hf.1, fun U hU => ?_⟩
    have hs : {p : E × E | p.2 - p.1 ∈ U} ∈ 𝓤 E := by
      rw [uniformity_eq_comap_nhds_zero']
      exact ⟨U, hU, fun p hp => by simpa [sub_eq_add_neg] using hp⟩
    obtain ⟨A, hA, hAA⟩ := mem_prod_same_iff.1 (hf.2 hs)
    exact ⟨A, hA, fun x hx y hy => hAA (Set.mk_mem_prod hy hx)⟩
  infer_instance

/-- the topology of a single seminorm -/
noncomputable def sTop {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    TopologicalSpace E :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) (fun _ : PUnit.{u+1} => p)).topology

lemma sTop_ws {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    @WithSeminorms ℂ E PUnit.{u+1} _ _ _ (fun _ => p) (sTop p) := by
  letI := sTop p
  exact ⟨rfl⟩

lemma sTop_lc {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    IsLocallyConvexTopology E (sTop p) := ⟨PUnit, inferInstance, _, sTop_ws p⟩

lemma sTop_cont_into {E : Type u} [AddCommGroup E] [Module ℂ E] {F : Type*} [AddCommGroup F]
    [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] (f : F →ₗ[ℂ] E)
    (p : Seminorm ℂ E) (hf : Continuous (p.comp f)) : @Continuous F E _ (sTop p) f := by
  letI := sTop p
  exact WithSeminorms.continuous_of_continuous_comp (sTop_ws p) f (fun _ => hf)

lemma sTop_cont {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    @Continuous E ℝ (sTop p) _ p := by
  letI := sTop p
  exact WithSeminorms.continuous_seminorm (sTop_ws p) PUnit.unit

end BarAux

open BarAux in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (hr : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x) :
    BarrelledSpace ℂ (StrongDual ℂ E) := by
  obtain ⟨h1, h2⟩ := lc_tvs hE.1
  have hD := strongDual_isHLCS E hE
  obtain ⟨ι, _, q, hq⟩ := hD.1
  haveI : LocallyConvexSpace ℝ (StrongDual ℂ E) := hq.toLocallyConvexSpace
  have hbasis := ContinuousLinearMap.hasBasis_nhds_zero (𝕜₁ := ℂ) (σ := RingHom.id ℂ)
    (E := E) (F := ℂ)
  refine ⟨fun p hp => ?_⟩
  have hTc : IsClosed (p.closedBall 0 1) := by
    rw [p.closedBall_zero_eq]; exact hp.isClosed_preimage 1
  let B : Set E := {x | ∀ f ∈ p.closedBall 0 1, ‖f x‖ ≤ 1}
  have hB : Bornology.IsVonNBounded ℂ B := by
    rw [bounded_iff_weakly_bounded E hE]
    intro ℓ
    have hr0 : 0 < p ℓ + 1 := by positivity
    rw [isBounded_iff_forall_norm_le]
    refine ⟨p ℓ + 1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hmem : ((p ℓ + 1 : ℝ) : ℂ)⁻¹ • ℓ ∈ p.closedBall 0 1 := by
      rw [Seminorm.mem_closedBall, sub_zero, map_smul_eq_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hr0.le]
      rw [inv_mul_le_iff₀ hr0]; linarith
    have := hx _ hmem
    rw [smul_apply, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hr0.le, inv_mul_le_iff₀ hr0] at this
    linarith
  have hN : {h : StrongDual ℂ E | ∀ x ∈ B, h x ∈ Metric.ball (0 : ℂ) 1} ∈
      𝓝 (0 : StrongDual ℂ E) :=
    hbasis.mem_of_mem (i := (B, Metric.ball 0 1)) ⟨hB, Metric.ball_mem_nhds 0 one_pos⟩
  have hT : p.closedBall 0 1 ∈ 𝓝 (0 : StrongDual ℂ E) := by
    refine Filter.mem_of_superset hN ?_
    intro h hh
    by_contra hT
    obtain ⟨φ, u, hφT, hφh⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      (Seminorm.convex_closedBall p 0 1) hTc hT
    obtain ⟨x0, hx0, -⟩ := hr φ
    have hu : 0 < u := by
      have := hφT 0 (by simp)
      simpa using this
    have hbd : ∀ t ∈ p.closedBall 0 1, ‖t x0‖ ≤ u := by
      intro t ht
      by_cases h0 : t x0 = 0
      · rw [h0, norm_zero]; exact hu.le
      have hn : (‖t x0‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
      let c : ℂ := conj (t x0) / ‖t x0‖
      have hc : ‖c‖ = 1 := by
        simp only [c, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm]
        exact div_self (norm_ne_zero_iff.2 h0)
      have hct : c • t ∈ p.closedBall 0 1 := by
        rw [Seminorm.mem_closedBall, sub_zero, map_smul_eq_mul, hc, one_mul]
        simpa using ht
      have hval : (c • t) x0 = (‖t x0‖ : ℂ) := by
        rw [smul_apply, smul_eq_mul]
        simp only [c]
        rw [div_mul_eq_mul_div, Complex.conj_mul']
        field_simp
      have := hφT _ hct
      rw [hx0, hval] at this
      have : ‖t x0‖ < u := by simpa using this
      exact this.le
    have hx1 : ((u : ℂ)⁻¹) • x0 ∈ B := by
      intro t ht
      rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu.le,
        inv_mul_le_iff₀ hu, mul_one]
      exact hbd t ht
    have e1 := hh _ hx1
    rw [Metric.mem_ball, dist_zero_right, map_smul, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hu.le, inv_mul_lt_iff₀ hu, mul_one] at e1
    rw [hx0] at hφh
    have := RCLike.re_le_norm (h x0)
    linarith
  exact Seminorm.continuous' hT
