-- Prove2me | solution 2 for MasulloGRH.frechet_regularBasis_continuousNorm
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:00:12.878996+00:00
-- url     : https://prove2.me/submissions/d5e2cc30-c27a-46ba-b220-b2793b0d8079

import Definitions.Def_MasulloGRH_SchauderBases

open Filter Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_frechet_regularBasis_continuousNorm

open Set
open scoped Uniformity

section complete

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- For a topological vector space, the Cauchy filters of the additive uniform structure are the
filters that are Cauchy in the sense of `IsCauchyFilter`. -/
theorem cauchy_iff_isCauchyFilter (f : Filter E) :
    @Cauchy E (IsTopologicalAddGroup.rightUniformSpace E) f ↔ MasulloGRH.IsCauchyFilter f := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  rw [cauchy_iff]
  refine and_congr Iff.rfl ⟨fun h U hU => ?_, fun h s hs => ?_⟩
  · have h2 : (fun p : E × E => p.2 + -p.1) ⁻¹' U ∈ 𝓤 E := by
      rw [uniformity_eq_comap_nhds_zero' E]
      exact Filter.preimage_mem_comap hU
    obtain ⟨A, hA, hAU⟩ := h _ h2
    refine ⟨A, hA, fun x hx y hy => ?_⟩
    have h3 : x + -y ∈ U := hAU (Set.mk_mem_prod hy hx)
    rwa [← sub_eq_add_neg] at h3
  · rw [uniformity_eq_comap_nhds_zero' E] at hs
    obtain ⟨U, hU, hUs⟩ := Filter.mem_comap.mp hs
    obtain ⟨A, hA, hAU⟩ := h U hU
    refine ⟨A, hA, fun q hq => hUs ?_⟩
    have h3 : q.2 - q.1 ∈ U := hAU q.2 hq.2 q.1 hq.1
    rwa [sub_eq_add_neg] at h3

/-- Completeness in the sense of `IsCompleteTVS` gives completeness of the additive uniform
structure. -/
theorem completeSpace_of_isCompleteTVS [Module ℂ E] (h : MasulloGRH.IsCompleteTVS E) :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  exact ⟨fun {f} hf => h.2 f ((cauchy_iff_isCauchyFilter f).mp hf)⟩

end complete

/-- Every continuous seminorm on `ℂ^ℕ` (product topology) vanishes at some nonzero vector. -/
theorem exists_ne_zero_seminorm_apply_pi (q : Seminorm ℂ (ℕ → ℂ)) (hq : Continuous q) :
    ∃ v : ℕ → ℂ, v ≠ 0 ∧ q v = 0 := by
  have hmem : {v : ℕ → ℂ | q v < 1} ∈ 𝓝 (0 : ℕ → ℂ) := by
    have h0 : q (0 : ℕ → ℂ) = 0 := map_zero q
    have h : Iio (1 : ℝ) ∈ 𝓝 (q (0 : ℕ → ℂ)) := by
      rw [h0]
      exact Iio_mem_nhds zero_lt_one
    exact ContinuousAt.preimage_mem_nhds hq.continuousAt h
  rw [nhds_pi] at hmem
  obtain ⟨I, t, htmem, hsub⟩ := Filter.mem_pi'.mp hmem
  obtain ⟨j₀, -, hj₀⟩ := (Set.Ioi_infinite (I.card : ℕ)).exists_notMem_finset I
  set e : ℕ → ℂ := fun j => if j = j₀ then (1 : ℂ) else 0 with he
  refine ⟨e, ?_, ?_⟩
  · intro h
    have := congrFun h j₀
    simp [e] at this
  · by_contra hv
    have hpos : 0 < q e := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hv)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / q e)
    have hjne : ∀ j ∈ I, j ≠ j₀ := fun j hj h => hj₀ (by rw [h] at hj; exact hj)
    have hmem' : (n : ℂ) • e ∈ Set.pi (I : Set ℕ) t := by
      intro j hj
      have hz : ((n : ℂ) • e) j = (0 : ℂ) := by
        simp [e, hjne j hj]
      rw [hz]
      exact mem_of_mem_nhds (htmem j)
    have h1 : q ((n : ℂ) • e) < 1 := hsub hmem'
    rw [map_smul_eq_mul, Complex.norm_natCast] at h1
    have hge : (1 : ℝ) < (n : ℝ) * q e := (div_lt_iff₀ hpos).mp hn
    linarith

open MasulloGRH in
/-- Part 1 in a Hausdorff barrelled space whose topology is given by a family of seminorms. -/
theorem exists_continuous_norm {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [BarrelledSpace ℂ E]
    {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p)
    (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) (hreg : IsRegularBasis x) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ u : E, q u = 0 → u = 0 := by
  obtain ⟨U, hU, hxU⟩ := hreg
  obtain ⟨s, r, hr, hsU⟩ := (hp.mem_nhds_iff 0 U).mp hU
  set p0 : Seminorm ℂ E := s.sup p with hp0def
  have hp0 : Continuous p0 := by
    refine Seminorm.continuous (r := r) ?_
    exact (hp.mem_nhds_iff 0 _).mpr ⟨s, r, hr, subset_rfl⟩
  have hpos : ∀ n, r ≤ p0 (x n) := by
    intro n
    by_contra h
    exact hxU n (hsU (by rw [Seminorm.mem_ball, sub_zero]; exact lt_of_not_ge h))
  let T : ℕ → E →L[ℂ] E := fun n => (f n).smulRight (x n)
  have hT : ∀ n u, T n u = f n u • x n := fun n u => rfl
  let R : ℕ → Seminorm ℂ E := fun n => p0.comp (T n).toLinearMap
  have hR : ∀ n u, R n u = p0 (f n u • x n) := fun n u => rfl
  have hRc : ∀ n, Continuous (R n) := fun n => hp0.comp (T n).continuous
  have hterm : ∀ u, Tendsto (fun n => f n u • x n) atTop (𝓝 0) := by
    intro u
    have h := hx.expansion u
    have h1 : Tendsto (fun n => basicProjection x f (n + 1) u - basicProjection x f n u)
        atTop (𝓝 (u - u)) := (h.comp (tendsto_add_atTop_nat 1)).sub h
    rw [sub_self] at h1
    have h2 : Tendsto (fun n => f (n + 1) u • x (n + 1)) atTop (𝓝 0) := by
      refine h1.congr fun n => ?_
      simp only [basicProjection]
      rw [Finset.sum_range_succ _ (n + 1), add_sub_cancel_left]
    exact (tendsto_add_atTop_iff_nat 1).mp h2
  have hbdd : BddAbove (range R) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    have ht : Tendsto (fun n => R n u) atTop (𝓝 (p0 0)) := by
      simp only [hR]
      exact (hp0.tendsto 0).comp (hterm u)
    exact (Metric.isBounded_range_of_tendsto _ ht).bddAbove
  refine ⟨⨆ n, R n, ?_, ?_⟩
  · rw [Seminorm.coe_iSup_eq hbdd]
    exact Seminorm.continuous_iSup R hRc hbdd
  · intro u hu
    have hz : ∀ n, f n u = 0 := by
      intro n
      have hle : R n ≤ ⨆ m, R m := le_ciSup hbdd n
      have hzero : R n u = 0 := le_antisymm ((hle u).trans_eq hu) (apply_nonneg _ _)
      rw [hR, map_smul_eq_mul, mul_eq_zero] at hzero
      rcases hzero with h0 | h0
      · exact norm_eq_zero.mp h0
      · exact absurd h0 (ne_of_gt (lt_of_lt_of_le hr (hpos n)))
    have hs := hx.expansion u
    have hP : ∀ k, basicProjection x f k u = 0 := by
      intro k
      simp [basicProjection, hz]
    simp only [hP] at hs
    exact tendsto_nhds_unique hs tendsto_const_nhds

end Sol_MasulloGRH_frechet_regularBasis_continuousNorm

open MasulloGRH Sol_MasulloGRH_frechet_regularBasis_continuousNorm
open scoped Uniformity

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hF : IsFrechet E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f)
    (hreg : IsRegularBasis x) :
    (∃ q : Seminorm ℂ E, Continuous q ∧ ∀ u : E, q u = 0 → u = 0) ∧
      ¬ ∃ S : Submodule ℂ E, IsClosed (S : Set E) ∧ S.ClosedComplemented ∧
        Nonempty (S ≃L[ℂ] (ℕ → ℂ)) := by
  obtain ⟨⟨ι, hι, p, hp⟩, hcomp, hmet⟩ := hF
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : T2Space E := hcomp.1
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := completeSpace_of_isCompleteTVS hcomp
  have : FirstCountableTopology E := inferInstance
  have : IsCountablyGenerated (𝓤 E) := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace E := BaireSpace.of_completelyPseudoMetrizable
  have : BarrelledSpace ℂ E := inferInstance
  obtain ⟨q, hq, hnorm⟩ := exists_continuous_norm hp x f hx hreg
  refine ⟨⟨q, hq, hnorm⟩, ?_⟩
  rintro ⟨S, -, -, ⟨T⟩⟩
  have hq' : Continuous
      (q.comp (S.subtypeL.comp T.symm.toContinuousLinearMap).toLinearMap) :=
    hq.comp (S.subtypeL.continuous.comp T.symm.continuous)
  obtain ⟨v, hv0, hvq⟩ := exists_ne_zero_seminorm_apply_pi _ hq'
  refine hv0 ?_
  have hzero : ((T.symm v : S) : E) = 0 := hnorm _ hvq
  have hzero' : (T.symm v : S) = 0 := Submodule.coe_eq_zero.mp hzero
  calc v = T (T.symm v) := (T.apply_symm_apply v).symm
    _ = 0 := by rw [hzero', map_zero]
