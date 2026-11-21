-- Prove2me | solution 1 for MasulloGRH.strongDual_frechet_fundamental_bounded_seq
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:31:58.264848+00:00
-- url     : https://prove2.me/submissions/a20e5007-dd6c-405f-ad21-a6d4a36b4c03

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Topology Filter Set

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    ∃ B : ℕ → Set (StrongDual ℂ E), (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set (StrongDual ℂ E), Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n := by
  obtain ⟨⟨ι, _, p, hp⟩, ⟨hT2, hC⟩, hM⟩ := hE
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  letI U : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have := isUniformAddGroup_of_addCommGroup (G := E)
  have hcg : (uniformity E).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]; infer_instance
  have hcomp : CompleteSpace E := by
    refine ⟨fun {f} hf => hC f ⟨hf.1, fun V hV => ?_⟩⟩
    have hV' : {q : E × E | q.2 - q.1 ∈ V} ∈ uniformity E := by
      rw [uniformity_eq_comap_nhds_zero]; exact ⟨V, hV, fun q hq => hq⟩
    obtain ⟨A, hA, hAA⟩ := Filter.mem_prod_same_iff.mp (hf.2 hV')
    exact ⟨A, hA, fun x hx y hy => hAA (mk_mem_prod hy hx)⟩
  letI : PseudoMetricSpace E := UniformSpace.pseudoMetricSpace E
  have : BaireSpace E := inferInstance
  have hBar : BarrelledSpace ℂ E := inferInstance
  obtain ⟨V, hV⟩ := (𝓝 (0 : E)).exists_antitone_basis
  refine ⟨fun n => {f : StrongDual ℂ E | ∀ x ∈ V n, ‖f x‖ ≤ 1}, fun n => ?_, fun S hS => ?_⟩
  · rw [ContinuousLinearMap.isVonNBounded_iff]
    intro s hs
    obtain ⟨a, ha⟩ := ((hs (hV.mem n)).and (Bornology.eventually_ne_cobounded (0 : ℂ))).exists
    refine (NormedSpace.isVonNBounded_closedBall ℂ ℂ ‖a‖).subset ?_
    rintro _ ⟨f, hf, x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := ha.1 hx
    simp only [Metric.mem_closedBall, dist_zero_right, map_smul, smul_eq_mul, norm_mul]
    simpa using mul_le_mul_of_nonneg_left (hf v hv) (norm_nonneg a)
  · let q : S → Seminorm ℂ E := fun f => (normSeminorm ℂ ℂ).comp (f : StrongDual ℂ E).toLinearMap
    have hpt : ∀ x : E, BddAbove (range fun f : S => q f x) := by
      intro x
      have hb := ContinuousLinearMap.isVonNBounded_image2_apply (R := ℂ) hS
        (Bornology.isVonNBounded_singleton x)
      obtain ⟨r, hr⟩ := (NormedSpace.isVonNBounded_iff' (𝕜 := ℂ) (E := ℂ)).mp hb
      refine ⟨r, ?_⟩
      rintro _ ⟨f, rfl⟩
      exact hr _ ⟨f, f.2, x, rfl, rfl⟩
    have hbdd : BddAbove (range q) := Seminorm.bddAbove_range_iff.mpr hpt
    have hcont : Continuous (⨆ f, q f) :=
      Seminorm.continuous_iSup q (fun f => continuous_norm.comp (f : StrongDual ℂ E).continuous) hbdd
    have hnhds : {x : E | ⨆ f, q f x < 1} ∈ 𝓝 (0 : E) := by
      have h0 : (⨆ f, ⇑(q f)) 0 < 1 := by
        rw [iSup_apply]; simp only [map_zero]
        rcases isEmpty_or_nonempty S with h | h
        · rw [Real.iSup_of_isEmpty]; norm_num
        · rw [ciSup_const]; norm_num
      have := hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds h0)
      convert this using 2
      ext x; simp [iSup_apply]
    obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.mp hnhds
    refine ⟨n, fun f hf x hx => ?_⟩
    have h1 := hn hx
    simp only [mem_setOf_eq] at h1
    have h2 : q ⟨f, hf⟩ x ≤ ⨆ g, q g x := le_ciSup (hpt x) ⟨f, hf⟩
    have : q ⟨f, hf⟩ x = ‖f x‖ := rfl
    linarith
