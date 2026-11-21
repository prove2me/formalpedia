-- Prove2me | solution 2 for MasulloGRH.limit_subspace_hull_condition
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T00:03:58.730454+00:00
-- url     : https://prove2.me/submissions/e6845c0e-7b59-4ef4-ac73-cb78e8d3eac3

import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages

open MasulloGRH Set Topology Filter
open scoped Pointwise

private theorem balanced_real_hull {E : Type*} [AddCommGroup E] [Module ℂ E]
    {S : Set E} (hb : Balanced ℂ S) : Balanced ℂ (convexHull ℝ S) := by
  refine balanced_iff_smul_mem.mpr ?_
  intro a ha x hx
  apply convexHull_min (t := {y | a • y ∈ convexHull ℝ S}) ?_ ?_ hx
  · intro y hy
    exact subset_convexHull ℝ S (hb.smul_mem ha hy)
  · intro v hv w hw c d hc hd hcd
    change a • (c • v + d • w) ∈ convexHull ℝ S
    rw [smul_add, smul_comm a c, smul_comm a d]
    exact convex_convexHull ℝ S hv hw hc hd hcd

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlim : (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) :
    ∀ W : ∀ k, Set (X k), (∀ k, W k ∈ nhds (0 : X k)) →
      ∃ O : ∀ k, Set (X k), (∀ k, O k ∈ nhds (0 : X k)) ∧
        ∀ v ∈ V, v ∈ convexHull ℝ (balancedHull ℂ (⋃ k, Subtype.val '' O k)) →
          v ∈ convexHull ℝ (balancedHull ℂ (⋃ k, (Subtype.val '' W k) ∩ (V : Set E)))  := by
  classical
  intro W hW
  obtain ⟨⟨⟨ι, hi, q, hq⟩, _⟩, _⟩ := bounded_in_strict_frechet_stages E X hmono hexh
    (fun n => (hX n).1) htop
  let _ := hq.topologicalAddGroup
  let _ := hq.continuousSMul
  let S : Set E := ⋃ n, (Subtype.val '' W n) ∩ (V : Set E)
  let D := convexHull ℝ (balancedHull ℂ S)
  let C : Set V := V.subtype ⁻¹' D
  have hbD : Balanced ℂ D := balanced_real_hull (balancedHull.balanced S)
  have hcD : Convex ℝ D := convex_convexHull .. 
  have hbC : Balanced ℂ C := balanced_iff_smul_mem.mpr
    (fun _ ha _ hx => hbD.smul_mem ha hx)
  have hcC : Convex ℝ C := hcD.linear_preimage (V.subtype.restrictScalars ℝ)
  let J (n : ℕ) : (V ⊓ X n : Submodule ℂ E) →ₗ[ℂ] V := Submodule.inclusion inf_le_left
  let K (n : ℕ) : (V ⊓ X n : Submodule ℂ E) →ₗ[ℂ] X n := Submodule.inclusion inf_le_right
  have hpre (n : ℕ) : (J n) ⁻¹' C ∈ nhds 0 := by
    have hcont : Continuous (K n) := continuous_subtype_val.subtype_mk _
    have hK : (K n) ⁻¹' W n ∈ nhds 0 := hcont.tendsto' 0 0 (map_zero _) (hW n)
    apply mem_of_superset hK
    intro z hz
    apply subset_convexHull ℝ _ (subset_balancedHull ℂ ?_)
    exact mem_iUnion.mpr ⟨n, ⟨K n z, hz, rfl⟩, z.prop.1⟩
  have haC : Absorbent ℝ C := by
    apply absorbent_iff_inv_smul.mpr
    intro x
    obtain ⟨n, hn⟩ := hexh x.val
    let z : (V ⊓ X n : Submodule ℂ E) := ⟨x.val, x.prop, hn⟩
    let _ : ContinuousSMul ℝ (V ⊓ X n : Submodule ℂ E) := ⟨by
      change Continuous (fun a : ℝ × (V ⊓ X n : Submodule ℂ E) => (a.1 : ℂ) • a.2)
      exact (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd⟩
    have h := (absorbent_iff_inv_smul.mp (absorbent_nhds_zero (𝕜 := ℝ) (hpre n))) z
    exact h
  let p := gaugeSeminorm hbC hcC haC
  have hp : Continuous p := by
    let family : SeminormFamily ℂ V ι := fun _ => p
    let t := family.moduleFilterBasis.topology
    have ht : WithSeminorms (topology := t) family := ⟨rfl⟩
    have hstep (n : ℕ) : Continuous (p.comp (J n)) := by
      apply Seminorm.continuous' (r := 1)
      rw [Seminorm.closedBall_zero_eq]
      exact mem_of_superset (hpre n) fun z hz => gauge_le_one_of_mem hz
    have hle : (instTopologicalSpaceSubtype : TopologicalSpace V) ≤ t := by
      rw [hlim]
      exact sInf_le ⟨⟨ι, hi, family, ht⟩, fun n =>
        WithSeminorms.continuous_of_continuous_comp ht (J n) (fun _ => hstep n)⟩
    have hpt : @Continuous V ℝ t _ p := ht.continuous_seminorm (Classical.choice hi)
    exact continuous_iff_le_induced.mpr (hle.trans (continuous_iff_le_induced.mp hpt))
  have hC : C ∈ nhds 0 := by
    refine mem_of_superset (p.ball_mem_nhds hp (r := 1) zero_lt_one) ?_
    rw [Seminorm.ball_zero_eq]
    exact setOfPred_gauge_lt_one_subset_self hcC haC.zero_mem haC
  rw [nhds_subtype] at hC
  obtain ⟨G, hG, hGC⟩ := mem_comap.mp hC
  obtain ⟨⟨s, r⟩, hr, hsub⟩ := hq.hasBasis_zero_ball.mem_iff.mp hG
  let H := (s.sup q).ball 0 r
  have hH : H ∈ nhds 0 := hq.hasBasis_zero_ball.mem_of_mem (i := (s,r)) hr
  refine ⟨fun n => Subtype.val ⁻¹' H, fun n => continuous_subtype_val.tendsto' 0 0 rfl hH, ?_⟩
  intro v hv hmem
  have hin : (⋃ k, (Subtype.val : X k → E) '' (Subtype.val ⁻¹' H)) ⊆ H := by
    intro x hx
    obtain ⟨k, a, ha, rfl⟩ := mem_iUnion.mp hx
    exact ha
  have hfin := convexHull_min ((s.sup q).balanced_ball_zero r |>.balancedHull_subset_of_subset hin)
    ((s.sup q).convex_ball 0 r)
  exact hGC (a := (⟨v, hv⟩ : V)) (hsub (hfin hmem))
