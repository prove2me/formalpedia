-- Prove2me | solution 1 for MasulloGRH.limit_subspace_hull_condition
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:02:55.476848+00:00
-- url     : https://prove2.me/submissions/551a2f0e-c407-478d-acd0-b5a3ac0cc01d

import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
open Set Filter Topology MasulloGRH

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
          v ∈ convexHull ℝ (balancedHull ℂ (⋃ k, (Subtype.val '' W k) ∩ (V : Set E))) := by
  classical
  intro W hW
  obtain ⟨hE,_⟩ := strictLF_hlcs_and_closed_steps E X hmono hexh (fun n => (hX n).1) htop
  obtain ⟨ι,hι,p,hp⟩ := hE.1
  have hadd := hp.topologicalAddGroup
  have hsm := hp.continuousSMul
  let S : Set E := ⋃ k, (Subtype.val '' W k) ∩ (V : Set E)
  let D := convexHull ℝ (balancedHull ℂ S)
  have hconv : Convex ℝ D := convex_convexHull .. 
  have hbal : Balanced ℂ D := by
    rw [balanced_iff_smul_mem]
    intro a ha
    exact convexHull_min (fun x hx => subset_convexHull ℝ _ ((balancedHull.balanced S).smul_mem ha hx))
      (hconv.linear_preimage (DistribSMul.toLinearMap ℝ E a))
  let A : Set V := V.subtype ⁻¹' D
  have hac : Convex ℝ A := hconv.linear_preimage (V.subtype.restrictScalars ℝ)
  have hab : Balanced ℂ A := by
    apply balanced_iff_smul_mem.mpr
    intro a ha x hx
    exact hbal.smul_mem ha hx
  let Y (n : ℕ) := V ⊓ X n
  let i (n : ℕ) : Y n →ₗ[ℂ] V := Submodule.inclusion inf_le_left
  have hAn (n : ℕ) : i n ⁻¹' A ∈ 𝓝 0 := by
    let j : Y n →ₗ[ℂ] X n := Submodule.inclusion inf_le_right
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    have hw : j ⁻¹' W n ∈ 𝓝 0 := (hj.tendsto' 0 0 (map_zero j)) (hW n)
    apply mem_of_superset hw
    intro x hx
    apply subset_convexHull
    apply subset_balancedHull
    exact mem_iUnion.mpr ⟨n,⟨⟨j x,hx,rfl⟩,x.property.1⟩⟩
  have ha : Absorbent ℝ A := by
    apply absorbent_iff_eventually_nhdsNE_zero.mpr
    intro x
    obtain ⟨n,hn⟩ := hexh (x:E)
    let y : Y n := ⟨x,x.property,hn⟩
    have : ContinuousSMul ℝ (Y n) := IsScalarTower.continuousSMul ℂ
    have H : Absorbent ℝ (i n ⁻¹' A) := absorbent_nhds_zero (hAn n)
    exact H.eventually_nhdsNE_zero y
  let g := gaugeSeminorm hab hac ha
  have hg : Continuous g := by
    let q : SeminormFamily ℂ V (ULift Unit) := fun _ => g
    let t := q.moduleFilterBasis.topology
    have hq : @WithSeminorms ℂ V _ _ _ _ q t := ⟨rfl⟩
    have hcomp (n : ℕ) : Continuous (g.comp (i n)) := by
      apply Seminorm.continuous' (r:=1)
      apply mem_of_superset (hAn n)
      intro x hx
      exact (Seminorm.mem_closedBall_zero _).mpr (gauge_le_one_of_mem hx)
    have hle : (instTopologicalSpaceSubtype : TopologicalSpace V) ≤ t := by
      apply hlim.le.trans
      apply sInf_le
      refine ⟨⟨ULift Unit,inferInstance,q,hq⟩,?_⟩
      intro n
      let : TopologicalSpace V := t
      exact (hq.continuous_iff_continuous_comp (i n)).mpr (fun _ => hcomp n)
    have hid : @Continuous V V instTopologicalSpaceSubtype t id := continuous_id_iff_le.mpr hle
    have hgT : @Continuous V ℝ t _ g := hq.continuous_seminorm (ULift.up ())
    exact @Continuous.comp V V ℝ instTopologicalSpaceSubtype t _ id g hgT hid
  have hA : A ∈ 𝓝 0 := by
    apply mem_of_superset ((Seminorm.continuous_iff (p:=g) zero_lt_one).mp hg)
    intro x hx
    exact setOfPred_gauge_lt_one_subset_self hac ha.zero_mem ha ((g.mem_ball_zero).mp hx)
  rw [nhds_subtype] at hA
  obtain ⟨G,hG,hGA⟩ := Filter.mem_comap.mp hA
  obtain ⟨s,r,hr,hball⟩ := (hp.mem_nhds_iff 0 G).mp hG
  let d := s.sup p
  let O (k : ℕ) := (X k).subtype ⁻¹' d.ball 0 r
  refine ⟨O,fun k => ?_,?_⟩
  · apply (continuous_subtype_val.tendsto' (0:X k) (0:E) rfl)
    exact hp.hasBasis_zero_ball.mem_of_mem (i:=(s,r)) hr
  · intro v hv hvin
    have hU : (⋃ k, Subtype.val '' O k) ⊆ d.ball 0 r := by
      rintro _ hx
      obtain ⟨k,y,hy,rfl⟩ := mem_iUnion.mp hx
      exact hy
    have h' := convexHull_min ((d.balanced_ball_zero r).balancedHull_subset_of_subset hU)
      (d.convex_ball 0 r) hvin
    exact hGA (a:=⟨v,hv⟩) (hball h')
