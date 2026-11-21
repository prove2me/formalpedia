-- Prove2me | solution 1 for MasulloGRH.nuclear_quotient
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T23:02:40.146907+00:00
-- url     : https://prove2.me/submissions/fb3d7987-953b-47cd-b662-7ddd8c41d230

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_nuclear_dual_domination
import Theorems.Thm_MasulloGRH_nuclear_of_dual_domination

set_option autoImplicit false

open MasulloGRH
open TensorProduct Topology
open scoped ComplexOrder

universe u

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsNuclear E) (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) :
    IsNuclear (E ⧸ V) := by
  obtain ⟨⟨ι, _, pE, hpE⟩, hT2⟩ := hE.1
  have := hpE.topologicalAddGroup
  have := hpE.continuousSMul
  have : LocallyConvexSpace ℝ E := hpE.toLocallyConvexSpace
  have : IsClosed (V : Set E) := hV
  have hopen : IsOpenMap V.mkQ := V.isOpenQuotientMap_mkQ.isOpenMap
  have : LocallyConvexSpace ℝ (E ⧸ V) := by
    rw [locallyConvexSpace_iff_exists_convex_subset_zero]
    intro U hU
    have h1 : V.mkQ ⁻¹' U ∈ 𝓝 (0 : E) :=
      (V.continuous_mkQ.tendsto' 0 0 (map_zero _)) hU
    obtain ⟨S, hS, hSc, hSU⟩ :=
      (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).1 inferInstance _ h1
    refine ⟨V.mkQ '' S, ?_, hSc.linear_image (V.mkQ.restrictScalars ℝ), ?_⟩
    · simpa using hopen.image_mem_nhds hS
    · rintro _ ⟨x, hx, rfl⟩; exact hSU hx
  have : ContinuousSMul ℝ (E ⧸ V) := IsScalarTower.continuousSMul (M := ℝ) (α := E ⧸ V) ℂ
  have hRC : ∀ {X : Type u} [AddCommGroup X] [Module ℂ X] {s : Set X}, Convex ℝ s → Convex ℂ s :=
    fun h => convex_of_nonneg_surjective_algebraMap _
      (fun z (hz : 0 ≤ z) => by
        obtain ⟨x, hx, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp hz
        exact ⟨x, hx, rfl⟩) h
  have : LocallyConvexSpace ℂ (E ⧸ V) := by
    rw [locallyConvexSpace_iff_exists_convex_subset_zero]
    intro U hU
    obtain ⟨S, hS, hSc, hSU⟩ :=
      (locallyConvexSpace_iff_exists_convex_subset_zero ℝ (E ⧸ V)).1 inferInstance U hU
    exact ⟨S, hS, hRC hSc, hSU⟩
  have hW : WithSeminorms (gaugeSeminormFamily ℂ (E ⧸ V)) := with_gaugeSeminormFamily
  have hHLCS : IsHLCS (E ⧸ V) := ⟨⟨_, inferInstance, _, hW⟩, inferInstance⟩
  refine nuclear_of_dual_domination (E ⧸ V) hHLCS ?_
  intro q hq
  obtain ⟨p, y, c, hp, hc0, hcs, hy, hdom⟩ :=
    nuclear_dual_domination E hE (q.comp V.mkQ) (hq.comp V.continuous_mkQ)
  -- the image of the open unit `p`-ball is an absolutely convex open set
  let B : Set (E ⧸ V) := V.mkQ '' p.ball 0 1
  have hB0 : (0 : E ⧸ V) ∈ B := ⟨0, by simp, by simp⟩
  have hBo : IsOpen B := hopen _ (by
    rw [Seminorm.ball_zero_eq]; exact isOpen_lt hp continuous_const)
  have hBb : Balanced ℂ B := by
    intro a ha
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, (p.balanced_ball_zero 1) a ha ⟨x, hx, rfl⟩, by simp⟩
  have hBc : Convex ℝ B :=
    (p.convex_ball 0 1).linear_image (V.mkQ.restrictScalars ℝ)
  let S : AbsConvexOpenSets ℂ (E ⧸ V) := ⟨B, hB0, hBo, hBb, hRC hBc⟩
  let pt : Seminorm ℂ (E ⧸ V) := gaugeSeminormFamily ℂ (E ⧸ V) S
  have hball : pt.ball 0 1 = B := gaugeSeminormFamily_ball S
  refine ⟨pt + pt, fun n => V.mkQ (y n), c, ?_, hc0, hcs, fun n => hy n, ?_⟩
  · exact (hW.continuous_seminorm S).add (hW.continuous_seminorm S)
  intro f hf ξ hξ
  have hlt : pt ξ < 1 := by
    have : pt ξ + pt ξ ≤ 1 := hξ
    have := apply_nonneg pt ξ
    linarith
  have hmem : ξ ∈ B := by
    rw [← hball, Seminorm.mem_ball_zero]; exact hlt
  obtain ⟨x, hx, rfl⟩ := hmem
  have hx' : p x ≤ 1 := le_of_lt (by simpa [Seminorm.mem_ball_zero] using hx)
  have := hdom (f.comp V.mkQL) (fun z => hf (V.mkQ z)) x hx'
  simpa using this
