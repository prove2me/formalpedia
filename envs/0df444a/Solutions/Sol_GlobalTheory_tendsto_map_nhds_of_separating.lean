-- Prove2me | solution 1 for GlobalTheory.tendsto_map_nhds_of_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:52.433909+00:00
-- url     : https://prove2.me/submissions/a59e9bc0-4c77-4e21-8995-dc3cd5cf10f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open Filter Topology Set Metric
open GlobalTheory
variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] {A : Type*} [AddCommGroup A]
  {ι : Type*} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
namespace GlobalTheory
theorem _root_.solution [CompleteSpace V] [ProperSpace W] {ex : W →+ A}
    (hex : Function.Surjective ex) {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → Y}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, ContinuousOn (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, ContinuousOn (fun z ↦ f i (G z)) (G ⁻¹' S)) :
    ∀ N ∈ 𝓝 (0 : W), ∀ᶠ z in 𝓝 (0 : V), G z ∈ ex '' N := by
  intro N hN
  have hN' : N ∩ ex ⁻¹' S ∈ 𝓝 (0 : W) := inter_mem hN (hSe.mem_nhds (by simpa using h0))
  obtain ⟨R, hR, hRN⟩ := nhds_basis_closedBall.mem_iff.1 hN'
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  let T : Set V := {z | ∃ w ∈ closedBall (0 : W) (2 * r), ex w = G z}
  have hKS : closedBall (0 : W) (2 * r) ⊆ ex ⁻¹' S := fun w hw ↦
    (hRN (closedBall_subset_closedBall (by linarith) hw)).2
  have hTS : T ⊆ G ⁻¹' S := by
    rintro z ⟨w, hw, h⟩
    rw [mem_preimage, ← h]
    exact hKS hw
  have hcl : closure T ∩ G ⁻¹' S ⊆ T := by
    rintro z ⟨hz, hzS⟩
    obtain ⟨x, hx, hxz⟩ := mem_closure_iff_seq_limit.1 hz
    choose w hw hwx using hx
    obtain ⟨w₀, hw₀, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : W) (2 * r)).tendsto_subseq hw
    refine ⟨w₀, hw₀, hsep _ (hKS hw₀) _ hzS fun i ↦ ?_⟩
    have h1 := (((hfe i).continuousAt (hSe.mem_nhds (hKS hw₀))).tendsto).comp hlim
    have h2 := (((hfG i).continuousAt (hSG.mem_nhds hzS)).tendsto).comp
      (hxz.comp hφ.tendsto_atTop)
    refine tendsto_nhds_unique h1 (h2.congr fun n ↦ ?_)
    simp [hwx]
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq W
  let B : ℕ → Set V := fun j ↦ {z | ∃ w ∈ ball (c j) r, ex w = G z}
  have hB : ⋃ j, closure (B j) = univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    obtain ⟨w, hw⟩ := hex (G z)
    obtain ⟨j, hj⟩ := hc.exists_dist_lt w hr0
    exact mem_iUnion.2 ⟨j, subset_closure ⟨w, hj, hw⟩⟩
  obtain ⟨j, y, hy⟩ := nonempty_interior_of_iUnion_of_closed (fun _ ↦ isClosed_closure) hB
  obtain ⟨z₀, hz₀i, w₀, hw₀, hz₀⟩ :=
    mem_closure_iff.1 (interior_subset hy) _ isOpen_interior hy
  have hBT : ∀ z ∈ B j, z - z₀ ∈ T := by
    rintro z ⟨w, hw, h⟩
    refine ⟨w - w₀, ?_, by simp [h, hz₀]⟩
    rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
    have := dist_triangle_right w w₀ (c j)
    rw [mem_ball] at hw hw₀
    linarith
  have h1 : ∀ᶠ z in 𝓝 (0 : V), z + z₀ ∈ closure (B j) := by
    have : Tendsto (fun z : V ↦ z + z₀) (𝓝 0) (𝓝 z₀) := by
      simpa using (continuous_add_const z₀).tendsto 0
    exact this (mem_interior_iff_mem_nhds.1 hz₀i)
  filter_upwards [h1, hSG.mem_nhds (show (0 : V) ∈ G ⁻¹' S by simpa using h0)] with z hz hzS
  have hzT : z ∈ closure T := by
    simpa using map_mem_closure (continuous_sub_right z₀) hz hBT
  obtain ⟨w, hw, h⟩ := hcl ⟨hzT, hzS⟩
  exact ⟨w, (hRN (closedBall_subset_closedBall (by linarith) hw)).1, h⟩
end GlobalTheory
