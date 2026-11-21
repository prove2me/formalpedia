-- Prove2me | solution 1 for MasulloGRH.bounded_iff_weakly_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:20:31.618596+00:00
-- url     : https://prove2.me/submissions/32f083e3-72a1-42cb-ad45-06cc834f7edb

import Definitions.Def_MasulloGRH_LocallyConvex

open MasulloGRH

private theorem continuous_from_finer {X Y : Type*} [TopologicalSpace Y]
    {a b : TopologicalSpace X} (hab : a ≤ b) {f : X → Y}
    (hf : @Continuous X Y b _ f) : @Continuous X Y a _ f :=
  @Continuous.comp X X Y a b _ id f hf (continuous_id_of_le hab)

private theorem bound_from_dual {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (B : Set F) (h : ∀ f : StrongDual ℂ F, ∃ C : ℝ, ∀ x ∈ B, ‖f x‖ ≤ C) :
    ∃ r > (0 : ℝ), ∀ x ∈ B, ‖x‖ < r := by
  let g (x : B) := NormedSpace.inclusionInDoubleDual ℂ F x.val
  have hpoint (f : StrongDual ℂ F) : ∃ C : ℝ, ∀ x : B, ‖g x f‖ ≤ C := by
    obtain ⟨C, hC⟩ := h f
    exact ⟨C, fun x => hC x x.property⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  refine ⟨max C 0 + 1, by positivity, fun x hx => ?_⟩
  have hnorm : ‖x‖ ≤ C := by
    rw [← (NormedSpace.inclusionInDoubleDualLi ℂ).norm_map x]
    exact hC ⟨x, hx⟩
  linarith [le_max_left C 0]

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [t : TopologicalSpace E] (hE : IsHLCS E) (B : Set E) :
    Bornology.IsVonNBounded ℂ B ↔ ∀ ℓ : StrongDual ℂ E, Bornology.IsBounded (ℓ '' B) := by
  constructor
  · intro h ℓ
    exact (NormedSpace.isVonNBounded_iff ℂ).mp (h.image ℓ)
  intro h
  obtain ⟨ι, _, p, hp⟩ := hE.1
  haveI := hp.topologicalAddGroup
  have hbound (f : E →ₗ[ℂ] ℂ) (hf : Continuous f) : ∃ C : ℝ, ∀ x ∈ B, ‖f x‖ ≤ C := by
    let L : StrongDual ℂ E := ⟨f, hf⟩
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (h L)
    exact ⟨C, fun x hx => hC (L x) ⟨x, hx, rfl⟩⟩
  apply hp.isVonNBounded_iff_seminorm_bounded.mpr
  intro i
  have ht : t ≤ (p i).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace :=
    (p.withSeminorms_iff_topologicalSpace_eq_iInf.mp hp).le.trans (iInf_le _ i)
  letI : SeminormedAddCommGroup E := (p i).toSeminormedAddCommGroup
  letI : NormedSpace ℂ E := { ‹Module ℂ E› with
    norm_smul_le := fun a x => (map_smul_eq_mul (p i) a x).le }
  apply bound_from_dual B
  letI : TopologicalSpace E := (p i).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
  intro f
  exact hbound f.toLinearMap (continuous_from_finer ht f.continuous)
