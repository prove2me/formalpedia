-- Prove2me | solution 2 for MasulloGRH.frechet_equiv_subspace_bidual
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:14:52.49619+00:00
-- url     : https://prove2.me/submissions/1bfa0467-4cec-42a0-af66-c9a165479bd1

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology Filter Set

noncomputable section

private theorem seminorm_norming {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) (x : E) :
    ∃ f : E →ₗ[ℂ] ℂ, (∀ y, ‖f y‖ ≤ p y) ∧ ‖f x‖ = p x := by
  let _ : SeminormedAddCommGroup E := p.toSeminormedAddCommGroup
  let _ : NormedSpace ℂ E := { norm_smul_le := fun a b => (map_smul_eq_mul p a b).le }
  obtain ⟨f, hf, hx⟩ := exists_dual_vector'' ℂ x
  refine ⟨f.toLinearMap, fun y => ?_, ?_⟩
  · change ‖f y‖ ≤ ‖y‖
    exact (f.le_opNorm y).trans (by simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg y))
  · change ‖f x‖ = ‖x‖
    rw [hx]
    simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]

private theorem norming_functional {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E]
    (p : Seminorm ℂ E) (hp : Continuous p) (x : E) :
    ∃ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ p y) ∧ ‖f x‖ = p x := by
  obtain ⟨f, hf, hx⟩ := seminorm_norming p x
  have hc : Continuous f := (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng ℂ f
    ⟨{⟨p, hp⟩}, 1, by simpa using (show (normSeminorm ℂ ℂ).comp f ≤ p from hf)⟩
  exact ⟨⟨f, hc⟩, hf, hx⟩

private def evalMap (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E] : E →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ E) where
  toFun x := { toLinearMap := (topDualPairing ℂ E).flip x
               cont := continuous_eval_const x }
  map_add' x y := by ext f; exact f.map_add x y
  map_smul' c x := by ext f; exact f.map_smul c x

private theorem evalMap_continuous (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [FirstCountableTopology E] : Continuous (evalMap E) := by
  refine LinearMap.continuous_of_locally_bounded (𝕜 := ℂ) (𝕜' := ℂ) (σ := RingHom.id ℂ) (E := E) (F := StrongDual ℂ (StrongDual ℂ E)) (evalMap E) ?_
  intro s hs
  apply ContinuousLinearMap.isVonNBounded_iff.mpr
  intro B hB
  apply (ContinuousLinearMap.isVonNBounded_image2_apply hB hs).subset
  rintro _ ⟨_, ⟨x, hx, rfl⟩, f, hf, rfl⟩
  exact ⟨f, hf, x, hx, rfl⟩

private theorem dominated_functionals_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E]
    (p : Seminorm ℂ E) (hp : Continuous p) :
    Bornology.IsVonNBounded ℂ {f : StrongDual ℂ E | ∀ x, ‖f x‖ ≤ p x} := by
  apply ContinuousLinearMap.isVonNBounded_iff.mpr
  intro s hs
  obtain ⟨r, hr, hbound⟩ :=
    (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp hs ⟨p, hp⟩
  apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
  refine ⟨r, ?_⟩
  rintro _ ⟨f, hf, x, hx, rfl⟩
  exact (hf x).trans (hbound x hx).le

private theorem evalMap_isInducing {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [FirstCountableTopology E] [PolynormableSpace ℂ E] : IsInducing (evalMap E) := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  apply le_antisymm
  · simpa using ((evalMap_continuous E).continuousAt (x := 0)).tendsto.le_comap
  · let P := PolynormableSpace.withSeminorms ℂ E
    rw [P.hasBasis_zero_ball.ge_iff]
    rintro ⟨s, r⟩ hr
    let p : Seminorm ℂ E := s.sup (fun q : {q : Seminorm ℂ E // Continuous q} => q.1)
    have hp : Continuous p := Seminorm.continuous_finsetSup (fun q _ => q.2)
    let B : Set (StrongDual ℂ E) := {f | ∀ x, ‖f x‖ ≤ p x}
    have hB : Bornology.IsVonNBounded ℂ B := dominated_functionals_bounded p hp
    have hN := ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hB
      (Metric.ball_mem_nhds (0 : ℂ) hr)
    apply Filter.mem_of_superset (Filter.preimage_mem_comap hN)
    intro x hx
    change p (x - 0) < r
    rw [sub_zero]
    obtain ⟨f, hf, hfx⟩ := norming_functional p hp x
    have hval := hx hf
    change dist (f x) 0 < r at hval
    simpa [dist_zero_right, hfx] using hval

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    ∃ V : Submodule ℂ (StrongDual ℂ (StrongDual ℂ E)), Nonempty (E ≃L[ℂ] V) := by
  obtain ⟨⟨ι, hι, p, hp⟩, ⟨hT, _⟩, hM⟩ := hE
  have : T2Space E := hT
  have : TopologicalSpace.MetrizableSpace E := hM
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : PolynormableSpace ℂ E := hp.toPolynormableSpace
  have hJ : IsInducing (evalMap E) := evalMap_isInducing
  let e := LinearEquiv.ofInjective (evalMap E) hJ.injective
  refine ⟨(evalMap E).range, ⟨{ e with
    continuous_toFun := ?_
    continuous_invFun := ?_ }⟩⟩
  · exact (evalMap_continuous E).subtype_mk _
  · apply hJ.continuous_iff.mpr
    convert continuous_subtype_val using 1
    funext x
    exact LinearEquiv.ofInjective_symm_apply (evalMap E) (h := hJ.injective) x
