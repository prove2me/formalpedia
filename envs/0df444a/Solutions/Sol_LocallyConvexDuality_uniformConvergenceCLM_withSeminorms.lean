-- Prove2me | solution 1 for LocallyConvexDuality.uniformConvergenceCLM_withSeminorms
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:53:47.709183+00:00
-- url     : https://prove2.me/submissions/6abb6333-ec12-460e-8857-f049b8744b09

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

namespace Sol_LocallyConvexDuality_uniformConvergenceCLM_withSeminorms

open Filter Topology Set

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F]

/-- Evaluation at a point `x`, as a linear map on the space of continuous linear maps with the
topology of uniform convergence on the members of `𝔖`. -/
def evalₗ (𝔖 : Set (Set E)) (x : E) : (E →Lᵤ[𝕜, 𝔖] F) →ₗ[𝕜] F where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalₗ_apply (𝔖 : Set (Set E)) (x : E) (f : E →Lᵤ[𝕜, 𝔖] F) :
    evalₗ (𝕜 := 𝕜) (F := F) 𝔖 x f = f x := rfl

/-- The seminorm `f ↦ ⨆ x ∈ T, ν (f x)` on the space of continuous linear maps. -/
noncomputable def supSeminorm (𝔖 : Set (Set E)) (T : Set E) (ν : Seminorm 𝕜 F) :
    Seminorm 𝕜 (E →Lᵤ[𝕜, 𝔖] F) :=
  ⨆ x : T, ν.comp (evalₗ 𝔖 (x : E))

/-- If `f '' T` is bounded for the seminorm `ν` for every `f`, the seminorm `supSeminorm 𝔖 T ν`
is given by the pointwise supremum. -/
theorem supSeminorm_apply (𝔖 : Set (Set E)) (T : Set E) (ν : Seminorm 𝕜 F)
    (hb : ∀ f : E →Lᵤ[𝕜, 𝔖] F, BddAbove (range fun x : T => ν (f x)))
    (f : E →Lᵤ[𝕜, 𝔖] F) :
    supSeminorm 𝔖 T ν f = ⨆ x : T, ν (f x) := by
  unfold supSeminorm
  refine Seminorm.iSup_apply (Seminorm.bddAbove_range_iff.mpr fun g => ?_)
  exact hb g

end Sol_LocallyConvexDuality_uniformConvergenceCLM_withSeminorms

open Sol_LocallyConvexDuality_uniformConvergenceCLM_withSeminorms in
open Filter Topology Set in
theorem solution {𝕜 E F ι : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [T2Space F]
    (p : SeminormFamily 𝕜 F ι) (hp : WithSeminorms p)
    (𝔖 : Set (Set E)) (h𝔖 : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜 S) :
    ∃ q : SeminormFamily 𝕜 (E →Lᵤ[𝕜, 𝔖] F) (𝔖 × ι),
      (∀ (T : 𝔖) (i : ι) (f : E →Lᵤ[𝕜, 𝔖] F), q (T, i) f = ⨆ x : (T : Set E), p i (f x)) ∧
        WithSeminorms q := by
  -- Boundedness of `x ↦ p i (f x)` on each member of `𝔖`.
  have hbdd : ∀ (T : Set E), T ∈ 𝔖 → ∀ (i : ι) (f : E →Lᵤ[𝕜, 𝔖] F),
      BddAbove (range fun x : T => p i (f x)) := by
    intro T hT i f
    obtain ⟨r, _, hr⟩ :=
      (hp.image_isVonNBounded_iff_seminorm_bounded (fun x : E => f x)).mp
        ((h𝔖 T hT).image (f : E →L[𝕜] F)) i
    exact ⟨r, forall_mem_range.mpr fun x => (hr x x.2).le⟩
  let q : SeminormFamily 𝕜 (E →Lᵤ[𝕜, 𝔖] F) (𝔖 × ι) := fun a =>
    supSeminorm 𝔖 (a.1 : Set E) (p a.2)
  have hq : ∀ (a : 𝔖 × ι) (f : E →Lᵤ[𝕜, 𝔖] F),
      q a f = ⨆ x : (a.1 : Set E), p a.2 (f x) := fun a f =>
    supSeminorm_apply 𝔖 (a.1 : Set E) (p a.2) (hbdd a.1 a.1.2 a.2) f
  refine ⟨q, fun T i f => hq (T, i) f, ?_⟩
  rw [q.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun a => ?_) ?_
  · -- each `q a` is continuous at `0`
    rw [((Metric.nhds_basis_ball (x := (0 : ℝ))).comap (q a)).ge_iff]
    intro r hr
    rw [← (q a).ball_zero_eq_preimage_ball]
    have hball : (p a.2).ball 0 (r / 2) ∈ 𝓝 (0 : F) :=
      Seminorm.ball_mem_nhds (hp.continuous_seminorm a.2) (half_pos hr)
    filter_upwards [UniformConvergenceCLM.eventually_nhds_zero_mapsTo
      (RingHom.id 𝕜) a.1.2 hball] with f hf
    refine (q a).mem_ball_zero.mpr ?_
    rw [hq]
    exact (Real.iSup_le (fun x => ((p a.2).mem_ball_zero.mp (hf x.2)).le)
      (half_pos hr).le).trans_lt (half_lt_self hr)
  · -- every basic neighbourhood of `0` contains a finite intersection of `q`-balls
    rw [UniformConvergenceCLM.nhds_zero_eq_of_basis (RingHom.id 𝕜) F 𝔖 hp.hasBasis_zero_ball]
    simp only [le_iInf_iff, le_principal_iff]
    intro T hT ir hr
    have hball : ∀ i : ι, (q (⟨T, hT⟩, i)).ball 0 ir.2 ∈ ⨅ a, comap (q a) (𝓝 (0 : ℝ)) := by
      intro i
      rw [(q (⟨T, hT⟩, i)).ball_zero_eq_preimage_ball]
      refine mem_iInf_of_mem (f := fun a => comap (q a) (𝓝 (0 : ℝ))) (⟨T, hT⟩, i) ?_
      exact preimage_mem_comap (Metric.ball_mem_nhds (0 : ℝ) hr)
    have hFin : (⋂ i ∈ ir.1, (q (⟨T, hT⟩, i)).ball 0 ir.2) ∈
        ⨅ a, comap (q a) (𝓝 (0 : ℝ)) :=
      (Finset.iInter_mem_sets ir.1).mpr fun i _ => hball i
    refine mem_of_superset hFin ?_
    intro f hf x hx
    refine (ir.1.sup p).mem_ball_zero.mpr ?_
    refine Seminorm.finset_sup_apply_lt hr ?_
    intro i hi
    have hxle : p i (f x) ≤ q (⟨T, hT⟩, i) f := by
      rw [hq]
      exact le_ciSup (f := fun y : T => p i (f y)) (hbdd T hT i f) ⟨x, hx⟩
    exact hxle.trans_lt ((q (⟨T, hT⟩, i)).mem_ball_zero.mp (mem_iInter₂.mp hf i hi))
