-- Prove2me | solution 1 for LocallyConvexDuality.tendsto_strongDual_of_tendsto_pointwise_of_barrelled_montel
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:43:32.401006+00:00
-- url     : https://prove2.me/submissions/1645d76b-71fe-4c93-824e-8bc000f86b47

import Mathlib

open Filter Topology

set_option autoImplicit false


theorem solution
    {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]
    [BarrelledSpace 𝕜 E] [MontelSpace 𝕜 E]
    (φ : ℕ → StrongDual 𝕜 E) (f : E → 𝕜)
    (hφ : ∀ x : E, Tendsto (fun n : ℕ => φ n x) atTop (𝓝 (f x))) :
    ∃ F : StrongDual 𝕜 E, (∀ x : E, F x = f x) ∧
      (∀ B : Set E, Bornology.IsVonNBounded 𝕜 B →
        TendstoUniformlyOn (fun (n : ℕ) (x : E) => φ n x) (fun x : E => F x) atTop B) ∧
      Tendsto φ atTop (𝓝 F) := by
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have _ : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  -- pointwise convergence as convergence in the product topology
  have h : Tendsto (fun n x ↦ φ n x) atTop (𝓝 f) := tendsto_pi_nhds.mpr hφ
  -- Banach–Steinhaus: the sequence is equicontinuous
  have hbdd : ∀ x, Bornology.IsVonNBounded 𝕜 (Set.range fun n ↦ φ n x) :=
    fun x ↦ (hφ x).isVonNBounded_range 𝕜
  have heq : UniformEquicontinuous ((↑) ∘ φ : ℕ → E → 𝕜) :=
    PolynormableSpace.banach_steinhaus hbdd
  -- the limit is a continuous linear functional
  let F : StrongDual 𝕜 E := continuousLinearMapOfTendsto φ h
  have hF : ∀ x, F x = f x := fun x ↦ rfl
  -- uniform convergence on compact sets (equicontinuity + pointwise convergence)
  have hK : ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun (n : ℕ) (x : E) => φ n x) (fun x : E => F x) atTop K := by
    have hcov : ⋃₀ {K : Set E | IsCompact K} = Set.univ :=
      Set.eq_univ_of_forall fun x ↦ ⟨{x}, isCompact_singleton, rfl⟩
    have := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi (𝔖 := {K : Set E | IsCompact K})
      (fun K hK ↦ hK) hcov (fun K _ ↦ heq.equicontinuous.equicontinuousOn K) atTop f).mpr h
    rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at this
    exact this
  -- Montel: the closure of a bounded set is compact
  have hB : ∀ B : Set E, Bornology.IsVonNBounded 𝕜 B →
      TendstoUniformlyOn (fun (n : ℕ) (x : E) => φ n x) (fun x : E => F x) atTop B :=
    fun B hB ↦ (hK _ (MontelSpace.isCompact_of_isClosed_of_isVonNBounded 𝕜 isClosed_closure
      hB.closure)).mono subset_closure
  refine ⟨F, hF, hB, ?_⟩
  exact (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn (σ := RingHom.id 𝕜) (F := 𝕜)
    {S : Set E | Bornology.IsVonNBounded 𝕜 S}).mpr hB
