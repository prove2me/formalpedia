-- Prove2me | solution 1 for LocallyConvexDuality.quasiCompleteSpace_uniformConvergenceCLM
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:14:21.630712+00:00
-- url     : https://prove2.me/submissions/1f7bc885-783f-45fc-bf35-5ecc5ae57213

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

open Set Filter Topology Bornology in
theorem solution {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [BarrelledSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
    [PolynormableSpace 𝕜 F] [T2Space F] [QuasiCompleteSpace 𝕜 F]
    (𝔖 : Set (Set E)) (h𝔖 : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜 S) (hcov : ⋃₀ 𝔖 = Set.univ) :
    QuasiCompleteSpace 𝕜 (E →Lᵤ[𝕜, 𝔖] F) := by
  refine ⟨fun A hA hAc ↦ completeSpace_coe_iff_isComplete.mp ⟨fun {l} hl ↦ ?_⟩⟩
  have := hl.1
  -- the members of `A`, seen as plain continuous linear maps
  let g : A → E →L[𝕜] F := fun a ↦ (UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F 𝔖).symm a.val
  have hind := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id 𝕜) F 𝔖
  -- evaluation at a point is uniformly continuous, because `𝔖` covers `E`
  have heval (x : E) : UniformContinuous (fun f : E →Lᵤ[𝕜, 𝔖] F ↦ f x) :=
    (UniformOnFun.uniformContinuous_eval hcov x).comp hind.uniformContinuous
  -- `A` is pointwise bounded
  have hbounded (x : E) : IsVonNBounded 𝕜 (range fun a : A ↦ g a x) := by
    let ev : (E →Lᵤ[𝕜, 𝔖] F) →L[𝕜] F :=
      ⟨{ toFun := fun f ↦ f x
         map_add' := fun _ _ ↦ rfl
         map_smul' := fun _ _ ↦ rfl }, (heval x).continuous⟩
    change IsVonNBounded 𝕜 (range (ev ∘ (Subtype.val : A → _)))
    rw [range_comp, Subtype.range_coe]
    exact hA.image ev
  -- quasi-completeness of the target gives a limit at each point
  have hlimit (x : E) : ∃ y, Tendsto (fun a : A ↦ g a x) l (𝓝 y) := by
    let gx : A → F := fun a ↦ g a x
    have hc : Cauchy (l.map gx) := hl.map ((heval x).comp uniformContinuous_subtype_val)
    have hmem : l.map gx ≤ 𝓟 (closure (range gx)) := by
      rw [le_principal_iff, mem_map]
      exact Eventually.of_forall fun a ↦ subset_closure (mem_range_self a)
    obtain ⟨y, _, hy⟩ := QuasiCompleteSpace.quasiComplete (hbounded x).closure isClosed_closure
      _ hc hmem
    exact ⟨y, hy⟩
  choose f hf using hlimit
  have hpoint : Tendsto (fun a x ↦ g a x) l (𝓝 f) := tendsto_pi_nhds.mpr hf
  -- Banach–Steinhaus makes the pointwise limit continuous
  let G : E →L[𝕜] F := ⟨linearMapOfTendsto f (fun a ↦ (g a).toLinearMap) hpoint,
    hpoint.continuous_of_equicontinuous (PolynormableSpace.banach_steinhaus hbounded).equicontinuous⟩
  let G' := UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F 𝔖 G
  -- the filter converges to the limit uniformly on each member of `𝔖`
  have hG : Tendsto (Subtype.val : A → E →Lᵤ[𝕜, 𝔖] F) l (𝓝 G') := by
    apply (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn _ _ 𝔖).mpr
    intro T hT
    have hc := hl.map (hind.uniformContinuous.comp uniformContinuous_subtype_val)
    have hu : UniformCauchySeqOn (fun a x ↦ g a x) l T := fun U hU ↦
      cauchy_map_iff'.mp hc (UniformOnFun.gen_mem_uniformity F 𝔖 hT hU)
    exact hu.tendstoUniformlyOn_of_tendsto fun x _ ↦ hf x
  have hGA := hAc.mem_of_tendsto hG (Eventually.of_forall Subtype.property)
  exact ⟨⟨G', hGA⟩, tendsto_subtype_rng.mpr hG⟩
