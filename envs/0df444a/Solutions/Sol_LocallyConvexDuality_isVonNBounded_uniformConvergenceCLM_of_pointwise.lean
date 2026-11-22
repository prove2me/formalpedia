-- Prove2me | solution 1 for LocallyConvexDuality.isVonNBounded_uniformConvergenceCLM_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:05:15.852981+00:00
-- url     : https://prove2.me/submissions/502c2a93-554a-4793-b0ff-c40cd3d0c54f

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

namespace Sol_LocallyConvexDuality_isVonNBounded_uniformConvergenceCLM_of_pointwise

open Set Filter Bornology
open scoped Topology Pointwise ComplexOrder

/-- On each bounded set in a quasi-complete polynormable space, a pointwise bounded family
of continuous linear maps has bounded joint image. -/
theorem isVonNBounded_image2_apply_of_pointwise {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F]
    [PolynormableSpace 𝕜 F]
    {ι : Type*} (f : ι → E →L[𝕜] F)
    (hf : ∀ x, IsVonNBounded 𝕜 (range fun i ↦ f i x))
    {T : Set E} (hT : IsVonNBounded 𝕜 T) :
    IsVonNBounded 𝕜 (image2 (fun (g : E →L[𝕜] F) x ↦ g x) (range f) T) := by
  let : Module ℝ E := Module.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let hE := PolynormableSpace.withSeminorms 𝕜 E
  -- Enlarge the test set to a closed absolutely convex bounded set.
  let D := closedAbsConvexHull 𝕜 (insert 0 T)
  have hTD : T ⊆ D := (subset_insert _ _).trans subset_closedAbsConvexHull
  have hD0 : (0 : E) ∈ D := subset_closedAbsConvexHull (mem_insert _ _)
  have hD : AbsConvex 𝕜 D := absConvex_convexClosedHull
  have hDc : IsClosed D := isClosed_closedAbsConvexHull
  have hDb : IsVonNBounded 𝕜 D := by
    apply hE.isVonNBounded_iff_seminorm_bounded.mpr
    intro j
    obtain ⟨R, hR, hbound⟩ := hE.isVonNBounded_iff_seminorm_bounded.mp (hT.insert 0) j
    let q : Seminorm 𝕜 E := j.val
    refine ⟨R + 1, by positivity, fun x hx ↦ ?_⟩
    have hsub : D ⊆ q.closedBall 0 R := by
      apply closedAbsConvexHull_min (fun y hy ↦ q.mem_closedBall_zero.mpr (hbound y hy).le)
      · refine ⟨q.balanced_closedBall_zero R, ?_⟩
        exact convex_of_nonneg_surjective_algebraMap 𝕜
          (fun _ hz ↦ RCLike.nonneg_iff_exists_ofReal.mp hz) (q.convex_closedBall 0 R)
      · rw [Seminorm.closedBall_zero_eq]
        exact isClosed_Iic.preimage (hE.continuous_seminorm j)
    exact (q.mem_closedBall_zero.mp (hsub hx)).trans_lt (lt_add_one R)
  let P := Submodule.span 𝕜 D
  let B : Set P := Subtype.val ⁻¹' D
  let : Module ℝ P := Module.restrictScalars ℝ 𝕜 P
  let : IsScalarTower ℝ 𝕜 P := IsScalarTower.restrictScalars ℝ 𝕜 P
  have hBb : Balanced 𝕜 B :=
    balanced_iff_smul_mem.mpr fun _ ha _ hx ↦ hD.1.smul_mem ha hx
  have hBc : Convex ℝ B := (hD.2.lift ℝ).linear_preimage (P.subtype.restrictScalars ℝ)
  have : ContinuousSMul ℝ P := IsScalarTower.continuousSMul 𝕜
  have hBclosed : IsClosed B := hDc.preimage continuous_subtype_val
  have hscale (r : ℝ) (hr : r ≠ 0) (x : P) : x ∈ r • B ↔ (x : E) ∈ r • D := by
    rw [mem_smul_set_iff_inv_smul_mem₀ hr, mem_smul_set_iff_inv_smul_mem₀ hr]
    rfl
  have hBabs : Absorbent ℝ B := by
    have hspan (x : E) (hx : x ∈ P) : ∃ r : ℝ, 0 < r ∧ x ∈ r • D := by
      induction hx using Submodule.span_induction with
      | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
      | zero => exact ⟨1, one_pos, zero_mem_smul_set hD0⟩
      | add x y _ _ hx hy =>
        obtain ⟨r, hr, hx⟩ := hx
        obtain ⟨s, hs, hy⟩ := hy
        refine ⟨r + s, add_pos hr hs, ?_⟩
        rw [(hD.2.lift ℝ).add_smul hr.le hs.le]
        exact add_mem_add hx hy
      | smul a x _ hx =>
        obtain ⟨r, hr, y, hy, rfl⟩ := hx
        refine ⟨r * (‖a‖ + 1), by positivity, ?_⟩
        rw [mul_smul, smul_comm a r]
        refine smul_mem_smul_set (hD.1.smul_mono (b := ‖a‖ + 1) ?_ (smul_mem_smul_set hy))
        rw [Real.norm_of_nonneg (by positivity)]
        exact le_add_of_nonneg_right zero_le_one
    intro x
    obtain ⟨r, hr, hx⟩ := hspan x x.property
    apply Absorbs.of_norm
    refine ⟨r, fun c hc ↦ singleton_subset_iff.mpr ?_⟩
    refine (show r • B ⊆ c • B from ?_) ((hscale r hr.ne' x).2 hx)
    have hBr : Balanced ℝ B := balanced_iff_smul_mem.mpr fun a ha x hx ↦
      hBb.smul_mem (by simpa [RCLike.norm_ofReal] using ha :
        ‖algebraMap ℝ 𝕜 a‖ ≤ 1) hx
    exact hBr.smul_mono (by simpa [Real.norm_of_nonneg hr.le] using hc)
  -- Equip the span with the gauge of the disk.
  let p := gaugeSeminorm hBb hBc hBabs
  have hunit (x : P) : p x ≤ 1 ↔ x ∈ B :=
    ⟨fun hx ↦ hBclosed.closure_subset (mem_closure_of_gauge_le_one hBc hBabs.zero_mem hBabs hx),
      gauge_le_one_of_mem⟩
  let : SeminormedAddCommGroup P := p.toSeminormedAddCommGroup
  let : NormedSpace 𝕜 P := ⟨fun a x ↦ (map_smul_eq_mul p a x).le⟩
  let : UniformSpace P := (inferInstance : PseudoMetricSpace P).toUniformSpace
  let : TopologicalSpace P := (inferInstance : UniformSpace P).toTopologicalSpace
  have hball {r : ℝ} (hr : 0 < r) (x : P) : ‖x‖ ≤ r ↔ (x : E) ∈ r • D := by
    rw [← hscale r hr.ne', mem_smul_set_iff_inv_smul_mem₀ hr.ne', ← hunit]
    change p x ≤ r ↔ p (r⁻¹ • x) ≤ 1
    rw [show p (r⁻¹ • x) = ‖r⁻¹‖ * p x from map_smul_eq_mul (p.restrictScalars ℝ) _ _,
      norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_one₀ hr]
  let i : P →ₗ[𝕜] E := P.subtype
  have hi : Continuous i := by
    apply continuous_of_continuousAt_zero i
    change Tendsto i (𝓝 0) (𝓝 (i 0))
    rw [map_zero]
    refine (Metric.nhds_basis_closedBall (x := (0 : P))).tendsto_left_iff.mpr ?_
    intro U hU
    obtain ⟨R, hR, hRU⟩ := (hDb hU).exists_pos
    refine ⟨R⁻¹, inv_pos.mpr hR, fun x hx ↦ ?_⟩
    have hx' := (hball (inv_pos.mpr hR) x).1 (by simpa using hx)
    have hsub : D ⊆ (algebraMap ℝ 𝕜 R) • U :=
      hRU _ (by simp [Real.norm_of_nonneg hR.le])
    change (x : E) ∈ U
    exact (show R⁻¹ • D ⊆ U by
      calc
        R⁻¹ • D ⊆ R⁻¹ • ((algebraMap ℝ 𝕜 R) • U) := smul_set_mono hsub
        _ = U := by rw [← smul_assoc, Algebra.smul_def, ← map_mul,
          inv_mul_cancel₀ hR.ne', map_one, one_smul]) hx'
  let j : P →L[𝕜] E := ⟨i, hi⟩
  -- A gauge-Cauchy sequence has bounded image in E. Its ambient limit also lies
  -- in the span, and the closed scaled disks control convergence in the gauge.
  have : CompleteSpace P := by
    apply Metric.complete_of_cauchySeq_tendsto
    intro u hu
    have hb : IsVonNBounded 𝕜 (range (j ∘ u)) := by
      rw [range_comp]
      exact ((NormedSpace.isVonNBounded_iff 𝕜).2 hu.isBounded_range).image j
    have hcomplete := QuasiCompleteSpace.quasiComplete (𝕜 := 𝕜) hb.closure isClosed_closure
    obtain ⟨y, _, hy⟩ := hcomplete (map (j ∘ u) atTop)
      (j.uniformContinuous.comp_cauchySeq hu) (by
        rw [Filter.le_principal_iff, Filter.mem_map]
        exact Eventually.of_forall fun n ↦
          show (j ∘ u) n ∈ closure (range (j ∘ u)) from subset_closure (mem_range_self n))
    change Tendsto (j ∘ u) atTop (𝓝 y) at hy
    have htail (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ n ≥ N, y - j (u n) ∈ ε • D := by
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
      refine ⟨N, fun n hn ↦ ?_⟩
      refine (isClosedMap_smul_of_ne_zero hε.ne' D hDc).mem_of_tendsto
        (hy.sub tendsto_const_nhds) ?_
      filter_upwards [eventually_ge_atTop N] with m hm
      change j (u m) - j (u n) ∈ ε • D
      rw [← map_sub]
      exact (hball hε (u m - u n)).mp (by simpa only [dist_eq_norm] using (hN m hm n hn).le)
    obtain ⟨N, hN⟩ := htail 1 one_pos
    have hyP : y ∈ P := by
      have hdiff : y - j (u N) ∈ D := by simpa using hN N le_rfl
      exact (sub_add_cancel y (j (u N))) ▸
        P.add_mem (Submodule.subset_span hdiff) (u N).property
    refine ⟨⟨y, hyP⟩, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
    obtain ⟨M, hM⟩ := htail (ε / 2) (half_pos hε)
    refine ⟨M, fun n hn ↦ ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact ((hball (half_pos hε) (⟨y, hyP⟩ - u n)).2 (hM n hn)).trans_lt (half_lt_self hε)
  -- Apply Banach–Steinhaus on the gauge space, whose unit ball contains the test set.
  let g (k : ι) := (f k).comp j
  let hF := PolynormableSpace.withSeminorms 𝕜 F
  have hg : UniformEquicontinuous ((↑) ∘ g) :=
    PolynormableSpace.banach_steinhaus (fun x ↦ hf (j x))
  apply hF.isVonNBounded_iff_seminorm_bddAbove.mpr
  intro k
  obtain ⟨q, hq, hle⟩ := (hF.uniformEquicontinuous_iff_exists_continuous_seminorm
    (fun a ↦ (g a).toLinearMap)).mp hg k
  have : PolynormableSpace 𝕜 P := (norm_withSeminorms 𝕜 P).toPolynormableSpace
  obtain ⟨C, _, hC⟩ := (PolynormableSpace.withSeminorms 𝕜 P).isVonNBounded_iff_seminorm_bounded.mp
    (NormedSpace.isVonNBounded_closedBall 𝕜 P 1) ⟨q, hq⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨z, ⟨_, ⟨a, rfl⟩, x, hx, rfl⟩, rfl⟩
  let x' : P := ⟨x, Submodule.subset_span (hTD hx)⟩
  have hx' : ‖x'‖ ≤ 1 := (hunit x').2 (hTD hx)
  exact (hle a x').trans (hC x' (by simpa using hx')).le

end Sol_LocallyConvexDuality_isVonNBounded_uniformConvergenceCLM_of_pointwise

theorem solution {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
    [PolynormableSpace 𝕜 F] [T2Space F]
    (𝔖 : Set (Set E)) (h𝔖 : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜 S)
    (H : Set (E →L[𝕜] F))
    (hH : ∀ x : E, Bornology.IsVonNBounded 𝕜 ((fun f : E →L[𝕜] F => f x) '' H)) :
    Bornology.IsVonNBounded 𝕜 (UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F 𝔖 '' H) := by
  rw [UniformConvergenceCLM.isVonNBounded_iff]
  intro T hT
  have hpoint (x : E) : Bornology.IsVonNBounded 𝕜 (Set.range fun f : H ↦ (f : E →L[𝕜] F) x) := by
    refine (hH x).subset ?_
    rintro _ ⟨f, rfl⟩
    exact ⟨f.1, f.2, rfl⟩
  have h := Sol_LocallyConvexDuality_isVonNBounded_uniformConvergenceCLM_of_pointwise.isVonNBounded_image2_apply_of_pointwise
    (fun f : H ↦ (f : E →L[𝕜] F)) hpoint
    (h𝔖 T hT)
  refine h.subset ?_
  rintro _ ⟨_, ⟨f, hf, rfl⟩, x, hx, rfl⟩
  exact ⟨f, ⟨⟨f, hf⟩, rfl⟩, x, hx, rfl⟩
