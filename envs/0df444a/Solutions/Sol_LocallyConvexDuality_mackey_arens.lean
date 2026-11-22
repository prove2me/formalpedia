-- Prove2me | solution 1 for LocallyConvexDuality.mackey_arens
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:21:56.751482+00:00
-- url     : https://prove2.me/submissions/b6e2c2f3-162c-4f25-a664-11cefc3d38d8

import Mathlib
import Definitions.Def_LocallyConvexDuality_PolarTopology

set_option autoImplicit false

namespace Sol_LocallyConvexDuality_mackey_arens

open Set Filter Topology
open scoped ComplexOrder Pointwise
open LocallyConvexDuality

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- **Bipolar theorem** for the absolute polars of a pairing: the bipolar of `A ⊆ E` is the
`σ(E, F)`-closure of the absolutely convex hull of `A ∪ {0}`. -/
theorem bipolar (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (A : Set E) :
    B.flip.polar (B.polar A) =
      closure (X := WeakBilin B) (absConvexHull 𝕜 (insert (0 : E) A)) := by
  let C : Set (WeakBilin B) := closure (X := WeakBilin B) (absConvexHull 𝕜 (insert (0 : E) A))
  have hsub : insert (0 : E) A ⊆ C :=
    subset_absConvexHull.trans (subset_closure (X := WeakBilin B))
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxC
    let : Module ℝ (WeakBilin B) := Module.restrictScalars ℝ 𝕜 _
    have : IsScalarTower ℝ 𝕜 (WeakBilin B) := IsScalarTower.restrictScalars ℝ 𝕜 _
    have : LocallyConvexSpace ℝ (WeakBilin B) :=
      B.weakBilin_withSeminorms.toLocallyConvexSpace
    have hC : AbsConvex 𝕜 C := AbsConvex.closure (E := WeakBilin B) absConvex_absConvexHull
    obtain ⟨f, r, hfr, hrx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
      (E := WeakBilin B) (s := C) (x := x) (hC.2.lift ℝ) isClosed_closure hxC
    obtain ⟨y, hy⟩ := LinearMap.dualEmbedding_surjective B f
    have hfy : ∀ z : WeakBilin B, f z = B z y := fun z => by rw [← hy]; rfl
    have hnorm : ∀ z : WeakBilin B, z ∈ C → ‖B z y‖ < r := by
      intro z hz
      obtain ⟨c, hc, hcz⟩ := RCLike.exists_norm_eq_mul_self (B z y)
      have hmem : c • z ∈ C := balanced_iff_smul_mem.mp hC.1 hc.le hz
      have h : RCLike.re (f (c • z)) < r := hfr (c • z) hmem
      have h2 : f (c • z) = ((‖B z y‖ : ℝ) : 𝕜) := by
        rw [map_smul, hfy, smul_eq_mul, ← hcz]
      rw [h2, RCLike.ofReal_re] at h
      exact h
    have hr : 0 < r := (norm_nonneg _).trans_lt (hnorm 0 (hsub (Set.mem_insert _ _)))
    have hscale : ∀ z : E, ‖B z ((r : 𝕜)⁻¹ • y)‖ = ‖B z y‖ / r := by
      intro z
      rw [map_smul, smul_eq_mul, norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hr,
        div_eq_inv_mul]
    have hy' : (r : 𝕜)⁻¹ • y ∈ B.polar A := by
      intro z hz
      rw [hscale, div_le_iff₀ hr, one_mul]
      exact (hnorm z (hsub (Set.mem_insert_of_mem _ hz))).le
    have hbound : ‖B x ((r : 𝕜)⁻¹ • y)‖ ≤ 1 := hx _ hy'
    rw [hscale, div_le_iff₀ hr, one_mul] at hbound
    have hrx' : r < RCLike.re (B x y) := lt_of_lt_of_eq hrx (congrArg RCLike.re (hfy x))
    exact absurd hbound (not_le.mpr (hrx'.trans_le (RCLike.re_le_norm _)))
  · exact closure_minimal (X := WeakBilin B)
      (absConvexHull_min (Set.insert_subset (B.flip.zero_mem_polar _) (B.subset_bipolar A))
        (LinearMap.polar_AbsConvex _)) (B.flip.polar_isClosed (B.polar A))

/-- **Hahn–Banach**: a continuous seminorm on a locally convex space is attained at a given vector
by the absolute value of a continuous linear functional dominated by that seminorm. -/
theorem exists_dual_norm_eq_seminorm [TopologicalSpace E] [PolynormableSpace 𝕜 E]
    (p : Seminorm 𝕜 E) (hp : Continuous p) (z : E) :
    ∃ φ : StrongDual 𝕜 E, (∀ y, ‖φ y‖ ≤ p y) ∧ ‖φ z‖ = p z := by
  by_cases hz : z = 0
  · exact ⟨0, fun _ ↦ by simp, by simp [hz]⟩
  let e := LinearEquiv.toSpanNonzeroSingleton 𝕜 E z hz
  let g : Module.Dual 𝕜 (Submodule.span 𝕜 {z}) := (p z : 𝕜) • e.symm.toLinearMap
  have hb (u : Submodule.span 𝕜 {z}) : ‖g u‖ ≤ p u := by
    obtain ⟨a, rfl⟩ := e.surjective u
    change ‖(p z : 𝕜) * e.symm (e a)‖ ≤ p (a • z)
    rw [e.symm_apply_apply, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p z),
      map_smul_eq_mul, mul_comm]
  obtain ⟨φ, hφ, hbound⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm _ g hp hb
  refine ⟨φ, hbound, ?_⟩
  have h := hφ (e 1)
  change φ ((1 : 𝕜) • z) = (p z : 𝕜) * e.symm (e 1) at h
  simp only [one_smul, e.symm_apply_apply, mul_one] at h
  rw [h, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p z)]

/-- For a compatible topology, the elements of the paired space dominated by a continuous
seminorm form a `σ(F, E)`-compact set (Alaoglu–Bourbaki). -/
theorem isCompact_dualSeminormBall (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [t : TopologicalSpace E]
    [PolynormableSpace 𝕜 E] (h : IsCompatibleTopology B t) (p : Seminorm 𝕜 E)
    (hp : Continuous p) :
    IsCompact (X := WeakBilin B.flip) {y | ∀ x, ‖B x y‖ ≤ p x} := by
  let D : Set (E → 𝕜) := univ.pi fun x ↦ Metric.closedBall 0 (p x)
  let ev : WeakBilin B.flip → (E → 𝕜) := fun y x ↦ B x y
  have hD : IsCompact D := isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _
  have hev : IsInducing ev := ⟨rfl⟩
  apply hev.isCompact_iff.mpr
  have himage : ev '' {y | ∀ x, ‖B x y‖ ≤ p x} =
      D ∩ range ((↑) : Module.Dual 𝕜 E → E → 𝕜) := by
    ext f
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨fun x _ ↦ mem_closedBall_zero_iff.mpr (hy x), ⟨B.flip y, rfl⟩⟩
    · rintro ⟨hf, l, rfl⟩
      have hb (x : E) : ‖l x‖ ≤ p x := mem_closedBall_zero_iff.mp (hf x (mem_univ x))
      have hl : Continuous l := by
        have : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms 𝕜 E).topologicalAddGroup
        apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms 𝕜 𝕜) l
        exact fun _ ↦ Seminorm.continuous_of_le hp hb
      obtain ⟨y, rfl⟩ := (h l).mp hl
      exact ⟨y, hb, rfl⟩
  rw [himage]
  exact hD.inter_right (LinearMap.isClosed_range_coe E 𝕜 (RingHom.id 𝕜))

/-- Under a compatible topology, each continuous seminorm is attained by evaluating against
an absolutely convex `σ(F, E)`-compact set of the paired space. -/
theorem exists_mackeyDisk (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [t : TopologicalSpace E]
    [PolynormableSpace 𝕜 E] (h : IsCompatibleTopology B t) (p : Seminorm 𝕜 E)
    (hp : Continuous p) :
    ∃ A : Set F, (AbsConvex 𝕜 A ∧ IsCompact (X := WeakBilin B.flip) A) ∧
      ∀ x : E, ∃ y ∈ A, ‖B x y‖ = p x := by
  let A : Set F := {y | ∀ x, ‖B x y‖ ≤ p x}
  refine ⟨A, ⟨?_, isCompact_dualSeminormBall B h p hp⟩, ?_⟩
  · let : Module ℝ F := Module.restrictScalars ℝ 𝕜 F
    have : IsScalarTower ℝ 𝕜 F := IsScalarTower.restrictScalars ℝ 𝕜 F
    let q (x : E) : Seminorm 𝕜 F := (normSeminorm 𝕜 𝕜).comp (B x)
    have hA : A = ⋂ x, (q x).closedBall 0 (p x) := by
      ext y
      simp [A, q]
    rw [hA]
    exact ⟨balanced_iInter fun x ↦ (q x).balanced_closedBall_zero (p x),
      convex_iInter fun x ↦ convex_RCLike_iff_convex_real.mpr ((q x).convex_closedBall 0 (p x))⟩
  · intro x
    obtain ⟨φ, hφ, hφx⟩ := exists_dual_norm_eq_seminorm p hp x
    obtain ⟨y, hy⟩ := (h φ.toLinearMap).mp φ.continuous
    refine ⟨y, fun z ↦ ?_, ?_⟩
    · rw [← LinearMap.flip_apply B, hy]
      exact hφ z
    · rw [← LinearMap.flip_apply B, hy]
      exact hφx

/-- A compatible locally convex topology is coarser than the Mackey topology. -/
theorem mackey_le_of_compatible (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [t : TopologicalSpace E]
    [PolynormableSpace 𝕜 E] (h : IsCompatibleTopology B t) : mackeyTopology B ≤ t := by
  let K : Set (Set F) := {A | AbsConvex 𝕜 A ∧ IsCompact (X := WeakBilin B.flip) A}
  let ev (x : E) := UniformOnFun.ofFun K (fun y : F => B x y)
  have : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms 𝕜 E).topologicalAddGroup
  have : ContinuousSMul 𝕜 E := (PolynormableSpace.withSeminorms 𝕜 E).continuousSMul
  apply continuous_id_iff_le.mp
  apply (@continuous_iff_continuousAt E E (mackeyTopology B) t id).mpr
  intro x
  suffices hx : Tendsto (fun z : E ↦ z - x) (@nhds E (mackeyTopology B) x) (𝓝 0) by
    change Tendsto (fun z : E ↦ z) (@nhds E (mackeyTopology B) x) (@nhds E t x)
    simpa only [sub_add_cancel, zero_add] using hx.add_const x
  change Tendsto _ (@nhds E (TopologicalSpace.induced ev inferInstance) x) _
  rw [nhds_induced]
  refine (PolynormableSpace.withSeminorms 𝕜 E).hasBasis_zero_ball.tendsto_right_iff.mpr ?_
  rintro ⟨s, r⟩ hr
  have hr' : (0 : ℝ) < r := hr
  set p : Seminorm 𝕜 E := s.sup (fun p : {p : Seminorm 𝕜 E // Continuous p} ↦ p.1) with hpdef
  have hp : Continuous p :=
    Seminorm.continuous (r := r)
      ((PolynormableSpace.withSeminorms 𝕜 E).hasBasis_zero_ball.mem_of_mem (i := (s, r)) hr)
  obtain ⟨A, hA, hattain⟩ := exists_mackeyDisk B h p hp
  have hnear := UniformOnFun.gen_mem_nhds 𝕜 K (ev x) (s := A) hA
    (Metric.uniformity_basis_dist.mem_iff.mpr ⟨r, hr', Subset.rfl⟩)
  filter_upwards [preimage_mem_comap hnear] with z hz
  obtain ⟨y, hy, hEq⟩ := hattain (z - x)
  have hlt : dist (B x y) (B z y) < r := hz y hy
  rw [dist_comm, dist_eq_norm, ← LinearMap.sub_apply, ← map_sub, hEq] at hlt
  exact p.mem_ball_zero.mpr hlt

/-- Every Mackey-continuous linear functional is an evaluation against the paired space. -/
theorem mem_range_flip_of_mackeyContinuous (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (l : E →ₗ[𝕜] 𝕜)
    (hl : @Continuous _ _ (mackeyTopology B) _ l) : l ∈ range B.flip := by
  let K : Set (Set F) := {A | AbsConvex 𝕜 A ∧ IsCompact (X := WeakBilin B.flip) A}
  have hzero : ({0} : Set F) ∈ K :=
    ⟨⟨balanced_zero, convex_singleton _⟩, isCompact_singleton⟩
  have hdir : DirectedOn (· ⊆ ·) K := by
    intro A hA D hD
    rcases A.eq_empty_or_nonempty with rfl | hAn
    · exact ⟨D, hD, empty_subset _, Subset.rfl⟩
    rcases D.eq_empty_or_nonempty with rfl | hDn
    · exact ⟨A, hA, Subset.rfl, empty_subset _⟩
    refine ⟨A + D, ⟨⟨hA.1.1.add hD.1.1, hA.1.2.add hD.1.2⟩, hA.2.add hD.2⟩, ?_, ?_⟩
    · intro y hy
      simpa only [add_zero] using add_mem_add hy (hD.1.1.zero_mem hDn)
    · intro y hy
      simpa only [zero_add] using add_mem_add (hA.1.1.zero_mem hAn) hy
  let ev (x : E) := UniformOnFun.ofFun K (fun y : F => B x y)
  have hn : {x : E | ‖l x‖ < 1} ∈ @nhds E (mackeyTopology B) 0 := by
    have hc0 : @ContinuousAt E 𝕜 (mackeyTopology B) _ l 0 :=
      @Continuous.continuousAt E 𝕜 (mackeyTopology B) _ l 0 hl
    have h1 : l ⁻¹' Metric.ball (l 0) 1 ∈ @nhds E (mackeyTopology B) 0 :=
      hc0 (Metric.ball_mem_nhds (l 0) one_pos)
    refine Filter.mem_of_superset h1 fun x hx => ?_
    have hx' : dist (l x) (l 0) < 1 := hx
    rw [map_zero, dist_zero_right] at hx'
    exact hx'
  change _ ∈ @nhds _ (TopologicalSpace.induced ev inferInstance) 0 at hn
  rw [nhds_induced] at hn
  obtain ⟨⟨A, ε⟩, ⟨hA, hε⟩, hbound⟩ :=
    ((UniformOnFun.hasBasis_nhds_of_basis F 𝕜 K (ev 0) ⟨{0}, hzero⟩ hdir
      Metric.uniformity_basis_dist).comap ev).mem_iff.mp hn
  have hε' : (0 : ℝ) < ε := hε
  obtain ⟨D, hD, hAD, h0D⟩ := hdir A hA {0} hzero
  -- the canonical pairing between the algebraic dual `E*` and `E`
  let P : Module.Dual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜 := (Module.Dual.eval 𝕜 E).flip
  let j : F →ₗ[𝕜] Module.Dual 𝕜 E := B.flip
  have hj : @Continuous F (Module.Dual 𝕜 E) (WeakBilin.instTopologicalSpace B.flip)
      (WeakBilin.instTopologicalSpace P) j := by
    let : TopologicalSpace F := WeakBilin.instTopologicalSpace B.flip
    exact WeakBilin.continuous_of_continuous_eval (B := P)
      fun x ↦ WeakBilin.eval_continuous B.flip x
  have hT2 : T2Space (WeakBilin P) :=
    (WeakBilin.isEmbedding (B := P) fun _ _ h ↦ h).t2Space
  -- the bipolar of the image of the disk is the disk itself in the algebraic dual
  have heq : P.flip.polar (P.polar (j '' D)) ⊆ j '' D := by
    have hzero' : (0 : Module.Dual 𝕜 E) ∈ j '' D := ⟨0, h0D (mem_singleton 0), map_zero j⟩
    have hbal : Balanced 𝕜 (j '' D) := by
      refine balanced_iff_smul_mem.mpr fun a ha x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨a • y, balanced_iff_smul_mem.mp hD.1.1 ha hy, map_smul j a y⟩
    have hconv : AbsConvex 𝕜 (j '' D) := ⟨hbal, hD.1.2.linear_image j⟩
    have hcomp : IsCompact (X := WeakBilin P) (j '' D) := hD.2.image hj
    have hclosed : IsClosed (X := WeakBilin P) (j '' D) := hcomp.isClosed
    rw [bipolar P (j '' D)]
    exact closure_minimal (X := WeakBilin P)
      (absConvexHull_min (Set.insert_subset hzero' Subset.rfl) hconv) hclosed
  let c : 𝕜 := ((ε / 2 : ℝ) : 𝕜)
  have hc : ‖c‖ = ε / 2 := by
    rw [RCLike.norm_ofReal, abs_of_nonneg (half_pos hε').le]
  have hcl : c • l ∈ j '' D := by
    refine heq ?_
    intro x hx
    have hxD (y : F) (hy : y ∈ D) : ‖B x y‖ ≤ 1 := hx (j y) (mem_image_of_mem j hy)
    have hl' : ‖l (c • x)‖ < 1 := hbound fun y hy ↦ by
      change dist (B (c • x) y) (B 0 y) < ε
      rw [map_zero B, LinearMap.zero_apply, dist_zero_right, map_smul, LinearMap.smul_apply,
        smul_eq_mul, norm_mul, hc]
      exact (mul_le_of_le_one_right (half_pos hε').le (hxD y (hAD hy))).trans_lt
        (half_lt_self hε')
    change ‖(c • l) x‖ ≤ 1
    rw [LinearMap.smul_apply, ← map_smul]
    exact hl'.le
  obtain ⟨y, _, hy⟩ := hcl
  have hc₀ : c ≠ 0 := norm_pos_iff.mp (hc ▸ half_pos hε')
  refine ⟨c⁻¹ • y, ?_⟩
  change B.flip y = c • l at hy
  rw [map_smul, hy, inv_smul_smul₀ hc₀]

end Sol_LocallyConvexDuality_mackey_arens

open LocallyConvexDuality Sol_LocallyConvexDuality_mackey_arens

/-- **Mackey–Arens theorem.** -/
theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (hB : B.Nondegenerate)
    (t : TopologicalSpace E) (ht : PolynormableSpace 𝕜 E (topology := t)) :
    IsCompatibleTopology B t ↔
      mackeyTopology B ≤ t ∧ t ≤ (inferInstance : TopologicalSpace (WeakBilin B)) := by
  constructor
  · -- a compatible topology lies between the Mackey topology and the weak topology
    intro h
    refine ⟨@mackey_le_of_compatible 𝕜 E F _ _ _ _ _ B t ht h, ?_⟩
    exact continuous_id_iff_le.mp (WeakBilin.continuous_of_continuous_eval (B := B) fun y ↦
      (h (B.flip y)).mpr (Set.mem_range_self y))
  · -- a topology between the two has dual exactly `F`
    rintro ⟨hM, hw⟩ l
    constructor
    · intro hl
      exact mem_range_flip_of_mackeyContinuous B l
        (@Continuous.comp E E 𝕜 (mackeyTopology B) t _ id l hl (continuous_id_iff_le.mpr hM))
    · rintro ⟨y, rfl⟩
      exact @Continuous.comp E E 𝕜 t (WeakBilin.instTopologicalSpace B) _ id (B.flip y)
        (WeakBilin.eval_continuous B y) (continuous_id_iff_le.mpr hw)
