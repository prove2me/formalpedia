-- Prove2me | solution 1 for HunterPDE.Elliptic.fredholm_alternative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T14:03:13.367997+00:00
-- url     : https://prove2.me/submissions/452f879b-3e9b-45e3-bf23-3b5e00064d0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_EllipticOperator
import Theorems.Thm_HunterPDE_Elliptic_energy_estimates
import Theorems.Thm_HunterPDE_Elliptic_resolvent_compact

set_option autoImplicit false

open scoped InnerProductSpace
open ContinuousLinearMap

namespace FA92

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Schauder (Hilbert space): the adjoint of a compact operator is compact. -/
lemma adjoint_compact (K : H →L[ℝ] H) (hK : IsCompactOperator K) :
    IsCompactOperator (adjoint K) := by
  set L := adjoint K with hLdef
  have hKL : IsCompactOperator (K.comp L) := hK.comp_clm L
  obtain ⟨C, hC, hsub⟩ :=
    hKL.image_closedBall_subset_compact (f := ((K.comp L : H →L[ℝ] H) : H →ₗ[ℝ] H)) 1
  have hTB : TotallyBounded ((K.comp L) '' Metric.closedBall (0 : H) 1) :=
    hC.totallyBounded.subset hsub
  -- key inequality
  have hineq : ∀ z : H, ‖z‖ ≤ 2 → ‖L z‖ ^ 2 ≤ 2 * ‖K (L z)‖ := by
    intro z hz
    have h1 : ‖L z‖ ^ 2 = ⟪z, K (L z)⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq, hLdef, adjoint_inner_left]
    rw [h1]
    calc ⟪z, K (L z)⟫_ℝ ≤ ‖z‖ * ‖K (L z)‖ := real_inner_le_norm _ _
      _ ≤ 2 * ‖K (L z)‖ := by gcongr
  have hTB' : TotallyBounded (L '' Metric.closedBall (0 : H) 1) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨t, hts, htf, hcov⟩ :=
      Metric.finite_approx_of_totallyBounded hTB (ε ^ 2 / 2) (by positivity)
    have hpre : ∀ y ∈ t, ∃ x ∈ Metric.closedBall (0 : H) 1, (K.comp L) x = y := fun y hy => hts hy
    choose! g hgB hgy using hpre
    refine ⟨(fun y => L (g y)) '' t, htf.image _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcov ⟨x, hx, rfl⟩)
    refine Set.mem_iUnion₂.mpr ⟨L (g y), ⟨y, hy, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hxy ⊢
    have hgy' := hgy y hy
    have hxB : ‖x‖ ≤ 1 := by simpa using hx
    have hgB' : ‖g y‖ ≤ 1 := by simpa using hgB y hy
    have hz : ‖x - g y‖ ≤ 2 := by
      calc ‖x - g y‖ ≤ ‖x‖ + ‖g y‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    have h2 := hineq (x - g y) hz
    rw [map_sub, map_sub] at h2
    have h3 : K (L x) - K (L (g y)) = (K.comp L) x - y := by
      simp only [ContinuousLinearMap.comp_apply] at hgy' ⊢
      rw [hgy']
    rw [h3] at h2
    have h4 : ‖L x - L (g y)‖ ^ 2 < ε ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h4
  exact (isCompactOperator_iff_image_closedBall_subset_compact
    (f := ((L : H →L[ℝ] H) : H →ₗ[ℝ] H)) one_pos).mpr
    ⟨closure (L '' Metric.closedBall (0 : H) 1), TotallyBounded.isCompact_of_isClosed hTB'.closure isClosed_closure, subset_closure⟩

/-- The kernel of `T` is finite-dimensional when `1 - T` is compact. -/
lemma fd_ker (T : H →L[ℝ] H) (hT : IsCompactOperator ⇑(1 - T : H →L[ℝ] H)) :
    FiniteDimensional ℝ (LinearMap.ker (T : H →ₗ[ℝ] H)) := by
  obtain ⟨C, hC, hsub⟩ :=
    hT.image_closedBall_subset_compact (f := (((1 - T) : H →L[ℝ] H) : H →ₗ[ℝ] H)) 1
  refine FiniteDimensional.of_isCompact_closedBall₀ ℝ one_pos ?_
  rw [Subtype.isCompact_iff]
  have hcl : IsClosed (((↑) : LinearMap.ker (T : H →ₗ[ℝ] H) → H) '' Metric.closedBall 0 1) := by
    have : ((↑) : LinearMap.ker (T : H →ₗ[ℝ] H) → H) '' Metric.closedBall 0 1 =
        Metric.closedBall (0 : H) 1 ∩ (T ⁻¹' {0}) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨by simpa using hy, ?_⟩
        simpa using y.2
      · rintro ⟨hx, hx'⟩
        refine ⟨⟨x, by simpa using hx'⟩, by simpa using hx, rfl⟩
    rw [this]
    exact Metric.isClosed_closedBall.inter (isClosed_singleton.preimage T.continuous)
  refine hC.of_isClosed_subset hcl ?_
  rintro _ ⟨y, hy, rfl⟩
  apply hsub
  refine ⟨(y : H), by simpa using hy, ?_⟩
  have hy0 : T (y : H) = 0 := y.2
  show (1 - T) (y : H) = y
  simp [hy0]

lemma adjoint_one_sub (T : H →L[ℝ] H) : adjoint (1 - T) = 1 - adjoint T := by
  rw [map_sub, adjoint_one]

/-- The key step: an injective `A0 : ker T → ker T†` is surjective, and `(ker T†)ᗮ ≤ range T`. -/
lemma key (T : H →L[ℝ] H) (hT : IsCompactOperator ⇑(1 - T : H →L[ℝ] H))
    (N N' : Submodule ℝ H) (hN : ∀ x, x ∈ N ↔ T x = 0) (hN' : ∀ x, x ∈ N' ↔ adjoint T x = 0)
    [FiniteDimensional ℝ N] (A0 : N →ₗ[ℝ] N') (hA0 : Function.Injective A0) :
    Function.Surjective A0 ∧ N'ᗮ ≤ LinearMap.range (T : H →ₗ[ℝ] H) := by
  haveI : CompleteSpace N := FiniteDimensional.complete ℝ N
  let A0c : N →L[ℝ] H := LinearMap.toContinuousLinearMap (N'.subtype ∘ₗ A0)
  let A : H →L[ℝ] H := A0c.comp N.orthogonalProjectionOnto
  have hAx : ∀ x, A x = ((A0 (N.orthogonalProjectionOnto x) : N') : H) := fun x => rfl
  have hAmem : ∀ x, A x ∈ N' := fun x => by rw [hAx]; exact (A0 _).2
  have hA : IsCompactOperator A :=
    (isCompactOperator_of_locallyCompactSpace_rng A0c).comp_clm N.orthogonalProjectionOnto
  let K' : H →L[ℝ] H := (1 - T) - A
  have hK'c : IsCompactOperator K' := by
    have := hT.sub hA
    simpa [K'] using this
  -- range T is orthogonal to ker T†
  have horth : ∀ x, ∀ w ∈ N', ⟪w, T x⟫_ℝ = 0 := by
    intro x w hw
    rw [← adjoint_inner_left, (hN' w).mp hw, inner_zero_left]
  have hTA : ∀ x, x - K' x = T x + A x := by
    intro x
    simp only [K', ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    abel
  -- injectivity of T + A
  have hinj : ∀ x, T x + A x = 0 → x = 0 := by
    intro x hx
    have hTx : T x = -A x := eq_neg_of_add_eq_zero_left hx
    have h0 : ⟪T x, T x⟫_ℝ = 0 := by
      have e1 : ⟪T x, T x⟫_ℝ = ⟪-A x, T x⟫_ℝ := by rw [← hTx]
      rw [e1, inner_neg_left, horth x (A x) (hAmem x), neg_zero]
    have hT0 : T x = 0 := by simpa using h0
    have hAz : A x = 0 := by
      have := hx; rw [hT0, zero_add] at this; exact this
    have hP : N.orthogonalProjectionOnto x = 0 := by
      apply hA0
      rw [map_zero]
      apply Subtype.ext
      have := hAx x
      rw [hAz] at this
      rw [← this]; rfl
    have hxN : x ∈ N := (hN x).mpr hT0
    have := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := N) ⟨x, hxN⟩
    rw [hP] at this
    have := congrArg Subtype.val this
    simpa using this.symm
  -- surjectivity of T + A from the compact Fredholm alternative
  have hsurj : ∀ y, ∃ x, T x + A x = y := by
    rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet hK'c (one_ne_zero (α := ℝ))
      with hev | hres
    · exfalso
      obtain ⟨x, hx⟩ := hev.exists_hasEigenvector
      have hx1 := Module.End.mem_eigenspace_iff.mp hx.1
      have hx0 : x ≠ 0 := hx.2
      apply hx0
      apply hinj
      rw [← hTA]
      have : K' x = x := by simpa using hx1
      rw [this, sub_self]
    · rw [spectrum.mem_resolventSet_iff, ContinuousLinearMap.isUnit_iff_bijective] at hres
      intro y
      obtain ⟨x, hx⟩ := hres.2 y
      refine ⟨x, ?_⟩
      rw [← hTA]
      simpa using hx
  refine ⟨?_, ?_⟩
  · intro w
    obtain ⟨x, hx⟩ := hsurj (w : H)
    have hd : (w : H) - A x ∈ N' := N'.sub_mem w.2 (hAmem x)
    have hdT : (w : H) - A x = T x := by rw [← hx]; abel
    have h0 : ⟪(w : H) - A x, (w : H) - A x⟫_ℝ = 0 := by
      have := horth x _ hd
      rw [← hdT] at this
      exact this
    have h1 : (w : H) - A x = 0 := by simpa using h0
    refine ⟨N.orthogonalProjectionOnto x, ?_⟩
    apply Subtype.ext
    rw [← hAx]
    exact (sub_eq_zero.mp h1).symm
  · intro y hy
    obtain ⟨x, hx⟩ := hsurj y
    have hAx' : A x = y - T x := by rw [← hx]; abel
    have hTx : T x ∈ N'ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      exact horth x w hw
    have hyT : y - T x ∈ N'ᗮ := N'ᗮ.sub_mem hy hTx
    have h0 : ⟪A x, A x⟫_ℝ = 0 := by
      have := (Submodule.mem_orthogonal _ _).mp hyT _ (hAmem x)
      rw [← hAx'] at this
      exact this
    have h1 : A x = 0 := by simpa using h0
    refine ⟨x, ?_⟩
    rw [h1] at hAx'
    exact (sub_eq_zero.mp hAx'.symm).symm

/-- Riesz–Schauder: `T = 1 - (compact)` has finite-dimensional kernels of equal dimension,
and closed range `(ker T†)ᗮ`. -/
theorem index_zero (T : H →L[ℝ] H) (hT : IsCompactOperator ⇑(1 - T : H →L[ℝ] H)) :
    FiniteDimensional ℝ (LinearMap.ker (T : H →ₗ[ℝ] H)) ∧ FiniteDimensional ℝ (LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H)) ∧
      Module.finrank ℝ (LinearMap.ker (T : H →ₗ[ℝ] H)) = Module.finrank ℝ (LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H)) ∧
      LinearMap.range (T : H →ₗ[ℝ] H) = (LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H))ᗮ := by
  have hT' : IsCompactOperator ⇑(1 - adjoint T : H →L[ℝ] H) := by
    rw [← adjoint_one_sub]; exact adjoint_compact _ hT
  haveI h1 : FiniteDimensional ℝ (LinearMap.ker (T : H →ₗ[ℝ] H)) := fd_ker T hT
  haveI h2 : FiniteDimensional ℝ (LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H)) := fd_ker _ hT'
  have heq : Module.finrank ℝ (LinearMap.ker (T : H →ₗ[ℝ] H)) = Module.finrank ℝ (LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H)) := by
    rcases le_total (Module.finrank ℝ (LinearMap.ker (T : H →ₗ[ℝ] H)))
        (Module.finrank ℝ (LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H))) with hle | hle
    · obtain ⟨A0, hA0⟩ := finrank_le_iff_exists_linearMap.mp hle
      have hs := (key T hT _ _ (fun x => LinearMap.mem_ker) (fun x => LinearMap.mem_ker) A0 hA0).1
      have := LinearMap.finrank_range_le A0
      rw [LinearMap.range_eq_top.mpr hs, finrank_top] at this
      omega
    · have hle' : Module.finrank ℝ (LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H)) ≤
          Module.finrank ℝ (LinearMap.ker ((adjoint (adjoint T) : H →L[ℝ] H) : H →ₗ[ℝ] H)) := by
        rw [adjoint_adjoint]; exact hle
      haveI : FiniteDimensional ℝ (LinearMap.ker ((adjoint (adjoint T) : H →L[ℝ] H) : H →ₗ[ℝ] H)) := by
        rw [adjoint_adjoint]; exact h1
      obtain ⟨A0, hA0⟩ := finrank_le_iff_exists_linearMap.mp hle'
      have hs := (key (adjoint T) hT' _ _ (fun x => LinearMap.mem_ker) (fun x => LinearMap.mem_ker) A0 hA0).1
      have := LinearMap.finrank_range_le A0
      rw [LinearMap.range_eq_top.mpr hs, finrank_top] at this
      rw [adjoint_adjoint] at this
      omega
  refine ⟨h1, h2, heq, ?_⟩
  apply le_antisymm
  · rw [← ContinuousLinearMap.orthogonal_range]
    exact Submodule.le_orthogonal_orthogonal _
  · let e := LinearEquiv.ofFinrankEq (LinearMap.ker (T : H →ₗ[ℝ] H)) (LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H)) heq
    exact (key T hT _ _ (fun x => LinearMap.mem_ker) (fun x => LinearMap.mem_ker) e.toLinearMap e.injective).2

end FA92

namespace FB92

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lax–Milgram core. -/
lemma core (a : V →L[ℝ] V →L[ℝ] ℝ) (C : ℝ) (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ a u u)
    (f : StrongDual ℝ V) : ∃! u : V, ∀ φ, a u φ = f φ := by
  have coercive : IsCoercive a := ⟨C, hC, fun u => by
    have := hcoer u; nlinarith [this]⟩
  set E := coercive.continuousLinearEquivOfBilin with hE
  set w0 := (InnerProductSpace.toDual ℝ V).symm f with hw0
  have key : ∀ y : V, (∀ φ, a y φ = f φ) ↔ E y = w0 := by
    intro y
    constructor
    · intro h
      refine ext_inner_right ℝ fun φ => ?_
      rw [hE, IsCoercive.continuousLinearEquivOfBilin_apply, h, hw0,
        InnerProductSpace.toDual_symm_apply]
    · intro h φ
      rw [← IsCoercive.continuousLinearEquivOfBilin_apply coercive, ← hE, h, hw0,
        InnerProductSpace.toDual_symm_apply]
  refine ⟨E.symm w0, (key _).2 (E.apply_symm_apply w0), fun y hy => ?_⟩
  have := (key y).1 hy
  rw [← this, E.symm_apply_apply]

/-- The bilinear form `(u, v) ↦ ⟪J u, J v⟫`. -/
noncomputable def jj (J : V →L[ℝ] H) : V →L[ℝ] V →L[ℝ] ℝ := (innerSL ℝ).bilinearComp J J

lemma jj_apply (J : V →L[ℝ] H) (u v : V) : jj J u v = ⟪J u, J v⟫_ℝ := by
  simp [jj]

/-- The homogeneous solution space of `b(u, φ) - lam ⟪J u, J φ⟫ = 0`. -/
noncomputable def Sub0 (J : V →L[ℝ] H) (b : V →L[ℝ] V →L[ℝ] ℝ) (lam : ℝ) : Submodule ℝ V :=
  LinearMap.ker ((b + (-lam) • jj J : V →L[ℝ] V →L[ℝ] ℝ) : V →ₗ[ℝ] V →L[ℝ] ℝ)

lemma mem_Sub0 (J : V →L[ℝ] H) (b : V →L[ℝ] V →L[ℝ] ℝ) (lam : ℝ) (u : V) :
    u ∈ Sub0 J b lam ↔ ∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = 0 := by
  simp only [Sub0, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.ext_iff,
    ContinuousLinearMap.add_apply, smul_apply, jj_apply,
    ContinuousLinearMap.zero_apply, smul_eq_mul]

section
variable (J : V →L[ℝ] H) (b : V →L[ℝ] V →L[ℝ] ℝ) {γ C μ : ℝ}

lemma uniq (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ) (hμ : γ ≤ μ)
    (w : V) (hw : ∀ φ, b w φ + μ * ⟪J w, J φ⟫_ℝ = 0) : w = 0 := by
  have h1 := hcoer w
  have h2 := hw w
  have h3 : 0 ≤ ⟪J w, J w⟫_ℝ := real_inner_self_nonneg
  have h4 : C * ‖w‖ ^ 2 ≤ 0 := by nlinarith
  have h5 : ‖w‖ ^ 2 ≤ 0 := by
    by_contra h
    push_neg at h
    nlinarith
  have h6 : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
  exact norm_eq_zero.mp h6

lemma exist (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ) (hμ : γ ≤ μ)
    (g : H) : ∃ u, ∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ := by
  have hc : ∀ u, C * ‖u‖ ^ 2 ≤ (b + μ • jj J) u u := by
    intro u
    simp only [ContinuousLinearMap.add_apply, smul_apply, jj_apply,
      smul_eq_mul]
    nlinarith [hcoer u, real_inner_self_nonneg (x := J u)]
  obtain ⟨u, hu, -⟩ := core (b + μ • jj J) C hC hc ((innerSL ℝ g).comp J)
  refine ⟨u, fun φ => ?_⟩
  have := hu φ
  simpa only [ContinuousLinearMap.add_apply, smul_apply, jj_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, innerSL_apply_apply] using this

lemma corr (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ) (hμ : γ ≤ μ)
    (lam : ℝ) (K T : H →L[ℝ] H) (hT : T = 1 - (lam + μ) • K)
    (hK : ∀ g u, (∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ) → K g = J u) :
    (∃ e : Sub0 J b lam ≃ₗ[ℝ] LinearMap.ker (T : H →ₗ[ℝ] H), ∀ u, (e u : H) = J u) ∧
    ∀ f : H, (∃ u, ∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = ⟪f, J φ⟫_ℝ) ↔
      K f ∈ LinearMap.range (T : H →ₗ[ℝ] H) := by
  have hTapp : ∀ x, T x = x - (lam + μ) • K x := by
    intro x; rw [hT]; simp
  have hsolμ : ∀ u f, (∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = ⟪f, J φ⟫_ℝ) ↔
      (∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪f + (lam + μ) • J u, J φ⟫_ℝ) := by
    intro u f
    refine forall_congr' fun φ => ?_
    rw [inner_add_left, real_inner_smul_left]
    constructor <;> intro h <;> linarith
  have hmapsto : ∀ u ∈ Sub0 J b lam, J u ∈ LinearMap.ker (T : H →ₗ[ℝ] H) := by
    intro u hu
    rw [mem_Sub0] at hu
    have h1 : ∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪(lam + μ) • J u, J φ⟫_ℝ := by
      intro φ
      have := hu φ
      rw [real_inner_smul_left]
      linarith
    have hk := hK _ _ h1
    rw [map_smul] at hk
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hTapp, hk, sub_self]
  let Φ : Sub0 J b lam →ₗ[ℝ] LinearMap.ker (T : H →ₗ[ℝ] H) :=
    LinearMap.codRestrict _ ((J : V →ₗ[ℝ] H) ∘ₗ (Sub0 J b lam).subtype)
      (fun u => hmapsto u u.2)
  have hΦ : ∀ u, (Φ u : H) = J u := fun u => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hJu : J u = 0 := by
      have := congrArg Subtype.val hu
      rw [hΦ] at this
      simpa using this
    have hu2 := (mem_Sub0 J b lam u).mp u.2
    have : (u : V) = 0 := by
      apply uniq J b hC hcoer hμ
      intro φ
      have := hu2 φ
      rw [hJu, inner_zero_left] at this ⊢
      linarith
    exact Subtype.ext this
  have hsurj : Function.Surjective Φ := by
    rintro ⟨w, hw⟩
    have hw' : w - (lam + μ) • K w = 0 := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hTapp] at hw; exact hw
    obtain ⟨u, hu⟩ := exist J b hC hcoer hμ ((lam + μ) • w)
    have hk := hK _ _ hu
    rw [map_smul] at hk
    have hJu : J u = w := by
      rw [← hk]; exact (sub_eq_zero.mp hw').symm
    have hmem : u ∈ Sub0 J b lam := by
      rw [mem_Sub0]
      intro φ
      have := hu φ
      rw [real_inner_smul_left, ← hJu] at this
      linarith
    refine ⟨⟨u, hmem⟩, Subtype.ext ?_⟩
    rw [hΦ]; exact hJu
  refine ⟨⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun u => rfl⟩, fun f => ?_⟩
  constructor
  · rintro ⟨u, hu⟩
    have hk := hK _ _ ((hsolμ u f).mp hu)
    rw [map_add, map_smul] at hk
    refine ⟨J u, ?_⟩
    rw [ContinuousLinearMap.coe_coe, hTapp]
    exact (eq_sub_of_add_eq hk).symm
  · rintro ⟨w, hw⟩
    rw [ContinuousLinearMap.coe_coe, hTapp] at hw
    obtain ⟨u, hu⟩ := exist J b hC hcoer hμ (f + (lam + μ) • w)
    have hk := hK _ _ hu
    rw [map_add, map_smul, ← hw] at hk
    have hJu : J u = w := by rw [← hk]; abel
    refine ⟨u, (hsolμ u f).mpr fun φ => ?_⟩
    have := hu φ
    rw [← hJu] at this
    exact this

lemma adjK (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ) (hμ : γ ≤ μ)
    (K : H →L[ℝ] H)
    (hK : ∀ g u, (∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ) → K g = J u) :
    ∀ g v, (∀ φ, b.flip v φ + μ * ⟪J v, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ) → adjoint K g = J v := by
  intro g v hv
  apply ext_inner_right ℝ
  intro h
  rw [adjoint_inner_left]
  obtain ⟨u, hu⟩ := exist J b hC hcoer hμ h
  rw [hK h u hu]
  have h1 := hv u
  have h2 := hu v
  rw [ContinuousLinearMap.flip_apply] at h1
  rw [real_inner_comm (J v) (J u)] at h2
  rw [real_inner_comm h (J v)]
  linarith

lemma adjoint_T (K : H →L[ℝ] H) (s : ℝ) : adjoint (1 - s • K) = 1 - s • adjoint K := by
  rw [map_sub, adjoint_one, map_smulₛₗ]
  simp

lemma sol_sub (lam : ℝ) (f : H) (u1 u2 : V)
    (h1 : ∀ φ, b u1 φ + (-lam) * ⟪J u1, J φ⟫_ℝ = ⟪f, J φ⟫_ℝ)
    (h2 : ∀ φ, b u2 φ + (-lam) * ⟪J u2, J φ⟫_ℝ = ⟪f, J φ⟫_ℝ) : u1 - u2 ∈ Sub0 J b lam := by
  rw [mem_Sub0]
  intro φ
  rw [map_sub, ContinuousLinearMap.sub_apply, map_sub, inner_sub_left]
  linarith [h1 φ, h2 φ]

lemma sol_add (lam : ℝ) (f : H) (u s : V)
    (h1 : ∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = ⟪f, J φ⟫_ℝ) (hs : s ∈ Sub0 J b lam) :
    ∀ φ, b (u + s) φ + (-lam) * ⟪J (u + s), J φ⟫_ℝ = ⟪f, J φ⟫_ℝ := by
  rw [mem_Sub0] at hs
  intro φ
  rw [map_add, ContinuousLinearMap.add_apply, map_add, inner_add_left]
  linarith [h1 φ, hs φ]

/-- Abstract Fredholm alternative for a coercive form with compact resolvent. -/
theorem abstract (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ)
    (hμ : γ ≤ μ) (lam : ℝ) (hσ : 0 < lam + μ) (K : H →L[ℝ] H) (hKc : IsCompactOperator K)
    (hK : ∀ g u, (∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ) → K g = J u) :
    ((∀ v, v ∈ Sub0 J b.flip lam → v = 0) ∧
      (∀ f : H, ∃! u, ∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = ⟪f, J φ⟫_ℝ) ∧
      (∀ u, u ∈ Sub0 J b lam → u = 0)) ∨
    ((∃ v, v ≠ 0 ∧ v ∈ Sub0 J b.flip lam) ∧
      FiniteDimensional ℝ (Sub0 J b lam) ∧ FiniteDimensional ℝ (Sub0 J b.flip lam) ∧
      Module.finrank ℝ (Sub0 J b lam) = Module.finrank ℝ (Sub0 J b.flip lam) ∧
      ∀ f : H, ((∃ u, ∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = ⟪f, J φ⟫_ℝ) ↔
          ∀ v, v ∈ Sub0 J b.flip lam → ⟪f, J v⟫_ℝ = 0) ∧
        ∀ u, (∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = ⟪f, J φ⟫_ℝ) →
          ∃ u', u' ≠ u ∧ ∀ φ, b u' φ + (-lam) * ⟪J u', J φ⟫_ℝ = ⟪f, J φ⟫_ℝ) := by
  set T : H →L[ℝ] H := 1 - (lam + μ) • K with hTdef
  have hTc : IsCompactOperator ⇑(1 - T : H →L[ℝ] H) := by
    have : (1 - T : H →L[ℝ] H) = (lam + μ) • K := by rw [hTdef]; abel
    rw [this]
    simpa using hKc.smul (lam + μ)
  obtain ⟨hfd1, hfd2, hrk, hran⟩ := FA92.index_zero T hTc
  obtain ⟨⟨e1, he1⟩, hran1⟩ := corr J b hC hcoer hμ lam K T hTdef hK
  have hcoerF : ∀ u, C * ‖u‖ ^ 2 ≤ b.flip u u + γ * ⟪J u, J u⟫_ℝ := by
    intro u; rw [ContinuousLinearMap.flip_apply]; exact hcoer u
  have hKA := adjK J b hC hcoer hμ K hK
  have hTadj : adjoint T = 1 - (lam + μ) • adjoint K := by rw [hTdef]; exact adjoint_T K _
  obtain ⟨⟨e2, he2⟩, -⟩ := corr J b.flip hC hcoerF hμ lam (adjoint K) (adjoint T) hTadj hKA
  have hσ0 : lam + μ ≠ 0 := hσ.ne'
  have hJsub0 : ∀ u (hu : u ∈ Sub0 J b lam), (e1 ⟨u, hu⟩ : H) = J u := fun u hu => he1 ⟨u, hu⟩
  -- zero transport
  have hzero1 : ∀ x : Sub0 J b lam, (e1 x : H) = 0 → (x : V) = 0 := by
    intro x hx
    have : e1 x = 0 := Subtype.ext hx
    rw [LinearEquiv.map_eq_zero_iff] at this
    rw [this]; rfl
  have hzero2 : ∀ x : Sub0 J b.flip lam, (e2 x : H) = 0 → (x : V) = 0 := by
    intro x hx
    have : e2 x = 0 := Subtype.ext hx
    rw [LinearEquiv.map_eq_zero_iff] at this
    rw [this]; rfl
  haveI : FiniteDimensional ℝ (Sub0 J b lam) := LinearEquiv.finiteDimensional e1.symm
  haveI : FiniteDimensional ℝ (Sub0 J b.flip lam) := LinearEquiv.finiteDimensional e2.symm
  have hrk' : Module.finrank ℝ (Sub0 J b lam) = Module.finrank ℝ (Sub0 J b.flip lam) :=
    e1.finrank_eq.trans (hrk.trans e2.finrank_eq.symm)
  by_cases hk : LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H) = ⊥
  · left
    have hk1 : LinearMap.ker (T : H →ₗ[ℝ] H) = ⊥ := by
      rw [← Submodule.finrank_eq_zero, hrk, hk, finrank_bot]
    have hkA : ∀ x, x ∈ LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H) → x = 0 := by
      intro x hx; rw [hk, Submodule.mem_bot] at hx; exact hx
    have hkT : ∀ x, x ∈ LinearMap.ker (T : H →ₗ[ℝ] H) → x = 0 := by
      intro x hx; rw [hk1, Submodule.mem_bot] at hx; exact hx
    refine ⟨fun v hv => ?_, fun f => ?_, fun u hu => ?_⟩
    · exact hzero2 ⟨v, hv⟩ (hkA _ (e2 ⟨v, hv⟩).2)
    · have hex : K f ∈ LinearMap.range (T : H →ₗ[ℝ] H) := by
        rw [hran, hk, Submodule.bot_orthogonal_eq_top]; trivial
      obtain ⟨u, hu⟩ := (hran1 f).mpr hex
      refine ⟨u, hu, fun u2 hu2 => ?_⟩
      have hm := sol_sub J b lam f u2 u hu2 hu
      exact sub_eq_zero.mp (hzero1 ⟨_, hm⟩ (hkT _ (e1 ⟨_, hm⟩).2))
    · exact hzero1 ⟨u, hu⟩ (hkT _ (e1 ⟨u, hu⟩).2)
  · right
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    refine ⟨⟨(e2.symm ⟨w, hw⟩ : V), fun h0 => hw0 ?_, (e2.symm ⟨w, hw⟩).2⟩,
      inferInstance, inferInstance, hrk', fun f => ⟨?_, ?_⟩⟩
    · have : e2.symm ⟨w, hw⟩ = 0 := Subtype.ext h0
      rw [LinearEquiv.map_eq_zero_iff] at this
      exact congrArg Subtype.val this
    · -- range criterion
      have hadjw : ∀ w ∈ LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H),
          (⟪w, K f⟫_ℝ = 0 ↔ ⟪w, f⟫_ℝ = 0) := by
        intro w hw
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hTadj] at hw
        have hw' : w = (lam + μ) • adjoint K w := by
          simpa [sub_eq_zero] using hw
        have : ⟪w, K f⟫_ℝ = (lam + μ)⁻¹ * ⟪w, f⟫_ℝ := by
          rw [← adjoint_inner_left]
          conv_rhs => rw [hw']
          rw [real_inner_smul_left, ← mul_assoc, inv_mul_cancel₀ hσ0, one_mul]
        rw [this]
        constructor
        · intro h
          rcases mul_eq_zero.mp h with h | h
          · exact absurd h (inv_ne_zero hσ0)
          · exact h
        · intro h; rw [h, mul_zero]
      rw [hran1 f, hran, Submodule.mem_orthogonal]
      constructor
      · intro h v hv
        have hm := (e2 ⟨v, hv⟩).2
        have := (hadjw _ hm).mp (h _ hm)
        rw [he2] at this
        rw [real_inner_comm]; exact this
      · intro h w hw
        rw [hadjw w hw]
        have := h _ (e2.symm ⟨w, hw⟩).2
        have he : J (e2.symm ⟨w, hw⟩ : V) = w := by
          rw [← he2, LinearEquiv.apply_symm_apply]
        rw [he] at this
        rw [real_inner_comm]; exact this
    · intro u hu
      have hne : Sub0 J b lam ≠ ⊥ := by
        intro hbot
        have h1 : Module.finrank ℝ (Sub0 J b.flip lam) = 0 := by
          rw [← hrk', hbot, finrank_bot]
        have h2 : Module.finrank ℝ (LinearMap.ker ((adjoint T : H →L[ℝ] H) : H →ₗ[ℝ] H)) = 0 := by
          rw [← e2.finrank_eq, h1]
        exact hk (Submodule.finrank_eq_zero.mp h2)
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      refine ⟨u + s, fun h => hs0 ?_, sol_add J b lam f u s hu hs⟩
      have := congrArg (· - u) h
      simpa using this

end

end FB92

open MeasureTheory

namespace HunterPDE.Elliptic.PDE92

open HunterPDE.Elliptic

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- Pointwise integrand of `form`. -/
noncomputable def Gf (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p q : Jet n) : ℝ :=
  ((∑ i, ∑ j, P.a i j x * (WithLp.ofLp p).2 i * (WithLp.ofLp q).2 j)
    - (∑ i, P.b i x * (WithLp.ofLp p).1 * (WithLp.ofLp q).2 i))
    + P.c x * (WithLp.ofLp p).1 * (WithLp.ofLp q).1

lemma form_eq (P : Coeffs n) (u v : H10 n Ω) :
    form P u v = ∫ x in Ω, Gf P x ((u : JetL2 n Ω) x) ((v : JetL2 n Ω) x) := rfl

lemma Gf_add_left (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p p' q : Jet n) :
    Gf P x (p + p') q = Gf P x p q + Gf P x p' q := by
  simp only [Gf, WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
  simp only [mul_add, Finset.sum_add_distrib, add_mul]
  ring

lemma Gf_add_right (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p q q' : Jet n) :
    Gf P x p (q + q') = Gf P x p q + Gf P x p q' := by
  simp only [Gf, WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

lemma Gf_smul_left (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (p q : Jet n) :
    Gf P x (c • p) q = c * Gf P x p q := by
  simp only [Gf, WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
  rw [mul_add, mul_sub]
  congr 1
  · congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  · ring

lemma Gf_smul_right (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (p q : Jet n) :
    Gf P x p (c • q) = c * Gf P x p q := by
  simp only [Gf, WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
  rw [mul_add, mul_sub]
  congr 1
  · congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  · ring

lemma memLp_fst (U : JetL2 n Ω) :
    MemLp (fun x => (WithLp.ofLp (U x)).1) 2 (volume.restrict Ω) :=
  ContinuousLinearMap.comp_memLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))) U

lemma memLp_snd (U : JetL2 n Ω) (i : Fin n) :
    MemLp (fun x => (WithLp.ofLp (U x)).2 i) 2 (volume.restrict Ω) :=
  ContinuousLinearMap.comp_memLp
    ((EuclideanSpace.proj i).comp (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))) U

lemma int3 {f g h : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f ⊤ (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) (hh : MemLp h 2 (volume.restrict Ω)) :
    Integrable (fun x => f x * g x * h x) (volume.restrict Ω) := by
  have h1 : Integrable (g * h) (volume.restrict Ω) := hg.integrable_mul hh
  have h2 := h1.mul_of_top_right hf
  refine h2.congr (ae_of_all _ fun x => ?_)
  simp [mul_assoc]

lemma Gf_integrable (P : Coeffs n) (hP : P.Admissible Ω) (U V : JetL2 n Ω) :
    Integrable (fun x => Gf P x (U x) (V x)) (volume.restrict Ω) := by
  unfold Gf
  refine Integrable.add (Integrable.sub ?_ ?_) ?_
  · refine integrable_finsetSum _ fun i _ => ?_
    refine integrable_finsetSum _ fun j _ => ?_
    exact int3 (hP.1 i j) (memLp_snd U i) (memLp_snd V j)
  · refine integrable_finsetSum _ fun i _ => ?_
    exact int3 (hP.2.1 i) (memLp_fst U) (memLp_snd V i)
  · exact int3 hP.2.2.1 (memLp_fst U) (memLp_fst V)

lemma form_add_left (P : Coeffs n) (hP : P.Admissible Ω) (u u' v : H10 n Ω) :
    form P (u + u') v = form P u v + form P u' v := by
  rw [form_eq, form_eq, form_eq, Submodule.coe_add,
    ← integral_add (Gf_integrable P hP _ _) (Gf_integrable P hP _ _)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (u : JetL2 n Ω) (u' : JetL2 n Ω)] with x hx
  rw [hx, Pi.add_apply, Gf_add_left]

lemma form_add_right (P : Coeffs n) (hP : P.Admissible Ω) (u v v' : H10 n Ω) :
    form P u (v + v') = form P u v + form P u v' := by
  rw [form_eq, form_eq, form_eq, Submodule.coe_add,
    ← integral_add (Gf_integrable P hP _ _) (Gf_integrable P hP _ _)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (v : JetL2 n Ω) (v' : JetL2 n Ω)] with x hx
  rw [hx, Pi.add_apply, Gf_add_right]

lemma form_smul_left (P : Coeffs n) (c : ℝ) (u v : H10 n Ω) :
    form P (c • u) v = c * form P u v := by
  rw [form_eq, form_eq, Submodule.coe_smul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c (u : JetL2 n Ω)] with x hx
  rw [hx, Pi.smul_apply, Gf_smul_left]

lemma form_smul_right (P : Coeffs n) (c : ℝ) (u v : H10 n Ω) :
    form P u (c • v) = c * form P u v := by
  rw [form_eq, form_eq, Submodule.coe_smul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c (v : JetL2 n Ω)] with x hx
  rw [hx, Pi.smul_apply, Gf_smul_right]

/-- The inclusion into `L²(Ω)` as a continuous linear map. -/
noncomputable def T (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    H10 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)).comp
    (H10 n Ω).subtypeL

lemma l2inner_eq (u v : H10 n Ω) : l2inner u v = inner ℝ (T n Ω u) (T n Ω v) := by
  rw [L2.inner_def]
  unfold l2inner
  refine integral_congr_ae ?_
  have hu := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
    (u : JetL2 n Ω)
  have hv := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
    (v : JetL2 n Ω)
  filter_upwards [hu, hv] with x hx hy
  change val u x * val v x = inner ℝ
    ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp (u : JetL2 n Ω) x)
    ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp (v : JetL2 n Ω) x)
  rw [hx, hy]
  simp [val, mul_comm]


end HunterPDE.Elliptic.PDE92


namespace HunterPDE.Elliptic.PDE92

open HunterPDE.Elliptic

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma toL2_eq (u : H10 n Ω) : toL2 u = T n Ω u := rfl

lemma l2pairing_eq (f : Lp ℝ 2 (volume.restrict Ω)) (φ : H10 n Ω) :
    l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ) φ = ⟪f, T n Ω φ⟫_ℝ := by
  rw [L2.inner_def]
  unfold l2pairing
  refine integral_congr_ae ?_
  have hv := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
    (φ : JetL2 n Ω)
  filter_upwards [hv] with x hy
  change f x * val φ x = inner ℝ (f x)
    ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp (φ : JetL2 n Ω) x)
  rw [hy]
  simp [val, mul_comm]

lemma formAdj_eq (P : Coeffs n) (hP : P.Admissible Ω) (u v : H10 n Ω) :
    formAdj P u v = form P v u := by
  have hsym : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j, P.a i j x = P.a j i x := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact hP.2.2.2 i j
  unfold formAdj form
  refine integral_congr_ae ?_
  filter_upwards [hsym] with x hx
  have h1 : (∑ i, ∑ j, P.a i j x * pd u i x * pd v j x) =
      ∑ i, ∑ j, P.a i j x * pd v i x * pd u j x := by
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hx i j]; ring
  have h2 : (∑ i, P.b i x * pd u i x * val v x) = ∑ i, P.b i x * val v x * pd u i x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, h2]
  ring

/-- The bounded bilinear form `form P` as a continuous bilinear map. -/
noncomputable def bF (P : Coeffs n) (hP : P.Admissible Ω) (C₂ : ℝ)
    (hbd : ∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖) :
    H10 n Ω →L[ℝ] H10 n Ω →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (fun u v => form P u v)
      (fun u u' v => form_add_left P hP u u' v)
      (fun c u v => by rw [form_smul_left P]; rfl)
      (fun u v v' => form_add_right P hP u v v')
      (fun c u v => by rw [form_smul_right P]; rfl)).mkContinuous₂ C₂
    (fun u v => by
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs]
      exact hbd u v)

lemma bF_apply (P : Coeffs n) (hP : P.Admissible Ω) (C₂ : ℝ)
    (hbd : ∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖) (u v : H10 n Ω) :
    bF P hP C₂ hbd u v = form P u v := rfl

lemma c_lower (P : Coeffs n) (hP : P.Admissible Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), -(eLpNorm P.c ⊤ (volume.restrict Ω)).toReal ≤ P.c x := by
  have hlt : eLpNorm P.c ⊤ (volume.restrict Ω) ≠ ⊤ := hP.2.2.1.2.ne
  rw [eLpNorm_exponent_top] at hlt ⊢
  filter_upwards [ae_le_eLpNormEssSup (f := P.c) (μ := volume.restrict Ω)] with x hx
  have h1 : ‖P.c x‖ ≤ (eLpNormEssSup P.c (volume.restrict Ω)).toReal := by
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono hlt hx
  rw [Real.norm_eq_abs] at h1
  have := neg_abs_le (P.c x)
  linarith

end HunterPDE.Elliptic.PDE92

open HunterPDE.Elliptic in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (P : Coeffs n) (hP : P.Admissible Ω)
    (hell : P.UniformlyElliptic Ω) (lam : ℝ) :
    ((∀ v : H10 n Ω, IsWeakSolution (formAdj P) (-lam) (fun _ => 0) v → v = 0) ∧
      (∀ f : Lp ℝ 2 (volume.restrict Ω),
        ∃! u : H10 n Ω, IsWeakSolution (form P) (-lam) (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u) ∧
      (∀ u : H10 n Ω, IsWeakSolution (form P) (-lam) (fun _ => 0) u → u = 0)) ∨
    ((∃ v : H10 n Ω, v ≠ 0 ∧ IsWeakSolution (formAdj P) (-lam) (fun _ => 0) v) ∧
      FiniteDimensional ℝ (solutionSpace (Ω := Ω) (form P) (-lam)) ∧
      FiniteDimensional ℝ (solutionSpace (Ω := Ω) (formAdj P) (-lam)) ∧
      Module.finrank ℝ (solutionSpace (Ω := Ω) (form P) (-lam)) =
        Module.finrank ℝ (solutionSpace (Ω := Ω) (formAdj P) (-lam)) ∧
      ∀ f : Lp ℝ 2 (volume.restrict Ω),
        ((∃ u : H10 n Ω, IsWeakSolution (form P) (-lam) (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u) ↔
          ∀ v : H10 n Ω, IsWeakSolution (formAdj P) (-lam) (fun _ => 0) v →
            l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ) v = 0) ∧
        ∀ u : H10 n Ω, IsWeakSolution (form P) (-lam) (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u →
          ∃ u' : H10 n Ω, u' ≠ u ∧
            IsWeakSolution (form P) (-lam) (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u') := by
  haveI : CompleteSpace (H10 n Ω) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨θ, hθ⟩ := hell
  obtain ⟨C₁, hC₁, C₂, hC₂, hbd, hco⟩ := energy_estimates Ω hΩ P hP θ hθ
  have hco' := hco _ (PDE92.c_lower P hP)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, ∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u + γ * l2inner u u := by
    by_cases hb : ∀ i, P.b i =ᵐ[volume.restrict Ω] 0
    · exact ⟨_, hco'.1 hb⟩
    · exact ⟨_, hco'.2 hb⟩
  set μ : ℝ := max γ (1 - lam) with hμdef
  have hμ : γ ≤ μ := le_max_left _ _
  have hσ : 0 < lam + μ := by
    have : 1 - lam ≤ μ := le_max_right _ _
    linarith
  obtain ⟨K, hKeq, -, hKc⟩ :=
    resolvent_compact Ω hΩ P hP γ ⟨C₁, hC₁, C₂, hC₂, hγ, hbd⟩ μ hμ
  set J := PDE92.T n Ω with hJ
  set b := PDE92.bF P hP C₂ hbd with hb
  have hbapp : ∀ u v, b u v = form P u v := fun u v => rfl
  have hcoer : ∀ u, C₁ * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ := by
    intro u; rw [hbapp, ← PDE92.l2inner_eq]; exact hγ u
  have hK : ∀ g u, (∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ) → K g = J u := by
    intro g u hu
    have hws : IsWeakSolution (form P) μ (l2pairing (g : EuclideanSpace ℝ (Fin n) → ℝ)) u := by
      intro φ
      rw [PDE92.l2inner_eq, PDE92.l2pairing_eq, ← hbapp]
      exact hu φ
    have hex : ∃ u : H10 n Ω,
        IsWeakSolution (form P) μ (l2pairing (g : EuclideanSpace ℝ (Fin n) → ℝ)) u := ⟨u, hws⟩
    rw [hKeq]
    unfold HunterPDE.Elliptic.resolvent
    rw [dif_pos hex]
    have hc := hex.choose_spec
    have heq : hex.choose = u := by
      have := FB92.uniq J b hC₁ hcoer hμ (hex.choose - u) (fun φ => by
        have h1 := hc φ
        have h2 := hws φ
        rw [PDE92.l2inner_eq] at h1 h2
        rw [map_sub, ContinuousLinearMap.sub_apply, map_sub, inner_sub_left, hbapp, hbapp]
        linarith)
      exact sub_eq_zero.mp this
    rw [heq]
    rfl
  have hA := FB92.abstract J b hC₁ hcoer hμ lam hσ K (hKc hΩb) hK
  -- dictionary
  have hW : ∀ (F : H10 n Ω → ℝ) u, IsWeakSolution (form P) (-lam) F u ↔
      ∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = F φ := by
    intro F u
    refine forall_congr' fun φ => ?_
    rw [hbapp, PDE92.l2inner_eq]
  have hWA : ∀ (F : H10 n Ω → ℝ) u, IsWeakSolution (formAdj P) (-lam) F u ↔
      ∀ φ, b.flip u φ + (-lam) * ⟪J u, J φ⟫_ℝ = F φ := by
    intro F u
    refine forall_congr' fun φ => ?_
    rw [ContinuousLinearMap.flip_apply, hbapp, PDE92.l2inner_eq, PDE92.formAdj_eq P hP]
  have hS0 : ∀ u, IsWeakSolution (form P) (-lam) (fun _ => 0) u ↔ u ∈ FB92.Sub0 J b lam := by
    intro u; rw [hW, FB92.mem_Sub0]
  have hS0A : ∀ u, IsWeakSolution (formAdj P) (-lam) (fun _ => 0) u ↔
      u ∈ FB92.Sub0 J b.flip lam := by
    intro u; rw [hWA, FB92.mem_Sub0]
  have hSS : solutionSpace (Ω := Ω) (form P) (-lam) = FB92.Sub0 J b lam := by
    unfold solutionSpace
    have : {u : H10 n Ω | IsWeakSolution (form P) (-lam) (fun _ => 0) u} =
        (FB92.Sub0 J b lam : Set (H10 n Ω)) := by
      ext u; exact hS0 u
    rw [this, Submodule.span_eq]
  have hSSA : solutionSpace (Ω := Ω) (formAdj P) (-lam) = FB92.Sub0 J b.flip lam := by
    unfold solutionSpace
    have : {u : H10 n Ω | IsWeakSolution (formAdj P) (-lam) (fun _ => 0) u} =
        (FB92.Sub0 J b.flip lam : Set (H10 n Ω)) := by
      ext u; exact hS0A u
    rw [this, Submodule.span_eq]
  have hWf : ∀ (f : Lp ℝ 2 (volume.restrict Ω)) u,
      IsWeakSolution (form P) (-lam) (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u ↔
      ∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = ⟪f, J φ⟫_ℝ := by
    intro f u
    rw [hW]
    refine forall_congr' fun φ => ?_
    rw [PDE92.l2pairing_eq]
  rw [hSS, hSSA]
  simp only [hS0, hS0A, hWf, PDE92.l2pairing_eq]
  exact hA
