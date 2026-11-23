-- Prove2me | solution 1 for NoHair.static_conformal_halves_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:18:58.811513+00:00
-- url     : https://prove2.me/submissions/bd0d1259-d4c9-44d7-a0a1-8d93f43db4d0

import Theorems.Thm_NoHair_static_conformal_halves_scalar_flat
import Theorems.Thm_NoHair_spatial_harmonic_strong_maximum_three
import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

open scoped Matrix

private abbrev X := ADMPoint
private abbrev I := Fin 3
private abbrev Mat := Matrix I I ℝ
private noncomputable abbrev pd := spatialADMPartial
private noncomputable abbrev bvec (i : I) : X := EuclideanSpace.single i 1

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∀ x ∈ closure Ω, 0 ≤ N x ∧ N x < 1 ∧ ∀ s : ℝ, s=1 ∨ s=-1 →
      let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := staticPositiveMetric (fun y => s*N y) h
      (k x).PosDef ∧ spatialScalarCurvature k x = 0 := by
  classical
  have sub : Ω ⊆ W := subset_closure.trans c.extendsAcross
  have pos (y : X) (hy : y∈Ω) : 0<N y := (c.positiveSide y (sub hy)).mp hy
  have bd (y : X) (hy : y∈closure Ω) (ny : y∉Ω) : N y=0 := by
    apply (c.regularLevel y _).1
    rw [c.openSlice.frontier_eq]
    exact ⟨hy,ny⟩
  have noMax (x : X) (hx : x∈Ω) (M : ∀ y ∈ Ω, N y≤N x) : False := by
    have eq : EqOn N (fun _ => N x) Ω :=
      spatial_harmonic_strong_maximum_three Ω N h c.openSlice (c.smoothLapse.mono sub)
        (fun i j => (c.smoothMetric i j).mono sub) (fun y hy => c.positiveMetric y (sub hy))
        c.connectedSlice (fun y hy => (c.equations y (subset_closure hy)).2) x hx M
    obtain ⟨b,hb⟩ := c.hasBoundary
    have q := eq.of_subset_closure (c.smoothLapse.continuousOn.mono c.extendsAcross)
      continuousOn_const subset_closure Subset.rfl (frontier_subset_closure hb)
    change N b = N x at q
    exact (pos x hx).ne' (q.symm.trans (c.regularLevel b hb).1)
  have weak (x : X) (hx : x∈Ω) : N x≤1 := by
    by_contra! hi
    obtain ⟨R,C,rp,cp,fall⟩ := c.falloff 0
    let B := max ‖x‖ (max R (C/(N x-1)))
    let K := closure Ω ∩ Metric.closedBall 0 B
    have kcomp : IsCompact K := (isCompact_closedBall (0:X) B).inter_left isClosed_closure
    have xK : x∈K := ⟨subset_closure hx,Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (le_max_left ‖x‖ (max R (C/(N x-1)))))⟩
    obtain ⟨y,hy,m⟩ := kcomp.exists_isMaxOn ⟨x,xK⟩ (c.smoothLapse.continuousOn.mono (fun t ht => c.extendsAcross ht.1))
    have n1 : 1<N y := hi.trans_le (m xK)
    have yo : y∈Ω := by by_contra ny; linarith only [bd y hy.1 ny,n1]
    apply noMax y yo
    intro z hz
    by_cases inside : ‖z‖≤B
    · exact m ⟨subset_closure hz,Metric.mem_closedBall.mpr (by rwa [dist_zero_right])⟩
    have hb : B<‖z‖ := lt_of_not_ge inside
    have rz := (max_lt_iff.mp (max_lt_iff.mp hb).2).1
    have cb := (max_lt_iff.mp (max_lt_iff.mp hb).2).2
    have err := (fall z rz).1
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] at err
    have d := sub_pos.mpr hi
    have r : 0<‖z‖ := rp.trans rz
    have small : C/‖z‖ ≤ N x-1 := (div_le_iff₀ r).mpr (by
      have t := (div_lt_iff₀ d).mp cb; linarith only [t])
    have val : N z ≤ N x := by linarith only [(abs_le.mp err).2,small]
    exact val.trans (m xK)
  intro x hx
  have range : 0 ≤ N x ∧ N x<1 := by
    by_cases hi : x∈Ω
    · refine ⟨(pos x hi).le,lt_of_le_of_ne (weak x hi) ?_⟩
      intro e
      exact noMax x hi (fun y hy => e ▸ weak y hy)
    · rw [bd x hx hi]
      norm_num
  refine ⟨range.1,range.2,?_⟩
  intro s hs
  have pp : 0<1+s*N x := by
    rcases hs with e|e <;> rw [e] <;> nlinarith only [range.1,range.2]
  exact ⟨(c.positiveMetric x (c.extendsAcross hx)).smul (pow_pos (half_pos pp) 4),
    (static_conformal_halves_scalar_flat Ω W N h c x hx).2 s pp.ne'⟩
