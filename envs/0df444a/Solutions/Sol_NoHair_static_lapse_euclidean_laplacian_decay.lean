-- Prove2me | solution 1 for NoHair.static_lapse_euclidean_laplacian_decay
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:27:07.049596+00:00
-- url     : https://prove2.me/submissions/1583b810-81da-4b28-a4db-ae39b7abfb80

import Theorems.Thm_NoHair_asymptotic_static_cartesian_ricci_expansion
import Theorems.Thm_NoHair_static_block_ricci_hessian_identities
import Mathlib.Analysis.InnerProductSpace.Laplacian
open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology
private abbrev X := ADMPoint
private lemma flat_trace (u : X → ℝ) {x : X} (cu : ContDiffAt ℝ ∞ u x) :
    (Δ u) x=flatLapseLaplacian u x := by
  have hcd := (cu.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  let e : X := EuclideanSpace.single i 1
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,EuclideanSpace.basisFun_apply]
  change fderiv ℝ (fderiv ℝ u) x e e=fderiv ℝ (fun y => fderiv ℝ u y e) x e
  rw [fderiv_clm_apply hcd (differentiableAt_const e)]
  simp

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |(Δ N) z| ≤ C/‖z‖^4 := by
  obtain ⟨B,hB,hcomp⟩:=c.compactComplement.isBounded.exists_pos_norm_lt
  have inside {x : X} (hx : B<‖x‖) : x∈Ω := by
    by_contra hn
    exact (not_lt_of_ge hx.le) (hcomp x hn)
  have sm {x : X} (hx : B<‖x‖) := c.openExtension.mem_nhds (c.extendsAcross (subset_closure (inside hx)))
  have cn {x : X} (hx : B<‖x‖) := c.smoothLapse.contDiffAt (sm hx)
  obtain ⟨R,C,hR,hC,herr⟩:=asymptotic_static_cartesian_ricci_expansion N h
    ⟨B,fun x hx => ⟨cn hx,fun i j => (c.smoothMetric i j).contDiffAt (sm hx),
      fun i j => by simpa only [star_trivial] using
        (c.positiveMetric x (c.extendsAcross (subset_closure (inside hx)))).isHermitian.apply j i⟩⟩
    (fun k _ => c.falloff k)
  refine ⟨max R B,C,hR.trans_le (le_max_left _ _),hC,?_⟩
  intro x hx
  obtain ⟨hr,hb⟩:=max_lt_iff.mp hx
  have ho:=inside hb
  have hw:=c.extendsAcross (subset_closure ho)
  have nz:= ((c.positiveSide x hw).mp ho).ne'
  have er:=(static_block_ricci_hessian_identities N h W c.openExtension c.smoothLapse c.smoothMetric
    c.positiveMetric x hw nz).1
  rw [(c.equations x (subset_closure ho)).2,mul_zero] at er
  have d:=(herr x hr).1
  rw [er,zero_sub,abs_neg,←flat_trace N (cn hb)] at d
  exact d
