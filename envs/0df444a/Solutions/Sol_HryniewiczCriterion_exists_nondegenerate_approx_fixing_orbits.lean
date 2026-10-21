-- Prove2me | solution 1 for HryniewiczCriterion.exists_nondegenerate_approx_fixing_orbits
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T17:00:11.817758+00:00
-- url     : https://prove2.me/submissions/b04fdc4e-16d4-42fa-aeea-6def0cda0104
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Theorems.Thm_HryniewiczCriterion_exists_approx_nondegenerate_along_orbits
import Theorems.Thm_HryniewiczCriterion_exists_nondegenerate_approx_of_nondegenerate_along_orbits
import Theorems.Thm_IteratedFDeriv_exists_diagonal_tendstoUniformlyOn

open HryniewiczCriterion

namespace HryniewiczCriterion

/-- A periodic orbit of `H` lying where `H'` agrees with `H` to first order is a periodic
orbit of `H'`, with the same parametrization and period. -/
def PeriodicOrbit.liftOfJet {H H' : R4 → ℝ} (R : PeriodicOrbit H)
    (h : ∀ t, H' (R.x t) = H (R.x t) ∧ fderiv ℝ H' (R.x t) = fderiv ℝ H (R.x t)) :
    PeriodicOrbit H' where
  x := R.x
  T := R.T
  T_pos := R.T_pos
  trajectory := by
    refine ⟨fun t => ?_, fun t => by rw [(h t).1]; exact R.trajectory.2 t⟩
    have hX : hamiltonianVectorField H' (R.x t) = hamiltonianVectorField H (R.x t) := by
      unfold hamiltonianVectorField partialDeriv
      rw [(h t).2]
    rw [hX]
    exact R.trajectory.1 t
  periodic := R.periodic

theorem exists_nondegenerate_approx_fixing_orbits_aux (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P Q : PeriodicOrbit H) :
    ∃ Hs : ℕ → R4 → ℝ, (∀ k, IsStrictlyStarShapedLevel (Hs k)) ∧
      (∀ k (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0) ∧
      (∀ k, ∀ y ∈ P.image ∪ Q.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y) ∧
      (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H)
        Filter.atTop K) := by
  obtain ⟨H1, hS1, hnd1, hjet1, hconv1⟩ := exists_approx_nondegenerate_along_orbits H hS P Q
  have hB := fun k => exists_nondegenerate_approx_of_nondegenerate_along_orbits (H1 k) (hS1 k)
    (P.liftOfJet fun t => hjet1 k _ (Or.inl ⟨t, rfl⟩))
    (Q.liftOfJet fun t => hjet1 k _ (Or.inr ⟨t, rfl⟩)) (hnd1 k)
  choose H2 hS2 hnd2 hjet2 hconv2 using hB
  obtain ⟨φ, hφ⟩ := IteratedFDeriv.exists_diagonal_tendstoUniformlyOn H H1 H2 hconv1 hconv2
  refine ⟨fun k => H2 k (φ k), fun k => hS2 k (φ k), fun k => hnd2 k (φ k), fun k y hy => ?_, hφ⟩
  obtain ⟨a, b⟩ := hjet2 k (φ k) y hy
  obtain ⟨c, d⟩ := hjet1 k y hy
  exact ⟨a.trans c, b.trans d⟩

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P Q : PeriodicOrbit H) :
    ∃ Hs : ℕ → R4 → ℝ, (∀ k, IsStrictlyStarShapedLevel (Hs k)) ∧
      (∀ k (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0) ∧
      (∀ k, ∀ y ∈ P.image ∪ Q.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y) ∧
      (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K) :=
  exists_nondegenerate_approx_fixing_orbits_aux H hS P Q
