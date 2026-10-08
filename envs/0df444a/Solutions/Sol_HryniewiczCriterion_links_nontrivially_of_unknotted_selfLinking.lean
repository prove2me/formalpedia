-- Prove2me | solution 1 for HryniewiczCriterion.links_nontrivially_of_unknotted_selfLinking
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T09:51:05.379511+00:00
-- url     : https://prove2.me/submissions/26912a39-3c8e-4cfc-b94a-21327175c3f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Theorems.Thm_HryniewiczCriterion_exists_nondegenerate_approx_fixing_orbits
import Theorems.Thm_HryniewiczCriterion_bounds_global_section_of_nondegenerate_approx
import Theorems.Thm_HryniewiczCriterion_linksNontrivially_of_isDiskLikeGlobalSectionMap

open HryniewiczCriterion

namespace HryniewiczCriterion

/-- Two Hamiltonians with the same value and differential along a trajectory of the first
have that curve as a common trajectory. -/
theorem l312_isTrajectory_of_jet_eq {H H' : R4 → ℝ} {y : ℝ → R4} (hy : IsTrajectory H y)
    (hjet : ∀ t, H' (y t) = H (y t) ∧ fderiv ℝ H' (y t) = fderiv ℝ H (y t)) :
    IsTrajectory H' y := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hX : hamiltonianVectorField H' (y t) = hamiltonianVectorField H (y t) := by
      simp only [hamiltonianVectorField, partialDeriv, (hjet t).2]
    rw [hX]; exact hy.1 t
  · rw [(hjet t).1]; exact hy.2 t

/-- A periodic orbit of `H` is a periodic orbit of every `H'` with the same `1`-jet along it. -/
def l312_transfer {H : R4 → ℝ} (H' : R4 → ℝ) (P : PeriodicOrbit H)
    (hjet : ∀ y ∈ P.image, H' y = H y ∧ fderiv ℝ H' y = fderiv ℝ H y) : PeriodicOrbit H' where
  x := P.x
  T := P.T
  T_pos := P.T_pos
  trajectory := l312_isTrajectory_of_jet_eq P.trajectory fun t => hjet _ ⟨t, rfl⟩
  periodic := P.periodic

end HryniewiczCriterion

theorem solution (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (P : PeriodicOrbit H) (hP : P.IsPrime)
    (hu : IsUnknotted H P) (hsl : HasSelfLinkingNumber H P (-1))
    (Q : PeriodicOrbit H) (hQ : Q.image ≠ P.image) :
    LinksNontrivially P Q := by
  obtain ⟨Hs, hSk, hnd, hjet, hconv⟩ := exists_nondegenerate_approx_fixing_orbits H hS P Q
  have hjetP : ∀ k, ∀ y ∈ P.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y :=
    fun k y hy => hjet k y (Or.inl hy)
  have hjetQ : ∀ k, ∀ y ∈ Q.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y :=
    fun k y hy => hjet k y (Or.inr hy)
  obtain ⟨K, hK⟩ := bounds_global_section_of_nondegenerate_approx H hS hdc P hP hu hsl Hs hSk
    hnd hjetP hconv
  let PK := l312_transfer (Hs K) P (hjetP K)
  let QK := l312_transfer (Hs K) Q (hjetQ K)
  obtain ⟨e, he⟩ := hK K le_rfl PK rfl rfl
  exact linksNontrivially_of_isDiskLikeGlobalSectionMap (Hs K) (hSk K) PK QK e he hQ
