-- Prove2me | solution 1 for HryniewiczCriterion.bounds_global_section_of_nondegenerate_approx
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T16:35:29.593562+00:00
-- url     : https://prove2.me/submissions/6d72f121-9718-420e-bda1-0f5d95e3a70e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Theorems.Thm_HryniewiczCriterion_czIndex_ge_three_of_bounded_action_approx
import Theorems.Thm_HryniewiczCriterion_bounds_global_section_of_approx_of_eventually_czIndex_ge_three

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (P : PeriodicOrbit H) (hP : P.IsPrime) (hu : IsUnknotted H P)
    (hsl : HasSelfLinkingNumber H P (-1))
    (Hs : ℕ → R4 → ℝ) (hSk : ∀ k, IsStrictlyStarShapedLevel (Hs k))
    (hnd : (∀ k (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0))
    (hjet : ∀ k, ∀ y ∈ P.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y)
    (hconv : (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K)) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ Pk : PeriodicOrbit (Hs k), Pk.x = P.x → Pk.T = P.T →
      BoundsDiskLikeGlobalSection (Hs k) Pk :=
  bounds_global_section_of_approx_of_eventually_czIndex_ge_three H hS P hP hu hsl Hs hSk hnd hjet
    hconv (czIndex_ge_three_of_bounded_action_approx H hS hdc Hs hSk hconv)
