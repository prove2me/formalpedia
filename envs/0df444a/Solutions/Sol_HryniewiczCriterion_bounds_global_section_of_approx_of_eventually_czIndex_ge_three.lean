-- Prove2me | solution 1 for HryniewiczCriterion.bounds_global_section_of_approx_of_eventually_czIndex_ge_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T16:54:21.095782+00:00
-- url     : https://prove2.me/submissions/b3e2f466-a891-4ebe-940a-23d90a45a3ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HryniewiczCriterion_exists_transverse_disk_open_book_of_approx
import Theorems.Thm_HryniewiczCriterion_isDiskLikeGlobalSectionMap_of_transverse_open_book

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (P : PeriodicOrbit H) (hP : P.IsPrime) (hu : IsUnknotted H P)
    (hsl : HasSelfLinkingNumber H P (-1))
    (Hs : ℕ → R4 → ℝ) (hSk : ∀ k, IsStrictlyStarShapedLevel (Hs k))
    (hnd : (∀ k (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0))
    (hjet : ∀ k, ∀ y ∈ P.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y)
    (hconv : (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K))
    (hcz : ∀ A : ℝ, ∃ K : ℕ, ∀ k, K ≤ k → ∀ (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)),
      IsLinearizedFlow (Hs k) R.x Y → (∫ t in (0 : ℝ)..R.T, liouvilleForm (R.x t) (deriv R.x t)) ≤ A →
      3 ≤ czIndexOfPath (linearizedXiPath (Hs k) R Y)) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ Pk : PeriodicOrbit (Hs k), Pk.x = P.x → Pk.T = P.T →
      BoundsDiskLikeGlobalSection (Hs k) Pk := by
  obtain ⟨K₁, hK₁⟩ := exists_transverse_disk_open_book_of_approx H hS P hP hu hsl Hs hSk hnd hjet
    hconv hcz
  obtain ⟨K₂, hK₂⟩ := hcz (∫ t in (0 : ℝ)..P.T, liouvilleForm (P.x t) (deriv P.x t))
  refine ⟨max K₁ K₂, fun k hk Pk hx hT => ?_⟩
  obtain ⟨page, hob⟩ := hK₁ k (le_of_max_le_left hk) Pk hx hT
  have hczk : ∀ Y : ℝ → (R4 →L[ℝ] R4), IsLinearizedFlow (Hs k) Pk.x Y →
      3 ≤ czIndexOfPath (linearizedXiPath (Hs k) Pk Y) := fun Y hY =>
    hK₂ k (le_of_max_le_right hk) Pk Y hY (by rw [hx, hT])
  exact ⟨page 0, isDiskLikeGlobalSectionMap_of_transverse_open_book (Hs k) (hSk k) Pk hczk page
    hob 0⟩
