-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.finite_monic_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:44.03881+00:00
-- url     : https://prove2.me/submissions/df0244b1-e4fb-482c-aaf0-d32048d03cd0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
universe u
variable {F : Type u} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {f : F[X]} (hf : f ≠ 0) : {g : F[X] | g.Monic ∧ g ∣ f}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := UniqueFactorizationMonoid.normalizedFactors) ?_ ?_
  · refine (UniqueFactorizationMonoid.normalizedFactors f).powerset.toFinset.finite_toSet.subset ?_
    rintro _ ⟨g, ⟨hgm, hgf⟩, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_powerset]
    exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      hgm.ne_zero hf).1 hgf
  · rintro g₁ ⟨hg₁, -⟩ g₂ ⟨hg₂, -⟩ h
    refine eq_of_monic_of_associated hg₁ hg₂ ?_
    have a₁ := UniqueFactorizationMonoid.prod_normalizedFactors hg₁.ne_zero
    have a₂ := UniqueFactorizationMonoid.prod_normalizedFactors hg₂.ne_zero
    rw [h] at a₁
    exact a₁.symm.trans a₂
end GroundTheory.Automorphic.ContragredientTranspose
