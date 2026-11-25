-- Prove2me | solution 1 for GlobalTheory.GradedBezout.exists_pos_nat_gradedQuotDeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:02:56.215038+00:00
-- url     : https://prove2.me/submissions/004da829-2f9e-4142-ae06-6c09f175cdf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_GradedBezout_exists_nat_gradedQuotDeg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module DirectSum
open GlobalTheory
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] (𝒜 : ℕ → Submodule K T)
open GlobalTheory.GradedBezout
variable [GradedAlgebra 𝒜]
variable {𝒜}
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin
namespace GlobalTheory.GradedBezout
theorem _root_.solution {P : Ideal T} [P.IsPrime] (hI : P.IsHomogeneous 𝒜)
    {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) :
    ∃ D : ℕ, 1 ≤ D ∧ gradedQuotDeg 𝒜 r P = D := by
  have hd := degree_hilbertPoly_eq_of_isPrime hx hfin hI hr
  obtain ⟨D, hD⟩ := exists_nat_gradedQuotDeg_eq hx hfin hI hd.le
  refine ⟨D, Nat.one_le_iff_ne_zero.2 ?_, hD⟩
  rintro rfl
  rw [gradedQuotDeg, Nat.cast_zero, mul_eq_zero] at hD
  exact hD.elim (by positivity) (coeff_ne_zero_of_eq_degree hd)
end GlobalTheory.GradedBezout
