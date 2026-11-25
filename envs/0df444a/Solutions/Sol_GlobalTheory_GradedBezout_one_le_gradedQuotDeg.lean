-- Prove2me | solution 1 for GlobalTheory.GradedBezout.one_le_gradedQuotDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:12:57.611145+00:00
-- url     : https://prove2.me/submissions/c867e641-decf-4e2c-8316-63fc42f38c45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_GradedBezout_exists_pos_nat_gradedQuotDeg_eq

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
    {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) : 1 ≤ gradedQuotDeg 𝒜 r P := by
  obtain ⟨D, h1, hD⟩ := exists_pos_nat_gradedQuotDeg_eq hx hfin hI hr
  rw [hD]
  exact_mod_cast h1
end GlobalTheory.GradedBezout
