-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.hilbertFun_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:27.657799+00:00
-- url     : https://prove2.me/submissions/2f73bf46-49e0-4d70-9f69-dd13229e6c9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_finrank_sup_add_finrank_colonX
import Theorems.Thm_GlobalTheory_MultiHilbert_finite_colourPiece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
namespace GlobalTheory.MultiHilbert
theorem _root_.solution {K σ : Type} [Field K] [Finite σ] {r : ℕ} (col : σ → Fin r)
    {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n : Fin r → ℕ, weightedHomogeneousComponent
      (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n F ∈ I) (i : σ) (n : Fin r → ℕ) :
    hilbertFun col I (n + Pi.single (col i) 1) =
      hilbertFun col (colonX I i) n +
        hilbertFun col (I ⊔ Ideal.span {X i}) (n + Pi.single (col i) 1) := by
  haveI := finite_colourPiece (K := K) col n
  haveI := finite_colourPiece (K := K) col (n + Pi.single (col i) 1)
  have h := finrank_sup_add_finrank_colonX (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) hI i n
  have h' := congrArg (Nat.cast : ℕ → ℚ) h
  rw [Nat.cast_add, Nat.cast_add] at h'
  unfold hilbertFun
  linarith
end GlobalTheory.MultiHilbert
