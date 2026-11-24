-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.colourPiece_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:43.244021+00:00
-- url     : https://prove2.me/submissions/e70f91fb-b8be-46cc-b676-4bc7680ead2f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_weight_colour_apply

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
variable {K σ : Type} [Field K] {r : ℕ} (col : σ → Fin r)
namespace GlobalTheory.MultiHilbert
theorem _root_.solution {I : Ideal (MvPolynomial σ K)} (k : Fin r)
    (hk : ∀ i, col i = k → X i ∈ I) (n : Fin r → ℕ) (hn : 1 ≤ n k) :
    weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ≤
      I.restrictScalars K := by
  intro F hF
  have h1 : Ideal.span (X '' {i | col i = k} : Set (MvPolynomial σ K)) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hk i hi
  refine h1 ?_
  rw [mem_ideal_span_X_image]
  intro m hm
  have h2 := hF (mem_support_iff.1 hm)
  by_contra hcon
  push Not at hcon
  have h3 := weight_colour_apply col m k
  rw [h2, Finset.sum_eq_zero] at h3
  · omega
  · intro i _
    split_ifs with h
    · exact hcon i h
    · rfl
end GlobalTheory.MultiHilbert
