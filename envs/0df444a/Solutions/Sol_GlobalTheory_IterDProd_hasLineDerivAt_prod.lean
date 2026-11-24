-- Prove2me | solution 1 for GlobalTheory.IterDProd.hasLineDerivAt_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:33.81001+00:00
-- url     : https://prove2.me/submissions/736cee9a-2a78-45f6-babe-f7aa271758b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivProdOneVarAtZero
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.IterDProd
namespace GlobalTheory.IterDProd
theorem _root_.solution {I : Type} [Fintype I] [DecidableEq I] (φ : I → ℂ → ℂ) (A : ℂ)
    (z : I → ℂ) (j : I) (hj : DifferentiableAt ℂ (φ j) (z j)) :
    HasLineDerivAt ℂ (fun z : I → ℂ ↦ A * ∏ i, φ i (z i))
      (A * (deriv (φ j) (z j) * ∏ i ∈ Finset.univ.erase j, φ i (z i))) z (Pi.single j 1) := by
  unfold HasLineDerivAt
  have h1 : (fun t : ℂ ↦ A * ∏ i, φ i ((z + t • (Pi.single j (1 : ℂ) : I → ℂ)) i))
      = fun t ↦ A * (φ j (z j + t) * ∏ i ∈ Finset.univ.erase j, φ i (z i)) := by
    funext t
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 2
    · simp
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi)]
  have h2 : HasDerivAt (fun t : ℂ ↦ φ j (z j + t)) (deriv (φ j) (z j)) 0 := by
    have h : HasDerivAt (φ j) (deriv (φ j) (z j)) (z j + 0) := by simpa using hj.hasDerivAt
    exact h.comp_const_add (z j) 0
  show HasDerivAt (fun t : ℂ ↦ A * ∏ i, φ i ((z + t • (Pi.single j (1 : ℂ) : I → ℂ)) i)) _ 0
  rw [h1]
  exact (h2.mul_const _).const_mul A
end GlobalTheory.IterDProd
