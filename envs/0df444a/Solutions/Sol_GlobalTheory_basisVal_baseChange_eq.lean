-- Prove2me | solution 1 for GlobalTheory.basisVal_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:29.046842+00:00
-- url     : https://prove2.me/submissions/8f8648a0-f80e-4a2f-9976-4a5fc7563a07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_eq_of_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial Module
variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)
namespace GlobalTheory
theorem _root_.solution (hv : ∀ a : O, v (algebraMap O R a) ≤ 1) (c : Basis κ O M)
    (x : R ⊗[O] M) : basisVal v (b.baseChange R) x = basisVal v (c.baseChange R) x :=
  basisVal_eq_of_le_one v _ _
    (fun _ => (basisVal_le_iff v _).mpr fun _ => by simpa [Algebra.smul_def] using hv _)
    (fun _ => (basisVal_le_iff v _).mpr fun _ => by simpa [Algebra.smul_def] using hv _) x
end GlobalTheory
