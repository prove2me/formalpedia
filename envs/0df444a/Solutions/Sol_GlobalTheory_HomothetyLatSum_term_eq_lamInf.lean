-- Prove2me | solution 1 for GlobalTheory.HomothetyLatSum.term_eq_lamInf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:21.170923+00:00
-- url     : https://prove2.me/submissions/76e27b83-255b-48c1-8851-e562da6636c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomothetyLatSum
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_prod_cpow
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_prod_norm_sq
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
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.HomothetyLatSum
variable {E : Type} [Field E] [NumberField E]
variable {I : Type} [Fintype I]
namespace GlobalTheory.HomothetyLatSum
theorem _root_.solution [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : Eˣ) :
    term φ (2 * s) κ σ α =
      (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) := by
  have key : ∀ i, ((‖φ i α‖ : ℝ) : ℂ) ^ (-2 * σ) = (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) ^ (-σ) := fun i => by
    have hp : 0 < ‖φ i α‖ := by simp
    have : (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) = ((‖φ i α‖ : ℝ) : ℂ) * ((‖φ i α‖ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.mul_cpow_ofReal_nonneg hp.le hp.le,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hp.ne')]
    congr 1; ring
  rw [← TermUnit.prod_norm_sq hφ, ← TermUnit.prod_cpow _ _ (fun i => by positivity)]
  unfold term lamInf
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [key]
  have gen : ∀ (a c N : ℂ) (m n : ℕ), a⁻¹ ^ m * c ^ n * N = (a ^ m * c⁻¹ ^ n)⁻¹ * N := by
    intro a c N m n
    rw [mul_inv, inv_pow, inv_pow, inv_inv]
  exact gen _ _ _ _ _
end GlobalTheory.HomothetyLatSum
