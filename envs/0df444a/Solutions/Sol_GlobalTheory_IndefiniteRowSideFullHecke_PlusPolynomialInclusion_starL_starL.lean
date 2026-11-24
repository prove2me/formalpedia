-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.starL_starL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:26.557178+00:00
-- url     : https://prove2.me/submissions/abbdab67-be77-4325-8d69-ad461e5367f8

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_alpha_val
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_starL_of
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_starL_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix NumberField IsDedekindDomain Formalism.UG
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
theorem _root_.solution (hP : IsPPol c r P) (hc : ∀ e, c (c e) = e) (y : AdjoinRoot P) :
    starL hP (starL hP y) = y := by
  have h : ((starL hP).comp (starL hP)).toRingHom = RingHom.id _ := by
    apply AdjoinRoot.ringHom_ext
    · ext e; simp [starL_of, hc]
    · have h1 : starL hP (AdjoinRoot.root P) * AdjoinRoot.root P = 1 := by
        rw [starL_root]; exact (alpha hP).inv_mul
      have h2 := congrArg (starL hP) h1
      rw [map_mul, map_one, starL_root hP, mul_comm] at h2
      have h3 := congrArg (fun t => (alpha hP : AdjoinRoot P) * t) h2
      simp only [← mul_assoc, Units.mul_inv, one_mul, mul_one] at h3
      simpa [starL_root, alpha_val] using h3
  exact RingHom.congr_fun h y
end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
