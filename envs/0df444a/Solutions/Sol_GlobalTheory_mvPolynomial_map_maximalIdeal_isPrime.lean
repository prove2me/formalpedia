-- Prove2me | solution 1 for GlobalTheory.mvPolynomial_map_maximalIdeal_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:41.049436+00:00
-- url     : https://prove2.me/submissions/d37efc36-6221-47e8-ac55-df2754972575

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] [IsLocalRing O] (g : ℕ) :
    ((IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)).IsPrime := by
  have h : (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)
      = RingHom.ker (MvPolynomial.map (σ := Fin g) (IsLocalRing.residue O)) := by
    ext F
    rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
  rw [h]
  exact RingHom.ker_isPrime _
end GlobalTheory
