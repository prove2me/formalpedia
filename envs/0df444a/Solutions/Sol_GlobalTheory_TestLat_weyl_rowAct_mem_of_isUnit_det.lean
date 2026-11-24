-- Prove2me | solution 1 for GlobalTheory.TestLat.weyl_rowAct_mem_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:39.373226+00:00
-- url     : https://prove2.me/submissions/79059c09-d22f-46d8-bfdd-79bc99e7b014

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_WeylRowActMemOfIsUnitDet
import Theorems.Thm_Formalism_UG_P_wlocal_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TestLat
namespace GlobalTheory.TestLat
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
      ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g.det →
        ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν,
          Formalism.GradedWeylDivisibility.rowAct R g f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν := by
  intro R _ _ n ν _ g hg f hf
  exact Formalism.UG.P.wlocal_main (le_refl n) ν n 0 (by omega) g g⁻¹ (Matrix.nonsing_inv_mul g hg)
    (fun _ _ hj => absurd hj (Nat.not_lt_zero _)) f hf
end GlobalTheory.TestLat
