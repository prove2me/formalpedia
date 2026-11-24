-- Prove2me | solution 1 for GlobalTheory.CNorm.herb_nrm_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:06:55.567349+00:00
-- url     : https://prove2.me/submissions/fcb376af-5664-42f5-865b-60237b1a1f9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormDifferenceIndexIdentity
import Theorems.Thm_GlobalTheory_CNorm_mem_fix
import Theorems.Thm_GlobalTheory_CNorm_nrm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution {A : Type} [CommGroup A] (σ : A →* A) (p : ℕ) (b : A)
    (hb : b ∈ fix σ) : nrm σ p b = b ^ p := by
  rw [nrm_apply, Finset.prod_congr rfl (fun i _ => Function.iterate_fixed ((mem_fix σ b).1 hb) i)]
  simp
end GlobalTheory.CNorm
