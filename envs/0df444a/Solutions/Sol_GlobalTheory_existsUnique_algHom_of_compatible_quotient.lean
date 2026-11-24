-- Prove2me | solution 1 for GlobalTheory.existsUnique_algHom_of_compatible_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:57:37.327053+00:00
-- url     : https://prove2.me/submissions/14b6aae0-8635-4476-aed7-97552071af1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_isAdicComplete_of_finite
import Theorems.Thm_GlobalTheory_existsUnique_algHom_of_compatible_tower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
variable [IsNoetherianRing R] [IsAdicComplete I R] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R B]
    (f : ∀ n : ℕ, (A ⧸ (I ^ n).map (algebraMap R A)) →ₐ[R] B ⧸ (I ^ n).map (algebraMap R B))
    (hf : ∀ n x, adicQuotTransition I B n (f (n + 1) x) = f n (adicQuotTransition I A n x)) :
    ∃! g : A →ₐ[R] B, ∀ n a, Ideal.Quotient.mk _ (g a) = f n (Ideal.Quotient.mk _ a) := by
  have := isAdicComplete_of_finite I B
  exact existsUnique_algHom_of_compatible_tower I
    (C := fun n ↦ B ⧸ (I ^ n).map (algebraMap R B)) (fun _ ↦ Ideal.Quotient.mkₐ R _)
    (fun _ ↦ Ideal.Quotient.mk_surjective)
    (fun n x ↦ by
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.smul_top_eq_map,
        Submodule.restrictScalars_mem])
    (fun n ↦ adicQuotTransition I B n) (fun _ _ ↦ rfl)
    (fun n ↦ (f n).comp (Ideal.Quotient.mkₐ R _))
    (fun n a ↦ hf n (Ideal.Quotient.mk _ a))
end GlobalTheory
