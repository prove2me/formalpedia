-- Prove2me | solution 1 for GlobalTheory.RegularNormal.dvd_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:31.37992+00:00
-- url     : https://prove2.me/submissions/8ef567fc-c94e-496c-860c-99ddd785a87f

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
import Theorems.Thm_GlobalTheory_SaturatedNotDvd_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.RegularNormal
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
namespace GlobalTheory.RegularNormal
theorem _root_.solution (hx : Prime x) (h : StableDvd (A ⧸ Ideal.span {x})) {a b : A}
    (hb : ¬ x ∣ b) {I : Ideal A} (hI : I ≠ ⊥)
    (hst : ∀ r ∈ I, ∃ s ∈ I, a * r = b * s) : b ∣ a := by
  first
  | exact @_root_.GlobalTheory.SaturatedNotDvd.main
  | exact _root_.GlobalTheory.SaturatedNotDvd.main
  | (apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedNotDvd.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedNotDvd.main ..)
end GlobalTheory.RegularNormal
