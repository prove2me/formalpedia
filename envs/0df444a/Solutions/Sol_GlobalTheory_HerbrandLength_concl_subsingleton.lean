-- Prove2me | solution 1 for GlobalTheory.HerbrandLength.concl_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:30.423096+00:00
-- url     : https://prove2.me/submissions/f10faad8-3e35-46aa-8e4a-11606b5a71b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
import Theorems.Thm_GlobalTheory_HerbrandLength_loc_zero_of_ann

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HerbrandLength
open IsLocalRing
variable {A : Type} [CommRing A]
namespace GlobalTheory.HerbrandLength
theorem _root_.solution (b : A) (P : Finset (PrimeSpectrum A)) (M : Type) [AddCommGroup M]
    [Module A M] [Subsingleton M] : Concl b P M := by
  have hk : Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) = 0 :=
    Module.length_eq_zero_iff.2 ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  have hc : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = 0 :=
    Module.length_eq_zero_iff.2 ((Submodule.mkQ_surjective _).subsingleton)
  refine ⟨by rw [hk]; exact ENat.zero_ne_top, ?_⟩
  rw [hk, hc, zero_add, eq_comm]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [loc_zero_of_ann p.asIdeal M 1 (Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one))
    (fun x => Subsingleton.elim _ _), zero_mul]
end GlobalTheory.HerbrandLength
