-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.inertiaDeg_primeOfPlace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:25.447917+00:00
-- url     : https://prove2.me/submissions/8c3c040e-4568-41c6-80fc-3b8d51300cc7

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_finrank_residueField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
attribute [local instance low] algebraExt
attribute [local instance] isScalarTower_ext
attribute [local instance] isTorsionFree_ext
variable [IsFunctionField k K] [IsFunctionField k K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] (v : Place k K)
attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure
omit [IsFunctionField k K']
namespace GroundTheory.FunctionField.Place
theorem _root_.solution
    (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    q.1.inertiaDeg v.ring = (v.placeOfPrime q).inertiaDeg v := by
  have := q.2.1
  have := q.2.2
  have hmax : q.1.IsMaximal := q.2.1.isMaximal (v.ne_bot_of_mem_primesOver q.2)
  have h := v.placeOfPrime_liesOver q
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal v.ring) q.1, ← h.finrank_residueField]
  let := h.algebra
  have := h.isLocalHom
  have : IsLocalization.AtPrime (v.placeOfPrime q).ring q.1 :=
    inferInstanceAs (IsLocalization (v.primeHS q).asIdeal.primeCompl
      (HeightOneSpectrum.valuationSubringAtPrime K' (v.primeHS q)))
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (IsLocalization.AtPrime.equivQuotMaximalIdeal q.1 (v.placeOfPrime q).ring) ?_
  apply Ideal.Quotient.ringHom_ext
  ext a
  rfl
end GroundTheory.FunctionField.Place
