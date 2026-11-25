-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ringKrullDim_le_of_hasGoingDown
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:58.709752+00:00
-- url     : https://prove2.me/submissions/e595d0cc-9be4-4b72-87d0-ddd736a6d35d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing
universe u
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.HasGoingDown A B] :
    ringKrullDim A ≤ ringKrullDim B := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  obtain ⟨P, -, hP, hlo⟩ := (maximalIdeal B).exists_ideal_le_liesOver_of_le
    (p := l.last.asIdeal) (q := maximalIdeal A) (le_maximalIdeal l.last.2.ne_top)
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  exact le_iSup_of_le L (by rw [hlen])
end GroundTheory.Arith.SchemeCoh
