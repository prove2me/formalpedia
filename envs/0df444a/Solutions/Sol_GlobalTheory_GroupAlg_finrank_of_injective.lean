-- Prove2me | solution 1 for GlobalTheory.GroupAlg.finrank_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:06:30.810818+00:00
-- url     : https://prove2.me/submissions/dc476d1d-8c15-4ace-9b73-370dc5c77f18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Theorems.Thm_GlobalTheory_GroupAlg_free_of_injective
import Theorems.Thm_GlobalTheory_GroupAlg_finite_of_finiteIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)
namespace GlobalTheory.GroupAlg
theorem _root_.solution (hu : Function.Injective u) [u.range.FiniteIndex]
    (p : PrimeSpectrum R[Y]) : (mapDomainRingHom R u).finrank p = u.range.index := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Nontrivial R[Y] := p.nontrivial
  change Module.rankAtStalk (R := R[Y]) R[X] p = _
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_nat_card_basis (cosetBasis R u hu)]
  rfl
end GlobalTheory.GroupAlg
