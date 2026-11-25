-- Prove2me | solution 1 for GlobalTheory.InertiaMovesRoot.val_eq_one_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:07:39.235542+00:00
-- url     : https://prove2.me/submissions/05238baf-71c4-4c67-a156-6a45c84659fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
open GlobalTheory GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
namespace GlobalTheory.InertiaMovesRoot
theorem _root_.solution (h : IsPlaceOver A w) {s : 𝓞 E} (hs : s ∉ w.asIdeal) :
    A.valuation (algebraMap E Ω (s : E)) = 1 :=
  le_antisymm (valuation_le_one_intCl (F := E) A (algebraMap (𝓞 E) _ s))
    (not_lt.mp fun hlt => hs ((h s).mp hlt))
end GlobalTheory.InertiaMovesRoot
