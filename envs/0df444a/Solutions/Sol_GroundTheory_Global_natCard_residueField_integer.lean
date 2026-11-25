-- Prove2me | solution 1 for GroundTheory.Global.natCard_residueField_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:11.566265+00:00
-- url     : https://prove2.me/submissions/28b3ff11-a30a-4cd5-b609-4f1eafa23401

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
namespace GroundTheory.Global
theorem _root_.solution :
    Nat.card 𝓀[u.adicCompletion F] = Nat.card (𝓞 F ⧸ u.asIdeal) :=
  (Nat.card_congr (residueEquivInteger u).toEquiv).symm
end GroundTheory.Global
