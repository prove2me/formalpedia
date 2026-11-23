-- Prove2me | solution 1 for GlobalTheory.Square.IsAwayUnit.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:51.846319+00:00
-- url     : https://prove2.me/submissions/a5221f6b-c543-41b3-895b-a03cf1706302

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
omit [NumberField K] [StarRing K]
namespace GlobalTheory.Square
namespace IsAwayUnit
theorem _root_.solution {m k : ℕ} {a : 𝓞 K} (h : a ∣ (m : 𝓞 K) ^ k) : IsAwayUnit m (a : K) :=
  ⟨a, 0, k, h, by simp⟩
end IsAwayUnit
end GlobalTheory.Square
