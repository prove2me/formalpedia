-- Prove2me | solution 1 for GlobalTheory.WeilM.ResEtaPow.triv_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:16.744854+00:00
-- url     : https://prove2.me/submissions/112276dc-a965-4a10-90bc-793208044e04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
omit [Invertible (2 : R)]
namespace GlobalTheory.WeilM
namespace ResEtaPow
theorem _root_.solution {K : Subgroup Rˣ} {χ : Eˣ →* Circle} {n : ℕ} (hχ : ResEtaPow K χ n) (hn : Even n)
    (a : Rˣ) : χ (Units.map (algebraMap R E : R →* E) a) = 1 := by
  rw [← Circle.coe_eq_one, hχ a, hn.neg_one_pow, ite_self]
end ResEtaPow
end GlobalTheory.WeilM
