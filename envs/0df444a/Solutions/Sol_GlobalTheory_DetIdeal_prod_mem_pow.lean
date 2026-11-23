-- Prove2me | solution 1 for GlobalTheory.DetIdeal.prod_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:39.473804+00:00
-- url     : https://prove2.me/submissions/7703d3be-cd67-48a0-8536-b203d1726bd6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
namespace GlobalTheory.DetIdeal
theorem _root_.solution {ι : Type} (c : FractionalIdeal R⁰ K) (s : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ s, f i ∈ c) : ∏ i ∈ s, f i ∈ c ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FractionalIdeal.one_mem_one R⁰
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact FractionalIdeal.mul_mem_mul (hf a (by simp)) (ih fun i hi => hf i (by simp [hi]))
end GlobalTheory.DetIdeal
