-- Prove2me | solution 1 for GlobalTheory.DetIdeal.det_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:28.053729+00:00
-- url     : https://prove2.me/submissions/33075ce1-bd78-486a-909b-4e1d0de5d8f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Theorems.Thm_GlobalTheory_DetIdeal_prod_mem_pow

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
theorem _root_.solution (c : FractionalIdeal R⁰ K) (M : Matrix (Fin r) (Fin r) K) (hM : ∀ i j, M i j ∈ c) :
    M.det ∈ c ^ r := by
  rw [Matrix.det_apply, ← FractionalIdeal.mem_coe]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have h := prod_mem_pow c Finset.univ (fun i => M (σ i) i) fun i _ => hM _ _
  rw [Finset.card_univ, Fintype.card_fin, ← FractionalIdeal.mem_coe] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact h
  · rw [hs, Units.neg_smul, one_smul]; exact neg_mem h
end GlobalTheory.DetIdeal
