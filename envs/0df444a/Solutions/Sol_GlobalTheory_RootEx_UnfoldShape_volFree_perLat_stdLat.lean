-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.volFree_perLat_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:12:26.60595+00:00
-- url     : https://prove2.me/submissions/aef1d1e9-ee76-4319-83bf-1c594026e5a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_boxExp_eq_zero
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_sum_boxExp
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_measure_pow_mul_mem
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_perLat_stdLat_eq
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n]
    [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (c : ℕ) (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (ν : Measure k) (hν : IsUnitVol ν) :
    volFree ν n n' c (perLat ϖ n' c (stdLat k n))
      = (resCard k : ENNReal) ^ expo c (Fintype.card n) := by
  classical
  have := hν.1
  have := secondCountable k
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rw [perLat_stdLat_eq h0, volFree, Measure.pi_pi]
  simp only [measure_pow_mul_mem hϖ ν hν]
  rw [Finset.prod_pow_eq_pow_sum, ← sum_boxExp n n' c]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter fun rs => Free 1 rs) (by simp) boxExp]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => boxExp_eq_zero x ?_
  simpa using hx
end GlobalTheory.RootEx.UnfoldShape
