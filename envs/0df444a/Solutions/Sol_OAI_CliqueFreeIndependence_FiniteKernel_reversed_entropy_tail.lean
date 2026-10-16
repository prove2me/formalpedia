-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteKernel.reversed_entropy_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:24:16.201097+00:00
-- url     : https://prove2.me/submissions/5ab3d8c8-f171-46ab-8986-a7773a3502cc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean:L388-L411
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteKernel.reversed_entropy_tail. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel

-- ---- from OAI.Combinatorics.CliqueFree.FiniteEntropy ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

variable {J : Type v} [Fintype J]

lemma entropy_tail_term {p w x a : ℝ} (hp : 0 ≤ p) (hw : 0 < w)
    (hx : 0 < x) (hd : p ≤ x * w) :
    (a + Real.log x) * (if p < w * Real.exp (-a) then p else 0) ≤
      p * (Real.log (w / p) + Real.log x) := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp]
  have hlog := Real.log_le_log hp hd
  rw [Real.log_mul hx.ne' hw.ne'] at hlog
  have hlower : 0 ≤ Real.log (w / p) + Real.log x := by
    rw [Real.log_div hw.ne' hp.ne']
    linarith
  split_ifs with hsmall
  · have h := Real.log_lt_log hp hsmall
    rw [Real.log_mul hw.ne' (Real.exp_ne_zero _), Real.log_exp] at h
    have ha : a ≤ Real.log (w / p) := by
      rw [Real.log_div hw.ne' hp.ne']
      linarith
    nlinarith
  · simpa using mul_nonneg hp.le hlower

lemma entropy_tail {p w : I → ℝ} (hp : IsProb p) (hw : ∀ i, 0 < w i)
    {x a : ℝ} (hx : 0 < x) (hd : ∀ i, p i ≤ x * w i) :
    (a + Real.log x) * (∑ i, if p i < w i * Real.exp (-a) then p i else 0) ≤
      entropy w p + Real.log x := by
  have h := sum_le_sum (s := univ) fun i _ ↦
    entropy_tail_term (a := a) (hp.1 i) (hw i) hx (hd i)
  simpa only [mul_sum, mul_add, sum_add_distrib, ← sum_mul, hp.2, one_mul,
    entropy] using h

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.FiniteKernel ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteKernel

open FiniteEntropy
variable {I : Type u} [Fintype I]

attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI
variable {J : Type v}

lemma reversed_entropy_tail {μ w : I → ℝ} {K : Matrix I I ℝ}
    (hμ : IsProb μ) (hw : ∀ i, 0 < w i) (hK : Stochastic K)
    (hr : Reversible μ K) {x a : ℝ} (hx : 0 < x)
    (hd : ∀ i j, K i j ≤ x * w j) :
    (a + Real.log x) *
        (∑ i, μ i * ∑ j, if K j i < w i * Real.exp (-a) then K i j else 0) ≤
      avgEntropy μ w K + Real.log x := by
  have h := sum_le_sum (s := univ) fun i _ ↦
    mul_le_mul_of_nonneg_left (entropy_tail (a := a) (hK i) hw hx (hd i)) (hμ.1 i)
  have heq : (∑ i, μ i * ∑ j, if K j i < w i * Real.exp (-a) then K i j else 0) =
      ∑ i, μ i * ∑ j, if K i j < w j * Real.exp (-a) then K i j else 0 := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    by_cases hb : K i j < w j * Real.exp (-a)
    · simp only [hb, ↓reduceIte]
      exact hr j i
    · simp only [hb, ↓reduceIte, mul_zero]
  rw [heq]
  simpa only [mul_sum, mul_add, sum_add_distrib, ← sum_mul, hμ.2, one_mul,
    avgEntropy, mul_left_comm] using h

end FiniteKernel

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteKernel
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open FiniteEntropy
attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteKernel.reversed_entropy_tail.{u} := @_root_.OAI.CliqueFreeIndependence.FiniteKernel.reversed_entropy_tail.{u}
