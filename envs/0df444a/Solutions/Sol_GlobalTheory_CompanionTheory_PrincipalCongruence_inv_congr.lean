-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrincipalCongruence.inv_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:28:05.822585+00:00
-- url     : https://prove2.me/submissions/d0030a96-1214-4bfa-b44d-13661c9c3cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenIsCompactPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrincipalCongruence
variable {k : Type*} [Field k] [ValuativeRel k]
namespace GlobalTheory.CompanionTheory.PrincipalCongruence
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n k)
    (hAB : A * B = 1) {t : k} (ht : valuation k t < 1)
    (hA : ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t) :
    ∀ i j, valuation k (B i j - (1 : Matrix n n k) i j) ≤ valuation k t := by
  by_contra h
  push_neg at h
  obtain ⟨i₁, j₁, h₁⟩ := h
  haveI : Nonempty (n × n) := ⟨(i₁, j₁)⟩
  obtain ⟨⟨i₀, j₀⟩, hm⟩ := Finite.exists_max
    (fun p : n × n => valuation k (B p.1 p.2 - (1 : Matrix n n k) p.1 p.2))
  have hm' : ∀ l j, valuation k (B l j - (1 : Matrix n n k) l j) ≤
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := fun l j => hm (l, j)
  have hM : valuation k t < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    h₁.trans_le (hm' i₁ j₁)
  have hM0 : 0 < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    lt_of_le_of_lt zero_le' hM
  have hmat : (A - 1) * (B - 1) = -(A - 1) - (B - 1) := by
    simp only [sub_mul, mul_sub, hAB, one_mul, mul_one]
    abel
  have key : B i₀ j₀ - (1 : Matrix n n k) i₀ j₀ = -(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀) -
      ∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀) := by
    have := congrFun (congrFun hmat i₀) j₀
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply] at this
    rw [this]
    ring
  have hsum : valuation k (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) *
      (B l j₀ - (1 : Matrix n n k) l j₀)) ≤
      valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := by
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hA i₀ l) (hm' l j₀)
  have hlt : valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) <
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    mul_lt_of_lt_one_left hM0 ht
  have hle := Valuation.map_sub (valuation k) (-(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀))
    (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀))
  rw [← key, Valuation.map_neg] at hle
  rcases le_max_iff.mp hle with h | h
  · exact absurd ((h.trans (hA i₀ j₀))) (not_le.mpr hM)
  · exact absurd (h.trans hsum) (not_le.mpr hlt)
end GlobalTheory.CompanionTheory.PrincipalCongruence
