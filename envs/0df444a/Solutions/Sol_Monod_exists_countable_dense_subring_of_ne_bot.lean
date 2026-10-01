-- Prove2me | solution 1 for Monod.exists_countable_dense_subring_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:04:48.213464+00:00
-- url     : https://prove2.me/submissions/6081267d-9b2d-4b1c-b7dc-c86a407b172f

import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Tactic

 theorem solution {A : Subring ℝ} (hA : A ≠ ⊥) :
    ∃ A' : Subring ℝ, A' ≤ A ∧ Countable A' ∧ Dense (A' : Set ℝ) := by
  classical
  obtain ⟨x, hxA, hxZ⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hA)
  have hxne : x ≠ (Int.floor x : ℝ) := by
    intro h
    exact hxZ (Subring.mem_bot.mpr ⟨Int.floor x,h.symm⟩)
  let t := Int.fract x
  have htpos : 0 < t := Int.fract_pos.mpr hxne
  have htone : t < 1 := Int.fract_lt_one x
  have htA : t ∈ A := A.sub_mem hxA (intCast_mem A _)
  let e : Polynomial ℤ →+* A := Polynomial.eval₂RingHom (Int.castRingHom A) ⟨t,htA⟩
  let er : Polynomial ℤ →+* ℝ := A.subtype.comp e
  let A' := er.range
  have htA' : t ∈ A' := by
    apply RingHom.mem_range.mpr
    exact ⟨Polynomial.X, by simp [er,e]⟩
  have hsub : A' ≤ A := by
    intro y hy
    obtain ⟨p,rfl⟩ := RingHom.mem_range.mp hy
    exact (e p).property
  haveI : Countable (AddMonoidAlgebra ℤ ℕ) := AddMonoidAlgebra.coeffEquiv.injective.countable
  haveI : Countable (Polynomial ℤ) := Polynomial.toFinsupp_injective.countable
  have hcount : Countable A' := er.rangeRestrict_surjective.countable
  refine ⟨A',hsub,hcount,?_⟩
  apply A'.toAddSubgroup.dense_of_not_isolated_zero
  intro ε hε
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hε htone
  exact ⟨t^k,A'.pow_mem htA' k,pow_pos htpos k,hk⟩
