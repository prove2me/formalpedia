-- Prove2me | solution 1 for N25.GlobalKummer.cyclotomic_coboundary_of_valuations
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:14.405026+00:00
-- url     : https://prove2.me/submissions/34fcfb07-6c03-40e5-9fbd-3a637cf9ecab

import Mathlib
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level
import Theorems.Thm_Rat_exists_pow_of_forall_padicValRat_dvd

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

local instance rationalValuationPrimeSeventyOne_s03ec08 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- Rational Kummer data with valuation divisible by 71 at every prime
makes the original cyclotomic-line cocycle a coboundary. -/
theorem _root_.solution
    (c : groupCohomology.cocycles₁ cyclotomicRep)
    (e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)))
    (he : ∀ (σ : Gal) (a : ZMod 71),
      e ((ExtCitation.cycloChar 71 σ : ZMod 71) * a) =
        Additive.ofMul (σ • Additive.toMul (e a)))
    (a : ℚˣ) (α : (AlgebraicClosure ℚ)ˣ)
    (hα : algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ) = (α : AlgebraicClosure ℚ) ^ 71)
    (hc : ∀ σ : Gal, (Additive.toMul (e (c σ))).val =
      groupCohomology.Kummer.kummerCocycle α σ)
    (hval : ∀ p : ℕ, Nat.Prime p → (71 : ℤ) ∣ padicValRat p (a : ℚ)) :
    (∃ m : cyclotomicRep, ∀ σ : Gal, c σ = cyclotomicRep.ρ σ m - m) ∧
      groupCohomology.H1π cyclotomicRep c = 0 := by
  obtain ⟨b, hb⟩ := Rat.exists_pow_of_forall_padicValRat_dvd (a : ℚ) a.ne_zero hval
  have hb0 : b ≠ 0 := by
    intro h
    apply a.ne_zero
    rw [← hb, h]
    norm_num
  let β : (AlgebraicClosure ℚ)ˣ :=
    Units.map (algebraMap ℚ (AlgebraicClosure ℚ)).toMonoidHom (Units.mk0 b hb0)
  have hβ : β ^ 71 = α ^ 71 := by
    apply Units.ext
    change (algebraMap ℚ (AlgebraicClosure ℚ) b) ^ 71 = (α : AlgebraicClosure ℚ) ^ 71
    rw [← map_pow, hb]
    exact hα
  let u : rootsOfUnity 71 (AlgebraicClosure ℚ) := ⟨α / β, by
    rw [mem_rootsOfUnity, div_pow, hβ]
    exact div_self' _⟩
  let m : ZMod 71 := e.symm (Additive.ofMul u)
  have hem : e m = Additive.ofMul u := e.apply_symm_apply _
  have hm : ∀ σ : Gal, c σ = cyclotomicRep.ρ σ m - m := by
    intro σ
    have hβfix : σ • β = β :=
      groupCohomology.Kummer.smul_units_eq_self_of_mem_range σ ⟨b, rfl⟩
    have hcu : Additive.toMul (e (c σ)) = (σ • u) / u := by
      apply Subtype.ext
      rw [hc σ]
      change σ • α / α = (σ • (α / β)) / (α / β)
      rw [groupCohomology.Kummer.smul_units_div, hβfix]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    apply e.injective
    change e (c σ) = e ((ExtCitation.cycloChar 71 σ : ZMod 71) * m - m)
    rw [map_sub, he, hem]
    change e (c σ) = Additive.ofMul ((σ • u) / u)
    exact congrArg Additive.ofMul hcu
  refine ⟨⟨m, hm⟩, ?_⟩
  apply (groupCohomology.H1π_eq_zero_iff c).mpr
  refine ⟨m, ?_⟩
  funext σ
  change cyclotomicRep.ρ σ m - m = c σ
  exact (hm σ).symm

end N25.GlobalKummer
