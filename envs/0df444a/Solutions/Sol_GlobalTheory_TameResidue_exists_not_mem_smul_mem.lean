-- Prove2me | solution 1 for GlobalTheory.TameResidue.exists_not_mem_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:40.434695+00:00
-- url     : https://prove2.me/submissions/d549fc84-2cc2-4996-a14f-6d251af5f84e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FiniteSeparableOfSumMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.TameResidue
namespace GlobalTheory.TameResidue
theorem _root_.solution {Γ B : Type} [Group Γ] [Finite Γ] [CommRing B]
    [MulSemiringAction Γ B] (q : Ideal B) [q.IsPrime] :
    ∃ y : B, y ∉ q ∧ ∀ g : Γ, g • q ≠ q → g • y ∈ q := by
  classical
  have hpow : ∀ h : Γ, h ^ (Nat.card Γ - 1) = h⁻¹ := fun h =>
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one'])
  have hex : ∀ g : Γ, ∃ a : B, a ∉ q ∧ (g • q ≠ q → g • a ∈ q) := by
    intro g
    by_cases hg : g • q = q
    · exact ⟨1, (Ideal.ne_top_iff_one q).1 (Ideal.IsPrime.ne_top inferInstance),
        fun h => absurd hg h⟩
    · by_contra hcon
      apply hg
      have h1 : ∀ a : B, g • a ∈ q → a ∈ q := fun a ha =>
        by_contra fun hn => hcon ⟨a, hn, fun _ => ha⟩
      have h2 : ∀ x ∈ q, g⁻¹ • x ∈ q := fun x hx => h1 _ (by rwa [smul_inv_smul])
      have h3 : ∀ m : ℕ, ∀ x ∈ q, (g⁻¹) ^ m • x ∈ q := by
        intro m
        induction m with
        | zero => intro x hx; rwa [pow_zero, one_smul]
        | succ m ih => intro x hx; rw [pow_succ', mul_smul]; exact h2 _ (ih x hx)
      have h5 : ∀ x ∈ q, g • x ∈ q := fun x hx => by
        have := h3 (Nat.card Γ - 1) x hx
        rwa [hpow, inv_inv] at this
      apply Ideal.ext
      intro x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      exact ⟨fun hx => by simpa using h5 _ hx, h2 x⟩
  choose a ha using hex
  haveI := Fintype.ofFinite Γ
  refine ⟨∏ g, a g, ?_, fun g hg => ?_⟩
  · exact prod_mem (S := q.primeCompl) fun g _ => (ha g).1
  · rw [Finset.smul_prod']
    exact q.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => g • a i) (Finset.mem_univ g)) ((ha g).2 hg)
end GlobalTheory.TameResidue
