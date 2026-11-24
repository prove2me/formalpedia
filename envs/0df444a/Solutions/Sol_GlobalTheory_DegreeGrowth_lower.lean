-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:12.784578+00:00
-- url     : https://prove2.me/submissions/34093ec1-a755-4c2c-82d5-68e87e25982e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.DegreeGrowth
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]
namespace GlobalTheory.DegreeGrowth
theorem _root_.solution {s m : ℕ} (φ : MvPolynomial (Fin s) K →ₐ[K] B) (hφ : Function.Injective φ)
    (r : Fin m → B)
    (hr : Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B)) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ t : ℕ,
      t ^ s ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) := by
  choose q hq using fun i => hr (φ (MvPolynomial.X i))
  set E : ℕ := (∑ i, (q i).totalDegree) + 1 with hE
  have hE0 : 0 < E := Nat.succ_pos _
  refine ⟨E ^ s, Nat.one_le_pow _ _ hE0, fun t => ?_⟩
  set V := (MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap with hV
  let e : (Fin s → Fin (t / E + 1)) → (Fin s →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm fun i => (a i : ℕ)
  have he : Function.Injective e := by
    intro a a' h
    funext i
    have := congrArg (fun z : Fin s →₀ ℕ => z i) h
    exact Fin.ext (by simpa [e] using this)
  have hli : LinearIndependent K fun a => φ (MvPolynomial.monomial (e a) (1 : K)) := by
    have h1 := ((MvPolynomial.basisMonomials (Fin s) K).linearIndependent.comp e he).map'
      φ.toLinearMap (LinearMap.ker_eq_bot.2 hφ)
    simpa [Function.comp_def] using h1
  have hmem : ∀ a, φ (MvPolynomial.monomial (e a) (1 : K)) ∈ V := by
    intro a
    refine ⟨∏ i, q i ^ (a i : ℕ), ?_, ?_⟩
    · refine (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ?_
      refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
      calc ∑ i, (q i ^ (a i : ℕ)).totalDegree ≤ ∑ i, (t / E) * (q i).totalDegree :=
            Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
              (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (a i).2))
        _ ≤ (t / E) * E := by
            rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ ≤ t := Nat.div_mul_le_self _ _
    · rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      simp [hq, e]
  have hli' : LinearIndependent K fun a => (⟨_, hmem a⟩ : V) :=
    LinearIndependent.of_comp V.subtype hli
  have hc := hli'.fintype_card_le_finrank
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] at hc
  calc t ^ s ≤ (E * (t / E + 1)) ^ s := Nat.pow_le_pow_left (Nat.lt_mul_div_succ t hE0).le _
    _ ≤ _ := by rw [mul_pow]; exact Nat.mul_le_mul_left _ hc
end GlobalTheory.DegreeGrowth
