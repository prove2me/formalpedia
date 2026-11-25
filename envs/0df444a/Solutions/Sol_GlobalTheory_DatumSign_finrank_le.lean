-- Prove2me | solution 1 for GlobalTheory.DatumSign.finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:04.710014+00:00
-- url     : https://prove2.me/submissions/09098ce1-30be-4a85-bcb8-b0e3dc1a1053

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_PEqQOfNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DatumSign
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct
variable {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.DatumSign
theorem _root_.solution (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A J K : V →ₗ[ℝ] V) (s : ℝ) (hs : 0 < s)
    (hA : ∀ x, A (A x) = -((s * s) • x)) (hJ : ∀ x, J (J x) = -x) (hK : ∀ x, K (K x) = -x)
    (hKA : K ∘ₗ A = A ∘ₗ K) (pJ : ∀ x, x ≠ 0 → 0 < B (J x) x) (pK : ∀ x, x ≠ 0 → 0 < B (K x) x) :
    finrank ℝ (LinearMap.ker (J ∘ₗ A - s • LinearMap.id)) ≤ finrank ℝ (LinearMap.ker (K ∘ₗ A - s • LinearMap.id)) := by
  have c : ∀ x, K (A x) = A (K x) := fun x => LinearMap.congr_fun hKA x
  let W := LinearMap.ker (J ∘ₗ A - s • LinearMap.id)
  let W' := LinearMap.ker (K ∘ₗ A - s • LinearMap.id)
  have hm : ∀ x, x ∈ W' ↔ K (A x) = s • x := fun x => by simp [W', sub_eq_zero]
  let f : W →ₗ[ℝ] W' := LinearMap.codRestrict W' ((K ∘ₗ A + s • LinearMap.id) ∘ₗ W.subtype) (fun x => (hm _).2 (by
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add,
      map_smul, Submodule.subtype_apply]
    rw [c (K (A x)), hK, map_neg, hA]
    module))
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  have hx0 : (x : V) ≠ 0 := fun h => h0 (Subtype.ext h)
  have h1 : J (A x) = s • (x : V) := by
    have : J (A x) - s • (x : V) = 0 := LinearMap.mem_ker.1 x.2
    exact sub_eq_zero.1 this
  have h2 : K (A x) = -(s • (x : V)) := by
    have := congrArg Subtype.val hx
    simpa [f, add_eq_zero_iff_eq_neg] using this
  have e1 : A x = -(s • J x) := by
    have := congrArg J h1
    rw [hJ, map_smul] at this
    rw [← this, neg_neg]
  have e2 : A x = s • K x := by
    have := congrArg K h2
    rw [hK, map_neg, map_smul] at this
    exact neg_injective this
  have b := congrArg (fun v => B v x) (e1.symm.trans e2)
  simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul] at b
  have := mul_pos hs (pJ x hx0)
  have := mul_pos hs (pK x hx0)
  linarith
end GlobalTheory.DatumSign
