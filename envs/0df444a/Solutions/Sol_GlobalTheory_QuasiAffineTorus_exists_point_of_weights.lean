-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.exists_point_of_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:36.594905+00:00
-- url     : https://prove2.me/submissions/a61442d3-a9aa-417a-b8c1-0c0ab37a7da3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_extend
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_torusCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.restrictPoints_val
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.QuasiAffineTorus
variable {k : Type} [Field k] [IsAlgClosed k] {X : Type} [AddCommGroup X]
variable {H : Type} [CommGroup H] (τ : (Multiplicative X →* kˣ) →* H) (A : Subalgebra k (H → k))
namespace GlobalTheory.QuasiAffineTorus
theorem _root_.solution (hdom : ∀ f ∈ A, ∀ g ∈ A, f * g = 0 → f = 0 ∨ g = 0)
    (hinv : ∀ f ∈ A, (fun y => f y⁻¹) ∈ A)
    (hc : ∀ f ∈ A, (∀ t y, f (τ t * y) = f y) → ∀ y, f y = f 1) (x : H) :
    ∃ t, ∀ g ∈ A, ∀ χ : X, (∀ t y, g (τ t * y) = (t (Multiplicative.ofAdd χ) : k) * g y) →
      g x = g (τ t) := by
  let Wt : (H → k) → X → Prop := fun g χ =>
    g ∈ A ∧ ∀ t y, g (τ t * y) = (t (Multiplicative.ofAdd χ) : k) * g y
  have hneg : ∀ g χ, Wt g χ → Wt (fun y => g y⁻¹) (-χ) := fun g χ h =>
    ⟨hinv g h.1, fun t y => by
      simp only [mul_inv, ← map_inv τ, h.2, ofAdd_neg, map_inv t]
      rfl⟩
  have hmul : ∀ g χ g' χ', Wt g χ → Wt g' χ' → Wt (g * g') (χ + χ') := fun g χ g' χ' h h' =>
    ⟨A.mul_mem h.1 h'.1, fun t y => by
      simp only [Pi.mul_apply, h.2, h'.2, ofAdd_add, map_mul, Units.val_mul]
      ring⟩
  have hone : Wt 1 0 := ⟨A.one_mem, fun t y => by simp⟩
  have hpair : ∀ g g' χ, Wt g χ → Wt g' χ → ∀ y, g y * g' y⁻¹ = g 1 * g' 1 := by
    intro g g' χ h h' y
    have h1 := hmul _ _ _ _ h (hneg _ _ h')
    simpa using hc _ h1.1 (fun t y => by rw [h1.2]; simp) y
  let M : AddSubgroup X :=
    { carrier := {χ | ∃ g, Wt g χ ∧ g 1 = 1}
      zero_mem' := ⟨1, hone, rfl⟩
      add_mem' := by
        rintro χ χ' ⟨g, h, e⟩ ⟨g', h', e'⟩
        exact ⟨_, hmul _ _ _ _ h h', by simp [e, e']⟩
      neg_mem' := by
        rintro χ ⟨g, h, e⟩
        exact ⟨_, hneg _ _ h, by simpa using e⟩ }
  choose u hu hu1 using fun m : M => (m.2 : ∃ g, Wt g m ∧ g 1 = 1)
  have hux : ∀ m, u m x * u m x⁻¹ = 1 := fun m => by simpa [hu1] using hpair _ _ _ (hu m) (hu m) x
  have huniq : ∀ (m : M) g, Wt g m → g x = g 1 * u m x := fun m g h => by
    have h1 := hpair _ _ _ h (hu m) x
    rw [hu1, _root_.mul_one] at h1
    rw [← h1, _root_.mul_assoc, mul_comm (u m x⁻¹), hux, _root_.mul_one]
  let φ : M →+ Additive kˣ := AddMonoidHom.mk'
    (fun m => Additive.ofMul (Units.mk0 (u m x) (left_ne_zero_of_mul_eq_one (hux m))))
    fun m m' => congrArg Additive.ofMul (Units.ext (by
      simpa [hu1] using (huniq (m + m') _ (hmul _ _ _ _ (hu m) (hu m'))).symm))
  obtain ⟨t, ht⟩ := exists_extend M φ
  refine ⟨t, fun g hg χ hχ => ?_⟩
  have h : Wt g χ := ⟨hg, hχ⟩
  by_cases h1 : g 1 = 0
  · have h0 : g * (fun y => g y⁻¹) = 0 := funext fun y => by simpa [h1] using hpair _ _ _ h h y
    have : g = 0 := by
      rcases hdom _ hg _ (hinv g hg) h0 with e | e
      · exact e
      · funext y
        simpa using congrFun e y⁻¹
    simp [this]
  · have hm : χ ∈ M := ⟨(g 1)⁻¹ • g, ⟨A.smul_mem hg _, fun t y => by simp [hχ]; ring⟩, by simp [h1]⟩
    have h2 := hχ t 1
    rw [_root_.mul_one] at h2
    rw [h2, huniq ⟨χ, hm⟩ g h, ht ⟨χ, hm⟩, mul_comm]
    rfl
end GlobalTheory.QuasiAffineTorus
