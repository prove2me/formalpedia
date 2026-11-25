-- Prove2me | solution 1 for GlobalTheory.Published.AbMulNSt.unit_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:08:22.966355+00:00
-- url     : https://prove2.me/submissions/439d4749-5c99-462c-96a2-54c5fc509b52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.AbMulNSt
variable {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] {g n : ℕ}
omit [IsAlgClosed k]
namespace GlobalTheory.Published.AbMulNSt
theorem _root_.solution (n : ℕ) : IsAbelianScheme (𝟙_ (Over (Sp k))) ∧
    SmoothOfRelativeDimension 0 (𝟙_ (Over (Sp k))).hom ∧
    Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ 𝟙_ (Over (Sp k))) // x ^ n = 1} = n ^ (2 * 0) := by
  refine ⟨⟨inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact inferInstanceAs (Smooth (𝟙 (Sp k)))
  · exact inferInstanceAs (IsProper (𝟙 (Sp k)))
  · change GeometricallyConnected (𝟙 (Sp k))
    refine ⟨fun K _ y Z fst snd H => ?_⟩
    have : IsIso snd := H.isIso_snd_of_isIso
    exact snd.homeomorph.symm.surjective.connectedSpace snd.homeomorph.symm.continuous
  · exact inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 (Sp k)))
  · have : Unique {x : (𝟙_ (Over (Sp k)) ⟶ 𝟙_ (Over (Sp k))) // x ^ n = 1} :=
      ⟨⟨⟨1, one_pow n⟩⟩, fun x => Subtype.ext (toUnit_unique _ _)⟩
    rw [Nat.card_unique, mul_zero, pow_zero]
end GlobalTheory.Published.AbMulNSt
