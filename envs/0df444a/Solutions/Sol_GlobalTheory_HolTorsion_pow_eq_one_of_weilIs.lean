-- Prove2me | solution 1 for GlobalTheory.HolTorsion.pow_eq_one_of_weilIs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:21.827656+00:00
-- url     : https://prove2.me/submissions/9506ba2b-5a17-4899-8da4-d73f42519d17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionEqAndWeilIsOfIsHolTo

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolTorsion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
namespace GlobalTheory.HolTorsion
theorem _root_.solution (hW : Out.WeilSt) {X : Scheme.{0}} [IsLocallyNoetherian X] (P : Out.PolAV X) (k : ℕ)
    {T : Over X} {u v : T ⟶ P.A} (hu : u ^ k = 1) (hv : v ^ k = 1) {e : Γ(T.left, ⊤)ˣ}
    (he : Out.WeilIs P.A P.L k u v e) : e ^ k = 1 := by
  obtain ⟨h₁, h₂, -⟩ := hW X P k T
  obtain ⟨d, hd, hd'⟩ := h₁ 1 v (one_pow k) hv
  have hdd := h₂ 1 1 v d d hd hd
  rw [_root_.mul_one] at hdd
  obtain rfl : d = 1 := mul_eq_left.1 (hd' _ hdd)
  have key : ∀ n : ℕ, Out.WeilIs P.A P.L k (u ^ n) v (e ^ n) := fun n => by
    induction n with
    | zero => simpa only [pow_zero] using hd
    | succ n ih => simpa only [pow_succ] using h₂ _ _ _ _ _ ih he
  have hk := key k
  rw [hu] at hk
  exact hd' _ hk
end GlobalTheory.HolTorsion
