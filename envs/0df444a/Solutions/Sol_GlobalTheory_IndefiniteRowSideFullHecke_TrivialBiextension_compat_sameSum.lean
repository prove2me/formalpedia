-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension.compat_sameSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:03.177477+00:00
-- url     : https://prove2.me/submissions/4fce6290-1697-4747-9097-00c89260be71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_sum_ulift_three

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{u}} (G : Over S) [GrpObj G]
namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
theorem _root_.solution {T : Over S} (a a' b b' : T ⟶ G) :
    LB.SameSum
      (Sum.elim (law₂φ G (padd G a a') b b') (Sum.elim (law₁φ G a a' b) (law₁φ G a a' b')))
      (Sum.elim lawε (Sum.elim lawε lawε))
      (Sum.elim (law₁φ G a a' (padd G b b')) (Sum.elim (law₂φ G a b b') (law₂φ G a' b b')))
      (Sum.elim lawε (Sum.elim lawε lawε)) := by
  intro ψ
  classical
  obtain ⟨c, hc⟩ : ∃ c : (T.left ⟶ (G2 G).left) → ℤ, ∀ (χ) (n : ℤ) (d : Decidable (χ = ψ)),
      (@ite _ (χ = ψ) d n 0) = n * c χ :=
    ⟨fun χ => if χ = ψ then 1 else 0, fun χ n d => by split_ifs <;> simp [*]⟩
  simp only [hc]
  simp only [Fintype.sum_sum_type, sum_ulift_three, Sum.elim_inl, Sum.elim_inr, law₁φ, law₂φ, lawε,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
