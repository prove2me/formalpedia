-- Prove2me | solution 1 for GlobalTheory.DescentPairing.interchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:10:50.552797+00:00
-- url     : https://prove2.me/submissions/796eeebe-9042-4901-8cc5-32f7d835e4ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DescentPairing
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h
namespace GlobalTheory.DescentPairing
theorem _root_.solution (p q r s x : A) :
    θ (p * q) (r * s) x * θ p q x * θ r s x = θ (p * r) (q * s) x * θ p r x * θ q s x := by
  have a := h.coc p q (r * s) x
  have b := h.coc q r s x
  have c := h.coc r q s x
  have d := h.coc p r (q * s) x
  rw [mul_comm r q, h.s01 r q] at c
  rw [mul_left_comm r q s] at d
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a' := E a; have b' := E b; have c' := E c; have d' := E d
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a' - b' + c' - d'
end GlobalTheory.DescentPairing
