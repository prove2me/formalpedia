-- Prove2me | solution 1 for GlobalTheory.DescentPairing.cubN_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:49:27.007112+00:00
-- url     : https://prove2.me/submissions/2aafdb9e-8bcc-48ae-9bfe-d68138fc3d6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing
import Theorems.Thm_GlobalTheory_DescentPairing_interchange

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
theorem _root_.solution (k : ℕ) (a b x : A) :
    cubN θ k 1 (a * b) x * θ a b x ^ k = θ (a ^ k) (b ^ k) x * cubN θ k 1 a x * cubN θ k 1 b x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := interchange h (a ^ k) (b ^ k) a b x
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ a, pow_succ b, pow_succ (θ a b x), mul_pow a b k]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'
end GlobalTheory.DescentPairing
