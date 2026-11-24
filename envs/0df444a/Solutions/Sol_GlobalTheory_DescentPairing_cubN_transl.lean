-- Prove2me | solution 1 for GlobalTheory.DescentPairing.cubN_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:26.925622+00:00
-- url     : https://prove2.me/submissions/d7ba5715-0922-4375-8312-f2291eea9a89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing
import Theorems.Thm_GlobalTheory_DescentPairing_cubN_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add


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
theorem _root_.solution (k : ℕ) (y w x : A) (hy : y ^ k = 1) :
    cubN θ k 1 (y * w) x * cubN θ k 1 y w = cubN θ k 1 w x * cubN θ k 1 y (x * w) := by
  have a := cubN_mul h k y w x
  have b := h.N_add k 1 y x w
  rw [hy, h.face, _root_.one_mul] at a
  rw [hy, _root_.mul_one (1 : A), h.face, _root_.one_mul, _root_.mul_one, h.s12 y x w] at b
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  simp only [ofMul_mul] at a' b' ⊢
  linear_combination (norm := abel) a' - b'
end GlobalTheory.DescentPairing
