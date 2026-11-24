-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.cub_eq_pot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:08:27.245719+00:00
-- url     : https://prove2.me/submissions/00f38b0b-8590-4250-aa9a-cde5297a87ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
import Theorems.Thm_GlobalTheory_UT_PhiOrder_pot_zero
import Theorems.Thm_GlobalTheory_UT_PhiOrder_pot_one
import Theorems.Thm_GlobalTheory_UT_PhiOrder_pot_two
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.PhiOrder
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace GlobalTheory.UT.PhiOrder
theorem _root_.solution (h : IsCub θ) (b : A) (i j l : ℕ) :
    Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) = Additive.ofMul (pot θ b (i + j + l)) - Additive.ofMul (pot θ b (i + j)) -
      Additive.ofMul (pot θ b (i + l)) - Additive.ofMul (pot θ b (j + l)) + Additive.ofMul (pot θ b i) +
      Additive.ofMul (pot θ b j) + Additive.ofMul (pot θ b l) := by
  set P : ℕ → Additive U := fun n => Additive.ofMul (pot θ b n) with hP
  have P0 : P 0 = 0 := pot_zero b
  have P1 : P 1 = 0 := pot_one b
  have P2 : P 2 = 0 := pot_two h b
  show _ = P (i + j + l) - P (i + j) - P (i + l) - P (j + l) + P i + P j + P l
  have step : ∀ l : ℕ, (∀ i, Additive.ofMul (θ (b ^ i) (b ^ 1) (b ^ l)) =
      P (i + 1 + l) - P (i + 1) - P (i + l) - P (1 + l) + P i + P 1 + P l) → ∀ j i,
      Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) =
        P (i + j + l) - P (i + j) - P (i + l) - P (j + l) + P i + P j + P l := by
    intro l H j
    induction j with
    | zero => intro i; rw [pow_zero, h.face₂, ofMul_one, add_zero, zero_add, P0]; abel
    | succ j ih =>
      intro i
      have c := congrArg Additive.ofMul (h.coc (b ^ i) (b ^ j) (b ^ 1) (b ^ l))
      rw [← pow_add, ← pow_add, ofMul_mul, ofMul_mul, H, H, ih] at c
      rw [← add_assoc i j 1]
      linear_combination (norm := abel) -c
  have base : ∀ i, Additive.ofMul (θ (b ^ i) (b ^ 1) (b ^ 1)) =
      P (i + 1 + 1) - P (i + 1) - P (i + 1) - P (1 + 1) + P i + P 1 + P 1 := by
    intro i
    have e₁ : P (i + 1 + 1) = P (i + 1) + Additive.ofMul (cubN θ (i + 1) 1 b b) := by
      simp only [hP, pot, Finset.prod_range_succ _ (i + 1), ofMul_mul]
    have e₂ : P (i + 1) = P i + Additive.ofMul (cubN θ i 1 b b) := by
      simp only [hP, pot, Finset.prod_range_succ _ i, ofMul_mul]
    have e₃ : Additive.ofMul (cubN θ (i + 1) 1 b b) = Additive.ofMul (cubN θ i 1 b b) +
        Additive.ofMul (θ (b ^ i) (b ^ 1) (b ^ 1)) := by
      simp only [cubN, Finset.prod_range_succ _ i, ofMul_mul, _root_.one_mul, pow_one]
    rw [show 1 + 1 = 2 from rfl, P2, P1]
    linear_combination (norm := abel) - e₁ + e₂ - e₃
  refine step l (fun i => ?_) j i
  rw [h.s12, step 1 base l i, add_right_comm i l 1, add_comm l 1]
  abel
end GlobalTheory.UT.PhiOrder
