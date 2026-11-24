-- Prove2me | solution 1 for GlobalTheory.SymLiftFrame.sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:05.113231+00:00
-- url     : https://prove2.me/submissions/1916faf2-266b-4e08-b01c-0a580b8351d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_of
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_ne_zero
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_corr_one
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_symGen
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_theta
import Theorems.Thm_GlobalTheory_SymLiftFrame_exists_choice
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_pairChart_iff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_snd_comp
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_translT
import Theorems.Thm_GlobalTheory_ThetaFn_exists_isPullConst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SymLiftFrame
open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ} {c : ℂ}
namespace GlobalTheory.SymLiftFrame
theorem _root_.solution (hL : L.IsLB) {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    (hc : HasAnConst u p Hm Θ x c) {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen)
    (h : LB.Gen.Corr L _ _ _ _ (symGen A L k Θ nu) (LB.oneGen L)) : c ^ 2 = 1 := by
  obtain ⟨J, hJ⟩ := exists_choice hL
  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hneg : ∀ z, u.ex (-z) = u.ex z ≫ ι := fun z => by
    rw [GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]
    refine (eq_inv_of_mul_eq_one_right ?_)
    rw [← u.ex_add, add_neg_cancel, hex0]
  have hxi : p ≫ Θ.pt⁻¹ = u.ex (-x) := by
    rw [GrpObj.comp_inv, hc.1, hneg, GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]
  have e2 : exAt u p 0 ≫ (negT A T).left = exAt u p 0 := by
    unfold negT exAt
    rw [← Over.comp_left, comp_lift, lift_fst, ← Category.assoc, lift_snd, ← hneg, neg_zero]
  have hΦ : ∀ z, exAt u p z ≫ (snd T A ≫ ι).left = (u.ex (-z)).left := fun z =>
    exAt_snd_comp p (hneg z)
  obtain ⟨-, -, cν, hcν0, hcν⟩ := exists_isPullConst hL hAH (Φ := -LinearMap.id)
    (fun z => by simpa only [LinearMap.neg_apply, LinearMap.id_apply] using hΦ z) (a := k) (b := k) hnu
  have hN : ∀ z, cval (L := L) nu (exAt u p z) J * u.fr (J (u.ex (-z)).left) (-z) ^ k =
      cν * u.fr (J (u.ex z).left) z ^ k := fun z => by
    rw [cval_of nu _ J ![J (u.ex z).left, J (u.ex (-z)).left] (fun i => ?_)]
    · exact hcν _ z ((exAt_mem_pairChart_iff (hΦ z) _).2 ⟨hJ _, hJ _⟩)
    · fin_cases i
      · show J ((lift p (u.ex z)).left ≫ (snd T A).left) = J (u.ex z).left
        rw [← Over.comp_left, lift_snd]
      · exact congrArg J (hΦ z)
  have hs := cval_corr_one hJ h (exAt u p 0)
  rw [cval_symGen hJ Θ nu, exAt_translT u hxi 0, zero_add, e2] at hs
  have t1 := cval_theta hJ hc (-x)
  have t2 := cval_theta hJ hc 0
  have p1 := hN 0
  have p2 := hN (-x)
  rw [neg_add_cancel] at t1
  rw [zero_add] at t2
  rw [neg_zero] at p1
  rw [neg_neg] at p2
  have hf : fockFactor Hm k x (-x) * fockFactor Hm k x 0 = 1 := by
    unfold fockFactor hermForm
    rw [← Complex.exp_add, neg_dotProduct, zero_dotProduct, ← Complex.exp_zero]
    congr 1
    ring
  have hF0 : u.fr (J (u.ex 0).left) 0 ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ (hJ _))
  have hFm : u.fr (J (u.ex (-x)).left) (-x) ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ (hJ _))
  have hn2 : cval (L := L) nu (exAt u p (-x)) J ≠ 0 := cval_ne_zero hJ nu _
  have hn1 : cval (L := L) nu (exAt u p 0) J = cν := mul_right_cancel₀ hF0 p1
  rw [hn1] at hs
  have e2' : cval (L := L) Θ.φ (exAt u p (-x)) J * cval (L := L) Θ.φ (exAt u p 0) J * cν =
      cval (L := L) nu (exAt u p (-x)) J := by
    have hi := mul_inv_cancel₀ hn2
    linear_combination (cval (L := L) nu (exAt u p (-x)) J) * hs -
      (cval (L := L) Θ.φ (exAt u p (-x)) J * cν * cval (L := L) Θ.φ (exAt u p 0) J) * hi
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hFm hF0) hcν0)
  linear_combination (-cν) * ((cval (L := L) Θ.φ (exAt u p 0) J * u.fr (J (u.ex x).left) x ^ k) * t1 +
      (c * fockFactor Hm k x (-x) * u.fr (J (u.ex (-x)).left) (-x) ^ k) * t2 +
      (c ^ 2 * u.fr (J (u.ex (-x)).left) (-x) ^ k * u.fr (J (u.ex 0).left) 0 ^ k) * hf) +
    (u.fr (J (u.ex 0).left) 0 ^ k * u.fr (J (u.ex x).left) x ^ k) * e2' + u.fr (J (u.ex 0).left) 0 ^ k * p2
end GlobalTheory.SymLiftFrame
