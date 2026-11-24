-- Prove2me | solution 1 for GlobalTheory.SelfCube.semicharacter_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:56:03.103809+00:00
-- url     : https://prove2.me/submissions/49ebd941-b99b-4278-9bff-5bb39f142f5c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Theorems.Thm_GlobalTheory_SelfCube_herm_add_left
import Theorems.Thm_GlobalTheory_SelfCube_herm_add_right
import Theorems.Thm_GlobalTheory_SelfCube_herm_zero_left
import Theorems.Thm_GlobalTheory_SelfCube_herm_conj
import Theorems.Thm_GlobalTheory_SelfCube_exp_pi_I_int
import Theorems.Thm_GlobalTheory_SelfCube_exists_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
open GlobalTheory.CubeValues
namespace GlobalTheory.SelfCube
theorem _root_.solution (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) {g : ℕ} (u : HolUnif A L g) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (χ : u.Λ → ℂ)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z =
      (χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l)) * u.fr i (z + l))
    (l m : u.Λ) (n : ℤ) (hn : (n : ℝ) = (hermForm Hm l m).im) :
    χ (l + m) = χ l * χ m * (-1) ^ n := by
  obtain ⟨i, hi⟩ := exists_chart hv hL u 0
  have hper : ∀ (a : u.Λ) z, u.ex (z + a) = u.ex z := fun a z => by
    rw [u.ex_add, (u.ker a).2 a.2, _root_.mul_one]
  have hne : u.fr i (0 + (l : Fin g → ℂ) + m) ≠ 0 := u.fr_ne i _ (by rw [hper m, hper l]; exact hi)
  have h1 := hfr (l + m) i 0 hi
  have h2 := hfr l i 0 hi
  have h3 := hfr m i (0 + l) (by rw [hper l]; exact hi)
  rw [Submodule.coe_add, ← add_assoc] at h1
  rw [h3] at h2
  have key := mul_right_cancel₀ hne (h1.symm.trans (h2.trans (_root_.mul_assoc _ _ _).symm))
  simp only [herm_zero_left, mul_zero, zero_add] at key
  have hsum : hermForm Hm (↑l + ↑m) (↑l + ↑m) = hermForm Hm l l + hermForm Hm l m +
      starRingEnd ℂ (hermForm Hm l m) + hermForm Hm m m := by
    rw [herm_add_left, herm_add_right, herm_add_right, ← herm_conj Hm hH]; ring
  rw [hsum] at key
  have hc : hermForm Hm l m - starRingEnd ℂ (hermForm Hm l m) =
      2 * ((hermForm Hm l m).im : ℂ) * I := by
    rw [Complex.sub_conj]; push_cast; ring
  have hn' : (n : ℂ) = ((hermForm Hm l m).im : ℂ) := by exact_mod_cast hn
  have hX := Complex.exp_ne_zero (π / 2 * (hermForm Hm l l + hermForm Hm l m +
      starRingEnd ℂ (hermForm Hm l m) + hermForm Hm m m))
  rw [← exp_pi_I_int n]
  refine mul_right_cancel₀ hX ?_
  rw [key]
  have hE : cexp (↑π / 2 * hermForm Hm ↑l ↑l) * cexp (↑π * hermForm Hm ↑l ↑m + ↑π / 2 * hermForm Hm ↑m ↑m) =
      cexp (↑π * I * ↑n) * cexp (↑π / 2 * (hermForm Hm ↑l ↑l + hermForm Hm ↑l ↑m +
      starRingEnd ℂ (hermForm Hm ↑l ↑m) + hermForm Hm ↑m ↑m)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination ((π : ℂ) / 2) * hc - ((π : ℂ) * I) * hn'
  linear_combination (χ l * χ m) * hE
end GlobalTheory.SelfCube
