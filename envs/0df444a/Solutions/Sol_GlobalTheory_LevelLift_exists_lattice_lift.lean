-- Prove2me | solution 1 for GlobalTheory.LevelLift.exists_lattice_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:51.677284+00:00
-- url     : https://prove2.me/submissions/40b9c23c-9718-4cb4-bec5-bff57a200a3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticeLiftOfLevelSection
import Theorems.Thm_GlobalTheory_LevelLift_exists_linear_lift
import Theorems.Thm_GlobalTheory_LevelLift_dvd_sub_of_exp_eq
import Theorems.Thm_GlobalTheory_weilIs_unique_fieldPoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open GlobalTheory GlobalTheory.LevelLift
namespace GlobalTheory.LevelLift
theorem _root_.solution : ∀ (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (u : HolUnif P.A P.L h) (Ef : LinearMap.BilinForm ℤ u.Λ), 0 < k → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → (∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) → (∀ (x y : u.Λ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((k : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e)) → ∃ l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] u.Λ, (∀ a, lev a = u.ex ((k : ℂ)⁻¹ • (l a : Fin h → ℂ))) ∧ ∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b := by
  intro h k P lev u Ef hk hl hp hW hE
  obtain ⟨l, hlift⟩ := exists_linear_lift u.ex u.ex_add u.ex_onto u.Λ u.ker k hk lev hl hp
  refine ⟨l, hlift, fun a b => ?_⟩
  have h1 := hW a b (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  have h2 := hE (l a) (l b) (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  rw [← hlift a, ← hlift b] at h2
  have h3 := GlobalTheory.weilIs_unique_fieldPoint _ P.A P.L P.isLB ℂ (𝟙 _) k (lev a) (lev b) _ _ h1 h2
  exact dvd_sub_of_exp_eq k hk _ _ (congrArg Units.val h3)
end GlobalTheory.LevelLift
