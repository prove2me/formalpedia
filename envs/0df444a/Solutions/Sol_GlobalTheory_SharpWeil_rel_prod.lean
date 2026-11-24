-- Prove2me | solution 1 for GlobalTheory.SharpWeil.rel_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:47:00.518794+00:00
-- url     : https://prove2.me/submissions/ab77677b-f441-4366-895b-e92d754cb397

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CommutatorPairingE8SharpLevelPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.SharpWeil
section Abstract
variable {G C : Type} [CommGroup G] [CommGroup C] {k : ℕ}
private theorem rel_one_one {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) : R 1 1 := by
  obtain ⟨c, hc, hu⟩ := hex 1 (one_pow k)
  have hcc : c * c = c := hu _ (by simpa using hmul 1 1 c c hc hc)
  have hc1 : c = 1 := by simpa using hcc
  rwa [hc1] at hc
private theorem rel_inv_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (hx : x ^ k = 1)
    (h : R x c) : R x⁻¹ c⁻¹ := by
  obtain ⟨d, hd, -⟩ := hex x⁻¹ (by rw [inv_pow, hx, inv_one])
  have h1 : R 1 (c * d) := by simpa using hmul _ _ _ _ h hd
  obtain ⟨e, -, hu⟩ := hex 1 (one_pow k)
  have hcd : c * d = 1 := (hu _ h1).trans (hu _ (rel_one_one hex hmul)).symm
  rwa [eq_inv_of_mul_eq_one_right hcd] at hd
private theorem rel_pow_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (h : R x c) (n : ℕ) :
    R (x ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using rel_one_one hex hmul
  | succ n ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h
private theorem rel_zpow_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (hx : x ^ k = 1)
    (h : R x c) (n : ℤ) : R (x ^ n) (c ^ n) := by
  cases n with
  | ofNat n => simpa using rel_pow_of_rel hex hmul h n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    exact rel_inv_of_rel hex hmul (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) (rel_pow_of_rel hex hmul h (n + 1))
end Abstract
end GlobalTheory.SharpWeil
namespace GlobalTheory
end GlobalTheory
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpWeil
variable {G C : Type} [CommGroup G] [CommGroup C] {k : ℕ}
namespace GlobalTheory.SharpWeil
theorem _root_.solution {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {I : Type} (s : Finset I) (q : I → G) (c : I → C)
    (hq : ∀ i, q i ^ k = 1) (h : ∀ i, R (q i) (c i)) (a : I → ℤ) :
    R (∏ i ∈ s, q i ^ a i) (∏ i ∈ s, c i ^ a i) := by
  classical
  refine Finset.induction_on s (by simpa using rel_one_one hex hmul) ?_
  intro i s hi ih
  rw [Finset.prod_insert hi, Finset.prod_insert hi]
  exact hmul _ _ _ _ (rel_zpow_of_rel hex hmul (hq i) (h i) (a i)) ih
end GlobalTheory.SharpWeil
