-- Prove2me | solution 1 for GlobalTheory.SympBasis.injective_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:47.323067+00:00
-- url     : https://prove2.me/submissions/cda37646-2b4c-4cd4-81f1-975b49dd1993

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasis
import Theorems.Thm_GlobalTheory_SympBasis_eq_of_sum_stdSymp
import Theorems.Thm_GlobalTheory_SympBasis_rel_prod
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
namespace GlobalTheory.SympBasis
private theorem zpow_finset_sum_divisor {U : Type} [CommGroup U] (z : U) {I : Type} (s : Finset I) (f : I → ℤ) :
    z ^ (∑ i ∈ s, f i) = ∏ i ∈ s, z ^ f i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro j t hj ih
  rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]
end GlobalTheory.SympBasis
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SympBasis
namespace GlobalTheory.SympBasis
theorem _root_.solution {M U : Type} [CommMonoid M] [CommGroup U] (W : M → M → U → Prop) (k : ℕ) [NeZero k]
    (hu : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) {g : ℕ} (p : Fin (2 * g) → M)
    (hp : ∀ i, p i ^ k = 1) (z : U) (hz : IsPrimitiveRoot z k)
    (hw : ∀ i j, W (p i) (p j) (z ^ Out.stdSymp g i j)) :
    Function.Injective fun c : Fin (2 * g) → ZMod k => ∏ i, p i ^ (c i).val := by
  classical

  have hone : ∀ y, y ^ k = 1 → W 1 y 1 := by
    intro y hy
    obtain ⟨c, hc, huniq⟩ := hu 1 y (one_pow k) hy
    have h2 : W 1 y (c * c) := by simpa using hm 1 1 y c c hc hc
    have hcc : c * c = c := huniq _ h2
    have hc1 : c = 1 := by simpa using hcc
    rw [hc1] at hc
    exact hc

  let e : (Fin (2 * g) → ZMod k) → Fin (2 * g) → ℤ := fun c j => ∑ i, Out.stdSymp g i j * ((c i).val : ℤ)
  have hW : ∀ (c : Fin (2 * g) → ZMod k) j, W (∏ i, p i ^ (c i).val) (p j) (z ^ e c j) := by
    intro c j
    have h := rel_prod (fun x v => W x (p j) v) (hone _ (hp j))
      (fun x x' v v' hx hx' => hm x x' (p j) v v' hx hx') Finset.univ p
      (fun i => z ^ Out.stdSymp g i j) (fun i => (c i).val) (fun i => hw i j)
    have hz' : (∏ i, (z ^ Out.stdSymp g i j) ^ (c i).val) = z ^ e c j := by
      simp only [e, zpow_finset_sum_divisor]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul]
    simpa only [hz'] using h
  have htors : ∀ c : Fin (2 * g) → ZMod k, (∏ i, p i ^ (c i).val) ^ k = 1 := by
    intro c
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, hp i, one_pow]
  intro c c' hcc
  have hcc' : (∏ i, p i ^ (c i).val) = ∏ i, p i ^ (c' i).val := hcc
  have key : ∀ j, z ^ e c j = z ^ e c' j := by
    intro j
    obtain ⟨w, _, huniq⟩ := hu _ (p j) (htors c) (hp j)
    have h1 := huniq _ (hW c j)
    have h2 := huniq _ (hcc' ▸ hW c' j)
    rw [h1, h2]
  apply eq_of_sum_stdSymp (R := ZMod k) c c'
  intro j
  have hd : ((e c j : ℤ) : ZMod k) = ((e c' j : ℤ) : ZMod k) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← hz.zpow_eq_one_iff_dvd, zpow_sub, key j, mul_inv_cancel]
  simpa [e, mul_comm] using hd
end GlobalTheory.SympBasis
