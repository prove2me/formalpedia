-- Prove2me | solution 1 for GlobalTheory.SharpWeil.rel_biprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:29.822723+00:00
-- url     : https://prove2.me/submissions/3f236912-6406-469c-9abd-341706c186d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CommutatorPairingE8SharpLevelPoints
import Theorems.Thm_GlobalTheory_SharpWeil_rel_prod
import Theorems.Thm_GlobalTheory_SharpWeil_prod_zpow_pow
import Theorems.Thm_P2M_GlobalTheory_SharpWeil_zpow_sum__176ec8fcdc9e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpWeil
variable {G C : Type} [CommGroup G] [CommGroup C] {k : ℕ}
namespace GlobalTheory.SharpWeil
theorem _root_.solution {R : G → G → C → Prop} (hex : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, R x y c)
    (hmul : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c'))
    (hsymm : ∀ x y c, R x y c → R y x c⁻¹) {I : Type} [Fintype I] (q : I → G) (ζ : C) (ω : I → I → ℤ)
    (hq : ∀ i, q i ^ k = 1) (h : ∀ i j, R (q i) (q j) (ζ ^ ω i j)) (a b : I → ℤ) :
    R (∏ i, q i ^ a i) (∏ i, q i ^ b i) (ζ ^ ∑ i, ∑ j, a i * b j * ω i j) := by
  have hy : (∏ j, q j ^ b j) ^ k = 1 := prod_zpow_pow q hq b
  have hrow : ∀ i, R (q i) (∏ j, q j ^ b j) (ζ ^ ∑ j, b j * ω i j) := by
    intro i
    have H : R (∏ j, q j ^ b j) (q i) (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j) :=
      rel_prod (R := fun x c => R x (q i) c) (fun x hx => hex x (q i) hx (hq i))
        (fun x x' c c' h1 h2 => hmul x x' (q i) c c' h1 h2) Finset.univ q (fun j => (ζ ^ ω i j)⁻¹) hq
        (fun j => hsymm _ _ _ (h i j)) b
    have e : ζ ^ ∑ j, b j * ω i j = (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j)⁻¹ := by
      rw [zpow_sum', ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [inv_zpow, inv_inv, ← zpow_mul, mul_comm (b j)]
    rw [e]
    exact hsymm _ _ _ H
  have H : R (∏ i, q i ^ a i) (∏ j, q j ^ b j) (∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i) :=
    rel_prod (R := fun x c => R x (∏ j, q j ^ b j) c) (fun x hx => hex x _ hx hy)
      (fun x x' c c' h1 h2 => hmul x x' _ c c' h1 h2) Finset.univ q (fun i => ζ ^ ∑ j, b j * ω i j) hq hrow a
  have e : ζ ^ ∑ i, ∑ j, a i * b j * ω i j = ∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i := by
    rw [zpow_sum']
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact H
end GlobalTheory.SharpWeil
