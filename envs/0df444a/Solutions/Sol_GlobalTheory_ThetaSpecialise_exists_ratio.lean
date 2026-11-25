-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:21:00.701081+00:00
-- url     : https://prove2.me/submissions/aa970177-4882-48ef-b3ab-d5222a915918

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {S F F' N V V' : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Field F']
  [AddCommGroup N] [Module S N] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution {fS : S →+* F} {π : S →+* F'} (hf : Function.Injective fS) (mv : N →ₛₗ[fS] V) (mv' : N →ₛₗ[π] V')
    (ind : ∀ (n : ℕ) (c : Fin n → F), (∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) →
      ∀ a : Fin n → N, ∑ i, c i • mv (a i) = 0 → ∀ i, a i = 0)
    {I : Type} (a b : I → N) (l : F) (h : ∀ i, mv (a i) = l • mv (b i)) (ha : ∃ i, mv' (a i) ≠ 0)
    (hb : ∃ i, mv' (b i) ≠ 0) : ∃ l' : F', l' ≠ 0 ∧ ∀ i, mv' (a i) = l' • mv' (b i) := by
  have inj : ∀ x y, mv x = mv y → x = y := fun x y e => sub_eq_zero.1 (ind 1 (fun _ => 1) (fun a ha i => by
    rw [Fin.sum_univ_one, _root_.mul_one] at ha
    rw [Subsingleton.elim i 0]; exact hf (ha.trans (map_zero _).symm)) (fun _ => x - y)
    (by rw [Fin.sum_univ_one, one_smul, map_sub, e, sub_self]) 0)
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  by_cases H : ∀ a : Fin 2 → S, ∑ i, fS (a i) * ![1, -l] i = 0 → ∀ i, a i = 0
  · refine absurd ?_ hi
    have e : a i = 0 := ind 2 _ H ![a i, b i] (by simp [Fin.sum_univ_two, h]) 0
    rw [e, map_zero]
  · push_neg at H
    obtain ⟨u, hu, m, hm⟩ := H
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, mul_neg] at hu
    have inj' : ∀ x, fS x = 0 → x = 0 := fun x e => hf (e.trans (map_zero _).symm)
    have h1 : u 1 ≠ 0 := fun e => by
      rw [e, map_zero, zero_mul, neg_zero, add_zero] at hu
      fin_cases m
      exacts [hm (inj' _ hu), hm e]
    have h1' : fS (u 1) ≠ 0 := fun e => h1 (inj' _ e)
    obtain ⟨t, ht | ht⟩ := ValuationRing.cond (u 0) (u 1)
    · have h0 : fS (u 0) ≠ 0 := fun e => h1' (by rw [← ht, map_mul, e, zero_mul])
      have e : fS t * l = 1 := mul_left_cancel₀ h0 (by rw [← ht, map_mul] at hu; linear_combination -hu)
      have k : ∀ i, mv' (b i) = π t • mv' (a i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, smul_smul, e, one_smul]))
      have p : π t ≠ 0 := fun e => hj (by rw [k, e, zero_smul])
      exact ⟨(π t)⁻¹, inv_ne_zero p, fun i => by rw [k, smul_smul, inv_mul_cancel₀ p, one_smul]⟩
    · have e : fS t = l := mul_left_cancel₀ h1' (by rw [← ht, map_mul] at hu; linear_combination hu)
      have k : ∀ i, mv' (a i) = π t • mv' (b i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, e]))
      exact ⟨π t, fun e => hi (by rw [k, e, zero_smul]), k⟩
end GlobalTheory.ThetaSpecialise
