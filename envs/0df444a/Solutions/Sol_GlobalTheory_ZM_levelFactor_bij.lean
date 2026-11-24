-- Prove2me | solution 1 for GlobalTheory.ZM.levelFactor_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:19:13.570872+00:00
-- url     : https://prove2.me/submissions/53ea671c-308e-4f63-8d2a-8ac0d6c3c15f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelOnFactorOfEighthPowerAbelianScheme
import Theorems.Thm_GlobalTheory_ZM_levelFactor_comp
import Theorems.Thm_GlobalTheory_ZM_levelFactor_torsion

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
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (hk : 0 < k) (ht : ∀ i, P i ^ k = 1)
    (hπ : ∀ y : Fin m → H, ∃! x : G, ∀ u, π u x = y u)
    (hb : ∀ y : G, y ^ k = 1 → ∃! c : Fin n → ZMod k, (List.ofFn fun i => P i ^ (c i).val).prod = y) :
    (∀ x, L x = 1 ↔ ∃ y, x = k • y) ∧ ∀ y : H, y ^ k = 1 → ∃ x, L x = y := by
  have : NeZero k := ⟨hk.ne'⟩
  have hcomp := levelFactor_comp bas P π L hL hP
  have htor := levelFactor_torsion u bas P π L hL hP k ht
  have L0 : L 0 = 1 := mul_left_cancel (a := L 0) (by rw [← hL, add_zero, _root_.mul_one])
  have hsm : ∀ (j : ℕ) (x : Λ), L (j • x) = L x ^ j := by
    intro j x
    induction j with
    | zero => rw [zero_smul, L0, pow_zero]
    | succ j ih => rw [succ_nsmul, hL, ih, pow_succ]
  have hone : ∀ a : G, (∀ v, π v a = 1) → a = 1 := by
    intro a ha
    obtain ⟨x, -, hx⟩ := hπ (fun _ => 1)
    exact (hx a ha).trans (hx 1 (fun v => map_one _)).symm
  have hred : ∀ w : Fin n → ℤ,
      ∏ i, P i ^ w i = (List.ofFn fun i => P i ^ ((w i : ZMod k).val)).prod := by
    intro w
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_eq_zpow_emod (w i) (n := (k : ℤ)) (by rw [zpow_natCast]; exact ht i),
      ← ZMod.val_intCast, zpow_natCast]
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ : ∃ w, bas w = Pi.single u x := ⟨_, bas.apply_symm_apply _⟩
    have hg : ∏ i, P i ^ w i = 1 := hone _ fun v => by
      rw [hcomp, hw]
      by_cases hv : v = u
      · subst hv; rw [Pi.single_eq_same, hx]
      · rw [Pi.single_eq_of_ne hv, L0]
    obtain ⟨c0, -, huniq⟩ := hb 1 (one_pow _)
    have e1 := huniq (fun i => (w i : ZMod k)) ((hred w).symm.trans hg)
    have e2 := huniq 0 (by simp)
    have hdvd : ∀ i, (k : ℤ) ∣ w i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun (e1.trans e2.symm) i)
    choose w' hw' using hdvd
    have hww : w = (k : ℤ) • w' := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, hw' i]
    refine ⟨bas w' u, ?_⟩
    calc x = bas w u := by rw [hw, Pi.single_eq_same]
      _ = ((k : ℤ) • bas w') u := by rw [hww, map_zsmul]
      _ = k • bas w' u := by rw [Pi.smul_apply, natCast_zsmul]
  · rintro ⟨y, rfl⟩
    rw [hsm, htor]
  · obtain ⟨a, ha, -⟩ := hπ (Pi.mulSingle u y)
    have hak : a ^ k = 1 := hone _ fun v => by
      rw [map_pow, ha]
      by_cases hv : v = u
      · subst hv; rw [Pi.mulSingle_eq_same, hy]
      · rw [Pi.mulSingle_eq_of_ne hv, one_pow]
    obtain ⟨c, hc, -⟩ := hb a hak
    refine ⟨bas (fun i => ((c i).val : ℤ)) u, ?_⟩
    have hprod : ∏ i, P i ^ ((c i).val : ℤ) = a := by
      rw [← hc, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => zpow_natCast _ _
    rw [← hcomp, hprod, ha, Pi.mulSingle_eq_same]
end GlobalTheory.ZM
