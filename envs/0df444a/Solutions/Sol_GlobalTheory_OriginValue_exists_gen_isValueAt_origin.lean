-- Prove2me | solution 1 for GlobalTheory.OriginValue.exists_gen_isValueAt_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:26.888799+00:00
-- url     : https://prove2.me/submissions/00c885d6-d153-4e9d-b245-9f5d73d72da0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenIsValueAtOrigin
import Theorems.Thm_P2M_GlobalTheory_OriginValue_eq_of_valAt__eq_of_isIso_0aa59719e453
import Theorems.Thm_GlobalTheory_OriginValue_top_le_preimage_wchart_one
import Theorems.Thm_GlobalTheory_OriginValue_ex_zero
import Theorems.Thm_GlobalTheory_OriginValue_unitOrOne_val
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a
import Theorems.Thm_P2M_GlobalTheory_valAt__constFn_1b31686fad50
import Theorems.Thm_P2M_GlobalTheory_valAt__map_238ef0722272
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c
import Theorems.Thm_P2M_GlobalTheory_valAt__zpow_0be005735ec2


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
open GlobalTheory GlobalTheory.OriginValue
namespace GlobalTheory.OriginValue
theorem _root_.solution : ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (a : ℤ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T), ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)), τ.IsGen ∧ ∀ (s : LB.Sec (Out.LPow P.A P.L a T)) (f : (Fin P.g → ℂ) → ℂ), (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L a T).U j) (s.f j) = f z * u.fr (j 0) z ^ (a : ℤ)) → Out.IsValueAt P.A P.L a s 1 τ (constFn T.hom ⊤ (f 0)) := by
  intro P u a T _ p
  let x : Sp ℂ ⟶ T.left := p.left
  have hx : x ≫ T.hom = 𝟙 _ := Over.w p
  have : IsIso x := by
    have : x = inv T.hom := IsIso.eq_inv_of_inv_hom_id hx
    rw [this]; infer_instance
  have h1 : p ≫ (1 : T ⟶ P.A) = u.ex 0 := by
    rw [ex_zero, MonObj.comp_one]
  have h1' : x ≫ (1 : T ⟶ P.A).left = (u.ex 0).left := congrArg CommaMorphism.left h1
  have hch : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U (j 0) := fun j h => by
    have := top_le_preimage_wchart_one P.L _ x j h
    rwa [h1'] at this
  let τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)) :=
    ⟨fun j => Units.map (constFnHom T.hom _).toMonoidHom (unitOrOne (u.fr (j 0) 0) ^ a)⟩
  have hτ : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      valAt' x (LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j) (τ.s j).val = u.fr (j 0) 0 ^ a := fun j h => by
    refine (valAt'_constFn x T.hom hx _ _ h).trans ?_
    rw [Units.val_zpow_eq_zpow_val, unitOrOne_val (u.fr_ne _ _ (hch j h))]
  refine ⟨τ, fun i j => ?_, fun s f hs j => ?_⟩
  · apply Units.ext
    refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    obtain ⟨hi, hj⟩ := (top_le_preimage_inf x _ _).1 h
    rw [Units.val_mul, valAt'_mul]
    refine ((valAt'_res x inf_le_left _ h).trans (hτ i hi)).trans ?_
    have e2 := (valAt'_res x inf_le_right _ h).trans (hτ j hj)
    refine Eq.trans ?_ (congrArg _ e2.symm)
    have hij : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.U (i 0) ⊓ P.L.U (j 0)) :=
      (top_le_preimage_inf (u.ex 0).left _ _).2 ⟨hch i hi, hch j hj⟩
    rw [u.fr_compat _ _ _ hij, mul_zpow]
    congr 1
    simp only [LB.LinComb, Fin.prod_univ_one]
    refine Eq.trans ?_ (valAt'_zpow x h _ a).symm
    congr 1
    refine Eq.trans ?_ (valAt'_res x _ _ h).symm
    refine Eq.trans ?_ (valAt'_comp x (1 : T ⟶ P.A).left (P.L.U (i 0) ⊓ P.L.U (j 0)) (P.L.g (i 0) (j 0)).val).symm
    rw [h1']
  · refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    rw [valAt'_mul, hτ j h, valAt'_map x _ _ h, valAt'_map x _ _ h, valAt'_constFn x T.hom hx _ _ le_top]
    refine (valAt'_comp x _ _ _).trans ?_
    have h2 : p ≫ Out.ptSecT P.A (1 : T ⟶ P.A) = lift p (u.ex 0) := by
      rw [Out.ptSecT, comp_lift, Category.comp_id, h1]
    have h2' : x ≫ (Out.ptSecT P.A (1 : T ⟶ P.A)).left = (lift p (u.ex 0)).left := congrArg CommaMorphism.left h2
    rw [h2']
    exact hs j 0 (hch j h)
end GlobalTheory.OriginValue
