-- Prove2me | solution 1 for GlobalTheory.PowUnif.exists_holUnif_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:36.370827+00:00
-- url     : https://prove2.me/submissions/e5fd9d78-6ec7-40c5-b084-7939f7a25593

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_le_wchart_iff
import Theorems.Thm_GlobalTheory_PowUnif_exists_chart
import Theorems.Thm_GlobalTheory_PowUnif_blockIn_apply
import Theorems.Thm_GlobalTheory_PowUnif_blockPr_blockIn
import Theorems.Thm_GlobalTheory_PowUnif_pow_hom_ext
import Theorems.Thm_GlobalTheory_PowUnif_powLift_pr
import Theorems.Thm_GlobalTheory_PowUnif_ex_zero
import Theorems.Thm_GlobalTheory_PowUnif_one_left
import Theorems.Thm_GlobalTheory_PowUnif_exists_powUnif
import Theorems.Thm_GlobalTheory_PowUnif_isDiff_map
import Theorems.Thm_GlobalTheory_PowUnif_val_boxRig
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__prod_553552cc56c1
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c
import Theorems.Thm_P2M_GlobalTheory_valAt__unit_ne_zero_54a31b83d959


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
namespace GlobalTheory.PowUnif
theorem _root_.solution : ∀ (x y : KeyIn ℂ) (j : ℕ) (u : HolUnif x.P.A x.P.L x.P.g) (θ : (Fin x.P.g → ℂ) → ℂ) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (u' : HolUnif y.P.A y.P.L y.P.g), (∀ z, z ∈ u'.Λ ↔ ∀ i, (fun k => z (e (i, k))) ∈ u.Λ) ∧ u'.IsRig y.rig ∧ u'.IsFn y.th (fun z => ∏ i, θ (fun k => z (e (i, k)))) ∧ ∀ p, u'.IsDiff (fun q => if (e.symm p).1 = (e.symm q).1 then W (e.symm p).2 (e.symm q).2 else 0) (y.v p) := by
  rintro x y j u θ W ⟨p, hg, hr, ht, hv⟩ hrig hfn hdiff
  let e : Fin j × Fin x.P.g ≃ Fin y.P.g := finProdFinEquiv.trans (finCongr hg)
  obtain ⟨u', hΛ, hex, hfr⟩ := exists_powUnif p.toIsPowGrp u x.P.isLB y.P.isLB p.w p.w_gen e
  let c : (Fin y.P.g → ℂ) → (Sp ℂ ⟶ y.P.A.left) := fun z => (u'.ex z).left
  let d : (Fin x.P.g → ℂ) → (Sp ℂ ⟶ x.P.A.left) := fun z => (u.ex z).left
  have hcd : ∀ z i, c z ≫ (p.pr i).left = d (blockPr e i z) := fun z i => congrArg (·.left) (hex z i)
  refine ⟨e, u', hΛ, fun b hb => ?_, fun b z hb => ?_, fun q => ?_⟩
  · have := y.P.isAb.comm
    have := x.P.isAb.comm
    obtain ⟨a, ha⟩ := exists_chart x.P.isLB (d 0)
    have hc0 : c 0 = eSec y.P.A := (congrArg (·.left) (ex_zero u')).trans one_left
    have hd0 : d 0 = eSec x.P.A := (congrArg (·.left) (ex_zero u)).trans one_left
    have h₁ : ⊤ ≤ c 0 ⁻¹ᵁ (Out.boxLB x.P.L p.pr).U fun _ => a :=
      (le_wchart_iff _ _ _ _).2 fun i => by rw [hcd, map_zero]; exact ha
    have h₂ : ⊤ ≤ c 0 ⁻¹ᵁ y.P.L.U (b PUnit.unit) := by
      rw [hc0]
      exact hb.trans (LB.wchart_le y.P.L (fun _ : PUnit => eSec y.P.A) b PUnit.unit)
    have h₃ : ⊤ ≤ (x.P.L.pull (eSec x.P.A)).U fun _ => a := by
      rw [hd0] at ha
      exact fun s hs => Set.mem_iInter.2 fun _ => ha hs
    have e₁ : _ = valAt' (c 0) _ _ * _ := hfr _ _ 0 h₁ h₂
    have hne := valAt'_unit_ne_zero (c 0) ((top_le_preimage_inf _ _ _).2 ⟨h₁, h₂⟩) (p.w.s (fun _ => a, b PUnit.unit))
    have e₂ := val_boxRig p.toIsPowGrp p.w x.rig y.rig hr a b (hc0 ▸ h₁) hb
    rw [hc0] at e₁ hne
    refine mul_left_cancel₀ hne (e₁.symm.trans (Eq.trans (Finset.prod_congr rfl fun i _ => ?_) e₂))
    rw [map_zero]
    exact hrig _ h₃
  · choose jj hjj using fun i => exists_chart x.P.isLB (d (blockPr e i z))
    have h₁ : ⊤ ≤ c z ⁻¹ᵁ (Out.boxLB x.P.L p.pr).U jj :=
      (le_wchart_iff _ _ _ _).2 fun i => by rw [hcd]; exact hjj i
    have hV : ⊤ ≤ c z ⁻¹ᵁ ((Out.boxLB x.P.L p.pr).U jj ⊓ y.P.L.U b) := (top_le_preimage_inf _ _ _).2 ⟨h₁, hb⟩
    have e₁ : _ = valAt' (c z) _ _ * _ := hfr _ _ z h₁ hb
    have hne := valAt'_unit_ne_zero (c z) hV (p.w.s (jj, b))
    have e₂ := congrArg (valAt' (c z) _) (ht jj b fun i =>
      inf_le_left.trans (LB.wchart_le x.P.L (fun i => (p.pr i).left) jj i))
    rw [valAt'_prod _ hV, valAt'_mul, valAt'_res _ _ _ hV] at e₂
    refine mul_left_cancel₀ hne (e₂.symm.trans ?_)
    rw [mul_left_comm]
    refine Eq.trans ?_ (congrArg (_ * ·) e₁)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [valAt'_appLE _ _ _ _ _ _ hV, hcd]
    exact hfn _ _ (hjj i)
  · obtain ⟨⟨i, k⟩, rfl⟩ := e.surjective q
    let ι' : x.P.A ⟶ y.P.A := powLift p.toIsPowGrp fun i' => if i = i' then 𝟙 _ else 1
    have hι : ∀ {T : Over (Sp ℂ)} (s : T ⟶ x.P.A) (i' : Fin j),
        (s ≫ ι') ≫ p.pr i' = if i = i' then s else 1 := fun s i' => by
      rw [Category.assoc, powLift_pr]
      split_ifs
      exacts [Category.comp_id _, MonObj.comp_one _]
    have hq : y.v (e (i, k)) = x.v k ≫ ι' := pow_hom_ext p.toIsPowGrp fun i' => (hv i i' k).trans (hι _ i').symm
    have hT : ∀ z, u'.ex (blockIn e i z) = u.ex z ≫ ι' := fun z => pow_hom_ext p.toIsPowGrp fun i' => by
      rw [hex, blockPr_blockIn, hι]
      split_ifs
      exacts [rfl, ex_zero u]
    have := isDiff_map u u' ι' (blockIn e i) hT (hq ▸ y.basis.1 _) (hdiff k)
    rw [blockIn_apply, ← hq] at this
    simpa only [Equiv.symm_apply_apply] using this
end GlobalTheory.PowUnif
