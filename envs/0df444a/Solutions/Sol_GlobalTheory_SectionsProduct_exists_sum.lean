-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.exists_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:55.1798+00:00
-- url     : https://prove2.me/submissions/f8740729-7087-4236-8d76-487945a73916

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_GlobalTheory_SectionsProduct_exists_sum_of_compatible
import Theorems.Thm_GlobalTheory_SectionsProduct_trF_same
import Theorems.Thm_GlobalTheory_SectionsProduct_exists_finite_cover
import Theorems.Thm_GlobalTheory_SectionsProduct_exists_sec_of_cover
import Theorems.Thm_GlobalTheory_SectionsProduct_gs_twist
import Theorems.Thm_GlobalTheory_SectionsProduct_prodFn_bijective
import Theorems.Thm_GlobalTheory_SectionsProduct_gs_prodFn_sum
import Theorems.Thm_GlobalTheory_SectionsProduct_gs_prodFn_map
import Theorems.Thm_GlobalTheory_SectionsProduct_trF_sum
import Theorems.Thm_GlobalTheory_SectionsProduct_le_wchart_sum
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.SectionsProduct
open GlobalTheory.KuennethOne
variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]
variable {p : W ⟶ X₁} {q : W ⟶ X₂} {i₁ : X₁ ⟶ S} {i₂ : X₂ ⟶ S} (H : IsPullback p q i₁ i₂)
variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (X₁ ⟶ B)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (X₂ ⟶ B)) (ε₂ : K₂ → ℤ)
include H
namespace GlobalTheory.SectionsProduct
theorem _root_.solution (hL : L.IsLB) [IsAffine S] (hS : IsField Γ(S, ⊤)) [CompactSpace X₁] [CompactSpace X₂]
    [X₁.IsSeparated] [X₂.IsSeparated]
    (v : LB.Sec (LB.LinComb L (Sum.elim (fun k => p ≫ φ₁ k) (fun k => q ≫ φ₂ k)) (Sum.elim ε₁ ε₂))) :
    ∃ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)),
      ∀ (T : Scheme.{0}) (r : T ⟶ W) (z : T) (J), Good L z J →
        sval v r z J = ∑ i, sval (a i) (r ≫ p) z J * sval (b i) (r ≫ q) z J := by
  obtain ⟨P, _, U, j, aU, hU, cU⟩ := exists_finite_cover hL φ₁
  obtain ⟨Q, _, V, k, aV, hV, cV⟩ := exists_finite_cover hL φ₂
  have le := fun x y => le_wchart_sum (p := p) (q := q) φ₁ φ₂ (hU x) (hV y)
  choose c hc using fun x y => (prodFn_bijective H (aU x) (aV y)).2 (rs (le x y) (v.f (Sum.elim (j x) (k y))))
  have hv : ∀ (T : Scheme.{0}) (r : T ⟶ W) (z : T) x y, r z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y →
      gs r z _ (prodFn H (U x) (V y) (c x y)) =
        gs r z (LB.wchart L _ (Sum.elim (j x) (k y))) (v.f (Sum.elim (j x) (k y))) :=
    fun T r z x y hz => (congrArg (gs r z _) (hc x y)).trans (gs_res r z (le x y) hz _)
  obtain ⟨n, a, b, ha, hb, e⟩ := exists_sum_of_compatible hS (A := fun x => Fn i₁ (U x)) (B := fun y => Fn i₂ (V y))
    (fun x x' => (rsA i₁ (inf_le_left : U x ⊓ U x' ≤ U x)).toLinearMap) (fun x x' => twist i₁ φ₁ ε₁ (hU x) (hU x'))
    (fun x x' => (rsA i₂ (inf_le_left : V x ⊓ V x' ≤ V x)).toLinearMap) (fun x x' => twist i₂ φ₂ ε₂ (hV x) (hV x')) c
    (fun x x' y => (prodFn_bijective H ((aU x).inf (aU x')) (aV y)).1 (fn_ext fun z hz => by
      have m : (𝟙 W : W ⟶ W) z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y := ⟨hz.1.1, hz.2⟩
      have m' : (𝟙 W : W ⟶ W) z ∈ p ⁻¹ᵁ U x' ⊓ q ⁻¹ᵁ V y := ⟨hz.1.2, hz.2⟩
      refine (gs_prodFn_map H (𝟙 W) z m hz (rsA i₁ (inf_le_left : U x ⊓ U x' ≤ U x)).toLinearMap LinearMap.id 1 1
        (fun a => (gs_res (𝟙 W ≫ p) z (inf_le_left : U x ⊓ U x' ≤ U x) hz.1 a).trans (_root_.one_mul _).symm)
        (fun a => (_root_.one_mul _).symm) _).trans
        (Eq.trans ?_ (gs_prodFn_map H (𝟙 W) z m' hz _ LinearMap.id _ 1
          (gs_twist i₁ φ₁ ε₁ (hU x) (hU x') (𝟙 W ≫ p) z hz.1) (fun a => (_root_.one_mul _).symm) _).symm)
      rw [hv _ _ z x y m, hv _ _ z x' y m', sec_trans v (𝟙 W) z (le x y m) (le x' y m'), trF_sum,
        Sum.elim_comp_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_comp_inr,
        trF_same hL φ₂ ε₂ (𝟙 W ≫ q) z (hV y hz.2)]
      simp))
    (fun x y y' => (prodFn_bijective H (aU x) ((aV y).inf (aV y'))).1 (fn_ext fun z hz => by
      have m : (𝟙 W : W ⟶ W) z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y := ⟨hz.1, hz.2.1⟩
      have m' : (𝟙 W : W ⟶ W) z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y' := ⟨hz.1, hz.2.2⟩
      refine (gs_prodFn_map H (𝟙 W) z m hz LinearMap.id (rsA i₂ (inf_le_left : V y ⊓ V y' ≤ V y)).toLinearMap 1 1
        (fun a => (_root_.one_mul _).symm)
        (fun a => (gs_res (𝟙 W ≫ q) z (inf_le_left : V y ⊓ V y' ≤ V y) hz.2 a).trans (_root_.one_mul _).symm) _).trans
        (Eq.trans ?_ (gs_prodFn_map H (𝟙 W) z m' hz LinearMap.id _ 1 _ (fun a => (_root_.one_mul _).symm)
          (gs_twist i₂ φ₂ ε₂ (hV y) (hV y') (𝟙 W ≫ q) z hz.2) _).symm)
      rw [hv _ _ z x y m, hv _ _ z x y' m', sec_trans v (𝟙 W) z (le x y m) (le x y' m'), trF_sum,
        Sum.elim_comp_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_comp_inr,
        trF_same hL φ₁ ε₁ (𝟙 W ≫ p) z (hU x hz.1)]
      simp))
  choose s hs using fun i => exists_sec_of_cover hL φ₁ ε₁ U j hU cU (a i) (fun x x' z h h' =>
    (gs_res (𝟙 X₁) z (inf_le_left : U x ⊓ U x' ≤ U x) ⟨h, h'⟩ _).symm.trans
      ((congrArg (gs (𝟙 X₁) z (U x ⊓ U x')) (ha i x x')).trans (gs_twist i₁ φ₁ ε₁ (hU x) (hU x') _ z ⟨h, h'⟩ _)))
  choose t ht using fun i => exists_sec_of_cover hL φ₂ ε₂ V k hV cV (b i) (fun x x' z h h' =>
    (gs_res (𝟙 X₂) z (inf_le_left : V x ⊓ V x' ≤ V x) ⟨h, h'⟩ _).symm.trans
      ((congrArg (gs (𝟙 X₂) z (V x ⊓ V x')) (hb i x x')).trans (gs_twist i₂ φ₂ ε₂ (hV x) (hV x') _ z ⟨h, h'⟩ _)))
  refine ⟨n, s, t, fun T r z J hJ => ?_⟩
  obtain ⟨x, hx⟩ := cU ((r ≫ p) z)
  obtain ⟨y, hy⟩ := cV ((r ≫ q) z)
  have m : r z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y := ⟨hx, hy⟩
  have m₁ := hJ.mem φ₁ (r ≫ p)
  have m₂ := hJ.mem φ₂ (r ≫ q)
  rw [sval_of v r z J (Sum.elim (fun κ => J ((r ≫ p) ≫ φ₁ κ)) (fun κ => J ((r ≫ q) ≫ φ₂ κ))) (by
      rintro (κ | κ) <;> simp),
    sec_trans v r z (le_wchart_sum φ₁ φ₂ le_rfl le_rfl ⟨m₁, m₂⟩) (le x y m), ← hv _ r z x y m, e,
    gs_prodFn_sum H r z m, trF_sum, Sum.elim_comp_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_comp_inr,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval, sval, hs i _ _ z x _ hx m₁, ht i _ _ z y _ hy m₂, Units.val_mul]
  ring
end GlobalTheory.SectionsProduct
