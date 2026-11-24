-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.eq_zero_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:53.192954+00:00
-- url     : https://prove2.me/submissions/5fc1894e-3547-423f-b87d-e49e3f51c74c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_GlobalTheory_SectionsProduct_eq_zero_of_linearIndependent
import Theorems.Thm_P2M_GlobalTheory_SectionsProduct_gs_sum__5d885260760f
import Theorems.Thm_P2M_GlobalTheory_SectionsProduct_gs_zero__6e6cf73bee24
import Theorems.Thm_GlobalTheory_SectionsProduct_exists_affine_le
import Theorems.Thm_GlobalTheory_SectionsProduct_exists_finite_cover
import Theorems.Thm_GlobalTheory_SectionsProduct_prodFn_bijective
import Theorems.Thm_GlobalTheory_SectionsProduct_gs_prodFn_zero
import Theorems.Thm_GlobalTheory_SectionsProduct_gs_prodFn_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hL : L.IsLB) [IsAffine S] (hS : IsField Γ(S, ⊤)) [CompactSpace X₁] {n : ℕ}
    (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (ha : ∀ c : Fin n → Γ(S, ⊤), (∀ j, ∑ i, resTop _ (i₁.appTop.hom (c i)) * (a i).f j = 0) → c = 0)
    (h : ∀ (z : W) (J), Good L z J → ∑ i, sval (a i) p z J * sval (b i) q z J = 0) (i : Fin n) (k : K₂ → L.ι) :
    (b i).f k = 0 := by
  obtain ⟨P, _, U, j, aU, hU, cU⟩ := exists_finite_cover hL φ₁
  let a' : Fin n → ∀ x, Fn i₁ (U x) := fun i x => rs (hU x) ((a i).f (j x))
  have cst : ∀ (O : X₁.Opens) (z : X₁) (_ : z ∈ O) (c : Γ(S, ⊤)),
      gs (𝟙 X₁) z O ((i₁.appLE ⊤ O le_top).hom c) = gs (𝟙 X₁ ≫ i₁) z ⊤ c :=
    fun O z hz c => gs_appLE i₁ ⊤ O _ _ z hz c
  have li : LinearIndependent Γ(S, ⊤) a' := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    refine congrFun (ha c fun j' => fn_ext fun z hz => ?_)
    obtain ⟨x, hx⟩ := cU z
    have e : (∑ i, (i₁.appLE ⊤ (U x) le_top).hom (c i) * rs (hU x) ((a i).f (j x)) : Γ(X₁, U x)) = 0 :=
      (Finset.sum_apply x Finset.univ (fun i => c i • a' i)).symm.trans (congrFun hc x)
    have e' := congrArg (gs (𝟙 X₁) z (U x)) e
    rw [gs_sum' _ z _ hx, gs_zero' _ z _ hx] at e'
    rw [gs_sum' _ z _ hz, gs_zero' _ z _ hz, ← mul_zero (trF φ₁ ε₁ (𝟙 X₁) z j' (j x)).val, ← e', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (gs_mul _ z _ hz _ _).trans ((congrArg₂ (· * ·) (cst _ z hz (c i))
      (sec_trans (a i) (𝟙 X₁) z hz (hU x hx))).trans (Eq.trans ?_ (congrArg _ ((gs_mul _ z _ hx _ _).trans
        (congrArg₂ (· * ·) (cst _ z hx (c i)) (gs_res (𝟙 X₁) z (hU x) hx _)))).symm))
    exact mul_left_comm _ _ _
  refine fn_ext fun y hy => ?_
  obtain ⟨V, aV, hyV, hV⟩ := exists_affine_le hy
  have := eq_zero_of_linearIndependent hS a' li (C := Fn i₂ V) (fun i => rs hV ((b i).f k)) (fun x =>
    (prodFn_bijective H (aU x) aV).1 (fn_ext fun z hz => by
      choose J hJ using fun χ : W ⟶ B => exists_chart hL (χ z)
      refine (gs_prodFn_sum H (𝟙 W) z hz (fun i => a' i x) (fun i => rs hV ((b i).f k))).trans ?_
      rw [gs_prodFn_zero H (𝟙 W) z hz, Category.id_comp, Category.id_comp,
        ← mul_zero ((trF φ₁ ε₁ p z (j x) (fun κ => J (p ≫ φ₁ κ))).val *
          (trF φ₂ ε₂ q z k (fun κ => J (q ≫ φ₂ κ))).val), ← h z J hJ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine (congrArg₂ (· * ·)
        ((gs_res p z (hU x) hz.1 _).trans (sec_trans (a i) p z (hU x hz.1) (Good.mem hJ φ₁ p)))
        ((gs_res q z hV hz.2 _).trans (sec_trans (b i) q z (hV hz.2) (Good.mem hJ φ₂ q)))).trans ?_
      exact _root_.mul_mul_mul_comm _ _ _ _)) i
  exact (gs_res (𝟙 X₂) y hV hyV _).symm.trans ((congrArg (gs (𝟙 X₂) y V) this).trans
    ((gs_zero' _ y _ hyV).trans (gs_zero' _ y _ hy).symm))
end GlobalTheory.SectionsProduct
