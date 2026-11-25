-- Prove2me | solution 1 for GlobalTheory.CubeDescent.exists_gen_descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:52.478022+00:00
-- url     : https://prove2.me/submissions/10765d2b-1f2b-40a0-b055-7d0c33bf011e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Theorems.Thm_GlobalTheory_CubeDescent_gs_appLE
import Theorems.Thm_GlobalTheory_FunDescent_app_injective
import Theorems.Thm_GlobalTheory_FunDescent_exists_app_eq
import Theorems.Thm_GlobalTheory_FunDescent_isUnit_of_isUnit_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open GlobalTheory GlobalTheory.CubeDescent
variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.CubeDescent
theorem _root_.solution {L : LB X} (hL : L.IsLB) (π : Y' ⟶ Y) [Flat π] [Surjective π]
    [QuasiCompact π] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen)
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ Y') (z : Z) (J), Good L z J → g₁ ≫ π = g₂ ≫ π →
      val u g₁ z J = val u g₂ z J) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      (π.app _).hom a = (res (le j) (u.s j)).val := by
    intro j
    refine FunDescent.exists_app_eq π _ _ fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z _ => ?_
    rw [gs_appLE, gs_appLE, gs_unit _ _ _ (h₁ (x := z) trivial), gs_unit _ _ _ (h₂ (x := z) trivial)]
    choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
    have c₁ := gen_trans hu g₁ z (le j (h₁ (x := z) trivial)) (Good.mem hI _ g₁)
    have c₂ := gen_trans hu g₂ z (le j (h₂ (x := z) trivial)) (Good.mem hI _ g₂)
    have c₃ : trF (fun k => π ≫ φ k) ε g₁ z j (fun k => I (g₁ ≫ π ≫ φ k)) =
        trF (fun k => π ≫ φ k) ε g₂ z j (fun k => I (g₂ ≫ π ≫ φ k)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : g₁ ≫ π ≫ φ k = g₂ ≫ π ≫ φ k := by rw [reassoc_of% e]
      show gm (g₁ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₁ ≫ π ≫ φ k))) (L.g (j k) (I (g₁ ≫ π ≫ φ k))) ^ _ =
        gm (g₂ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₂ ≫ π ≫ φ k))) (L.g (j k) (I (g₂ ≫ π ≫ φ k))) ^ _
      rw [this]
    exact congrArg Units.val ((gm_res g₁ z (le j) (h₁ (x := z) trivial) _).trans
      ((c₁.trans ((congrArg₂ (· * ·) c₃ (h Z g₁ g₂ z I hI e)).trans c₂.symm)).trans
        (gm_res g₂ z (le j) (h₂ (x := z) trivial) _).symm))
  choose a ha using desc
  have hun : ∀ j, IsUnit (a j) := fun j =>
    FunDescent.isUnit_of_isUnit_app π _ _ (ha j ▸ Units.isUnit _)
  have hv : ∀ j (y : Y'), π y ∈ LB.wchart L φ j → gm π y (LB.wchart L φ j) (hun j).unit =
      gm (𝟙 Y') y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j y hy
    have e : pullU π _ (hun j).unit = res (le j) (u.s j) := Units.ext (ha j)
    refine Eq.trans ?_ ((gm_pull (𝟙 Y') π y _ hy _).symm.trans
      ((congrArg (gm (𝟙 Y') y _) e).trans (gm_res (𝟙 Y') y (le j) hy _)))
    rw [Category.id_comp]
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext
    (FunDescent.app_injective π (LB.wchart L φ j ⊓ LB.wchart L φ j') ?_)⟩
  refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
  have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
  rw [Category.id_comp]
  refine ((gm_res π y _ hy' _).trans ((hv j y hy'.1).trans
    (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε π y j j' hy'.1 hy'.2).trans ?_)
    ((gm_res π y _ hy' _).trans (hv j' y hy'.2)))
  simp only [trF, Category.id_comp]
end GlobalTheory.CubeDescent
