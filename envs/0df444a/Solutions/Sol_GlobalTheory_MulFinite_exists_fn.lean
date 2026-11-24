-- Prove2me | solution 1 for GlobalTheory.MulFinite.exists_fn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:42.706358+00:00
-- url     : https://prove2.me/submissions/c9388931-3c64-4e4d-a183-31cb8abafcff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Theorems.Thm_GlobalTheory_MulFinite_isUnit_gs
import Theorems.Thm_GlobalTheory_MulFinite_gs_appLE
import Theorems.Thm_GlobalTheory_MulFinite_gs_pow
import Theorems.Thm_GlobalTheory_MulFinite_pow_aux
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial
namespace GlobalTheory.MulFinite
theorem _root_.solution {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (m : X ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1])) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : L.ι) (h₀ : ∀ z, m (w (r z)) ∈ L.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => (r ≫ w) ⁻¹ᵁ L.U j
  have l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  have l₂ : ∀ j, V j ≤ (r ≫ w) ⁻¹ᵁ LB.wchart L (K := Fin 2) ![𝟙 X, m] ![j, j₀] :=
    fun j z hz => Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact hz
      · exact h₀ z
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j)) (s.f (fun _ => j)) ^ e *
        ((gm (r ≫ w) z (LB.wchart L (K := Fin 2) ![𝟙 X, m] ![j, j₀]) (α.s ![j, j₀]))⁻¹).val ^ N := by
    refine ⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) ^ e *
      ((r ≫ w).appLE _ _ (l₂ j)).hom ((α.s ![j, j₀])⁻¹).val ^ N, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    · exact congrArg (· ^ e) (gs_appLE r z _ _ _ hz _)
    · refine congrArg (· ^ N) ((gs_appLE (r ≫ w) z _ _ _ hz _).trans ?_)
      exact (gs_unit (r ≫ w) z _ (l₂ j hz) _).trans (congrArg Units.val (map_inv _ _))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2),
        gen_trans hα (r ≫ w) z (l₂ j hz.1) (l₂ j' hz.2)]
      have h1 : gm ((r ≫ w) ≫ m) z (L.U j₀ ⊓ L.U j₀) (L.g j₀ j₀) = 1 := gm_self hL _ z (h₀ z)
      have t₁ : trF (L := L) (K := Fin N) (fun _ => w) (fun _ => 1) r z (fun _ => j) (fun _ => j') =
          gm (r ≫ w) z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]
      have t₂ : trF (L := L) (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1] (r ≫ w) z ![j, j₀] ![j', j₀] =
          gm (r ≫ w) z (L.U j ⊓ L.U j') (L.g j j') ^ e := by
        rw [trF, Fin.prod_univ_two]
        change gm ((r ≫ w) ≫ 𝟙 X) z (L.U j ⊓ L.U j') (L.g j j') ^ (e : ℤ) *
          gm ((r ≫ w) ≫ m) z (L.U j₀ ⊓ L.U j₀) (L.g j₀ j₀) ^ (-1 : ℤ) = _
        rw [h1, Category.comp_id]; simp
      rw [t₁, t₂]
      exact pow_aux _ _ _ _ _)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔
      IsUnit (gs r z (LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j)) (s.f (fun _ => j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ LB.wchart L (K := Fin N) (fun _ => w) k := W.basicOpen_le _ hk
    rw [sec_trans s r z (l₁ j hj) hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)
end GlobalTheory.MulFinite
