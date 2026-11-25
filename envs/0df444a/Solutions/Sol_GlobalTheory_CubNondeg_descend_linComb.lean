-- Prove2me | solution 1 for GlobalTheory.CubNondeg.descend_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:57:06.98095+00:00
-- url     : https://prove2.me/submissions/72451f0a-a7c2-4282-9020-78b1a4f21728

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TorsionInvariantDescendsFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RatioTranslate
import Theorems.Thm_GlobalTheory_CubNondeg_gs_appLE
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CubNondeg
namespace GlobalTheory.CubNondeg
theorem _root_.solution {X Y Y' : Scheme.{0}} (m : Y' ⟶ Y) {T : Type} (τ : T → (Y' ⟶ Y'))
    (hτ : ∀ t, τ t ≫ m = m)
    (H : ∀ (V : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ V)),
      (∀ t, ∀ h : m ⁻¹ᵁ V ≤ τ t ⁻¹ᵁ (m ⁻¹ᵁ V), ((τ t).appLE _ _ h).hom a = a) →
      ∃! a' : Γ(Y, V), (m.app V).hom a' = a)
    (M : LB X) (hM : M.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (σ : LB.Gen (LB.LinComb M (fun k => m ≫ ψ k) ε)) (hσ : σ.IsGen)
    (inv : ∀ t (z : Y') (J : (Y' ⟶ X) → M.1), Good M z J → val σ (τ t) z J = val σ (𝟙 Y') z J) :
    ∃ t : (LB.LinComb M ψ ε).Gen, t.IsGen := by
  have inj : ∀ V : Y.Opens, Function.Injective (m.app V).hom := by
    intro V a b e
    obtain ⟨c, -, hc⟩ := H V ((m.app V).hom a) (fun t h => fn_ext fun x hx => by
      rw [gs_appLE (τ t) _ _ h _ x hx, gs_pull (τ t) m x V (h hx), gs_pull (𝟙 Y') m x V hx, hτ,
        Category.id_comp])
    exact (hc a rfl).trans (hc b e.symm).symm
  have injU : ∀ V : Y.Opens, Function.Injective (pullU m V) := fun V a b e =>
    Units.ext (inj V (congrArg Units.val e))
  have descU : ∀ (V : Y.Opens) (u : Γ(Y', m ⁻¹ᵁ V)ˣ),
      (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ v : Γ(Y, V)ˣ, pullU m V v = u := by
    intro V u hu
    have key : ∀ u : Γ(Y', m ⁻¹ᵁ V)ˣ, (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) →
        ∃ a : Γ(Y, V), (m.app V).hom a = u.val := fun u hu =>
      (H V u.val (fun t h => fn_ext fun x hx => by
        rw [gs_appLE (τ t) _ _ h _ x hx, gs_unit (τ t) x (m ⁻¹ᵁ V) (h hx),
          gs_unit (𝟙 Y') x (m ⁻¹ᵁ V) hx,
          hu t x hx])).exists
    obtain ⟨a, ha⟩ := key u hu
    obtain ⟨b, hb⟩ := key u⁻¹ (fun t x hx => by rw [map_inv, map_inv, hu t x hx])
    have e : a * b = 1 := inj V (by rw [map_mul, map_one, ha, hb]; exact u.mul_inv)
    exact ⟨⟨a, b, e, (mul_comm _ _).trans e⟩, Units.ext ha⟩
  have le : ∀ j : K → M.ι, m ⁻¹ᵁ LB.wchart M ψ j ≤ LB.wchart M (fun k => m ≫ ψ k) j :=
    fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have loc : ∀ j : K → M.ι, ∃ v : Γ(Y, LB.wchart M ψ j)ˣ, pullU m _ v = res (le j) (σ.s j) := by
    intro j
    refine descU _ _ fun t x hx => ?_
    have hx' : τ t x ∈ m ⁻¹ᵁ LB.wchart M ψ j :=
      (congrArg (fun q : Y' ⟶ Y => q x ∈ LB.wchart M ψ j) (hτ t)).mpr hx
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hM x
    have this := inv t x J hJ
    have e : ∀ k, τ t ≫ m ≫ ψ k = 𝟙 Y' ≫ m ≫ ψ k := fun k => by rw [Category.id_comp, ← Category.assoc, hτ]
    have g₁ := gen_trans hσ (τ t) x (le j hx') (hJ.mem (fun k => m ≫ ψ k) (τ t))
    have g₂ := gen_trans hσ (𝟙 Y') x (le j hx) (hJ.mem (fun k => m ≫ ψ k) (𝟙 Y'))
    refine (gm_res (τ t) x (le j) hx' _).trans ((g₁.trans (Eq.trans (congrArg₂ (· * ·) ?_ this) g₂.symm)).trans
      (gm_res (𝟙 Y') x (le j) hx _).symm)
    exact congrArg (fun q : K → (Y' ⟶ X) => ∏ k, gm (q k) x (M.U (j k) ⊓ M.U (J (q k))) (M.g (j k) (J (q k))) ^ ε k)
      (funext e)
  choose v hv using loc
  refine ⟨⟨v⟩, fun i j => injU _ (unit_ext fun x hx => ?_)⟩
  have hv' : ∀ j : K → M.ι, m x ∈ LB.wchart M ψ j →
      gm (𝟙 Y' ≫ m) x _ (v j) = gm (𝟙 Y') x (LB.wchart M (fun k => m ≫ ψ k) j) (σ.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m x _ hj _).symm.trans ((congrArg (gm (𝟙 Y') x _) (hv j)).trans (gm_res (𝟙 Y') x (le j) hj _))
  have hx' : (𝟙 Y' ≫ m) x ∈ LB.wchart M ψ i ⊓ LB.wchart M ψ j := hx
  refine (gm_pull (𝟙 Y') m x _ hx _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m x _ hx _).symm)
  refine (gm_res _ x _ hx' _).trans ((hv' i hx.1).trans ((gen_trans hσ (𝟙 Y') x (le i hx.1) (le j hx.2)).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb M ψ ε (𝟙 Y' ≫ m) x i j hx'.1 hx'.2).trans ?_)
      ((gm_res _ x _ hx' _).trans (hv' j hx.2)))))))
  simp only [trF, Category.assoc]
end GlobalTheory.CubNondeg
