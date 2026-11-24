-- Prove2me | solution 1 for GlobalTheory.MulSplit.Descends.exists_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:51:47.023081+00:00
-- url     : https://prove2.me/submissions/755c1deb-081d-42d3-9a61-3dbca3b676a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_dv_support
import Theorems.Thm_GlobalTheory_MulSplit_dv_comp
import Theorems.Thm_GlobalTheory_MulSplit_mem_Sg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B} {G : Type}
namespace GlobalTheory.MulSplit
namespace Descends
theorem _root_.solution (hL : L.IsLB) {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (H : Descends q τ) (hq : q ≫ p = p)
    (hτ : ∀ g, τ g ≫ p = p) (hτq : ∀ g, τ g ≫ q = q) {D : (Y ⟶ X) →₀ ℤ} {v : Vals L p}
    (hv : v ∈ Sg L p (D.mapDomain (q ≫ ·))) (h : ∀ g, pl L (τ g) (hτ g) v = v) :
    ∃ w ∈ Sg L p D, pl L q hq w = v := by
  let φ : D.support → (Y ⟶ X) := fun k => k.1
  let ε : D.support → ℤ := fun k => D k.1
  obtain ⟨s, rfl⟩ := (mem_Sg hL (φ := fun k => q ≫ φ k) (ε := ε) (by rw [dv_comp, dv_support]) v).1 hv
  have le : ∀ j, q ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => q ≫ φ k) j :=
    fun j _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have ge : ∀ j, LB.wchart L (fun k => q ≫ φ k) j ≤ q ⁻¹ᵁ LB.wchart L φ j :=
    fun j _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have ex : ∀ j, ∃ a, (q.app (LB.wchart L φ j)).hom a = (Y.presheaf.map (homOfLE (le j)).op).hom (s.f j) :=
    fun j => H.2 _ _ fun g y hy => by
      have hy' : τ g y ∈ q ⁻¹ᵁ LB.wchart L φ j := (congrArg (fun t => t y ∈ LB.wchart L φ j) (hτq g)).mpr hy
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have h0 : sval s (𝟙 Y ≫ τ g) y I = sval s (𝟙 Y) y I :=
        congrFun (h g) ⟨(y, I, 𝟙 Y), hI, Category.id_comp _⟩
      rw [Category.id_comp] at h0
      refine (gs_res _ y (le j) hy' _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y (le j) hy _).symm)
      refine (sec_trans s (τ g) y (le j hy') (Good.mem hI _ _)).trans
        (Eq.trans ?_ (sec_trans s (𝟙 Y) y (le j hy) (Good.mem hI _ _)).symm)
      refine congrArg₂ (· * ·) ?_ h0
      have e : ∀ k, τ g ≫ q ≫ φ k = 𝟙 Y ≫ q ≫ φ k := fun k => by
        rw [← Category.assoc, hτq, Category.id_comp]
      refine congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)
      show gm (τ g ≫ q ≫ φ k) y (L.U (j k) ⊓ L.U (I (τ g ≫ q ≫ φ k))) (L.g (j k) (I (τ g ≫ q ≫ φ k))) ^ _ =
        gm (𝟙 Y ≫ q ≫ φ k) y (L.U (j k) ⊓ L.U (I (𝟙 Y ≫ q ≫ φ k))) (L.g (j k) (I (𝟙 Y ≫ q ≫ φ k))) ^ _
      rw [e]
  choose a ha using ex
  have key : ∀ (r : Y ⟶ Y) (y : Y) (j), r y ∈ LB.wchart L (fun k => q ≫ φ k) j →
      gs (r ≫ q) y (LB.wchart L φ j) (a j) = gs r y (LB.wchart L (fun k => q ≫ φ k) j) (s.f j) :=
    fun r y j hy => (gs_pull r q y (LB.wchart L φ j) (show r y ∈ q ⁻¹ᵁ LB.wchart L φ j from ge j hy) _).symm.trans ((congrArg (gs r y _) (ha j)).trans
      (gs_res r y (le j) (ge j hy) _))
  let s' : LB.Sec (LB.LinComb L φ ε) := ⟨a, fun j j' => H.1 _ (fn_ext fun y hy => by
    have hm : (𝟙 Y ≫ q) y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
    refine (gs_pull (𝟙 Y) q y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y) q y _ hy _).symm)
    refine ((gs_res _ y _ hm _).trans (key _ y j (le j hy.1))).trans (Eq.trans ?_ ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans
        (congrArg Units.val (gm_linComb L φ ε (𝟙 Y ≫ q) y j j' hm.1 hm.2)))
        ((gs_res _ y _ hm _).trans (key _ y j' (le j' hy.2))))).symm)
    rw [sec_trans s (𝟙 Y) y (le j hy.1) (le j' hy.2)]
    simp only [trF, Category.assoc])⟩
  refine ⟨ev p s', ⟨s', rfl⟩, funext fun i => ?_⟩
  exact (sval_of s' (i.1.2.2 ≫ q) i.1.1 i.1.2.1 (fun k => i.1.2.1 (i.1.2.2 ≫ q ≫ φ k))
    (fun k => by rw [Category.assoc])).trans (key _ _ _ (i.2.1.mem _ _))
end Descends
end GlobalTheory.MulSplit
