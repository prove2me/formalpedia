-- Prove2me | solution 1 for GlobalTheory.GenExtendDense.gm_eq_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:29:34.083167+00:00
-- url     : https://prove2.me/submissions/31d08733-e780-4fef-a532-594f2d161880

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueGeneratorExtendDenseProOpen
import Theorems.Thm_GlobalTheory_DvrModel_wchart_comp
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtendDense
open GlobalTheory.GenericExtend GlobalTheory.DvrModel
namespace GlobalTheory.GenExtendDense
theorem _root_.solution {X Y U HU H Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (H ⟶ X)} {ε : I → ℤ} {jH : HU ⟶ H} {e : Y ⟶ H} {j : U ⟶ Y} {eU : U ⟶ HU}
    (heU : eU ≫ jH = j ≫ e)
    {t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)}
    {ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)} (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j))
    (κ : Z ⟶ U) (z : Z) (a : I → L.ι) (ha : e (j (κ z)) ∈ LB.wchart L φ a) :
    gm (κ ≫ eU) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) =
      gm (κ ≫ j) z (LB.wchart L (fun i => e ≫ φ i) a) (ρ.s a) := by
  choose Jg hJg using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  have hG : Good L z Jg := hJg
  have hv := val_corr hG hc κ
  rw [val_pull hG, val_pull hG] at hv
  have hw : ∀ k, (κ ≫ eU) ≫ jH ≫ φ k = (κ ≫ j) ≫ e ≫ φ k := fun k => by
    simp only [Category.assoc, reassoc_of% heU]
  let a' : I → L.ι := fun k => Jg ((κ ≫ eU) ≫ jH ≫ φ k)
  have ha' : a' = fun k => Jg ((κ ≫ j) ≫ e ≫ φ k) := funext fun k => congrArg Jg (hw k)
  rw [val_of t (κ ≫ eU) z Jg a' (fun k => rfl),
    val_of ρ (κ ≫ j) z Jg a' (fun k => by rw [ha'])] at hv
  have hpt : jH ((κ ≫ eU) z) = e ((κ ≫ j) z) := by
    rw [← Scheme.Hom.comp_apply, Category.assoc, heU, ← Category.assoc, Scheme.Hom.comp_apply]
  have h1 : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a :=
    (wchart_comp L jH φ a).ge (show jH ((κ ≫ eU) z) ∈ LB.wchart L φ a by rw [hpt]; exact ha)
  have h2 : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a := (wchart_comp L e φ a).ge ha
  have h1' : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a' := hG.mem (fun i => jH ≫ φ i) (κ ≫ eU)
  have h2' : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a' := by
    rw [ha']; exact hG.mem (fun i => e ≫ φ i) (κ ≫ j)
  have htr : trF (L := L) (fun i => jH ≫ φ i) ε (κ ≫ eU) z a a' =
      trF (L := L) (fun i => e ≫ φ i) ε (κ ≫ j) z a a' := by
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [hw k]
  rw [gen_trans ht (κ ≫ eU) z h1 h1', gen_trans hρ (κ ≫ j) z h2 h2', htr, hv]
end GlobalTheory.GenExtendDense
