-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.exists_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:30:08.457232+00:00
-- url     : https://prove2.me/submissions/6c3255b8-a2d1-4254-9bf4-f8b7e9843b98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Theorems.Thm_GlobalTheory_ThetaBaseChange_exists_unpull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pull_isLB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
variable {Y Y' X X' N N' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB N} {M' : LB N'}
namespace GlobalTheory.ThetaBaseChange
theorem _root_.solution (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB) (hM' : M'.IsLB)
    {c₀ : Y ⟶ X} {q : Y ⟶ N} {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen) (n : X ⟶ Y) (hn : n ≫ c₀ = 𝟙 X)
    {c₁ : Y' ⟶ X'} {q' : Y' ⟶ N'} {w' : LB.Iso (L'.pull c₁) (M'.pull q')} (hw' : w'.IsGen)
    {Ψ : N' ⟶ N} {wM : LB.Iso M' (M.pull Ψ)} (hwM : wM.IsGen) (Φ : Y' ⟶ X) (hΦ : Φ ≫ n ≫ q = q' ≫ Ψ) :
    ∃ v : LB.Iso (L'.pull c₁) (L.pull Φ), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (z : Z) (j : M.ι) (j' : M'.ι) (i : L.ι) (i' : L'.ι),
        Ψ (q' (f z)) ∈ M.U j → q' (f z) ∈ M'.U j' → Φ (f z) ∈ L.U i → c₁ (f z) ∈ L'.U i' →
        isoVal w (f ≫ Φ ≫ n) z j i * isoVal v f z i i' = gw wM (f ≫ q') z j j' * isoVal w' f z j' i' := by
  obtain ⟨u, hu, hu'⟩ := exists_unpull hw n hn (P := n ≫ q) rfl
  obtain ⟨w₁, T₁⟩ := exists_comp hM' wM w' ((isGen_iff wM).mp hwM) ((isGen_iff w').mp hw') hM (pull_isLB hL' c₁)
  have T₁' : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (y : Z) (j : M.ι) (i : M'.ι) (k : PUnit → L'.ι),
      Ψ (q' (f y)) ∈ M.U j → q' (f y) ∈ M'.U i → f y ∈ (L'.pull c₁).U k →
      gw w₁ f y j k = gw wM (f ≫ q') y j i * gw w' f y i k := T₁
  have P₁ := T₁.pgen_comp hM' ((isGen_iff wM).mp hwM) ((isGen_iff w').mp hw')
  clear T₁
  generalize hQ : q' ≫ Ψ = Q at w₁ T₁' P₁
  have hQ' : Φ ≫ n ≫ q = Q := hΦ.trans hQ
  subst hQ'
  obtain ⟨v, T₂⟩ := exists_cancel hM u w₁ hu P₁ hL (pull_isLB hL' c₁)
  refine ⟨v, (isGen_iff v).mpr (T₂.pgen_cancel hM hu P₁), ?_⟩
  intro Z f z j j' i i' hj hj' hi hi'
  have m₁ : (n ≫ q) (Φ (f z)) ∈ M.U j := by
    have m₀ : (Φ ≫ n ≫ q) (f z) ∈ M.U j := by
      rw [hΦ]
      exact hj
    exact m₀
  have e₂ := T₂ Z f z j i (fun _ => i') m₁ hi (mem_pull.mpr hi')
  have e₁ := T₁' Z f z j j' (fun _ => i') hj hj' (mem_pull.mpr hi')
  have e₃ := hu' Z (f ≫ Φ) z j i m₁ hi
  rw [e₃, Category.assoc] at e₂
  exact e₂.symm.trans e₁
end GlobalTheory.ThetaBaseChange
