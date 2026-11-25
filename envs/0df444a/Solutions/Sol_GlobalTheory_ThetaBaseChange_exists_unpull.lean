-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.exists_unpull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:55:46.394105+00:00
-- url     : https://prove2.me/submissions/ce44f262-4bbe-427a-ac62-dd6d86fff57a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Theorems.Thm_GlobalTheory_FieldBaseChange_isoVal_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
theorem _root_.solution {c₀ : Y ⟶ X} {q : Y ⟶ N} {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen) (n : X ⟶ Y)
    (hn : n ≫ c₀ = 𝟙 X) {P : X ⟶ N} (hP : n ≫ q = P) :
    ∃ u : LB.Iso L (M.pull P), PGen u ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j : M.ι) (i : L.ι),
      P (f z) ∈ M.U j → f z ∈ L.U i → gw u f z j i = isoVal w (f ≫ n) z j i := by
  subst hP
  have hle : ∀ p : (PUnit → M.ι) × L.ι,
      (M.pull (n ≫ q)).U p.1 ⊓ L.U p.2 ≤ n ⁻¹ᵁ ((M.pull q).U p.1 ⊓ (L.pull c₀).U (fun _ => p.2)) := by
    rintro ⟨J, i⟩ x ⟨hx1, hx2⟩
    have hx3 : (n ≫ c₀) x ∈ L.U i := by rw [hn]; exact hx2
    have hx4 := mem_pull.mp hx1
    exact ⟨mem_pull.mpr hx4, mem_pull.mpr hx3⟩
  let u : LB.Iso L (M.pull (n ≫ q)) := ⟨fun p => res (hle p) (pullU n _ (w.s (p.1, fun _ => p.2)))⟩
  have key : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j : M.ι) (i : L.ι), (n ≫ q) (f z) ∈ M.U j → f z ∈ L.U i →
      gw u f z j i = isoVal w (f ≫ n) z j i := by
    intro Z f z j i hj hi
    have hV : f z ∈ (M.pull (n ≫ q)).U (fun _ => j) ⊓ L.U i := ⟨mem_pull.mpr hj, hi⟩
    exact (gm_res f z (hle ((fun _ => j), i)) hV _).trans (gm_pull f n z _ (hle ((fun _ => j), i) hV) _)
  refine ⟨u, ?_, key⟩
  intro Y₀ f y j j' k k' hj hj' hk hk'
  have hfn : (f ≫ n) ≫ c₀ = f := by rw [Category.assoc, hn, Category.comp_id]
  have a₁ : ((f ≫ n) ≫ c₀) y ∈ L.U k := by rw [hfn]; exact hk
  have b₁ : ((f ≫ n) ≫ c₀) y ∈ L.U k' := by rw [hfn]; exact hk'
  rw [key _ f y j k hj hk, key _ f y j' k' hj' hk', isoVal_trans hw (f ≫ n) y hj hj' a₁ b₁, hfn, Category.assoc]
end GlobalTheory.ThetaBaseChange
