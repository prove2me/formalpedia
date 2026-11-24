-- Prove2me | solution 1 for GlobalTheory.SecGlue.glue_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:26.003046+00:00
-- url     : https://prove2.me/submissions/707d87d3-0829-420d-abcb-dac59ba945e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
import Theorems.Thm_GlobalTheory_SecGlue_gs_appLE
import Theorems.Thm_GlobalTheory_SecGlue_ext_cover
import Theorems.Thm_GlobalTheory_SecGlue_glue_cover
import Theorems.Thm_GlobalTheory_SecGlue_mem_chart
import Theorems.Thm_GlobalTheory_SecGlue_Rel_gs_eq
import Theorems.Thm_GlobalTheory_SecGlue_compat_at
import Theorems.Thm_GlobalTheory_SecGlue_trF_comp
import Theorems.Thm_GlobalTheory_SecGlue_sec_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {A X Y Z : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {ε : K → ℤ}
namespace GlobalTheory.SecGlue
theorem _root_.solution {J : Type} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hc : ∀ x : X, ∃ i y, a i y = x) (q : X ⟶ A) (q' : ∀ i, T i ⟶ A) (e : ∀ i, a i ≫ q = q' i)
    (s : ∀ i, LB.Sec (LB.LinComb L (fun _ : K => q' i) ε))
    (h : ∀ i j y y', a i y = a j y' → ∃ (Z : Scheme.{0}) (b : Z ⟶ T i) (c : Z ⟶ T j) (z : Z)
      (p : Z ⟶ A) (t : LB.Sec (LB.LinComb L (fun _ : K => p) ε)),
      IsOpenImmersion (b ≫ a i) ∧ b ≫ a i = c ≫ a j ∧ b z = y ∧ b ≫ q' i = p ∧
        Rel b (s i) t ∧ Rel c (s j) t) :
    ∃! s₀ : LB.Sec (LB.LinComb L (fun _ : K => q) ε), ∀ i, Rel (a i) s₀ (s i) := by
  have key : ∀ k : K → L.ι, ∃ f : Γ(X, LB.wchart L (fun _ : K => q) k), ∀ i y,
      y ∈ LB.wchart L (fun _ : K => q' i) k →
      gs (a i) y _ f = gs (𝟙 _) y (LB.wchart L (fun _ : K => q' i) k) ((s i).f k) := fun k =>
    glue_cover a hc _ (fun i => LB.wchart L (fun _ : K => q' i) k) (fun i y => mem_chart (e i) k y)
      (fun i => (s i).f k) fun i j y y' hy hk => by
        obtain ⟨Z, b, c, z, p, t, h1, h2, rfl, h4, h5, h6⟩ := h i j y y' hy
        have h7 : c ≫ q' j = p := by rw [← h4, ← e i, ← e j, reassoc_of% h2]
        have hz := (mem_chart h4 k z).2 hk
        have h8 := h5.gs_eq h4 k (𝟙 Z) z hz
        have h9 := h6.gs_eq h7 k (𝟙 Z) z hz
        rw [Category.id_comp] at h8 h9
        exact ⟨Z, b, c, z, h1, h2, rfl, h8.trans h9.symm⟩
  choose f hf using key
  refine ⟨⟨f, fun (k k' : K → L.ι) => ?_⟩, fun i k hh => ?_, fun t ht => sec_ext fun k => ?_⟩
  · refine ext_cover a hc fun i y hy => compat_at (a i) y _ _ hy ?_
    have h1 := (mem_chart (e i) k y).2 hy.1
    have h2 := (mem_chart (e i) k' y).2 hy.2
    rw [hf k i y h1, hf k' i y h2]
    exact (sec_trans (s i) (𝟙 _) y h1 h2).trans
      (congrArg (fun u => Units.val u * _) (trF_comp (e i) y k k'))
  · refine fn_ext fun y hy => (gs_appLE (𝟙 _) (a i) y _ _ _ hy _).trans ?_
    rw [Category.id_comp]
    exact hf k i y hy
  · refine ext_cover a hc fun i y hy => ?_
    have h1 := (mem_chart (e i) k y).2 hy
    have h2 := (ht i).gs_eq (e i) k (𝟙 _) y h1
    rw [Category.id_comp] at h2
    exact h2.trans (hf k i y h1).symm
end GlobalTheory.SecGlue
