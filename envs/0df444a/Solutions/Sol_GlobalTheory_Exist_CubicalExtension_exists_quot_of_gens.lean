-- Prove2me | solution 1 for GlobalTheory.Exist.CubicalExtension.exists_quot_of_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:46:55.507828+00:00
-- url     : https://prove2.me/submissions/7f822c62-84cf-4020-a72b-bbea4467d505

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SabMapOfIsoOfExtendGen
import Theorems.Thm_GlobalTheory_Exist_CubicalExtension_mem_qchart
import Theorems.Thm_GlobalTheory_Exist_CubicalExtension_isGen_quot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.CubicalExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' X'' A : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
namespace GlobalTheory.Exist.CubicalExtension
theorem _root_.solution {Y Y' : Scheme.{0}} {e : Y ⟶ X} {e' : Y' ⟶ X'} {h : Y' ⟶ Y} (he : e' ≫ F = h ≫ e)
    (t : LB.Gen (L.pull e)) (t' : LB.Gen (L'.pull e')) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ ρ : LB.Gen ((LB.div (L.pull F) L').pull e'), ρ.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (y : Z) a i, F (e' (f y)) ∈ L.U a → e' (f y) ∈ L'.U i →
        gm f y (qchart L L' F e' a i) (ρ.s (fun _ => (fun _ => a, i))) =
          gm (f ≫ h) y (LB.wchart L (fun _ : PUnit => e) (fun _ => a)) (t.s (fun _ => a)) *
            (gm f y (LB.wchart L' (fun _ : PUnit => e') (fun _ => i)) (t'.s (fun _ => i)))⁻¹ := by
  have pe : ∀ y, e (h y) = F (e' y) := fun y => congrArg (fun g => g y) he.symm
  have l₁ : ∀ a i, qchart L L' F e' a i ≤ h ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => a) := fun a i x hx =>
    mem_pull.2 (by rw [pe]; exact (mem_qchart.1 hx).1)
  have l₂ : ∀ a i, qchart L L' F e' a i ≤ LB.wchart L' (fun _ : PUnit => e') (fun _ => i) := fun a i x hx =>
    mem_pull.2 (mem_qchart.1 hx).2
  obtain ⟨s, hs⟩ : ∃ s : ∀ a i, Γ(Y', qchart L L' F e' a i)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (y : Z) a i,
      F (e' (f y)) ∈ L.U a → e' (f y) ∈ L'.U i → gm f y (qchart L L' F e' a i) (s a i) =
          gm (f ≫ h) y (LB.wchart L (fun _ : PUnit => e) (fun _ => a)) (t.s (fun _ => a)) *
            (gm f y (LB.wchart L' (fun _ : PUnit => e') (fun _ => i)) (t'.s (fun _ => i)))⁻¹ :=
    ⟨fun a i => res (l₁ a i) (pullU h _ (t.s (fun _ => a))) * (res (l₂ a i) (t'.s (fun _ => i)))⁻¹,
      fun Z f y a i ha hi =>
        have hy : f y ∈ qchart L L' F e' a i := mem_qchart.2 ⟨ha, hi⟩
        (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res f y (l₁ a i) hy _).trans (gm_pull f h y _ (l₁ a i hy) _))
          ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y (l₂ a i) hy _))))⟩
  refine ⟨_, isGen_quot s fun y a a' i i' ha ha' hi hi' => ?_, hs⟩
  have e₁ := gen_trans ht (𝟙 Y' ≫ h) y (j := fun _ => a) (j' := fun _ => a') (l₁ a i (mem_qchart.2 ⟨ha, hi⟩))
    (l₁ a' i (mem_qchart.2 ⟨ha', hi⟩))
  have e₂ := gen_trans ht' (𝟙 Y') y (j := fun _ => i) (j' := fun _ => i') (mem_pull.2 hi) (mem_pull.2 hi')
  rw [trF, Fintype.prod_unique, zpow_one] at e₁ e₂
  rw [hs _ (𝟙 _) y a i ha hi, hs _ (𝟙 _) y a' i' ha' hi', e₁, e₂, Category.id_comp, Category.id_comp, he]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.Exist.CubicalExtension
