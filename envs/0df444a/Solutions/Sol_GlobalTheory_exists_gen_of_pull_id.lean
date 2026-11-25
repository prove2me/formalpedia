-- Prove2me | solution 1 for GlobalTheory.exists_gen_of_pull_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:23.41292+00:00
-- url     : https://prove2.me/submissions/3c98345d-5042-4c63-99cc-80134a6da66d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigidifiedFaithfullyFlatDescent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory
private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)ˣ) :
    res h₂ (res h₁ a) = res (h₂.trans h₁) a := by
  unfold res
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
private lemma U_le_pull_id_U {X : Scheme.{0}} (N : LB X) (i : N.ι) :
    N.U i ≤ (N.pull (𝟙 X)).U (fun _ => i) := by
  intro x hx
  unfold LB.pull LB.LinComb LB.wchart
  simpa using hx
private lemma res_pullU_id_moduli {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (h' : V ≤ U)
    (a : Γ(X, U)ˣ) : res h (pullU (𝟙 X) U a) = res h' a := by
  unfold res pullU
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rfl
private lemma res_self_moduli {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by
  unfold res
  ext
  simp
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}} (N : LB X) (t : (N.pull (𝟙 X)).Gen) (ht : t.IsGen) :
    ∃ t : N.Gen, t.IsGen := by
  refine ⟨⟨fun i => res (U_le_pull_id_U N i) (t.s (fun _ => i))⟩, ?_⟩
  intro i j
  have key := congrArg (res (inf_le_inf (U_le_pull_id_U N i) (U_le_pull_id_U N j))) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, res_res_lemma, res_res_lemma] at key
  simp only [res_res_lemma]
  refine key.trans ?_
  congr 1
  have hle : (N.pull (𝟙 X)).U (fun _ => i) ⊓ (N.pull (𝟙 X)).U (fun _ => j) ≤ (𝟙 X) ⁻¹ᵁ (N.U i ⊓ N.U j) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    simp only [LB.pull, LB.LinComb, LB.wchart] at h1 h2
    have a : x ∈ N.U i := by simpa using h1
    have b : x ∈ N.U j := by simpa using h2
    exact ⟨a, b⟩
  have hG : (N.pull (𝟙 X)).g (fun _ => i) (fun _ => j) = res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j)) := by
    show ∏ _k : PUnit, (res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [hG, res_res_lemma]
  exact (res_pullU_id_moduli _ le_rfl _).trans (res_self_moduli _ _)
end GlobalTheory
