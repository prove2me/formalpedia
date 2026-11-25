-- Prove2me | solution 1 for GlobalTheory.FieldDescentGen.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:59:11.911802+00:00
-- url     : https://prove2.me/submissions/a60e388b-0c53-4d54-9a17-e9d21a25af6c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveAppTopOfSmoothOfIsProperOfGeometrically
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleTrivialIsoDescendField
import Theorems.Thm_GlobalTheory_FieldDescentGen_exists_ratio
import Theorems.Thm_GlobalTheory_FieldDescentGen_isUnit_of_surjective
import Theorems.Thm_GlobalTheory_FieldBaseChange_epi_and_isMonHom_iff
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main
import Theorems.Thm_GlobalTheory_SectionsDescent_main
import Theorems.Thm_GlobalTheory_bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pull_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_eq_local


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
noncomputable section
open GlobalTheory
open GlobalTheory.FieldDescentGen
variable {X₀ X : Scheme.{0}}
namespace GlobalTheory.FieldDescentGen
theorem _root_.solution {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K)
    (φ : X ⟶ X₀) [Smooth p₀] [IsProper p₀] [GeometricallyConnected p₀] (H : IsPullback φ p p₀ (spMap i))
    (M : LB X₀) (hM : M.IsLB) (t : (M.pull φ).Gen) (ht : t.IsGen) : ∃ t : M.Gen, t.IsGen := by
  have hb : Function.Bijective p.appTop.hom := GlobalTheory.bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K X p
    (MorphismProperty.of_isPullback (P := @Smooth) H inferInstance)
    (MorphismProperty.of_isPullback (P := @IsProper) H inferInstance)
    (MorphismProperty.of_isPullback (P := @GeometricallyConnected) H inferInstance)
  have hF : IsField Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective p.appTop.hom hb)).symm.toMulEquiv.isField (Field.toIsField K)
  have : Surjective φ := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).1 X₀ X p₀ p φ H).2.2.1
  have hP := pull_isLB hM φ
  let ts : (M.pull φ).Sec := ⟨fun j => (t.s j).val, fun a b => congrArg Units.val (ht a b)⟩
  obtain ⟨n, c, s, hs⟩ := GlobalTheory.SectionsDescent.main K₀ K i X₀ X p₀ p φ M hM H ts
  choose u hu using fun a => exists_ratio hP t ht (secPull M φ (s a))
  have hne : ∃ a, u a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hF.nontrivial
    refine one_ne_zero (Out.TLinPf.eq_local (M.pull φ).U hP.cover 1 0 fun j => ?_)
    have h0 : (t.s j).val = 0 := by
      refine (hs j (pull_le M φ j)).trans (Finset.sum_eq_zero fun a _ => ?_)
      have e : (φ.appLE _ _ (pull_le M φ j)).hom ((s a).f (j PUnit.unit)) = _ := hu a j
      rw [e, hcon a, map_zero, zero_mul, mul_zero]
    rw [map_one, map_zero, ← (t.s j).mul_inv, h0, zero_mul]
  obtain ⟨a, ha⟩ := hne
  obtain ⟨v, hv⟩ := hF.mul_inv_cancel ha
  have hua : IsUnit (u a) := IsUnit.of_mul_eq_one v hv
  have hunit : ∀ k, IsUnit ((s a).f k) := fun k =>
    isUnit_of_surjective φ (pull_le M φ fun _ => k) (fun _ hy => mem_pull.2 hy) _ (by
      have e : (φ.appLE _ _ (pull_le M φ fun _ => k)).hom ((s a).f k) = _ := hu a fun _ => k
      rw [e]
      exact (hua.map _).mul (Units.isUnit _))
  exact ⟨⟨fun k => (hunit k).unit⟩, fun k l => Units.ext ((s a).compat k l)⟩
end GlobalTheory.FieldDescentGen
