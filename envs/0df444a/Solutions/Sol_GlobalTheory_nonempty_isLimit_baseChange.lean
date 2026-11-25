-- Prove2me | solution 1 for GlobalTheory.nonempty_isLimit_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:54:46.49145+00:00
-- url     : https://prove2.me/submissions/b199d793-20a6-49e1-acd2-ef81834eb88e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_GlobalTheory_FGAbove_exists_mem
import Theorems.Thm_GlobalTheory_FGAbove_exists_ringHom
import Theorems.Thm_GlobalTheory_hom_spec_ext
import Theorems.Thm_GlobalTheory_appTop_comp_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
variable {B : Scheme.{0}} (pB : B ⟶ Sp k)
namespace GlobalTheory
theorem _root_.solution (h : R₀.FG) :
    Nonempty (IsLimit (schemeConeOfFamily (baseChangeDiagram R₀ pB)
      (X := pullback pB (spMap (algebraMap k C))) (fun R => baseChangeMap pB R.unop.1.val)
      (fun {R T} f => baseChangeMap_comp pB
        (Subalgebra.inclusion (show T.unop.1 ≤ R.unop.1 from leOfHom f.unop)) R.unop.1.val))) := by
  let o : FGAbove R₀ := ⟨R₀, h, le_rfl⟩
  refine ⟨IsLimit.ofExistsUnique fun s => ?_⟩
  let a : ∀ R : FGAbove R₀, s.pt ⟶ pullback pB (spMap (algebraMap k R.1)) := fun R => s.π.app (.op R)
  have ha : ∀ (R T : FGAbove R₀) (hRT : R.1 ≤ T.1),
      a T ≫ baseChangeMap pB (Subalgebra.inclusion hRT) = a R :=
    fun R T hRT => s.w (homOfLE (show R ≤ T from hRT)).op
  obtain ⟨ψ, hψ⟩ := FGAbove.exists_ringHom h
    (fun R => ((Scheme.ΓSpecIso (.of R.1)).inv ≫ (a R ≫ pullback.snd _ _).appTop).hom) (by
      intro R T hRT x
      rw [← ha R T hRT, Category.assoc, baseChangeMap_snd, ← Category.assoc (a T), appTop_comp_spMap]
      rfl)
  obtain ⟨b, hb⟩ : ∃ b : s.pt ⟶ Sp C, (Scheme.ΓSpecIso (.of C)).inv ≫ b.appTop = CommRingCat.ofHom ψ := by
    refine ⟨s.pt.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop]
    simp
  have hb' : ∀ R : FGAbove R₀, b ≫ spMap R.1.val.toRingHom = a R ≫ pullback.snd _ _ := fun R =>
    hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => by
      rw [appTop_comp_spMap, hb]
      exact hψ R x))
  have hf : ∀ R : FGAbove R₀, a R ≫ pullback.fst _ _ = a o ≫ pullback.fst _ _ := fun R => by
    rw [← ha o R R.2.2, Category.assoc, baseChangeMap_fst]
  refine ⟨pullback.lift (a o ≫ pullback.fst _ _) b ?_, fun R => ?_, fun m hm => ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ← hb' o, Category.assoc, spMap_comp_ring]
    congr 2
  · show _ ≫ baseChangeMap pB R.unop.1.val = a R.unop
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeMap_fst, pullback.lift_fst, hf R.unop]
    · rw [Category.assoc, baseChangeMap_snd, pullback.lift_snd_assoc, hb']
  · change s.pt ⟶ pullback pB (spMap (algebraMap k C)) at m
    have hm' : ∀ R : FGAbove R₀, m ≫ baseChangeMap pB R.1.val = a R := fun R => hm (.op R)
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← hm' o, Category.assoc, baseChangeMap_fst]
    · rw [pullback.lift_snd]
      refine hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
      obtain ⟨R, hx⟩ := FGAbove.exists_mem h x
      have e : (m ≫ pullback.snd _ _) ≫ spMap R.1.val.toRingHom = b ≫ spMap R.1.val.toRingHom := by
        rw [hb', ← hm' R, Category.assoc, Category.assoc, baseChangeMap_snd]
      exact (appTop_comp_spMap R.1.val.toRingHom _ ⟨x, hx⟩).symm.trans
        (e ▸ appTop_comp_spMap R.1.val.toRingHom b ⟨x, hx⟩)
end GlobalTheory
