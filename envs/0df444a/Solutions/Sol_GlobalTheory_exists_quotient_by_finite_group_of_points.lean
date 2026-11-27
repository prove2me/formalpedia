-- Prove2me | solution 1 for GlobalTheory.exists_quotient_by_finite_group_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:39.783419+00:00
-- url     : https://prove2.me/submissions/499fadb9-d399-4446-84aa-206894635ca6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
import Theorems.Thm_GlobalTheory_PointQuot_constPt_desc
import Theorems.Thm_GlobalTheory_PointQuot_locally_const_desc
import Theorems.Thm_GlobalTheory_PointQuot_epi_toUnit
import Theorems.Thm_GlobalTheory_PointQuot_mono_constDesc
import Theorems.Thm_GlobalTheory_PointQuot_exists_grpObj_constObj
import Theorems.Thm_GlobalTheory_PointQuot_comp_eq_of_invariant
import Theorems.Thm_GlobalTheory_PointQuot_existsUnique_desc
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_etale
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_isFinite
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_of_isPullback
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff_exists_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torsor_pullback


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
open PointQuot
namespace GlobalTheory
theorem _root_.solution :
    Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)), Finite C → ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) ∧ ∀ (Y : Over (Sp k)) (f : P.A ⟶ Y), (∀ x ∈ C, ((toUnit P.A ≫ x) * 𝟙 P.A) ≫ f = f) → ∃! f' : B ⟶ Y, ψ ≫ f' = f := by
  intro L k _ _ P C hC
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let x : Fin n → (𝟙_ (Over (Sp k)) ⟶ P.A) := fun c => (e.symm c).1
  have hx : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  have hr : Set.range x = C := by
    ext y
    exact ⟨by rintro ⟨c, rfl⟩; exact (e.symm c).2, fun hy => ⟨e ⟨y, hy⟩, by simp [x]⟩⟩
  have mem : ∀ c, x c ∈ C := fun c => hr.le ⟨c, rfl⟩
  have hmono := mono_constDesc x hx
  obtain ⟨_, hi⟩ := exists_grpObj_constObj x C hr
  have hs : FinEt.IsSplitOfRank (constObj (Sp k) (Fin n)).hom n :=
    (FinEt.isSplitOfRank_iff_exists_iso _ _).mpr ⟨Iso.refl _, Category.id_comp _⟩
  have het := hs.etale
  obtain ⟨B, _, hB, q, hq, hfin, hflat, hsurj, hker⟩ :=
    L.quotient k P (constObj (Sp k) (Fin n)) (constDesc x) hi hmono hs.isFinite inferInstance
  have hw : constDesc x ≫ q = 1 := hker.w
  refine ⟨B, inferInstance, q, hB, hq, hfin, ?_, hsurj, fun y => ⟨fun hy => ?_, fun hy => ?_⟩,
    fun Y f hf => existsUnique_desc q f
      (comp_eq_of_invariant x q hker f fun c => hf _ (mem c))⟩
  · refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback (constDesc x) q hker).map (Over.forget _)).flip
      ⟨⟨hsurj, hflat⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
    exact MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback _ _) het
  · obtain ⟨z⟩ : Nonempty (𝟙_ (Over (Sp k))).left := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (hker.lift y (toUnit _) hy) z
    have : Nonempty (openObj _ V).left := ⟨(⟨z, hV⟩ : V)⟩
    have := epi_toUnit (openObj _ V)
    rw [hker.lift_fst, toUnit_unique (openι _ V) (toUnit _), cancel_epi] at hc
    exact hc ▸ mem c
  · obtain ⟨c, rfl⟩ := hr.ge hy
    rw [← constPt_desc x c, Category.assoc, hw, MonObj.comp_one]
end GlobalTheory
