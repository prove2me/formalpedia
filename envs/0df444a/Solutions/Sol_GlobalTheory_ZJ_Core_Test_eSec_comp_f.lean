-- Prove2me | solution 1 for GlobalTheory.ZJ.Core.Test.eSec_comp_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:50:43.118311+00:00
-- url     : https://prove2.me/submissions/9f2e0c45-dab5-4f70-b0fa-82504f4a8be5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesian
import Theorems.Thm_GlobalTheory_ZJ_eSec_comp_of_isGrpPullback
import Theorems.Thm_GlobalTheory_TorusConst_Glue_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
namespace Core.Test
theorem _root_.solution {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y) :
    (eSec τ.H ≫ τ.f : Sp τ.V ⟶ C.G.toScheme) = τ.y₀ ≫ C.e := by
  have := C.proper
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  have : IsDominant (Out.jK τ.V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective τ.V _)]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated C.GG.hom ?_ (Out.jK τ.V) ?_
  · have h₁ : (eSec τ.H ≫ τ.H.hom : Sp τ.V ⟶ Sp τ.V) = 𝟙 _ := Over.w η[τ.H]
    have h₂ : C.e ≫ C.GG.hom = 𝟙 _ := C.e_sec
    rw [Category.assoc, Category.assoc, τ.f_over, h₂, Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.y₀) h₁).trans (Category.id_comp _))
  · have h₁ := @eSec_comp_of_isGrpPullback _ _ _ _ (_) (_) _ _ τ.φ_cart
    have h₂ := eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (Out.jK τ.V))
    rw [← reassoc_of% τ.yK_fac, C.e_zero]
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.a) h₁) |>.trans (Category.assoc _ _ _))
    rw [τ.φ_f]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) h₂.symm).trans (Category.assoc _ _ _))
end Core.Test
end GlobalTheory.ZJ
