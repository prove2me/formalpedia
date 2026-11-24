-- Prove2me | solution 1 for GlobalTheory.KS.TangentAt.comp_eq_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:58.237073+00:00
-- url     : https://prove2.me/submissions/38e6600b-3bf8-4338-b8b8-35bbd30a5e2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationUniformisedAbelianVarietyUniqueVec
import Theorems.Thm_GlobalTheory_KS_TangentAt_fst_dval
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.TangentAt
private theorem ΓSpecIso_appLE_spMap_top {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e : (⊤ : (Sp S).Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((Scheme.Hom.appLE (spMap φ) ⊤ ⊤ e).hom a) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
  have key := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  rw [← key]
  rfl
private theorem top_le_preimage_top' {X Y : Scheme.{0}} (f : X ⟶ Y) : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
end GlobalTheory.KS.TangentAt
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.TangentAt
namespace GlobalTheory.KS.TangentAt
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Sp ℂ) (v : Sp (DualNumber ℂ) ⟶ X)
    (h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ p = 𝟙 _)
    (h2 : ∀ a, (dval v ⊤ le_top (constFn p ⊤ a)).snd = 0) :
    v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) := by
  have hD : ∀ c : ℂ, dval (v ≫ p) ⊤ (top_le_preimage_top' _) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c) =
      algebraMap ℂ (DualNumber ℂ) c := by
    intro c
    apply TrivSqZeroExt.ext
    · rw [fst_dval, h1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
        show (𝟙 (Sp ℂ)) = spMap (RingHom.id ℂ) by simp [spMap],
        valAt', dif_pos (top_le_preimage_top' _), valAt]
      exact (ΓSpecIso_appLE_spMap_top (RingHom.id ℂ) _ _).trans (by simp)
    · rw [dval_comp v p ⊤ (top_le_preimage_top' _) ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _)]
      refine (h2 c).trans ?_
      rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv,
    ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  refine (hD c).trans ?_
  have k := ΓSpecIso_appLE_spMap_top (algebraMap ℂ (DualNumber ℂ)) (top_le_preimage_top' _)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)
  rw [Iso.inv_hom_id_apply] at k
  exact k.symm
end GlobalTheory.KS.TangentAt
