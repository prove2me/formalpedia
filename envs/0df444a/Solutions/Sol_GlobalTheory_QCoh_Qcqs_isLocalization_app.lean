-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.isLocalization_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:31:51.811345+00:00
-- url     : https://prove2.me/submissions/478c2bbc-703d-4cbb-bcb0-a07001d00e5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_algebraMap
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))
include H
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution {V : X.Opens} (hV : IsAffineOpen V) :
    letI := (g.app V).hom.toAlgebra
    IsLocalization (S.map (baseRingHom p V).hom) Γ(Y, g ⁻¹ᵁ V) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have po' : IsPushout (baseRingHom p V) (CommRingCat.ofHom (algebraMap R L)) (g.app V)
      (baseRingHom q (g ⁻¹ᵁ V)) := by
    refine po.of_iso (Scheme.ΓSpecIso R) (Iso.refl _) (Scheme.ΓSpecIso L) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [baseRingHom]
  let := (g.app V).hom.toAlgebra
  let := (baseRingHom p V).hom.toAlgebra
  let := (baseRingHom q (g ⁻¹ᵁ V)).hom.toAlgebra
  let := (baseRingHom (g ≫ p) (g ⁻¹ᵁ V)).hom.toAlgebra
  have : IsScalarTower R Γ(X, V) Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (app_baseRingHom g p V r).symm
  have : IsScalarTower R L Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap H _ r).symm
  exact (Algebra.isLocalization_iff_isPushout S L).mpr
    (CommRingCat.isPushout_iff_isPushout.mp po')
end GlobalTheory.QCoh.Qcqs
