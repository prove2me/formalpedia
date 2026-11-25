-- Prove2me | solution 1 for GlobalTheory.ZJ.Charts.exists_proper_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:58:13.8158+00:00
-- url     : https://prove2.me/submissions/3f8c5ce5-cc5c-490c-8022-3851662c7d7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
import Theorems.Thm_GlobalTheory_ZJ_mem_range_appLE_chart_iff
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_ProjSpace_IsCoordFamily_pullRatio_toHom
import Theorems.Thm_GlobalTheory_ProjSpace_IsCoordFamily_toHom_preimage
import Theorems.Thm_GlobalTheory_ProjSpace_IsCoordFamily_toHom_str
import Theorems.Thm_GlobalTheory_ProjSpace_isAffineOpen_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isProper_str
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_appLE_of_eq


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
noncomputable section
open GlobalTheory GlobalTheory.ZJ
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs
namespace GlobalTheory.ZJ
namespace Charts
theorem _root_.solution {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) (C : Charts Y)
    [Nonempty Y] : ∃ (B : Scheme.{0}) (p : B ⟶ Sp R) (q : Y ⟶ B), q ≫ p = f ∧ IsProper p ∧ IsAffineHom q ∧
      ∃ V : {i // C.wt i = C.c₀} → B.Opens, ⨆ a, V a = ⊤ ∧ ∀ a, IsAffineOpen (V a) ∧ ∃ h : C.W a = q ⁻¹ᵁ V a,
        Function.Injective (q.appLE (V a) (C.W a) h.le).hom ∧ ∀ u,
          u ∈ Set.range (q.appLE (V a) (C.W a) h.le).hom ↔
          u ∈ Subring.closure (Set.range (f.appLE ⊤ (C.W a) le_top).hom ∪
            {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r a j}) := by
  have hne : Nonempty {i // C.wt i = C.c₀} := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    obtain ⟨a, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (C.cover.ge (Set.mem_univ y))
    exact ⟨a⟩
  obtain ⟨n, ⟨e₀⟩⟩ := Finite.exists_equiv_fin {i // C.wt i = C.c₀}
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := by
    cases n with
    | zero => exact (e₀ hne.some).elim0
    | succ N => exact ⟨N, rfl⟩
  let e := e₀.symm
  have hC : IsCoordFamily (fun i : Fin (N + 1) => C.W (e i)) (fun i j => C.r (e i) (e j).1) :=
    { cover := (e.iSup_comp (g := C.W)).trans C.cover
      self := fun i => C.r_self _
      mul := fun i j k => (C.trans _ _ _).symm
      basicOpen_le := fun i j => (C.inter _ _).ge.trans inf_le_right }
  obtain ⟨φ, hφ, hpre, hr⟩ : ∃ φ : Y ⟶ PSpace R N, φ ≫ PSpace.str R N = f ∧
      ∃ hpre : ∀ i, φ ⁻¹ᵁ chart R N i = C.W (e i), ∀ i j,
        pullRatio φ (C.W (e i)) i (hpre i).ge j = C.r (e i) (e j).1 :=
    ⟨hC.toHom f, hC.toHom_str f, hC.toHom_preimage f, hC.pullRatio_toHom f⟩
  have haff : IsAffineHom φ := isAffineHom_of_forall_exists_isAffineOpen φ fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 ((iSup_chart R N).ge (Set.mem_univ x))
    exact ⟨_, hi, isAffineOpen_chart R N i, (hpre i).symm ▸ C.aff _⟩
  have hq : ∀ i, C.W (e i) = φ.toImage ⁻¹ᵁ φ.imageι ⁻¹ᵁ chart R N i := fun i => by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toImage_imageι, hpre]
  have hV : ∀ i, IsAffineOpen (φ.imageι ⁻¹ᵁ chart R N i) := fun i => (isAffineOpen_chart R N i).preimage _
  have hcov : ⨆ i, φ.imageι ⁻¹ᵁ chart R N i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_chart, Scheme.Hom.preimage_top]
  have := isProper_str R N
  refine ⟨φ.image, φ.imageι ≫ PSpace.str R N, φ.toImage, by rw [Scheme.Hom.toImage_imageι_assoc, hφ],
    inferInstance, ?_, fun a => φ.imageι ⁻¹ᵁ chart R N (e₀ a),
    (e₀.iSup_comp (g := fun i => φ.imageι ⁻¹ᵁ chart R N i)).trans hcov, fun a => ?_⟩
  · refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ x))
    exact ⟨_, hi, hV i, hq i ▸ C.aff _⟩
  · obtain ⟨i, rfl⟩ := e.surjective a
    have hi : e₀ (e i) = i := e₀.apply_symm_apply i
    beta_reduce
    rw [hi]
    refine ⟨hV i, hq i, ?_, fun u => ?_⟩
    · have key : ∀ (W : Y.Opens) (h : W = φ.toImage ⁻¹ᵁ φ.imageι ⁻¹ᵁ chart R N i),
          Function.Injective (φ.toImage.appLE _ W h.le).hom := by
        rintro _ rfl
        rw [Scheme.Hom.appLE_eq_app]
        exact φ.toImage_app_injective ⟨_, isAffineOpen_chart R N i⟩
      exact key _ (hq i)
    · have hs : {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r (e i) j} =
          Set.range (pullRatio φ (C.W (e i)) i (hpre i).ge) := by
        ext v
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨e₀ ⟨j, hj⟩, (hr i _).trans (by rw [show e (e₀ ⟨j, hj⟩) = ⟨j, hj⟩ from e₀.symm_apply_apply _])⟩
        · rintro ⟨j, rfl⟩
          exact ⟨_, (e j).2, hr i j⟩
      rw [hs, ← hφ, ← mem_range_appLE_chart_iff]
      have hc : ∀ v, (φ.toImage.appLE _ _ (hq i).le).hom ((φ.imageι.app (chart R N i)).hom v) =
          (φ.appLE (chart R N i) _ (hpre i).ge).hom v := fun v => by
        rw [Scheme.Hom.app_eq_appLE, appLE_appLE]
        exact congrArg (fun ψ : _ ⟶ Γ(Y, C.W (e i)) => ψ.hom v) (appLE_of_eq φ.toImage_imageι _ _ _ _)
      constructor
      · rintro ⟨w, rfl⟩
        obtain ⟨v, rfl⟩ := φ.imageι.app_surjective _ (isAffineOpen_chart R N i) w
        exact ⟨v, (hc v).symm⟩
      · rintro ⟨v, rfl⟩
        exact ⟨_, hc v⟩
end Charts
end GlobalTheory.ZJ
