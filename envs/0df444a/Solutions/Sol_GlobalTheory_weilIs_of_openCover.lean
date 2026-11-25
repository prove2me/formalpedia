-- Prove2me | solution 1 for GlobalTheory.weilIs_of_openCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:07.060229+00:00
-- url     : https://prove2.me/submissions/66a60235-030b-4ee0-9451-fd9cdbde1d09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsIffOfIsGrpPullbackComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsLocalOnBaseOfOpenCover
import Theorems.Thm_GlobalTheory_WeilLocal_local_of_openImmersion
import Theorems.Thm_GlobalTheory_CoverGlue_exists_mem
import Theorems.Thm_GlobalTheory_weilIs_iff_of_isGrpPullback_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm


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
open GlobalTheory.ZM
namespace GlobalTheory
theorem _root_.solution : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (k : ℤ) (x y : Out.baseOver S ⟶ A) (x' y' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i) (c : Γ(S, ⊤)ˣ), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, (y' i).left ≫ ψ i = (U i).ι ≫ y.left) → (∀ i, Out.WeilIs (G i) (M i) k (x' i) (y' i) (Units.map (U i).ι.appTop.hom.toMonoidHom c)) → Out.WeilIs A L k x y c := by
  intro S I U A _ G _ ψ hU hψ L M hL hM hML hA hG k x y x' y' c hx hy hW
  haveI : IsCommMonObj A := hA.comm
  unfold Out.WeilIs
  intro p
  obtain ⟨i, hi⟩ := GlobalTheory.CoverGlue.exists_mem hU p
  obtain ⟨j, hj⟩ : ∃ j : Over.mk ((Out.baseOver (U i).toScheme).hom ≫ (U i).ι) ⟶ Out.baseOver S,
      j.left = (U i).ι := ⟨Over.homMk (U i).ι (by simp [Out.baseOver]), rfl⟩
  haveI : IsOpenImmersion j.left := by
    rw [hj]
    infer_instance
  have hx₀ : (j ≫ x).left = (x' i).left ≫ ψ i := by rw [Over.comp_left, hj, hx i]
  have hy₀ : (j ≫ y).left = (y' i).left ≫ ψ i := by rw [Over.comp_left, hj, hy i]
  have H₀ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm S (U i).toScheme A (G i) (U i).ι (ψ i) L (M i) hL (hM i)
    (hψ i) (hML i) (Out.baseOver (U i).toScheme) k (x' i) (y' i) (j ≫ x) (j ≫ y)
    (Units.map (U i).ι.appTop.hom.toMonoidHom c) hx₀ hy₀).1 (hW i)
  have H₁ : Out.WeilIs A L k (j ≫ x) (j ≫ y) (Units.map j.left.appTop.hom.toMonoidHom c) := by
    rw [hj]
    exact H₀
  obtain ⟨V, hV, hl, hc⟩ := GlobalTheory.WeilLocal.local_of_openImmersion hL j H₁ ⟨p, hi⟩
  refine ⟨V, ?_, hl, hc⟩
  rw [hj] at hV
  exact hV
end GlobalTheory
