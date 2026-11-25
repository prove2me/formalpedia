-- Prove2me | solution 1 for GlobalTheory.TanBasisLocal.tanBasis_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:44:32.236111+00:00
-- url     : https://prove2.me/submissions/fd098747-f887-40f7-b493-059206ced157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsTangentVectorBasisAtPointBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TanBasisLocal
import Theorems.Thm_GlobalTheory_TanBasisLocal_dual_ext
import Theorems.Thm_GlobalTheory_TanBasisLocal_tan_pull
import Theorems.Thm_GlobalTheory_TanBasisLocal_tan_local
import Theorems.Thm_GlobalTheory_TanBasisLocal_comb_unique
import Theorems.Thm_GlobalTheory_TanBasisLocal_comb_exists
import Theorems.Thm_GlobalTheory_TanBasisLocal_coeff_compat
import Theorems.Thm_Formalism_L2_Pj_isCombAt_pull
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_dual_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.TanBasisLocal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.TanBasisLocal
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), (∀ i, TanBasis (spMap (algebraMap S (Localization.Away (h i))) ≫ x) (fun k => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ v k)) → TanBasis x v := by
  intro E _ _ _ H Dw l Xo S _ x n h hs m v hb
  have hv : ∀ k, IsTanAt x (v k) := fun k => tan_local hs fun i => (hb i).1 k
  have hb' : ∀ f : Set.range h, TanBasis (spMap (algebraMap S (Localization.Away f.1)) ≫ x)
      (fun k => spMap (dualMap (algebraMap S (Localization.Away f.1))) ≫ v k) := by
    rintro ⟨_, i, rfl⟩
    exact hb i
  refine ⟨hv, fun w hw => ?_⟩
  choose d hd hdu using fun f : Set.range h =>
    (hb' f).2 _ (tan_pull (algebraMap S (Localization.Away f.1)) hw)
  have compat : ∀ (k : Fin m) (f g : Set.range h),
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (f * g : S)) f.1 g (d f k) =
        IsLocalization.Away.awayToAwayLeft g.1 f (d g k) := by
    intro k f g
    let α : Localization.Away f.1 →+* Localization.Away (f * g : S) :=
      IsLocalization.Away.awayToAwayRight f.1 g
    let β : Localization.Away g.1 →+* Localization.Away (f * g : S) :=
      IsLocalization.Away.awayToAwayLeft g.1 f
    have hα : α.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun s => IsLocalization.Away.awayToAwayRight_eq f.1 g.1 s
    have hβ : β.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun s => IsLocalization.Away.awayToAwayLeft_eq g.1 f.1 s
    exact congrFun (coeff_compat α β hα hβ hw (hb' f) (hd f) (hd g)) k
  choose c hc hcu using fun k => Localization.existsUnique_algebraMap_eq_of_span_eq_top (Set.range h) hs
    (fun f => d f k) (compat k)
  refine ⟨c, ?_, fun a ha => funext fun k => hcu k _ fun f => ?_⟩
  · obtain ⟨w', hw'⟩ := comb_exists hv c
    have : w' = w := dual_ext hs fun i => by
      let f : Set.range h := ⟨h i, i, rfl⟩
      have h1 := isCombAt_pull (algebraMap S (Localization.Away f.1)) rfl (fun _ => rfl) rfl hw'
      have e : (fun j => algebraMap S (Localization.Away f.1) (c j)) = d f := funext fun j => hc j f
      rw [e] at h1
      exact comb_unique h1 (hd f)
    exact this ▸ hw'
  · exact congrFun (hdu f _ (isCombAt_pull (algebraMap S (Localization.Away f.1)) rfl (fun _ => rfl) rfl ha)) k
end GlobalTheory.TanBasisLocal
