-- Prove2me | solution 1 for GlobalTheory.Frames.SecCalc.sec_calc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:08.816249+00:00
-- url     : https://prove2.me/submissions/368833c0-431c-4b0d-a838-60c0a6ce2b74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ScaledBaseChangeFibreSectionCalculus
import Theorems.Thm_P2M_GlobalTheory_Frames_SecCalc_spMap_comp__7a01e427db9f
import Theorems.Thm_P2M_GlobalTheory_Frames_SecCalc_spMap_id__02584de24f07
import Theorems.Thm_P2M_GlobalTheory_Frames_SecCalc_scal_mul__7e52c5a25909
import Theorems.Thm_P2M_GlobalTheory_Frames_SecCalc_scal_add__eab1234a9fdc
import Theorems.Thm_P2M_GlobalTheory_Frames_SecCalc_scal_one__7e65ea0a63c7
import Theorems.Thm_P2M_GlobalTheory_Frames_SecCalc_scal_pull__3b720095437c
import Theorems.Thm_GlobalTheory_Frames_SecCalc_pm_exists
import Theorems.Thm_GlobalTheory_Frames_SecCalc_secBC_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.SecCalc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.Frames.SecCalc
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T U : Type) [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (x'' : Sp U ⟶ Xo.X), x' = spMap φ ≫ x → x'' = spMap ψ ≫ x' → (∀ (a : S) s s' s'', SecBC φ a x x' s s' → (SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'')) ∧ (∀ (a : S) (s t : LB.Sec (PPx x)), SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i) ∧ (∀ (a : S) s (s' t' : LB.Sec (PPx x')), SecBC φ 1 x x' s s' → (SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i)) ∧ (∀ (a b : S) i, scal x (a * b) i = scal x a i * scal x b i ∧ scal x (a + b) i = scal x a i + scal x b i ∧ scal x 1 i = 1) := by
  intro E _ _ _ H Dw l Xo S T U _ _ _ φ ψ x x' x'' hx hx'
  obtain ⟨p, ps, pf⟩ := pm_exists φ hx
  obtain ⟨q, qs, qf⟩ := pm_exists ψ hx'
  refine ⟨fun a s s' s'' h => ?_, fun a s t => ?_, fun a s s' t' h => ?_,
    fun a b i => ⟨scal_mul' x a b i, scal_add' x a b i, scal_one' x i⟩⟩
  · have rs : (q ≫ p) ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x'') Xo.univ.t.G).left := by
      rw [Category.assoc, ps, qs]
    have rf : (q ≫ p) ≫ (fst (Over.mk x) Xo.univ.t.G).left =
        (fst (Over.mk x'') Xo.univ.t.G).left ≫ spMap (ψ.comp φ) := by
      rw [Category.assoc, pf, ← Category.assoc, qf, Category.assoc, spMap_comp']
    rw [secBC_iff φ a p ps pf] at h
    rw [secBC_iff ψ 1 q qs qf, secBC_iff (ψ.comp φ) a (q ≫ p) rs rf]
    refine forall_congr' fun i => ?_
    have e : (q ≫ p).appLE _ _ (ppx_le (q ≫ p) rs i) = p.appLE _ _ (ppx_le p ps i) ≫ q.appLE _ _ (ppx_le q qs i) :=
      (Scheme.Hom.appLE_comp_appLE q p _ _ _ _ _).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, h i, map_one, scal_one' x'' i, _root_.one_mul, map_mul,
      scal_pull' ψ q qf]
    rfl
  · rw [secBC_iff (RingHom.id S) a (𝟙 (Gx x)) (Category.id_comp _)
      (by rw [spMap_id']; exact (Category.id_comp _).trans (Category.comp_id _).symm)]
    refine forall_congr' fun i => ?_
    have e : ∀ hh : (PPx x).U i ≤ (𝟙 (Gx x) : Gx x ⟶ Gx x) ⁻¹ᵁ (PPx x).U i,
        (𝟙 (Gx x) : Gx x ⟶ Gx x).appLE _ _ hh = 𝟙 _ := by
      intro hh
      exact (Scheme.Hom.appLE_eq_app (𝟙 (Gx x) : Gx x ⟶ Gx x)).trans (Scheme.Hom.id_app _)
    rw [e]
    rfl
  · rw [secBC_iff φ 1 p ps pf] at h
    rw [secBC_iff φ a p ps pf]
    refine forall_congr' fun i => ?_
    rw [h i, map_one, scal_one' x' i, _root_.one_mul]
end GlobalTheory.Frames.SecCalc
