-- Prove2me | solution 1 for GlobalTheory.TanMod.exists_tangent_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:45.565683+00:00
-- url     : https://prove2.me/submissions/5c3377e3-0d67-4cb2-9d16-1c3da1786b56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Theorems.Thm_GlobalTheory_TanMod_smT_zero_of
import Theorems.Thm_GlobalTheory_TanMod_unit_of_smT_zero
import Theorems.Thm_GlobalTheory_TanMod_TanSp_pt_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TanMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
namespace GlobalTheory.TanMod
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module S N) (v : N → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (ρ : 𝓞 E →+* Module.End S N), Function.Injective v ∧ (∀ w, IsTanAt x w ↔ w ∈ Set.range v) ∧ (∀ (n : ℕ) (b : Fin n → N) (a : Fin n → S) w, IsCombAt x (fun i => v (b i)) a w ↔ w = v (∑ i, a i • b i)) ∧ (∀ a m, v (ρ a m) = v m ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (s : S) m, v (s • m) = spMap (epsMul s) ≫ v m := by
  intro E _ _ _ H Dw l Xo S _ x
  refine ⟨TanSp x Xo.univ.t.G, inferInstance, inferInstance, fun m => m.pt.left, TanSp.act x Xo.univ.t.act,
    fun m n h => TanSp.ext (Over.OverMorphism.ext h), fun w => ⟨fun h => ?_, ?_⟩, fun n b a w => ⟨?_, ?_⟩,
    fun a m => rfl, fun s m => rfl⟩
  · exact ⟨TanSp.mk (Over.homMk w h.1) (smT_zero_of x _ h.2), rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨Over.w m.pt, unit_of_smT_zero x _ m.tan⟩
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst this
    rw [List.prod_ofFn, ← TanSp.pt_sum]
  · rintro rfl
    exact ⟨fun i => (a i • b i).pt, fun i => rfl, by rw [List.prod_ofFn, ← TanSp.pt_sum]⟩
end GlobalTheory.TanMod
