-- Prove2me | solution 1 for GlobalTheory.Moduli.LevelAction.comp_eq_id_of_twists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:26.939036+00:00
-- url     : https://prove2.me/submissions/bad3c2e2-3504-4507-bfdc-07db2a40c934

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_exists_comp_sabMap
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_mem_of_modN
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_eta_congr
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_etaA_congr

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
open GlobalTheory GlobalTheory.Moduli GlobalTheory.Moduli.LevelAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.Moduli.LevelAction
theorem _root_.solution {l : Level H} (Xo : Moduli D l) {g g' : Sim D} (hred : IsReduced Xo.X)
    (i : ObjMap Xo.univ Xo.univ (𝟙 _)) {f f' : Xo.X ⟶ Xo.X} (h : Twists Xo g f) (h' : Twists Xo g' f')
    (hM : ∀ a, D.ModN l.M (g.f l.M (g'.f l.M a) - a)) (hA : ∀ a, D.ModN l.A (g.f l.A (g'.f l.A a) - a)) :
    f ≫ f' = 𝟙 _ := by
  obtain ⟨hf, ν, e₁, e₂⟩ := h
  obtain ⟨hf', ν', e₁', e₂'⟩ := h'
  obtain ⟨n, hn⟩ := exists_comp_sabMap ν ν' rfl
  refine (Xo.rep _ Xo.s hred Xo.univ).unique ⟨by rw [Category.assoc, hf', hf], ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩⟩
    ⟨Category.id_comp _, ⟨i⟩⟩
  · show _ ≫ n.φ = _
    rw [hn, Category.assoc, ← e₁', ← Category.assoc, ← Category.assoc, ← e₁,
      eta_congr Xo.univ (mem_of_modN l (hM a))]
  · show _ ≫ n.φ = _
    rw [hn, Category.assoc, ← e₂', ← Category.assoc, ← Category.assoc, ← e₂, etaA_congr Xo.univ (hA a)]
end GlobalTheory.Moduli.LevelAction
