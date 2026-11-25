-- Prove2me | solution 1 for GlobalTheory.LevelFibre.sub_mem_of_inGam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:19.145039+00:00
-- url     : https://prove2.me/submissions/f30f7e1a-bb50-4cee-bde2-105caddf0bb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
import Theorems.Thm_GlobalTheory_LevelFibre_mem_of_modN
import Theorems.Thm_GlobalTheory_LevelFibre_level_pos

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
open GlobalTheory GlobalTheory.LevelFibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
namespace GlobalTheory.LevelFibre
theorem _root_.solution {l l₂ : Level H} (hd : l.Dvd l₂) {g : Sim D} (hg : g.InGam l l₂) (a : D.La) :
    g.f l₂.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨d, hdd⟩ := hd.1
  have hd0 : 0 < d := Nat.pos_of_mul_pos_left (hdd ▸ level_pos l₂)
  have h := mem_of_modN l (g.tower l.M d (level_pos l) hd0 a)
  rw [← hdd] at h
  have := Submodule.add_mem _ h (hg.2.1 a)
  rwa [sub_add_sub_cancel] at this
end GlobalTheory.LevelFibre
