-- Prove2me | solution 1 for GlobalTheory.LevelFibre.mem_of_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:02.04992+00:00
-- url     : https://prove2.me/submissions/be6a2c82-9090-4f71-a4c3-19af17e3057c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
import Theorems.Thm_GlobalTheory_LevelFibre_level_split
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
theorem _root_.solution (l : Level H) (J : TateIso D k Q act e) (P : D.La → Q) (hP : ∀ a b, P (a + b) = P a * P b)
    (hk : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), P a = 1)
    (hJ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), P a = J.ev l.M a)
    {c : D.La} (hc : P c = 1) : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨u, hu, v, hv, huv⟩ := level_split l
  have hcs : c = u • c + v • c := by rw [← add_smul, huv, one_smul]
  have h1 : u • c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.smul_mem_smul hu trivial
  have h2 : J.ev l.M (v • c) = 1 := by
    rw [← hJ _ (Submodule.smul_mem_smul hv trivial)]
    rw [hcs, hP, hk _ h1, _root_.one_mul] at hc
    exact hc
  rw [hcs]
  exact Submodule.add_mem _ h1 (mem_of_modN l ((J.ker _ (level_pos l) _).1 h2))
end GlobalTheory.LevelFibre
