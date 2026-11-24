-- Prove2me | solution 1 for GlobalTheory.ZV.VAmp.exists_veryAmpleBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:51:32.504385+00:00
-- url     : https://prove2.me/submissions/2432b191-2773-4ab5-8ee2-14f4f8ef2e28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Theorems.Thm_GlobalTheory_ZV_vAmp_iff_veryAmpleBy_equiv

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
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
namespace GlobalTheory.ZV
namespace VAmp
theorem _root_.solution {p : X ⟶ Sp K} {M : LB X} {σ : Type} [Finite σ] [Nonempty σ] {th : σ → M.Sec}
    (h : VAmp p M th) : ∃ (m : ℕ) (e : Fin (m + 1) ≃ σ), AbLaw.VeryAmpleBy p M (fun i => th (e i)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun hn => (hn ▸ e (Classical.arbitrary σ) : Fin 0).elim0
  exact ⟨m, e.symm, (vAmp_iff_veryAmpleBy_equiv p M th e.symm).1 h⟩
end VAmp
end GlobalTheory.ZV
