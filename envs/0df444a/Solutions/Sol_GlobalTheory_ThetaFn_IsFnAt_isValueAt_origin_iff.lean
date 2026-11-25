-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsFnAt.isValueAt_origin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:07.260849+00:00
-- url     : https://prove2.me/submissions/bf16e6df-d72d-4388-9ccb-e48509e86ac6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnAt_isValueAt_of_isIso
import Theorems.Thm_GlobalTheory_ThetaFn_comp_one_eq_ex_zero
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__rigT_c8abb9786299
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnAt_value_origin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
variable (u p)
variable {u p}
namespace GlobalTheory.ThetaFn
namespace IsFnAt
theorem _root_.solution [IsIso p] (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))}
    (hrig : u.IsRig rig) {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) (v : Γ(T.left, ⊤)) :
    IsValueAt A L k s 1 (rigT A L rig T k) v ↔ valAt' p.left ⊤ v = θ 0 :=
  ⟨h.value_origin hL hrig, fun hv => h.isValueAt_of_isIso (comp_one_eq_ex_zero u p) fun j hj => by
    rw [valAt'_rigT p hrig k j hj, hv]⟩
end IsFnAt
end GlobalTheory.ThetaFn
