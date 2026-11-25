-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsFnAt.value_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:37:33.150345+00:00
-- url     : https://prove2.me/submissions/7ec6e580-7cd5-4223-93a4-b7ff8dc8ebe4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnAt_value_mul_frame
import Theorems.Thm_GlobalTheory_ThetaFn_comp_one_eq_ex_zero
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__rigT_c8abb9786299
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
theorem _root_.solution (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig)
    {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ} (h : IsFnAt u p k s θ)
    {v : Γ(T.left, ⊤)} (hv : IsValueAt A L k s 1 (rigT A L rig T k) v) :
    valAt' p.left ⊤ v = θ 0 := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
  have h1 := h.value_mul_frame (comp_one_eq_ex_zero u p) hv (fun _ => i) hi
  rw [valAt'_rigT p hrig k (fun _ => i) hi] at h1
  exact mul_right_cancel₀ (zpow_ne_zero k (u.fr_ne i 0 hi)) h1
end IsFnAt
end GlobalTheory.ThetaFn
