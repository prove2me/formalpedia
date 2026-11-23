-- Prove2me | solution 1 for GlobalTheory.exists_smul_mem_of_mem_span_fraction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:24.474876+00:00
-- url     : https://prove2.me/submissions/e0962e70-81a4-4c38-9467-8c17c1308911

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Theorems.Thm_GlobalTheory_LatticeBoundedAction_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (v : V) (hv : v ∈ Submodule.span K (Λ : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • v ∈ Λ := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_8 h_9 h_10 h_11; revert R K h_2 h_3 h_4 h_5 h_6 V h_8 h_9 h_10 h_11 Λ v hv; exact @_root_.GlobalTheory.LatticeBoundedAction.main)
  | exact @_root_.GlobalTheory.LatticeBoundedAction.main
  | exact _root_.GlobalTheory.LatticeBoundedAction.main
  | (apply _root_.GlobalTheory.LatticeBoundedAction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBoundedAction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBoundedAction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBoundedAction.main ..)
end GlobalTheory
