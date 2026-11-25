-- Prove2me | solution 1 for GlobalTheory.ArchMetric.arDeg_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:44.426715+00:00
-- url     : https://prove2.me/submissions/cf53e942-fe65-46fb-885d-4c13365d679a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_arDeg_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A : Submodule (𝓞 K) V} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchMetric
theorem _root_.solution (W : Submodule K V) {A : Submodule (𝓞 K) W} (hA : A.FG) :
    (h.restrict W).arDeg A = h.arDeg (A.map (W.subtype.restrictScalars (𝓞 K))) :=
  h.arDeg_comap _ _ hA
end GlobalTheory.ArchMetric
