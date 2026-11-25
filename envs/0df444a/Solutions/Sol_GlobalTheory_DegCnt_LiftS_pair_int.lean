-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.pair_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:58:01.586777+00:00
-- url     : https://prove2.me/submissions/749e4c9f-59da-44a8-8b25-ef6331feda0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_star_one_mem
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_ipow_star
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_ipow_mul
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_line_le
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_normalForm_baseLattice_le_dualSpan_sup_line
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegCnt.LiftS
section Ideals
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Ideals
section Abstract
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
end Abstract
section Flag
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
end Flag
section Conc
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
end Conc
section Lat
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
private theorem B_smul_ist_mem_one_of_mem_ipow (a : Fin r) (ha : N.j ≤ a.val) {t : K} (ht : t ∈ ipow N.𝔡 ((r : ℤ) - a.val))
    {y : V} (hy : y ∈ N.P0) : H.B y (t • N.ist a) ∈ (1 : Submodule (𝓞 K) K) := by
  have hz : (0 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.zero_mem _
  have hle : N.P0 ≤ (1 : Submodule (𝓞 K) K).comap ((H.B.flip (t • N.ist a)).restrictScalars (𝓞 K)) := by
    apply normalForm_baseLattice_le_dualSpan_sup_line
    · intro b u hu
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.flip_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, N.ist_e b a ha, smul_eq_mul]
      split_ifs with hba
      · subst hba
        have hm := Submodule.mul_mem_mul (ipow_star N.𝔡 N.𝔡_ne N.𝔡_star _ ht) hu
        unfold NF.aa at hm
        rw [ipow_mul N.𝔡 N.𝔡_ne] at hm
        convert hm using 1
        simp only [starRingEnd_apply, mul_one]
        ring
      · simpa using hz
    · intro b hb u hu
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.flip_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, N.ist_e' b a hb ha, smul_eq_mul, mul_zero]
      exact hz
    · intro u hu
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.flip_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, N.normalForm_dual_orthogonal_last a ha, smul_eq_mul, mul_zero]
      exact hz
    · intro b hb u hu
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.flip_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, N.ist_iso b a hb ha, smul_eq_mul, mul_zero]
      exact hz
  simpa using hle hy
end Lat
section Main
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
end Main
end GlobalTheory.DegCnt.LiftS
end

set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution {x y : V} (hx : x ∈ Pst N) (hy : y ∈ N.P0) : H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
  have hle : Pst N ≤ (1 : Submodule (𝓞 K) K).comap ((H.B.flip y).restrictScalars (𝓞 K)) := by
    unfold Pst
    refine iSup_le fun a => iSup_le fun ha => line_le fun t ht => ?_
    have h := star_one_mem (B_smul_ist_mem_one_of_mem_ipow N a ha ht hy)
    rw [H.herm] at h
    simpa using h
  simpa using hle hx
end GlobalTheory.DegCnt.LiftS
