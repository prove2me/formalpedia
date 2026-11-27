-- Prove2me | solution 1 for GroundTheory.Global.Modulus.mem_rayUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:11.006952+00:00
-- url     : https://prove2.me/submissions/09b4fc1f-e7f1-45a3-8e19-e2d01b255b2c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_Modulus_one_le_exponent_iff
import Theorems.Thm_GroundTheory_Global_Modulus_mem_idelesOneMod
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_mem_unitsLevel_of_one_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal



set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)
namespace GroundTheory.Global.Modulus
theorem _root_.solution {a : Kˣ} :
    a ∈ 𝔪.rayUnits ↔
      (∀ v, v.asIdeal ∣ 𝔪.ideal → v.valuation K ((a : K) - 1) ≤ exp (-(𝔪.exponent v : ℤ))) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.embedding_of_isReal w.2 (a : K) := by
  rw [rayUnits, Subgroup.mem_comap, mem_idelesOneMod]
  refine and_congr (forall_congr' fun v ↦ forall_congr' fun hv ↦ ?_)
    (forall_congr' fun w ↦ forall_congr' fun _ ↦ ?_)
  · have hc : ∀ k : K, (k : v.adicCompletion K) = algebraMap K (v.adicCompletion K) k := fun k ↦ by
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [mem_unitsLevel_of_one_le ((𝔪.one_le_exponent_iff v).2 hv), coe_finiteProj_diagonal,
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hc, hc,
      (algebraMap K (v.adicCompletion K)).map_sub, (algebraMap K (v.adicCompletion K)).map_one]
  · rw [coe_infiniteProj_diagonal]
    exact Iff.of_eq (congrArg (0 < ·) (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe _ _))
end GroundTheory.Global.Modulus
