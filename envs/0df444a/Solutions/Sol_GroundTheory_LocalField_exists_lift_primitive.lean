-- Prove2me | solution 1 for GroundTheory.LocalField.exists_lift_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:14.006063+00:00
-- url     : https://prove2.me/submissions/3abb1cd1-2609-4a26-99a8-23b665f7331a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Theorems.Thm_GroundTheory_LocalField_residue_aeval
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧
      P.natDegree = residueDegree K L ∧ (P.map (residue 𝒪[K])).Separable ∧
      IntermediateField.adjoin 𝓀[K] {residue 𝒪[L] β} = ⊤ := by
  obtain ⟨b, hb⟩ := Field.exists_primitive_element 𝓀[K] 𝓀[L]
  have hbi : IsIntegral 𝓀[K] b := .of_finite _ _
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := lifts_and_natDegree_eq_and_monic
    (f := residue 𝒪[K]) (p := minpoly 𝓀[K] b)
    ((lifts_iff_coeff_lifts _).2 fun n ↦ residue_surjective _) (minpoly.monic hbi)
  have hsep : (minpoly 𝓀[K] b).Separable := Algebra.IsSeparable.isSeparable 𝓀[K] b
  obtain ⟨b0, rfl⟩ := residue_surjective (R := 𝒪[L]) b
  let Q := P.map (algebraMap 𝒪[K] 𝒪[L])
  have hQ : Q.Monic := hPmon.map _
  have h1 : Q.eval b0 ∈ 𝓂[L] := by
    rw [← residue_eq_zero_iff, eval_map_algebraMap, residue_aeval K L (fun _ ↦ rfl), hPmap, minpoly.aeval]
  have h2 : IsUnit (Q.derivative.eval b0) := by
    rw [← residue_ne_zero_iff_isUnit, derivative_map, eval_map_algebraMap, residue_aeval K L (fun _ ↦ rfl),
      ← derivative_map, hPmap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨β, hβ, hβb⟩ := HenselianLocalRing.is_henselian Q hQ b0 h1 h2
  have hres : residue 𝒪[L] β = residue 𝒪[L] b0 := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hβb
  refine ⟨β, P, hPmon, ?_, ?_, ?_, ?_⟩
  · rw [← eval_map_algebraMap]
    exact hβ
  · rw [hPdeg, residueDegree_eq_finrank, ← IntermediateField.adjoin.finrank hbi, hb,
      IntermediateField.finrank_top']
  · rw [hPmap]
    exact hsep
  · rw [hres]
    exact hb
end GroundTheory.LocalField
