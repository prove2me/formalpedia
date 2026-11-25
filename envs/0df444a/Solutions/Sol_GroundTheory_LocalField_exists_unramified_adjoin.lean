-- Prove2me | solution 1 for GroundTheory.LocalField.exists_unramified_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:39.610403+00:00
-- url     : https://prove2.me/submissions/6cfbb53a-db5b-40c6-a4ed-b1a308fa9c96

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Theorems.Thm_GroundTheory_LocalField_isScalarTower_residueField
import Theorems.Thm_GroundTheory_LocalField_exists_lift_primitive
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_one_iff_surjective
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_algebraMap_mem_integer_iff
import Theorems.Thm_GroundTheory_LocalField_isUnramified_iff_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos
import Theorems.Thm_GroundTheory_LocalField_residueDegree_tower


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
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ (P.map (residue 𝒪[K])).Separable ∧
      IsUnramified K K⟮(β : L)⟯ ∧ Module.finrank K K⟮(β : L)⟯ = residueDegree K L ∧
      residueDegree K⟮(β : L)⟯ L = 1 := by
  obtain ⟨β, P, hPm, hβ, hdeg, hsep, hgen⟩ := exists_lift_primitive K L
  set T := K⟮(β : L)⟯ with hT
  have hβL : aeval (β : L) P = 0 := by
    have := aeval_algHom_apply (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) β P
    rw [hβ, map_zero] at this
    exact this
  have hle : Module.finrank K T ≤ residueDegree K L := by
    have hi : IsIntegral K (β : L) := .of_finite K _
    rw [hT, IntermediateField.adjoin.finrank hi, ← hdeg]
    have hne : P.map (algebraMap 𝒪[K] K) ≠ 0 := (hPm.map _).ne_zero
    have hd := minpoly.dvd K (β : L) (p := P.map (algebraMap 𝒪[K] K))
      (by rw [aeval_map_algebraMap]; exact hβL)
    calc (minpoly K (β : L)).natDegree ≤ (P.map (algebraMap 𝒪[K] K)).natDegree :=
          natDegree_le_of_dvd hd hne
      _ = P.natDegree := hPm.natDegree_map _
  have hβT : (β : L) ∈ T := IntermediateField.mem_adjoin_simple_self K _
  let βT : 𝒪[T] := ⟨⟨β, hβT⟩, (algebraMap_mem_integer_iff T L _).1 β.2⟩
  have hsurj : Function.Surjective (algebraMap 𝓀[T] 𝓀[L]) := by
    have := isScalarTower_residueField K T L (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    have hb : residue 𝒪[L] β ∈ (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range :=
      ⟨residue 𝒪[T] βT, rfl⟩
    have htop : Algebra.adjoin 𝓀[K] {residue 𝒪[L] β} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite _ _), hgen, IntermediateField.top_toSubalgebra]
    have hr : (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range = ⊤ :=
      eq_top_iff.2 (htop ▸ Algebra.adjoin_le (Set.singleton_subset_iff.2 hb))
    intro y
    obtain ⟨z, hz⟩ := (hr ▸ Algebra.mem_top : y ∈ (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range)
    exact ⟨z, hz⟩
  have h1 : residueDegree T L = 1 := (residueDegree_eq_one_iff_surjective L T).2 hsurj
  have htower := residueDegree_tower K T L
  rw [h1, mul_one] at htower
  have hfe : residueDegree K T ≤ Module.finrank K T := by
    rw [← ramificationIndex_mul_residueDegree K T]
    exact Nat.le_mul_of_pos_left _ (ramificationIndex_pos K T)
  have heq : Module.finrank K T = residueDegree K T := by omega
  exact ⟨β, P, hPm, hβ, hsep, (isUnramified_iff_residueDegree_eq_finrank K T).2 heq.symm,
    heq.trans htower.symm, h1⟩
end GroundTheory.LocalField
