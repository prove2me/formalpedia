-- Prove2me | solution 1 for GroundTheory.LocalField.mem_of_residueDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:23.641318+00:00
-- url     : https://prove2.me/submissions/44ceda41-1bc4-42fe-9d48-7e65a19e735c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Theorems.Thm_GroundTheory_LocalField_residue_aeval
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_one_iff_surjective

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
theorem _root_.solution (F : IntermediateField K L) (hF : residueDegree F L = 1)
    (P : 𝒪[K][X]) (hP : P.Monic) (γ : 𝒪[L]) (hγ : aeval γ P = 0)
    (hd : IsUnit (aeval γ (derivative P))) : (γ : L) ∈ F := by
  have hsurj := (residueDegree_eq_one_iff_surjective L F).1 hF
  have hinj : Function.Injective (algebraMap 𝓀[F] 𝓀[L]) := (algebraMap 𝓀[F] 𝓀[L]).injective
  obtain ⟨c₀', hc₀'⟩ := hsurj (residue 𝒪[L] γ)
  obtain ⟨c₀, rfl⟩ := residue_surjective (R := 𝒪[F]) c₀'
  have hc₀ : residue 𝒪[L] (algebraMap 𝒪[F] 𝒪[L] c₀) = residue 𝒪[L] γ := hc₀'

  have key : ∀ Q : 𝒪[K][X], algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] (aeval c₀ Q)) =
      residue 𝒪[L] (aeval γ Q) := by
    intro Q
    rw [show algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] (aeval c₀ Q)) =
        residue 𝒪[L] (algebraMap 𝒪[F] 𝒪[L] (aeval c₀ Q)) from rfl, ← aeval_algebraMap_apply,
      residue_aeval K L (fun _ ↦ rfl), hc₀, ← residue_aeval K L (fun _ ↦ rfl)]
  let Q := P.map (algebraMap 𝒪[K] 𝒪[F])
  have h1 : Q.eval c₀ ∈ 𝓂[F] := by
    rw [← residue_eq_zero_iff, eval_map_algebraMap]
    apply hinj
    rw [key, hγ, map_zero, map_zero]
  have h2 : IsUnit (Q.derivative.eval c₀) := by
    rw [← residue_ne_zero_iff_isUnit, derivative_map, eval_map_algebraMap]
    intro h0
    have := key (derivative P)
    rw [h0, map_zero] at this
    exact (residue_ne_zero_iff_isUnit _).2 hd this.symm
  obtain ⟨c, hc, hcc₀⟩ := HenselianLocalRing.is_henselian Q (hP.map _) c₀ h1 h2
  have hcF : aeval c P = 0 := by
    rw [← eval_map_algebraMap]
    exact hc
  set c' := algebraMap 𝒪[F] 𝒪[L] c
  have hc' : aeval c' P = 0 := by
    rw [aeval_algebraMap_apply, hcF, map_zero]
  have hres : residue 𝒪[L] c' = residue 𝒪[L] γ := by
    rw [← hc₀]
    have : residue 𝒪[F] c = residue 𝒪[F] c₀ := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hcc₀
    change algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] c) = algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] c₀)
    rw [this]
  have heq : γ = c' := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.map (algebraMap 𝒪[K] 𝒪[L]))
      (by rw [eval_map_algebraMap]; exact hγ) (by rw [eval_map_algebraMap]; exact hc') ?_ ?_
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]
    · rw [derivative_map, eval_map_algebraMap]
      exact hd
  rw [heq]
  exact (c : F).2
end GroundTheory.LocalField
