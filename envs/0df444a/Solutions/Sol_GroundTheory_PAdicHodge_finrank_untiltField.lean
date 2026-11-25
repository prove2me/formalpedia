-- Prove2me | solution 1 for GroundTheory.PAdicHodge.finrank_untiltField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:22:44.967263+00:00
-- url     : https://prove2.me/submissions/ebe485ac-f317-4894-acf1-c95e7f56952d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep
import Definitions.Def_GroundTheory_PAdicHodge_UntiltDegree
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_tiltSharp_mem_untiltField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    Module.finrank K (untiltField K C p N) = Module.finrank K♭ N := by
  obtain ⟨w, t, r, ρ, -, -, -, -, -, -, -, hwN, -, -, -, -, hli, hsub⟩ :=
    exists_untiltField_basis (K := K) (C := C) (p := p) N
  set V := Submodule.span K (Set.range fun i => tiltSharp C p (w i))
  have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
  apply le_antisymm
  · let f : untiltField K C p N →ₗ[K] V :=
      { toFun := fun y => ⟨y, hsub y y.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg Subtype.val h :)
    calc Module.finrank K (untiltField K C p N) ≤ Module.finrank K V :=
          LinearMap.finrank_le_finrank_of_injective hf
      _ ≤ Fintype.card (Fin (Module.finrank K♭ N)) := finrank_range_le_card _
      _ = _ := Fintype.card_fin _
  · let u : Fin (Module.finrank K♭ N) → untiltField K C p N :=
      fun i => ⟨tiltSharp C p (w i), tiltSharp_mem_untiltField (hwN i)⟩
    have hu : LinearIndependent K u :=
      LinearIndependent.of_comp (IntermediateField.val _).toLinearMap hli
    simpa using hu.fintype_card_le_finrank
end GroundTheory.PAdicHodge
