-- Prove2me | solution 1 for GroundTheory.PAdicHodge.tiltIntermediateField_untiltField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:46.931802+00:00
-- url     : https://prove2.me/submissions/95bc4143-aa1b-40c8-8dd1-37cacc315812

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltDegree
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Theorems.Thm_GroundTheory_PAdicHodge_le_tiltIntermediateField_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_exists_tiltSharp_linearIndependent
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_tiltSharp_mem_of_mem_tiltIntermediateField
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
    tiltIntermediateField p (untiltField K C p N) = N := by
  classical
  set T := tiltIntermediateField p (untiltField K C p N)
  have hle := le_tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N

  have hbound : ∀ s : Finset T, LinearIndependent K♭ (fun i : s => (i : T)) →
      s.card ≤ Module.finrank K (untiltField K C p N) := by
    intro s hs
    have hv : LinearIndependent K♭ (fun i : s => ((i : T) : C♭)) :=
      hs.map' T.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    obtain ⟨w, hw, -, -, hli⟩ := exists_tiltSharp_linearIndependent (K := K) (C := C) hv
    have hwT : ∀ i, w i ∈ T := fun i => by
      have hsp : Submodule.span K♭ (Set.range fun i : s => ((i : T) : C♭)) ≤
          Subalgebra.toSubmodule T.toSubalgebra :=
        Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ((j : T)).2)
      exact hsp (hw i)
    let u : s → untiltField K C p N := fun i =>
      ⟨tiltSharp C p (w i), tiltSharp_mem_of_mem_tiltIntermediateField _ (hwT i)⟩
    have hu : LinearIndependent K u :=
      LinearIndependent.of_comp (IntermediateField.val _).toLinearMap hli
    simpa using hu.fintype_card_le_finrank
  have hrank : Module.rank K♭ T ≤ Module.finrank K (untiltField K C p N) := rank_le hbound
  have hfin : FiniteDimensional K♭ T :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  have hfr : Module.finrank K♭ T ≤ Module.finrank K♭ N := by
    rw [← finrank_untiltField (K := K) (C := C) (p := p) N]
    exact Module.finrank_le_of_rank_le hrank
  exact (IntermediateField.eq_of_le_of_finrank_le hle hfr).symm
end GroundTheory.PAdicHodge
