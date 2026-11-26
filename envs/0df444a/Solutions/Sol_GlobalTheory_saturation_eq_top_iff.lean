-- Prove2me | solution 1 for GlobalTheory.saturation_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:29:46.109985+00:00
-- url     : https://prove2.me/submissions/f1f00953-abd5-49ae-a45b-c78f94bbd842

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
theorem _root_.solution {N : Submodule R M} :
    saturation N = ⊤ ↔ Module.IsTorsion R (M ⧸ N) := by
  first
    | (rw [eq_top_iff]
       constructor
       · intro h x
         obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
         obtain ⟨a, ha, hay⟩ := GlobalTheory.mem_saturation_iff'.1 (h (Submodule.mem_top (x := y)))
         refine ⟨⟨a, ha⟩, ?_⟩
         show a • (Submodule.Quotient.mk y : M ⧸ N) = 0
         rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
         exact hay
       · intro h y _
         rw [GlobalTheory.mem_saturation_iff']
         obtain ⟨⟨a, ha⟩, hay⟩ := h (x := Submodule.Quotient.mk y)
         refine ⟨a, ha, ?_⟩
         rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
         exact hay)

