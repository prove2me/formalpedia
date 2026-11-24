-- Prove2me | solution 1 for GlobalTheory.JR.Step.UNormal.exists_algebraMap_of_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:11:17.853799+00:00
-- url     : https://prove2.me/submissions/577a24e4-2b0f-4077-888e-a0c4805a02cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.UNormal
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]
namespace GlobalTheory.JR.Step.UNormal
theorem _root_.solution (y : E) (hy : star y = y) : ∃ x : F, algebraMap F E x = y := by
  have hU : Unram F E := inferInstance
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  let S : Submodule F E :=
    { carrier := {z | star z = z}
      add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [star_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq] at *
        rw [Algebra.smul_def, star_mul, hz, hU.star_fix, mul_comm] }
  have h1 : (Submodule.span F {(1 : E)}) ≤ S := by
    rw [Submodule.span_le]; intro z hz; simp only [Set.mem_singleton_iff] at hz; subst hz
    show star (1 : E) = 1; exact star_one E
  have hne : S ≠ ⊤ := by
    obtain ⟨z, hz⟩ := hU.star_ne
    intro h; apply hz; have : z ∈ S := h ▸ Submodule.mem_top; exact this
  have hlt : Module.finrank F S < 2 := by
    rw [← hU.finrank_eq]; exact Submodule.finrank_lt hne
  have hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
  have heq : Submodule.span F {(1 : E)} = S :=
    Submodule.eq_of_le_of_finrank_le h1 (by omega)
  have hyS : y ∈ S := hy
  rw [← heq, Submodule.mem_span_singleton] at hyS
  obtain ⟨c, hc⟩ := hyS
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
end GlobalTheory.JR.Step.UNormal
