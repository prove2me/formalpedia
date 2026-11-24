-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.fixed_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:52.373373+00:00
-- url     : https://prove2.me/submissions/318eee3c-f77d-445e-87b1-4ce669ae2ddc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.HermInv
theorem _root_.solution [Unram F E] {y : E} (hy : star y = y) : ∃ x : F, algebraMap F E x = y := by
  by_contra hne
  push_neg at hne
  have hli : LinearIndependent F ![(1 : E), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hne (-(s / t))
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination -hst
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [Unram.finrank_eq (F := F) (E := E)])
  obtain ⟨z, hz⟩ := Unram.star_ne (F := F) (E := E)
  apply hz
  have hle : Submodule.span F (Set.range ![(1 : E), y]) ≤ LinearMap.ker (starLin (F := F) (E := E) - LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simp [starLin]
    · simp [starLin, hy]
  have := hle (htop ▸ Submodule.mem_top : z ∈ Submodule.span F (Set.range ![(1 : E), y]))
  simpa [starLin, sub_eq_zero] using this
end GlobalTheory.JR.HermInv
