-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.RowCompletion.integral_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:49.387172+00:00
-- url     : https://prove2.me/submissions/f0155d7b-ef33-477b-adf6-e44a31f03208

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFinite
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_RowCompletion_integral_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.RowCompletion
open nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.Core.RowCompletion
theorem _root_.solution {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {r g : SL(2, F)}
    (hr : Adapted A r) (hg : Adapted A g) (i j : Fin 2) :
    ∃ z : 𝓞 F, (z : F) = (r⁻¹ * g) i j := by
  obtain ⟨r0, r1, r2, r3⟩ := hr
  obtain ⟨g0, g1, g2, g3⟩ := hg
  obtain ⟨z1, e1⟩ := integral_of_mem hA r3 g0
  obtain ⟨z2, e2⟩ := integral_of_mem hA r3 g1
  obtain ⟨z3, e3⟩ := integral_of_mem hA r2 g0
  obtain ⟨z4, e4⟩ := integral_of_mem hA r2 g1
  obtain ⟨z5, e5⟩ := integral_of_mem hA g2 r1
  obtain ⟨z6, e6⟩ := integral_of_mem hA g3 r1
  obtain ⟨z7, e7⟩ := integral_of_mem hA g2 r0
  obtain ⟨z8, e8⟩ := integral_of_mem hA g3 r0
  have hinv : ((r⁻¹ * g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![r 1 1, -r 0 1; -r 1 0, r 0 0] * (g : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rfl
  rw [hinv]
  fin_cases i <;> fin_cases j
  · refine ⟨z1 - z5, ?_⟩
    simp only [map_sub, RingOfIntegers.map_mk, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast [e1, e5]
    simp
    ring
  · refine ⟨z2 - z6, ?_⟩
    push_cast [e2, e6]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · refine ⟨z7 - z3, ?_⟩
    push_cast [e7, e3]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · refine ⟨z8 - z4, ?_⟩
    push_cast [e8, e4]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
end GlobalTheory.CompanionTheory.SW.Core.RowCompletion
