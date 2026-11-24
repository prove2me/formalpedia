-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.RowCompletion.exists_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:48.134159+00:00
-- url     : https://prove2.me/submissions/1eaf504e-6eb4-40c5-bfe1-ec66174218a8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFinite
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_RowCompletion_exists_bezout

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
theorem _root_.solution {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {p q : F}
    (h : A = FractionalIdeal.spanSingleton _ p + FractionalIdeal.spanSingleton _ q) :
    ∃ g : SL(2, F), Adapted A g ∧ g 1 0 = p ∧ g 1 1 = q := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_bezout hA h
  have hp : p ∈ A := by
    rw [h, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_add, Submodule.add_eq_sup]
    exact Submodule.mem_sup_left (FractionalIdeal.mem_coe.2
      (FractionalIdeal.mem_spanSingleton_self _ _))
  have hq : q ∈ A := by
    rw [h, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_add, Submodule.add_eq_sup]
    exact Submodule.mem_sup_right (FractionalIdeal.mem_coe.2
      (FractionalIdeal.mem_spanSingleton_self _ _))
  refine ⟨⟨!![a, b; p, q], by simpa [Matrix.det_fin_two] using hab⟩, ?_, by simp, by simp⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa
end GlobalTheory.CompanionTheory.SW.Core.RowCompletion
