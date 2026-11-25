-- Prove2me | solution 1 for GlobalTheory.SW.Model.not_admissible_half_lattice_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:10:14.813235+00:00
-- url     : https://prove2.me/submissions/760450f2-0349-4eee-8239-8a5f88027b42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Theorems.Thm_GlobalTheory_SW_Model_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Model_stdL_mem_Vset
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Base_stdL_mem_Vset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution {n N M : ℕ} : ¬ admitted M 1 (divFam E (n + 1) (N + 1) 2) := by
  classical
  intro h
  have h1 := h.supp _ (stdL_mem_Vset (n + 1) M) (Matrix.of fun _ _ => (2⁻¹ : E)) (by
    have : ColsIn (stdL E (n + 1)) (((2 : ℕ) : E) •
        (Matrix.of fun _ _ => (2⁻¹ : E) : Matrix (Fin (n + 1)) (Fin (N + 1)) E)) := fun a =>
      (mem_stdL _).2 fun k => by simpa using isIntegral_one
    simp only [divFam, if_pos this]; exact one_ne_zero)
  have h2 : IsIntegral ℤ (2⁻¹ : E) := by simpa using (mem_stdL _).1 (h1 0) 0
  have h3 : IsIntegral ℤ (2⁻¹ : ℚ) := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap ℚ E).injective]; simpa using h2
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have : (2 : ℚ) * k = 1 := by
    have : (k : ℚ) = 2⁻¹ := by simpa using hk
    rw [this]; norm_num
  have : (2 : ℤ) * k = 1 := by exact_mod_cast this
  omega
end GlobalTheory.SW.Model
