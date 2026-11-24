-- Prove2me | solution 1 for GlobalTheory.WeilM.ResEtaPow.map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:47.825791+00:00
-- url     : https://prove2.me/submissions/c477a810-04ad-487e-91d5-8d1833383ff4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_algebraMap_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
variable {c}
namespace GlobalTheory.WeilM
namespace ResEtaPow
theorem _root_.solution {ξ : E} (h : IsQuad c ξ) {K : Subgroup Rˣ} {χ : Eˣ →* Circle} {n : ℕ} (hχ : ResEtaPow K χ n)
    (z : Eˣ) : χ (Units.map (c : E →* E) z) = (χ z)⁻¹ := by
  have h1 := hχ (Units.map (Algebra.norm R : E →* R) z)
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, rfl⟩)), Circle.coe_eq_one,
    show Units.map (algebraMap R E : R →* E) (Units.map (Algebra.norm R : E →* R) z) = z * Units.map (c : E →* E) z from
      Units.ext (h.algebraMap_norm z), map_mul] at h1
  exact eq_inv_of_mul_eq_one_right h1
end ResEtaPow
end GlobalTheory.WeilM
