-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_eq_of_finrank_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:31.656912+00:00
-- url     : https://prove2.me/submissions/88dc4d75-03eb-47d8-affc-0eb39a8342ee

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_finiteDimensional_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_natDegree_minpoly_eq_of_finrank_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {B₀ Ω : Type*} [Field B₀] [Field Ω] [Algebra B₀ Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k A B : IntermediateField B₀ Ω} (hA : k ≤ A)
    (hB : k ≤ B) [FiniteDimensional B₀ A] [FiniteDimensional B₀ B]
    (h : finrank B₀ ↥(A ⊔ B) * finrank B₀ k = finrank B₀ A * finrank B₀ B) {z : Ω} (hz : z ∈ A) :
    normTrace B z = normTrace k z := by
  haveI := finiteDimensional_of_le hA
  have hz0 : IsIntegral B₀ z := by
    have := IsIntegral.of_finite B₀ (⟨z, hz⟩ : A)
    exact this.map (IsScalarTower.toAlgHom B₀ A Ω)
  have hzk : IsIntegral k z := hz0.tower_top
  have hzB : IsIntegral B z := hz0.tower_top
  letI : Algebra k B := (IntermediateField.inclusion hB).toAlgebra
  haveI : IsScalarTower k B Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hdvd := minpoly.dvd_map_of_isScalarTower k B z
  have heq : (minpoly k z).map (algebraMap k B) = minpoly B z :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzB) ((minpoly.monic hzk).map _) hdvd
      (by rw [natDegree_map, natDegree_minpoly_eq_of_finrank_sup hA hB h hz])
  rw [normTrace, normTraceF, ← heq, nextCoeff_map (algebraMap k B).injective, natDegree_map,
    normTrace, normTraceF]
  rw [← map_natCast (algebraMap k B), ← map_neg, ← map_div₀, ← IsScalarTower.algebraMap_apply]
end GroundTheory.PAdicHodge
