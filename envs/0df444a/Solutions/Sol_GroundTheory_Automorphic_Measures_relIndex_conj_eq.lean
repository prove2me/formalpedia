-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.relIndex_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:35.008185+00:00
-- url     : https://prove2.me/submissions/411714e8-672a-4cbf-a865-2b9a04bd011c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Theorems.Thm_GroundTheory_Automorphic_Measures_measure_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_Measures_inv_eq_self_GL
import Theorems.Thm_GroundTheory_Automorphic_Measures_inv_doubleCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F)))
    (hKc : IsCompact (K : Set (GL (Fin n) F))) (g : GL (Fin n) F) :
    (K.map (MulAut.conj g).toMonoidHom).relIndex K =
      (K.map (MulAut.conj g⁻¹).toMonoidHom).relIndex K := by
  borelize (GL (Fin n) F)
  let μ : Measure (GL (Fin n) F) := Measure.haar
  have hK0 : μ K ≠ 0 := hKo.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ∞ := hKc.measure_lt_top.ne
  have h1 := measure_doubleCoset μ hKo hKc g
  have h3 : μ (doubleCoset g (K : Set (GL (Fin n) F)) K) =
      μ (doubleCoset g⁻¹ (K : Set (GL (Fin n) F)) K) := by
    conv_lhs => rw [← inv_eq_self_GL F n μ]
    rw [Measure.inv_apply, inv_doubleCoset]
  rw [h3, measure_doubleCoset μ hKo hKc g⁻¹] at h1
  exact_mod_cast ((ENNReal.mul_left_inj hK0 hKT).1 h1).symm
end GroundTheory.Automorphic.Measures
