-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.unit_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:49.615118+00:00
-- url     : https://prove2.me/submissions/1a353f54-21d5-4387-8bc4-8be8d35e9290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution {A O : Type} [CommRing A] [CommRing O] (φ : A →+* O) (hφ : φ.IsIntegral) (j : A)
    (hj : ∀ a, IsUnit (1 + j * a)) (z : O) : IsUnit (1 + φ j * z) := by
  by_contra h
  obtain ⟨M, hM, hx⟩ := exists_max_ideal_of_mem_nonunits h
  have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hφ M
  have hjm : j ∈ M.comap φ := by
    have : j ∈ Ideal.jacobson (⊥ : Ideal A) := by
      rw [Ideal.mem_jacobson_bot]
      intro y
      rw [add_comm]; exact hj y
    exact Ideal.mem_sInf.1 this ⟨bot_le, hm⟩
  apply hM.ne_top
  rw [Ideal.eq_top_iff_one]
  have := M.sub_mem hx (M.mul_mem_right z (Ideal.mem_comap.1 hjm))
  simpa using this
end GlobalTheory.AdLat.RootNear
