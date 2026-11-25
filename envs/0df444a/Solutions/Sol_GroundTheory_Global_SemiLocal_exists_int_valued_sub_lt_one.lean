-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.exists_int_valued_sub_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:58.637331+00:00
-- url     : https://prove2.me/submissions/d9b628a8-1b63-4525-8b16-e02635c911b8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (d : u.adicCompletion F) (hd : Valued.v d ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (d - algebraMap (𝓞 F) (u.adicCompletion F) r) < 1 := by
  obtain ⟨x, hx⟩ : ∃ x : F, Valued.v (d - algebraMap F (u.adicCompletion F) x) < 1 := by
    have ho : IsOpen {y : u.adicCompletion F | Valued.v (d - y) < 1} := by
      have : {y : u.adicCompletion F | Valued.v (d - y) < 1} = Metric.ball d 1 := by
        ext y
        rw [Set.mem_ofPred_eq, Metric.mem_ball, dist_comm, dist_eq_norm,
          Valued.toNormedField.norm_lt_one_iff]
      rw [this]
      exact Metric.isOpen_ball
    exact (HeightOneSpectrum.denseRange_algebraMap F u).exists_mem_open ho ⟨d, by simp⟩
  have hx1 : u.valuation F x ≤ 1 := by
    rw [← valued_algebraMap_field]
    calc Valued.v (algebraMap F (u.adicCompletion F) x)
        = Valued.v (d - (d - algebraMap F (u.adicCompletion F) x)) := by rw [sub_sub_cancel]
      _ ≤ max (Valued.v d) (Valued.v (d - algebraMap F (u.adicCompletion F) x)) :=
          Valuation.map_sub _ _ _
      _ ≤ 1 := max_le hd hx.le
  obtain ⟨r, hr⟩ := u.exists_valuation_sub_lt_of_integer hx1 1
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) r -
      algebraMap F (u.adicCompletion F) x) < 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (u.adicCompletion F), ← map_sub,
      valued_algebraMap_field]
    simpa using hr
  calc Valued.v (d - algebraMap (𝓞 F) (u.adicCompletion F) r)
      = Valued.v ((d - algebraMap F (u.adicCompletion F) x) -
          (algebraMap (𝓞 F) (u.adicCompletion F) r - algebraMap F (u.adicCompletion F) x)) := by
        congr 1; ring
    _ ≤ max _ _ := Valuation.map_sub _ _ _
    _ < 1 := max_lt hx hr'
end GroundTheory.Global.SemiLocal
