-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_strictInterlaces_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/3aa553d2-f1a5-49f7-adc8-ed306f7626db

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_tendsto_flooredCoordinates_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_signature_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) :
    ∀ᶠ n : ℕ in atTop, ∀ v : Vertex r m,
      HigherRepresentationGraph.StrictInterlaces
        (signature a n v) (flooredCoordinates b n) := by
  apply eventually_all.2
  intro v
  apply eventually_all.2
  intro i
  let V : ℕ → Vertex r m := fun _ => v
  have hab :=
    ((tendsto_signature_ratio a V i.castSucc
      (h.ambient_nonneg i.castSucc)).sub
      (tendsto_flooredCoordinates_ratio b i
        (h.stabilizer_pos i).le)).eventually
          (Ioi_mem_nhds (sub_pos.mpr (h.2 i).1))
  have hba :=
    ((tendsto_flooredCoordinates_ratio b i
      (h.stabilizer_pos i).le).sub
      (tendsto_signature_ratio a V i.succ
        (h.ambient_nonneg i.succ))).eventually
          (Ioi_mem_nhds (sub_pos.mpr (h.2 i).2))
  filter_upwards [hab, hba, eventually_gt_atTop (0 : ℕ)] with n hn hn' hnpos
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  constructor
  · exact_mod_cast
      ((div_lt_div_iff_of_pos_right hnreal).mp
        (show (flooredCoordinates b n i : ℝ) / n <
          (signature a n v i.castSucc : ℝ) / n by
            change 0 < _ at hn
            dsimp [V] at hn
            linarith))
  · exact_mod_cast
      ((div_lt_div_iff_of_pos_right hnreal).mp
        (show (signature a n v i.succ : ℝ) / n <
          (flooredCoordinates b n i : ℝ) / n by
            change 0 < _ at hn'
            dsimp [V] at hn'
            linarith))
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
