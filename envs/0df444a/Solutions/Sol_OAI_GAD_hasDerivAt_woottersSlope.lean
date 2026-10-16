-- Prove2me | solution 1 for OAI.GAD.hasDerivAt_woottersSlope
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:56:49.261978+00:00
-- url     : https://prove2.me/submissions/13f661de-5eb0-49f3-9e69-9d57170eb723

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/OutputConvexity.lean:L102-L116
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.hasDerivAt_woottersSlope. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity

-- ---- from OAI.InformationTheory.AmplitudeDamping.OutputConvexity ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators
open Set Filter Topology

namespace GAD

theorem radius_pos_lt_one {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    0 < radius s ∧ radius s < 1 := by
  have hx : 0 < 1 - 4 * s ^ 2 := by nlinarith [hs.1, hs.2]
  have hx' : 1 - 4 * s ^ 2 < 1 := by nlinarith [hs.1]
  unfold radius
  exact ⟨Real.sqrt_pos.2 hx, (Real.sqrt_lt' (by norm_num)).2 (by simpa using hx')⟩

theorem radius_sq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
    radius s ^ 2 = 1 - 4 * s ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [hs.1, hs.2]

theorem hasDerivAt_radius {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt radius (-4 * s / radius s) s := by
  have hx : 1 - 4 * s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
  have hd := (Real.hasDerivAt_sqrt hx).comp s
    ((hasDerivAt_const s (1 : ℝ)).sub (((hasDerivAt_id s).pow 2).const_mul 4))
  convert! hd using 1
  simp [radius]
  ring

theorem hasDerivAt_logRatio {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    HasDerivAt logRatio (2 / (1 - t ^ 2)) t := by
  have hp : 1 + t ≠ 0 := by linarith
  have hm : 1 - t ≠ 0 := by linarith
  have hd := (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).log hp).sub
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log hm)
  convert! hd using 1
  simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add, zero_sub, neg_div]
  have he : 1 - t ^ 2 = (1 + t) * (1 - t) := by ring
  rw [he]
  field_simp
  ring

theorem hasDerivAt_woottersSlope {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt woottersSlope
      (2 * (logRatio (radius s) - 2 * radius s) / radius s ^ 3) s := by
  have ht := radius_pos_lt_one hs
  have ht0 : radius s ≠ 0 := ne_of_gt ht.1
  have hs0 : s ≠ 0 := ne_of_gt hs.1
  have ht2 : 1 - radius s ^ 2 = 4 * s ^ 2 := by
    nlinarith [radius_sq ⟨hs.1.le, hs.2.le⟩]
  have hd := (((hasDerivAt_id s).const_mul 2).div (hasDerivAt_radius hs) ht0).mul
    ((hasDerivAt_logRatio (by linarith [ht.1]) ht.2).comp s (hasDerivAt_radius hs))
  convert! hd using 1
  simp only [Pi.div_apply, Function.comp_apply, id_eq, mul_one, ht2]
  field_simp
  have he : radius s ^ 2 + 4 * s ^ 2 - 1 = 0 := by linarith
  linear_combination -logRatio (radius s) * he

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.GAD.hasDerivAt_woottersSlope := @_root_.OAI.GAD.hasDerivAt_woottersSlope
