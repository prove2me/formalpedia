-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.hasDerivAt_pairEntropyGap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:33:36.591082+00:00
-- url     : https://prove2.me/submissions/d64f1206-3c33-4200-94f9-a3f4852c0252

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PairEntropy.lean:L224-L239
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.hasDerivAt_pairEntropyGap. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
  ring

theorem hasDerivAt_psi {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt psi (Real.artanh v) v := by
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hm : 1 - v ≠ 0 := by linarith [hv.2]
  have h1 := ((Real.hasDerivAt_mul_log hp).comp v
    ((hasDerivAt_id v).const_add 1)).div_const 2
  have h2 := ((Real.hasDerivAt_mul_log hm).comp v
    ((hasDerivAt_id v).const_sub 1)).div_const 2
  convert! h1.add h2 using 1
  · ext u
    dsimp [psi]
    ring
  · rw [artanh_eq_log_sub hv]
    ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.PairEntropy ----
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem pair_add_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a + b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_add_le a b) h)

theorem pair_sub_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a - b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_sub a b) h)

theorem pairEntropyGap_eq_psi (a b : ℝ) :
    pairEntropyGap a b = (psi (a + b) + psi (a - b)) / 2 - psi a := by
  unfold pairEntropyGap entropy
  ring

theorem hasDerivAt_pairEntropyGap (a b : ℝ) (h : |a| + |b| < 1) :
    HasDerivAt (fun t => pairEntropyGap a t)
      ((Real.artanh (a + b) - Real.artanh (a - b)) / 2) b := by
  have hp : HasDerivAt (fun t => psi (a + t)) (Real.artanh (a + b)) b := by
    convert! (hasDerivAt_psi (pair_add_mem_Ioo a b h)).comp b
      ((hasDerivAt_id b).const_add a) using 1
    simp
  have hm : HasDerivAt (fun t => psi (a - t)) (-Real.artanh (a - b)) b := by
    convert! (hasDerivAt_psi (pair_sub_mem_Ioo a b h)).comp b
      ((hasDerivAt_const b a).sub (hasDerivAt_id b)) using 1
    simp
  have hf : (fun t => pairEntropyGap a t) =
      (fun t => (psi (a + t) + psi (a - t)) / 2 - psi a) :=
    funext (pairEntropyGap_eq_psi a)
  rw [hf]
  convert! ((hp.add hm).div_const 2).sub_const (psi a) using 1

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.hasDerivAt_pairEntropyGap := @_root_.OAI.LeanBlast.CourtadeKumar.hasDerivAt_pairEntropyGap
