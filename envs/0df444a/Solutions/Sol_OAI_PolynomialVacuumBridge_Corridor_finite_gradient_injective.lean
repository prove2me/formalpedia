-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.finite_gradient_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:32:19.017032+00:00
-- url     : https://prove2.me/submissions/f21dbb88-6a0f-4310-89f6-9f39b5c4a46e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Currents.lean:L124-L145
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.finite_gradient_injective. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents

-- ---- from OAI.Combinatorics.HoneycombCorridor.Currents ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem finite_gradient_injective (r s : FaceIndex →₀ ℚ)
    (h : faceGradient r = faceGradient s) : r = s := by
  have hh (i j : ℤ) : r (i+1,j) - s (i+1,j) = r (i,j) - s (i,j) := by
    have he := congrFun h ((i+1,j),0)
    simp [faceGradient,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] at he
    linarith
  ext a
  rcases a with ⟨i,j⟩
  let k : ℤ := -(QFlow.faceRadius r : ℤ) - QFlow.faceRadius s - 1
  have hr : r (k,j) = 0 := by
    by_contra hz
    have hb := (QFlow.mem_support_in_box r (k,j) (Finsupp.mem_support_iff.mpr hz)).1
    dsimp [k] at hb
    omega
  have hs : s (k,j) = 0 := by
    by_contra hz
    have hb := (QFlow.mem_support_in_box s (k,j) (Finsupp.mem_support_iff.mpr hz)).1
    dsimp [k] at hb
    omega
  have he := QFlow.int_function_constant (f := fun i => r (i,j) - s (i,j)) (fun i => hh i j) i k
  rw [hr,hs] at he
  linarith

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.finite_gradient_injective := @_root_.OAI.PolynomialVacuumBridge.Corridor.finite_gradient_injective
