-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.cell_euler_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:40:11.551388+00:00
-- url     : https://prove2.me/submissions/495e1a62-8405-45c5-9025-c7d4f1f10049

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/EulerRank.lean:L9-L31
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.cell_euler_of_exact. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport

-- ---- from OAI.Combinatorics.HoneycombCorridor.EulerRank ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem cell_euler_of_exact {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [Nonempty V]
    (A : Matrix V E ℚ) (B : (F → ℚ) →ₗ[ℚ] (E → ℚ))
    (hB : Function.Injective B) (hex : B.range = A.mulVecLin.ker)
    (hconst : A.transpose.mulVecLin.ker = Submodule.span ℚ {(1 : V → ℚ)}) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F = 1 := by
  have hF : Module.finrank ℚ A.mulVecLin.ker = Fintype.card F := by
    rw [← hex,LinearMap.finrank_range_of_inj hB,Module.finrank_fintype_fun_eq_card]
  have hV : Module.finrank ℚ A.transpose.mulVecLin.ker = 1 := by
    rw [hconst]
    exact finrank_span_singleton (by
      obtain ⟨v⟩ := ‹Nonempty V›
      intro h
      have := congrFun h v
      norm_num at this)
  have hrE := A.mulVecLin.finrank_range_add_finrank_ker
  have hrV := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr := A.rank_transpose
  change Module.finrank ℚ A.transpose.mulVecLin.range =
    Module.finrank ℚ A.mulVecLin.range at hr
  rw [hF,Module.finrank_fintype_fun_eq_card] at hrE
  rw [hV,Module.finrank_fintype_fun_eq_card] at hrV
  omega

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.cell_euler_of_exact := @_root_.OAI.PolynomialVacuumBridge.Corridor.cell_euler_of_exact
