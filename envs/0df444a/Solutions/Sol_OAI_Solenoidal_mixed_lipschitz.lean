-- Prove2me | solution 1 for OAI.Solenoidal.mixed_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:49:33.679981+00:00
-- url     : https://prove2.me/submissions/6886a834-bb4f-41cf-8375-5058a4b02d6b

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/CircuitPrograms.lean:L318-L343
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.mixed_lipschitz. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Circuits
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_CircuitPrograms
import Theorems.Thm_OAI_Solenoidal_norm_flatten

-- ---- from OAI.MathematicalPhysics.SheetFlows.Differential ----
namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_contDiff {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (directional g v) :=
  (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

end DirectionalCalculus

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.ScheduledForce ----
namespace OAI

/-! SheetFlows scheduled force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem mixedDerivative_contDiff {u : Field} (hu : Smooth u) (α : List (Fin 4)) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedDerivative u α) := by
  induction α with
  | nil => exact hu
  | cons j α ih => exact directional_contDiff ih (spacetimeBasis j)

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.CircuitPrograms ----
namespace OAI

/-! SheetFlows circuit programs. -/

section
open Encodable Denumerable
namespace Solenoidal.Computing
open Nat.Partrec

end Solenoidal.Computing
end

open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal

namespace Circuit

end Circuit

namespace Computing

end Computing

theorem spacetime_expansion (z : SpaceTime) :
    z = ∑ j : Fin 4, flatten z j • spacetimeBasis j := by
  apply Prod.ext
  · simp [flatten,spacetimeBasis,Fin.sum_univ_succ]
  · ext k
    fin_cases k <;> simp [flatten,spacetimeBasis,basis,Fin.sum_univ_succ]

theorem jetLipschitz_nonneg {B : List (Fin 4) → ℚ} (h : ∀ a, 0 ≤ B a)
    (a : List (Fin 4)) : 0 ≤ jetLipschitz B a := Finset.sum_nonneg (fun _ _ => h _)

theorem mixed_lipschitz {u : Field} (hu : Smooth u) {B : List (Fin 4) → ℚ}
    (hB : ∀ a, 0 ≤ B a) (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ))
    (a : List (Fin 4)) (z w : SpaceTime) :
    ‖mixedDerivative u a z - mixedDerivative u a w‖ ≤ (jetLipschitz B a:ℝ)*‖z-w‖ := by
  have hd (x : SpaceTime) : ‖fderiv ℝ (mixedDerivative u a) x‖ ≤ (jetLipschitz B a:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by exact_mod_cast jetLipschitz_nonneg hB a)
    intro v
    have he : fderiv ℝ (mixedDerivative u a) x v =
        ∑ j : Fin 4, flatten v j • mixedDerivative u (j::a) x := by
      conv_lhs => rw [spacetime_expansion v]
      simp only [map_sum,map_smul,mixedDerivative]
    rw [he]
    apply (norm_sum_le _ _).trans
    calc
      ∑ j : Fin 4, ‖flatten v j • mixedDerivative u (j::a) x‖ ≤
          ∑ j : Fin 4, (B (j::a):ℝ) * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul,mul_comm]
        exact mul_le_mul (hb (j::a) x)
          ((norm_le_pi_norm (flatten v) j).trans_eq (norm_flatten v))
          (norm_nonneg _) (by exact_mod_cast hB (j::a))
      _ = _ := by simp [jetLipschitz,Finset.sum_mul]
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (mixedDerivative_contDiff hu a).differentiable (by simp) x)
    (fun x _ => hd x) convex_univ (Set.mem_univ w) (Set.mem_univ z)

namespace Computing

end Computing
end Solenoidal

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set Filter Encodable
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.mixed_lipschitz := @_root_.OAI.Solenoidal.mixed_lipschitz
