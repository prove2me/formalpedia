-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.fieldArgs_time_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:12:02.003367+00:00
-- url     : https://prove2.me/submissions/64645b6f-7620-4fc5-9e4f-bc618fed2749

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryCalculus.lean:L81-L96
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.fieldArgs_time_hasDerivAt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryCalculus ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
open BalancedTransport.Geometry

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma fieldArgs_time_hasDerivAt {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    HasDerivAt (fun s => fieldArgs p s x) (Pi.single (Fin.castAdd d 0) 1) t := by
  apply hasDerivAt_pi.mpr
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [fieldArgs, Fin.append_left, Fin.cons_zero, Pi.single_eq_same]
      exact hasDerivAt_id _
    · have hn : Fin.castAdd d i.succ ≠ Fin.castAdd d (0 : Fin 4) := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_succ, Fin.val_zero] at this; omega
      simpa only [fieldArgs, Fin.append_left, Fin.cons_succ, Pi.single_apply, ite_eq_right hn] using hasDerivAt_const t (x i)
  · intro j
    have hn : Fin.natAdd 4 j ≠ Fin.castAdd d (0 : Fin 4) := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero] at this; omega
    simpa only [fieldArgs, Fin.append_right, Pi.single_apply, ite_eq_right hn] using hasDerivAt_const t (p j)

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

end BalancedTransport.Effectivity.ElementaryScalar
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.fieldArgs_time_hasDerivAt := @_root_.OAI.BalancedTransport.Effectivity.fieldArgs_time_hasDerivAt
