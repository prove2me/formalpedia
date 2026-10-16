-- Prove2me | solution 1 for OAI.CrossEnsemble.operator_comp_left
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:28:21.87511+00:00
-- url     : https://prove2.me/submissions/6b118f2c-1f97-4dbb-a2f5-717e4aaa70ca

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/Fock/Operators.lean:L487-L501
-- (upload_full_project.md Phase 4): solution for node OAI.CrossEnsemble.operator_comp_left. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators

-- ---- from OAI.MathematicalPhysics.Fock.Operators ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate

namespace WeightedShift
variable {I J : Type*}
variable [DecidableEq I] [DecidableEq J]

end WeightedShift

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace CrossEnsemble
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem operator_comp_left {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Z ∘L operator u v=operator (fun i => Z (u i)) v := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  have hh := ((hasSum_operator hu hv).mapL (ContinuousLinearMap.apply ℂ E y)).mapL Z
  have ht := hh.mapL (innerSL ℂ x)
  have ht' : HasSum (fun i => inner ℂ x (Z (u i))*inner ℂ (v i) y)
      (inner ℂ x (Z (operator u v y))) := by
    convert! ht using 1
    ext i
    simp [InnerProductSpace.rankOne_apply, mul_comm]
  exact ht'.unique (entry_hasSum (applied_summable hu Z) hv x y)

end CrossEnsemble

namespace CrossEnsemble
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

end

end

end OAI

-- ---- platform node ----
open OAI OAI.CrossEnsemble
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate


theorem solution : type_of% @_root_.OAI.CrossEnsemble.operator_comp_left := @_root_.OAI.CrossEnsemble.operator_comp_left
