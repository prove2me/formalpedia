-- Prove2me | solution 1 for OAI.BeamLadder.lowerR_single
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:38:12.554668+00:00
-- url     : https://prove2.me/submissions/49d6fc04-67ac-4374-ad4a-73d13326710c

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean:L121-L140
-- (upload_full_project.md Phase 4): solution for node OAI.BeamLadder.lowerR_single. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace

-- ---- from OAI.InformationTheory.PhotonNumber.BeamTrace ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
theorem lowerR_single (j : Fin n) (a b : NumberIndex n) :
    lowerR j (lp.single 2 (a,b) 1)=
      ((Real.sqrt (b j)/W (a,b):ℝ):ℂ) • lp.single 2 (a,down j b) 1 := by
  by_cases hb : 0<b j
  · have he : (a,b)=upR j (a,down j b) := by simp [upR, up_down j b hb]
    conv_lhs => arg 2; arg 2; rw [he]
    rw [lowerR, WeightedShift.pullCLM_single]
    have hw : W (a,down j b)+1=W (a,b) := by simpa only [upR, up_down j b hb] using W_upR j (a,down j b) |>.symm
    have hc : ((down j b) j:ℝ)+1=b j := by
      rw [down, Function.update_self]
      exact_mod_cast (Nat.sub_add_cancel hb)
    simp only [hc, hw, mul_one]
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E:=fun _ : NumberIndex n × NumberIndex n => ℂ) 2 (a,down j b) ((Real.sqrt (b j)/W (a,b):ℝ):ℂ) (1:ℂ)
  · have hz : b j=0 := Nat.eq_zero_of_not_pos hb
    have hout (ke : NumberIndex n × NumberIndex n) : upR j ke ≠ (a,b) := by
      intro he
      have hh := congrArg (fun p : NumberIndex n × NumberIndex n => p.2 j) he
      simp [upR, hz] at hh
    rw [lowerR, WeightedShift.pullCLM_single_outside _ _ _ _ _ _ _ hout]
    simp [hz]

end BeamLadder

namespace EntropyPhotonNumber
end EntropyPhotonNumber

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end BeamLadder

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace E] [CompleteSpace H]

end

variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal

namespace EntropyPhotonNumber
variable {n : ℕ}
end EntropyPhotonNumber

namespace TensorLp
variable {A B I : Type*}
end TensorLp

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace TensorLp
variable {A B I : Type*}

end TensorLp

namespace TraceEnsemble
open TensorLp
variable {A B I J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open TensorLp
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.BeamLadder
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open EntropyPhotonNumber QuantumTrace Annihilation


theorem solution : type_of% @_root_.OAI.BeamLadder.lowerR_single := @_root_.OAI.BeamLadder.lowerR_single
