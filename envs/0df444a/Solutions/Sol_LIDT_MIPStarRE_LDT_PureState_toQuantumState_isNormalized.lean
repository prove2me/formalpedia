-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.PureState.toQuantumState_isNormalized
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:45:04.983741+00:00
-- url     : https://prove2.me/submissions/f13de3c9-4acf-4c3c-aa07-c01edafa97c7

-- Generated proof for MIPStarRE.LDT.PureState.toQuantumState_isNormalized.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Basic/QuantumState.lean. -/
/-!
# Quantum states and tensor placement for the low individual degree test

Core quantum-state definitions together with tensor-placement operators.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT













namespace PureState















theorem normalizedTrace_density {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) :
    MIPStarRE.Quantum.normalizedTrace ψ.density = 1 := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold density pureDensity MIPStarRE.Quantum.normalizedTrace
  rw [Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_comm, ψ.unit]
  change ((Fintype.card ι : ℂ) * 1) / (Fintype.card ι : ℂ) = 1
  rw [mul_one, div_self hcard]







end PureState























namespace QuantumState







end QuantumState



























































end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Quantum states and tensor placement for the low individual degree test

Core quantum-state definitions together with tensor-placement operators.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT













open LIDT.MIPStarRE.LDT.PureState

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : _root_.LIDT.MIPStarRE.LDT.PureState ι) :
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι).IsNormalized := by
  simpa [_root_.LIDT.MIPStarRE.LDT.QuantumState.IsNormalized] using ψ.normalizedTrace_density
