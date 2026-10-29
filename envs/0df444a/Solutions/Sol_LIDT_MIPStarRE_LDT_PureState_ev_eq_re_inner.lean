-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.PureState.ev_eq_re_inner
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:45:04.693678+00:00
-- url     : https://prove2.me/submissions/38fe8e3e-6e31-4788-ad05-ce2ecb689136

-- Generated proof for MIPStarRE.LDT.PureState.ev_eq_re_inner.
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



















theorem normalizedTrace_density_mul {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) (X : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.normalizedTrace ((ψ : QuantumState ι).density * X) =
      star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector) := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    MIPStarRE.Quantum.normalizedTrace ((ψ : QuantumState ι).density * X)
      = MIPStarRE.Quantum.normalizedTrace (X * (ψ : QuantumState ι).density) := by
          rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
    _ = MIPStarRE.Quantum.normalizedTrace (X * ψ.density) := by rfl
    _ = MIPStarRE.Quantum.normalizedTrace
          ((Fintype.card ι : ℂ) • (X * Matrix.vecMulVec ψ.vector (star ψ.vector))) := by
          simp [density, pureDensity]
    _ = (Fintype.card ι : ℂ) *
          MIPStarRE.Quantum.normalizedTrace (X * Matrix.vecMulVec ψ.vector (star ψ.vector)) := by
          rw [MIPStarRE.Quantum.normalizedTrace_smul]
    _ = (Fintype.card ι : ℂ) *
          (((X * Matrix.vecMulVec ψ.vector (star ψ.vector)).trace) /
            (Fintype.card ι : ℂ)) := by
          simp [MIPStarRE.Quantum.normalizedTrace]
    _ = (Fintype.card ι : ℂ) *
          (((Matrix.vecMulVec (X *ᵥ ψ.vector) (star ψ.vector)).trace) /
            (Fintype.card ι : ℂ)) := by
          rw [Matrix.mul_vecMulVec]
    _ = (Fintype.card ι : ℂ) *
          (((X *ᵥ ψ.vector) ⬝ᵥ star ψ.vector) / (Fintype.card ι : ℂ)) := by
          rw [Matrix.trace_vecMulVec]
    _ = (X *ᵥ ψ.vector) ⬝ᵥ star ψ.vector := by
          field_simp [hcard]
    _ = star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector) := by
          rw [dotProduct_comm]



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

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : _root_.LIDT.MIPStarRE.LDT.PureState ι) (X : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.ev (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) X =
      Complex.re (star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector)) := by
  unfold _root_.LIDT.MIPStarRE.LDT.ev
  rw [ψ.normalizedTrace_density_mul]
