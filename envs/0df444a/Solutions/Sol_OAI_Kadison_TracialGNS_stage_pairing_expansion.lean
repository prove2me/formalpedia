-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.stage_pairing_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:50:13.662212+00:00
-- url     : https://prove2.me/submissions/25238ffd-10d7-4248-bb95-34221d1e214b

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_SchurWeyl_centered_expansion_contractions

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {k l : ℕ} (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

lemma stage_pairing_expansion_oai (d : Equiv.Perm (Option (TailSlots k l)) → ℂ)
    (hd : ∀ σ, 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (TailSlots k l)) + 1 → d σ = 0)
    (hexp : ∀ v : Option (TailSlots k l) → Matrix I I ℂ,
      stageCoefficient τ Y φ v = ∑ σ, d σ * SchurWeyl.cycleTrace σ v)
    (v : TailSlots k l → Matrix I I ℂ) (hv : ∀ j, Matrix.trace (v j) = 0) :
    stageCoefficient τ Y φ (fun o => o.elim (1 : Matrix I I ℂ) v) =
      ∑ σ : Pairing (TailSlots k l), d (SchurWeyl.endpointPairingPerm σ) *
        Pairing.contraction σ (fun X Z => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Z)) v := by
  have hh := SchurWeyl.centered_expansion_contractions d hd
    (fun o : Option (TailSlots k l) => o.elim (1 : Matrix I I ℂ) v) (fun j => hv j)
  have hm : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Option.elim_none, Option.elim_some, Matrix.trace_one,
    inv_mul_cancel₀ hm, one_mul] at hh
  exact (hexp (fun o : Option (TailSlots k l) => o.elim (1 : Matrix I I ℂ) v)).trans hh

end Kadison.TracialGNS
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TracialGNS.stage_pairing_expansion_oai.{u_1} := @OAI.Kadison.TracialGNS.stage_pairing_expansion_oai.{u_1}
