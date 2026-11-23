-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.ball_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:21.054985+00:00
-- url     : https://prove2.me/submissions/52e04680-0761-4e87-b716-dfa555eb3fc4

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Theorems.Thm_Formalism_L2_Host_unif_spec
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.OrderUnits
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z : P.adicCompletion E) :
    {x : P.adicCompletion E | Valued.v (x - z) ≤ WithZero.exp (-(n : ℤ))} ∈ 𝓝 z := by
  set t : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) ^ n with ht
  have hv : Valued.v (t : P.adicCompletion E) = WithZero.exp (-(n : ℤ)) := by
    have h2 : Valued.v ((Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) : (P.adicCompletion E)ˣ) : P.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec P
    rw [ht, Units.val_pow_eq_pow_val, map_pow, h2, ← WithZero.exp_nsmul]
    simp
  have hc : Continuous fun x : P.adicCompletion E => (x - z) / (t : P.adicCompletion E) := by fun_prop
  have ho := (Valued.isOpen_valuationSubring (P.adicCompletion E)).preimage hc
  refine mem_of_superset (ho.mem_nhds ?_) ?_
  · show (z - z) / (t : P.adicCompletion E) ∈ Valued.v.valuationSubring
    rw [sub_self, zero_div]; exact zero_mem _
  · intro x hx
    have hx' : Valued.v ((x - z) / (t : P.adicCompletion E)) ≤ 1 := hx
    rw [map_div₀, hv, div_le_one₀ (WithZero.exp_pos)] at hx'
    exact hx'
end GlobalTheory.CMVal.OrderUnits
