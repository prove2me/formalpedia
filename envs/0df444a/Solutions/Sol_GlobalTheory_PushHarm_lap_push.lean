-- Prove2me | solution 1 for GlobalTheory.PushHarm.lap_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:09.755802+00:00
-- url     : https://prove2.me/submissions/4801352b-96f7-4476-85dc-69b4f48384b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PushMemHarmK
import Theorems.Thm_GlobalTheory_PushHarm_pderiv_push
import Theorems.Thm_GlobalTheory_PushHarm_lap_one_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PushHarm
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n : ℕ}
namespace GlobalTheory.PushHarm
theorem _root_.solution (γ : Matrix (Fin n) (Fin n) E) (hγ : IsUnitary γ) (τ : E →+* ℂ) (a : Fin (Dw.mult τ))
    (a' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))) (P : MvPolynomial (LtN Dw n) c.F) :
    lap Dw.mult n c.F 1 τ (ComplexEmbedding.conjugate τ) a a' (push c γ P) =
      push c γ (lap Dw.mult n c.F 1 τ (ComplexEmbedding.conjugate τ) a a' P) := by
  have hc : ∀ x : E, embF c (ComplexEmbedding.conjugate τ) x = embF c τ (IsCMField.complexConj E x) :=
    fun x => Subtype.ext (IsCMField.complexEmbedding_complexConj E τ x).symm
  have hu : ∀ j' j : Fin n, ∑ b, embF c (ComplexEmbedding.conjugate τ) (γ b j') * embF c τ (γ b j) =
      if j' = j then 1 else 0 := by
    intro j' j
    have h := congrArg (embF c τ) (congrFun (congrFun hγ j') j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
      Matrix.one_apply, apply_ite (embF c τ), map_one, map_zero] at h
    simpa only [hc] using h
  rw [lap_one_apply, lap_one_apply, map_sum]
  simp only [pderiv_push, map_sum, Derivation.map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hu, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
end GlobalTheory.PushHarm
