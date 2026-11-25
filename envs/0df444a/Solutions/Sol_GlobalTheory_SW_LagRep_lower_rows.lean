-- Prove2me | solution 1 for GlobalTheory.SW.LagRep.lower_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:40.163593+00:00
-- url     : https://prove2.me/submissions/43a4ccf6-3d8b-4c82-a213-9bac09fbdc20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
import Theorems.Thm_P2M_GlobalTheory_SW_LagRep_ccT_ccT__22e929649a54
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LagRep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.LagRep
theorem _root_.solution {N : ℕ} (γ : M2 E N) (hγ : γ ∈ UU E N) :
    LinearIndependent E (fun i => (γ.submatrix Sum.inr id) i) ∧
      γ.submatrix Sum.inr id * Matrix.J (Fin N) E * ccT (γ.submatrix Sum.inr id) = 0 := by
  obtain ⟨⟨hdet, -, hc, -⟩, -⟩ := unitary_act_halfSpace E ∅ N γ hγ
  constructor
  · have h : LinearIndependent E (fun i => γ i) :=
      Matrix.linearIndependent_rows_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det γ).mpr hdet)
    exact h.comp Sum.inr Sum.inr_injective
  · have h : γ * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E := by
      have : ccT (ccT γ) * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E := hc
      rwa [ccT_ccT'] at this
    ext i j
    have h' : (γ * Matrix.J (Fin N) E * ccT γ) (Sum.inr i) (Sum.inr j) = 0 := by
      rw [h]
      simp [Matrix.J]
    exact h'
end GlobalTheory.SW.LagRep
