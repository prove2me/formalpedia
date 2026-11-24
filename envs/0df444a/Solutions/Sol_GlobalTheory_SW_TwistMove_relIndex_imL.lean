-- Prove2me | solution 1 for GlobalTheory.SW.TwistMove.relIndex_imL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:45:33.16106+00:00
-- url     : https://prove2.me/submissions/cfe8c520-eafc-4365-89c7-6e7e6ffb966f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevel
import Theorems.Thm_GlobalTheory_SW_TwistMove_std_eq_closure

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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistMove
open GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.TwistMove
theorem _root_.solution {b₁ b₂ : Matrix (Fin N) (Fin N) E} (h₁ : b₁.det ≠ 0) (h₂ : b₂.det ≠ 0)
    (hle : imL b₁ ≤ imL b₂) :
    ((imL b₁).relIndex (imL b₂) : ℚ) * |Algebra.norm ℚ b₂.det| = |Algebra.norm ℚ b₁.det| := by
  let B := Pi.basis fun _ : Fin N => integralBasis E
  have key : ∀ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 → ∃ B' : Module.Basis _ ℚ (Fin N → E),
      imL b = AddSubgroup.closure (Set.range B') ∧ B.det B' = Algebra.norm ℚ b.det := by
    intro b hb
    have hd : LinearMap.det (Matrix.toLin' b) ≠ 0 := by rwa [LinearMap.det_toLin']
    refine ⟨B.map (((Matrix.toLin' b).equivOfDetNeZero hd).restrictScalars ℚ), ?_, ?_⟩
    · rw [imL, std_eq_closure, AddMonoidHom.map_closure, ← Set.range_comp]
      rfl
    · rw [← LinearMap.det_toLin', ← LinearMap.det_restrictScalars]
      have := B.det_comp ((Matrix.toLin' b).restrictScalars ℚ) B
      rw [B.det_self, mul_one] at this
      exact this
  obtain ⟨B₁, e₁, d₁⟩ := key b₁ h₁
  obtain ⟨B₂, e₂, d₂⟩ := key b₂ h₂
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hle B₁ B₂ e₁ e₂, ← d₁, ← d₂, ← abs_mul, mul_comm,
    Module.Basis.det_mul_det]
end GlobalTheory.SW.TwistMove
