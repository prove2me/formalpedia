-- Prove2me | solution 1 for GlobalTheory.SW.WeilAct.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:01:06.419311+00:00
-- url     : https://prove2.me/submissions/9a35bf9f-1b01-4baa-9b26-0b0adecdb37a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Theorems.Thm_GlobalTheory_SW_Base_I_mem_Hn
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace
import Theorems.Thm_GlobalTheory_T_hermitianTheta_summable_and_determines_testFn


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
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.WeilAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.WeilAct
theorem _root_.solution (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ ψ ψ' : Matrix (Fin n) (Fin N) E → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ')
    (t : TransH Ψ γ φ ψ) (t' : TransH Ψ γ φ ψ') : ψ = ψ' := by
  have hZ := Base.I_mem_Hn (N := N) Ψ
  set Z : CM Ψ N N := fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) with hZdef
  obtain ⟨hd, hA, -⟩ := (unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  refine (GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N ψ hψ _ hA).2 ψ' hψ' fun w w' => ?_
  have u1 : ∀ τ, IsUnit (hDen Ψ γ Z τ).det := fun τ => (hd τ).1.isUnit
  have u2 : ∀ τ, IsUnit (hDen' Ψ γ Z τ).det := fun τ => by
    refine Ne.isUnit fun h => (hd τ).1 ?_
    rw [← (hd τ).2.1, h, zero_mul]
  have e1 := t Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k)
    (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)
  have e2 := t' Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k)
    (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)
  have a1 : (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ
      (Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k) k : CM Ψ n N) = w := by
    funext τ
    ext k i
    change ((hDen' Ψ γ Z τ)⁻¹ *ᵥ (hDen' Ψ γ Z τ *ᵥ w τ k)) i = _
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (u2 τ), Matrix.one_mulVec]
  have a2 : (fun τ => Matrix.of fun k =>
      (Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ) k ᵥ* (hDen Ψ γ Z τ)⁻¹ : CM Ψ n N) = w' := by
    funext τ
    ext k i
    change ((w' τ k ᵥ* hDen Ψ γ Z τ) ᵥ* (hDen Ψ γ Z τ)⁻¹) i = _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (u1 τ), Matrix.vecMul_one]
  have e := e1.trans e2.symm
  beta_reduce at e
  rw [a1, a2] at e
  exact e
end GlobalTheory.SW.WeilAct
