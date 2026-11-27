-- Prove2me | solution 1 for GlobalTheory.ChF.exists_linDat_of_extSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:24:15.877389+00:00
-- url     : https://prove2.me/submissions/f6355b65-bc6a-44a0-9d1d-49e99aff13c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalSeriesJacobianChainRuleLinearPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalTorusCharacterLiftToLawStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLinearDataOfSplitFormalGroupExtension
import Theorems.Thm_GlobalTheory_T_exists_formalTorus_character_lift_to_law
import Theorems.Thm_GlobalTheory_T_formalSeriesJacobian_chain_rule_linearPart
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_u1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (d g r : ℕ) (F : FGLaw O d) (FB : FGLaw O g) (J : Fin d → PS O 1 r) (Q : Fin g → PS O 1 d), ExtSer F.F FB.F J Q → FH p F.F → ∀ (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (αB : OE → Fin g → PS O 1 g), (∀ a, lin Q * ρG a = lin (αB a) * lin Q) → (∀ a, ρG a * lin J = lin J * (N a).map (Int.castRingHom O)) → (∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (αB a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ ∀ i, ∃ u : PS O 1 g, IsCh FB.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (B : Matrix (Fin g) (Fin d) O) (m : ℕ) (u : Fin m → PS O 1 d), (∀ k, IsCh F.F (u k)) ∧ LinDat H (lin J) B ρG N (fun k => dl (u k)) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ d g r F FB J Q hE hFH ρG N αB hB hA ⟨cp, hU, H, S, hP, hPL, hS, hα, hu⟩
  classical
  obtain ⟨h0, A', B', hA', hB', hAB⟩ := hE.exact
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hS1 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdet
  have hS2 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hdet
  choose u1 hu1 hu1' using hu
  choose u2 hu2 hu2' using GlobalTheory.T.exists_formalTorus_character_lift_to_law p C v O hv d r F hFH J A' hE.homI hA'
  obtain ⟨hc1, -, hc3⟩ := GlobalTheory.T.formalSeriesJacobian_chain_rule_linearPart O d g Q hE.homQ.1
  let w : (Fin g ⊕ Fin g) ⊕ Fin r → PS O 1 d := Sum.elim (fun i => sub ![Q] (u1 i)) u2
  let e := Fintype.equivFin ((Fin g ⊕ Fin g) ⊕ Fin r)
  refine ⟨cp, hU, H, S⁻¹ * lin Q, _, fun k => w (e.symm k), ?_, ⟨hP, hPL⟩, ⟨?_, A', B' * S, hA', ?_, ?_⟩,
    ?_, hA, ?_, ?_⟩
  · intro k
    show IsCh F.F (w (e.symm k))
    rcases e.symm k with i | i
    · exact hc3 F FB hE.homQ _ (hu1 i)
    · exact hu2 i
  · rw [Matrix.mul_assoc, h0, Matrix.mul_zero]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (lin Q), hB', Matrix.one_mul, hS1]
  · rw [Matrix.mul_assoc B', ← Matrix.mul_assoc S, hS2, Matrix.one_mul, hAB]
  · intro a
    have h : S⁻¹ * lin (αB a) = H.ρL (1 ⊗ₜ[ℤ] a) * S⁻¹ := by
      calc S⁻¹ * lin (αB a) = S⁻¹ * (lin (αB a) * S) * S⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hS2, Matrix.mul_one]
        _ = _ := by rw [hα a, ← Matrix.mul_assoc, hS1, Matrix.one_mul]
    rw [Matrix.mul_assoc, hB a, ← Matrix.mul_assoc, h, Matrix.mul_assoc]
  · intro i
    refine ⟨e (Sum.inl i), ?_⟩
    simp only [Equiv.symm_apply_apply, w, Sum.elim_inl]
    rw [(hc1 _).1, ← hu1' i, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.mul_assoc, hS2,
      Matrix.one_mul]
  · intro i
    refine ⟨e (Sum.inr i), ?_⟩
    simp only [Equiv.symm_apply_apply, w, Sum.elim_inr]
    exact hu2' i
end GlobalTheory.ChF
