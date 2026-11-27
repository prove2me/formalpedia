-- Prove2me | solution 1 for GlobalTheory.KeyPow.normalAt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:31.476911+00:00
-- url     : https://prove2.me/submissions/3652cbc4-6fa7-4951-9e8e-2ee0247cab1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LatticeBlocks
import Theorems.Thm_GlobalTheory_KeyPow_det_blocks
import Theorems.Thm_GlobalTheory_KeyPow_lattice_blocks
import Theorems.Thm_GlobalTheory_T_exists_holomorphicUniformisation_powerThetaKeyDatum
import Theorems.Thm_GlobalTheory_thetaChar_blockDiagonal
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
namespace GlobalTheory.KeyPow
theorem _root_.solution : ∀ (x y : KeyIn ℂ) (j : ℕ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℝ) (c : ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → GlobalTheory.KeyPow.NormalAt x τ M (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) c → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (τ' M' : Matrix (Fin y.P.g) (Fin y.P.g) ℂ), M'.det = M.det ^ j ∧ GlobalTheory.KeyPow.NormalAt y τ' M' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) (c ^ j) := by
  rintro x y j τ M a b c hp ⟨u, hs, hd, hΛ, hr, hf, hv⟩
  obtain ⟨e, u', hΛ', hr', hf', hv'⟩ := GlobalTheory.T.exists_holomorphicUniformisation_powerThetaKeyDatum x y j u _
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M) hp hr hf hv
  obtain ⟨hs', hd', hθ⟩ := thetaChar_blockDiagonal j _ τ a b _ e hs hd
  refine ⟨e, _, _, det_blocks e M, u', hs', hd', fun z => ?_, hr', ?_, fun p => ?_⟩
  · rw [hΛ', ← lattice_blocks]
    exact forall_congr' fun i => hΛ _
  · convert hf' using 2 with z
    rw [hθ, Finset.prod_mul_distrib]
    simp
  · convert hv' p using 1
    funext q
    simp only [Pi.smul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
end GlobalTheory.KeyPow
