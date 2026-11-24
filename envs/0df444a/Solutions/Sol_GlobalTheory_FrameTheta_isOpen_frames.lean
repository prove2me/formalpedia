-- Prove2me | solution 1 for GlobalTheory.FrameTheta.isOpen_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:29:45.082392+00:00
-- url     : https://prove2.me/submissions/66c38961-a5fc-4217-9ae4-ad431067be62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsThetaFrameFrames
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FrameTheta
namespace GlobalTheory.FrameTheta
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (p : ℕ) : IsOpen (FD.GG Ψ G p) := by
  have hmat : ∀ τ : Ψ, Continuous fun x : FD.Frame Ψ r => FD.mat x τ := fun τ =>
    show Continuous fun x : FD.Frame Ψ r => (x τ : Matrix (Fin r) (Fin r) ℂ) from continuous_apply τ
  have hgram : ∀ τ : Ψ, Continuous fun x : FD.Frame Ψ r => FD.gram τ.1 G (FD.mat x τ) := by
    intro τ
    refine continuous_matrix fun a b => ?_
    simp only [FD.gram, FD.hermC, FD.col, FD.mat, Matrix.of_apply]
    fun_prop
  have hdmin : ∀ (τ : Ψ) (i : Fin (r + 1)), Continuous fun x : FD.Frame Ψ r => FD.dmin G x τ i := by
    intro τ i
    unfold FD.dmin FD.lminor
    exact ((hgram τ).matrix_submatrix _ _).matrix_det
  unfold FD.GG
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (hmat τ).matrix_det continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))
end GlobalTheory.FrameTheta
