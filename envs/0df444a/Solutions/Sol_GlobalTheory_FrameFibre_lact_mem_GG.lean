-- Prove2me | solution 1 for GlobalTheory.FrameFibre.lact_mem_GG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:14.366707+00:00
-- url     : https://prove2.me/submissions/ac657991-fbb6-4b0b-b07c-72f8d16d0756

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_PerMove_col_mul
import Theorems.Thm_GlobalTheory_PerMove_hermC_unitary
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
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FrameFibre
variable {E : Type} [Field E] [NumberField E] {r : ℕ}
variable [IsCMField E]
namespace GlobalTheory.FrameFibre
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {q : ℕ} {γ : GL (Fin r) E}
    (hγ : ∀ u v, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      FD.herm G u v) {x : FD.Frame Ψ r} (hx : x ∈ FD.GG Ψ G q) : FD.lact γ x ∈ FD.GG Ψ G q := by
  intro τ
  have e1 : FD.mat (FD.lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * FD.mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map τ.1.mapMatrix)
    rw [e1, Matrix.det_mul]
    exact mul_ne_zero hu.ne_zero (hx τ).1
  · have h := (hx τ).2 i
    have e2 : FD.gram τ.1 G (FD.mat (FD.lact γ x) τ) = FD.gram τ.1 G (FD.mat x τ) := by
      ext a b
      simp only [FD.gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
    unfold FD.dmin at h ⊢
    rwa [e2]
end GlobalTheory.FrameFibre
