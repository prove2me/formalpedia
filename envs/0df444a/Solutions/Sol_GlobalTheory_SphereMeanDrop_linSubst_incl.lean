-- Prove2me | solution 1 for GlobalTheory.SphereMeanDrop.linSubst_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:26.613626+00:00
-- url     : https://prove2.me/submissions/70cf80fc-b88b-4a42-a804-70aacb08014d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMeanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreservingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsMultiHomogeneousRenameCastLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanDrop
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights
namespace GlobalTheory.SphereMeanDrop
theorem _root_.solution {B N n : ℕ} (h : N ≤ n) (f : MvPolynomial (Fin B × Fin N) ℂ) :
    GlobalTheory.ChowHt.linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
                 if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f := by
  unfold GlobalTheory.ChowHt.linSubst
  have hfun : (fun p : Fin B × Fin N => ∑ k : Fin n, C ((Matrix.of fun (j : Fin N) (k : Fin n) =>
      if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) p.2 k) * X (p.1, k)) =
      fun p => X (p.1, Fin.castLE h p.2) := by
    funext p
    rw [Fintype.sum_eq_single (Fin.castLE h p.2)]
    · simp
    · intro k hk
      have hne : (p.2 : ℕ) ≠ (k : ℕ) := fun he => hk (Fin.ext (by rw [Fin.coe_castLE]; exact he.symm))
      simp [Matrix.of_apply, hne]
  rw [hfun]
  have hal : (aeval fun p : Fin B × Fin N => (X (p.1, Fin.castLE h p.2) : MvPolynomial (Fin B × Fin n) ℂ)) =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) :=
    MvPolynomial.algHom_ext fun p => by simp
  rw [hal]
end GlobalTheory.SphereMeanDrop
