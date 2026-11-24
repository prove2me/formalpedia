-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums.formFrame_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:12.607301+00:00
-- url     : https://prove2.me/submissions/e42051b9-4651-487a-9688-c3fb03d5bd1e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_InfinitePlaceDepthSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums
namespace GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums
theorem _root_.solution {K : Type} [Field K] [NumberField K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    IsUnit (formFrame H v).det ∧
      ((formFrame H v)⁻¹).conjTranspose * (formFrame H v)⁻¹ = H.map v.embedding := by
  unfold formFrame
  generalize H.map v.embedding = A at h
  have h0 : 0 ≤ A := h.posSemidef.nonneg
  have h1 : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h0
  have hd : IsUnit (CFC.sqrt A).det := by
    have : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 h.isUnit
    rw [← h1, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hh : (CFC.sqrt A).conjTranspose = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)).isHermitian
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hd, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ hd, hh, h1]
end GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums
