-- Prove2me | solution 1 for MassDataIdxStIm.card_isN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:47.860494+00:00
-- url     : https://prove2.me/submissions/5336ae3a-057d-4151-a58d-10b165adf328

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Block31OfBlocks
import Theorems.Thm_MassDataIdxStIm_card_par

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open MassDataIdxStIm
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]
variable {r k : ℕ}
namespace MassDataIdxStIm
theorem _root_.solution (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} =
      Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  have e : {x : Matrix (Idx r k) (Idx r k) K // IsN x} ≃
      {x : Matrix (Idx r k) (Idx r k) K // Par (fun h : Matrix (Fin k) (Fin k) K => h = 1) x} :=
    Equiv.subtypeEquivRight (fun x => by
      unfold IsN Par
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6⟩
        exact ⟨h1, h2, h4, h5, h6, 1, rfl, by rw [h3]; simp [midEmb]⟩
      · rintro ⟨h1, h2, h4, h5, h6, h, rfl, h3⟩
        exact ⟨h1, h2, by rw [h3]; simp [midEmb], h4, h5, h6⟩)
  have hone : Nat.card {h : Matrix (Fin k) (Fin k) K // h = 1} = 1 := by
    first
      | exact Nat.card_unique
      | simp
  rw [Nat.card_congr e, card_par, hone, one_mul]
end MassDataIdxStIm
