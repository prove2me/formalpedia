-- Prove2me | solution 1 for MassDataIdxStIm.parMap_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:56.412606+00:00
-- url     : https://prove2.me/submissions/5158e0eb-2e3c-4876-9728-69b717d67e6e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Block31OfBlocks
import Theorems.Thm_MassDataIdxStIm_block12_of_blocks
import Theorems.Thm_MassDataIdxStIm_block13_of_blocks
import Theorems.Thm_MassDataIdxStIm_block23_of_blocks

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
theorem _root_.solution (P : Matrix (Fin k) (Fin k) A → Prop) : Function.Bijective (parMap (r := r) P) := by
  constructor
  · rintro ⟨⟨a1, ha1⟩, ⟨f1, hf1⟩, ⟨h1, hh1⟩, b1, c1, e1⟩ ⟨⟨a2, ha2⟩, ⟨f2, hf2⟩, ⟨h2, hh2⟩, b2, c2, e2⟩ heq
    have hx := congrArg Subtype.val heq
    change mk a1 b1 c1 (midEmb h1) e1 f1 = mk a2 b2 c2 (midEmb h2) e2 f2 at hx
    have ea := congrArg b11 hx
    have eb := congrArg b12 hx
    have ec := congrArg b13 hx
    have em := congrArg b22 hx
    have ee := congrArg b23 hx
    have ef := congrArg b33 hx
    rw [block11_of_blocks, block11_of_blocks] at ea
    rw [block12_of_blocks, block12_of_blocks] at eb
    rw [block13_of_blocks, block13_of_blocks] at ec
    rw [block22_of_blocks, block22_of_blocks] at em
    rw [block23_of_blocks, block23_of_blocks] at ee
    rw [block33_of_blocks, block33_of_blocks] at ef
    have eh : h1 = h2 := by
      have := congrArg Matrix.toBlocks₁₁ em
      simpa [midEmb] using this
    subst ea eb ec ee ef eh
    rfl
  · rintro ⟨x, h11, h33, h21, h31, h32, h, hP, h22⟩
    refine ⟨(⟨b11 x, h11⟩, ⟨b33 x, h33⟩, ⟨h, hP⟩, b12 x, b13 x, b23 x), ?_⟩
    apply Subtype.ext
    change mk (b11 x) (b12 x) (b13 x) (midEmb h) (b23 x) (b33 x) = x
    have z21 : ∀ i j, x (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := fun i j => by
      simpa [b21] using congrFun (congrFun h21 i) j
    have z31 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := fun i j => by
      simpa [b31] using congrFun (congrFun h31 i) j
    have z32 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = 0 := fun i j => by
      simpa [b32] using congrFun (congrFun h32 i) j
    rw [← h22]
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [mk, b11, b12, b13, b22, b23, b33, z21, z31, z32]
end MassDataIdxStIm
