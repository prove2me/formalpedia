-- Prove2me | solution 1 for GlobalTheory.KeyKa.submatrix_mul_of_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:32:29.950805+00:00
-- url     : https://prove2.me/submissions/5fd64fc5-f84f-4e74-8221-81d553e803b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution {R Ix J K L : Type} [CommRing R] [Fintype Ix] [Fintype L]
    (A B : Matrix Ix Ix R) (f : J → Ix) (g : K → Ix) (i : L → Ix) (hi : Function.Injective i)
    (h : ∀ p q r, r ∉ Set.range i → A (f p) r * B r (g q) = 0) :
    (A * B).submatrix f g = A.submatrix f i * B.submatrix i g := by
  classical
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  exact Fintype.sum_of_injective i hi _ (fun r => A (f p) r * B r (g q))
    (fun r hr => h p q r hr) (fun _ => rfl)
end GlobalTheory.KeyKa
