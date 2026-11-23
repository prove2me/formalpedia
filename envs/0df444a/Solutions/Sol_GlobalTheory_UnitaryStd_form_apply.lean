-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.form_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:16.466234+00:00
-- url     : https://prove2.me/submissions/3fc62c5e-f37e-4437-8929-8cad4223f467

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open GlobalTheory GlobalTheory.UnitaryStd
variable {r g : ℕ}
variable {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)
variable {ρ g}
variable (ρ g)
namespace GlobalTheory.UnitaryStd
theorem _root_.solution (S : Matrix (Fin r) (Fin r) ℤ) (x y : Lat ρ g) :
    form ρ g S x y = ∑ i, ∑ j, S i j * ((x i).1 ⬝ᵥ (y j).2 - (x i).2 ⬝ᵥ (y j).1) := rfl
end GlobalTheory.UnitaryStd
