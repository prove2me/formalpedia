-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.basis_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:16.307017+00:00
-- url     : https://prove2.me/submissions/2f9b7719-1099-4312-aed9-f3f441b5b200

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
theorem _root_.solution (p : Fin r × (Fin g ⊕ Fin g)) (i : Fin r) :
    basis ρ g p i = (fun k => Pi.single (M := fun _ => ℤ) p 1 (i, Sum.inl k),
      fun k => Pi.single (M := fun _ => ℤ) p 1 (i, Sum.inr k)) := by
  rw [basis, Module.Basis.coe_ofEquivFun]
  rfl
end GlobalTheory.UnitaryStd
