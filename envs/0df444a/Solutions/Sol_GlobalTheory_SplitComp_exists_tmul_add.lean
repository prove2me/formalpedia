-- Prove2me | solution 1 for GlobalTheory.SplitComp.exists_tmul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:45.33849+00:00
-- url     : https://prove2.me/submissions/12b0b32d-33e0-4038-9277-0c34f9423179

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
import Theorems.Thm_GlobalTheory_SplitComp_exists_real_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct
open GlobalTheory GlobalTheory.SplitComp
variable (L : Type) [Field L] [NumberField L] [IsCMField L]
namespace GlobalTheory.SplitComp
theorem _root_.solution (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (z : AL L) :
    ∃ a b : AFplus L, z = (1 : L) ⊗ₜ[maximalRealSubfield L] a + θ ⊗ₜ[maximalRealSubfield L] b := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x c =>
    obtain ⟨a, b, rfl⟩ := exists_real_add L θ h0 hθ x
    exact ⟨a • c, b • c, by rw [add_tmul, smul_tmul, smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [tmul_add, tmul_add]; abel⟩
end GlobalTheory.SplitComp
