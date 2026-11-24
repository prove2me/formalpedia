-- Prove2me | solution 1 for GlobalTheory.FinTypCount.exists_nat_smul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:37.013121+00:00
-- url     : https://prove2.me/submissions/892177ab-e4d9-4f73-a8d8-8f04f955da39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
namespace GlobalTheory.FinTypCount
theorem _root_.solution (e : L) : ∃ D : ℕ, 0 < D ∧ ∃ o : 𝓞 L, (o : L) = D • e := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := L) ({e} : Finset L)
  refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
  have hi : IsIntegral ℤ ((y * y).natAbs • e) := by
    rw [← natCast_zsmul, Int.natAbs_of_nonneg (mul_self_nonneg y), mul_smul]
    exact (h e (Finset.mem_singleton_self e)).smul y
  exact ⟨⟨_, hi⟩, rfl⟩
end GlobalTheory.FinTypCount
