-- Prove2me | solution 1 for GlobalTheory.SW.EisConv.span_rows_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:28:36.456798+00:00
-- url     : https://prove2.me/submissions/755276fb-e772-43b4-bf9b-e0173c800aa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.EisConv
theorem _root_.solution {m : Type} (a : Matrix (Fin N) (Fin N) E) (ha : a.det ≠ 0)
    (W : Matrix (Fin N) m E) :
    Submodule.span E (Set.range fun i => (a * W) i) = Submodule.span E (Set.range fun i => W i) := by
  have key : ∀ (b : Matrix (Fin N) (Fin N) E) (X : Matrix (Fin N) m E),
      Submodule.span E (Set.range fun i => (b * X) i) ≤
        Submodule.span E (Set.range fun i => X i) := by
    intro b X
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : (b * X) i = ∑ k, b i k • X k := by ext j; simp [mul_apply]
    simp only [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine le_antisymm (key a W) ?_
  have := key a⁻¹ (a * W)
  rwa [← Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit ha), Matrix.one_mul] at this
end GlobalTheory.SW.EisConv
