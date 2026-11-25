-- Prove2me | solution 1 for GlobalTheory.SW.LagRep.exists_rep_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:13.193808+00:00
-- url     : https://prove2.me/submissions/29d288cb-b046-4631-9075-5b4e306d8821

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
import Theorems.Thm_GlobalTheory_SW_LagRep_linearIndependent_mul
import Theorems.Thm_GlobalTheory_SW_LagRep_span_mul
import Theorems.Thm_P2M_GlobalTheory_SW_LagRep_ccT_mul__96963e977bb1
import Theorems.Thm_GlobalTheory_SW_LagRep_lower_rows
import Theorems.Thm_GlobalTheory_SW_RowExt_exists_unitary_ext
import Theorems.Thm_GlobalTheory_SW_exists_nearly_primitive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LagRep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.LagRep
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ),
    ∃ c : ℕ, 0 < c ∧ ∀ U : Lag E N, ∃ γ ∈ UU E N, Den c γ ∧ botSpan γ = U.1 := by
  intro E _ _ _ N
  classical
  obtain ⟨c, C, hc, hprim⟩ := exists_nearly_primitive E N
  obtain ⟨c', hc', hext⟩ := RowExt.exists_unitary_ext E N c hc
  refine ⟨c', hc', ?_⟩
  rintro ⟨U, γ₀, hγ₀, rfl⟩
  obtain ⟨hli, hiso⟩ := lower_rows γ₀ hγ₀
  set W₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E := γ₀.submatrix Sum.inr id with hW₀
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin N × (Fin N ⊕ Fin N) => W₀ p.1 p.2)
  set D : Matrix (Fin N) (Fin N) E := (d : E) • (1 : Matrix (Fin N) (Fin N) E) with hD
  have hDdet : D.det ≠ 0 := by
    rw [hD, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Int.cast_ne_zero.mpr hd)
  have hDint : IntM (D * W₀) := by
    intro i j
    have := hint (W₀ i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    rw [hD, Matrix.smul_mul, Matrix.one_mul]
    simpa [zsmul_eq_mul] using this
  obtain ⟨a, ha, -, haint, hap⟩ := hprim _ (D * W₀) hDint (linearIndependent_mul D hDdet W₀ hli)
  obtain ⟨γ, hγ, hden, hrows⟩ := hext (a * (D * W₀)) haint
    (linearIndependent_mul a ha _ (linearIndependent_mul D hDdet W₀ hli))
    (by
      have : a * (D * W₀) * Matrix.J (Fin N) E * ccT (a * (D * W₀)) =
          a * D * (W₀ * Matrix.J (Fin N) E * ccT W₀) * (ccT D * ccT a) := by
        simp only [ccT_mul', Matrix.mul_assoc]
      rw [this, hiso, Matrix.mul_zero, Matrix.zero_mul]) hap
  refine ⟨γ, hγ, hden, ?_⟩
  show botSpan γ = botSpan γ₀
  unfold botSpan
  simp only [hrows]
  rw [span_mul a ha, span_mul D hDdet]
  rfl
end GlobalTheory.SW.LagRep
