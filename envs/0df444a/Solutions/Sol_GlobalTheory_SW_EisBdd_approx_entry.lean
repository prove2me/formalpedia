-- Prove2me | solution 1 for GlobalTheory.SW.EisBdd.approx_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:10.741332+00:00
-- url     : https://prove2.me/submissions/9f96b5e8-005b-41aa-9532-8021b161556f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBounded
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisBdd
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.EisBdd
theorem _root_.solution (hΨ : IsType Ψ) : ∃ K : ℝ, ∀ w : Ψ → ℂ, ∃ a : E, IsIntegral ℤ a ∧
    ∀ τ : Ψ, ‖w τ - τ.1 a‖ ≤ K := by
  classical
  refine ⟨∑ σ : E →+* ℂ, ∑ i, ‖σ (integralBasis E i)‖, fun w => ?_⟩
  let w' : (E →+* ℂ) → ℂ := fun σ => if h : σ ∈ Ψ then w ⟨σ, h⟩ else 0
  let x : (E →+* ℂ) → ℂ := fun σ => w' σ + conj (w' (ComplexEmbedding.conjugate σ))
  let c := (canonicalEmbedding.latticeBasis E).repr x
  have hx : ∀ σ, x σ = ∑ i, c i * σ (integralBasis E i) := fun σ => by
    conv_lhs => rw [← (canonicalEmbedding.latticeBasis E).sum_repr x]
    simp [c, canonicalEmbedding.latticeBasis_apply, Finset.sum_apply]
  have hre : ∀ τ : Ψ, w τ = ∑ i, ((c i).re : ℂ) * τ.1 (integralBasis E i) := fun τ => by
    have h0 : w' (ComplexEmbedding.conjugate τ.1) = 0 := dif_neg ((hΨ τ.1).1 τ.2)
    have h1 : w' τ.1 = w τ := dif_pos τ.2
    have h2 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1) = τ.1 := star_star _
    have e1 := hx τ.1
    have e2 := congrArg conj (hx (ComplexEmbedding.conjugate τ.1))
    simp only [x, h0, h1, h2, map_zero, add_zero, zero_add, conj_conj, map_sum, map_mul,
      ComplexEmbedding.conjugate_coe_eq] at e1 e2
    have : w τ = (w τ + w τ) / 2 := by ring
    rw [this]
    nth_rewrite 1 [e1]
    rw [e2, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_eq_add_conj]
    ring
  refine ⟨∑ i, (⌊(c i).re⌋ : E) * integralBasis E i, IsIntegral.sum _ fun i _ => ?_, fun τ => ?_⟩
  · refine IsIntegral.mul ?_ ?_
    · simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := ⌊(c i).re⌋)
    · rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  · rw [hre, map_sum, ← Finset.sum_sub_distrib]
    refine le_trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
      (Finset.single_le_sum (f := fun σ : E →+* ℂ => ∑ i, ‖σ (integralBasis E i)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ.1))
    rw [map_mul, map_intCast, ← sub_mul, norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
end GlobalTheory.SW.EisBdd
