-- Prove2me | solution 1 for OAI.MaxCutGames.theorem11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:18:19.591018+00:00
-- url     : https://prove2.me/submissions/d165dd32-d727-46d7-84d0-55ef88646fe3

import Mathlib
import Definitions.Def_OAIQ087A035
import Theorems.Thm_OAI_MaxCutGames_Decoder_ActualMatrixContradiction_contradiction
import Theorems.Thm_OAI_MaxCutGames_Decoder_MatrixGapChoice_exists_inverse_parameters
import Theorems.Thm_OAI_MaxCutGames_Gadget_BaseConstruction_exists_base
import Theorems.Thm_OAI_MaxCutGames_Inverse_ShortcodeTheorem_inversePrinciple

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BinaryCoordinates
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Dimension-independent transport between the compact bit-vector coordinates of
the finite motif and the coordinate functions used by the later constructions.
The vector-space addition involved here is XOR, not modular integer addition.
-/

/-! Exact transport from XOR bit vectors to vector spaces over `ZMod 2`. -/
namespace MaxCutGames.Integration.BinaryLinear

open BinaryCoordinates

theorem finrank_vector (n : Nat) : Module.finrank F2 (Vector n) = n := by
  simp [Vector]

end MaxCutGames.Integration.BinaryLinear

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Parameters
attribute [-instance] _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scalar parameter selection for the v2 repetition rate.

These results concern powers of real numbers only. In particular, they do not
assert a parallel-repetition theorem for games. The exponent depends only on
the gap and the desired error; no alphabet or logical dimension occurs here.
-/

namespace MaxCutGames.Repetition

theorem dsRate_lt_one {gap : ℝ} (hgap : 0 < gap) : dsRate gap < 1 := by
  dsimp [dsRate]
  nlinarith [sq_pos_of_pos hgap]

/-- A scalar contraction admits a strictly positive exponent for every positive
target error. This lemma makes no assertion about any game value. -/
theorem exists_positive_power_lt {rate error : ℝ}
    (hrate₀ : 0 ≤ rate) (hrate₁ : rate < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ rate ^ n < error := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hrate₀ hrate₁
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds herror)).exists
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), ?_⟩
  calc
    rate ^ (n + 1) = rate ^ n * rate := pow_succ _ _
    _ ≤ rate ^ n := mul_le_of_le_one_right (pow_nonneg hrate₀ n) hrate₁.le
    _ < error := hn

/-- Select the repetition count before choosing any alphabet. -/
theorem exists_dsRate_pow_le {gap error : ℝ}
    (hgap₀ : 0 < gap) (hgap₁ : gap < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ dsRate gap ^ n ≤ error := by
  obtain ⟨n, hn, hbound⟩ := exists_positive_power_lt
    (dsRate_nonneg hgap₀.le hgap₁.le) (dsRate_lt_one hgap₀) herror
  exact ⟨n, hn, hbound.le⟩

theorem dsRate_one_div_eight_hundred :
    dsRate (1 / 800) = 1 - (1 : ℝ) / 10240000 := by
  norm_num [dsRate]

/-- The final soundness exponent depends only on `error`, even when the later
construction chooses its alphabet after this exponent. -/
theorem exists_final_repetition_count {error : ℝ} (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ (1 - (1 : ℝ) / 10240000) ^ n ≤ error := by
  simpa only [dsRate_one_div_eight_hundred] using
    exists_dsRate_pow_le (gap := (1 / 800 : ℝ)) (by norm_num) (by norm_num) herror

end MaxCutGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MaskMoment
attribute [-instance] _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Clean

open Foundations.Games
open scoped BigOperators

noncomputable section

variable {E : Type*} [Fintype E] [Nonempty E]

/-- The exponential estimate uses nonnegativity of `1 - x` before raising to
a natural power. It also covers the empty mask. -/
theorem mask_rate_le_exp {x : ℝ} (hx : x ≤ 1) (k : ℕ) :
    (1 - x) ^ k ≤ Real.exp (-(k : ℝ) * x) := by
  calc
    (1 - x) ^ k ≤ Real.exp (-x) ^ k :=
      pow_le_pow_left₀ (sub_nonneg.mpr hx) (Real.one_sub_le_exp_neg x) k
    _ = Real.exp (-(k : ℝ) * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem cube_singleton_probability_le_one {n : ℕ} (hn : 1 ≤ n) :
    (1 / (n : ℝ)) ^ 2 ≤ 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq₀ : 0 ≤ 1 / (n : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hq₁ : 1 / (n : ℝ) ≤ 1 :=
    (div_le_iff₀ (by linarith)).mpr (by simpa using hn')
  nlinarith [mul_nonneg hq₀ (sub_nonneg.mpr hq₁)]

/-- On cubes, `k = n^3` and `beta = n^(-2)`, so `k * beta = n`.
The advice-space size bound `N` is fixed independently of `n`. -/
theorem cube_mask_rate_le_exp {n : ℕ} (hn : 1 ≤ n) {N : ℝ} (hN : 1 ≤ N) :
    (1 - ((1 / (n : ℝ)) ^ 2 / N) / 3600) ^ (n ^ 3) ≤
      Real.exp (-(n : ℝ) / (3600 * N)) := by
  have hn₀ : (n : ℝ) ≠ 0 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN₀ : N ≠ 0 := by linarith
  have hq : (1 / (n : ℝ)) ^ 2 / N ≤ 1 :=
    (div_le_iff₀ (by linarith)).mpr
      (by simpa using (cube_singleton_probability_le_one hn).trans hN)
  have hx : (1 / (n : ℝ)) ^ 2 / N / 3600 ≤ 1 :=
    (div_le_iff₀ (by norm_num)).mpr (by linarith)
  have he : -((n ^ 3 : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ 2 / N / 3600) =
      -(n : ℝ) / (3600 * N) := by
    simp only [Nat.cast_pow]
    field_simp [hn₀, hN₀]

  calc
    _ ≤ Real.exp (-((n ^ 3 : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ 2 / N / 3600)) :=
      mask_rate_le_exp hx (n ^ 3)
    _ = _ := congrArg Real.exp he

/-- A repetition cube can be selected after fixing only the advice-space size
bound and the required error. This is a scalar fact, not a game-value theorem. -/
theorem exists_cube_exponential_lt {N error : ℝ} (hN : 0 < N) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ Real.exp (-(n : ℝ) / (3600 * N)) < error := by
  let rate := Real.exp (-(1 / (3600 * N)))
  have hrate₀ : 0 ≤ rate := (Real.exp_pos _).le
  have hrate₁ : rate < 1 := Real.exp_lt_one_iff.mpr
    (neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) hN)))
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hrate₀ hrate₁
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds herror)).exists
  refine ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m), ?_⟩
  have hp : rate ^ (m + 1) < error :=
    lt_of_le_of_lt (by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hrate₀ m) hrate₁.le) hm
  have he : Real.exp (-((m + 1 : ℕ) : ℝ) / (3600 * N)) = rate ^ (m + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [he]

end
end MaxCutGames.Clean

/-!
# Averaging the actual sparse clean experiment

The explicit seed has an independent singleton coin and uniform single-column
advice at each position. Additional independent data supply the intercept and
both full-block columns. Unused columns are sampled and discarded, allowing a
fixed finite product sample space. A local strategy may depend on the fixed
seed; the bound consequently also covers the original, less informed players.

The only mathematical rate input below is the stated bound on the actual
ordinary repeated game. No conditional distribution, local reconstruction,
mask distribution, or averaging assertion is assumed.
-/

/-!
# Exact overlap bound for independently sampled uniform fixed-size subsets

All expectations below are explicit rational sums over `Finset.powersetCard`.
The marginal inclusion probability is derived from the exact binomial count
of subsets containing a prescribed singleton. No probabilistic estimate is an
assumption. This is the active-set overlap bound used in Lemma 6.3.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalParameters
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence of the finite numerical choices in Section 4.1. All errors and
search tests here are rational, including the fourth-power test in (4.1). -/

/-! Actual finite binary-vector-space gadgets and their uniform experiments.
The existence statement is the target of the recursive construction, not an
assumed theorem. Noise is indexed by a nonempty finite type; repeated vector
values therefore keep their intended multiplicities. -/

namespace MaxCutGames.Gadget.ActualGadget

attribute [instance] Data.ambientAddCommGroup Data.ambientModule Data.ambientFintype
attribute [instance] Data.noiseFintype Data.noiseNonempty

end MaxCutGames.Gadget.ActualGadget

namespace MaxCutGames.Reduction.ActualSource

open MaxCutGames.Integration.BinaryLinear

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

end MaxCutGames.Reduction.ActualSource

/-! Transport of actual gadgets to the split coordinate model used by the reduction. -/

namespace MaxCutGames.Integration.SplitGadget

open BinaryLinear

variable {R : Type} [AddCommGroup R] [Module F2 R] [FiniteDimensional F2 R]

/-- Any injective symbol embedding admits finite coordinates in which it is the
first summand. This is a theorem about the actual ambient vector space. -/
theorem exists_split_equiv {s : Nat} (e : Vector s →ₗ[F2] R)
    (he : Function.Injective e) :
    ∃ d : Nat, ∃ φ : R ≃ₗ[F2] (Vector s × Vector d),
      ∀ c, φ (e c) = (c, 0) := by
  obtain ⟨U, hU⟩ := e.range.exists_isCompl
  let er := LinearEquiv.ofInjective e he
  let eu := (Module.finBasis F2 U).equivFun
  let split := e.range.prodEquivOfIsCompl U hU
  refine ⟨Module.finrank F2 U, split.symm.trans (er.symm.prodCongr eu), ?_⟩
  intro c
  change (er.symm.prodCongr eu) (split.symm (e c)) = (c, 0)
  have hc : split.symm (e c) = (er c, 0) :=
    e.range.prodEquivOfIsCompl_symm_apply_left U hU (er c)
  rw [hc]
  simp

open MaxCutGames.Gadget.ActualGadget (Data stabilityError failureIndicator kernelError Satisfies)
open MaxCutGames.Reduction.ActualSource

/-- Uniform stability is invariant under the coordinate change. -/
theorem transport_stabilityError {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0)) :
    (transport g φ he).stabilityError = stabilityError g := by
  classical
  apply Fintype.expect_equiv (φ.symm.toEquiv.prodCongr (Equiv.refl g.NoiseIndex))
  intro x
  simp [transport, failureIndicator, map_add]

/-- The restriction to the symbol space is exactly the same linear map. -/
theorem transport_symbol_map {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    (S.comp φ.toLinearMap).comp g.embed = S.comp (alphabetEmbedding s d) := by
  apply LinearMap.ext
  intro c
  change S (φ (g.embed c)) = S (c, 0)
  rw [he]

theorem transport_kernelProbability {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    kernelProbability (transport g φ he) S =
      kernelError g (S.comp φ.toLinearMap) := by
  rfl

/-- The coordinate representative preserves dispersion for every target,
including the question spaces used directly by the soundness analysis. -/
theorem exists_split_gadget_general {s : Nat} (g : Data (Vector s))
    {ζ ν : ℚ} {r : Nat} (hg : Satisfies g ζ ν r) :
    ∃ d : Nat, ∃ h : SplitGadget s d,
      h.stabilityError ≤ ζ ∧
      ∀ (P : Type) [AddCommGroup P] [Module F2 P]
        (S : Ambient s d →ₗ[F2] P),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        kernelProbability h S ≤ ν := by
  obtain ⟨d, φ, he⟩ := exists_split_equiv g.embed g.embed_injective
  refine ⟨d, transport g φ he, ?_, ?_⟩
  · rw [transport_stabilityError]
    exact hg.1
  · intro P _ _ S hS
    rw [transport_kernelProbability g φ he S]
    apply hg.2 P (S.comp φ.toLinearMap)
    rwa [transport_symbol_map g φ he S]

end MaxCutGames.Integration.SplitGadget

/-! Exact passage from the rational construction parameters and experiments to
the real inequalities used by the Fourier and soundness proofs. -/

/-! Lemma 6.3 for the actual independently sampled partner maps. -/

/-!
# Exact partner-map laws in shared raw target coordinates

Inactive positions do not use a retained slot. Replacing their slots leaves
both the concrete partner projection and the shared raw projection unchanged.

The row/column expectation identity below transports the two actual uniform
map samples through the target coordinate equivalence independently. It is an
exact identity for every observable of the pulled-back maps; it requires no
trace, character, or naturality hypotheses.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinishBounds
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scalar estimates for the last paragraph of the v2 construction. These lemmas
only perform the stated rounding/subdivision/repetition arithmetic; they do
not assume or assert an unproved repetition theorem or hardness result.
-/

namespace MaxCutGames.Explicit.FinishBounds

theorem exists_reciprocal_tolerance (ε : ℚ) (hε : 0 < ε) (t : Nat) (ht : 0 < t) :
    ∃ C : Nat, 200 ≤ C ∧ (0 : ℚ) < 1 / C ∧
      1 / (C : ℚ) ≤ 1 / 200 ∧ 1 / (C : ℚ) ≤ ε / t := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℚ) / ε)
  let C := n + 200
  have hC : (0 : ℚ) < C := by dsimp [C]; positivity
  have ht' : (0 : ℚ) < t := by exact_mod_cast ht
  have hCn : (n : ℚ) ≤ C := by dsimp [C]; exact_mod_cast Nat.le_add_right n 200
  have hbound : (t : ℚ) / ε < C := lt_of_lt_of_le hn hCn
  have hbudget : (t : ℚ) ≤ ε * C := by
    have he := (div_lt_iff₀ hε).mp hbound
    nlinarith
  refine ⟨C, by dsimp [C]; omega, one_div_pos.mpr hC, ?_, ?_⟩
  · apply one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 200)
    dsimp [C]
    exact_mod_cast Nat.le_add_left 200 n
  · apply (div_le_div_iff₀ hC ht').mpr
    simpa [mul_comm] using hbudget

end MaxCutGames.Explicit.FinishBounds

/-!
The outer error parameters are fixed before the latent gadget or its alphabet.
We use the same positive reciprocal integer for the latent noise budget and
the rounding tolerance. This permitted specialization makes uniform occurrence
rounding an exact fixed-copy operation. The later parity error is chosen only
after the tuple length has been fixed.
-/

namespace MaxCutGames.ParameterSelection
noncomputable section

/-- Choose the alphabet-independent exponent and both rational budgets using
only the two prescribed real errors. -/
theorem exists_outerParameters (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Nonempty (OuterParameters ε δ) := by
  obtain ⟨ε₀, hε₀, hεbound⟩ := exists_rat_btwn hε
  obtain ⟨δ₀, hδ₀, hδbound⟩ := exists_rat_btwn hδ
  have hεq : (0 : ℚ) < ε₀ := by exact_mod_cast hε₀
  have hδq : (0 : ℚ) < δ₀ := by exact_mod_cast hδ₀
  obtain ⟨t, ht, hrate⟩ := Repetition.exists_final_repetition_count hδ₀
  have htpos : 0 < t := ht
  obtain ⟨C, hC, hCpos, hCsmall, hCbudget⟩ :=
    Explicit.FinishBounds.exists_reciprocal_tolerance ε₀ hεq t htpos
  exact ⟨⟨ε₀, δ₀, hεq, hδq, hεbound.le, hδbound.le,
    t, htpos, hrate, C, hC, hCpos, hCsmall, hCbudget⟩⟩

end
end MaxCutGames.ParameterSelection

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SparseLaw
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite calculation behind v2 Lemma `projected-tv`. The three singleton
lines are averaged before the divergence is taken; projection choices are
not part of the compared sample space. Coordinates are independently sampled
occurrences, irrespective of whether their equation IDs coincide.
-/

namespace MaxCutGames.Decoder.SparseLaw

open scoped BigOperators
open MaxCutGames.Foundations.Information

noncomputable section

variable {α : Type*} [Fintype α]

theorem uniformChiSquare_eq_secondMoment [Nonempty α] (p : α → ℝ)
    (hp : IsProbability p) :
    uniformChiSquare p = (Fintype.card α : ℝ) * (∑ a, p a ^ 2) - 1 := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpoint (a : α) :
      (Fintype.card α : ℝ) * (p a - uniformWeights α a) ^ 2 =
        (Fintype.card α : ℝ) * p a ^ 2 - 2 * p a + uniformWeights α a := by
    simp only [uniformWeights]
    field_simp [hn]
    ring
  rw [uniformChiSquare, Finset.mul_sum]
  simp only [hpoint, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2,
    (uniformWeights_isProbability (α := α)).2]
  ring

theorem mixture_isProbability [Nonempty α] (p : α → ℝ) (hp : IsProbability p)
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) : IsProbability (mixture β p) := by
  constructor
  · intro a
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hβ') (uniformWeights_pos a).le)
      (mul_nonneg hβ (hp.1 a))
  · simp only [mixture, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2,
      (uniformWeights_isProbability (α := α)).2]
    ring

theorem uniformChiSquare_mixture (p : α → ℝ) (β : ℝ) :
    uniformChiSquare (mixture β p) = β ^ 2 * uniformChiSquare p := by
  have hpoint (a : α) :
      (mixture β p a - uniformWeights α a) ^ 2 =
        β ^ 2 * (p a - uniformWeights α a) ^ 2 := by
    unfold mixture
    ring
  simp only [uniformChiSquare, hpoint, ← Finset.mul_sum]
  ring

theorem totalVariation_le_half_sqrt (p : α → ℝ) :
    totalVariation p (uniformWeights α) ≤ Real.sqrt (uniformChiSquare p) / 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun _ => (1 : ℝ)) (fun a => |p a - uniformWeights α a|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs] at hcs
  have hs := Real.le_sqrt_of_sq_le hcs
  exact div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2)

theorem uniformChiSquare_independent [Nonempty α] (p : α → ℝ)
    (hp : IsProbability p) (k : ℕ) :
    uniformChiSquare (independentWeights p k) = (1 + uniformChiSquare p) ^ k - 1 := by
  rw [uniformChiSquare_eq_secondMoment _ (independentWeights_isProbability p hp k),
    uniformChiSquare_eq_secondMoment p hp]
  have hsecond : (∑ x : Fin k → α, independentWeights p k x ^ 2) =
      (∑ a, p a ^ 2) ^ k := by
    simp only [independentWeights, ← Finset.prod_pow]
    exact (Fintype.sum_pow (fun a => p a ^ 2) k).symm
  rw [hsecond]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [← mul_pow]
  exact congrArg (fun t : ℝ => t ^ k - 1) (by ring)

/-- A finite bound sufficient for the cube asymptotic, without introducing a
limit theorem or choosing the alphabet after the repetition count. -/
theorem pow_mul_one_sub_le_one (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k * (1 - k * x) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ (1 + x) ^ k := pow_nonneg (by linarith) _
    have herr : 0 ≤ (1 + x) ^ k * ((k : ℝ) + 1) * x ^ 2 :=
      mul_nonneg (mul_nonneg hp (by positivity)) (sq_nonneg x)
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem pow_sub_one_le_fraction (x : ℝ) (hx : 0 ≤ x) (k : ℕ)
    (hk : (k : ℝ) * x < 1) :
    (1 + x) ^ k - 1 ≤ (k : ℝ) * x / (1 - (k : ℝ) * x) := by
  apply (le_div_iff₀ (sub_pos.mpr hk)).2
  have h := pow_mul_one_sub_le_one x hx k
  nlinarith

theorem pow_sub_one_le_twice (x : ℝ) (hx : 0 ≤ x) (k : ℕ)
    (hk : (k : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ k - 1 ≤ 2 * (k : ℝ) * x := by
  have hk' : (k : ℝ) * x < 1 := by linarith
  refine (pow_sub_one_le_fraction x hx k hk').trans ?_
  apply (div_le_iff₀ (sub_pos.mpr hk')).2
  have hn : 0 ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  nlinarith

section Singleton

variable (V : Type*) [Fintype V] [Zero V] [DecidableEq V]

theorem lineCount_sum : ∑ z : V × V, lineCount V z = 3 * Fintype.card V := by
  have h₁ : (∑ z : V × V, if z.2 = 0 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type]
    simp
  have h₂ : (∑ z : V × V, if z.1 = 0 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp
  have h₃ : (∑ z : V × V, if z.1 = z.2 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type]
    simp
  simp only [lineCount, Finset.sum_add_distrib, h₁, h₂, h₃]
  ring

omit [Fintype V] in
theorem lineCount_sq (z : V × V) :
    lineCount V z ^ 2 = lineCount V z + (if z.1 = 0 ∧ z.2 = 0 then 6 else 0) := by
  by_cases hx : z.1 = 0 <;> by_cases hy : z.2 = 0 <;>
    by_cases hxy : z.1 = z.2 <;> simp_all [lineCount] ; norm_num

theorem lineCount_sq_sum :
    ∑ z : V × V, lineCount V z ^ 2 = 3 * Fintype.card V + 6 := by
  simp only [lineCount_sq, Finset.sum_add_distrib, lineCount_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (0 : V)]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem singletonPairWeights_isProbability : IsProbability (singletonPairWeights V) := by
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · intro z
    unfold singletonPairWeights lineCount
    positivity
  · simp only [singletonPairWeights, div_eq_mul_inv, ← Finset.sum_mul, lineCount_sum]
    exact mul_inv_cancel₀ (ne_of_gt (mul_pos (by norm_num) hn))

theorem singletonPairWeights_secondMoment :
    ∑ z : V × V, singletonPairWeights V z ^ 2 =
      (3 * Fintype.card V + 6) / (3 * Fintype.card V) ^ 2 := by
  simp only [singletonPairWeights, div_pow]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, lineCount_sq_sum]

theorem singletonPairWeights_chiSquare :
    uniformChiSquare (singletonPairWeights V) = ((Fintype.card V : ℝ) - 1) / 3 := by
  rw [uniformChiSquare_eq_secondMoment _ (singletonPairWeights_isProbability V),
    singletonPairWeights_secondMoment]
  simp only [Fintype.card_prod, Nat.cast_mul]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hn]
  ring

/-- Exact finite divergence of the padded slope law. -/
theorem paddedSlope_chiSquare (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (k : ℕ) :
    uniformChiSquare (independentWeights (mixture β (singletonPairWeights V)) k) =
      (1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1 := by
  rw [uniformChiSquare_independent _
    (mixture_isProbability _ (singletonPairWeights_isProbability V) hβ hβ'),
    uniformChiSquare_mixture, singletonPairWeights_chiSquare]
  exact congrArg (fun t : ℝ => (1 + t) ^ k - 1) (by ring)

theorem paddedSlope_totalVariation (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (k : ℕ) :
    totalVariation (independentWeights (mixture β (singletonPairWeights V)) k)
      (uniformWeights (Fin k → V × V)) ≤
        Real.sqrt ((1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1) / 2 := by
  simpa only [paddedSlope_chiSquare V β hβ hβ' k] using
    totalVariation_le_half_sqrt (independentWeights (mixture β (singletonPairWeights V)) k)

theorem paddedSlope_totalVariation_small (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (k : ℕ)
    (hk : (k : ℝ) * (β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ≤ 1 / 2) :
    totalVariation (independentWeights (mixture β (singletonPairWeights V)) k)
      (uniformWeights (Fin k → V × V)) ≤
        Real.sqrt (2 * (k : ℝ) * (β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3)) / 2 := by
  have hn : (1 : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card V))
  refine (paddedSlope_totalVariation V β hβ hβ' k).trans ?_
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact pow_sub_one_le_twice _ (by positivity) _ hk

theorem cubeSlope_totalVariation (m : ℕ) (hm : 0 < m)
    (hsize : 2 * ((Fintype.card V : ℝ) - 1) / 3 ≤ m) :
    totalVariation
      (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
      (uniformWeights (Fin (m ^ 3) → V × V)) ≤
        Real.sqrt (2 * ((Fintype.card V : ℝ) - 1) / (3 * m)) / 2 := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hbeta : (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hmpos)).2
    nlinarith
  have hproduct : ((m ^ 3 : ℕ) : ℝ) *
      ((1 / (m : ℝ) ^ 2) ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) =
        ((Fintype.card V : ℝ) - 1) / (3 * m) := by
    push_cast
    field_simp [hmpos.ne']

  have hsmall : ((m ^ 3 : ℕ) : ℝ) *
      ((1 / (m : ℝ) ^ 2) ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ≤ 1 / 2 := by
    rw [hproduct]
    apply (div_le_iff₀ (mul_pos (by norm_num) hmpos)).2
    linarith
  have h := paddedSlope_totalVariation_small V (1 / (m : ℝ) ^ 2)
    (by positivity) hbeta (m ^ 3) hsmall
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  calc
    2 * ((Fintype.card V : ℝ) - 1) / (3 * m) =
        2 * (((Fintype.card V : ℝ) - 1) / (3 * m)) := by ring
    _ = _ := by rw [← hproduct]; ring

/-- Arbitrarily many expected singleton coordinates coexist with arbitrarily
small variation error: taking `k=m³` and `beta=m⁻²` leaves `k*beta=m`.
The bound involves only the fixed alphabet and requested error. -/
theorem exists_cubeSlope_totalVariation_le (η : ℝ) (hη : 0 < η) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ η := by
  obtain ⟨m, hm⟩ := exists_nat_ge
    (max (max (1 : ℝ) N)
      (max (2 * ((Fintype.card V : ℝ) - 1) / 3)
        (((Fintype.card V : ℝ) - 1) / (6 * η ^ 2))))
  have hlow : max (1 : ℝ) N ≤ m := (le_max_left _ _).trans hm
  have hmone : (1 : ℝ) ≤ m := (le_max_left _ _).trans hlow
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) hmone
  have hN : (N : ℝ) ≤ m := (le_max_right _ _).trans hlow
  have hhigh : max (2 * ((Fintype.card V : ℝ) - 1) / 3)
      (((Fintype.card V : ℝ) - 1) / (6 * η ^ 2)) ≤ m :=
    (le_max_right _ _).trans hm
  have hsize := (le_max_left _ _).trans hhigh
  have hrate := (le_max_right _ _).trans hhigh
  have hrate' : (Fintype.card V : ℝ) - 1 ≤ (m : ℝ) * (6 * η ^ 2) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * η ^ 2)).mp hrate
  refine ⟨m, by exact_mod_cast hN, Nat.cast_pos.mp hmpos, ?_⟩
  refine (cubeSlope_totalVariation V m (Nat.cast_pos.mp hmpos) hsize).trans ?_
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply (Real.sqrt_le_left (by positivity : 0 ≤ η * 2)).2
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * m)).2
  nlinarith

end Singleton

end
end MaxCutGames.Decoder.SparseLaw

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CanonicalAddress
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct canonical-body addresses. The fixed list of canonical words is
interpreted in big-endian order, matching forward Horner steps `B*acc+digit`.
Unused addresses represent isolated vertices. These are semantic encoding and
polynomial-size results, not an assumed machine implementation. -/

/-! Finite noise tables for the executable outer reduction. Positions, including
positions containing equal vectors, remain distinct sample outcomes. -/

namespace MaxCutGames.Integration.NoiseTables

open BinaryLinear MaxCutGames.Reduction.ActualSource

variable {s d : Nat}

namespace Table

theorem noise_positionEquiv (g : SplitGadget s d) (en : NoiseEnumeration g)
    (i : Fin (ofEnumeration g en).vectors.length) :
    ((ofEnumeration g en).gadget g.f g.equivariant).noise i =
      g.noise (positionEquiv g en i) := by
  change (en.indices.map g.noise)[i.val] = g.noise en.indices[i.val]
  exact List.getElem_map _

theorem stabilityError_ofEnumeration (g : SplitGadget s d) (en : NoiseEnumeration g) :
    ((ofEnumeration g en).gadget g.f g.equivariant).stabilityError =
      g.stabilityError := by
  apply Fintype.expect_equiv
    ((Equiv.refl (Ambient s d)).prodCongr (positionEquiv g en))
  intro x
  change (if g.f (x.1 + _) = g.f x.1 then (0 : ℚ) else 1) = _
  rw [noise_positionEquiv]
  rfl

theorem kernelProbability_ofEnumeration (g : SplitGadget s d)
    (en : NoiseEnumeration g) {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    SplitGadget.kernelProbability ((ofEnumeration g en).gadget g.f g.equivariant) S =
      SplitGadget.kernelProbability g S := by
  classical
  apply Fintype.expect_equiv (positionEquiv g en)
  intro i
  rw [noise_positionEquiv]

end Table
end MaxCutGames.Integration.NoiseTables

/-! Injective vertex addresses may leave unused output vertices. The actual
instance is obtained by mapping endpoints in the original constraint list;
constraint order, multiplicity, and permutation tables are retained exactly. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TableKeysAddressGame
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Direct addresses for the v2 single-orbit matrix game. There is one canonical
body address space, with no side bit and no extra right-endpoint offset.
Unused addresses are isolated. Runtime construction uses canonical words and
radix arithmetic, not deduplication or inverse vertex enumeration.
-/

/-! Transport the matrix-test bound to the actual direct-address edge list.
Every address labeling restricts to a semantic orbit labeling, with exactly
the same satisfied fraction and the same occurrence multiplicities. -/

namespace MaxCutGames.Decoder.MatrixGap

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Foundations.Target
open MaxCutGames.Integration
open ActualSource

noncomputable section

/-- Soundness is measured on the generated direct-address instance. Unused
addresses and reindexing introduce no additional labeling advantage. -/
theorem address_value_le_of_semantic_acceptance (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (h : ∀ labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s),
      TableKeysGame.acceptanceProbability S k (T.gadget f hf) labeling ≤ (99 : ℚ) / 100) :
    InstanceValue.value (TableKeysAddressGame.tableOutput S k T) ≤ (99 : ℝ) / 100 := by
  rw [TableKeysAddressGame.tableOutput_eq_with_witness S k T f hf]
  apply (InstanceValue.forall_rate_le_iff _ (by positivity) _).mp
  intro labeling
  change (Fin (TableKeysAddressGame.vertexCount S k s d) → Fin (2 ^ s)) at labeling
  have hrate : GapSemantics.satisfactionRate
      (TableKeysAddressGame.outputInstance S k (T.gadget f hf)
        (TableReduction.tableEnumeration T f hf)) labeling ≤ (99 : ℚ) / 100 := by
    rw [address_rate_eq_semantic_acceptance S k (T.gadget f hf)
      (TableReduction.tableEnumeration T f hf) labeling]
    exact h _
  have hreal := (Rat.cast_le (K := ℝ)
    (p := GapSemantics.satisfactionRate
      (TableKeysAddressGame.outputInstance S k (T.gadget f hf)
        (TableReduction.tableEnumeration T f hf)) labeling)
    (q := (99 : ℚ) / 100)).2 hrate
  simpa [GapSemantics.satisfactionRate] using hreal

end

end MaxCutGames.Decoder.MatrixGap

/-!
Completeness on the actual single-orbit address output. An honest semantic
labeling is extended over unused addresses, with its satisfied fraction
unchanged. The two rational error bounds need no packaged error parameter.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SurrogateFibers
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The surrogate perturbation fixes the complementary table exactly. Splitting
the actual uniform matrix law therefore expresses surrogate acceptance as the
mean of the uniform shortcode tests on the `(U,T)` fibers, including zero
perturbation factors. This supplies the sampling identification needed before
applying the inverse theorem to the many useful fibers.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Reduction.ActualSource
open MaxCutGames.Fourier.MatrixNoise

namespace MaxCutGames.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

theorem eta_pos (r : Nat) : 0 < eta r := by unfold eta; positivity

end MaxCutGames.Decoder.ActualSpectral
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualGoodRows
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.ActualGoodRows

open Integration.BinaryLinear Reduction ActualSource
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

theorem goodRowMass_pos (rstar s r : ℕ) : 0 < goodRowMass rstar s r := by
  unfold goodRowMass
  have h := ActualSpectral.eta_pos rstar
  positivity

end
end MaxCutGames.Decoder.ActualGoodRows

namespace MaxCutGames.Decoder.ConstantSelection

open MaxCutGames.Foundations.Information
open SparseLaw

noncomputable section

theorem visibleMass_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < visibleMass α g₀ ell r := by
  unfold visibleMass
  positivity

theorem conditionalMass_pos {α : ℝ} (hα : 0 < α) (ell r : ℕ) :
    0 < conditionalMass α ell r := by
  unfold conditionalMass
  positivity

theorem decodingMass_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < decodingMass α g₀ ell r :=
  mul_pos (visibleMass_pos hα hg₀ ell r) (conditionalMass_pos hα ell r)

theorem variationBudget_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < variationBudget α g₀ ell r := by
  exact div_pos (visibleMass_pos hα hg₀ ell r) (by positivity)

/-- Exponential clean-mask decay persists after increasing the cube root. -/
theorem cube_exponential_antitone {m n : ℕ} (hmn : m ≤ n)
    {N : ℝ} (hN : 0 < N) :
    Real.exp (-(n : ℝ) / (3600 * N)) ≤
      Real.exp (-(m : ℝ) / (3600 * N)) := by
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact neg_le_neg (by exact_mod_cast hmn)

/-- One tuple length meets the sparse-law and repetition requirements, while
exceeding any independent inverse/erasure dimension threshold. -/
theorem exists_simultaneous_cube (V : Type*) [Fintype V] [Zero V] [DecidableEq V]
    {N ε γ : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hγ : 0 < γ) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ ε ∧
      (1 - ((1 / (m : ℝ) ^ 2) / N) / 3600) ^ (m ^ 3) < γ := by
  obtain ⟨m₀, hm₀, hexp⟩ := Clean.exists_cube_exponential_lt
    (show 0 < N by linarith) hγ
  obtain ⟨m, hlarge, hm, htv⟩ := exists_cubeSlope_totalVariation_le V ε hε
    (max lower m₀)
  have hbase : m₀ ≤ m := (le_max_right _ _).trans hlarge
  refine ⟨m, (le_max_left _ _).trans hlarge, hm, htv, ?_⟩
  have hdecay := (Clean.cube_mask_rate_le_exp (Nat.succ_le_iff.mpr hm) hN).trans
    (cube_exponential_antitone hbase (by linarith : 0 < N))
  have hbeta : (1 / (m : ℝ)) ^ 2 = 1 / (m : ℝ) ^ 2 := by ring
  rw [hbeta] at hdecay
  exact hdecay.trans_lt hexp

/-- All scalar requirements for the final decoding contradiction can be met
after the fixed alphabet and inverse parameters have been chosen. -/
theorem exists_matrix_cube (V : Type*) [Fintype V] [Zero V] [DecidableEq V]
    {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r dimW lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ variationBudget α g₀ ell r ∧
      (1 - ((1 / (m : ℝ) ^ 2) / (2 : ℝ) ^ (dimW + r)) / 3600) ^ (m ^ 3) <
        decodingMass α g₀ ell r := by
  exact exists_simultaneous_cube V (one_le_pow₀ (by norm_num))
    (variationBudget_pos hα hg₀ ell r) (decodingMass_pos hα hg₀ ell r) lower

end
end MaxCutGames.Decoder.ConstantSelection

namespace MaxCutGames.Decoder.MatrixGapChoice

open Integration.BinaryLinear Reduction ActualSource
open Inverse.Shortcode (Mat HasAffineSlice InversePrinciple equalityAcceptance)

noncomputable section

/-- After all fixed dimensions are known, the cube simultaneously exceeds the
inverse threshold, reduces full-table variation, and beats the decoder mass. -/
theorem exists_cube {rstar : ℕ} (P : InverseParameters rstar) (d : ℕ) :
    ∃ m : ℕ, 0 < m ∧ P.tupleThreshold ≤ m ^ 3 ∧
      0 ≤ 1 / (m : ℝ) ^ 2 ∧ 1 / (m : ℝ) ^ 2 ≤ 1 ∧
      Foundations.Information.totalVariation
        (SparseLaw.independentWeights
          (SparseLaw.mixture (1 / (m : ℝ) ^ 2)
            (SparseLaw.singletonPairWeights (Ambient P.s d))) (m ^ 3))
        (SparseLaw.uniformWeights (Fin (m ^ 3) → Ambient P.s d × Ambient P.s d)) ≤
          ConstantSelection.variationBudget P.α (ActualGoodRows.goodRowMass rstar P.s P.r) P.s P.r ∧
      (1 - ((1 / (m : ℝ) ^ 2) / (2 : ℝ) ^ (d + P.r)) / 3600) ^ (m ^ 3) <
        ConstantSelection.decodingMass P.α (ActualGoodRows.goodRowMass rstar P.s P.r) P.s P.r := by
  obtain ⟨m, hlarge, hm, htv, hrate⟩ := ConstantSelection.exists_matrix_cube (Ambient P.s d)
    P.positive (ActualGoodRows.goodRowMass_pos rstar P.s P.r) P.s P.r d P.tupleThreshold
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hmsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hmreal
  refine ⟨m, hm, hlarge.trans (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) m),
    by positivity, ?_, htv, hrate⟩
  exact (div_le_one (by positivity)).mpr hmsq

end
end MaxCutGames.Decoder.MatrixGapChoice

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_BaseDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

/-- Noise pushforward preserves the change event pointwise, before averaging. -/
theorem change_iff (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u a : P) :
    (output R lam C hC (projection R lam u + projection R lam a) ≠
      output R lam C hC (projection R lam u)) ↔ C (u + a) ≠ C u := by
  rw [← map_add, output_projection, output_projection]

theorem fiberMap_bijective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (a : P) :
    Function.Bijective (fiberMap R lam a) := by
  constructor
  · intro h k he
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val he)
  · intro u
    have hm : u.val - a ∈ shiftKernel R lam :=
      (Submodule.Quotient.eq _).mp u.property
    refine ⟨⟨u.val - a, hm⟩, Subtype.ext ?_⟩
    change a + (u.val - a) = u.val
    rw [add_comm, sub_add_cancel]

/-- Every fiber has the same cardinality, justifying uniform-input pushforward. -/
theorem fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : Space R lam) :
    Nat.card {u : P // projection R lam u = x} = Nat.card (shiftKernel R lam) := by
  obtain ⟨a, rfl⟩ := projection_surjective R lam x
  exact (Nat.card_congr (Equiv.ofBijective _ (fiberMap_bijective R lam a))).symm

end MaxCutGames.Gadget.Quotient

namespace MaxCutGames.Gadget.StageQuotient

universe u v

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B]

theorem noise_change_iff (s : Stage k B) (u : s.Input) (t : s.Noise) :
    (output s (projection s u + noise s t) ≠ output s (projection s u)) ↔
      s.output (u + s.noise t) ≠ s.output u :=
  Quotient.change_iff (shifts s) (logical s) s.output (equivariant s) u (s.noise t)

end MaxCutGames.Gadget.StageQuotient

/-!
# From full character lifts to linear-map detection

If a target linear map is injective on the logical alphabet, a linear left
inverse of that restriction turns all logical characters into a full lift.
Detection by this lift implies that the target map does not annihilate the
noise. The left inverse is proved to exist by the vector-space splitting
theorem; it is not an additional premise.
-/

/-!
# Detection survives the logical-kernel quotient

A full family of logical characters on the quotient pulls back to a full
lift on the original stage. Its detection event is the same pointwise.
Combining this with the proved left-inverse construction gives detection of
every linear map injective on the quotient's logical subspace.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_StageNoiseRecurrence
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact finite-stage nonlinear noise law

This packages the one-level recurrence for the actual recursive `Stage`, solves
it at every height, and proves that the ambient-kernel quotient preserves it.
The averaged block kernel remains an explicit argument for later instantiation
with the concrete quadratic family.
-/

namespace MaxCutGames.Gadget.StageNoiseRecurrence

open scoped BigOperators

theorem average_eq_expect {A : Type*} [Fintype A] (f : A → ℚ) :
    average f = 𝔼 a, f a := by
  have he : Fintype.ofFinite A = ‹Fintype A› := Subsingleton.elim _ _
  unfold average
  rw [he]

universe u v

variable {k : Type u} {B : Type v} [CommRing k] [AddCommGroup B] [Module k B]

theorem error_eq_expect [DecidableEq B] (s : Stage k B) [Fintype s.Input] [Fintype s.Noise] :
    error s = 𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0 := by
  classical
  simp only [error, average_eq_expect]
  apply Finset.expect_congr rfl
  intro n _
  apply Finset.expect_congr rfl
  intro u _
  split_ifs <;> rfl

end MaxCutGames.Gadget.StageNoiseRecurrence

/-!
The spanning clause of v2 Lemma `latent-block`.  Three coordinate lines
already suffice.  Horizontal coordinate vectors lie in their own block;
vertical coordinate vectors lie in either of the other two blocks.
-/

/-! Surjectivity of the actual all-lines/all-orientations parent aggregate. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FiniteFieldChoice
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A concrete mathematical family of finite binary fields of unbounded size.
The extension degree is chosen from numerical thresholds alone, before the
logical output dimension of the latent gadget is selected.
-/

/-!
# One field for every rank up to a fixed threshold

The extension degree is chosen using only the rank threshold and the requested
genericity error.  In particular it is fixed before the logical dimension in
the later enlargement construction.  A generic top-rank space exists in the
same field.
-/

/-!
# The finite base gadget with arbitrarily small nonlinear change

The harmonic rank and genericity error are chosen first. A single finite field
then supplies all required genericity statements, and the actual recursion is
run to its harmonic depth. The kernel quotient injects the logical alphabet.
Every linear map injective there detects at least one quarter of the noise.
-/

namespace MaxCutGames.Gadget.Enlargement

open scoped BigOperators Classical

noncomputable section

/-- A union bound without independence assumptions. -/
theorem probability_exists_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : I → Ω → Prop) :
    probability (fun x => ∃ i, p i x) ≤ ∑ i, probability (p i) := by
  classical
  have heq : (Finset.univ.filter fun x => ∃ i, p i x) =
      Finset.univ.biUnion (fun i => Finset.univ.filter (p i)) := by
    ext x
    simp
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [heq, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset I))
    (t := fun i => Finset.univ.filter (p i)))

/-- Equal-size fibers determine the exact probability of every target event. -/
theorem probability_preimage_of_fibers {Ω T : Type*} [Fintype Ω] [Fintype T]
    [Nonempty Ω] [Nonempty T] (f : Ω → T)
    (hf : ∀ x y : T, Nat.card {a : Ω // f a = x} = Nat.card {a : Ω // f a = y})
    (p : T → Prop) : probability (fun a => p (f a)) = probability p := by
  classical
  let t₀ : T := Classical.choice inferInstance
  let c := (Finset.univ.filter fun a => f a = t₀).card
  have hfc (x : T) : (Finset.univ.filter fun a => f a = x).card = c := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hf x t₀
  have hΩ : Fintype.card Ω = Fintype.card T * c := by
    calc
      Fintype.card Ω = ∑ t : T, (Finset.univ.filter fun a => f a = t).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = Fintype.card T * c := by simp_rw [hfc]; simp
  have hp : (Finset.univ.filter fun a => p (f a)).card =
      (Finset.univ.filter p).card * c := by
    calc
      _ = ∑ t ∈ Finset.univ.filter p,
          (Finset.univ.filter fun a => f a = t).card := by
        symm
        simpa using Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset Ω) (Finset.univ.filter p) f
      _ = _ := by simp_rw [hfc]; simp
  have hc : (c : ℚ) ≠ 0 := by
    have : c ≠ 0 := by
      intro hc
      have := Fintype.card_pos (α := Ω)
      simp [hc] at hΩ
    exact_mod_cast this
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hp, hΩ]
  push_cast
  exact mul_div_mul_right _ _ hc

/-- Updating only one copy changes the output by its relabeled base-output
difference. This identity retains all summands and does not assume they are
independent. -/
theorem enlargedOutput_update {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) (L : LinearInjection F B K) (y : V) :
    enlargedOutput C (Function.update x L y) =
      enlargedOutput C x + L.1 (C y - C (x L)) := by
  classical
  have hfun : (fun J => J.1 (C (Function.update x L y J))) =
      Function.update (fun J : LinearInjection F B K => J.1 (C (x J))) L (L.1 (C y)) := by
    funext J
    by_cases h : J = L
    · subst J
      simp
    · simp [h]
  unfold enlargedOutput
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ L)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ L)]
  rw [map_sub]
  abel

/-- Injectivity of the selected relabeling makes the enlargement output
change exactly when that copy's base output changes. -/
theorem enlargedOutput_update_ne_iff {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) (L : LinearInjection F B K) (y : V) :
    enlargedOutput C (Function.update x L y) ≠ enlargedOutput C x ↔ C y ≠ C (x L) := by
  rw [enlargedOutput_update, ne_eq, add_eq_left, map_eq_zero_iff _ L.2,
    sub_eq_zero, ne_eq]

theorem injection_eval_uniform {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K]
    [Fintype K] [Fintype (LinearInjection F B K)]
    [Nonempty (LinearInjection F B K)] (b : B) (hb : b ≠ 0)
    (p : {x : K // x ≠ 0} → Prop) :
    probability (fun L : LinearInjection F B K =>
      p ⟨L.1 b, injection_eval_ne_zero L hb⟩) = probability p := by
  classical
  let : Nonempty {x : K // x ≠ 0} :=
    ⟨⟨(Classical.choice inferInstance : LinearInjection F B K).1 b,
      injection_eval_ne_zero _ hb⟩⟩
  let f : LinearInjection F B K → {x : K // x ≠ 0} :=
    fun L => ⟨L.1 b, injection_eval_ne_zero L hb⟩
  apply probability_preimage_of_fibers f
  intro x y
  obtain ⟨e, he⟩ := exists_equiv_map_nonzero (F := F) x.1 y.1 x.2 y.2
  let ee : {L : LinearInjection F B K // f L = x} ≃
      {L : LinearInjection F B K // f L = y} :=
    (postcompose e).subtypeEquiv (fun L => by
      change f L = x ↔ f (postcompose e L) = y
      constructor
      · intro h
        apply Subtype.ext
        change e (L.1 b) = y.1
        rw [show L.1 b = x.1 from congrArg Subtype.val h, he]
      · intro h
        apply Subtype.ext
        apply e.injective
        exact (congrArg Subtype.val h).trans he.symm)
  exact Nat.card_congr ee

/-- Failure of the pullback family to span the full dual has a nonzero vector
witness in its common annihilator. -/
theorem pullback_ne_top_iff {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [FiniteDimensional F B] [AddCommGroup K] [Module F K]
    (L : B →ₗ[F] K) (S : Submodule F (Module.Dual F K)) :
    S.map L.dualMap ≠ ⊤ ↔ ∃ b : B, b ≠ 0 ∧ L b ∈ S.dualCoannihilator := by
  let W := S.map L.dualMap
  have hann : W.dualCoannihilator = S.dualCoannihilator.comap L := by
    ext b
    simp only [Submodule.mem_dualCoannihilator, Submodule.mem_comap,
      ]
    constructor
    · intro h z hz
      exact h (z.comp L) ⟨z, hz, rfl⟩
    · intro h z ⟨w, hw, hwz⟩
      subst z
      exact h w hw
  constructor
  · intro hW
    have hn : W.dualCoannihilator ≠ ⊥ := by
      intro hz
      have hh := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
      rw [hz, Submodule.dualAnnihilator_bot] at hh
      exact hW hh.symm
    obtain ⟨b, hb, hb0⟩ := (Submodule.ne_bot_iff _).1 hn
    exact ⟨b, hb0, by simpa [hann] using hb⟩
  · rintro ⟨b, hb0, hb⟩ htop
    have hz : b ∈ W.dualCoannihilator := by simpa [hann] using hb
    change b ∈ (S.map L.dualMap).dualCoannihilator at hz
    rw [htop] at hz
    have hall : ∀ z : Module.Dual F B, z b = 0 := by
      simpa only [Submodule.mem_dualCoannihilator, Submodule.mem_top,
        forall_true_left] using hz
    obtain ⟨z, hz'⟩ := Module.Projective.exists_dual_ne_zero F hb0
    exact hz' (hall z)

/-- The nonzero part of a codimension-`r` subspace has density at most `2⁻ʳ`
among all nonzero ambient vectors. The dimensions are written additively to
avoid truncated subtraction. -/
theorem nonzero_density_le (d r : ℕ) (h : 0 < d + r) :
    ((2 : ℚ) ^ d - 1) / ((2 : ℚ) ^ (d + r) - 1) ≤ 1 / (2 : ℚ) ^ r := by
  have hpow : 1 < (2 : ℚ) ^ (d + r) := one_lt_pow₀ (by norm_num) (by omega)
  have hr : (1 : ℚ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  rw [pow_add]
  nlinarith

/-- Cardinality of all nonzero vectors in a finite binary vector space. -/
theorem card_nonzero_binary (K : Type*) [AddCommGroup K] [Module (ZMod 2) K]
    [Fintype K] :
    Nat.card {x : K // x ≠ 0} = 2 ^ Module.finrank (ZMod 2) K - 1 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : K => x = 0), Fintype.card_subtype_eq]
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- Exact density of the nonzero part of a binary subspace. -/
theorem probability_nonzero_subspace (K : Type*) [AddCommGroup K]
    [Module (ZMod 2) K] [Fintype K] (W : Submodule (ZMod 2) K) :
    probability (fun x : {x : K // x ≠ 0} => x.1 ∈ W) =
      ((2 : ℚ) ^ Module.finrank (ZMod 2) W - 1) /
        ((2 : ℚ) ^ Module.finrank (ZMod 2) K - 1) := by
  classical
  let : Fintype W := Fintype.ofFinite _
  let e : {x : {x : K // x ≠ 0} // x.1 ∈ W} ≃ {x : W // x ≠ 0} :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, by
        intro h
        exact x.1.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨⟨x.1.1, by
        intro h
        apply x.2
        exact Subtype.ext h⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold probability
  rw [Nat.card_congr e,
    card_nonzero_binary W, card_nonzero_binary K]
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)),
    Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
  push_cast ; rfl

/-- The annihilator dimension identity gives precisely the exponent needed
by the enlargement, without any loss depending on the ambient dimension. -/
theorem probability_annihilator_le (K : Type*) [AddCommGroup K]
    [Module (ZMod 2) K] [Fintype K] [FiniteDimensional (ZMod 2) K]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hK : 0 < Module.finrank (ZMod 2) K) :
    probability (fun x : {x : K // x ≠ 0} => x.1 ∈ S.dualCoannihilator) ≤
      1 / (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
  rw [probability_nonzero_subspace]
  have hr := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  rw [← hr, add_comm (Module.finrank (ZMod 2) S)]
  apply nonzero_density_le
  omega

/-- The threshold `b + 2` is chosen before the ambient dimension. -/
theorem union_bound_le_quarter (b r : ℕ) (hr : b + 2 ≤ r) :
    ((2 : ℚ) ^ b - 1) / (2 : ℚ) ^ r ≤ 1 / 4 := by
  have hpow : (2 : ℚ) ^ (b + 2) ≤ (2 : ℚ) ^ r :=
    pow_le_pow_right₀ (by norm_num) hr
  rw [pow_add] at hpow
  norm_num at hpow
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ r)).2
  nlinarith [show (0 : ℚ) ≤ 2 ^ b by positivity]

/-- The enlargement's uniform-injection union bound, including its actual
linear-algebraic bad event. -/
theorem pullback_failure_probability_le {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hK : 0 < Module.finrank (ZMod 2) K) :
    probability (fun L : LinearInjection (ZMod 2) B K => S.map L.1.dualMap ≠ ⊤) ≤
      ((2 : ℚ) ^ Module.finrank (ZMod 2) B - 1) /
        (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
  classical
  calc
    _ = probability (fun L : LinearInjection (ZMod 2) B K =>
        ∃ b : {b : B // b ≠ 0}, L.1 b.1 ∈ S.dualCoannihilator) := by
      congr 1
      funext L
      apply propext
      rw [pullback_ne_top_iff]
      exact ⟨fun ⟨b, hb, h⟩ => ⟨⟨b, hb⟩, h⟩,
        fun ⟨b, h⟩ => ⟨b.1, b.2, h⟩⟩
    _ ≤ ∑ b : {b : B // b ≠ 0}, probability
        (fun L : LinearInjection (ZMod 2) B K => L.1 b.1 ∈ S.dualCoannihilator) :=
      probability_exists_le_sum _
    _ ≤ ∑ _b : {b : B // b ≠ 0},
        1 / (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
      apply Finset.sum_le_sum
      intro b _
      rw [injection_eval_uniform b.1 b.2
        (fun x : {x : K // x ≠ 0} => x.1 ∈ S.dualCoannihilator)]
      exact probability_annihilator_le K S hK
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, card_nonzero_binary B,
        Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
      push_cast
      ring

/-- At least three quarters of the injection copies restrict onto the full
base dual when the restriction rank is at least `dim B + 2`. -/
theorem pullback_failure_probability_le_quarter {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2) S) :
    probability (fun L : LinearInjection (ZMod 2) B K => S.map L.1.dualMap ≠ ⊤) ≤
      1 / 4 := by
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  exact (pullback_failure_probability_le S (by omega)).trans
    (union_bound_le_quarter _ _ hr)

theorem probability_not {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → Prop) : probability (fun x => ¬ p x) = 1 - probability p := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω)) p
  have h' : ((Finset.univ.filter p).card : ℚ) +
      ((Finset.univ.filter fun x => ¬p x).card : ℚ) = Fintype.card Ω := by
    exact_mod_cast h
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply (eq_sub_iff_add_eq).2
  rw [← add_div, add_comm, h', div_self hcard]

/-- Averaging a nonnegative detection rate which is at least one quarter on
each good copy. This is the last finite probability step of enlargement. -/
theorem average_detection_lower_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (bad : Ω → Prop) (detected : Ω → ℚ)
    (hnonneg : ∀ x, 0 ≤ detected x)
    (hgood : ∀ x, ¬bad x → 1 / 4 ≤ detected x) :
    (1 - probability bad) * (1 / 4) ≤
      (∑ x, detected x) / (Fintype.card Ω : ℚ) := by
  classical
  have hs : ∑ x : Ω, (if bad x then (0 : ℚ) else 1 / 4) ≤ ∑ x, detected x := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : bad x
    · simpa [hx] using hnonneg x
    · simpa [hx] using hgood x hx
  have heq : ∑ x : Ω, (if bad x then (0 : ℚ) else 1 / 4) =
      ((Finset.univ.filter fun x => ¬bad x).card : ℚ) * (1 / 4) := by
    rw [Finset.sum_ite]
    simp
  rw [heq] at hs
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Fintype.card Ω) :
    (0 : ℚ) ≤ Fintype.card Ω)
  rw [← probability_not]
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [div_mul_eq_mul_div] using hd

/-- The enlargement retains `3/16` detection, and hence the advertised `1/8`.
The hypotheses are the bad-copy probability and the average lower bound from
the base gadget; they make no independence assertion. -/
theorem detection_constants {bad detected : ℚ} (hbad : bad ≤ 1 / 4)
    (hdetected : (1 - bad) * (1 / 4) ≤ detected) :
    3 / 16 ≤ detected ∧ 1 / 8 ≤ detected := by
  constructor <;> linarith

theorem enlarged_detection {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2) S)
    (detected : LinearInjection (ZMod 2) B K → ℚ)
    (hnonneg : ∀ L, 0 ≤ detected L)
    (hbase : ∀ L, S.map L.1.dualMap = ⊤ → 1 / 4 ≤ detected L) :
    3 / 16 ≤ (∑ L, detected L) / (Fintype.card (LinearInjection (ZMod 2) B K) : ℚ) ∧
    1 / 8 ≤ (∑ L, detected L) / (Fintype.card (LinearInjection (ZMod 2) B K) : ℚ) := by
  apply detection_constants (pullback_failure_probability_le_quarter S hr)
  apply average_detection_lower_bound _ detected hnonneg
  intro L hL
  exact hbase L (not_not.mp hL)

end

end MaxCutGames.Gadget.Enlargement

noncomputable section

namespace MaxCutGames.Gadget.EnlargementConstruction

open scoped BigOperators Classical
open Enlargement

theorem probability_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (p : Ξ → Prop) :
    probability (fun x : Ω => p (e x)) = probability p := by
  classical
  unfold probability
  rw [Nat.card_congr (Equiv.subtypeEquivOfSubtype (p := p) e), Nat.card_congr e]

theorem probability_eq_sum_indicator {Ω : Type*} [Fintype Ω]
    (p : Ω → Prop) :
    probability p =
      (∑ x : Ω, if p x then (1 : ℚ) else 0) / (Fintype.card Ω : ℚ) := by
  classical
  simp only [probability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- Uniform probability on a product is the average of the second-coordinate
probabilities. No nonemptiness hypotheses are needed for this identity. -/
theorem probability_prod_average {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Ξ → Prop) :
    probability (fun z : Ω × Ξ => p z.1 z.2) =
      (∑ x : Ω, probability (p x)) / (Fintype.card Ω : ℚ) := by
  classical
  simp_rw [probability_eq_sum_indicator]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.sum_div, div_div]
  congr 1
  exact mul_comm _ _

/-- The same product identity, averaging in the other order. -/
theorem probability_prod_average_right {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Ξ → Prop) :
    probability (fun z : Ω × Ξ => p z.1 z.2) =
      (∑ y : Ξ, probability (fun x : Ω => p x y)) /
        (Fintype.card Ξ : ℚ) := by
  classical
  simp_rw [probability_eq_sum_indicator]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type_right,
    ← Finset.sum_div, div_div]

/-- Every coordinate of a uniformly chosen function has the uniform marginal.
Pointwise transpositions biject the evaluation fibers. -/
theorem probability_coordinate {I X : Type*} [Fintype I] [Fintype X]
    (i : I) (p : X → Prop) :
    probability (fun g : I → X => p (g i)) = probability p := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let : IsEmpty X := hX
      let : IsEmpty (I → X) := ⟨fun g => isEmptyElim (g i)⟩
      simp [probability]
  | inr hX =>
      let : Nonempty X := hX
      let : Nonempty (I → X) := ⟨fun _ => Classical.choice hX⟩
      apply probability_preimage_of_fibers (fun g : I → X => g i)
      intro x y
      let e : (I → X) ≃ (I → X) :=
        Equiv.piCongrRight (fun _ : I => Equiv.swap x y)
      let ee : {g : I → X // g i = x} ≃
          {g : I → X // g i = y} :=
        e.subtypeEquiv (fun g => by
          change g i = x ↔ Equiv.swap x y (g i) = y
          constructor
          · intro h
            rw [h, Equiv.swap_apply_left]
          · intro h
            apply (Equiv.swap x y).injective
            exact h.trans (Equiv.swap_apply_left x y).symm)
      exact Nat.card_congr ee

/-- Coordinate projection preserves the joint uniform law with an independent
finite noise sample. -/
theorem probability_coordinate_prod {I X N : Type*}
    [Fintype I] [Fintype X] [Fintype N] (i : I) (p : X → N → Prop) :
    probability (fun z : (I → X) × N => p (z.1 i) z.2) =
      probability (fun z : X × N => p z.1 z.2) := by
  rw [probability_prod_average_right (fun (g : I → X) n => p (g i) n),
    probability_prod_average_right p]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact probability_coordinate i (fun x => p x n)

/-- Grouping the same three uniform choices in another order. -/
theorem probability_prod_reorder {Ω I N : Type*}
    [Fintype Ω] [Fintype I] [Fintype N] (p : Ω → I → N → Prop) :
    probability (fun z : Ω × (I × N) => p z.1 z.2.1 z.2.2) =
      probability (fun z : I × (Ω × N) => p z.2.1 z.1 z.2.2) := by
  let e : (Ω × (I × N)) ≃ (I × (Ω × N)) :=
    { toFun := fun z => (z.2.1, z.1, z.2.2)
      invFun := fun z => (z.2.1, z.1, z.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact probability_equiv e (fun z => p z.2.1 z.1 z.2.2)

/-- If each conditional probability is the same, their uniform average is
that common value. -/
theorem probability_prod_eq_of_const {Ω Ξ : Type*}
    [Fintype Ω] [Fintype Ξ] [Nonempty Ω]
    (p : Ω → Ξ → Prop) (q : ℚ) (h : ∀ x, probability (p x) = q) :
    probability (fun z : Ω × Ξ => p z.1 z.2) = q := by
  rw [probability_prod_average]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ q hcard

/-- For a fixed selected injection, the enlargement's change event has exactly
the base input/noise probability. -/
theorem enlarged_single_copy_probability {F B K V N : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Fintype V] [Fintype N]
    [Fintype (LinearInjection F B K)]
    (C : V → B) (a : N → V) (L : LinearInjection F B K) :
    probability (fun z : (LinearInjection F B K → V) × N =>
      enlargedOutput C (Function.update z.1 L (z.1 L + a z.2)) ≠
        enlargedOutput C z.1) =
      probability (fun z : V × N => C (z.1 + a z.2) ≠ C z.1) := by
  calc
    _ = probability (fun z : (LinearInjection F B K → V) × N =>
        C (z.1 L + a z.2) ≠ C (z.1 L)) := by
      congr 1
      funext z
      exact propext (enlargedOutput_update_ne_iff C z.1 L (z.1 L + a z.2))
    _ = _ := probability_coordinate_prod L (fun x n => C (x + a n) ≠ C x)

/-- The same equality after selecting the injection uniformly as part of the
noise sample. Its sample space is exactly product-input × (copy × base-noise). -/
theorem enlarged_random_copy_probability {F B K V N : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Fintype V] [Fintype N]
    [Fintype (LinearInjection F B K)] [Nonempty (LinearInjection F B K)]
    (C : V → B) (a : N → V) :
    probability (fun z : (LinearInjection F B K → V) ×
        (LinearInjection F B K × N) =>
      enlargedOutput C
        (Function.update z.1 z.2.1 (z.1 z.2.1 + a z.2.2)) ≠
          enlargedOutput C z.1) =
      probability (fun z : V × N => C (z.1 + a z.2) ≠ C z.1) := by
  rw [probability_prod_reorder (fun x L n =>
    enlargedOutput C (Function.update x L (x L + a n)) ≠ enlargedOutput C x)]
  apply probability_prod_eq_of_const (fun L (z : (LinearInjection F B K → V) × N) =>
    enlargedOutput C (Function.update z.1 L (z.1 L + a z.2)) ≠ enlargedOutput C z.1)
  intro L
  exact enlarged_single_copy_probability C a L

universe u

variable {B K V N : Type u}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

private theorem update_canonical {A B : Type*} (d : DecidableEq A) (f : A → B) (a : A) (b : B) :
    @Function.update A (fun _ => B) d f a b =
      @Function.update A (fun _ => B) (Classical.typeDecidableEq A) f a b := by
  cases Subsingleton.elim d (Classical.typeDecidableEq A : DecidableEq A)
  rfl

private theorem probability_pointwise {A : Type*} (i j : Fintype A) (p q : A → Prop)
    (h : ∀ a, p a ↔ q a) : @probability A i p = @probability A j q := by
  unfold probability
  have he : p = q := funext (fun a => propext (h a))
  rw [he]

attribute [local instance] OAI.MaxCutGames.Gadget.EnlargementConstruction.instFintypeCopies
omit [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] [Module (ZMod 2) V] [Fintype V] in
theorem add_single_eq_update (x : Copies B K → V) (L : Copies B K) (a : V) :
    x + Pi.single L a = Function.update x L (x L + a) := by
  funext J
  by_cases h : J = L
  · subst J
    simp
  · simp [h]

/-- The quotient and injection preserve each individual nonlinear change
event exactly, before taking any finite averages. -/
theorem change_iff (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (x : Copies B K → V) (L : Copies B K) (n : N) :
    let s := productStage i hi C hC noise hdim b₀ hb₀
    StageQuotient.output s (StageQuotient.projection s x + StageQuotient.noise s (L, n)) ≠
        StageQuotient.output s (StageQuotient.projection s x) ↔
      C (x L + noise n) ≠ C (x L) := by
  dsimp only
  refine (StageQuotient.noise_change_iff
    (productStage i hi C hC noise hdim b₀ hb₀) x (L, n)).trans ?_
  change enlargedOutput C (x + Pi.single L (noise n)) ≠ enlargedOutput C x ↔ _
  rw [add_single_eq_update]
  have h := enlargedOutput_update_ne_iff C x L (x L + noise n)
  simp only [update_canonical] at h ⊢
  exact h

theorem copyObserver_shift {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (L : Copies B K) :
    (copyObserver i hi C hC noise hdim b₀ hb₀ T L).comp i =
      (T.comp (StageQuotient.shift (productStage i hi C hC noise hdim b₀ hb₀))).comp L.1 := by
  ext b
  let s := productStage i hi C hC noise hdim b₀ hb₀
  have he : s.embed (Pi.single L b) = Pi.single L (i b) := by
    funext J
    change i ((Pi.single L b : Copies B K → B) J) =
      (Pi.single L (i b) : Copies B K → V) J
    by_cases h : J = L
    · subst J
      simp
    · simp [h]
  have hl : s.logical (Pi.single L b) = L.1 b := by
    change (∑ J : Copies B K, J.1 ((Pi.single L b : Copies B K → B) J)) = L.1 b
    simp [Pi.single_apply, apply_ite]
  have hh := congrArg T (StageQuotient.shift_logical s (Pi.single L b))
  rw [he, hl] at hh
  exact hh.symm

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] in
theorem dual_pullback_eq_top_iff {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (A : K →ₗ[ZMod 2] E) (L : B →ₗ[ZMod 2] K) :
    (LinearMap.range A.dualMap).map L.dualMap = ⊤ ↔ Function.Injective (A.comp L) := by
  rw [← LinearMap.range_comp, LinearMap.dualMap_comp_dualMap,
    LinearMap.range_eq_top, LinearMap.dualMap_surjective_iff]

/-- Average detection over the actual injection-indexed base copies. The
restriction threshold is the rank on the final embedded logical space. -/
theorem detection_average {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (hbase : ∀ U : V →ₗ[ZMod 2] E, Function.Injective (U.comp i) →
      1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0))
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (T.comp (StageQuotient.shift
        (productStage i hi C hC noise hdim b₀ hb₀))))) :
    1 / 8 ≤
      (∑ L : Copies B K, probability (fun n : N =>
        copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0)) /
          (Fintype.card (Copies B K) : ℚ) := by
  let : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  let A := T.comp (StageQuotient.shift (productStage i hi C hC noise hdim b₀ hb₀))
  apply (enlarged_detection (LinearMap.range A.dualMap)
    (by simpa only [LinearMap.finrank_range_dualMap_eq_finrank_range] using hr)
    (fun L => probability (fun n : N =>
      copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0))
    (fun _ => by unfold probability; positivity) ?_).2
  intro L hL
  apply hbase
  rw [copyObserver_shift]
  exact (dual_pullback_eq_top_iff A L.1).1 hL

omit [Fintype K] [FiniteDimensional (ZMod 2) K] in
/-- Passing uniform input through the actual quotient preserves its law. -/
theorem probability_projection (s : Stage (ZMod 2) K)
    [Fintype s.Input] [Fintype (StageQuotient.Space s)]
    (p : StageQuotient.Space s → Prop) :
    probability (fun x : s.Input => p (StageQuotient.projection s x)) = probability p := by
  apply probability_preimage_of_fibers (StageQuotient.projection s)
  intro x y
  have h := (Quotient.fiber_card (StageQuotient.shifts s) (StageQuotient.logical s) x).trans
    (Quotient.fiber_card (StageQuotient.shifts s) (StageQuotient.logical s) y).symm
  exact h

omit [Fintype K] [FiniteDimensional (ZMod 2) K] in
theorem probability_projection_prod (s : Stage (ZMod 2) K)
    [Fintype s.Input] [Fintype (StageQuotient.Space s)]
    {A : Type*} [Fintype A] (p : StageQuotient.Space s → A → Prop) :
    probability (fun z : s.Input × A => p (StageQuotient.projection s z.1) z.2) =
      probability (fun z : StageQuotient.Space s × A => p z.1 z.2) := by
  rw [probability_prod_average_right (fun x a => p (StageQuotient.projection s x) a),
    probability_prod_average_right p]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact probability_projection s (fun x => p x a)

/-- Nonlinear change probability is exactly the base probability after both
the single-copy enlargement and quotient, on uniform quotient input. -/
theorem change_probability (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    [Fintype (StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀))] :
    let s := productStage i hi C hC noise hdim b₀ hb₀
    probability (fun z : StageQuotient.Space s × (Copies B K × N) =>
      StageQuotient.output s (z.1 + StageQuotient.noise s z.2) ≠ StageQuotient.output s z.1) =
        probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) := by
  dsimp only
  let : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  let s := productStage i hi C hC noise hdim b₀ hb₀
  let : Fintype s.Input := Fintype.ofFinite _
  have hp := probability_projection_prod s (fun q (t : Copies B K × N) =>
    StageQuotient.output s (q + StageQuotient.noise s t) ≠ StageQuotient.output s q)
  calc
    _ = probability (fun z : s.Input × (Copies B K × N) =>
        StageQuotient.output s (StageQuotient.projection s z.1 + StageQuotient.noise s z.2) ≠
          StageQuotient.output s (StageQuotient.projection s z.1)) := hp.symm
    _ = probability (fun z : (Copies B K → V) × (Copies B K × N) =>
        enlargedOutput C
          (Function.update z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)) ≠ enlargedOutput C z.1) := by
      apply probability_pointwise
      intro z
      have h₁ := change_iff i hi C hC noise hdim b₀ hb₀ z.1 z.2.1 z.2.2
      have h₂ := enlargedOutput_update_ne_iff C z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)
      simp only [update_canonical] at h₁ h₂ ⊢
      have hc := h₁.trans h₂.symm
      -- `s.Input` is a defined function space; rewrite at default transparency.
      erw [update_canonical] at hc
      exact hc
    _ = _ := by
      have hh := enlarged_random_copy_probability (F := ZMod 2) (K := K) C noise
      simp only [update_canonical] at hh ⊢
      unfold probability at hh ⊢
      exact hh

/-- The final noise sample is the actual product sampler and meets the stated
rank-detection bound. No detection premise about the enlarged gadget is assumed. -/
theorem detection_probability {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (hbase : ∀ U : V →ₗ[ZMod 2] E, Function.Injective (U.comp i) →
      1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0))
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (T.comp (StageQuotient.shift
        (productStage i hi C hC noise hdim b₀ hb₀))))) :
    1 / 8 ≤ probability (fun t : Copies B K × N =>
      T (StageQuotient.noise (productStage i hi C hC noise hdim b₀ hb₀) t) ≠ 0) := by
  change 1 / 8 ≤ probability (fun t : Copies B K × N =>
    copyObserver i hi C hC noise hdim b₀ hb₀ T t.1 (noise t.2) ≠ 0)
  rw [probability_prod_average (fun L n =>
    copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0)]
  exact detection_average i hi C hC noise hdim b₀ hb₀ hbase T hr

end MaxCutGames.Gadget.EnlargementConstruction
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_StageData
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Gadget.StageData

open scoped BigOperators Classical
open MaxCutGames.Gadget

variable {C : Type} [AddCommGroup C] [Module (ZMod 2) C]

/-- Intrinsic count probability and uniform finite expectation are identical. -/
theorem count_probability_eq_expect {Ω : Type*} [Fintype Ω] (p : Ω → Prop) :
    Enlargement.probability p = 𝔼 x : Ω, if p x then (1 : ℚ) else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Enlargement.probability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem stabilityError_toData (s : Stage (ZMod 2) C) (embed : C →ₗ[ZMod 2] s.Input)
    (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c) :
    ActualGadget.stabilityError (toData s embed hinj hEquiv) = StageNoiseRecurrence.error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  rw [StageNoiseRecurrence.error_eq_expect]
  unfold ActualGadget.stabilityError
  change (𝔼 t : s.Input × s.Noise,
    if s.output (t.1 + s.noise t.2) = s.output t.1 then (0 : ℚ) else 1) = _
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  simp only [ne_eq, ite_not]

theorem stabilityError_toData_count (s : Stage (ZMod 2) C)
    [Fintype s.Input] [Fintype s.Noise] (embed : C →ₗ[ZMod 2] s.Input)
    (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c) :
    ActualGadget.stabilityError (toData s embed hinj hEquiv) =
      Enlargement.probability (fun t : s.Input × s.Noise =>
        s.output (t.1 + s.noise t.2) ≠ s.output t.1) := by
  classical
  rw [stabilityError_toData, StageNoiseRecurrence.error_eq_expect,
    count_probability_eq_expect]
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro u _
  apply Finset.expect_congr rfl
  intro n _
  split_ifs <;> rfl

theorem error_eq_count_probability (s : Stage (ZMod 2) C)
    [Fintype s.Input] [Fintype s.Noise] :
    StageNoiseRecurrence.error s = Enlargement.probability
      (fun t : s.Input × s.Noise => s.output (t.1 + s.noise t.2) ≠ s.output t.1) := by
  classical
  rw [StageNoiseRecurrence.error_eq_expect, count_probability_eq_expect]
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro u _
  apply Finset.expect_congr rfl
  intro n _
  split_ifs <;> rfl

theorem kernelError_toData_count (s : Stage (ZMod 2) C) [Fintype s.Noise]
    (embed : C →ₗ[ZMod 2] s.Input) (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (T : s.Input →ₗ[ZMod 2] E) :
    ActualGadget.kernelError (toData s embed hinj hEquiv) T =
      Enlargement.probability (fun n : s.Noise => T (s.noise n) = 0) := by
  classical
  rw [count_probability_eq_expect]
  change StageNoiseRecurrence.average (fun n : s.Noise =>
    if T (s.noise n) = 0 then (1 : ℚ) else 0) = _
  rw [StageNoiseRecurrence.average_eq_expect]

/-- The common interface's zero-image error is exactly the complement of
the v2 nonzero-image detection probability. -/
theorem kernelError_eq_one_sub_detection (s : Stage (ZMod 2) C) [Fintype s.Noise]
    (embed : C →ₗ[ZMod 2] s.Input) (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (T : s.Input →ₗ[ZMod 2] E) :
    ActualGadget.kernelError (toData s embed hinj hEquiv) T =
      1 - Enlargement.probability (fun n : s.Noise => T (s.noise n) ≠ 0) := by
  classical
  rw [kernelError_toData_count, count_probability_eq_expect, count_probability_eq_expect]
  calc
    (𝔼 n : s.Noise, if T (s.noise n) = 0 then (1 : ℚ) else 0) =
        𝔼 n : s.Noise, (1 - if T (s.noise n) ≠ 0 then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro n _
      by_cases hn : T (s.noise n) = 0 <;> simp [hn]
    _ = _ := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const]
      apply congrArg (fun x : ℚ => 1 - x)
      apply Finset.expect_congr rfl
      intro n _
      split_ifs <;> rfl

theorem kernelError_le_of_detection (s : Stage (ZMod 2) C) [Fintype s.Noise]
    (embed : C →ₗ[ZMod 2] s.Input) (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (T : s.Input →ₗ[ZMod 2] E)
    (d : ℚ) (hd : d ≤ Enlargement.probability (fun n : s.Noise => T (s.noise n) ≠ 0)) :
    ActualGadget.kernelError (toData s embed hinj hEquiv) T ≤ 1 - d := by
  rw [kernelError_eq_one_sub_detection]
  exact sub_le_sub_left hd 1

end MaxCutGames.Gadget.StageData

/-!
# Constant-detection enlargement endpoint

The finite base alphabet and its rank threshold are fixed before the target
logical space. The resulting actual gadget has the same nonlinear error and
linear kernel error at most `7/8`. Only the common data and experiment interface
is reused from the old gadget namespace.
-/

namespace MaxCutGames.Gadget.EnlargementEndpoint

open scoped Classical
open Enlargement EnlargementConstruction
open MaxCutGames.Gadget

variable {B K V N : Type}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

/-- Base stability and base detection suffice for the complete enlarged
gadget. Its detection error is the fixed constant `7/8`, as required by v2. -/
theorem data_satisfies (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (p : ℚ)
    (hchange : probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) ≤ p)
    (hbase : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : V →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
        1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0)) :
    ActualGadget.Satisfies (data i hi C hC noise hdim b₀ hb₀) p (7 / 8)
      (Module.finrank (ZMod 2) B + 2) := by
  let s := productStage i hi C hC noise hdim b₀ hb₀
  let q := StageQuotient.toStage s
  let : Fintype (StageQuotient.Space s) := Fintype.ofFinite _
  let : Fintype q.Input := Fintype.ofFinite _
  let : Fintype q.Noise := Fintype.ofFinite _
  constructor
  · change ActualGadget.stabilityError (StageData.toData q (StageQuotient.shift s)
      (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s)) ≤ p
    have heq := StageData.stabilityError_toData_count q (StageQuotient.shift s)
      (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s)
    have hc := change_probability i hi C hC noise hdim b₀ hb₀
    exact heq.le.trans (hc.le.trans hchange)
  · intro E _ _ T hr
    have hd := detection_probability i hi C hC noise hdim b₀ hb₀ (hbase E) T hr
    have he := StageData.kernelError_le_of_detection q (StageQuotient.shift s)
      (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s) T (1 / 8) hd
    norm_num at he
    exact he

/-- For every permitted logical space there is an actual gadget. The rank
threshold `dim B + 2` and all base data are independent of that space. -/
theorem exists_data (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (p : ℚ)
    (hchange : probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) ≤ p)
    (hbase : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : V →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
        1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0)) :
    ∃ g : ActualGadget.Data K,
      ActualGadget.Satisfies g p (7 / 8) (Module.finrank (ZMod 2) B + 2) :=
  ⟨data i hi C hC noise hdim b₀ hb₀,
    data_satisfies i hi C hC noise hdim b₀ hb₀ p hchange hbase⟩

end MaxCutGames.Gadget.EnlargementEndpoint
end

namespace MaxCutGames.Gadget

open Quadratic QuadraticStageNoise
open MaxCutGames.Integration.BinaryLinear
open scoped Classical

noncomputable section

/-- Actual finite gadget data, with a rank threshold independent of the final
logical dimension and an arbitrarily small nonlinear change probability. -/
theorem exists_actual_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ g : MaxCutGames.Gadget.ActualGadget.Data (Vector ℓ),
        MaxCutGames.Gadget.ActualGadget.Satisfies g p (7 / 8) r := by
  obtain ⟨d, _hd, n, herror, hdetect⟩ := BaseConstruction.exists_base p hp
  let B := Vec (BinaryField d)
  let s := quotientStage (F := BinaryField d) n
  let : Fintype B := Fintype.ofFinite _
  let : FiniteDimensional (ZMod 2) B := Module.Finite.of_finite
  let : Fintype s.Input := Fintype.ofFinite _
  let : Fintype s.Noise := Fintype.ofFinite _
  let i : B →ₗ[ZMod 2] s.Input := s.embed
  let r := Module.finrank (ZMod 2) B + 2
  refine ⟨r, by omega, ?_⟩
  intro ℓ hℓ
  have hdim : Module.finrank (ZMod 2) B ≤
      Module.finrank (ZMod 2) (Vector ℓ) := by
    rw [finrank_vector]
    omega
  let b₀ : B := fun _ => 1
  have hb₀ : b₀ ≠ 0 := by
    intro h
    have hzero := congrFun h (0 : Fin 3)
    exact one_ne_zero hzero
  have hequiv : ∀ u (b : B), s.output (u + i b) = s.output u + b := by
    intro u b
    exact s.equivariant u b
  have hc : Enlargement.probability (fun z : s.Input × s.Noise =>
      s.output (z.1 + s.noise z.2) ≠ s.output z.1) ≤ p := by
    rw [← StageData.error_eq_count_probability s]
    exact herror
  have hb : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : s.Input →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
      (1 / 4 : ℚ) ≤ Enlargement.probability (fun t => U (s.noise t) ≠ 0) := by
    intro E _ _ U hU
    have h := hdetect E U hU
    rw [StageNoiseRecurrence.average_eq_expect] at h
    refine h.trans_eq ?_
    rw [StageData.count_probability_eq_expect]
    apply Finset.expect_congr rfl
    intro t _
    by_cases ht : U (s.noise t) = 0
    · simp only [s] at ht ⊢
      simp only [ht, ne_eq, not_true_eq_false, ite_false]
    · simp only [s] at ht ⊢
      simp only [ht, ne_eq, not_false_eq_true, ite_true, if_true]
  exact EnlargementEndpoint.exists_data (B := B) (K := Vector ℓ)
    i s.embed_injective s.output hequiv s.noise hdim b₀ hb₀ p hc hb

theorem exists_split_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ d : ℕ, ∃ g : MaxCutGames.Reduction.ActualSource.SplitGadget ℓ d,
        g.stabilityError ≤ p ∧
        ∀ (P : Type) [AddCommGroup P] [Module F2 P]
          (S : MaxCutGames.Reduction.ActualSource.Ambient ℓ d →ₗ[F2] P),
          r ≤ Module.finrank F2
            (S.comp (MaxCutGames.Reduction.ActualSource.alphabetEmbedding ℓ d)).range →
          MaxCutGames.Integration.SplitGadget.kernelProbability g S ≤ 7 / 8 := by
  obtain ⟨r, hr, hg⟩ := exists_actual_gadget p hp
  refine ⟨r, hr, ?_⟩
  intro ℓ hℓ
  obtain ⟨g, hgood⟩ := hg ℓ hℓ
  exact MaxCutGames.Integration.SplitGadget.exists_split_gadget_general g hgood

end

end MaxCutGames.Gadget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_MatrixGapInverse
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matrix reduction assembled from the gadget and decoder.
The dimension-uniform shortcode inverse is the sole explicit mathematical
input here. This intermediate theorem is not an unconditional endpoint until
that input is supplied by the independently proved KMS foundation. -/

namespace MaxCutGames.Decoder.MatrixGap

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Integration

noncomputable section

theorem parameters_of_inverse (hinverse : Inverse.Shortcode.InversePrinciple)
    (p : ℚ) (hp : 0 < p) : Nonempty (Parameters p) := by
  obtain ⟨rstar, hrstar, hgadget⟩ := Gadget.exists_split_gadget p hp
  obtain ⟨P⟩ := MatrixGapChoice.exists_inverse_parameters hinverse rstar
  obtain ⟨d, g, hstable, hkernel⟩ := hgadget P.s P.s_large
  let en := NoiseEnumeration.ofFintype g
  let T := NoiseTables.Table.ofEnumeration g en
  let gT := T.gadget g.f g.equivariant
  have hstableT : gT.stabilityError ≤ p := by
    exact (NoiseTables.Table.stabilityError_ofEnumeration g en).trans_le hstable
  have hkernelT : ∀ (Q : Type) [AddCommGroup Q] [Module F2 Q]
      (L : Ambient P.s d →ₗ[F2] Q),
      rstar ≤ Module.finrank F2 (L.comp (alphabetEmbedding P.s d)).range →
        Integration.SplitGadget.kernelProbability gT L ≤ 7 / 8 := by
    intro Q _ _ L hL
    exact (NoiseTables.Table.kernelProbability_ofEnumeration g en L).trans_le (hkernel Q L hL)
  obtain ⟨m, hm, hlarge, hβ, hβ', htv, hrate⟩ := MatrixGapChoice.exists_cube P d
  refine ⟨{
    k := m ^ 3
    s := P.s
    d := d
    k_pos := Nat.succ_le_iff.mpr (pow_pos hm _)
    s_pos := hrstar.trans P.s_large
    T := T
    f := g.f
    equivariant := g.equivariant
    stability := hstableT
    sound := ?_ }⟩
  intro S hdistinct hopt
  apply address_value_le_of_semantic_acceptance S (m ^ 3) T g.f g.equivariant
  intro labeling
  apply le_of_lt
  by_contra hnot
  have haccept : (99 : ℚ) / 100 ≤ TableKeysGame.acceptanceProbability S (m ^ 3) gT labeling :=
    le_of_not_gt hnot
  have hgood := P.advice (m ^ 3) hlarge S d gT labeling
    (fun L hL => hkernelT (ActualHomogeneous.E (m ^ 3)) L hL) haccept
  exact ActualMatrixContradiction.contradiction S labeling P.α
    (ActualGoodRows.goodRowMass rstar P.s P.r) (1 / (m : ℝ) ^ 2)
    P.positive P.trivial_small hβ hβ' hgood htv hrate hdistinct hopt

end
end MaxCutGames.Decoder.MatrixGap

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_MatrixGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed finite matrix reduction obtained from the actual v2 latent
gadget, dimension-uniform shortcode inverse, sparse full-table law and private
local decoder. The construction precedes the parity input and its accuracy.
No inverse, noise, spectral, or decoder certificate is supplied as a premise. -/

namespace MaxCutGames.Decoder.MatrixGap

theorem exists_parameters (p : ℚ) (hp : 0 < p) : Nonempty (Parameters p) :=
  parameters_of_inverse Inverse.ShortcodeTheorem.inversePrinciple p hp

end MaxCutGames.Decoder.MatrixGap

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Theorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Theorem

theorem exists_binaryGapReduction (ε δ : ℝ)
    (hε : 0 < ε) (_hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (_hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) := by
  obtain ⟨P⟩ := ParameterSelection.exists_outerParameters ε δ hε hδ
  obtain ⟨M⟩ := Decoder.MatrixGap.exists_parameters P.pStar P.pStar_pos
  exact ⟨FromMatrixGap.reduction P M⟩

end MaxCutGames.Theorem

namespace MaxCutGames

/-- For every fixed pair of errors in `(0, 1/2)`, binary 3SAT reduces in
polynomial time to translation Unique Games with completeness at least `1 - ε`
and soundness at most `δ`. The alphabet and machine depend only on the errors. -/
theorem theorem11_oai (ε δ : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) :=
  Theorem.exists_binaryGapReduction ε δ hε hεhalf hδ hδhalf

end MaxCutGames

end OAI
end

theorem solution : type_of% @OAI.MaxCutGames.theorem11_oai := @OAI.MaxCutGames.theorem11_oai
