-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:16:12.145136+00:00
-- url     : https://prove2.me/submissions/c1645649-2577-4677-8b20-a3d249d1e983

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U012

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_BinaryLinear
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact transport from XOR bit vectors to vector spaces over `ZMod 2`. -/
namespace UniqueGamesTheorem.Integration.BinaryLinear

open BinaryCoordinates

theorem toBit_add : ∀ a b : F2, toBit (a + b) = (toBit a ^^ toBit b) := by decide

end UniqueGamesTheorem.Integration.BinaryLinear

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixCharacters

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear

section LinearFunctionals

variable {E : Type*} [AddCommGroup E] [Module F2 E]

theorem linearFunctionalCharacter_injective :
    Function.Injective (linearFunctionalCharacter (E := E)) := by
  intro φ ψ h
  ext x
  apply binarySign_injective
  exact congrArg (fun χ : AddChar E ℂ => χ x) h

theorem linearFunctionalCharacter_eq_zero_iff (φ : E →ₗ[F2] F2) :
    linearFunctionalCharacter φ = 0 ↔ φ = 0 := by
  rw [← linearFunctionalCharacter_zero, linearFunctionalCharacter_injective.eq_iff]

theorem sum_linearFunctionalCharacter [Fintype E] (φ : E →ₗ[F2] F2) :
    ∑ x, linearFunctionalCharacter φ x =
      if φ = 0 then (Fintype.card E : ℂ) else 0 := by
  rw [AddChar.sum_eq_ite]
  simp only [linearFunctionalCharacter_eq_zero_iff]

theorem expect_linearFunctionalCharacter [Fintype E] (φ : E →ₗ[F2] F2) :
    (𝔼 x, linearFunctionalCharacter φ x) = if φ = 0 then 1 else 0 := by
  rw [Fintype.expect_eq_sum_div_card, sum_linearFunctionalCharacter]
  split_ifs <;> simp [Fintype.card_ne_zero]

end LinearFunctionals

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_add_right (X : E →ₗ[F2] F) (S T : F →ₗ[F2] E) :
    linearTracePair X (S + T) = linearTracePair X S + linearTracePair X T := by
  simp [linearTracePair, LinearMap.comp_add]

theorem linearTraceCharacter_add (S T : F →ₗ[F2] E) :
    linearTraceCharacter (S + T) = linearTraceCharacter S + linearTraceCharacter T := by
  ext X
  simp only [linearTraceCharacter_apply, linearTracePair_add_right, binarySign_add,
    AddChar.add_apply]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixCharacters

end

end

section

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open UniqueGamesTheorem.Fourier.MatrixCharacters

section LinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem linear_fourier_inversion (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re = f X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          fourierCoeff (fun Y => (f Y : ℂ)) (linearTraceCharacter S) *
            linearTraceCharacter S X := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E,
        linearCoeff f S * (linearTraceCharacter S X).re) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      change ((linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, linearCoeff_complex, linearTraceCharacter_real]
    _ = (f X : ℂ) := linear_complex_inversion _ X

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixFourier

end

end

section

/-! Actual binary matrix and linear-map parity used in Lemma 5.3. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixParity

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped Matrix BigOperators Classical

section LinearMaps

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

/-- Generic trace pairing of a rank-one color shift. -/
theorem trace_smulRight_comp [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (c : C) (S : C →ₗ[F2] E) :
    LinearMap.trace F2 C ((τ.smulRight c).comp S) = τ (S c) := by
  have heq : (τ.smulRight c).comp S = (τ.comp S).smulRight c := by
    ext x
    rfl
  rw [heq, LinearMap.trace_smulRight, LinearMap.comp_apply]

/-- The exact number of binary linear maps, supplying the count in (5.20).
Taking `E` to be the subspace `W` counts precisely maps whose image lies in `W`. -/
theorem card_linearMaps [FiniteDimensional F2 E] [FiniteDimensional F2 C]
    [Fintype (C →ₗ[F2] E)] :
    Fintype.card (C →ₗ[F2] E) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 E) := by
  classical
  let bC := Module.finBasis F2 C
  let bE := Module.finBasis F2 E
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (LinearMap.toMatrix bC bE).toEquiv]
  change Nat.card (Fin (Module.finrank F2 E) → Fin (Module.finrank F2 C) → F2) = _
  rw [Nat.card_fun, Nat.card_fun]
  simp [F2, Integration.BinaryLinear.F2, Nat.card_eq_fintype_card, ← pow_mul,
    Nat.mul_comm]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixParity

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixNoiseLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace UniqueGamesTheorem.Fourier.MatrixNoise

open scoped BigOperators Matrix
open UniqueGamesTheorem.Integration.BinaryLinear (Vector)
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem evaluationCharacter_eq_zero_iff (w : E) :
    evaluationCharacter w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff F2 w).mp
    intro ℓ
    apply binarySign_injective
    have hx := congrArg (fun ψ : AddChar (E →ₗ[F2] F2) ℂ => ψ ℓ) h
    simpa using hx
  · rintro rfl
    ext ℓ
    simp

theorem average_evaluationCharacter [Fintype (E →ₗ[F2] F2)] (w : E) :
    (𝔼 ℓ : E →ₗ[F2] F2, binarySign (ℓ w)) =
      if w = 0 then (1 : ℂ) else 0 := by
  classical
  change (𝔼 ℓ, evaluationCharacter w ℓ) = _
  rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
  simp only [evaluationCharacter_eq_zero_iff]
  split_ifs <;> simp

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixNoise

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixRestrictions
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixRestrictions

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

theorem quotientKernel_card (W : Submodule F2 E)
    [Fintype {T : C →ₗ[F2] E // W.mkQ.comp T = 0}]
    [Fintype (C →ₗ[F2] W)] :
    Fintype.card {T : C →ₗ[F2] E // W.mkQ.comp T = 0} =
      Fintype.card (C →ₗ[F2] W) :=
  Fintype.card_congr (quotientKernelEquiv W)

end UniqueGamesTheorem.Fourier.MatrixRestrictions

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixParityRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Fourier expansion of actual affine restrictions and parity extraction. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixParityRow

open MatrixCharacters MatrixFourier MatrixParity
open scoped BigOperators Classical

variable {E C V : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [AddCommGroup V] [Module F2 V]

theorem traceCharacter_comp (Q : E →ₗ[F2] V) (A : V →ₗ[F2] C)
    (T : C →ₗ[F2] E) :
    linearTraceCharacter T (A.comp Q) = linearTraceCharacter (Q.comp T) A := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

theorem traceCharacter_re_add (T : C →ₗ[F2] E) (X Y : E →ₗ[F2] C) :
    (linearTraceCharacter T (X + Y)).re =
      (linearTraceCharacter T X).re * (linearTraceCharacter T Y).re := by
  rw [AddChar.map_add_eq_mul, Complex.mul_re]
  simp [linearTraceCharacter_apply, binarySign_im]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 C] [FiniteDimensional F2 V]
  [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] [Fintype (V →ₗ[F2] C)]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] in
/-- Characters restricted to the row vanish unless the dual map lands in the
kernel of `Q`. For `Q = W.mkQ` this is precisely `range T ≤ W`. -/
theorem row_character_average (Q : E →ₗ[F2] V) (T : C →ₗ[F2] E) :
    (𝔼 A : V →ₗ[F2] C, (linearTraceCharacter T (A.comp Q)).re) =
      if Q.comp T = 0 then 1 else 0 := by
  have hcomplex : (𝔼 A : V →ₗ[F2] C,
      linearTraceCharacter T (A.comp Q)) = if Q.comp T = 0 then 1 else 0 := by
    simp only [traceCharacter_comp, Fintype.expect_eq_sum_div_card,
      sum_linearTraceCharacter]
    split <;> simp [Fintype.card_ne_zero]
  have h := congrArg Complex.re hcomplex
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re] using h

end UniqueGamesTheorem.Fourier.MatrixParityRow

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_and_le_left (μ : FiniteDistribution Ω) (event event' : Ω → Bool) :
    μ.probability (fun x => event x && event' x) ≤ μ.probability event := by
  apply μ.probability_mono
  intro x hx
  have h : event x = true ∧ event' x = true := by simpa using hx
  exact h.1

theorem probability_and_eq_zero_of_probability_eq_zero (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (zero : μ.probability given = 0) :
    μ.probability (fun x => given x && event x) = 0 := by
  apply le_antisymm
  · exact (μ.probability_and_le_left given event).trans_eq zero
  · exact μ.probability_nonnegative _

end FiniteDistribution

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_MixtureLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact finite total variation and its event-probability bound. -/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem totalVariation_comm (μ ν : FiniteDistribution Ω) :
    μ.totalVariation ν = ν.totalVariation μ := by
  unfold totalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

namespace UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

variable [Nonempty A₁] [Nonempty A₂]

theorem exists_deterministic_ge_stochastic (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂,
      G.stochasticSuccess responses₁ responses₂ ≤ G.success strategy := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  refine ⟨strategy, ?_⟩
  rw [h]
  exact G.stochasticSuccess_le_value responses₁ responses₂
end Game
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualCanonicalLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {Name : Type u} {Id : Type v} {R : Type w}
variable {k : Nat}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

omit [DecidableEq R] in
theorem add_both (x y t : R) : (x + t) + (y + t) = x + y := by
  calc
    _ = (x + y) + (t + t) := by abel
    _ = _ := by rw [add_self, add_zero]

omit [Module F2 R] in
theorem pivot_translate (a : Fin 3 → R) (t : R) :
    pivot (translate a t) = pivot a + t := by
  classical
  by_cases h1 : a 0 = a 1 <;> by_cases h2 : a 0 = a 2 <;>
    simp [pivot, translate, h1, h2]

theorem normalize_translate (a : Fin 3 → R) (t : R) :
    normalize (translate a t) = normalize a := by
  unfold normalize
  rw [pivot_translate]
  funext i
  exact add_both _ _ _

theorem record_translate (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) (t : R) :
    record names e (translate a t) = record names e a := by
  classical
  have hs (i : Fin 3) : translate a t i = a i + t := rfl
  simp only [record, hs, add_right_cancel_iff, add_both, normalize_translate]

theorem data_gauge (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z : R) (a : Fin k → Fin 3 → R) (t : Fin k → R) :
    data occ names rhs (z + ∑ j, rhs (occ j) • t j) (fun j => translate (a j) (t j)) =
      data occ names rhs z a := by
  apply Prod.ext
  · simp only [data, pivot_translate, smul_add, Finset.sum_add_distrib]
    exact add_both _ _ _
  · funext j
    exact record_translate names (occ j) (a j) (t j)

omit [DecidableEq R] in
/-- Equality on the homogeneous space forces the free-coordinate identities. -/
theorem extension_coefficients (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) (h : Represents b z a X) :
    X (hBasis k) = z + ∑ j, b j • a j 2 ∧
      ∀ j, X (firstBasis j) = a j 0 + a j 2 ∧
        X (secondBasis j) = a j 1 + a j 2 := by
  constructor
  · simpa only [ambientEval_hBasis] using (h (hBasis k)).symm
  · intro j
    exact ⟨by simpa only [ambientEval_firstBasis] using (h (firstBasis j)).symm,
      by simpa only [ambientEval_secondBasis] using (h (secondBasis j)).symm⟩

/-- Every ambient extension of a genuine map gives the same canonical data. -/
theorem canonical_eq_of_extension (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) (X : E k →ₗ[F2] R)
    (h : Represents (fun j => rhs (occ j)) z a X) :
    canonical occ names rhs X = data occ names rhs z a := by
  obtain ⟨hz, ha⟩ := extension_coefficients _ z a X h
  have ht : standardTriple X = fun j => translate (a j) (a j 2) := by
    funext j i
    fin_cases i
    · exact (ha j).1
    · exact (ha j).2
    · exact (add_self (a j 2)).symm
  unfold canonical
  rw [hz, ht]
  exact data_gauge occ names rhs z a (fun j => a j 2)

omit [Module F2 R] in
theorem pivot_singleton (i : Fin 3) (c : R) : pivot (singletonTriple i c) = 0 := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;> simp [singletonTriple, pivot, hc]

omit [Module F2 R] in
theorem record_singleton (names : Id → Fin 3 → Name) (e : Id) (i : Fin 3) (c : R) :
    record names e (singletonTriple i c) =
      (if c = 0 then Record.blank else Record.single (names e i) c) := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;>
    simp [record, singletonTriple, hc, eq_comm]

theorem singleton_global_adjustment (rhs : Id → F2) (e : Id) (i : Fin 3) (c : R) :
    rhs e • pivot (singletonTriple i c) = 0 := by rw [pivot_singleton, smul_zero]

omit [Module F2 R] in
/-- The hidden occurrence and its internal slot cannot affect a retained
single-variable record. The occurrence need not differ from other positions. -/
theorem singleton_locality (names : Id → Fin 3 → Name) (e e' : Id)
    (i i' : Fin 3) (c : R) (hname : names e i = names e' i') :
    record names e (singletonTriple i c) = record names e' (singletonTriple i' c) := by
  simp only [record_singleton, hname]

end UniqueGamesTheorem.Reduction.ActualCanonical

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ZeroInformationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.secondInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Soundness.ZeroInformation

/-! ## The observation fibre is a Cartesian product -/

/-! ## Exact weighted finite counting -/

/-! ## Position-indexed row maps -/

theorem rowSum_congr {P R : Type} (positions : List P) (a b : P → Bits R)
    (h : ∀ j, a j = b j) : rowSum positions a = rowSum positions b := by
  have hab : a = b := funext h
  rw [hab]

/-- Changing an index where its position coefficient is zero does not change the
entire row map. This is an equality for all ambient coordinates, so also on E_U. -/
theorem pullbackRow_index_independent {P R : Type} (positions : List P)
    (single : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (i i' : P → Fin 3)
    (agrees : ∀ j, single j = true → omega j ≠ zero → i j = i' j)
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    pullbackRow positions single zeta0 zeta1 zeta2 omega i homogeneous x =
      pullbackRow positions single zeta0 zeta1 zeta2 omega i' homogeneous x := by
  unfold pullbackRow
  congr 1
  apply rowSum_congr
  intro j
  cases hs : single j
  · simp
  · simp only [↓reduceIte]
    by_cases hz : omega j = zero
    · simp [hz]
    · rw [agrees j hs hz]

/-! ## Complete private-input reconstruction -/

theorem decodeIndex_name {O N : Type} (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i') (o : O) (i : Fin 3) :
    decodeIndex name o (name o i) = i := by
  classical
  unfold decodeIndex
  have he : ∃ i', name o i' = name o i := ⟨i, rfl⟩
  simp only [he, ↓reduceDIte]
  exact distinct o _ i (Classical.choose_spec he)

theorem reconstructQuestion_actual {P X : Type} (hidden : P → Bool)
    (actual outside : P → X) (houtside : ∀ j, hidden j = false → outside j = actual j) :
    reconstructQuestion hidden actual outside = actual := by
  funext j
  cases hj : hidden j
  · simp [reconstructQuestion, hj, houtside j hj]
  · simp [reconstructQuestion, hj]

theorem first_input_reconstruction {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (hidden_zero : ∀ j, hidden j = true → omega j = zero)
    (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (occurrences outsideOccurrences : P → O) (indices : P → Fin 3)
    (outsideNames : P → N)
    (houtsideO : ∀ j, hidden j = false → outsideOccurrences j = occurrences j)
    (houtsideN : ∀ j, hidden j = false → outsideNames j = name (occurrences j) (indices j)) :
    reconstructFirst positions single hidden zeta0 zeta1 zeta2 omega name
        occurrences outsideOccurrences outsideNames =
      firstInput positions single zeta0 zeta1 zeta2 omega occurrences indices := by
  unfold reconstructFirst firstInput
  rw [reconstructQuestion_actual hidden occurrences outsideOccurrences houtsideO]
  congr 1
  funext homogeneous x
  apply pullbackRow_index_independent
  intro j _ hz
  have hj : hidden j = false := by
    cases hh : hidden j
    · rfl
    · exact False.elim (hz (hidden_zero j hh))
  rw [houtsideO j hj, houtsideN j hj]
  exact decodeIndex_name name distinct (occurrences j) (indices j)

theorem second_input_reconstruction {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (hidden_single : ∀ j, hidden j = true → single j = true)
    (occurrences outsideOccurrences : P → O) (names outsideNames : P → N)
    (houtsideO : ∀ j, hidden j = false → outsideOccurrences j = occurrences j)
    (houtsideN : ∀ j, hidden j = false → outsideNames j = names j) :
    reconstructSecond positions single hidden zeta0 zeta1 zeta2 omega
        outsideOccurrences names outsideNames =
      secondInput positions single zeta0 zeta1 zeta2 omega occurrences names := by
  unfold reconstructSecond secondInput
  rw [reconstructQuestion_actual hidden names outsideNames houtsideN]
  congr 1
  funext j
  unfold partnerQuestion
  cases hs : single j
  · have hj : hidden j = false := by
      cases hh : hidden j
      · rfl
      · have contradiction := hidden_single j hh
        rw [hs] at contradiction
        contradiction
    simp [houtsideO j hj]
  · simp

end UniqueGamesTheorem.Soundness.ZeroInformation

open scoped BigOperators

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ConditionalLocality
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.secondInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete local private inputs after fixing H

The constructors here consume only the appropriate zero-set question tuple:
occurrences for the first player, names for the second. A single reference sample
from the positive observation fibre is fixed once as part of H-dependent advice.
It supplies arbitrary padding at hidden positions and never depends on the actual
remaining sample. The reconstruction theorems prove equality of the complete
question-plus-row input, and the row maps restrict to the actual equation spaces
as shown in `ZeroInformation.supplied_map_pullback`.
-/

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences

noncomputable section

theorem singleCoefficient_zero {P R : Type} [DecidableEq P]
    [Fintype R] [DecidableEq R] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) (j : P)
    (hj : j ∈ zeroSet J gamma) : singleCoefficient J gamma j = ZeroInformation.zero := by
  obtain ⟨hjJ, hz⟩ := (mem_zeroSet J gamma j).mp hj
  change gamma (some (.inr ⟨j, hjJ⟩)) = ZeroInformation.zero at hz
  simpa only [singleCoefficient, hjJ, ↓reduceDIte] using hz

variable {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  (J : Finset P) (name : O → Fin 3 → N)
  (gamma : RawCoefficients J (ZeroInformation.Bits R))
  (observed : PositionOutside (zeroSet J gamma) → O × N)

omit [Fintype P] [DecidableEq R] in
theorem outside_pair_agree (reference sample : RawObservationFibre J name gamma observed)
    (j : P) (hj : j ∉ zeroSet J gamma) :
    incidence name (reference.val.2 j) = incidence name (sample.val.2 j) := by
  exact congrFun (reference.property.2.trans sample.property.2.symm) ⟨j, hj⟩

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_occurrences (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma) (fun j => (reference.val.2 j).1)
        (fun j => (sample.val.2 j.val).1) =
      (fun j => (sample.val.2 j).1) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj)

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_names (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma)
        (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      (fun j => name (sample.val.2 j).1 (sample.val.2 j).2) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj)

/-- Equality of the entire first private input, including its row map. -/
theorem localFirstFromH_correct
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (reference sample : RawObservationFibre J name gamma observed) :
    localFirstFromH J name gamma observed reference (fun j => (sample.val.2 j.val).1) =
      actualFirst J gamma sample.val.2 := by
  unfold localFirstFromH actualFirst
  rw [fillHidden_occurrences J name gamma observed reference sample]
  apply ZeroInformation.first_input_reconstruction
  · intro j hj
    exact singleCoefficient_zero J gamma j (of_decide_eq_true hj)
  · exact distinct
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj')
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj')

omit [DecidableEq R] in
/-- Equality of the entire second private input. The constructor requires no
occurrence, equation rhs, or slot from any position in K. -/
theorem localSecondFromH_correct (reference sample : RawObservationFibre J name gamma observed) :
    localSecondFromH J name gamma observed reference
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      actualSecond J name gamma sample.val.2 := by
  unfold localSecondFromH actualSecond
  rw [fillHidden_names J name gamma observed reference sample]
  apply ZeroInformation.second_input_reconstruction
  · intro j hj
    exact decide_eq_true (zeroSet_subset J gamma (of_decide_eq_true hj))
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj')
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj')

end

end UniqueGamesTheorem.Soundness.ConditionalIncidences

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ExpectationComparisonLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Soundness.IncidenceExtraction

theorem Incidence.accepts_implies_namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) (h : g.accepts o i a b) :
    g.namedAccepts o (g.name o i) a b :=
  ⟨i, rfl, h⟩

/-- Distinct names make the named-variable predicate equivalent to the sampled
    retained-slot predicate, without revealing that slot to either strategy. -/
theorem Incidence.namedAccepts_iff_accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (o : Occurrence) (i : Fin 3) (a : Triple) (b : Bool) :
    g.namedAccepts o (g.name o i) a b ↔ g.accepts o i a b := by
  constructor
  · rintro ⟨j, hname, h⟩
    have hji := distinct o j i hname
    simpa [hji] using h
  · exact g.accepts_implies_namedAccepts o i a b

/-!
The next definitions separate local strategies from arbitrary joint strategies.
Each question reconstruction and each answer extraction has access to only one
player's question. A value conditioned on by an analysis may occur as a fixed
parameter of a `LocalSimulation`; it cannot become an additional random input.
-/

/-- A local simulation transports every deterministic strategy and contains
    its winning event pointwise. No shared access to the questions is used. -/
theorem LocalSimulation.induced_wins
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB)
    (qa : InnerQA) (qb : InnerQB)
    (hwins : s.wins outer (r.questionA qa) (r.questionB qb)) :
    (r.induced s).wins inner qa qb :=
  r.sound qa qb (s.first (r.questionA qa)) (s.second (r.questionB qb)) hwins

end UniqueGamesTheorem.Soundness.IncidenceExtraction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_LinearMapDensityLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
This bridge connects the concrete partner projection to the actual equation/name
predicate of the incidence game. It uses no probabilistic or analytic hypotheses.
-/

namespace UniqueGamesTheorem.Soundness.ConcreteExtraction

open PartnerProjection IncidenceExtraction

theorem parity_coordinates (x : PartnerProjection.Triple) :
    IncidenceExtraction.xorTriple (tripleCoordinates x) = PartnerProjection.parity x := rfl

theorem retained_coordinates (x : PartnerProjection.Triple) (i : PartnerProjection.Slot) :
    tripleCoordinates x (slotIndex i) = PartnerProjection.retained i x := by
  cases i <;> rfl

end UniqueGamesTheorem.Soundness.ConcreteExtraction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_PartnerLinearLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Soundness.PartnerLinear

open PartnerProjection
open UniqueGamesTheorem.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
  toBit_ofBit ofBit_xor)

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

theorem projection_apply (x : SourcePoint rhs) :
    projection rhs active slot x = project rhs active slot x := rfl

end UniqueGamesTheorem.Soundness.PartnerLinear

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_PartnerMapCoordinates
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Every partner linear map has independent raw coefficient coordinates

The coefficient index is exactly `ConditionalIncidences.RawSlot`: one global
coefficient, two coefficients at every full position, and one at every single
position.  The coordinate bijection below is for every actual partner linear
map, and its finite-uniform-law theorem has no distributional hypothesis.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Soundness.PartnerMapCoordinates

open PartnerProjection
open ConditionalIncidences (PositionInside PositionOutside RawSlot RawCoefficients )
open UniqueGamesTheorem.Integration.BinaryLinear (F2 ofBit toBit)

noncomputable section

variable {P : Type} [DecidableEq P] (rhs : P → Bool) (J : Finset P)

variable [Fintype P]

variable (R : Type) [AddCommGroup R] [Module F2 R]

/-- The raw-coefficient formula for every partner point. -/
theorem mapEquiv_expansion (gamma : RawCoefficients J R) (y : PartnerPoint rhs (activeOf J)) :
    mapEquiv rhs J R gamma y =
      ofBit y.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (y.full j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (y.full j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J, ofBit (y.single j.val) • gamma (some (.inr j)) := by
  rw [mapEquiv_apply, Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, pointEquiv_none, pointEquiv_full_first,
    pointEquiv_full_second, pointEquiv_single]
  simp only [add_assoc]

theorem pullback_expansion (gamma : RawCoefficients J R) (slot : P → Slot)
    (x : SourcePoint rhs) :
    mapEquiv rhs J R gamma (PartnerLinear.projection rhs (activeOf J) slot x) =
      ofBit x.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (x.coordinates j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (x.coordinates j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J,
          ofBit (retained (slot j.val) (x.coordinates j.val)) • gamma (some (.inr j)) := by
  rw [mapEquiv_expansion]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]
  · apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]

end

end UniqueGamesTheorem.Soundness.PartnerMapCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ActualCanonicalPullbackLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.secondInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Canonical-row descent for every actual partner linear map. -/

namespace UniqueGamesTheorem.Soundness.ActualCanonicalPullback

open scoped BigOperators
open PartnerProjection PartnerMapCoordinates
open ConditionalIncidences
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction

noncomputable section

variable {k : Nat} (rhsB : Fin k → Bool) (J : Finset (Fin k))
variable (R : Type) [AddCommGroup R] [Module F2 R]

theorem ofBit_and (a b : Bool) : ofBit (a && b) = ofBit a * ofBit b := by
  cases a <;> cases b <;> decide

theorem inverse_homogeneous (v : ActualHomogeneous.E k) :
    ofBit (((PartnerLinear.sourceLinearEquiv rhsB).symm v).homogeneous) = v.1 :=
  ofBit_toBit _

theorem inverse_first (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).first) =
      (v.2 j).1 := ofBit_toBit _

theorem inverse_second (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).second) =
      (v.2 j).2 := ofBit_toBit _

theorem inverse_retained_free (v : ActualHomogeneous.E k) (j : Fin k)
    (slot : Fin k → Slot) :
    ofBit (retained (slot j)
      (((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j)) =
        selectedFree (fun j => ofBit (rhsB j)) slot v j := by
  unfold selectedFree
  cases hslot : slot j with
  | first => exact ofBit_toBit _
  | second => exact ofBit_toBit _
  | third =>
    change ofBit (((rhsB j && toBit v.1).xor (toBit (v.2 j).1)).xor
      (toBit (v.2 j).2)) = ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2
    rw [ofBit_xor, ofBit_xor, ofBit_and, ofBit_toBit, ofBit_toBit, ofBit_toBit]

theorem freePullback_expansion (gamma : RawCoefficients J R)
    (slot : Fin k → Slot) (v : ActualHomogeneous.E k) :
    freePullback rhsB J R gamma slot v =
      v.1 • gamma none +
        (∑ j : PositionOutside J, ((v.2 j.val).1 • gamma (some (.inl (j,0))) +
          (v.2 j.val).2 • gamma (some (.inl (j,1))))) +
        ∑ j : PositionInside J, selectedFree (fun j => ofBit (rhsB j)) slot v j.val •
          gamma (some (.inr j)) := by
  change mapEquiv rhsB J R gamma
    (PartnerLinear.projection rhsB (activeOf J) slot
      ((PartnerLinear.sourceLinearEquiv rhsB).symm v)) = _
  rw [pullback_expansion]
  simp only [inverse_homogeneous, inverse_first, inverse_second, inverse_retained_free]

omit [Module F2 R] in
theorem sum_outside_inside (f : PositionOutside J → R) (g : PositionInside J → R) :
    (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, if hj : j ∈ J then g ⟨j,hj⟩ else f ⟨j,hj⟩ := by
  rw [← (outsideInsideEquiv J).sum_comp]
  rw [Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro j _
    simp [outsideInsideEquiv, j.property]
  · intro j _
    simp [outsideInsideEquiv, j.property]

theorem raw_represents (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.Represents (fun j => ofBit (rhsB j)) (gamma none)
      (ambientCoefficients J R gamma slot) (freePullback rhsB J R gamma slot) := by
  intro v
  let f : PositionOutside J → R := fun j =>
    (v.2 j.val).1 • gamma (some (.inl (j,0))) +
      (v.2 j.val).2 • gamma (some (.inl (j,1)))
  let g : PositionInside J → R := fun j =>
    selectedFree (fun j => ofBit (rhsB j)) slot v j.val • gamma (some (.inr j))
  have hs : (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, ((v.2 j).1 • ambientCoefficients J R gamma slot j 0 +
        (v.2 j).2 • ambientCoefficients J R gamma slot j 1 +
        (ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2) •
          ambientCoefficients J R gamma slot j 2) := by
    rw [sum_outside_inside]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · cases hslot : slot j <;>
        simp [g, ambientCoefficients, selectedFree, hj, hslot, ConcreteExtraction.slotIndex]
    · simp [f, ambientCoefficients, hj]
  calc
    ActualCanonical.ambientEval _ _ _ v = v.1 • gamma none + ((∑ j, f j) + (∑ j, g j)) :=
      congrArg (fun z : R => v.1 • gamma none + z) hs.symm
    _ = (v.1 • gamma none + (∑ j, f j)) + (∑ j, g j) := (add_assoc _ _ _).symm
    _ = freePullback rhsB J R gamma slot v :=
      (freePullback_expansion rhsB J R gamma slot v).symm

theorem canonical_raw_pullback [DecidableEq R] {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) := by
  apply ActualCanonical.canonical_eq_of_extension
  simpa only [ofBit_toBit] using raw_represents (fun j => toBit (rhs (occ j))) J R gamma slot

omit [Module F2 R] in
theorem ambientCoefficients_single (gamma : RawCoefficients J R) (slot : Fin k → Slot)
    (j : Fin k) (hj : j ∈ J) :
    ambientCoefficients J R gamma slot j =
      ActualCanonical.singletonTriple (ConcreteExtraction.slotIndex (slot j))
        (gamma (some (.inr ⟨j,hj⟩))) := by
  funext i
  simp [ambientCoefficients, hj, ActualCanonical.singletonTriple, Pi.single_apply]

omit [Module F2 R] in
theorem ambientCoefficients_full_eq (gamma : RawCoefficients J R)
    (slot slot' : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    ambientCoefficients J R gamma slot j = ambientCoefficients J R gamma slot' j := by
  funext i
  simp [ambientCoefficients, hj]

/-- Raw canonical data is determined by the full displayed occurrences and
    retained variable names. Hidden single occurrences and slot indices vanish. -/
theorem raw_data_locality [DecidableEq R] {Id Name : Type}
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) =
      ActualCanonical.data occ' names rhs (gamma none) (ambientCoefficients J R gamma slot') := by
  apply Prod.ext
  · change gamma none + _ = gamma none + _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      simp only [ActualCanonical.singleton_global_adjustment]
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]
  · funext j
    change ActualCanonical.record names (occ j) (ambientCoefficients J R gamma slot j) =
      ActualCanonical.record names (occ' j) (ambientCoefficients J R gamma slot' j)
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      exact ActualCanonical.singleton_locality names _ _ _ _ _ (hsingle j hj)
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]

/-- Lemma 6.2 for the actual pullbacks in the shared F₂ coordinate model. -/
theorem canonical_private_input_locality [DecidableEq R]
    {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.canonical occ' names rhs
      (freePullback (fun j => toBit (rhs (occ' j))) J R gamma slot') := by
  rw [canonical_raw_pullback, canonical_raw_pullback]
  exact raw_data_locality J R names rhs occ occ' slot slot' gamma hfull hsingle

end
end UniqueGamesTheorem.Soundness.ActualCanonicalPullback

end

section

/-! Exact transport from genuine binary linear maps to the complete private rows
used by the conditional game. -/

namespace UniqueGamesTheorem.Soundness.BinaryRowTransport
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open ConditionalIncidences PartnerMapCoordinates

noncomputable section
attribute [local instance] Classical.propDecidable
variable {Q : Type}

theorem rowBits_zero : rowBits (0 : Q → F2) = ZeroInformation.zero := by
  funext q
  change toBit (0 : F2) = false
  decide

theorem rowBits_add (v w : Q → F2) : rowBits (v+w) = ZeroInformation.add (rowBits v) (rowBits w) := by
  funext q
  exact toBit_add _ _

theorem rowBits_smul (b : Bool) (v : Q → F2) :
    rowBits (ofBit b • v) = ZeroInformation.scale (rowBits v) b := by
  cases b <;> funext q <;> simp [rowBits, ZeroInformation.scale, ofBit, toBit]

theorem rowBits_list_sum {P : Type} (xs : List P) (f : P → Q → F2) :
    rowBits (xs.map f |>.sum) = ZeroInformation.rowSum xs (fun j => rowBits (f j)) := by
  induction xs with
  | nil => exact rowBits_zero
  | cons j xs ih =>
    simp only [List.map_cons, List.sum_cons, rowBits_add, ih, ZeroInformation.rowSum, List.foldr_cons]

theorem rowBits_sum {P : Type} [Fintype P] (f : P → Q → F2) :
    rowBits (∑ j, f j) = ZeroInformation.rowSum Finset.univ.toList (fun j => rowBits (f j)) := by
  rw [← Finset.sum_map_toList]
  exact rowBits_list_sum _ _

theorem actual_pullbackRow {k : Nat} [Fintype Q] [DecidableEq Q]
    (rhs : Fin k → Bool) (J : Finset (Fin k))
    (gamma : RawCoefficients J (Q → F2)) (slot : Fin k → PartnerProjection.Slot)
    (x : PartnerProjection.SourcePoint rhs) :
    rowBits (mapEquiv rhs J (Q → F2) gamma
      (PartnerLinear.projection rhs (activeOf J) slot x)) =
    ZeroInformation.pullbackRow Finset.univ.toList (membershipBool J)
      ((rowCoefficients J gamma) none)
      (fullCoefficient J (rowCoefficients J gamma) 0)
      (fullCoefficient J (rowCoefficients J gamma) 1)
      (singleCoefficient J (rowCoefficients J gamma))
      (fun j => ConcreteExtraction.slotIndex (slot j)) x.homogeneous
      (fun j => ConcreteExtraction.tripleCoordinates (x.coordinates j)) := by
  let f : PositionOutside J → Q → F2 := fun j =>
    ofBit (x.coordinates j.val).first • gamma (some (.inl (j,0))) +
      ofBit (x.coordinates j.val).second • gamma (some (.inl (j,1)))
  let g : PositionInside J → Q → F2 := fun j =>
    ofBit (PartnerProjection.retained (slot j.val) (x.coordinates j.val)) • gamma (some (.inr j))
  rw [pullback_expansion]
  change rowBits ((ofBit x.homogeneous • gamma none + ∑ j, f j) + ∑ j, g j) = _
  rw [add_assoc, ActualCanonicalPullback.sum_outside_inside J (Q → F2) f g,
    rowBits_add, rowBits_smul, rowBits_sum]
  unfold ZeroInformation.pullbackRow
  congr 1
  apply ZeroInformation.rowSum_congr
  intro j
  by_cases hj : j ∈ J
  · simp [g, hj, membershipBool, singleCoefficient, rowCoefficients,
      rowBits_smul, ConcreteExtraction.retained_coordinates]
  · simp [f, hj, membershipBool, fullCoefficient, rowCoefficients,
      rowBits_add, rowBits_smul, ConcreteExtraction.tripleCoordinates]

theorem actual_partnerRow {k : Nat} [Fintype Q] [DecidableEq Q]
    (rhs : Fin k → Bool) (J : Finset (Fin k))
    (gamma : RawCoefficients J (Q → F2))
    (y : PartnerProjection.PartnerPoint rhs (activeOf J)) :
    rowBits (mapEquiv rhs J (Q → F2) gamma y) =
    ZeroInformation.partnerRow Finset.univ.toList (membershipBool J)
      ((rowCoefficients J gamma) none)
      (fullCoefficient J (rowCoefficients J gamma) 0)
      (fullCoefficient J (rowCoefficients J gamma) 1)
      (singleCoefficient J (rowCoefficients J gamma)) y.homogeneous
      (fun j => ConcreteExtraction.tripleCoordinates (y.full j)) y.single := by
  let f : PositionOutside J → Q → F2 := fun j =>
    ofBit (y.full j.val).first • gamma (some (.inl (j,0))) +
      ofBit (y.full j.val).second • gamma (some (.inl (j,1)))
  let g : PositionInside J → Q → F2 := fun j =>
    ofBit (y.single j.val) • gamma (some (.inr j))
  rw [mapEquiv_expansion]
  change rowBits ((ofBit y.homogeneous • gamma none + ∑ j, f j) + ∑ j, g j) = _
  rw [add_assoc, ActualCanonicalPullback.sum_outside_inside J (Q → F2) f g,
    rowBits_add, rowBits_smul, rowBits_sum]
  unfold ZeroInformation.partnerRow
  congr 1
  apply ZeroInformation.rowSum_congr
  intro j
  by_cases hj : j ∈ J
  · simp [g, hj, membershipBool, singleCoefficient, rowCoefficients, rowBits_smul]
  · simp [f, hj, membershipBool, fullCoefficient, rowCoefficients,
      rowBits_add, rowBits_smul, ConcreteExtraction.tripleCoordinates]

end
end UniqueGamesTheorem.Soundness.BinaryRowTransport

end

section

/-! A partner target whose coordinates depend only on the displayed full/single
positions. It does not contain hidden occurrence identities or right-hand sides. -/

namespace UniqueGamesTheorem.Soundness.RawPartnerTarget
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open PartnerProjection PartnerMapCoordinates ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {R : Type} [AddCommGroup R] [Module F2 R]

theorem rawMap_pullback (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (Y : RawPoint J →ₗ[F2] R) :
    Y.comp (rawProjection rhsB J slot) =
      ActualCanonicalPullback.freePullback rhsB J R (gammaOfRawMap J Y) slot := by
  apply LinearMap.ext
  intro x
  change Y (pointEquiv rhsB J
      (PartnerLinear.projection rhsB (activeOf J) slot
        ((PartnerLinear.sourceLinearEquiv rhsB).symm x))) =
    mapEquiv rhsB J R (gammaOfRawMap J Y)
      (PartnerLinear.projection rhsB (activeOf J) slot
        ((PartnerLinear.sourceLinearEquiv rhsB).symm x))
  exact rawMap_on_partner rhsB J Y _

end
end UniqueGamesTheorem.Soundness.RawPartnerTarget

end

section

/-! Local extraction of the genuine linear row maps from complete supplied inputs. -/

namespace UniqueGamesTheorem.Soundness.ActualInputRows
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open ConditionalIncidences PartnerMapCoordinates RawPartnerTarget BinaryRowTransport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Q Id Name : Type}

theorem firstMap_eq (rhs : Id → Bool) (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (Z : ActualHomogeneous.E k →ₗ[F2] (Q → F2))
    (hZ : ∀ x, restrictedFirst rhs qa x = Z x) : firstMap rhs qa = Z := by
  have h : ∃ W : ActualHomogeneous.E k →ₗ[F2] (Q → F2),
      ∀ x, W x = restrictedFirst rhs qa x := ⟨Z, fun x => (hZ x).symm⟩
  unfold firstMap
  rw [dite_eq_left h]
  exact LinearMap.ext (fun x => (Classical.choose_spec h x).trans (hZ x))

theorem secondMap_eq (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) (Y : RawPoint J →ₗ[F2] (Q → F2))
    (hY : ∀ v, restrictedSecond J qb v = Y v) : secondMap J qb = Y := by
  have h : ∃ W : RawPoint J →ₗ[F2] (Q → F2),
      ∀ v, W v = restrictedSecond J qb v := ⟨Y, fun v => (hY v).symm⟩
  unfold secondMap
  rw [dite_eq_left h]
  exact LinearMap.ext (fun v => (Classical.choose_spec h v).trans (hY v))

/-- The first player's extraction on the actual sampled input equals `Y π`.
There is no assumption that an arbitrary input row is linear. -/
theorem firstMap_actual [Fintype Q] [DecidableEq Q]
    (J : Finset (Fin k)) (rhs : Id → Bool) (occ : Fin k → Id)
    (slot : Fin k → PartnerProjection.Slot) (Y : RawPoint J →ₗ[F2] (Q → F2)) :
    firstMap rhs (actualFirst J (rowCoefficients J (gammaOfRawMap J Y))
      (fun j => (occ j, ConcreteExtraction.slotIndex (slot j)))) =
      Y.comp (rawProjection (fun j => rhs (occ j)) J slot) := by
  apply firstMap_eq
  intro x
  let p := (PartnerLinear.sourceLinearEquiv (fun j => rhs (occ j))).symm x
  have h := actual_pullbackRow (fun j => rhs (occ j)) J (gammaOfRawMap J Y) slot p
  rw [← rawMap_on_partner (fun j => rhs (occ j)) J Y] at h
  funext q
  have he := congrArg ofBit (congrFun h q).symm
  simp only [rowBits, ofBit_toBit, restrictedFirst, actualFirst,
    ZeroInformation.firstInput, rawProjection, p, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap] at he ⊢
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 5

/-- The second player's extraction equals the genuine supplied raw target map. -/
theorem secondMap_actual [Fintype Q] [DecidableEq Q]
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (draw : Draw (Fin k) Id)
    (Y : RawPoint J →ₗ[F2] (Q → F2)) :
    secondMap J (actualSecond J names (rowCoefficients J (gammaOfRawMap J Y)) draw) = Y := by
  apply secondMap_eq
  intro v
  let y := (pointEquiv (fun _ : Fin k => false) J).symm v
  have h := actual_partnerRow (fun _ : Fin k => false) J (gammaOfRawMap J Y) y
  rw [← rawMap_on_partner (fun _ : Fin k => false) J Y] at h
  have hy : pointEquiv (fun _ : Fin k => false) J y = v :=
    (pointEquiv (fun _ : Fin k => false) J).apply_symm_apply v
  rw [hy] at h
  funext q
  have he := congrArg ofBit (congrFun h q).symm
  simpa only [rowBits, ofBit_toBit, restrictedSecond, actualSecond,
    ZeroInformation.secondInput, y] using he

end
end UniqueGamesTheorem.Soundness.ActualInputRows

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_RawPrivateTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The private Fourier table is defined from displayed data alone. Compatibility
with every hidden extension follows from the proved canonical locality theorem. -/

namespace UniqueGamesTheorem.Soundness.RawPrivateTable
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open PartnerProjection RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Id Name : Type}

theorem full_occurrence_eq_of_displayed_eq
    {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    {occ occ' : Fin k → Id} {slot slot' : Fin k → Slot}
    (h : displayed J names occ slot = displayed J names occ' slot')
    (j : Fin k) (hj : j ∉ J) : occ j = occ' j := by
  simpa [displayed, hj] using congrFun h j

theorem single_name_eq_of_displayed_eq
    {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    {occ occ' : Fin k → Id} {slot slot' : Fin k → Slot}
    (h : displayed J names occ slot = displayed J names occ' slot')
    (j : Fin k) (hj : j ∈ J) :
    names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j)) := by
  simpa [displayed, hj] using congrFun h j

theorem representative_display {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    (V : SupportedV J names) :
    displayed J names (representative V).1 (representative V).2 = V.val :=
  Classical.choose_spec V.property

variable (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
  {R D C Label : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]
  [DecidableEq Id] [DecidableEq Name]

theorem canonical_same_display (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (Y : RawPoint J →ₗ[F2] R)
    (h : displayed J names occ slot = displayed J names occ' slot') :
    ActualCanonical.canonical occ names rhs (Y.comp (projection J rhs occ slot)) =
      ActualCanonical.canonical occ' names rhs (Y.comp (projection J rhs occ' slot')) := by
  unfold projection
  rw [rawMap_pullback, rawMap_pullback]
  exact ActualCanonicalPullback.canonical_private_input_locality J R names rhs
    occ occ' slot slot' (gammaOfRawMap J Y)
    (full_occurrence_eq_of_displayed_eq h) (single_name_eq_of_displayed_eq h)

end
end UniqueGamesTheorem.Soundness.RawPrivateTable

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_SubsetIntersectionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Full slot indices and the actual partner law

Uniform indices at all positions restrict to uniform indices on an active set.
The explicit restriction/complement equivalence proves this sampling fact. The
dependent partner average then equals sampling the active set followed by all
slot indices, including unused indices outside the active set. Finally, the
coordinatewise occurrence/slot draw is related to that same law.
-/

namespace UniqueGamesTheorem.Soundness.PartnerFullSampling

open scoped BigOperators

noncomputable section

/-- Marginalizing the nonempty complement tuple gives the exact uniform law
on the active coordinates. This includes an empty active set or complement. -/
theorem expect_restrictIndices {P X : Type*} [Fintype P] [DecidableEq P]
    [Fintype X] [Nonempty X] (J : Finset P) (h : (↥J → X) → ℝ) :
    (𝔼 indices : P → X, h (restrictIndices J indices)) =
      𝔼 activeIndices : ↥J → X, h activeIndices := by
  calc
    (𝔼 indices : P → X, h (restrictIndices J indices)) =
        𝔼 parts : (↥J → X) × ({j : P // j ∉ J} → X), h parts.1 :=
      Fintype.expect_equiv (restrictionProductEquiv J) _ _ (fun _ => rfl)
    _ = 𝔼 activeIndices : ↥J → X, h activeIndices := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (↥J → X))
          (Finset.univ : Finset ({j : P // j ∉ J} → X))
          (fun parts => h parts.1))

end

end UniqueGamesTheorem.Soundness.PartnerFullSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ActualPointAnswers
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.secondInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Conversion of actual binary linear points to the named projection answers. -/

namespace UniqueGamesTheorem.Soundness.ActualPointAnswers
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget
open RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat}

private theorem triple_eq_of_first_second_parity (a b : PartnerProjection.Triple)
    (h₁ : a.first = b.first) (h₂ : a.second = b.second) (hp : parity a = parity b) : a = b := by
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  dsimp only at h₁ h₂
  subst b₁
  subst b₂
  simp only [parity] at hp
  have h₃ := congrArg (fun z => (a₁ ^^ a₂) ^^ z) hp
  have cancel (c d : Bool) : (c ^^ (c ^^ d)) = d := by
    cases c <;> cases d <;> rfl
  simp only [cancel] at h₃
  cases h₃
  rfl

/-- Inactive occurrences determine every full triple. The active right-hand
sides never enter the partner answer. -/
theorem secondAnswer_projection (rhs rhs' : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (x : ActualHomogeneous.E k)
    (hout : ∀ j, j ∉ J → rhs' j = rhs j) :
    secondAnswer rhs' J (rawProjection rhs J slot x) =
      ActualProjection.project (activeOf J) (fun j => ConcreteExtraction.slotIndex (slot j))
        (firstAnswer rhs x) := by
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  let y := (pointEquiv rhs' J).symm (rawProjection rhs J slot x)
  let z := PartnerLinear.projection rhs (activeOf J) slot p
  have hr : pointEquiv rhs' J y = pointEquiv rhs J z :=
    (pointEquiv rhs' J).apply_symm_apply _
  have hh : y.homogeneous = z.homogeneous := by
    have h := congrArg toBit (congrFun hr none)
    simpa only [pointEquiv_none, toBit_ofBit] using h
  have hfull : y.full = z.full := by
    funext j
    by_cases hj : j ∈ J
    · rw [y.full_zero j (by simp [activeOf, hj]), z.full_zero j (by simp [activeOf, hj])]
    · have h₁ : (y.full j).first = (z.full j).first := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(0:Fin 2)))))
        simpa only [pointEquiv_full_first, toBit_ofBit] using h
      have h₂ : (y.full j).second = (z.full j).second := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(1:Fin 2)))))
        simpa only [pointEquiv_full_second, toBit_ofBit] using h
      have hp : parity (y.full j) = parity (z.full j) := by
        rw [y.full_valid j (by simp [activeOf, hj]),
          z.full_valid j (by simp [activeOf, hj]), hout j hj, hh]
      exact triple_eq_of_first_second_parity _ _ h₁ h₂ hp
  have hsingle : y.single = z.single := by
    funext j
    by_cases hj : j ∈ J
    · have h := congrArg toBit (congrFun hr (some (.inr ⟨j,hj⟩)))
      simpa only [pointEquiv_single, toBit_ofBit] using h
    · rw [y.single_zero j (by simp [activeOf, hj]), z.single_zero j (by simp [activeOf, hj])]
  change (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single) = _
  rw [hh, hfull, hsingle]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext j i
      change ConcreteExtraction.tripleCoordinates
          (if decide (j ∈ J) then zeroTriple else p.coordinates j) i =
        (if decide (j ∈ J) then false else ConcreteExtraction.tripleCoordinates (p.coordinates j) i)
      cases decide (j ∈ J) <;> simp [ConcreteExtraction.tripleCoordinates, zeroTriple]
    · funext j
      change (if decide (j ∈ J) then retained (slot j) (p.coordinates j) else false) =
        (if decide (j ∈ J) then ConcreteExtraction.tripleCoordinates (p.coordinates j)
          (ConcreteExtraction.slotIndex (slot j)) else false)
      rw [ConcreteExtraction.retained_coordinates]

theorem displayedRhs_full {Id Name : Type} (rhs : Id → Bool)
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    displayedRhs rhs (RawPrivateTable.displayed J names occ slot) j = rhs (occ j) := by
  simp [displayedRhs, RawPrivateTable.displayed, hj]

/-- Actual point equality gives acceptance in the named verifier on complete
private inputs, with local answer conversions. -/
theorem actual_accepts {Q Id Name : Type} (J : Finset (Fin k))
    (g : IncidenceExtraction.Incidence Id Name)
    (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name)
    (slot : Fin k → Slot)
    (hquestion : qb.question = RawPrivateTable.displayed J g.name qa.question slot)
    (x : ActualHomogeneous.E k) (v : RawPoint J)
    (hone : sourceTau x = 1)
    (hprojection : rawProjection (fun j => g.rhs (qa.question j)) J slot x = v) :
    ActualProjection.accepts g (activeOf J) qa qb
      (firstAnswer (fun j => g.rhs (qa.question j)) x)
      (secondAnswer (displayedRhs g.rhs qb.question) J v) := by
  let p := (PartnerLinear.sourceLinearEquiv (fun j => g.rhs (qa.question j))).symm x
  have hp : p.homogeneous = true := by
    change toBit x.1 = true
    change x.1 = 1 at hone
    rw [hone]
    decide
  refine ⟨?_, hp, (fun j => ConcreteExtraction.slotIndex (slot j)), ?_, ?_⟩
  · intro j
    exact (ConcreteExtraction.parity_coordinates _).trans (p.valid j)
  · rw [hquestion]
    funext j
    by_cases hj : j ∈ J <;>
      simp [RawPrivateTable.displayed, ZeroInformation.partnerQuestion, activeOf, hj]
  · rw [← hprojection]
    exact secondAnswer_projection _ _ J slot x (fun j hj => by
      rw [hquestion]
      exact displayedRhs_full g.rhs J g.name qa.question slot j hj)

end
end UniqueGamesTheorem.Soundness.ActualPointAnswers

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_MaskMomentLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Clean

open Foundations.Games
open scoped BigOperators

noncomputable section

theorem product_mask {k : ℕ} (mask : Fin k → Bool) (ρ : ℝ) :
    (∏ i, if mask i then ρ else 1) = ρ ^ maskCount mask := by
  classical
  simp [maskCount, Finset.prod_ite]

/-- The finite product identity underlying the binomial generating function. -/
theorem iid_product_moment {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (f : Ω → ℝ) (k : ℕ) :
    (μ.iid k).expectation (fun x => ∏ i, f (x i)) = μ.expectation f ^ k := by
  classical
  unfold FiniteDistribution.expectation FiniteDistribution.iid
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]

theorem bernoulli_mask_moment (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (k : ℕ) (ρ : ℝ) :
    ((bernoulli p hp₀ hp₁).iid k).expectation (fun mask => ρ ^ maskCount mask) =
      (1 - p * (1 - ρ)) ^ k := by
  calc
    _ = ((bernoulli p hp₀ hp₁).iid k).expectation
        (fun mask => ∏ i, if mask i then ρ else 1) :=
      FiniteDistribution.expectation_congr _ (fun mask => (product_mask mask ρ).symm)
    _ = ((bernoulli p hp₀ hp₁).expectation (fun b => if b then ρ else 1)) ^ k :=
      iid_product_moment (bernoulli p hp₀ hp₁) (fun b : Bool => if b then ρ else 1) k
    _ = _ := by
      congr 1
      simp [FiniteDistribution.expectation, bernoulli]
      ring

variable {E : Type*} [Fintype E] [Nonempty E]

theorem clean_pushforward (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (origin : E) :
    (singletonSlopeLaw (E := E) β hβ₀ hβ₁).pushforward (cleanBit origin) =
      bernoulli (cleanProbability β E)
        (cleanProbability_nonneg hβ₀) (cleanProbability_le_one hβ₁) := by
  classical
  let μ := (singletonSlopeLaw (E := E) β hβ₀ hβ₁).pushforward (cleanBit origin)
  have ht : μ.weight true = cleanProbability β E := by
    simp [μ, FiniteDistribution.pushforward, singletonSlopeLaw,
      FiniteDistribution.product, Fintype.sum_prod_type,
      bernoulli, cleanBit, FiniteDistribution.uniform, cleanProbability, div_eq_mul_inv]
  apply FiniteDistribution.eq_of_weight_eq
  intro b
  cases b with
  | false =>
      change μ.weight false = 1 - cleanProbability β E
      have hn := μ.normalized
      simp only [Fintype.sum_bool] at hn
      linarith
  | true => exact ht

/-- In particular, the *whole* mask has the independent Bernoulli law. -/
theorem clean_mask_law (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).pushforward
        (fun sample i => cleanBit origin (sample i)) =
      (bernoulli (cleanProbability β E)
        (cleanProbability_nonneg hβ₀) (cleanProbability_le_one hβ₁)).iid k := by
  rw [← FiniteDistribution.iid_pushforward, clean_pushforward]

theorem clean_mask_moment (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) (ρ : ℝ) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => ρ ^ maskCount (fun i => cleanBit origin (sample i))) =
      (1 - cleanProbability β E * (1 - ρ)) ^ k := by
  rw [← FiniteDistribution.expectation_pushforward
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k)
    (fun sample i => cleanBit origin (sample i)) (fun mask => ρ ^ maskCount mask)]
  rw [clean_mask_law, bernoulli_mask_moment]

theorem cleanProbability_ge_of_card_le {β : ℝ} (hβ₀ : 0 ≤ β) {N : ℝ}
    (hcard : (Fintype.card E : ℝ) ≤ N) :
    β / N ≤ cleanProbability β E := by
  exact div_le_div_of_nonneg_left hβ₀
    (Nat.cast_pos.mpr Fintype.card_pos) hcard

/-- Larger clean probability decreases the moment for a rate in `[0,1]`. -/
theorem mask_rate_antitone {p q ρ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hqp : q ≤ p) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (k : ℕ) :
    (1 - p * (1 - ρ)) ^ k ≤ (1 - q * (1 - ρ)) ^ k := by
  have hl : 0 ≤ 1 - p * (1 - ρ) := by
    nlinarith [mul_nonneg hp₀ hρ₀]
  apply pow_le_pow_left₀ hl
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hqp (sub_nonneg.mpr hρ₁)) 1

/-- Section 5's numerical specialization. A bound on the number of possible
advice slopes gives a uniform bound over every fixed advice map. -/
theorem clean_mask_moment_le (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) {N : ℝ} (hcard : (Fintype.card E : ℝ) ≤ N) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => (1 - (1 : ℝ) / 3600) ^
          maskCount (fun i => cleanBit origin (sample i))) ≤
      (1 - (β / N) / 3600) ^ k := by
  rw [clean_mask_moment]
  have h := mask_rate_antitone (cleanProbability_nonneg (E := E) hβ₀)
    (cleanProbability_le_one (E := E) hβ₁)
    (cleanProbability_ge_of_card_le hβ₀ hcard)
    (ρ := 1 - (1 : ℝ) / 3600) (by norm_num) (by norm_num) k
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

/-- `2^(dim W + r_s)` is chosen before the particular advice-map rank. -/
theorem clean_mask_moment_le_dimension (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k dimW rs : ℕ) (hcard : Fintype.card E ≤ 2 ^ (dimW + rs)) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => (1 - (1 : ℝ) / 3600) ^
          maskCount (fun i => cleanBit origin (sample i))) ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  apply clean_mask_moment_le β hβ₀ hβ₁ origin k
  exact_mod_cast hcard

end
end UniqueGamesTheorem.Clean

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ProductLaw
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Weighted conditional product law for the v2 clean coordinates

The equation distribution is arbitrary.  All identities below are identities
of finite sums of its actual weights, rather than a reduction to uniform
occurrence sampling.  The clean set is fixed by independently sampled advice;
the only subsequently exposed question data lie outside that set.  Conditioning
on such data preserves the entire joint law of the clean questions.
-/

namespace UniqueGamesTheorem.Clean.ProductLaw

open scoped BigOperators
open Foundations.Games
open Soundness.ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P Q S : Type} [Fintype P] [DecidableEq P] [Fintype Q] [Fintype S]

/-- Independent weighted sampling splits into independent clean and nonclean
parts. This identity proves, rather than assumes, their independence. -/
theorem table_split (μ : P → FiniteDistribution Q) (K : Finset P) :
    (FiniteDistribution.table μ).transport (splitCoordinates K) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).product
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro pieces
  change (∏ i, (μ i).weight ((splitCoordinates K).symm pieces i)) =
    (∏ i : PositionInside K, (μ i.val).weight (pieces.1 i)) *
      ∏ i : PositionOutside K, (μ i.val).weight (pieces.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : P => i ∈ K)
    (fun i => (μ i).weight ((splitCoordinates K).symm pieces i))
  have hi : Subtype.fintype (fun i : P => i ∈ K) =
      Finset.Subtype.fintype K := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : PositionInside K,
        (μ i.val).weight ((splitCoordinates K).symm pieces i.val)) *
        ∏ i : PositionOutside K,
          (μ i.val).weight ((splitCoordinates K).symm pieces i.val) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [splitCoordinates, Equiv.piEquivPiSubtypeProd, i.property]

theorem probability_product_and (μ : FiniteDistribution Q) (ν : FiniteDistribution S)
    (event : Q → Bool) (given : S → Bool) :
    (μ.product ν).probability (fun x => event x.1 && given x.2) =
      μ.probability event * ν.probability given := by
  classical
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    Fintype.sum_prod_type]
  calc
    _ = ∑ q, ∑ s, (if event q then μ.weight q else 0) *
        (if given s then ν.weight s else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro s _
      cases event q <;> cases given s <;> simp
    _ = _ := by rw [Finset.sum_mul_sum]

/-- Exact factorization for an arbitrary joint event of clean coordinates and
an arbitrary observation/event depending only on the nonclean coordinates. -/
theorem table_inside_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (event : (PositionInside K → Q) → Bool)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability
        (fun x => event (fun i => x i.val) && given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event *
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  rw [← probability_product_and, ← table_split]
  exact (FiniteDistribution.probability_transport (FiniteDistribution.table μ)
    (splitCoordinates K) (fun pieces => event pieces.1 && given pieces.2)).symm

theorem table_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability (fun x => given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  simpa using table_inside_outside μ K (fun _ => true) given

/-- The normalized conditional law is the ordinary independent product law.
The only hypothesis is that the observed outside event has positive mass. -/
theorem conditioned_inside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (positive : 0 < (FiniteDistribution.table μ).probability
      (fun x => given (fun i => x i.val)))
    (event : (PositionInside K → Q) → Bool) :
    ((FiniteDistribution.table μ).condition
      (fun x => given (fun i => x i.val)) positive).probability
        (fun x => event (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event := by
  rw [FiniteDistribution.probability_condition]
  simp_rw [Bool.and_comm (given _)]
  rw [table_inside_outside, table_outside]
  have hne : (FiniteDistribution.table
      (fun i : PositionOutside K => μ i.val)).probability given ≠ 0 := by
    rw [table_outside] at positive
    exact ne_of_gt positive
  exact mul_div_cancel_right₀ _ hne

/-- Reindexing a finite coordinate set gives the usual `iid` law on `Fin r`. -/
theorem table_reindex (μ : FiniteDistribution Q) {A : Type} [Fintype A] [DecidableEq A]
    {r : ℕ} (e : Fin r ≃ A) :
    (FiniteDistribution.table (fun _ : A => μ)).transport (coordinateReindex e) =
      μ.iid r := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ a, μ.weight (x (e.symm a))) = ∏ i, μ.weight (x i)
  exact e.symm.prod_comp (fun i => μ.weight (x i))

/-- Fixed advice, intercept and nonclean data preserve precisely the repeated
incidence law for arbitrary occurrence weights. Repeated IDs are permitted. -/
theorem conditioned_incidence_reindex
    {O N D : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [Zero D] [DecidableEq D]
    (μ : FiniteDistribution (O × Fin 3))
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)))
    {r : ℕ} (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (event : (Fin r → O × N) → Bool) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed))
        positive).probability
          (fun x => event (fun i => incidence name (x (e i).val))) =
      ((μ.pushforward (incidence name)).iid r).probability event := by
  classical
  let given : (PositionOutside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => decide ((fun i => incidence name (x i)) = observed)
  let insideEvent : (PositionInside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => event (fun i => incidence name (x (e i)))
  have h := conditioned_inside (fun _ : P => μ) (zeroSet J gamma)
    given positive insideEvent
  change _ = _ at h
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.probability_pushforward]
  rw [← table_reindex μ e, FiniteDistribution.probability_transport]
  exact h

end
end UniqueGamesTheorem.Clean.ProductLaw

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_WeightedPartition
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Weighted total probability for the public clean-coordinate observation.
The observation may have zero-probability fibres. Only its positive fibres
require a conditional bound; the identity itself is proved from finite sums.
-/

namespace UniqueGamesTheorem.Clean.WeightedPartition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]

theorem sum_fibre_inter (μ : FiniteDistribution Ω) (observe : Ω → H)
    (event : Ω → Bool) :
    (∑ h, μ.probability (fun x => fibre observe h x && event x)) =
      μ.probability event := by
  classical
  unfold FiniteDistribution.probability fibre
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : event x = true <;> simp [hx]

theorem sum_fibre_bound (μ : FiniteDistribution Ω) (observe : Ω → H)
    (bound : H → ℝ) :
    (∑ h, μ.probability (fibre observe h) * bound h) =
      μ.expectation (fun x => bound (observe x)) := by
  classical
  unfold FiniteDistribution.probability FiniteDistribution.expectation fibre
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq, ite_mul, zero_mul]
  simp

/-- The averaging step for a genuine weighted observation. No conditional
independence or law-of-total-probability equality is supplied as a premise. -/
theorem probability_le_conditional_bounds (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : H → ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound h) :
    μ.probability event ≤ μ.expectation (fun x => bound (observe x)) := by
  rw [← sum_fibre_inter μ observe event, ← sum_fibre_bound μ observe bound]
  apply Finset.sum_le_sum
  intro h _
  by_cases positive : 0 < μ.probability (fibre observe h)
  · rw [μ.probability_inter_eq_mul_conditional (fibre observe h) event positive]
    exact mul_le_mul_of_nonneg_left (conditional h positive) positive.le
  · have zero : μ.probability (fibre observe h) = 0 :=
      le_antisymm (le_of_not_gt positive) (μ.probability_nonnegative _)
    rw [μ.probability_and_eq_zero_of_probability_eq_zero (fibre observe h) event zero,
      zero, zero_mul]

/-- A constant bound survives arbitrary public outside observations. -/
theorem probability_le_of_conditional_le (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound) :
    μ.probability event ≤ bound := by
  have estimate := probability_le_conditional_bounds μ observe event
    (fun _ => bound) conditional
  have constant : μ.expectation (fun _ => bound) = bound := by
    rw [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]
  simpa only [constant] using estimate

end
end UniqueGamesTheorem.Clean.WeightedPartition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ConditionalSimulationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The genuine conditional experiment is the reconstructed repeated-game law. -/

namespace UniqueGamesTheorem.Soundness.ConditionalGameLaw
open scoped BigOperators
open Foundations.Games
open ConditionalIncidences ConditionalSimulation IncidenceExtraction RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualWin_iff_reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (sample : RawObservationFibre J g.name gamma observed) :
    actualWin J g gamma strategy sample.val.2 ↔
      reconstructedEvent J g gamma observed reference e strategy
        (fun i => incidence g.name (sample.val.2 (e i).val)) := by
  unfold actualWin reconstructedEvent
  simp only [incidence, Equiv.apply_symm_apply]
  rw [localFirstFromH_correct J g.name gamma observed distinct reference sample,
    localSecondFromH_correct J g.name gamma observed reference sample]

end
end UniqueGamesTheorem.Soundness.ConditionalGameLaw

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_UpperBound
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Clean.UpperBound

open scoped BigOperators
open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq R] [Fintype N] in
private theorem reference_of_positive
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (name : O → Fin 3 → N) (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) name draw = observed))) :
    Nonempty (RawObservationFibre J name gamma observed) := by
  classical
  have exists_draw : ∃ draw : Draw P O,
      outsideRecord (zeroSet J gamma) name draw = observed := by
    by_contra h
    have absent : ∀ draw : Draw P O,
        outsideRecord (zeroSet J gamma) name draw ≠ observed := by
      simpa only [not_exists] using h
    simp [FiniteDistribution.probability, absent] at positive
  obtain ⟨draw, equality⟩ := exists_draw
  exact ⟨⟨(gamma, draw), rfl, equality⟩⟩

/-- On each positive public observation fibre, the full agreement event is
bounded by ordinary repetition. The reference draw is fixed public padding,
not an extra input depending on the still hidden question pair. -/
theorem conditioned_success_le_repeated_value_with_reference
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed)))
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  classical
  let event : (Fin (zeroSet J gamma).card → O × N) → Bool :=
    fun questions => decide (reconstructedEvent J g gamma observed reference e strategy questions)
  have agree : ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) =
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability
      (fun draw => event (fun i => incidence g.name (draw (e i).val))) := by
    unfold FiniteDistribution.probability FiniteDistribution.condition
    apply Finset.sum_congr rfl
    intro draw _
    by_cases hdraw : outsideRecord (zeroSet J gamma) g.name draw = observed
    · let sample : RawObservationFibre J g.name gamma observed :=
        ⟨(gamma, draw), rfl, hdraw⟩
      have equivalent : actualWin J g gamma strategy draw ↔
          reconstructedEvent J g gamma observed reference e strategy
            (fun i => incidence g.name (draw (e i).val)) :=
        actualWin_iff_reconstructedEvent J g gamma observed reference e strategy distinct sample
      simp only [event, decide_eq_true_eq, equivalent]
    · simp [hdraw]
  have distribution_law :=
    ProductLaw.conditioned_incidence_reindex μ J g.name gamma observed positive e event
  apply (le_of_eq (agree.trans distribution_law)).trans
  let G := (incidenceGame g (μ.pushforward (incidence g.name))).repetition (zeroSet J gamma).card
  let simulation := actualLocalSimulation J g gamma observed reference
    (μ.pushforward (incidence g.name)) e
  let induced := Simulation.strategyPair (simulation.induced strategy)
  refine le_trans ?_ (G.success_le_value induced)
  change ((μ.pushforward (incidence g.name)).iid (zeroSet J gamma).card).probability event ≤
    (((μ.pushforward (incidence g.name)).iid (zeroSet J gamma).card).transport
      (Game.tupleQuestionEquiv (zeroSet J gamma).card)).probability (G.wins induced)
  rw [FiniteDistribution.probability_transport]
  apply FiniteDistribution.probability_mono
  intro questions hwin
  have houter : strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (simulation.questionA (fun i => (questions i).1))
      (simulation.questionB (fun i => (questions i).2)) :=
    of_decide_eq_true hwin
  exact simulation.induced_wins strategy _ _ houter

theorem conditioned_success_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed)))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  classical
  let reference := Classical.choice (reference_of_positive μ J g.name gamma observed positive)
  let e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma) :=
    (Fintype.equivFinOfCardEq (by simp [PositionInside])).symm
  exact conditioned_success_le_repeated_value_with_reference
    μ J g gamma observed positive reference e strategy distinct

/-- All outside observations are genuinely averaged with their actual weights.
The result permits arbitrary repeated occurrence IDs and correlated local
answers across the entire clean tuple. -/
theorem fixed_advice_success_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    fixedAdviceSuccess μ J g gamma strategy ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  unfold fixedAdviceSuccess
  apply WeightedPartition.probability_le_of_conditional_le
    _ (outsideRecord (zeroSet J gamma) g.name)
  intro observed positive
  exact conditioned_success_le_repeated_value μ J g gamma observed positive strategy distinct

end
end UniqueGamesTheorem.Clean.UpperBound

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_Experiment
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

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

namespace UniqueGamesTheorem.Clean.Experiment

open scoped BigOperators
open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw

noncomputable section

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq R] in
/-- The actual zero coefficient set is exactly the clean mask counted by the
Bernoulli law. The homogeneous intercept and full columns never enter it. -/
theorem zeroSet_eq_cleanMask {k : ℕ} (extra : Additional k R) (seed : SparseSeed k R) :
    zeroSet (singletonSet seed) (coefficients extra seed) =
      Finset.univ.filter (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i) = true) := by
  classical
  ext i
  rw [mem_zeroSet]
  simp [singletonSet, coefficients, cleanBit]
  intro _
  rfl

omit [DecidableEq R] in
theorem zeroSet_card {k : ℕ} (extra : Additional k R) (seed : SparseSeed k R) :
    (zeroSet (singletonSet seed) (coefficients extra seed)).card =
      maskCount (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i)) := by
  rw [zeroSet_eq_cleanMask]
  rfl

private theorem expectation_mono {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

private theorem expectation_const {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (c : ℝ) : μ.expectation (fun _ => c) = c := by
  rw [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]

/-- Exact clean-coordinate upper bound for arbitrary weighted occurrences.
The sole external theorem input `rate` concerns the genuine classical repeated
game, so its alphabet dependence cannot be concealed in this interface. -/
theorem success_le_of_repetition (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (ρ : ℝ)
    (rate : ∀ n, ((incidenceGame g (μ.pushforward (incidence g.name))).repetition n).value ≤ ρ ^ n) :
    success k μ g extraLaw β hβ₀ hβ₁ strategy ≤
      (1 - (β / (Fintype.card (Coefficient R) : ℝ)) * (1 - ρ)) ^ k := by
  unfold success
  calc
    _ ≤ extraLaw.expectation (fun _ =>
      (1 - (β / (Fintype.card (Coefficient R) : ℝ)) * (1 - ρ)) ^ k) := by
      apply expectation_mono
      intro extra
      calc
        _ ≤ ((singletonSlopeLaw (E := Coefficient R) β hβ₀ hβ₁).iid k).expectation
            (fun seed => ρ ^ maskCount (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i))) := by
          apply expectation_mono
          intro seed
          have bound := (UpperBound.fixed_advice_success_le_repeated_value μ
            (singletonSet seed) g (coefficients extra seed) (strategy extra seed) distinct).trans (rate _)
          simpa only [zeroSet_card] using bound
        _ = _ := clean_mask_moment β hβ₀ hβ₁ (ZeroInformation.zero : Coefficient R) k ρ
    _ = _ := expectation_const _ _

end
end UniqueGamesTheorem.Clean.Experiment

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_IncidenceGap
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The weighted equation-versus-variable game for a three-variable parity system.
An occurrence is sampled with its given weight and one of its three positions is
sampled uniformly. Alice sees the occurrence and Bob sees only the variable
name. Distinct positions make the predicate a partial projection. The loss of a
factor of three in the gap is proved directly by counting the three positions.
No PCP hardness statement or parallel-repetition bound is a premise here.
-/

namespace UniqueGamesTheorem.Clean.IncidenceGap

open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Soundness.IncidenceExtraction (Incidence Triple xorTriple)
open scoped BigOperators

noncomputable section

variable {O N : Type} [Fintype O] [Fintype N]

attribute [local instance] OAI.UniqueGamesTheorem.Clean.IncidenceGap.accepts_decidable
theorem game_isProjection (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    UniqueGamesTheorem.Repetition.IsProjection (game g ω) := by
  intro o n a b b' hb hb'
  obtain ⟨i, hi, _, hai⟩ := (game_accepts_iff g ω o n a b).mp hb
  obtain ⟨j, hj, _, haj⟩ := (game_accepts_iff g ω o n a b').mp hb'
  have hij := distinct o i j (hi.trans hj.symm)
  subst j
  exact hai.symm.trans haj

theorem paritySuccess_le_parityValue (g : Incidence O N) (ω : FiniteDistribution O)
    (b : N → Bool) : paritySuccess g ω b ≤ parityValue g ω := by
  classical
  exact Finset.le_sup' (paritySuccess g ω) (Finset.mem_univ b)

/-- If Bob violates the equation, at most two of Alice's three coordinates can
agree with him while satisfying the required parity. -/
theorem local_count_bound (a b : Triple) (rhs : Bool) :
    (∑ i : Fin 3, if xorTriple a = rhs ∧ a i = b i then (1 : ℝ) else 0) ≤
      2 + if xorTriple b = rhs then (1 : ℝ) else 0 := by
  rw [Fin.sum_univ_three]
  by_cases ha : xorTriple a = rhs
  · by_cases hb : xorTriple b = rhs
    · simp only [ha, hb, true_and, ite_true, if_true]
      split_ifs <;> norm_num
    · by_cases h0 : a 0 = b 0 <;> by_cases h1 : a 1 = b 1 <;>
        by_cases h2 : a 2 = b 2 <;> simp_all [xorTriple] <;> norm_num
  · simp only [ha, false_and, ite_false, zero_add]
    split_ifs <;> norm_num

theorem game_success_eq_slot_average (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (a : O → Triple) (b : N → Bool) :
    (game g ω).success (a, b) =
      ∑ o, ω.weight o * ((∑ i : Fin 3,
        if g.accepts o i (a o) (b (g.name o i)) then (1 : ℝ) else 0) / 3) := by
  classical
  unfold Game.success
  change ((slotLaw ω).pushforward (fun q => (q.1, g.name q.1 q.2))).probability _ = _
  rw [FiniteDistribution.probability_pushforward]
  simp only [FiniteDistribution.probability, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Game.wins, game, decide_eq_true_eq, slotLaw_weight,
    Incidence.namedAccepts_iff_accepts g distinct]
  by_cases h : g.accepts o i (a o) (b (g.name o i)) <;> simp [h, div_eq_mul_inv]

theorem game_success_le_two_add_parity_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (a : O → Triple) (b : N → Bool) :
    (game g ω).success (a, b) ≤ (2 + paritySuccess g ω b) / 3 := by
  classical
  rw [game_success_eq_slot_average g ω distinct]
  calc
    _ ≤ ∑ o, ω.weight o * ((2 + if xorTriple (fun i => b (g.name o i)) =
        g.rhs o then (1 : ℝ) else 0) / 3) := by
      apply Finset.sum_le_sum
      intro o _
      apply mul_le_mul_of_nonneg_left _ (ω.nonnegative o)
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 3)
      exact local_count_bound (a o) (fun i => b (g.name o i)) (g.rhs o)
    _ = (2 + paritySuccess g ω b) / 3 := by
      simp_rw [← mul_div_assoc, mul_add]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ω.normalized]
      simp only [one_mul, paritySuccess, FiniteDistribution.probability,
        decide_eq_true_eq, mul_ite, mul_one, mul_zero]

theorem game_value_le_one_sub_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    (game g ω).value ≤ 1 - (1 - parityValue g ω) / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro s
  have h := game_success_le_two_add_parity_third g ω distinct s.1 s.2
  have hv := paritySuccess_le_parityValue g ω s.2
  linarith

theorem game_value_le_fourteen_fifteenths
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : parityValue g ω ≤ (4 : ℝ) / 5) :
    (game g ω).value ≤ (14 : ℝ) / 15 := by
  have h := game_value_le_one_sub_third g ω distinct
  linarith

end
end UniqueGamesTheorem.Clean.IncidenceGap

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_CoefficientSampling
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Uniform raw advice coefficients obtained by discarding unused flat coordinates.
The intercept, both full columns at every position, and one singleton column at
every position are independent. For a fixed singleton set, selecting the used
columns gives exactly the uniform law on the dynamic raw coefficient type.
The identity holds for every joint test function, not merely for marginals.
-/

namespace UniqueGamesTheorem.Clean.CoefficientSampling

open Foundations.Games
open Soundness.ConditionalIncidences
open Soundness.PartnerFullSampling
open scoped BigOperators

noncomputable section

variable {P C : Type} [Fintype P] [DecidableEq P] [Fintype C] [Nonempty C]

/-- The complement restriction is also uniform, including an empty complement. -/
theorem expect_outside (J : Finset P) (f : (PositionOutside J → C) → ℝ) :
    (𝔼 full : P → C, f (fun j => full j.val)) =
      𝔼 outside : PositionOutside J → C, f outside := by
  calc
    _ = 𝔼 parts : (PositionInside J → C) × (PositionOutside J → C), f parts.2 :=
      Fintype.expect_equiv (restrictionProductEquiv J) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (PositionInside J → C))
          (Finset.univ : Finset (PositionOutside J → C)) (fun parts => f parts.2))

omit [Nonempty C] in
theorem expect_rawCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (𝔼 gamma : RawCoefficients J C, F gamma) =
      𝔼 intercept : C, 𝔼 full : PositionOutside J → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm (intercept, full, single)) := by
  calc
    _ = 𝔼 parts : C × ((PositionOutside J → C × C) × (PositionInside J → C)),
        F ((coefficientProductEquiv J).symm parts) :=
      Fintype.expect_equiv (coefficientProductEquiv J) _ _ (fun _ => by simp)
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      apply Finset.expect_congr rfl
      intro intercept _
      rw [← Finset.univ_product_univ, Finset.expect_product]

/-- Sampling all columns and then discarding unused ones has exactly the
uniform joint law on the coefficients used by this singleton set. -/
theorem expect_selectCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (𝔼 extra : C × (P → C × C), 𝔼 single : P → C,
      F (selectCoefficients J extra single)) =
      𝔼 gamma : RawCoefficients J C, F gamma := by
  calc
    _ = 𝔼 intercept : C, 𝔼 full : P → C × C, 𝔼 single : P → C,
        F (selectCoefficients J (intercept, full) single) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = 𝔼 intercept : C, 𝔼 full : P → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm
            (intercept, (fun i => full i.val), single)) := by
      apply Finset.expect_congr rfl
      intro intercept _
      apply Finset.expect_congr rfl
      intro full _
      exact expect_restrictIndices J (fun single =>
        F ((coefficientProductEquiv J).symm (intercept, (fun i => full i.val), single)))
    _ = 𝔼 intercept : C, 𝔼 full : PositionOutside J → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm (intercept, full, single)) := by
      apply Finset.expect_congr rfl
      intro intercept _
      exact expect_outside J (fun full => 𝔼 single : PositionInside J → C,
        F ((coefficientProductEquiv J).symm (intercept, full, single)))
    _ = _ := (expect_rawCoefficients J F).symm

private theorem uniform_expectation_eq_expect {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) : (FiniteDistribution.uniform X).expectation f = 𝔼 x : X, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

theorem uniform_selectCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (FiniteDistribution.uniform (C × (P → C × C))).expectation (fun extra =>
      (FiniteDistribution.uniform (P → C)).expectation (fun single =>
        F (selectCoefficients J extra single))) =
      (FiniteDistribution.uniform (RawCoefficients J C)).expectation F := by
  simp_rw [uniform_expectation_eq_expect]
  exact expect_selectCoefficients J F

end
end UniqueGamesTheorem.Clean.CoefficientSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_NativeExperiment
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Clean.NativeExperiment

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Experiment
open scoped BigOperators

noncomputable section

private theorem expectation_transport {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (e : X ≃ Y) (f : Y → ℝ) :
    (μ.transport e).expectation f = μ.expectation (fun x => f (e x)) := by
  unfold FiniteDistribution.expectation FiniteDistribution.transport
  exact Fintype.sum_equiv e.symm _ _ (fun _ => by simp)

theorem iid_product_split {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (k : ℕ) :
    ((μ.product ν).iid k).transport (Game.tupleQuestionEquiv k) =
      (μ.iid k).product (ν.iid k) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro pair
  change (∏ i, μ.weight (pair.1 i) * ν.weight (pair.2 i)) =
    (∏ i, μ.weight (pair.1 i)) * ∏ i, ν.weight (pair.2 i)
  exact Finset.prod_mul_distrib

theorem expectation_iid_product {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (k : ℕ)
    (f : (Fin k → X × Y) → ℝ) :
    ((μ.product ν).iid k).expectation f =
      (μ.iid k).expectation (fun x =>
        (ν.iid k).expectation (fun y => f (fun i => (x i, y i)))) := by
  have law := expectation_transport ((μ.product ν).iid k)
    (Game.tupleQuestionEquiv k) (fun pair => f (fun i => (pair.1 i, pair.2 i)))
  rw [iid_product_split, FiniteDistribution.expectation_product] at law
  exact law.symm

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem success_eq_flat (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : MaskStrategy k R O N) :
    success k μ g β hβ₀ hβ₁ strategy =
      Experiment.success k μ g (FiniteDistribution.uniform (Additional k R))
        β hβ₀ hβ₁ (liftStrategy strategy) := by
  unfold success Experiment.success singletonSlopeLaw
  symm
  calc
    _ = (FiniteDistribution.uniform (Additional k R)).expectation fun extra =>
        ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
          (FiniteDistribution.uniform (Fin k → Coefficient R)).expectation fun single =>
            UpperBound.fixedAdviceSuccess μ (maskSet mask) g
              (CoefficientSampling.selectCoefficients (maskSet mask) extra single)
              (strategy mask (CoefficientSampling.selectCoefficients (maskSet mask) extra single)) := by
      apply FiniteDistribution.expectation_congr
      intro extra
      rw [expectation_iid_product, FiniteDistribution.iid_uniform]
      apply FiniteDistribution.expectation_congr
      intro mask
      apply FiniteDistribution.expectation_congr
      intro single
      have hgamma : coefficients extra (fun i => (mask i, single i)) =
          CoefficientSampling.selectCoefficients (maskSet mask) extra single := by
        funext slot
        cases slot with
        | none => rfl
        | some slot =>
          cases slot with
          | inl pair => rfl
          | inr i => rfl
      change UpperBound.fixedAdviceSuccess μ (maskSet mask) g
        (coefficients extra (fun i => (mask i, single i)))
        (strategy mask (coefficients extra (fun i => (mask i, single i)))) = _
      rw [hgamma]
    _ = ((bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Additional k R)).expectation fun extra =>
          (FiniteDistribution.uniform (Fin k → Coefficient R)).expectation fun single =>
            UpperBound.fixedAdviceSuccess μ (maskSet mask) g
              (CoefficientSampling.selectCoefficients (maskSet mask) extra single)
              (strategy mask (CoefficientSampling.selectCoefficients (maskSet mask) extra single))) :=
      FiniteDistribution.expectation_comm _ _ _
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro mask
      exact CoefficientSampling.uniform_selectCoefficients (maskSet mask)
        (fun gamma => UpperBound.fixedAdviceSuccess μ (maskSet mask) g gamma (strategy mask gamma))

end
end UniqueGamesTheorem.Clean.NativeExperiment

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_TensorAlgebraLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Alphabet-independent repetition of ordinary finite projection games.

The game is the actual finite question distribution and its local acceptance
predicate. The proof bounds nonnegative vector assignments by finite
thresholding and correlated sampling, factors each unrestricted product
strategy through that bound, and iterates the resulting collision contraction.
No repetition bound, decoder certificate, or alphabet-size budget is a premise.

The deterministic-predicate game interface permits arbitrary real question
weights. Distinct hidden constraints on the same question pair are not encoded
by this interface. Both v2 uses have a unique predicate for each question pair:
the distinct-position equation--variable game and the final simple graph.
-/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem clean_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    (hvalue : G.value ≤ (14 : ℝ) / 15) :
    (G.repetition n).value ≤ (1 - (1 : ℝ) / 3600) ^ n := by
  have hv : G.value ≤ 1 - (1 : ℝ) / 15 := by
    convert hvalue using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have h := projection_repetition_value G hG n
    (gap := (1 : ℝ) / 15) (by norm_num) (by norm_num) hv
  norm_num at h ⊢
  exact h

end
end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualAdviceBridgeLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

namespace Clean.ActualAdviceBridge

open scoped BigOperators
open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Soundness.RawPartnerTarget Soundness.BinaryRowTransport
open AnswerBridge

attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]

theorem sample_question [Fintype Q] [DecidableEq Q]
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (gamma : RawCoefficients J (ZeroInformation.Bits Q)) (draw : Draw (Fin k) O) :
    (actualSecond J g.name gamma draw).question = (displayedQuestion g J draw).val := by
  funext j
  simp [actualSecond, ZeroInformation.secondInput, ZeroInformation.partnerQuestion,
    membershipBool, displayedQuestion, RawPrivateTable.supported,
    RawPrivateTable.displayed]

variable [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]

theorem uniform_maps_to_bits (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (F : RawCoefficients J (ZeroInformation.Bits Q) → ℝ) :
    (FiniteDistribution.uniform (RawPoint J →ₗ[F2] D)).expectation
      (fun Y => F (encodedMapCoefficients coordinates J Y)) =
      (FiniteDistribution.uniform (RawCoefficients J (ZeroInformation.Bits Q))).expectation F := by
  simp only [FiniteDistribution.expectation_uniform, ← Fintype.expect_eq_sum_div_card]
  exact Fintype.expect_equiv (mapBitsEquiv coordinates J) _ F (fun _ => rfl)

theorem expectation_mono {X : Type} [Fintype X] (μ : FiniteDistribution X)
    {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

end Clean.ActualAdviceBridge

namespace Clean.Bound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Experiment

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq O] [DecidableEq N] in
/-- The precise rate is obtained from the proved ordinary projection-game
bound, with no question-set or alphabet parameter in its base. -/
theorem repeated_incidence_value_le
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) (n : ℕ) :
    ((incidenceGame g ((IncidenceGap.slotLaw ω).pushforward (incidence g.name))).repetition n).value ≤
      (1 - (1 : ℝ) / 3600) ^ n := by
  change ((IncidenceGap.game g ω).repetition n).value ≤ _
  exact Repetition.clean_repetition_value (IncidenceGap.game g ω)
    (IncidenceGap.game_isProjection g ω distinct) n
    (IncidenceGap.game_value_le_fourteen_fifteenths g ω distinct hopt)

/-- A uniform bound on visible advice dimension makes the estimate independent
of the sampled map `A`. Apply with `Coefficient R ≃ W × range A`. -/
theorem clean_success_le_dimension (k : ℕ) (g : IncidenceExtraction.Incidence O N)
    (ω : FiniteDistribution O) (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card (Coefficient R) ≤ 2 ^ (dimW + rs)) :
    success k (IncidenceGap.slotLaw ω) g extraLaw β hβ₀ hβ₁ strategy ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  have comparison := clean_mask_moment_le_dimension β hβ₀ hβ₁
    (ZeroInformation.zero : Coefficient R) k dimW rs hcard
  rw [clean_mask_moment] at comparison
  have estimate := success_le_of_repetition k (IncidenceGap.slotLaw ω) g extraLaw
    β hβ₀ hβ₁ strategy distinct (1 - (1 : ℝ) / 3600)
    (repeated_incidence_value_le g ω distinct hopt)
  exact estimate.trans comparison

theorem native_clean_success_le_dimension (k : ℕ)
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : NativeExperiment.MaskStrategy k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card (Coefficient R) ≤ 2 ^ (dimW + rs)) :
    NativeExperiment.success k (IncidenceGap.slotLaw ω) g β hβ₀ hβ₁ strategy ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  rw [NativeExperiment.success_eq_flat]
  exact clean_success_le_dimension k g ω (FiniteDistribution.uniform (Additional k R))
    β hβ₀ hβ₁ (NativeExperiment.liftStrategy strategy) distinct hopt dimW rs hcard

end Clean.Bound

end UniqueGamesTheorem

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_AdviceImageLaw
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The exact visible-advice law for a fixed latent map

For every fixed binary-linear map `A`, including rank-deficient maps, a uniform
latent column has a uniform image in `range A`.  An explicit range/kernel
bijection proves the assertion simultaneously for every intercept and slope.
The final theorem starts with the actual pair of independently uniform linear
maps on the partner answer space and pushes it to independent uniform visible
coefficients in `W × range A`.  No full-rank or independence premise is assumed.
-/

namespace UniqueGamesTheorem.Clean.AdviceImageLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Soundness.ConditionalIncidences
open UniqueGamesTheorem.Soundness.PartnerMapCoordinates
open UniqueGamesTheorem.Foundations.Games

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K S W : Type} [AddCommGroup K] [Module F2 K]
  [AddCommGroup S] [Module F2 S]

/-- Exact pushforward law for all columns jointly, including the original
intercept. This implies every event identity, not just individual marginals. -/
theorem uniform_visible_coefficients {I : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (F : (I → W × A.range) → ℝ) :
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
      𝔼 visible : I → W × A.range, F visible := by
  calc
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
        𝔼 pieces : (I → W × A.range) × (I → A.ker), F pieces.1 :=
      Fintype.expect_equiv (coefficientsSplitEquiv I A) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (I → W × A.range))
          (Finset.univ : Finset (I → A.ker)) (fun pieces => F pieces.1))

/-- The worst-case codomain cardinality suffices; no rank estimate is needed. -/
theorem visible_card_le [Fintype W] [Fintype K] [Fintype S] (A : K →ₗ[F2] S) :
    Fintype.card (W × A.range) ≤ Fintype.card W * Fintype.card S := by
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul_left _
    (Fintype.card_le_of_injective (fun z : A.range => (z : S)) Subtype.val_injective)

theorem visible_card_binary_le [Fintype K] (w r : Nat)
    (A : K →ₗ[F2] (Fin r → F2)) :
    Fintype.card ((Fin w → F2) × A.range) ≤ 2 ^ (w + r) := by
  calc
    Fintype.card ((Fin w → F2) × A.range) ≤
        Fintype.card (Fin w → F2) * Fintype.card (Fin r → F2) :=
      visible_card_le A
    _ = 2 ^ (w + r) := by simp [F2, pow_add]

end

end UniqueGamesTheorem.Clean.AdviceImageLaw

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_SparseLawLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite calculation of projected total variation. The three singleton
lines are averaged before the divergence is taken; projection choices are
not part of the compared sample space. Coordinates are independently sampled
occurrences, irrespective of whether their equation IDs coincide.
-/

namespace UniqueGamesTheorem.Decoder.SparseLaw

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Information

noncomputable section

variable {α : Type*} [Fintype α]

section Singleton

variable (V : Type*) [Fintype V] [Zero V] [DecidableEq V]

theorem singletonSamplerWeights_eq (z : V × V) :
    singletonSamplerWeights V z = singletonPairWeights V z := by
  classical
  rcases z with ⟨x, y⟩
  have hleft : (∑ a : V, if (a, 0) = (x, y) then uniformWeights V a else 0) =
      if y = 0 then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hy : y = 0
    · simp [hy, uniformWeights]
    · simp [Prod.mk.injEq, Ne.symm hy, hy]
  have hright : (∑ a : V, if (0, a) = (x, y) then uniformWeights V a else 0) =
      if x = 0 then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hx : x = 0
    · simp [hx, uniformWeights]
    · simp [Prod.mk.injEq, Ne.symm hx, hx]
  have hdiag : (∑ a : V, if (a, a) = (x, y) then uniformWeights V a else 0) =
      if x = y then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hxy : x = y
    · simp [hxy, uniformWeights]
    · have hnone (a : V) : (a, a) ≠ (x, y) := by
        intro ha
        have he := Prod.mk.inj ha
        exact hxy (he.1.symm.trans he.2)
      simp [hnone, hxy]
  simp only [singletonSamplerWeights, hleft, hright, hdiag,
    singletonPairWeights, lineCount]
  split_ifs <;> ring

end Singleton

section Intercept

variable {V : Type*} [Fintype V] [AddGroup V] [DecidableEq V]

theorem uniform_intercept_pushforward (shift z : V) :
    (∑ t : V, if t + shift = z then uniformWeights V t else 0) =
      uniformWeights V z := by
  classical
  simp [← eq_sub_iff_add_eq, uniformWeights]

omit [Fintype α] in
theorem joint_intercept_pushforward (p : α → ℝ) (shift : α → V) (a : α) (z : V) :
    (∑ t : V, if t + shift a = z then p a * uniformWeights V t else 0) =
      p a * uniformWeights V z := by
  classical
  calc
    _ = p a * (∑ t : V, if t + shift a = z then uniformWeights V t else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      split <;> simp_all
    _ = _ := by rw [uniform_intercept_pushforward]

end Intercept

end
end UniqueGamesTheorem.Decoder.SparseLaw

end

section

namespace UniqueGamesTheorem.Decoder.ConstantSelection

open UniqueGamesTheorem.Foundations.Information
open SparseLaw

noncomputable section

theorem conditionalMass_pos {α : ℝ} (hα : 0 < α) (ell r : ℕ) :
    0 < conditionalMass α ell r := by
  unfold conditionalMass
  positivity

theorem variationBudget_suffices {α g₀ ε : ℝ} (hα : 0 < α) (ell r : ℕ)
    (hε : ε ≤ variationBudget α g₀ ell r) :
    (1 + α / 4) * ε ≤ α * g₀ * (1 / (2 : ℝ) ^ (ell * r)) / 8 := by
  have hd : 0 < 1 + α / 4 := by positivity
  have h := (le_div_iff₀ hd).mp hε
  calc
    (1 + α / 4) * ε = ε * (1 + α / 4) := mul_comm _ _
    _ ≤ visibleMass α g₀ ell r := h
    _ = α * g₀ * (1 / (2 : ℝ) ^ (ell * r)) / 8 := by
      unfold visibleMass
      ring

end
end UniqueGamesTheorem.Decoder.ConstantSelection

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_PaddedLaw
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual linear-map realization of the sparse padded-table experiment.
The finite sample has one independent full pair or singleton coefficient at
each occurrence position and one independent homogeneous intercept. Its map
is formed by composing a genuine map on the raw projected target with the
actual parity projection. The third position contributes its parity-dependent
intercept; it is not treated as a homogeneous two-coordinate projection.
-/

namespace UniqueGamesTheorem.Decoder.PaddedLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget RawMapLaw
open ActualCanonicalPullback
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePushforward

variable {α B : Type*} [Fintype α]

theorem pushforwardWeight_pi (p : α → ℝ) (f : α → B) (k : ℕ)
    (ys : Fin k → B) :
    pushforwardWeight (independentWeights p k) (fun xs i => f (xs i)) ys =
      independentWeights (pushforwardWeight p f) k ys := by
  classical
  simp only [pushforwardWeight, independentWeights]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro xs _
  simp only [Fintype.prod_ite_zero, funext_iff]
  split_ifs <;> rfl

theorem pushforwardWeight_joint_uniform_intercept {W : Type*} [Fintype W] [AddGroup W]
    (p : α → ℝ) (f : α → B) (shift : α → W) (z : W) (b : B) :
    pushforwardWeight (fun az : α × W => p az.1 * uniformWeights W az.2)
      (fun az => (az.2 + shift az.1, f az.1)) (z, b) =
        uniformWeights W z * pushforwardWeight p f b := by
  classical
  simp only [pushforwardWeight, Fintype.sum_prod_type]
  calc
    (∑ a : α, ∑ t : W,
        if (t + shift a, f a) = (z, b) then p a * uniformWeights W t else 0) =
      ∑ a : α, if f a = b then p a * uniformWeights W z else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : f a = b
        · simp only [Prod.mk.injEq, h, and_true, ite_true, if_true]
          exact joint_intercept_pushforward p shift a z
        · simp [Prod.mk.injEq, h]
    _ = uniformWeights W z * (∑ a : α, if f a = b then p a else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : f a = b <;> simp [h, mul_comm]

end FinitePushforward

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

theorem slotIndex_decodeSlot (i : Fin 3) : ConcreteExtraction.slotIndex (decodeSlot i) = i := by
  fin_cases i <;> rfl

omit [Module F2 V] in
theorem ambientCoefficients_draw (d : Fin k → BlockDraw V) (z : V) :
    ambientCoefficients (singletonPositions d) V (drawCoefficients d z) (drawSlots d) =
      fun j => blockAmbient (d j) := by
  funext j i
  cases hd : d j with
  | inl ab =>
      fin_cases i <;>
        simp [ambientCoefficients, singletonPositions, drawCoefficients, blockAmbient, hd]
  | inr ia =>
      simp [ambientCoefficients, singletonPositions, drawCoefficients, drawSlots,
        blockAmbient, hd, slotIndex_decodeSlot, Pi.single_apply]

theorem paddedMap_toCoefficients (rhs : Fin k → Bool) (d : Fin k → BlockDraw V)
    (z : V) :
    ActualEnumeration.toCoefficients k V (paddedMap rhs d z) =
      (z + interceptShift rhs d, fun j => blockSlopes (d j)) := by
  have hrep := raw_represents rhs (singletonPositions d) V (drawCoefficients d z) (drawSlots d)
  rw [ambientCoefficients_draw] at hrep
  have hc := ActualCanonical.extension_coefficients _ _ _ _ hrep
  have hmap : paddedMap rhs d z =
      freePullback rhs (singletonPositions d) V (drawCoefficients d z) (drawSlots d) := by
    unfold paddedMap
    rw [rawMap_pullback, coefficients_rawMap]
  rw [hmap]
  apply Prod.ext
  · exact hc.1
  · funext j
    exact Prod.ext (hc.2 j).1 (hc.2 j).2

/-- Uniform raw coefficients are exactly uniform genuine maps on the actual
projected target, for each fixed mask and projection choice. -/
theorem uniform_rawMaps [Fintype V] (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] V) → ℝ) :
    (𝔼 gamma : RawCoefficients J V, H (rawMap J V gamma)) = 𝔼 Y, H Y := by
  exact Fintype.expect_equiv (rawMapEquiv J V) _ H (fun _ => rfl)

omit [Module F2 V] in
theorem tupleDraw_ambient (J : Finset (Fin k)) (slot : Fin k → Slot)
    (a : RawTuple J V) :
    (fun j => blockAmbient (tupleDraw J slot a j)) =
      ambientCoefficients J V (rawTupleEquiv J a) slot := by
  funext j i
  by_cases hj : j ∈ J
  · simp [tupleDraw, hj, blockAmbient, ambientCoefficients, rawTupleEquiv, Pi.single_apply]
  · fin_cases i <;>
      simp [tupleDraw, hj, blockAmbient, ambientCoefficients, rawTupleEquiv]

theorem paddedMap_tupleDraw (rhs : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (a : RawTuple J V) :
    paddedMap rhs (tupleDraw J slot a) a.1 =
      (rawMap J V (rawTupleEquiv J a)).comp (rawProjection rhs J slot) := by
  have hr := raw_represents rhs J V (rawTupleEquiv J a) slot
  rw [← tupleDraw_ambient] at hr
  have hc := ActualCanonical.extension_coefficients _ _ _ _ hr
  apply (ActualEnumeration.coefficientEquiv k V).symm.injective
  change ActualEnumeration.toCoefficients k V _ = ActualEnumeration.toCoefficients k V _
  rw [paddedMap_toCoefficients, rawMap_pullback, coefficients_rawMap]
  apply Prod.ext
  · exact hc.1.symm
  · funext j
    exact Prod.ext (hc.2 j).1.symm (hc.2 j).2.symm

/-- Conditional on every fixed mask and position choice, independently
uniform full pairs/singletons and intercept give the uniform law on genuine
projected-target maps followed by the actual projection. -/
theorem uniform_fixed_projection_tuple [Fintype V] (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot : Fin k → Slot)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (𝔼 a : RawTuple J V, H (paddedMap rhs (tupleDraw J slot a) a.1)) =
      𝔼 Y : RawPoint J →ₗ[F2] V, H (Y.comp (rawProjection rhs J slot)) := by
  simp_rw [paddedMap_tupleDraw]
  exact Fintype.expect_equiv ((rawTupleEquiv J).trans (rawMapEquiv J V)) _ _ (fun _ => rfl)

section Law

variable [Fintype V]

omit [Module F2 V] in
theorem blockWeights_slopes (β : ℝ) (ab : V × V) :
    pushforwardWeight (blockWeights (V := V) β) blockSlopes ab =
      mixture β (singletonPairWeights V) ab := by
  have hfull : (∑ x : V × V, if blockSlopes (.inl x) = ab then
        blockWeights β (.inl x) else 0) = (1 - β) * uniformWeights (V × V) ab := by
    simp [blockWeights]
  have hsingle : (∑ ia : Fin 3 × V, if blockSlopes (.inr ia) = ab then
        blockWeights β (.inr ia) else 0) = β * singletonSamplerWeights V ab := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    simp only [blockSlopes_first, blockSlopes_second,
      blockSlopes_third, blockWeights]
    have hfactor (f : V → V × V) :
        (∑ a : V, if f a = ab then β / 3 * uniformWeights V a else 0) =
          (β / 3) * ∑ a : V, if f a = ab then uniformWeights V a else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split <;> simp_all
    simp only [hfactor, singletonSamplerWeights]
    ring
  unfold pushforwardWeight
  rw [Fintype.sum_sum_type]
  calc
    _ = (∑ x : V × V, if blockSlopes (.inl x) = ab then blockWeights β (.inl x) else 0) +
        (∑ ia : Fin 3 × V, if blockSlopes (.inr ia) = ab then blockWeights β (.inr ia) else 0) := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> split_ifs <;> rfl
    _ = _ := by rw [hfull, hsingle, singletonSamplerWeights_eq]; rfl

theorem paddedWeights_eq (rhs : Fin k → Bool) (β : ℝ)
    (a : ActualEnumeration.Coefficients k V) :
    paddedWeights rhs β a = uniformWeights V a.1 *
      independentWeights (mixture β (singletonPairWeights V)) k a.2 := by
  rcases a with ⟨z, slopes⟩
  unfold paddedWeights
  simp_rw [paddedMap_toCoefficients]
  unfold drawWeights
  have hj := pushforwardWeight_joint_uniform_intercept
    (independentWeights (blockWeights (V := V) β) k)
    (fun d j => blockSlopes (d j)) (interceptShift rhs) z slopes
  calc
    _ = uniformWeights V z * pushforwardWeight
        (independentWeights (blockWeights (V := V) β) k)
        (fun d j => blockSlopes (d j)) slopes := by
      convert hj using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := by
      rw [pushforwardWeight_pi]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact blockWeights_slopes β (slopes j)

theorem uniformWeights_prod {A B : Type*} [Fintype A] [Fintype B] (ab : A × B) :
    uniformWeights (A × B) ab = uniformWeights A ab.1 * uniformWeights B ab.2 := by
  simp [uniformWeights, Fintype.card_prod, Nat.cast_mul, one_div, mul_comm]

theorem totalVariation_uniform_front {A B : Type*} [Fintype A] [Nonempty A] [Fintype B]
    (p q : B → ℝ) :
    UniqueGamesTheorem.Foundations.Information.totalVariation
      (fun ab : A × B => uniformWeights A ab.1 * p ab.2)
      (fun ab : A × B => uniformWeights A ab.1 * q ab.2) =
        UniqueGamesTheorem.Foundations.Information.totalVariation p q := by
  unfold UniqueGamesTheorem.Foundations.Information.totalVariation
  rw [Fintype.sum_prod_type]
  simp only [← mul_sub, abs_mul, abs_of_nonneg (uniformWeights_pos _).le,
    ← Finset.mul_sum, ← Finset.sum_mul, (uniformWeights_isProbability (α := A)).2, one_mul]

theorem paddedWeights_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ) :
    UniqueGamesTheorem.Foundations.Information.totalVariation (paddedWeights (V := V) rhs β)
      (uniformWeights (ActualEnumeration.Coefficients k V)) =
        UniqueGamesTheorem.Foundations.Information.totalVariation
          (independentWeights (mixture β (singletonPairWeights V)) k)
          (uniformWeights (Fin k → V × V)) := by
  have hp : paddedWeights (V := V) rhs β = fun a => uniformWeights V a.1 *
      independentWeights (mixture β (singletonPairWeights V)) k a.2 := by
    funext a
    exact paddedWeights_eq rhs β a
  have hu : uniformWeights (ActualEnumeration.Coefficients k V) =
      fun a => uniformWeights V a.1 * uniformWeights (Fin k → V × V) a.2 := by
    funext a
    exact uniformWeights_prod a
  rw [hp, hu, totalVariation_uniform_front]

omit [AddCommGroup V] [Module F2 V] in
theorem blockWeights_choice_mixture (β : ℝ) (d : BlockDraw V) :
    blockWeights β d = ∑ c : ProjectionChoice, choiceWeight β c * blockKernel c d := by
  cases d <;>
    simp [Fintype.sum_option, choiceWeight, blockKernel, blockWeights, mul_ite]

omit [AddCommGroup V] [Module F2 V] in
theorem independent_blockWeights_mixture (β : ℝ) (d : Fin k → BlockDraw V) :
    independentWeights (blockWeights β) k d =
      ∑ c : Fin k → ProjectionChoice, choiceTupleWeight β c * kernelTupleWeight c d := by
  unfold independentWeights choiceTupleWeight kernelTupleWeight
  simp_rw [blockWeights_choice_mixture]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.prod_mul_distrib

omit [AddCommGroup V] [Module F2 V] in
theorem drawWeights_choice_mixture (β : ℝ) (dz : (Fin k → BlockDraw V) × V) :
    drawWeights β k dz = ∑ c : Fin k → ProjectionChoice,
      choiceTupleWeight β c * (kernelTupleWeight c dz.1 * uniformWeights V dz.2) := by
  rw [drawWeights, independent_blockWeights_mixture, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

omit [AddCommGroup V] [Module F2 V] in
/-- This is the unconditioned law identity before replacing the coefficient
kernel by uniform projected-target maps. No division by a mask probability. -/
theorem draw_expectation_choice_mixture (β : ℝ)
    (H : ((Fin k → BlockDraw V) × V) → ℝ) :
    (∑ dz, drawWeights β k dz * H dz) =
      ∑ c : Fin k → ProjectionChoice, choiceTupleWeight β c *
        ∑ dz, (kernelTupleWeight c dz.1 * uniformWeights V dz.2) * H dz := by
  simp_rw [drawWeights_choice_mixture, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro dz _
  ring

omit [AddCommGroup V] [Module F2 V] in
theorem blockKernel_uniform_pushforward (c : ProjectionChoice) (d : BlockDraw V) :
    blockKernel c d =
      pushforwardWeight (uniformWeights (ChoiceValue V c)) (choiceEmbed c) d := by
  cases c with
  | none =>
      cases d <;> simp [blockKernel, pushforwardWeight, choiceEmbed, ChoiceValue]
      exact fun h => False.elim (h (Finset.mem_univ _))
  | some i =>
      cases d with
      | inl ab => simp [blockKernel, pushforwardWeight, choiceEmbed, ChoiceValue]
      | inr ja =>
          rcases ja with ⟨j, a⟩
          by_cases h : i = j <;>
            simp [blockKernel, pushforwardWeight, choiceEmbed, ChoiceValue,
              Prod.mk.injEq, h]
          exact fun h => False.elim (h (Finset.mem_univ _))

theorem pushforwardWeight_pi_dep {I B : Type*} [Fintype I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (p : (i : I) → A i → ℝ) (f : (i : I) → A i → B) (ys : I → B) :
    pushforwardWeight (fun xs : ∀ i, A i => ∏ i, p i (xs i))
      (fun xs : ∀ i, A i => fun i => f i (xs i)) ys =
      ∏ i, pushforwardWeight (p i) (f i) (ys i) := by
  classical
  simp only [pushforwardWeight]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro xs _
  simp only [Fintype.prod_ite_zero, funext_iff]

omit [AddCommGroup V] [Module F2 V] in
theorem kernelTuple_uniform_pushforward (c : Fin k → ProjectionChoice)
    (d : Fin k → BlockDraw V) :
    kernelTupleWeight c d =
      pushforwardWeight (uniformWeights (∀ j, ChoiceValue V (c j)))
        (fun f j => choiceEmbed (c j) (f j)) d := by
  unfold kernelTupleWeight
  simp_rw [blockKernel_uniform_pushforward]
  rw [← pushforwardWeight_pi_dep]
  have hp : (fun f : ∀ j, ChoiceValue V (c j) =>
      ∏ j, uniformWeights (ChoiceValue V (c j)) (f j)) =
      uniformWeights (∀ j, ChoiceValue V (c j)) := by
    funext f
    simp [uniformWeights, Fintype.card_pi, Nat.cast_prod, one_div,
      Finset.prod_inv_distrib]
  rw [hp]
  congr 1
  exact Subsingleton.elim _ _

theorem sum_pushforwardWeight_mul {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (f : A → B) (H : B → ℝ) :
    (∑ b, pushforwardWeight p f b * H b) = ∑ a, p a * H (f a) := by
  classical
  simp only [pushforwardWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem sum_uniformWeights_mul {A : Type*} [Fintype A] (H : A → ℝ) :
    (∑ a, uniformWeights A a * H a) = 𝔼 a, H a := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [uniformWeights, ← Finset.mul_sum]
  ring

omit [Module F2 V] [Fintype V] in
theorem restoreChoiceDraw (q : ProjectionChoice) (v : ChoiceValue V q) :
    (if q.isSome then
      Sum.inr (ConcreteExtraction.slotIndex (choiceSlot q),
          singleChoiceValue q v)
    else Sum.inl (fullChoiceValue q v)) = choiceEmbed q v := by
  cases q <;> simp [fullChoiceValue, singleChoiceValue, choiceEmbed, choiceSlot,
    slotIndex_decodeSlot]

omit [Module F2 V] [Fintype V] in
theorem tupleDraw_choiceValues (c : Fin k → ProjectionChoice)
    (fz : (∀ j, ChoiceValue V (c j)) × V) :
    tupleDraw (choiceMask c) (choiceSlots c) (choiceValuesRawTupleEquiv c fz) =
      fun j => choiceEmbed (c j) (fz.1 j) := by
  funext j
  change (if j ∈ choiceMask c then
      Sum.inr (ConcreteExtraction.slotIndex (choiceSlot (c j)),
        singleChoiceValue (c j) (fz.1 j))
    else Sum.inl (fullChoiceValue (c j) (fz.1 j))) = choiceEmbed (c j) (fz.1 j)
  simpa only [choiceMask, Finset.mem_filter,
    Finset.mem_univ, true_and] using restoreChoiceDraw (c j) (fz.1 j)

/-- The whole fixed-choice kernel is precisely the uniform actual-map law.
This lemma closes the gap between an arbitrary fixed-mask sampling experiment
and the conditioning kernel that actually occurs in drawWeights. -/
theorem fixed_choice_kernel_map_expectation
    (rhs : Fin k → Bool) (c : Fin k → ProjectionChoice)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (∑ dz : (Fin k → BlockDraw V) × V,
      (kernelTupleWeight c dz.1 * uniformWeights V dz.2) *
        H (paddedMap rhs dz.1 dz.2)) =
      𝔼 Y : RawPoint (choiceMask c) →ₗ[F2] V,
        H (Y.comp (rawProjection rhs (choiceMask c) (choiceSlots c))) := by
  calc
    _ = ∑ d : Fin k → BlockDraw V, kernelTupleWeight c d *
        ∑ z : V, uniformWeights V z * H (paddedMap rhs d z) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = ∑ f : ∀ j, ChoiceValue V (c j), uniformWeights _ f *
        ∑ z : V, uniformWeights V z *
          H (paddedMap rhs (fun j => choiceEmbed (c j) (f j)) z) := by
      simp_rw [kernelTuple_uniform_pushforward]
      exact sum_pushforwardWeight_mul _ _ _
    _ = 𝔼 fz : (∀ j, ChoiceValue V (c j)) × V,
        H (paddedMap rhs (fun j => choiceEmbed (c j) (fz.1 j)) fz.2) := by
      rw [← sum_uniformWeights_mul, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [uniformWeights_prod]
      ring
    _ = 𝔼 a : RawTuple (choiceMask c) V,
        H (paddedMap rhs (tupleDraw (choiceMask c) (choiceSlots c) a) a.1) := by
      apply Fintype.expect_equiv (choiceValuesRawTupleEquiv c)
      intro fz
      rw [tupleDraw_choiceValues]
      rfl
    _ = _ := uniform_fixed_projection_tuple rhs (choiceMask c) (choiceSlots c) H

theorem actual_projection_mixture_expectation
    (rhs : Fin k → Bool) (β : ℝ)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (∑ dz : (Fin k → BlockDraw V) × V,
      drawWeights β k dz * H (paddedMap rhs dz.1 dz.2)) =
      ∑ c : Fin k → ProjectionChoice, choiceTupleWeight β c *
        (𝔼 Y : RawPoint (choiceMask c) →ₗ[F2] V,
          H (Y.comp (rawProjection rhs (choiceMask c) (choiceSlots c)))) := by
  rw [draw_expectation_choice_mixture]
  apply Finset.sum_congr rfl
  intro c _
  rw [fixed_choice_kernel_map_expectation]

section MapSpace

variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

omit [Fintype (ActualHomogeneous.E k →ₗ[F2] V)] in
theorem paddedMapWeights_eq (rhs : Fin k → Bool) (β : ℝ)
    (X : ActualHomogeneous.E k →ₗ[F2] V) :
    paddedMapWeights rhs β X =
      paddedWeights rhs β (ActualEnumeration.toCoefficients k V X) := by
  unfold paddedMapWeights paddedWeights pushforwardWeight
  apply Finset.sum_congr rfl
  intro dz _
  have he : paddedMap rhs dz.1 dz.2 = X ↔
      ActualEnumeration.toCoefficients k V (paddedMap rhs dz.1 dz.2) =
        ActualEnumeration.toCoefficients k V X :=
    (ActualEnumeration.coefficientEquiv k V).symm.injective.eq_iff.symm
  simp only [he]
  split_ifs <;> rfl

theorem uniform_sourceMap_coordinates (a : ActualEnumeration.Coefficients k V) :
    uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)
      (ActualEnumeration.coefficientEquiv k V a) =
        uniformWeights (ActualEnumeration.Coefficients k V) a := by
  simp only [uniformWeights]
  rw [Fintype.card_congr (ActualEnumeration.coefficientEquiv k V)]

theorem paddedMapWeights_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ) :
    UniqueGamesTheorem.Foundations.Information.totalVariation (paddedMapWeights (V := V) rhs β)
      (uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)) =
        UniqueGamesTheorem.Foundations.Information.totalVariation
          (independentWeights (mixture β (singletonPairWeights V)) k)
          (uniformWeights (Fin k → V × V)) := by
  have heq : UniqueGamesTheorem.Foundations.Information.totalVariation
      (paddedMapWeights (V := V) rhs β)
      (uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)) =
      UniqueGamesTheorem.Foundations.Information.totalVariation
        (paddedWeights (V := V) rhs β)
        (uniformWeights (ActualEnumeration.Coefficients k V)) := by
    unfold UniqueGamesTheorem.Foundations.Information.totalVariation
    rw [← (ActualEnumeration.coefficientEquiv k V).sum_comp]
    simp only [paddedMapWeights_eq,
      ActualEnumeration.coefficientEquiv, Equiv.coe_fn_mk,
      ActualEnumeration.to_fromCoefficients]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [show uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)
      (ActualEnumeration.fromCoefficients k V a) =
        uniformWeights (ActualEnumeration.Coefficients k V) a from
          uniform_sourceMap_coordinates a]
  rw [heq]
  exact paddedWeights_totalVariation_eq_slope rhs β

end MapSpace

end Law

end
end UniqueGamesTheorem.Decoder.PaddedLaw

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_StochasticBound
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Local randomized advice responses are bounded using complete independently
sampled response tables. The verifier questions are the actual weighted
pushforward of the occurrence/position draw, with the complete private row
input retained on each side. No response sees the opposite private question.

The outer mask and coefficient tuple may be fixed before selecting either
response kernel. Revealing these data only strengthens this upper bound; they
contain no clean question or agreement event. The quantitative game-repetition
rate is a separate input to the final averaging lemma.
-/

namespace UniqueGamesTheorem.Clean.StochasticBound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds
open scoped BigOperators

noncomputable section

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq R] [DecidableEq O] [DecidableEq N] in
/-- The two deterministic strategy representations have exactly the same
winning probability under the explicitly constructed question law. -/
theorem success_eq_fixedAdviceSuccess
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : Strategy (ZeroInformation.FirstInput P R O)
      (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)) :
    (actualGame μ J g gamma).success strategy =
      UpperBound.fixedAdviceSuccess μ J g gamma ⟨strategy.1, strategy.2⟩ := by
  classical
  unfold Game.success actualGame Simulation.weightedGame UpperBound.fixedAdviceSuccess
  rw [FiniteDistribution.probability_pushforward]
  rfl

omit [DecidableEq R] [DecidableEq O] [DecidableEq N] in
/-- Each stochastic local response has a deterministic complete response table
with at least its success probability. The table is chosen before the questions. -/
theorem exists_deterministic_ge_stochastic
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (responses₁ : ZeroInformation.FirstInput P R O →
      FiniteDistribution (ActualProjection.FirstAnswer P))
    (responses₂ : ZeroInformation.SecondInput P R O N →
      FiniteDistribution (ActualProjection.SecondAnswer P)) :
    ∃ strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N),
      (actualGame μ J g gamma).stochasticSuccess responses₁ responses₂ ≤
        UpperBound.fixedAdviceSuccess μ J g gamma strategy := by
  classical
  obtain ⟨strategy, h⟩ :=
    (actualGame μ J g gamma).exists_deterministic_ge_stochastic responses₁ responses₂
  refine ⟨⟨strategy.1, strategy.2⟩, ?_⟩
  calc
    _ ≤ (actualGame μ J g gamma).success strategy := h
    _ = _ := success_eq_fixedAdviceSuccess μ J g gamma strategy

private theorem expectation_mono {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

omit [DecidableEq O] [DecidableEq N] in
/-- The deterministic witness family is indexed by the pre-question public
data only. No single global deterministic strategy is claimed here. -/
theorem native_stochastic_le_deterministic
    (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N) :
    ∃ strategy : NativeExperiment.MaskStrategy k R O N,
      nativeStochasticSuccess k μ g β hβ₀ hβ₁ responses ≤
        NativeExperiment.success k μ g β hβ₀ hβ₁ strategy := by
  classical
  let strategy : NativeExperiment.MaskStrategy k R O N := fun mask gamma =>
    Classical.choose (exists_deterministic_ge_stochastic μ (NativeExperiment.maskSet mask)
      g gamma (responses mask gamma).1 (responses mask gamma).2)
  refine ⟨strategy, ?_⟩
  unfold nativeStochasticSuccess NativeExperiment.success
  apply expectation_mono
  intro mask
  apply expectation_mono
  intro gamma
  exact Classical.choose_spec (exists_deterministic_ge_stochastic μ
    (NativeExperiment.maskSet mask) g gamma (responses mask gamma).1 (responses mask gamma).2)

end
end UniqueGamesTheorem.Clean.StochasticBound

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_AdviceFibersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact visible row advice and private matrix coordinates

Every nonempty fiber of `M ↦ A ∘ M` is an affine copy of
`Hom(E, ker A)`, whether or not `A` is surjective.  Choosing one base matrix
for each attainable row gives a product decomposition of the complete matrix
space.  Uniform sampling therefore makes visible row advice and the hidden
kernel-valued matrix independent.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear

namespace UniqueGamesTheorem.Decoder.AdviceFibers

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K]
  [AddCommGroup R] [Module F2 R]

/-- Affine target intercepts are retained in the private coordinates. -/
theorem assemble_affine_target (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) (z : E) (u : K) :
    assemble A M₀ N z + u = (N z : K) + (M₀ z + u) := by
  rw [assemble_apply]
  ac_rfl

end UniqueGamesTheorem.Decoder.AdviceFibers

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Decoder.PrivateFourier

open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixParity
open UniqueGamesTheorem.Fourier.MatrixParityRow
open scoped BigOperators Classical

section Signs

theorem sign_add (a b : F2) : sign (a + b) = sign a * sign b := by
  simp [sign, binarySign_add, Complex.mul_re]

theorem sign_add_one (a : F2) : sign (a + 1) = -sign a := by
  rw [sign_add, sign_one]
  ring

end Signs

section CharacterAverages

variable {H K : Type*} [AddCommGroup H] [Module F2 H]
    [AddCommGroup K] [Module F2 K]

theorem binary_neg_eq_self (x : K) : -x = x := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hh := congrArg (fun a : F2 => a • x) htwo
  exact neg_eq_iff_add_eq_zero.mpr
    (by simpa only [add_smul, one_smul, zero_smul] using hh)

theorem binary_add_eq_zero_iff (x y : K) : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg, binary_neg_eq_self]

theorem average_sign_dual [Fintype (K →ₗ[F2] F2)] (x : K) :
    (𝔼 σ : K →ₗ[F2] F2, sign (σ x)) = if x = 0 then 1 else 0 := by
  have h := congrArg Complex.re
    (UniqueGamesTheorem.Fourier.MatrixNoise.average_evaluationCharacter x)
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re, sign] using h

theorem average_sign_primal [Fintype H] (σ : H →ₗ[F2] F2) :
    (𝔼 h : H, sign (σ h)) = if σ = 0 then 1 else 0 := by
  have h := congrArg Complex.re (expect_linearFunctionalCharacter σ)
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re,
    linearFunctionalCharacter_apply, sign] using h

/-- Exact character expansion of equality in the actual output space. -/
theorem average_sign_equality [Fintype (K →ₗ[F2] F2)] (x y : K) :
    (𝔼 σ : K →ₗ[F2] F2, sign (σ x) * sign (σ y)) =
      if x = y then 1 else 0 := by
  simp_rw [← sign_add, ← map_add]
  rw [average_sign_dual, binary_add_eq_zero_iff]

/-- The ambient uniform character has trivial restriction to `H` with exactly
the reciprocal cardinality of `H`.  No conditioning on the private character
is substituted for the real experiment. -/
theorem trivial_restriction_probability [Fintype H] [Fintype (K →ₗ[F2] F2)]
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι) :
    (𝔼 σ : K →ₗ[F2] F2, if σ.comp ι = 0 then (1 : ℝ) else 0) =
      1 / (Fintype.card H : ℝ) := by
  calc
    _ = 𝔼 σ : K →ₗ[F2] F2, 𝔼 h : H, sign (σ (ι h)) := by
      apply Finset.expect_congr rfl
      intro σ _
      exact (average_sign_primal (σ.comp ι)).symm
    _ = 𝔼 h : H, 𝔼 σ : K →ₗ[F2] F2, sign (σ (ι h)) :=
      Finset.expect_comm _ _ _
    _ = 𝔼 h : H, if h = 0 then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro h _
      rw [average_sign_dual]
      have heq : ι h = 0 ↔ h = 0 := by
        rw [← map_zero ι]
        exact hι.eq_iff
      rw [heq]
    _ = _ := by simp

end CharacterAverages

section ActualFourier

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H]
  [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
theorem tableSign_antifold (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (σ : K →ₗ[F2] F2) (h : H)
    (folded : ∀ N, F (N + τ.smulRight h) = F N + ι h)
    (hσ : σ (ι h) = 1) :
    ∀ N, tableSign F σ (N + τ.smulRight h) = -tableSign F σ N := by
  intro N
  simp only [tableSign, folded, map_add, hσ, sign_add_one]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (H →ₗ[F2] E)] in
/-- Translation of the input multiplies a coefficient by its character. -/
theorem linearCoeff_translate (f : (E →ₗ[F2] H) → ℝ)
    (D : E →ₗ[F2] H) (Φ : H →ₗ[F2] E) :
    linearCoeff (fun N => f (N + D)) Φ =
      linearCoeff f Φ * (linearTraceCharacter Φ D).re := by
  have hself : D + D = 0 :=
    (linearMap_add_eq_zero_iff D D).2 rfl
  have hchange := Fintype.expect_equiv (Equiv.addRight D)
    (fun N => f (N + D) * (linearTraceCharacter Φ N).re)
    (fun N => f N * (linearTraceCharacter Φ (N + D)).re)
    (fun N => by simp only [Equiv.coe_addRight, add_assoc, hself, add_zero])
  unfold linearCoeff
  rw [hchange]
  simp only [traceCharacter_re_add, ← mul_assoc]
  exact (Finset.expect_mul _ _ _).symm

omit [FiniteDimensional F2 E] [Fintype (H →ₗ[F2] E)] in
/-- Anti-folding forces every positive-mass frequency to return first bit one. -/
theorem positive_frequency_first_bit (f : (E →ₗ[F2] H) → ℝ)
    (τ : E →ₗ[F2] F2) (h : H) (Φ : H →ₗ[F2] E)
    (folded : ∀ N, f (N + τ.smulRight h) = -f N)
    (positive : 0 < frequencyWeight f Φ) : τ (Φ h) = 1 := by
  have hcoeff : linearCoeff f Φ ≠ 0 := by
    intro hz
    simp [frequencyWeight, hz] at positive
  have heq := linearCoeff_translate f (τ.smulRight h) Φ
  have hneg : linearCoeff (fun N => f (N + τ.smulRight h)) Φ =
      -linearCoeff f Φ := by
    simp only [linearCoeff, folded, neg_mul]
    simp [Fintype.expect_eq_sum_div_card]
  rw [hneg] at heq
  have hchar : (linearTraceCharacter Φ (τ.smulRight h)).re = sign (τ (Φ h)) := by
    simp only [linearTraceCharacter_apply, linearTracePair, trace_smulRight_comp, sign]
  rw [hchar] at heq
  rcases Integration.BinaryLinear.scalar_cases (τ (Φ h)) with hz | hone
  · rw [hz, sign_zero, mul_one] at heq
    exact False.elim (hcoeff (by linarith))
  · exact hone

end ActualFourier

section AffineSlice

variable {E H V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H]
  [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
theorem traceCharacter_re_mul (Φ θ : H →ₗ[F2] E) (N : E →ₗ[F2] H) :
    (linearTraceCharacter Φ N).re * (linearTraceCharacter θ N).re =
      (linearTraceCharacter (Φ + θ) N).re := by
  rw [linearTraceCharacter_add, AddChar.add_apply, Complex.mul_re]
  simp [linearTraceCharacter_apply]

/-- The exact Fourier coset expansion of the affine conditional correlation. -/
theorem sliceCorrelation_eq_coset (q : E →ₗ[F2] V) (N₀ : E →ₗ[F2] H)
    (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) :
    sliceCorrelation q N₀ f θ =
      ∑ Φ ∈ frequencyCoset q θ,
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) N₀).re := by
  unfold sliceCorrelation
  calc
    _ = 𝔼 A : V →ₗ[F2] H, ∑ Φ : H →ₗ[F2] E,
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) (N₀ + A.comp q)).re := by
      apply Finset.expect_congr rfl
      intro A _
      rw [← linear_fourier_inversion f (N₀ + A.comp q), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Φ _
      rw [mul_assoc, traceCharacter_re_mul]
    _ = ∑ Φ : H →ₗ[F2] E, if q.comp (Φ + θ) = 0 then
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) N₀).re else 0 := by
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro Φ _
      simp only [traceCharacter_re_add, ← mul_assoc]
      rw [← Finset.mul_expect, row_character_average]
      split <;> simp
    _ = _ := by simp [frequencyCoset, Finset.sum_filter]

/-- Cauchy--Schwarz bounds an affine correlation by the actual Fourier mass
in its target coset; no spectral mass is assumed. -/
theorem sliceCorrelation_sq_le_coset_mass (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) :
    sliceCorrelation q N₀ f θ ^ 2 ≤
      (frequencyCoset q θ).card *
        ∑ Φ ∈ frequencyCoset q θ, frequencyWeight f Φ := by
  rw [sliceCorrelation_eq_coset]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (frequencyCoset q θ)
    (linearCoeff f) (fun Φ => (linearTraceCharacter (Φ + θ) N₀).re)
  have hs : ∀ Φ : H →ₗ[F2] E,
      (linearTraceCharacter (Φ + θ) N₀).re ^ 2 = 1 := by
    intro Φ
    exact sign_sq _
  simpa only [hs, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul,
    frequencyWeight, mul_comm] using hcs

end AffineSlice

section AffineEquality

variable {E H K V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K] [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)] [Fintype (K →ₗ[F2] F2)]

omit [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- The pure-tensor target character is literally evaluation at `z`. -/
theorem target_character (σ : H →ₗ[F2] F2) (z : E) (N : E →ₗ[F2] H) :
    (linearTraceCharacter (σ.smulRight z) N).re = sign (σ (N z)) := by
  simp only [linearTraceCharacter_apply, sign]
  congr 2
  rw [linearTracePair_swap]
  exact trace_smulRight_comp σ z N

omit [FiniteDimensional F2 V] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- Affine target equality expands into the correlations with the intercept
phase `sign (σ b)`.  In the projected experiment `b = M₀ z + u`. -/
theorem affine_equality_character_expansion (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (z : E) (b : K) :
    (𝔼 A : V →ₗ[F2] H,
      if F (N₀ + A.comp q) = b + ι ((N₀ + A.comp q) z) then (1 : ℝ) else 0) =
      𝔼 σ : K →ₗ[F2] F2, sign (σ b) *
        sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z) := by
  calc
    _ = 𝔼 A : V →ₗ[F2] H, 𝔼 σ : K →ₗ[F2] F2,
        sign (σ (F (N₀ + A.comp q))) *
          sign (σ (b + ι ((N₀ + A.comp q) z))) := by
      apply Finset.expect_congr rfl
      intro A _
      exact (average_sign_equality _ _).symm
    _ = 𝔼 σ : K →ₗ[F2] F2, 𝔼 A : V →ₗ[F2] H,
        sign (σ (F (N₀ + A.comp q))) *
          sign (σ (b + ι ((N₀ + A.comp q) z))) := Finset.expect_comm _ _ _
    _ = _ := by
      apply Finset.expect_congr rfl
      intro σ _
      unfold sliceCorrelation
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro A _
      simp only [map_add, sign_add, target_character, tableSign, LinearMap.comp_apply]
      ring

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
  [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] [Fintype (K →ₗ[F2] F2)] in
/-- Every slice correlation has absolute value at most one. -/
theorem sliceCorrelation_tableSign_abs_le_one (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (σ : K →ₗ[F2] F2) (θ : H →ₗ[F2] E) :
    |sliceCorrelation q N₀ (tableSign F σ) θ| ≤ 1 := by
  unfold sliceCorrelation
  calc
    _ ≤ 𝔼 A : V →ₗ[F2] H,
        |tableSign F σ (N₀ + A.comp q) *
          (linearTraceCharacter θ (N₀ + A.comp q)).re| := Finset.abs_expect_le _ _
    _ = 1 := by
      have hp (N : E →ₗ[F2] H) : |(linearTraceCharacter θ N).re| = 1 := sign_abs _
      simp only [abs_mul, tableSign, sign_abs, hp, mul_one]
      exact Fintype.expect_const 1

omit [FiniteDimensional F2 V] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- Dropping the unit intercept phase can only increase the average absolute
correlation; the hypothesis is the actual affine-slice agreement probability. -/
theorem agreement_le_average_abs_correlation (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (z : E) (b : K) :
    (𝔼 A : V →ₗ[F2] H,
      if F (N₀ + A.comp q) = b + ι ((N₀ + A.comp q) z) then (1 : ℝ) else 0) ≤
      𝔼 σ : K →ₗ[F2] F2,
        |sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z)| := by
  rw [affine_equality_character_expansion]
  apply Finset.expect_le_expect
  intro σ _
  calc
    _ ≤ |sign (σ b) *
        sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z)| := le_abs_self _
    _ = _ := by rw [abs_mul, sign_abs, one_mul]

end AffineEquality

section CosetCardinality

variable {E H : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (H →ₗ[F2] E)]

/-- The exact number of frequencies in the affine coset.  Translation does not
alter the annihilator cardinality, including when the target is nonzero. -/
theorem frequencyCoset_card (Q : Submodule F2 E) [Fintype (H →ₗ[F2] Q)]
    (θ : H →ₗ[F2] E) :
    (frequencyCoset Q.mkQ θ).card =
      2 ^ (Module.finrank F2 H * Module.finrank F2 Q) := by
  classical
  rw [frequencyCoset, ← Fintype.card_subtype]
  calc
    Fintype.card {Φ : H →ₗ[F2] E // Q.mkQ.comp (Φ + θ) = 0} =
        Fintype.card {Φ : H →ₗ[F2] E // Q.mkQ.comp Φ = 0} :=
      Fintype.card_congr (Equiv.subtypeEquiv (Equiv.addRight θ) (fun _ => Iff.rfl))
    _ = Fintype.card (H →ₗ[F2] Q) :=
      UniqueGamesTheorem.Fourier.MatrixRestrictions.quotientKernel_card Q
    _ = _ := card_linearMaps

theorem frequencyCoset_card_le (Q : Submodule F2 E) [Fintype (H →ₗ[F2] Q)]
    (θ : H →ₗ[F2] E) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hQ : Module.finrank F2 Q ≤ r) :
    (frequencyCoset Q.mkQ θ).card ≤ 2 ^ (ℓ * r) := by
  rw [frequencyCoset_card]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul hH hQ)

end CosetCardinality

section Averaging

variable {SigmaChar : Type*} [Fintype SigmaChar] [Nonempty SigmaChar]

omit [Nonempty SigmaChar] in
/-- Discarding a set of characters costs at most its actual uniform mass. -/
theorem remove_bad_characters (C : SigmaChar → ℝ) (good : SigmaChar → Prop)
    (a b : ℝ) (hC : ∀ σ, |C σ| ≤ 1)
    (hcorrelation : a ≤ 𝔼 σ, |C σ|)
    (hbad : (𝔼 σ, if good σ then (0 : ℝ) else 1) ≤ b) :
    a - b ≤ 𝔼 σ, if good σ then |C σ| else 0 := by
  classical
  have hp : (𝔼 σ, |C σ|) ≤
      (𝔼 σ, if good σ then |C σ| else 0) +
      (𝔼 σ, if good σ then (0 : ℝ) else 1) := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_le_expect
    intro σ _
    by_cases hg : good σ
    · simp [hg]
    · simpa [hg] using hC σ
  linarith

/-- The second Cauchy--Schwarz step in private decoding.  The first step is
`sliceCorrelation_sq_le_coset_mass`; the mass is the actual sampled Fourier
mass and `good` selects nontrivial output characters. -/
theorem average_coset_mass_lower (C mass : SigmaChar → ℝ) (good : SigmaChar → Prop)
    (N c : ℝ) (hN : 0 < N) (hc : 0 ≤ c)
    (hcorrelation : c ≤ 𝔼 σ, if good σ then |C σ| else 0)
    (hpoint : ∀ σ, good σ → C σ ^ 2 ≤ N * mass σ) :
    c ^ 2 / N ≤ 𝔼 σ, if good σ then mass σ else 0 := by
  classical
  let d : SigmaChar → ℝ := fun σ => if good σ then |C σ| else 0
  have hj := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const] at hj
  have hp : (𝔼 σ, d σ ^ 2) ≤ N * (𝔼 σ, if good σ then mass σ else 0) := by
    rw [Finset.mul_expect]
    apply Finset.expect_le_expect
    intro σ _
    by_cases hg : good σ
    · simpa [d, hg, sq_abs] using hpoint σ hg
    · simp [d, hg]
  have hs : c ^ 2 ≤ (𝔼 σ, d σ) ^ 2 := by
    have hd : c ≤ 𝔼 σ, d σ := hcorrelation
    nlinarith
  apply (div_le_iff₀ hN).2
  nlinarith

end Averaging

section Contraction

variable {E H : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup H] [Module F2 H]

/-- A frequency in the target coset contracts into `z + Q`. -/
theorem contraction_mem_target_coset (Q : Submodule F2 E)
    (σ : H →ₗ[F2] F2) (z : E) (Φ : H →ₗ[F2] E) (h : H)
    (hσ : σ h = 1) (hcoset : Q.mkQ.comp (Φ + σ.smulRight z) = 0) :
    Φ h - z ∈ Q := by
  have hq := LinearMap.congr_fun hcoset h
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    hσ, one_smul, LinearMap.zero_apply] at hq
  have hmem : Φ h + z ∈ Q := by
    change Q.mkQ (Φ h + z) = 0 at hq
    exact (Submodule.Quotient.mk_eq_zero Q).mp hq
  have hz : -z = z := by
    have htwo : (1 + 1 : F2) = 0 := by decide
    have hzz : z + z = 0 := by
      have hh := congrArg (fun a : F2 => a • z) htwo
      simpa only [add_smul, one_smul, zero_smul] using hh
    exact neg_eq_iff_add_eq_zero.mpr hzz
  simpa only [sub_eq_add_neg, hz] using hmem

end Contraction

section IndependentSampling

variable {U O Ω : Type*} [Fintype Ω]

/-- If the returned projected answer has a preimage in the candidate set, the
uniform, independently sampled candidate finds a preimage with this probability. -/
theorem uniform_preimage_probability (s : Finset U) (π : U → O) (b : O)
    (preimage : ∃ u ∈ s, π u = b) :
    1 / (s.card : ℝ) ≤ 𝔼 u ∈ s, if π u = b then (1 : ℝ) else 0 := by
  classical
  obtain ⟨u, hu, hπ⟩ := preimage
  have hsum : (1 : ℝ) ≤ ∑ v ∈ s, if π v = b then (1 : ℝ) else 0 := by
    have hnonneg : ∀ v ∈ s, (0 : ℝ) ≤ if π v = b then 1 else 0 := by
      intro v _
      split <;> norm_num
    have h := Finset.single_le_sum hnonneg hu
    simpa only [hπ, ite_true, if_true] using h
  rw [Finset.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

/-- An explicit product sampling law: the left strategy samples uniformly from
`s`, independently of the right strategy's private sample.  Only positive-mass
good samples need a preimage; no private Fourier information is passed left. -/
theorem independent_agreement_lower (s : Finset U) (π : U → O)
    (answer : Ω → O) (weight : Ω → ℝ) (good : Ω → Prop)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (preimage : ∀ ω, good ω → 0 < weight ω → ∃ u ∈ s, π u = answer ω) :
    (∑ ω, if good ω then weight ω else 0) / (s.card : ℝ) ≤
      ∑ ω, weight ω * (𝔼 u ∈ s, if π u = answer ω then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ω _
  have havg : 0 ≤ 𝔼 u ∈ s, if π u = answer ω then (1 : ℝ) else 0 :=
    Finset.expect_nonneg fun _ _ => by positivity
  by_cases hg : good ω
  · simp only [hg, ite_true, if_true]
    by_cases hw : 0 < weight ω
    · have hb := uniform_preimage_probability s π (answer ω) (preimage ω hg hw)
      have := mul_le_mul_of_nonneg_left hb (hweight ω)
      simpa only [div_eq_mul_inv, one_mul] using this
    · have hz : weight ω = 0 := le_antisymm (le_of_not_gt hw) (hweight ω)
      simp [hz]
  · simp only [hg, ite_false, zero_div]
    exact mul_nonneg (hweight ω) havg

end IndependentSampling

end UniqueGamesTheorem.Decoder.PrivateFourier

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_PrivateStrategyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual private response laws for Fourier decoding

The right response law has only its row-fiber table, the inclusion of its hidden
kernel, a first-bit map, and an actual fallback answer as arguments.  In
particular it has no column slice or witness.  Zero-mass invalid frequencies
are repaired to the fallback so that the response type always consists of
actual answers.  Witness data occur only in the success analysis.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.PrivateStrategy

attribute [local instance] Classical.propDecidable

open PrivateFourier
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

section Candidates

variable {E E' : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup E'] [Module F2 E'] [Fintype E]

theorem candidates_nonempty (Z : Submodule F2 E) (z : E)
    (τ : E →ₗ[F2] F2) (hz : τ z = 1) : (candidates Z z τ).Nonempty := by
  exact ⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩

theorem candidates_card_le (Z : Submodule F2 E) [Fintype Z] (z : E)
    (τ : E →ₗ[F2] F2) : (candidates Z z τ).card ≤ Fintype.card Z := by
  let f : {v // v ∈ candidates Z z τ} → Z := fun v =>
    ⟨v.1 - z, ((mem_candidates Z z v.1 τ).1 v.2).1⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change x.val - z = y.val - z at he
    exact sub_left_injective he
  simpa using Fintype.card_le_of_injective f hf

theorem candidates_card_le_pow (Z : Submodule F2 E) [Fintype Z]
    [FiniteDimensional F2 Z] (z : E) (τ : E →ₗ[F2] F2)
    (r : ℕ) (hr : Module.finrank F2 Z ≤ r) :
    (candidates Z z τ).card ≤ 2 ^ r := by
  have hc : Fintype.card Z = 2 ^ Module.finrank F2 Z := by
    simpa [F2, UniqueGamesTheorem.Integration.BinaryLinear.F2, ZMod.card] using
      Module.card_fintype (Module.finBasis F2 Z)
  calc
    _ ≤ Fintype.card Z := candidates_card_le Z z τ
    _ = 2 ^ Module.finrank F2 Z := hc
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide : 0 < 2) hr

/-- First-bit preservation converts a projected coset member into an actual
answer in the left candidate set. -/
theorem candidate_preimage (Z : Submodule F2 E) (z : E)
    (π : E →ₗ[F2] E') (τ : E →ₗ[F2] F2) (τ' : E' →ₗ[F2] F2)
    (hτ : τ'.comp π = τ) (y : E') (hy : y - π z ∈ Z.map π)
    (hybit : τ' y = 1) : ∃ v ∈ candidates Z z τ, π v = y := by
  obtain ⟨w, hw, hwπ⟩ := Submodule.mem_map.mp hy
  have heq : π (z + w) = y := by
    rw [map_add, hwπ]
    rw [add_comm, sub_add_cancel]
  refine ⟨z + w, (mem_candidates Z z (z + w) τ).2 ⟨?_, ?_⟩, heq⟩
  · simpa only [add_sub_cancel_left] using hw
  · rw [← hτ, LinearMap.comp_apply, heq, hybit]

end Candidates

section RightRule

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

omit [FiniteDimensional F2 H] in
theorem chooseUnit_spec (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) :
    σ (chooseUnit σ hne) = 1 := Classical.choose_spec (exists_unit σ hne)

theorem privateSeedLaw_expectation (F : (E →ₗ[F2] H) → K)
    (g : ((K →ₗ[F2] F2) × (H →ₗ[F2] E)) → ℝ) :
    (privateSeedLaw F).expectation g =
      𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
        frequencyWeight (tableSign F σ) Φ * g (σ, Φ) := by
  simp only [FiniteDistribution.expectation, privateSeedLaw, Fintype.sum_prod_type,
    Fintype.expect_eq_sum_div_card]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]

omit [FiniteDimensional F2 E] [Fintype (H →ₗ[F2] E)] [Fintype (K →ₗ[F2] F2)] in
theorem privateOutput_eq_contraction (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h)
    (σ : K →ₗ[F2] F2) (Φ : H →ₗ[F2] E)
    (hn : σ.comp ι ≠ 0) (hp : 0 < frequencyWeight (tableSign F σ) Φ) :
    (privateOutput ι τ fallback (σ, Φ)).1 = Φ (chooseUnit (σ.comp ι) hn) := by
  have hunit : σ (ι (chooseUnit (σ.comp ι) hn)) = 1 := chooseUnit_spec (σ.comp ι) hn
  have hfold := tableSign_antifold F ι τ σ (chooseUnit (σ.comp ι) hn)
    (fun N => folded N _) hunit
  have hbit := positive_frequency_first_bit (tableSign F σ) τ
    (chooseUnit (σ.comp ι) hn) Φ hfold hp
  simp [privateOutput, hn, hbit]

theorem privateLaw_expectation [Fintype E] (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (g : ActualAnswer τ → ℝ) :
    (privateLaw F ι τ fallback).expectation g =
      𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
        frequencyWeight (tableSign F σ) Φ * g (privateOutput ι τ fallback (σ, Φ)) := by
  rw [privateLaw, FiniteDistribution.expectation_pushforward, privateSeedLaw_expectation]

end RightRule

section LeftRule

variable {E : Type*} [AddCommGroup E] [Module F2 E] [Fintype E]

theorem candidateLaw_expectation (Z : Submodule F2 E) (z : E)
    (τ : E →ₗ[F2] F2) (hz : τ z = 1) (g : E → ℝ) :
    (candidateLaw Z z τ hz).expectation (fun v => g v.1) =
      𝔼 v ∈ candidates Z z τ, g v := by
  let : Nonempty {v // v ∈ candidates Z z τ} :=
    ⟨⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩⟩
  unfold candidateLaw
  rw [FiniteDistribution.expectation_pushforward, FiniteDistribution.expectation_uniform,
    Finset.expect_eq_sum_div_card]
  simp only [Fintype.card_coe, Finset.sum_coe_sort]

end LeftRule

section ConditionalAgreement

variable {U E H K : Type*}
variable [AddCommGroup U] [Module F2 U] [Fintype U]
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

theorem conditionalAgreement_eq_sum (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) :
    conditionalAgreement Z z τU hz π F ι τ fallback =
      𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
        frequencyWeight (tableSign F σ) Φ *
          (𝔼 v ∈ candidates Z z τU,
            if π v = (privateOutput ι τ fallback (σ, Φ)).1 then (1 : ℝ) else 0) := by
  unfold conditionalAgreement
  have hp (μ : FiniteDistribution (ActualAnswer τU × ActualAnswer τ)) :
      μ.probability (fun a => decide (π a.1.1 = a.2.1)) =
      μ.expectation (fun a => if π a.1.1 = a.2.1 then (1 : ℝ) else 0) := by
    simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
  rw [hp, FiniteDistribution.expectation_product]
  simp_rw [privateLaw_expectation]
  rw [candidateLaw_expectation Z z τU hz (fun v =>
    𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
      frequencyWeight (tableSign F σ) Φ *
        (if π v = (privateOutput ι τ fallback (σ, Φ)).1 then (1 : ℝ) else 0)),
    Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro σ _
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro Φ _
  exact (Finset.mul_expect _ _ _).symm

omit [Fintype E] [FiniteDimensional F2 E] [FiniteDimensional F2 H] in
theorem goodCosetMass_nonneg (Q : Submodule F2 E) (z' : E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K) :
    0 ≤ goodCosetMass Q z' F ι := by
  apply Finset.expect_nonneg
  intro σ _
  split
  · exact Finset.sum_nonneg fun _ _ => frequencyWeight_nonneg _ _
  · exact le_rfl

omit [Fintype E] [FiniteDimensional F2 E] [Fintype (K →ₗ[F2] F2)] in
/-- A good sampled frequency has a valid left preimage.  Neither decoder is
given the proof or the witness used here. -/
theorem good_frequency_preimage (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (hτ : τ.comp π = τU)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h)
    (σ : K →ₗ[F2] F2) (Φ : H →ₗ[F2] E)
    (hn : σ.comp ι ≠ 0)
    (hc : Φ ∈ frequencyCoset (Z.map π).mkQ ((σ.comp ι).smulRight (π z)))
    (hp : 0 < frequencyWeight (tableSign F σ) Φ) :
    ∃ v ∈ candidates Z z τU, π v = (privateOutput ι τ fallback (σ, Φ)).1 := by
  have hout := privateOutput_eq_contraction F ι τ fallback folded σ Φ hn hp
  apply candidate_preimage Z z π τU τ hτ
  · rw [hout]
    apply contraction_mem_target_coset (Z.map π) (σ.comp ι) (π z) Φ
      (chooseUnit (σ.comp ι) hn) (chooseUnit_spec _ _)
    simpa [frequencyCoset] using hc
  · exact (privateOutput ι τ fallback (σ, Φ)).2

/-- The actual independent policies agree with at least the good Fourier mass
divided by the number of left candidates. -/
theorem conditionalAgreement_ge_mass_div_card (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (hτ : τ.comp π = τU)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h) :
    goodCosetMass (Z.map π) (π z) F ι / (candidates Z z τU).card ≤
      conditionalAgreement Z z τU hz π F ι τ fallback := by
  rw [goodCosetMass, Finset.expect_div, conditionalAgreement_eq_sum]
  apply Finset.expect_le_expect
  intro σ _
  have hi := independent_agreement_lower (candidates Z z τU) π
    (fun Φ => (privateOutput ι τ fallback (σ, Φ)).1)
    (frequencyWeight (tableSign F σ))
    (fun Φ => σ.comp ι ≠ 0 ∧
      Φ ∈ frequencyCoset (Z.map π).mkQ ((σ.comp ι).smulRight (π z)))
    (frequencyWeight_nonneg _)
    (fun Φ hΦ hp => good_frequency_preimage Z z τU π F ι τ fallback
      hτ folded σ Φ hΦ.1 hΦ.2 hp)
  by_cases hn : σ.comp ι ≠ 0
  · simpa [hn, Finset.sum_filter] using hi
  · simpa [hn] using hi

end ConditionalAgreement

section SliceBound

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H] [Fintype H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

omit [Fintype E] in
/-- The actual transferred affine-slice agreement supplies the sampled good
Fourier mass, including removal of characters trivial on the hidden kernel. -/
theorem goodCosetMass_lower_from_slice (Q : Submodule F2 E)
    [Fintype (H →ₗ[F2] Q)] [Fintype ((E ⧸ Q) →ₗ[F2] H)]
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι) (z' : E) (b : K)
    (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hQ : Module.finrank F2 Q ≤ r)
    (hsmall : 1 / (Fintype.card H : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤ 𝔼 A : (E ⧸ Q) →ₗ[F2] H,
      if F (N₀ + A.comp Q.mkQ) = b + ι ((N₀ + A.comp Q.mkQ) z')
      then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) ≤ goodCosetMass Q z' F ι := by
  let good : (K →ₗ[F2] F2) → Prop := fun σ => σ.comp ι ≠ 0
  let : DecidablePred good := fun _ => Classical.propDecidable _
  let C : (K →ₗ[F2] F2) → ℝ := fun σ =>
    sliceCorrelation Q.mkQ N₀ (tableSign F σ) ((σ.comp ι).smulRight z')
  let mass : (K →ₗ[F2] F2) → ℝ := fun σ =>
    ∑ Φ ∈ frequencyCoset Q.mkQ ((σ.comp ι).smulRight z'),
      frequencyWeight (tableSign F σ) Φ
  have habs : α / 4 ≤ 𝔼 σ : K →ₗ[F2] F2, |C σ| :=
    hagreement.trans (agreement_le_average_abs_correlation Q.mkQ N₀ F ι z' b)
  have hbad : (𝔼 σ : K →ₗ[F2] F2,
      if good σ then (0 : ℝ) else 1) ≤ α / 8 := by
    have ht := trivial_restriction_probability ι hι
    have heq : (𝔼 σ : K →ₗ[F2] F2,
        if good σ then (0 : ℝ) else 1) = 1 / (Fintype.card H : ℝ) := by
      calc
        _ = 𝔼 σ : K →ₗ[F2] F2, if σ.comp ι = 0 then (1 : ℝ) else 0 := by
          apply Finset.expect_congr rfl
          intro σ _
          by_cases hn : σ.comp ι = 0 <;> simp [good, hn]
        _ = _ := ht
    exact heq.le.trans hsmall
  have hselected : α / 8 ≤ 𝔼 σ : K →ₗ[F2] F2,
      if good σ then |C σ| else 0 := by
    have hh := remove_bad_characters C good (α / 4) (α / 8)
      (fun σ => sliceCorrelation_tableSign_abs_le_one Q.mkQ N₀ F σ
        ((σ.comp ι).smulRight z')) habs hbad
    linarith
  have hbound := average_coset_mass_lower C mass good
    ((2 : ℝ) ^ (ℓ * r)) (α / 8) (by positivity) (by positivity) hselected
    (by
      intro σ _
      have hcs := sliceCorrelation_sq_le_coset_mass Q.mkQ N₀ (tableSign F σ)
        ((σ.comp ι).smulRight z')
      have hc : ((frequencyCoset Q.mkQ ((σ.comp ι).smulRight z')).card : ℝ) ≤
          (2 : ℝ) ^ (ℓ * r) := by
        exact_mod_cast frequencyCoset_card_le Q ((σ.comp ι).smulRight z') ℓ r hH hQ
      exact hcs.trans (mul_le_mul_of_nonneg_right hc
        (Finset.sum_nonneg fun _ _ => frequencyWeight_nonneg _ _)))
  calc
    _ ≤ 𝔼 σ : K →ₗ[F2] F2, if good σ then mass σ else 0 := hbound
    _ = goodCosetMass Q z' F ι := by
      unfold goodCosetMass
      apply Finset.expect_congr rfl
      intro σ _
      by_cases hn : σ.comp ι = 0 <;> simp [good, mass, hn]

end SliceBound

section FinalConditionalBound

variable {U E H K : Type*}
variable [AddCommGroup U] [Module F2 U] [Fintype U]
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H] [Fintype H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 U] [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

theorem conditionalAgreement_from_slice (Z : Submodule F2 U) [Fintype Z]
    (z : U) (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    [Fintype (H →ₗ[F2] Z.map π)] [Fintype ((E ⧸ Z.map π) →ₗ[F2] H)]
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) (hτ : τ.comp π = τU)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h)
    (b : K) (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hZ : Module.finrank F2 Z ≤ r)
    (hsmall : 1 / (Fintype.card H : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤ 𝔼 A : (E ⧸ Z.map π) →ₗ[F2] H,
      if F (N₀ + A.comp (Z.map π).mkQ) =
        b + ι ((N₀ + A.comp (Z.map π).mkQ) (π z)) then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) / (2 : ℝ) ^ r ≤
      conditionalAgreement Z z τU hz π F ι τ fallback := by
  have hQ : Module.finrank F2 (Z.map π) ≤ r :=
    (Submodule.finrank_map_le π Z).trans hZ
  have hmass := goodCosetMass_lower_from_slice (Z.map π) N₀ F ι hι (π z) b
    α hα ℓ r hH hQ hsmall hagreement
  have hcard : ((candidates Z z τU).card : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast candidates_card_le_pow Z z τU r hZ
  have hcardpos : (0 : ℝ) < (candidates Z z τU).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (candidates_nonempty Z z τU hz))
  calc
    _ ≤ goodCosetMass (Z.map π) (π z) F ι / (2 : ℝ) ^ r :=
      div_le_div_of_nonneg_right hmass (by positivity)
    _ ≤ goodCosetMass (Z.map π) (π z) F ι / (candidates Z z τU).card :=
      div_le_div_of_nonneg_left (goodCosetMass_nonneg _ _ _ _) hcardpos hcard
    _ ≤ _ := conditionalAgreement_ge_mass_div_card Z z τU hz π F ι τ fallback hτ folded

end FinalConditionalBound

end UniqueGamesTheorem.Decoder.PrivateStrategy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Every nonempty affine row/column slice is an affine copy of the full space of
linear maps from the column quotient into the row kernel. This gives exact
uniform-law transport and preserves the affine evaluation offset.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureSliceQuotient

noncomputable section

variable {R E K L : Type*} [Field R]
  [AddCommGroup E] [AddCommGroup K] [AddCommGroup L]
  [Module R E] [Module R K] [Module R L]

/-- Exact uniform-law transport through the affine parametrization. -/
theorem expect_equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    [Fintype ((E ⧸ Q) →ₗ[R] A.ker)] [Fintype (AffineSlice A Q M₀)]
    (f : AffineSlice A Q M₀ → ℝ) :
    Finset.univ.expect (fun N => f (equiv A Q M₀ N)) = Finset.univ.expect f := by
  exact Fintype.expect_equiv (equiv A Q M₀) _ _ (fun _ => rfl)

end
end UniqueGamesTheorem.Inverse.RowErasureSliceQuotient

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_TableKeysLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact affine-table keys for outer questions

The retained data has one entry at every original block position.  A full entry
contains the equation *occurrence ID*, a singleton entry contains the actual
variable ID, and the first component is the entire reduced affine intercept.
The common coefficient-normalization implementation below is independent of
every latent-gadget existence or inverse theorem.

The explicit binary slope cases justify its use for the rank-zero, rank-one,
and rank-two rule.  In particular, the third-position pullback adds the parity
intercept twice, so exact sharing preserves the intercept as well as the slopes.
-/

namespace UniqueGamesTheorem.Decoder.TableKeys

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open scoped BigOperators

universe u v w

section ExactKeys

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
variable {k : Nat}

theorem key_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (P : ActualHomogeneous.E k →ₗ[F2] R) (c : R) :
    key occ names rhs (P + ActualHomogeneous.tau.smulRight c) =
      ((key occ names rhs P).1 + c, (key occ names rhs P).2) :=
  ActualCanonical.canonical_shift occ names rhs P c

variable [DecidableEq Name] [DecidableEq Id]

/-- Every displayed singleton is its actual bit, including the affine parity
intercept in position three.  Hidden occurrence IDs are forgotten precisely
at singleton positions and retained at full positions. -/
theorem projected_key_sharing
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R)
    (h : RawPrivateTable.displayed J names occ slot =
      RawPrivateTable.displayed J names occ' slot') :
    key occ names rhs (Y.comp (RawPrivateTable.projection J rhs occ slot)) =
      key occ' names rhs (Y.comp (RawPrivateTable.projection J rhs occ' slot')) :=
  RawPrivateTable.canonical_same_display J names rhs occ occ' slot slot' Y h

theorem projectedKey_pullback
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) :
    projectedKey J names rhs (RawPrivateTable.supported J names occ slot) Y =
      key occ names rhs (Y.comp (RawPrivateTable.projection J rhs occ slot)) := by
  apply projected_key_sharing
  exact RawPrivateTable.representative_display (RawPrivateTable.supported J names occ slot)

end ExactKeys

end UniqueGamesTheorem.Decoder.TableKeys

end

section

namespace UniqueGamesTheorem.Decoder.TableKeys

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R]
variable {k : Nat}

theorem projection_preserves_homogeneous (J : Finset (Fin k)) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (x : ActualHomogeneous.E k) :
    visibleTau J (RawPrivateTable.projection J rhs occ slot x) = ActualHomogeneous.tau x := by
  change ofBit (toBit x.1) = x.1
  exact ofBit_toBit _

theorem pullback_shift (J : Finset (Fin k)) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) (c : R) :
    (Y + (visibleTau J).smulRight c).comp (RawPrivateTable.projection J rhs occ slot) =
      Y.comp (RawPrivateTable.projection J rhs occ slot) +
        ActualHomogeneous.tau.smulRight c := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    projection_preserves_homogeneous]

variable [DecidableEq Name] [DecidableEq Id] [DecidableEq R]

omit [DecidableEq Name] [DecidableEq Id] in
/-- Constant translation commutes with exact sharing at the level of whole
reduced keys, including the removed alphabet component of the intercept. -/
theorem projectedKey_shift (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (Q : RawPrivateTable.SupportedV J names)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) (c : R) :
    projectedKey J names rhs Q (Y + (visibleTau J).smulRight c) =
      ((projectedKey J names rhs Q Y).1 + c, (projectedKey J names rhs Q Y).2) := by
  unfold projectedKey
  rw [pullback_shift, key_shift]

end UniqueGamesTheorem.Decoder.TableKeys

end

section

/-!
The concrete observation maps of the projected-advice experiment.

The full hidden draw contains the equation occurrence IDs, singleton positions,
projection choices, public row map, and the two sampled tables. The observations
are precisely `(U,A,Tπ,AMπ)` and `(O,A,T,AM)`. The hidden matrix is absent from
both observation types. Changing its kernel-valued part preserves both inputs
and hence every deterministic witness or strategy chosen from those inputs.
-/

namespace UniqueGamesTheorem.Decoder.AdviceExperiment

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness

noncomputable section

variable (k : Nat) (Id K W R : Type)
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup W] [Module F2 W]
variable [AddCommGroup R] [Module F2 R]

variable {k Id K W R}

variable {Name : Type} (names : Id → Fin 3 → Name)

variable (rhs : Id → F2)

theorem right_rows_attainable (d : Draw k Id K W R) :
    ∃ M : RawPartnerTarget.RawPoint d.singletons →ₗ[F2] K,
      d.rowMap.comp M = (rightObservation names d).2.rows :=
  ⟨d.hiddenMatrix, rfl⟩

end
end UniqueGamesTheorem.Decoder.AdviceExperiment

end

section

/-!
Restore actual orbit labels as a total function of the entire reduced key.
The arbitrary value at unrealized orbit bodies is used only to make this
function total; every table queried by the verifier and by the sparse
experiment is proved to be an actual realization.  Folding holds even for
the total extension, because the removed intercept is always restored.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysRestoration

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

section OrbitExtension

variable {Q T : Type} {s d : Nat}

theorem extendedLabel_actual (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (q : Q) :
    extendedLabel can label (ActualOrbit.body can q) = label (ActualOrbit.vertex can q) := by
  rw [extendedLabel, dite_eq_left ⟨q, rfl⟩]
  rfl

theorem restoredData_actual (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (q : Q) :
    restoredData can label (can q) = ActualOrbit.unfold can label q := by
  change extendedLabel can label (ActualOrbit.body can q) + ActualOrbit.offset can q = _
  rw [extendedLabel_actual]
  rfl

theorem restoredData_shift (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (D : Ambient s d × T) (c : Alphabet s) :
    restoredData can label (D.1 + (c, 0), D.2) = restoredData can label D + c := by
  simp only [restoredData, Prod.fst_add, Prod.snd_add, add_zero]
  exact (add_assoc _ _ _).symm

end OrbitExtension

theorem keyAnswer_actual (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (q : TableKeysGame.Query S k s d) :
    keyAnswer S k s d labeling (TableKeysGame.canonical S k s d q) =
      TableKeysGame.unfolded S k s d labeling q :=
  restoredData_actual _ _ q

theorem keyAnswer_shift (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (D : TableKeys.Key k (Fin S.variables) (Fin S.occurrences) (Ambient s d))
    (c : Alphabet s) :
    keyAnswer S k s d labeling (D.1 + (c, 0), D.2) = keyAnswer S k s d labeling D + c :=
  restoredData_shift _ _ D c

/-- No extra consistency predicate: projected answers equal full-query answers
for every table and every compatible hidden extension. -/
theorem projectedAnswer_pullback (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) :
    projectedAnswer S k s d labeling J
        (RawPrivateTable.supported J (ActualGame.names S) occ slot) Y =
      TableKeysGame.unfolded S k s d labeling
        (occ, Y.comp (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) := by
  unfold projectedAnswer
  rw [TableKeys.projectedKey_pullback]
  exact keyAnswer_actual S k s d labeling
    (occ, Y.comp (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))

/-- The visible table has the exact same affine folding law, with its genuine
homogeneous coordinate rather than an assumed or reconstructed first bit. -/
theorem projectedAnswer_fold (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) (c : Alphabet s) :
    projectedAnswer S k s d labeling J O
        (Y + (TableKeys.visibleTau J).smulRight (c, (0 : Vector d))) =
      projectedAnswer S k s d labeling J O Y + c := by
  unfold projectedAnswer
  rw [TableKeys.projectedKey_shift, keyAnswer_shift]

end

end UniqueGamesTheorem.Decoder.TableKeysRestoration

end

section

/-!
The private row table obtained from an actual single-orbit labeling.  Its
parameters are only the visible question, public row map, visible row value,
and complement table.  Neither a hidden full question nor a selected affine
witness is supplied to its definition.  Affine target intercepts remain
explicit when the matrix is expressed in private kernel coordinates.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysPrivateRow

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ActualSource

noncomputable section

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

theorem assemble_prod_shift (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (M₀ : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d) (h : A.ker) :
    (AdviceFibers.assemble A M₀ (N + (TableKeys.visibleTau J).smulRight h)).prod T =
      (AdviceFibers.assemble A M₀ N).prod T +
        (TableKeys.visibleTau J).smulRight ((h : Alphabet s), (0 : Vector d)) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change M₀ x + ((N x : Alphabet s) + TableKeys.visibleTau J x • (h : Alphabet s)) =
      (M₀ x + (N x : Alphabet s)) + TableKeys.visibleTau J x • (h : Alphabet s)
    exact (add_assoc _ _ _).symm
  · change T x = T x + TableKeys.visibleTau J x • (0 : Vector d)
    simp

/-- Folding on the hidden kernel is a consequence of the exact key action. -/
theorem rowAnswer_fold (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker) (h : A.ker) :
    rowAnswer S labeling J Q A rows T (N + (TableKeys.visibleTau J).smulRight h) =
      rowAnswer S labeling J Q A rows T N + (h : Alphabet s) := by
  unfold rowAnswer
  rw [assemble_prod_shift, TableKeysRestoration.projectedAnswer_fold]

theorem affine_target_on_row (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)
    (z : RawPartnerTarget.RawPoint J) (u : Alphabet s) :
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows) N z + u =
      (N z : Alphabet s) + targetIntercept J A rows z u :=
  AdviceFibers.assemble_affine_target A (AdviceFibers.observedBase A rows) N z u

end

end UniqueGamesTheorem.Decoder.TableKeysPrivateRow

end

section

/-!
# Decoding an actual transferred column slice

The point `Mstar` used to parametrize a transferred slice is distinct from the
canonical visible row base `observedBase A rows`.  The right strategy uses only
the latter.  Their kernel-valued difference appears solely in the analysis.
The exact quotient equivalence transports uniform slice agreement, including
the affine offset, to the conditional private-decoder theorem.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.TransferredDecoding

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ActualSource
open PrivateFourier PrivateStrategy
open scoped BigOperators Classical

open UniqueGamesTheorem.Inverse

attribute [local instance] Fintype.ofFinite

/-- Equality indicators depend on their propositions, not on the chosen
computable or classical decision procedures. Both deciders are explicit. -/
theorem indicator_congr (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q)
    (h : P ↔ Q) : @ite ℝ P dP 1 0 = @ite ℝ Q dQ 1 0 := by
  cases propext h
  cases Subsingleton.elim dP dQ
  rfl

section Rebase

variable {E K R : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup K] [Module F2 K] [AddCommGroup R] [Module F2 R]

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.TransferredDecoding.homFintype
/-- Rebase the complete quotient parametrization without changing its matrices. -/
theorem assemble_privateOrigin (A : K →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := E) A)
    (Mstar : E →ₗ[F2] K) (hstar : A.comp Mstar = rows.val)
    (Q : Submodule F2 E) (L : (E ⧸ Q) →ₗ[F2] A.ker) :
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows)
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
        (RowErasureSliceQuotient.equiv A Q Mstar L).val := by
  ext x
  change AdviceFibers.observedBase A rows x +
      ((Mstar x - AdviceFibers.observedBase A rows x) + (L (Q.mkQ x) : K)) =
    Mstar x + (L (Q.mkQ x) : K)
  rw [← add_assoc]
  congr 1
  rw [add_comm, sub_add_cancel]

end Rebase

section ActualSlice

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.TransferredDecoding.homFintype
/-- Exact transport from the actual conditional matrix slice to the private
Fourier coordinates.  `targetIntercept` uses the visible base, not `Mstar`. -/
theorem actual_slice_agreement_eq_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (Mstar : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (hstar : A.comp Mstar = rows.val) (Q : Submodule F2 (RawPartnerTarget.RawPoint J))
    [Fintype ((RawPartnerTarget.RawPoint J ⧸ Q) →ₗ[F2] A.ker)]
    [Fintype (RowErasureSliceQuotient.AffineSlice A Q Mstar)]
    (z' : RawPartnerTarget.RawPoint J) (u : Alphabet s) :
    (𝔼 M : RowErasureSliceQuotient.AffineSlice A Q Mstar,
      if TableKeysRestoration.projectedAnswer S k s d labeling J O (M.val.prod T) =
        M.val z' + u then (1 : ℝ) else 0) =
    𝔼 L : (RawPartnerTarget.RawPoint J ⧸ Q) →ₗ[F2] A.ker,
      if TableKeysPrivateRow.rowAnswer S labeling J O A rows T
          (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
        TableKeysPrivateRow.targetIntercept J A rows z' u +
          ((privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' : Alphabet s)
      then (1 : ℝ) else 0 := by
  rw [← RowErasureSliceQuotient.expect_equiv A Q Mstar]
  apply Finset.expect_congr rfl
  intro L _
  rw [← assemble_privateOrigin A rows Mstar hstar Q L]
  change (if TableKeysPrivateRow.rowAnswer S labeling J O A rows T
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows)
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' + u
    then (1 : ℝ) else 0) = _
  rw [TableKeysPrivateRow.affine_target_on_row J A rows
    (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' u]
  rw [add_comm (((privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z') : Alphabet s)
    (TableKeysPrivateRow.targetIntercept J A rows z' u)]

/-- Private policies for an actual restored labeling satisfy the conditional
decoding bound on every transferred good slice.  Folding and first-bit
preservation come from their concrete constructions, not additional premises. -/
theorem actual_transferred_decoding (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (Mstar : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (hstar : A.comp Mstar = rows.val)
    (Z : Submodule F2 (ActualHomogeneous.E k)) [Fintype Z]
    (z : ActualHomogeneous.E k) (hz : ActualHomogeneous.tau z = 1)
    (u : Alphabet s) (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 A.ker ≤ ℓ) (hZ : Module.finrank F2 Z ≤ r)
    [Fintype A.ker]
    [Fintype (RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)]
    [Fintype (A.ker →ₗ[F2] RawPartnerTarget.RawPoint J)]
    [Fintype (A.ker →ₗ[F2] Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))]
    [Fintype ((RawPartnerTarget.RawPoint J ⧸
      Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) →ₗ[F2] A.ker)]
    [Fintype (RowErasureSliceQuotient.AffineSlice A
      (Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) Mstar)]
    (hsmall : 1 / (Fintype.card A.ker : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤
      𝔼 M : RowErasureSliceQuotient.AffineSlice A
          (Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) Mstar,
        if TableKeysRestoration.projectedAnswer S k s d labeling J
            (RawPrivateTable.supported J (ActualGame.names S) occ slot) (M.val.prod T) =
          M.val (RawPrivateTable.projection J (ActualGame.rhs S) occ slot z) + u
        then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) / (2 : ℝ) ^ r ≤
      PrivateStrategy.conditionalAgreement Z z ActualHomogeneous.tau hz
        (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)
        (TableKeysPrivateRow.rowAnswer S labeling J
          (RawPrivateTable.supported J (ActualGame.names S) occ slot) A rows T)
        A.ker.subtype (TableKeys.visibleTau J) (visibleFallback J) := by
  let π := RawPrivateTable.projection J (ActualGame.rhs S) occ slot
  let O := RawPrivateTable.supported J (ActualGame.names S) occ slot
  have hτ : (TableKeys.visibleTau J).comp π = ActualHomogeneous.tau := by
    apply LinearMap.ext
    intro x
    exact TableKeys.projection_preserves_homogeneous J (ActualGame.rhs S) occ slot x
  apply conditionalAgreement_from_slice Z z ActualHomogeneous.tau hz π
    (privateOrigin A rows Mstar hstar)
    (TableKeysPrivateRow.rowAnswer S labeling J O A rows T)
    A.ker.subtype Subtype.val_injective (TableKeys.visibleTau J) (visibleFallback J) hτ
    (TableKeysPrivateRow.rowAnswer_fold S labeling J O A rows T)
    (TableKeysPrivateRow.targetIntercept J A rows (π z) u)
    α hα ℓ r hH hZ hsmall
  apply hagreement.trans_eq
  calc
    _ = _ := actual_slice_agreement_eq_private S labeling J O A rows T Mstar hstar
      (Z.map π) (π z) u
    _ = _ := by
      apply Finset.expect_congr rfl
      intro L _
      exact indicator_congr _ _ _ _ Iff.rfl

end ActualSlice

end UniqueGamesTheorem.Decoder.TransferredDecoding

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualAdviceStochasticBridgeLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

/-! Actual randomized point policies are transported locally into Boolean
answer kernels. Complete response tables are selected only after public advice
is fixed and before the remaining questions. No global deterministic policy
independent of public advice is asserted or needed for this upper bound. -/

namespace Clean.ActualAdviceStochasticBridge

open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.RawPartnerTarget
open Soundness.RepeatedGameBounds
open AnswerBridge ActualAdviceBridge

attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]
  [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem extendTargetKernel_apply (J : Finset (Fin k)) (names : O → Fin 3 → N)
    (kernel : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) →
      FiniteDistribution (TargetAnswer J))
    (V : RawPrivateTable.SupportedV J names) (Y : RawPoint J →ₗ[F2] D) :
    extendTargetKernel J names kernel V.val Y = kernel V Y := by
  unfold extendTargetKernel
  rw [dite_eq_left V.property]
  congr 1

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem decodeFirstMap_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap g.rhs
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw)) =
      Y.comp (projection g J draw) := by
  have h := ActualInputRows.firstMap_actual J g.rhs (fun j => (draw j).1)
    (fun j => indexSlot (draw j).2) (coordinates.toLinearMap.comp Y)
  have repack : (fun j => ((draw j).1,
      ConcreteExtraction.slotIndex (indexSlot (draw j).2))) = draw := by
    funext j
    simp
  rw [repack] at h
  unfold encodedMapCoefficients projection
  rw [h]
  apply LinearMap.ext
  intro x
  exact coordinates.symm_apply_apply _

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem decodeSecondMap_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)) = Y := by
  unfold encodedMapCoefficients
  rw [ActualInputRows.secondMap_actual]
  ext x
  simp

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem firstResponse_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    firstResponse coordinates g policy J
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw) =
      (policy.first J (fun j => (draw j).1) (Y.comp (projection g J draw))).pushforward
        (fun x => ActualPointAnswers.firstAnswer (fun j => g.rhs (draw j).1) x.val) := by
  unfold firstResponse
  rw [decodeFirstMap_actual]
  rfl

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem secondResponse_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    secondResponse coordinates g policy J
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw) =
      (policy.second J (displayedQuestion g J draw) Y).pushforward
        (fun v => ActualPointAnswers.secondAnswer
          (ActualPointAnswers.displayedRhs g.rhs (displayedQuestion g J draw).val) J v.val) := by
  unfold secondResponse
  rw [decodeSecondMap_actual, sample_question, extendTargetKernel_apply]

omit [DecidableEq O] [DecidableEq N] [Fintype D] in
theorem fixedMapSuccess_le (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    fixedMapSuccess μ g policy J Y ≤
      (StochasticBound.actualGame μ J g (encodedMapCoefficients coordinates J Y)).stochasticSuccess
        (firstResponse coordinates g policy J) (secondResponse coordinates g policy J) := by
  unfold fixedMapSuccess Game.stochasticSuccess StochasticBound.actualGame
    Simulation.weightedGame
  rw [FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro draw
  rw [firstResponse_actual, secondResponse_actual,
    FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro x
  rw [FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro v
  by_cases h : projection g J draw x.val = v.val
  · have accepted := ActualPointAnswers.actual_accepts J g
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw)
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)
      (fun j => indexSlot (draw j).2)
      (sample_question g J (encodedMapCoefficients coordinates J Y) draw)
      x.val v.val x.property h
    have firstQuestion :
        (actualFirst J (encodedMapCoefficients coordinates J Y) draw).question =
          (fun j => (draw j).1) := rfl
    rw [firstQuestion] at accepted
    have accepted' : (ActualProjection.predicateGame g (membershipBool J)).accepts
        (actualFirst J (encodedMapCoefficients coordinates J Y) draw)
        (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)
        (ActualPointAnswers.firstAnswer (fun j => g.rhs (draw j).1) x.val)
        (ActualPointAnswers.secondAnswer
          (ActualPointAnswers.displayedRhs g.rhs (displayedQuestion g J draw).val)
          J v.val) := by
      change ActualProjection.accepts g (PartnerMapCoordinates.activeOf J) _ _ _ _
      rw [← sample_question g J (encodedMapCoefficients coordinates J Y) draw]
      exact accepted
    simp only [h, ite_eq_left, accepted', decide_true, le_refl]
  · simp only [h, ite_false]
    split <;> norm_num

omit [DecidableEq O] [DecidableEq N] in
theorem success_le_native_stochastic (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    success μ g policy β hβ₀ hβ₁ ≤
      StochasticBound.nativeStochasticSuccess k μ g β hβ₀ hβ₁
        (responses coordinates g policy) := by
  unfold success StochasticBound.nativeStochasticSuccess responses
  apply expectation_mono
  intro mask
  calc
    _ ≤ (FiniteDistribution.uniform
        (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] D)).expectation
        (fun Y => (StochasticBound.actualGame μ (NativeExperiment.maskSet mask) g
          (encodedMapCoefficients coordinates (NativeExperiment.maskSet mask) Y)).stochasticSuccess
          (firstResponse coordinates g policy (NativeExperiment.maskSet mask))
          (secondResponse coordinates g policy (NativeExperiment.maskSet mask))) :=
      expectation_mono _ (fun Y => fixedMapSuccess_le coordinates μ g policy _ Y)
    _ = _ := uniform_maps_to_bits coordinates (NativeExperiment.maskSet mask)
      (fun gamma => (StochasticBound.actualGame μ (NativeExperiment.maskSet mask) g gamma).stochasticSuccess
        (firstResponse coordinates g policy (NativeExperiment.maskSet mask))
        (secondResponse coordinates g policy (NativeExperiment.maskSet mask)))

omit [DecidableEq O] [DecidableEq N] in
theorem success_le_some_native (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    ∃ strategy : NativeExperiment.MaskStrategy k Q O N,
      success μ g policy β hβ₀ hβ₁ ≤ NativeExperiment.success k μ g β hβ₀ hβ₁ strategy := by
  obtain ⟨strategy, h⟩ := StochasticBound.native_stochastic_le_deterministic
    k μ g β hβ₀ hβ₁ (responses coordinates g policy)
  exact ⟨strategy, (success_le_native_stochastic coordinates μ g policy β hβ₀ hβ₁).trans h⟩

end Clean.ActualAdviceStochasticBridge

/-! Section 5's clean bound for actual local linear-advice policies. The
sampling correspondence, private response conversion, weighted conditional
product law, and alphabet-independent repetition estimate are all invoked as
proved theorems. No sampler or repeated-game bound is an input hypothesis. -/

namespace Clean.ActualAdviceBound

open Foundations.Games Integration.BinaryLinear
open Soundness
open AnswerBridge

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D] [Fintype D]
  [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

/-- Arbitrary local randomized point policies obey the same bound. Complete
deterministic response tables may be chosen after the public mask/advice is
fixed, but before the remaining question pair is drawn. -/
theorem stochastic_success_le_dimension (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : ActualAdviceStochasticBridge.Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card D ≤ 2 ^ (dimW + rs)) :
    ActualAdviceStochasticBridge.success (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  have hcard' : Fintype.card (Experiment.Coefficient Q) ≤ 2 ^ (dimW + rs) :=
    (Fintype.card_congr (bitsCoordinatesEquiv coordinates).symm).le.trans hcard
  obtain ⟨strategy, h⟩ := ActualAdviceStochasticBridge.success_le_some_native coordinates
    (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁
  exact h.trans (Bound.native_clean_success_le_dimension k g ω β hβ₀ hβ₁
    strategy distinct hopt dimW rs hcard')

theorem stochastic_success_le_dimension_finite [FiniteDimensional F2 D]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : ActualAdviceStochasticBridge.Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card D ≤ 2 ^ (dimW + rs)) :
    ActualAdviceStochasticBridge.success (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k :=
  stochastic_success_le_dimension finiteCoordinates g ω policy β hβ₀ hβ₁
    distinct hopt dimW rs hcard

end Clean.ActualAdviceBound

/-!
The actual finite advice law. Uniform independent hidden/complement maps induce
the exact uniform visible-map law, including for rank-deficient public maps.
The whole-table comparison retains an arbitrary common occurrence/public-data
law, so weighted occurrence sampling is not replaced by uniform IDs.
-/

namespace Decoder.AdviceLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open ConditionalIncidences RawPartnerTarget RawMapLaw
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Clean

attribute [local instance] Classical.propDecidable

section VisibleMap

variable {k : ℕ} {K W R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup W] [Module F2 W] [Fintype W]
  [AddCommGroup R] [Module F2 R] [Fintype R]

omit [Fintype K] [Fintype W] [Fintype R] in
theorem visibleMap_raw (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (TM : (RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K)) :
    visibleMap A TM.1 TM.2 = rawMap J (W × A.range)
      (AdviceImageLaw.visibleCoefficients A (rawMapPairCoefficientsEquiv J TM)) := by
  exact (rawMap_coefficients J (W × A.range) (visibleMap A TM.1 TM.2)).symm

/-- Equality for every observable proves the whole joint visible-map law. -/
theorem uniform_visible_maps (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] (W × A.range)) → ℝ) :
    (𝔼 TM : (RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K),
      H (visibleMap A TM.1 TM.2)) =
      𝔼 Y : RawPoint J →ₗ[F2] (W × A.range), H Y := by
  calc
    _ = 𝔼 columns : RawSlot J → W × K,
        H (rawMap J (W × A.range) (AdviceImageLaw.visibleCoefficients A columns)) := by
      apply Fintype.expect_equiv (rawMapPairCoefficientsEquiv J)
      intro TM
      rw [visibleMap_raw]
    _ = 𝔼 gamma : RawSlot J → W × A.range, H (rawMap J (W × A.range) gamma) :=
      AdviceImageLaw.uniform_visible_coefficients (I := RawSlot J) (W := W) A
        (fun gamma : RawSlot J → W × A.range => H (rawMap J (W × A.range) gamma))
    _ = _ := PaddedLaw.uniform_rawMaps J H

theorem uniform_visible_maps_expectation (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] (W × A.range)) → ℝ) :
    (FiniteDistribution.uniform
      ((RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K))).expectation
        (fun TM => H (visibleMap A TM.1 TM.2)) =
      (FiniteDistribution.uniform (RawPoint J →ₗ[F2] (W × A.range))).expectation H := by
  simpa only [FiniteDistribution.expectation_uniform,
    ← Fintype.expect_eq_sum_div_card] using uniform_visible_maps A J H

variable {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualSuccess_eq_cleanSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (A : K →ₗ[F2] R)
    (policy : ActualAdviceStochasticBridge.Policies k g (W × A.range))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    actualSuccess μ g A policy β hβ₀ hβ₁ =
      ActualAdviceStochasticBridge.success μ g policy β hβ₀ hβ₁ := by
  unfold actualSuccess ActualAdviceStochasticBridge.success
  apply FiniteDistribution.expectation_congr
  intro mask
  exact uniform_visible_maps_expectation A (NativeExperiment.maskSet mask)
    (ActualAdviceStochasticBridge.fixedMapSuccess μ g policy (NativeExperiment.maskSet mask))

end VisibleMap

section WholeTable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
  [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

/-- Padding adds an independent uniform affine intercept. The full map's
variation is therefore exactly the sparse slope variation used in constants. -/
theorem paddedDistribution_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (paddedDistribution (V := V) rhs β hβ hβ').totalVariation
      (FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V)) =
        UniqueGamesTheorem.Foundations.Information.totalVariation
          (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
          (SparseLaw.uniformWeights (Fin k → V × V)) := by
  exact PaddedLaw.paddedMapWeights_totalVariation_eq_slope rhs β

end WholeTable

section CommonLaw

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

theorem withKernel_totalVariation (μ : FiniteDistribution Ω)
    (p q : Ω → FiniteDistribution Y) :
    (withKernel μ p).totalVariation (withKernel μ q) =
      ∑ x, μ.weight x * (p x).totalVariation (q x) := by
  unfold FiniteDistribution.totalVariation withKernel
  rw [Fintype.sum_prod_type]
  have inner (x : Ω) :
      (∑ y, |μ.weight x * (p x).weight y - μ.weight x * (q x).weight y|) =
        μ.weight x * ∑ y, |(p x).weight y - (q x).weight y| := by
    simp only [← mul_sub, abs_mul, abs_of_nonneg (μ.nonnegative x), ← Finset.mul_sum]
  simp_rw [inner]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

end CommonLaw

/-- Common occurrence/public randomness preserves the exact slope variation. -/
theorem wholeAdvice_totalVariation_eq_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (withKernel (occurrences.product publicLaw)
      (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ')).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) =
      UniqueGamesTheorem.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) := by
  rw [withKernel_totalVariation]
  simp_rw [paddedDistribution_totalVariation_eq_slope]
  rw [← Finset.sum_mul, (occurrences.product publicLaw).normalized, one_mul]

section ProjectionSeeds

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]

variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

theorem projectionSeed_expectation (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (projectionSeedDistribution β hβ hβ').expectation (fun s => H (projectSeedMap rhs s)) =
      (paddedDistribution rhs β hβ hβ').expectation H := by
  rw [paddedDistribution, FiniteDistribution.expectation_pushforward]
  change (∑ s : ProjectionSeed k V,
      PaddedLaw.choiceTupleWeight β s.1 * SparseLaw.uniformWeights _ s.2 *
        H (projectSeedMap rhs s)) =
    ∑ dz, PaddedLaw.drawWeights β k dz * H (PaddedLaw.paddedMap rhs dz.1 dz.2)
  rw [PaddedLaw.actual_projection_mixture_expectation, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  calc
    _ = PaddedLaw.choiceTupleWeight β c *
        ∑ Y : RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V,
          SparseLaw.uniformWeights _ Y *
            H (Y.comp (rawProjection rhs (PaddedLaw.choiceMask c) (PaddedLaw.choiceSlots c))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      exact mul_assoc _ _ _
    _ = _ := by rw [PaddedLaw.sum_uniformWeights_mul]

theorem projectionSeed_pushforward (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (projectionSeedDistribution β hβ hβ').pushforward (projectSeedMap (V := V) rhs) =
      paddedDistribution rhs β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro Y
  have h := projectionSeed_expectation rhs β hβ hβ' (fun X => if X = Y then 1 else 0)
  simpa [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite,
    PaddedLaw.pushforwardWeight] using h

end ProjectionSeeds

section MaskSlots

theorem maskSlotChoice_pushforward (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((bernoulli β hβ hβ').product (FiniteDistribution.uniform (Fin 3))).pushforward
      maskSlotChoice = choiceDistribution β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.uniform, Clean.bernoulli, choiceDistribution]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases c <;> simp [maskSlotChoice, PaddedLaw.choiceWeight, div_eq_mul_inv]
  ring

/-- The Option sampler is exactly the Bernoulli-mask sampler with independent
uniform slots at every position, including the full positions. This identity
allows arbitrary functions of the retained choices. -/
theorem choices_expectation {k : ℕ} (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (H : (Fin k → PaddedLaw.ProjectionChoice) → ℝ) :
    ((choiceDistribution β hβ hβ').iid k).expectation H =
      ((bernoulli β hβ hβ').iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
          H (choicesOfMaskSlots mask slots))) := by
  rw [← maskSlotChoice_pushforward, FiniteDistribution.iid_pushforward,
    FiniteDistribution.expectation_pushforward, NativeExperiment.expectation_iid_product,
    FiniteDistribution.iid_uniform]
  rfl

theorem choices_mask {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    PaddedLaw.choiceMask (choicesOfMaskSlots mask slots) =
      NativeExperiment.maskSet mask := by
  ext j
  cases h : mask j <;>
    simp [PaddedLaw.choiceMask, NativeExperiment.maskSet, choicesOfMaskSlots,
      maskSlotChoice, h]

theorem choices_active_slot {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3)
    (j : Fin k) (hj : mask j = true) :
    PaddedLaw.choiceSlots (choicesOfMaskSlots mask slots) j = PaddedLaw.decodeSlot (slots j) := by
  simp [PaddedLaw.choiceSlots, PaddedLaw.choiceSlot, choicesOfMaskSlots, maskSlotChoice, hj]

/-- The same identity with the entire original target map retained. This is
the full two-stage seed law, not merely the law of its padded marginal. -/
theorem projectionSeed_mask_slots_expectation {k : ℕ} {V : Type}
    [AddCommGroup V] [Module F2 V] [Fintype V]
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (H : ProjectionSeed k V → ℝ) :
    (projectionSeedDistribution β hβ hβ').expectation H =
      ((bernoulli β hβ hβ').iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
          (FiniteDistribution.uniform
            (RawPoint (PaddedLaw.choiceMask (choicesOfMaskSlots mask slots)) →ₗ[F2] V)).expectation
              (fun Y => H ⟨choicesOfMaskSlots mask slots, Y⟩))) := by
  calc
    _ = ((choiceDistribution β hβ hβ').iid k).expectation (fun c =>
        (FiniteDistribution.uniform (RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V)).expectation
          (fun Y => H ⟨c, Y⟩)) := by
      unfold FiniteDistribution.expectation
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro c _
      change (∑ Y, PaddedLaw.choiceTupleWeight β c * SparseLaw.uniformWeights _ Y * H ⟨c, Y⟩) =
        PaddedLaw.choiceTupleWeight β c * ∑ Y, SparseLaw.uniformWeights _ Y * H ⟨c, Y⟩
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      exact mul_assoc _ _ _
    _ = _ := choices_expectation β hβ hβ' _

end MaskSlots

section FullSeedLaw

variable {Ω Z Y : Type*} [Fintype Ω] [Fintype Z] [Fintype Y]

theorem product_pushforward_withKernel (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution Z) (f : Ω → Z → Y) :
    (μ.product ν).pushforward (fun xz => (xz.1, f xz.1 xz.2)) =
      withKernel μ (fun x => ν.pushforward (f x)) := by
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product, withKernel]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : Ω, if x = a then μ.weight x *
        ∑ z, if f x z = b then ν.weight z else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = a
      · subst x
        simp only [Prod.mk.injEq, true_and, ite_true, if_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      · simp [Prod.mk.injEq, hx]
    _ = _ := by simp

end FullSeedLaw

theorem fullSeed_pad_law {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward (fullSeedPad rhs) =
      withKernel (occurrences.product publicLaw)
        (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ') := by
  unfold fullSeedLaw fullSeedPad
  rw [product_pushforward_withKernel (occurrences.product publicLaw)
    (projectionSeedDistribution (k := k) (V := V) β hβ hβ')
    (fun ua seed => projectSeedMap (fun j => rhs (ua.1 j)) seed)]
  congr 1
  funext ua
  exact projectionSeed_pushforward (fun j => rhs (ua.1 j)) β hβ hβ'

theorem fullSeed_totalVariation_eq_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward
      (fullSeedPad rhs)).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) =
      UniqueGamesTheorem.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) := by
  rw [fullSeed_pad_law]
  exact wholeAdvice_totalVariation_eq_slope occurrences publicLaw rhs β hβ hβ'

theorem fullSeed_totalVariation_le_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward
      (fullSeedPad rhs)).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) ≤
      UniqueGamesTheorem.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) :=
  (fullSeed_totalVariation_eq_slope occurrences publicLaw rhs β hβ hβ').le

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

theorem completeDraw_seed (d : CompleteData k Id K W R) (N : PrivateMap d) :
    seedToActualDraw (completeAssemble d N).1.1 (completeAssemble d N).1.2
      (completeAssemble d N).2 = completeDraw d N := rfl

variable [Fintype Id] [Fintype K] [Fintype W] [Fintype R] [Fintype (K →ₗ[F2] R)]

omit [Fintype R] in
/-- The actual law has exactly constant point weights on every fiber of all
observed data, even for arbitrary occurrence and public-map laws. -/
theorem fullSeed_weight_observed (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (s : FullSeed k Id K W R) :
    (fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').weight s =
      completeWeight occurrences publicLaw β (completeObserve s) := rfl

omit [Fintype R] in
theorem fullSeed_weight_fiber (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (d : CompleteData k Id K W R)
    (s : FullSeed k Id K W R) (hs : completeObserve s = d) :
    (fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').weight s =
      completeWeight occurrences publicLaw β d := by
  rw [fullSeed_weight_observed, hs]

end Decoder.AdviceLaw

end UniqueGamesTheorem

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeInterfaceLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The size bound for simultaneous row/column slices.
Starting at any point of a nonempty slice, maps from the quotient by its column
span into the common row kernel give distinct points of that same affine slice.
Rank-nullity gives the dimension lower bound even when equations are dependent.
This argument uses only finite-dimensional linear algebra.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Matrix

namespace Slice

variable {ell m : ℕ}

theorem columnSpan_finrank_le (S : Slice ell m) :
    Module.finrank F2 S.columnSpan ≤ S.columns := by
  have h := finrank_range_le_card (R := F2) (M := Vector m) S.columnCoefficient
  change Module.finrank F2 (Submodule.span F2 (Set.range S.columnCoefficient)) ≤
    Fintype.card (Fin S.columns) at h
  rw [Fintype.card_fin] at h
  exact h

theorem card_directions (S : Slice ell m) :
    Nat.card S.Directions =
      2 ^ (Module.finrank F2 (Vector m ⧸ S.columnSpan) *
        Module.finrank F2 S.rowMap.ker) := by
  rw [Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

end Slice
end
end UniqueGamesTheorem.Inverse.Shortcode

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureMatrixLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Visible selection of a row-erasure witness. The selected description depends
only on the fixed table function, the row map, and the observed row value.
The full sampled matrix enters only the later event testing its membership in
the already selected slice. Classical choice fixes one witness once and for all;
proof irrelevance makes the choice independent of the goodness proof.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure

noncomputable section

variable {X Y A S D : Type*}

theorem SliceFamily.good_of_selectedDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) {d : D}
    (hselected : F.selectedDescription f α a s = some d) :
    F.GoodAdvice f α a s := by
  classical
  by_contra hgood
  simp only [SliceFamily.selectedDescription, dite_eq_right hgood] at hselected
  cases hselected

theorem SliceFamily.selectedDescription_spec (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) {d : D}
    (hselected : F.selectedDescription f α a s = some d) :
    F.rowMap d = a ∧ F.rowValue d = s ∧ (F.points d).Nonempty ∧
      α / 2 ≤ F.agreement f d := by
  have hgood := F.good_of_selectedDescription f α a s hselected
  rw [F.selectedDescription_of_good f α a s hgood] at hselected
  have hd := Option.some.inj hselected
  rw [← hd]
  exact F.chosenDescription_spec f α a s hgood

theorem SliceFamily.selectedMatch_iff_of_advice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) (hx : F.advice a x = s) :
    F.selectedMatch f α a x ↔
      x ∈ F.points (F.chosenDescription f α a s hgood) ∧
        f x = F.target (F.chosenDescription f α a s hgood) x := by
  unfold SliceFamily.selectedMatch
  rw [hx, F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hmem, hmatch⟩
    have he := Option.some.inj hd
    simpa only [he] using And.intro hmem hmatch
  · rintro ⟨hmem, hmatch⟩
    exact ⟨_, rfl, hmem, hmatch⟩

theorem SliceFamily.selectedEvent_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X)
    (hx : F.selectedEvent f α a x) : F.goodAt f α a x := by
  obtain ⟨d, hd, _⟩ := hx
  exact F.good_of_selectedDescription f α a (F.advice a x) hd

theorem SliceFamily.selectedMatch_event (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X)
    (hx : F.selectedMatch f α a x) : F.selectedEvent f α a x := by
  obtain ⟨d, hd, hmem, _⟩ := hx
  exact ⟨d, hd, hmem⟩

end
end UniqueGamesTheorem.Inverse.RowErasure

end

section

/-!
Finite partition estimates for a selector fixed by visible data. The observation
fibers need not have equal sizes. Each local counting inequality is summed over
the actual fibers, then divided by the size of the hidden sample space.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure.SelectionPartition

open scoped BigOperators Classical

noncomputable section

variable {X S : Type*} [Fintype X] [Fintype S]

/-- Arbitrary real summands can be compared fiber by fiber. No uniformity of
the induced observation distribution is asserted or required. -/
theorem expect_le_expect_of_fiber_sum_le (observe : X → S) (f g : X → ℝ)
    (hle : ∀ s, (∑ x ∈ fiber observe s, f x) ≤ ∑ x ∈ fiber observe s, g x) :
    Finset.univ.expect f ≤ Finset.univ.expect g := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_fiberwise Finset.univ observe f,
    ← Finset.sum_fiberwise Finset.univ observe g]
  exact Finset.sum_le_sum fun s _ => hle s

omit [Fintype S] in
/-- On good visible data, the selected event sums exactly over the selected
points, including for arbitrary real weights on the hidden sample. -/
theorem sum_event_mul_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (s : S) (hgood : good s) (w : X → ℝ) :
    (∑ x ∈ fiber observe s, indicator (event observe good chosen x) * w x) =
      ∑ x ∈ chosen s, w x := by
  have hsub : chosen s ⊆ fiber observe s := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, support s x hx⟩
  calc
    _ = ∑ x ∈ fiber observe s, if x ∈ chosen s then w x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [event, indicator, hobs, hgood, ite_mul]
    _ = ∑ x ∈ chosen s, if x ∈ chosen s then w x else 0 := by
      exact (Finset.sum_subset hsub (by
        intro x _ hx
        simp only [ite_eq_right hx])).symm
    _ = ∑ x ∈ chosen s, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ite_eq_left hx

omit [Fintype S] in
theorem sum_event_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (s : S) (hgood : good s) :
    (∑ x ∈ fiber observe s, indicator (event observe good chosen x)) =
      ((chosen s).card : ℝ) := by
  simpa using sum_event_mul_fiber observe good chosen support s hgood (fun _ => 1)

omit [Fintype S] in
theorem sum_match_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (hit : S → X → Prop) (s : S) (hgood : good s) :
    (∑ x ∈ fiber observe s, indicator (matchEvent observe good chosen hit x)) =
      ∑ x ∈ chosen s, indicator (hit s x) := by
  calc
    _ = ∑ x ∈ fiber observe s,
        indicator (event observe good chosen x) * indicator (hit s x) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      by_cases hevent : event observe good chosen x <;>
        by_cases hhit : hit s x <;>
        simp [matchEvent, indicator, hevent, hobs, hhit]
    _ = ∑ x ∈ chosen s, indicator (hit s x) :=
      sum_event_mul_fiber observe good chosen support s hgood (fun x => indicator (hit s x))

/-- A lower fraction inside every good fiber gives the same lower fraction
of the actual good-advice mass. Empty fibers and empty sample spaces are valid. -/
theorem mass_event_ge (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (c : ℝ)
    (hsize : ∀ s, good s →
      c * ((fiber observe s).card : ℝ) ≤ ((chosen s).card : ℝ)) :
    c * uniformMass (fun x => good (observe x)) ≤
      uniformMass (event observe good chosen) := by
  unfold uniformMass
  rw [Finset.mul_expect]
  apply expect_le_expect_of_fiber_sum_le observe
  intro s
  by_cases hgood : good s
  · rw [sum_event_fiber observe good chosen support s hgood]
    calc
      (∑ x ∈ fiber observe s, c * indicator (good (observe x))) =
          c * ((fiber observe s).card : ℝ) := by
        calc
          _ = ∑ _x ∈ fiber observe s, c := by
            apply Finset.sum_congr rfl
            intro x hx
            have hobs : observe x = s := (Finset.mem_filter.mp hx).2
            simp [indicator, hobs, hgood]
          _ = _ := by simp [mul_comm]
      _ ≤ _ := hsize s hgood
  · have hz : ∀ x ∈ fiber observe s,
        indicator (good (observe x)) = 0 ∧
          indicator (event observe good chosen x) = 0 := by
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [indicator, event, hobs, hgood]
    have hleft : (∑ x ∈ fiber observe s, c * indicator (good (observe x))) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [(hz x hx).1, mul_zero]
    have hright : (∑ x ∈ fiber observe s, indicator (event observe good chosen x)) = 0 :=
      Finset.sum_eq_zero fun x hx => (hz x hx).2
    rw [hleft, hright]

/-- A matching fraction in every selected good fiber survives averaging over
the hidden sample space, without any equiprobability assumption on fibers. -/
theorem mass_match_ge (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (hit : S → X → Prop) (β : ℝ)
    (hmatch : ∀ s, good s →
      β * ((chosen s).card : ℝ) ≤ ∑ x ∈ chosen s, indicator (hit s x)) :
    β * uniformMass (event observe good chosen) ≤
      uniformMass (matchEvent observe good chosen hit) := by
  unfold uniformMass
  rw [Finset.mul_expect]
  apply expect_le_expect_of_fiber_sum_le observe
  intro s
  by_cases hgood : good s
  · rw [← Finset.mul_sum, sum_event_fiber observe good chosen support s hgood,
      sum_match_fiber observe good chosen support hit s hgood]
    exact hmatch s hgood
  · have hz : ∀ x ∈ fiber observe s,
        indicator (event observe good chosen x) = 0 ∧
          indicator (matchEvent observe good chosen hit x) = 0 := by
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [indicator, event, matchEvent, hobs, hgood]
    have hleft : (∑ x ∈ fiber observe s, β * indicator (event observe good chosen x)) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [(hz x hx).1, mul_zero]
    have hright :
        (∑ x ∈ fiber observe s, indicator (matchEvent observe good chosen hit x)) = 0 :=
      Finset.sum_eq_zero fun x hx => (hz x hx).2
    rw [hleft, hright]

end
end UniqueGamesTheorem.Inverse.RowErasure.SelectionPartition

end

section

/-!
Exact uniform parametrization of the concrete row/column slice.  The quotient
parameter describes every point, not only a lower-bounding subfamily.  Affine
targets retain the base-point contribution and their original intercept.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode.Slice

noncomputable section
open scoped BigOperators Matrix

variable {ell m : ℕ}

theorem card_points_eq_directions (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) : S.points.card = Nat.card S.Directions := by
  rw [← Nat.card_eq_finsetCard, Nat.card_congr (S.directionEquiv M₀ h₀).symm]

end
end UniqueGamesTheorem.Inverse.Shortcode.Slice

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_MatrixCoordinates
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.MatrixCoordinates.homFintype
theorem affine_evaluation (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) (z : Fin (1 + 2 * k) → F2)
    (u : Fin ell → F2) :
    Inverse.Shortcode.evaluate M z + u =
      (mapEquiv k ell).symm M ((domainCoordinates k).symm z) + u := by
  change Inverse.Shortcode.evaluate M z + u =
    Matrix.toLin' M ((domainCoordinates k) ((domainCoordinates k).symm z)) + u
  rw [LinearEquiv.apply_symm_apply]
  rfl

end
end UniqueGamesTheorem.Decoder.MatrixCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact mass of a nonempty column slice within a fixed row-advice fiber. A
column span of dimension at most `r` costs at most `ell*r` binary degrees of
freedom. All inhomogeneous values are represented by the chosen base point.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureColumnMass

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Decoder.AdviceFibers
open UniqueGamesTheorem.Inverse.RowErasureSliceQuotient

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K]
  [AddCommGroup R] [Module F2 R]

theorem card_affineSlice (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (AffineSlice A Q M₀) =
      2 ^ (Module.finrank F2 (E ⧸ Q) * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (equiv A Q M₀).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

theorem card_rowFiber (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) =
      2 ^ (Module.finrank F2 E * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (rowFiberEquiv A (A.comp M₀) M₀ rfl).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

/-- The exact number of row-fiber points for each compatible specification on
the column span. Dependent column equations cost only their actual rank. -/
theorem card_rowFiber_eq_mul (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) = Nat.card (AffineSlice A Q M₀) *
      2 ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  rw [card_rowFiber, card_affineSlice, ← pow_add, ← Nat.add_mul,
    Q.finrank_quotient_add_finrank]

/-- The exact uniform fraction of the row fiber occupied by its compatible
affine column slice. -/
theorem column_fraction_eq (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) =
      1 / (2 : ℝ) ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  have hs : (0 : ℝ) < Nat.card (AffineSlice A Q M₀) := by
    rw [card_affineSlice]
    positivity
  rw [card_rowFiber_eq_mul A Q M₀]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_mul_cancel_left₀ hs.ne', one_div]

/-- At most `r` independent column constraints retain at least the fraction
`2^(-ell*r)` of any nonempty row-advice fiber. -/
theorem column_fraction_ge (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) (ell r : ℕ)
    (hQ : Module.finrank F2 Q ≤ r) (hK : Module.finrank F2 K ≤ ell) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) := by
  rw [column_fraction_eq]
  have hker : Module.finrank F2 A.ker ≤ ell := A.ker.finrank_le.trans hK
  have hexponent : Module.finrank F2 Q * Module.finrank F2 A.ker ≤ ell * r := by
    simpa only [Nat.mul_comm r ell] using Nat.mul_le_mul hQ hker
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)

end
end UniqueGamesTheorem.Inverse.RowErasureColumnMass

end

section

/-!
The actual finite matrix column event occupies at least `2^(-ell*r)` of its
row-advice fiber. This connects the intrinsic quotient-map count to the padded
descriptions used by the selector, without assuming independent equations.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass

noncomputable section
open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open UniqueGamesTheorem.Inverse.RowErasureMatrix
open scoped BigOperators Classical

theorem rowOnly_contains_iff {ell m : ℕ} (S : Slice ell m) (M : Mat ell m) :
    (rowOnly S).Contains M ↔ rowAdvice S.rowCoefficient M = S.rowValue := by
  constructor
  · intro h
    funext i j
    exact h.1 i j
  · intro h
    constructor
    · intro i j
      exact congrFun (congrFun h i) j
    · intro i
      exact Fin.elim0 i

theorem rowOnly_points {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).points = rowFiber S.rowCoefficient S.rowValue := by
  ext M
  simp only [Slice.points, rowFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    rowOnly_contains_iff]

theorem contains_rowOnly {ell m : ℕ} (S : Slice ell m) {M : Mat ell m}
    (hM : S.Contains M) : (rowOnly S).Contains M := by
  exact ⟨hM.1, fun i => Fin.elim0 i⟩

theorem rowOnly_columnSpan {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).columnSpan = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨i, _⟩
  exact Fin.elim0 i

theorem rowOnly_quotient_finrank {ell m : ℕ} (S : Slice ell m) :
    Module.finrank F2 (Shortcode.Vector m ⧸ (rowOnly S).columnSpan) = m := by
  have h := (rowOnly S).columnSpan.finrank_quotient_add_finrank
  have hz : Module.finrank F2 (rowOnly S).columnSpan = 0 := by
    rw [rowOnly_columnSpan]
    simp
  have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
  rw [hz, add_zero, hm] at h
  exact h

/-- The size of an actual nonempty row fiber, in the same coordinates used by
the selector's uniform matrix sample. -/
theorem rowFiber_card {ell m : ℕ} (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) :
    (rowFiber S.rowCoefficient S.rowValue).card =
      2 ^ (m * Module.finrank F2 S.rowMap.ker) := by
  rw [← rowOnly_points S,
    (rowOnly S).card_points_eq_directions M₀ (contains_rowOnly S h₀),
    (rowOnly S).card_directions, rowOnly_quotient_finrank]
  rfl

theorem rowFiber_nonempty {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) : (rowFiber d.1 d.2.1).Nonempty := by
  obtain ⟨M, hM⟩ := hne
  have hc : d.toSlice.Contains M := (Finset.mem_filter.mp hM).2
  refine ⟨M, (mem_rowFiber _ _ _).mpr ?_⟩
  funext i j
  exact hc.1 i j

/-- The chosen nonempty column event has the required mass inside its actual
row-advice fiber. The target coefficient and intercept do not affect its size. -/
theorem column_fraction_ge {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (d.toSlice.points.card : ℝ) / ((rowFiber d.1 d.2.1).card : ℝ) := by
  obtain ⟨M₀, hM₀⟩ := hne
  have h₀ : d.toSlice.Contains M₀ := (Finset.mem_filter.mp hM₀).2
  have hs : d.toSlice.points.card = Nat.card
      (RowErasureSliceQuotient.AffineSlice d.toSlice.rowMap d.toSlice.columnSpan
        (Matrix.toLin' M₀)) := by
    rw [d.toSlice.card_points_eq_directions M₀ h₀, d.toSlice.card_directions,
      RowErasureColumnMass.card_affineSlice]
  have hr : (rowFiber d.1 d.2.1).card = Nat.card
      (UniqueGamesTheorem.Decoder.AdviceFibers.RowFiber d.toSlice.rowMap
        (d.toSlice.rowMap.comp (Matrix.toLin' M₀))) := by
    have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
    rw [RowErasureColumnMass.card_rowFiber, hm]
    exact rowFiber_card d.toSlice M₀ h₀
  have h := RowErasureColumnMass.column_fraction_ge
    d.toSlice.rowMap d.toSlice.columnSpan (Matrix.toLin' M₀) ell r
    d.toSlice.columnSpan_finrank_le (by simp [Shortcode.Vector])
  rwa [← hs, ← hr] at h

end
end UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass

end

section

/-!
The selected column event under the actual uniform matrix and row-map samples.
The witness is fixed by visible row advice before testing the hidden matrix.
Fiber sizes are retained explicitly; no uniformity of row values is assumed.
The final averaging lemmas also allow arbitrary nonnegative context weights.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure

noncomputable section
open scoped BigOperators

variable {X Y A S D : Type*}

theorem SliceFamily.selectedPoints_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.selectedPoints f α a s = F.points (F.chosenDescription f α a s hgood) := by
  unfold SliceFamily.selectedPoints
  rw [F.selectedDescription_of_good f α a s hgood]

theorem SliceFamily.selectedHit_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) :
    F.selectedHit f α a s x ↔ f x = F.target (F.chosenDescription f α a s hgood) x := by
  unfold SliceFamily.selectedHit
  rw [F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hhit⟩
    have he := Option.some.inj hd
    simpa only [he] using hhit
  · intro hhit
    exact ⟨_, rfl, hhit⟩

theorem SliceFamily.selectedPoints_support (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X)
    (hx : x ∈ F.selectedPoints f α a s) : F.advice a x = s := by
  classical
  cases hd : F.selectedDescription f α a s with
  | none => simp [SliceFamily.selectedPoints, hd] at hx
  | some d =>
    have hspec := F.selectedDescription_spec f α a s hd
    have hmem : x ∈ F.points d := by
      simpa only [SliceFamily.selectedPoints, hd] using hx
    have h := F.points_row d x hmem
    rw [hspec.1, hspec.2.1] at h
    exact h

theorem SliceFamily.selectedEvent_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedEvent f α a x ↔
      F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x) := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedEvent_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x hx)).elim
    · intro hx
      exact (hg hx.1).elim

theorem SliceFamily.selectedMatch_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedMatch f α a x ↔
      (F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x)) ∧
          F.selectedHit f α a (F.advice a x) x := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedMatch_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg,
      F.selectedHit_of_good f α a (F.advice a x) hg x]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x (F.selectedMatch_event f α a x hx))).elim
    · intro hx
      exact (hg hx.1.1).elim

theorem SliceFamily.selectedPoints_match_sum (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    (α / 2) * ((F.selectedPoints f α a s).card : ℝ) ≤
      ∑ x ∈ F.selectedPoints f α a s, indicator (F.selectedHit f α a s x) := by
  classical
  have hspec := F.chosenDescription_spec f α a s hgood
  have hcard : (0 : ℝ) < (F.points (F.chosenDescription f α a s hgood)).card :=
    Nat.cast_pos.mpr hspec.2.2.1.card_pos
  have hagree := hspec.2.2.2
  rw [SliceFamily.agreement, Finset.expect_eq_sum_div_card] at hagree
  rw [F.selectedPoints_of_good f α a s hgood]
  simp_rw [F.selectedHit_of_good f α a s hgood]
  exact (le_div_iff₀ hcard).mp hagree

end
end UniqueGamesTheorem.Inverse.RowErasure

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

noncomputable section
open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass
open scoped BigOperators

variable {ell m r : ℕ}

theorem selectedPoints_column_mass (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) (s : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A s) :
    (1 / (2 : ℝ) ^ (ell * r)) * ((rowFiber A s).card : ℝ) ≤
      (((family ell m r).selectedPoints f α A s).card : ℝ) := by
  let d := (family ell m r).chosenDescription f α A s hgood
  have hspec := (family ell m r).chosenDescription_spec f α A s hgood
  have hne : d.toSlice.points.Nonempty := hspec.2.2.1
  have hcard : (0 : ℝ) < (rowFiber d.1 d.2.1).card :=
    Nat.cast_pos.mpr (rowFiber_nonempty d hne).card_pos
  have h := (le_div_iff₀ hcard).mp (column_fraction_ge d hne)
  have hA : d.1 = A := hspec.1
  have hs : d.2.1 = s := hspec.2.1
  rw [hA, hs] at h
  rw [(family ell m r).selectedPoints_of_good f α A s hgood]
  exact h

theorem selected_event_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (1 / (2 : ℝ) ^ (ell * r)) *
      uniformMass ((family ell m r).goodAt f α A) ≤
        uniformMass ((family ell m r).selectedEvent f α A) := by
  have h := SelectionPartition.mass_event_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    (1 / (2 : ℝ) ^ (ell * r))
    (fun s hg => by
      have hfiber : SelectionPartition.fiber ((family ell m r).advice A) s =
          rowFiber A s := by
        ext M
        simp only [SelectionPartition.fiber, rowFiber, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rfl
      rw [hfiber]
      exact selectedPoints_column_mass f α A s hg)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  rw [he] at h
  exact h

theorem selected_match_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (α / 2) * uniformMass ((family ell m r).selectedEvent f α A) ≤
      uniformMass ((family ell m r).selectedMatch f α A) := by
  have h := SelectionPartition.mass_match_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    ((family ell m r).selectedHit f α A)
    (α / 2) ((family ell m r).selectedPoints_match_sum f α A)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  have hm : SelectionPartition.matchEvent ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A)
      ((family ell m r).selectedHit f α A) =
      (family ell m r).selectedMatch f α A := by
    funext M
    exact propext ((family ell m r).selectedMatch_iff_points f α A M).symm
  rw [he, hm] at h
  exact h

theorem selectedEventMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (1 / (2 : ℝ) ^ (ell * r)) * adviceMass ((family ell m r).goodAt f α) ≤
      selectedEventMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_event_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  have hadvice : (𝔼 A : RowMap ell r, uniformMass ((family ell m r).goodAt f α A)) =
      adviceMass ((family ell m r).goodAt f α) := by
    simp only [uniformMass, adviceMass]
    exact Finset.expect_comm _ _ _
  rw [hadvice] at h
  exact h

theorem selectedMatchMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * selectedEventMass r f α ≤ selectedMatchMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_match_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  exact h

/-- The same bound for a uniform finite seed space, allowing repeated contexts. -/
theorem selectedEventMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α g₀ : ℝ)
    (hgood : g₀ ≤ 𝔼 q, adviceMass ((family ell m r).goodAt (f q) α)) :
    (1 / (2 : ℝ) ^ (ell * r)) * g₀ ≤ 𝔼 q, selectedEventMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedEventMass_ge (r := r) (f q) α)
  rw [← Finset.mul_expect] at h
  exact (mul_le_mul_of_nonneg_left hgood (by positivity)).trans h

theorem selectedMatchMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * (𝔼 q, selectedEventMass r (f q) α) ≤
      𝔼 q, selectedMatchMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedMatchMass_ge (r := r) (f q) α)
  rwa [← Finset.mul_expect] at h

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualSpectralLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Reduction.ActualSource
open UniqueGamesTheorem.Fourier.MatrixNoise

namespace UniqueGamesTheorem.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

theorem expect_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a, b) := by
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product Finset.univ Finset.univ f)

end UniqueGamesTheorem.Decoder.ActualSpectral

end

end

section

/-! The two full-table events used in the projected-witness transfer. Their
sample space contains actual occurrence tuples and complete affine tables,
but no projection choice. The selected witness depends on row advice only.
-/

namespace UniqueGamesTheorem.Decoder.ActualEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.ActualEvents.homFintype
theorem targetHit_implies_slice (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r)
    (h : targetHit S k s d r labeling α p = true) :
    sliceEvent S k s d r labeling α p = true := by
  exact of_decide_eq_true h |> fun hm => decide_eq_true
    ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch_event _ α _ _ hm)

theorem uniform_probability_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → Bool) :
    (FiniteDistribution.uniform Ω).probability p =
      𝔼 x : Ω, if p x then (1 : ℝ) else 0 := by
  simp only [FiniteDistribution.probability, FiniteDistribution.uniform,
    Fintype.expect_eq_sum_div_card, Finset.sum_div, ite_div, one_div, zero_div]

theorem unrestricted_slice_mass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    (unrestricted S k s d r).probability (sliceEvent S k s d r labeling α) =
      𝔼 q : Context S k d,
        RowErasureMatrix.selectedEventMass r
          (ActualGoodRows.table S k s d labeling q.1 q.2) α := by
  unfold unrestricted
  rw [uniform_probability_expect, ActualSpectral.expect_prod]
  apply Finset.expect_congr rfl
  intro q _
  rw [ActualSpectral.expect_prod]
  simp only [sliceEvent, RowErasureMatrix.selectedEventMass, uniformMass, indicator,
    decide_eq_true_eq]

theorem unrestricted_match_mass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    (unrestricted S k s d r).probability
      (fun p => sliceEvent S k s d r labeling α p && targetHit S k s d r labeling α p) =
      𝔼 q : Context S k d,
        RowErasureMatrix.selectedMatchMass r
          (ActualGoodRows.table S k s d labeling q.1 q.2) α := by
  have he : (fun p => sliceEvent S k s d r labeling α p && targetHit S k s d r labeling α p) =
      targetHit S k s d r labeling α := by
    funext p
    by_cases h : targetHit S k s d r labeling α p = true
    · simp [h, targetHit_implies_slice S k s d r labeling α p h]
    · simp [Bool.eq_false_iff.mpr h]
  rw [he]
  unfold unrestricted
  rw [uniform_probability_expect, ActualSpectral.expect_prod]
  apply Finset.expect_congr rfl
  intro q _
  rw [ActualSpectral.expect_prod]
  simp only [targetHit, RowErasureMatrix.selectedMatchMass, uniformMass, indicator,
    decide_eq_true_eq]

/-- The full-table slice event pays exactly one bounded column-fiber factor. -/
theorem slice_probability_lower (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α g₀ : ℝ)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α) :
    g₀ * (1 / (2 : ℝ) ^ (s * r)) ≤
      (unrestricted S k s d r).probability (sliceEvent S k s d r labeling α) := by
  rw [unrestricted_slice_mass]
  have h := RowErasureMatrix.selectedEventMass_contextual_ge (r := r)
    (fun q : Context S k d => ActualGoodRows.table S k s d labeling q.1 q.2) α g₀
    (by simpa only [ActualGoodRows.adviceMass, ActualSpectral.expect_prod] using hgood)
  simpa only [mul_comm] using h

theorem target_probability_lower (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    (α / 2) * (unrestricted S k s d r).probability (sliceEvent S k s d r labeling α) ≤
      (unrestricted S k s d r).probability
        (fun p => sliceEvent S k s d r labeling α p && targetHit S k s d r labeling α p) := by
  rw [unrestricted_slice_mass, unrestricted_match_mass]
  exact RowErasureMatrix.selectedMatchMass_contextual_ge (r := r)
    (fun q : Context S k d => ActualGoodRows.table S k s d labeling q.1 q.2) α

end
end UniqueGamesTheorem.Decoder.ActualEvents

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_VisiblePoliciesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Decoder.VisiblePolicies

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource PrivateStrategy
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d : ℕ} {R : Type} [AddCommGroup R] [Module F2 R]

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.VisiblePolicies.homFintype
theorem chosenWitness_spec {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) (h : ∃ w, good q w) :
    good q (chosenWitness good q) := by
  rw [chosenWitness, dite_eq_left h]
  exact Classical.choose_spec h

theorem rightPolicy_on_attainable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (q : RightInput S J s d R)
    (h : ∃ M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s,
      q.rowMap.comp M = q.rows) :
    rightPolicy S labeling J q =
      privateLaw
        (TableKeysPrivateRow.rowAnswer S labeling J q.question q.rowMap ⟨q.rows, h⟩ q.complement)
        q.rowMap.ker.subtype (TableKeys.visibleTau J) (TransferredDecoding.visibleFallback J) := by
  rw [rightPolicy, dite_eq_left h]

theorem rightPolicy_on_draw (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) :
    rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2 =
      privateLaw
        (TableKeysPrivateRow.rowAnswer S labeling draw.singletons
          (RawPrivateTable.supported draw.singletons (ActualGame.names S)
            draw.occurrences draw.positions)
          draw.rowMap (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement)
        draw.rowMap.ker.subtype (TableKeys.visibleTau draw.singletons)
        (TransferredDecoding.visibleFallback draw.singletons) := by
  rw [rightPolicy_on_attainable S labeling draw.singletons
    (AdviceExperiment.rightObservation (ActualGame.names S) draw).2
    (AdviceExperiment.right_rows_attainable (ActualGame.names S) draw)]
  rfl

/-- The private-decoding expression is exactly the actual local-kernel product
probability.  In particular there is no shared decoder random tape. -/
theorem observedAgreement_eq_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) :
    observedAgreement S labeling good draw =
      let w := chosenWitness good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)
      PrivateStrategy.conditionalAgreement w.columns w.coefficient
        ActualHomogeneous.tau w.firstBit (AdviceExperiment.projection (ActualGame.rhs S) draw)
        (TableKeysPrivateRow.rowAnswer S labeling draw.singletons
          (RawPrivateTable.supported draw.singletons (ActualGame.names S)
            draw.occurrences draw.positions)
          draw.rowMap (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement)
        draw.rowMap.ker.subtype (TableKeys.visibleTau draw.singletons)
        (TransferredDecoding.visibleFallback draw.singletons) := by
  rw [observedAgreement, rightPolicy_on_draw S labeling draw]
  dsimp only [PrivateStrategy.conditionalAgreement, leftPolicy]
  congr 1
  funext answers
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

end UniqueGamesTheorem.Decoder.VisiblePolicies

end

end

section

/-!
# The actual visible selector used by the stochastic decoder

At fixed labeling, the matrix table depends only on the occurrence question and
complement map. Its normalized row/column witness is selected from the observed
row map and row value. Transporting this witness through the actual homogeneous
coordinates supplies `VisiblePolicies.ResponseWitness`; the selected target's
affine intercept is retained separately, including exact equality on the slice.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.SelectedPolicies

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Inverse
open ActualSource VisiblePolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

theorem normalizedResponse_dimension (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    Module.finrank F2 (normalizedResponse S labeling α hα hsmall q hgood).columns ≤ r := by
  exact (Submodule.finrank_map_le (domainCoordinates k).symm.toLinearMap
    (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan).trans
    (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan_finrank_le

theorem chosenWitness_eq_normalizedResponse (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    chosenWitness (goodPredicate S labeling α hα hsmall) q =
      normalizedResponse S labeling α hα hsmall q hgood := by
  obtain ⟨hgood', hw⟩ := chosenWitness_spec (goodPredicate S labeling α hα hsmall) q
    ⟨normalizedResponse S labeling α hα hsmall q hgood, hgood, rfl⟩
  exact hw

/-- Coordinate transport keeps the actual affine target, including its selected
intercept; first-bit normalization never replaces it by a homogeneous target. -/
theorem normalized_target (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k)) :
    (RowErasureMatrix.family s (1 + 2 * k) r).target
        (normalizedDescription S labeling α hα hsmall q hgood) M =
      (mapEquiv k s).symm M (normalizedResponse S labeling α hα hsmall q hgood).coefficient +
        (normalizedDescription S labeling α hα hsmall q hgood).intercept :=
  affine_evaluation k s M _ _

end UniqueGamesTheorem.Decoder.SelectedPolicies

end

end

section

/-!
# Conditional success of the actual selected policies

This endpoint uses the normalized witness chosen from the left observation and
the private Fourier kernel chosen from the right observation. The hypothesis is
literal uniform agreement on a transferred affine column slice. Deriving that
hypothesis from the actual visible conditional law is the separate transfer
step; it is not assumed as an inverse theorem or as extra prover information.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.SelectedDecoding

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.homFintype
/-- The selected target-hit event uses exactly the transported coefficient and
its adjusted intercept. This identifies the event used by the mass estimates. -/
theorem selectedMatch_iff_normalized (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k))
    (hrow : RowErasureMatrix.rowAdvice (LinearMap.toMatrix' q.rowMap) M =
      mapEquiv k r q.rows) :
    (RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
        (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap) M ↔
      M ∈ (RowErasureMatrix.family s (1 + 2 * k) r).points
          (normalizedDescription S labeling α hα hsmall q hgood) ∧
        fullTable S labeling q M =
          (mapEquiv k s).symm M
              (normalizedResponse S labeling α hα hsmall q hgood).coefficient +
            (normalizedDescription S labeling α hα hsmall q hgood).intercept := by
  let F := RowErasureMatrix.family s (1 + 2 * k) r
  let D := normalizedDescription S labeling α hα hsmall q hgood
  let D₀ := F.chosenDescription (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood
  have he := F.selectedMatch_iff_of_advice (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood M hrow
  obtain ⟨_, _, _, _, _, hslice, _, htarget⟩ :=
    normalizedDescription_spec S labeling α hα hsmall q hgood
  have hp : F.points D = F.points D₀ := congrArg Shortcode.Slice.points hslice
  rw [← normalized_target S labeling α hα hsmall q hgood M]
  constructor
  · intro h
    obtain ⟨hm, hf⟩ := he.mp h
    refine ⟨hp.symm ▸ hm, ?_⟩
    rw [htarget M hm]
    exact hf
  · rintro ⟨hm, hf⟩
    have hm₀ : M ∈ F.points D₀ := hp ▸ hm
    apply he.mpr
    refine ⟨hm₀, ?_⟩
    rw [← htarget M hm₀]
    exact hf

/-- Rank-nullity supplies the small trivial-character probability for every
row map, including those with dependent rows. -/
theorem rowKernel_reciprocal_le (A : Alphabet s →ₗ[F2] Vector r) :
    1 / (Fintype.card A.ker : ℝ) ≤ 1 / (2 : ℝ) ^ (s - r) := by
  have hk : 2 ^ (s - r) ≤ Fintype.card A.ker := by
    simpa only [Nat.card_eq_fintype_card] using binary_kernel_card_lower A
  have hk' : (2 : ℝ) ^ (s - r) ≤ (Fintype.card A.ker : ℝ) := by
    exact_mod_cast hk
  exact one_div_le_one_div_of_le (by positivity) hk'

/-- The actual independently sampled local policies obey the decoding lower
bound at every datum with a transferred good slice for its selected witness. -/
theorem observedAgreement_lower (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (hgood : GoodAdvice S labeling α (AdviceExperiment.leftObservation (ActualGame.rhs S) draw))
    (Mstar : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s)
    (hstar : draw.rowMap.comp Mstar = draw.rowMap.comp draw.hiddenMatrix)
    (hagreement : α / 4 ≤ transferredAgreement S labeling draw
      (normalizedResponse S labeling α hα hsmall
        (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood)
      (normalizedDescription S labeling α hα hsmall
        (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood).intercept Mstar) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (s * r) / (2 : ℝ) ^ r ≤
      observedAgreement S labeling (goodPredicate S labeling α hα hsmall) draw := by
  let q := AdviceExperiment.leftObservation (ActualGame.rhs S) draw
  let w := normalizedResponse S labeling α hα hsmall q hgood
  let u := (normalizedDescription S labeling α hα hsmall q hgood).intercept
  have hH : Module.finrank F2 draw.rowMap.ker ≤ s := by
    simpa only [Module.finrank_fin_fun] using draw.rowMap.ker.finrank_le
  have hs : 1 / (Fintype.card draw.rowMap.ker : ℝ) ≤ α / 8 :=
    (rowKernel_reciprocal_le draw.rowMap).trans hsmall.le
  have h := TransferredDecoding.actual_transferred_decoding S labeling draw.singletons
    draw.occurrences draw.positions draw.rowMap
    (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement Mstar hstar
    w.columns w.coefficient w.firstBit u α hα.le s r hH
    (normalizedResponse_dimension S labeling α hα hsmall q hgood) hs hagreement
  rw [observedAgreement_eq_private,
    chosenWitness_eq_normalizedResponse S labeling α hα hsmall _ hgood]
  exact h

end UniqueGamesTheorem.Decoder.SelectedDecoding

end

end

section

/-!
# The selected padded slice is the actual projected affine slice

After fixing row advice, the selected full-domain column equations on `Mπ` are
exactly the equations fixing `M` on the image of the selected column span under
`π`. The equivalence keeps the same maps, so both uniform sampling and affine
target equality transport without changing the chosen intercept.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.ProjectedColumnSlice

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

/-- Exact key sharing identifies the selected full table with the projected
answer table at every possible hidden matrix in this visible fiber. -/
theorem fullTable_padded (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (M : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s) :
    fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)
        (mapEquiv k s (M.comp (AdviceExperiment.projection (ActualGame.rhs S) draw))) =
      TableKeysRestoration.projectedAnswer S k s d labeling draw.singletons
        (RawPrivateTable.supported draw.singletons (ActualGame.names S)
          draw.occurrences draw.positions) (M.prod draw.complement) := by
  unfold fullTable matrixTable
  rw [LinearEquiv.symm_apply_apply, TableKeysRestoration.projectedAnswer_pullback]
  rfl

end UniqueGamesTheorem.Decoder.ProjectedColumnSlice

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_UniformConditioning
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A finite experiment whose sample weights are constant on the selected
event becomes exactly uniform after conditioning on that event. The event is
allowed to have arbitrary positive mass, so this applies after the complete
visible datum and the chosen column constraints have both been fixed. -/

namespace UniqueGamesTheorem.Decoder.UniformConditioning

open Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem sum_over_event (given : Ω → Bool) (f : Ω → ℝ) :
    (∑ x, if given x then f x else 0) = ∑ x : {x : Ω // given x = true}, f x.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun x => by simp) f

theorem probability_as_subtype_sum (μ : FiniteDistribution Ω) (given : Ω → Bool) :
    μ.probability given = ∑ x : {x : Ω // given x = true}, μ.weight x.val :=
  sum_over_event given μ.weight

theorem probability_and_as_subtype_sum (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) :
    μ.probability (fun x => given x && event x) =
      ∑ x : {x : Ω // given x = true}, if event x.val then μ.weight x.val else 0 := by
  calc
    _ = ∑ x, if given x then (if event x then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      change (if given x && event x then μ.weight x else 0) = _
      cases given x <;> cases event x <;> rfl
    _ = _ := sum_over_event given _

theorem probability_of_constant_weight (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (c : ℝ) (hconstant : ∀ x, given x = true → μ.weight x = c) :
    μ.probability given = (Fintype.card {x : Ω // given x = true} : ℝ) * c := by
  rw [probability_as_subtype_sum]
  calc
    _ = ∑ _x : {x : Ω // given x = true}, c := by
      apply Finset.sum_congr rfl
      intro x _
      exact hconstant x.val x.property
    _ = _ := by simp [nsmul_eq_mul]

/-- Every remaining point receives equal conditional weight. Positivity of
the conditioning event justifies cancellation; no unconditional uniform law
on the original ambient experiment is required. -/
theorem condition_probability_uniform (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given)
    (c : ℝ) (hconstant : ∀ x, given x = true → μ.weight x = c) :
    (μ.condition given positive).probability event =
      𝔼 x : {x : Ω // given x = true}, if event x.val then (1 : ℝ) else 0 := by
  have hp := probability_of_constant_weight μ given c hconstant
  have hc : c ≠ 0 := by
    intro hz
    rw [hp, hz, mul_zero] at positive
    exact (lt_irrefl 0) positive
  have hn : (Fintype.card {x : Ω // given x = true} : ℝ) ≠ 0 := by
    intro hz
    rw [hp, hz, zero_mul] at positive
    exact (lt_irrefl 0) positive
  rw [FiniteDistribution.probability_condition, probability_and_as_subtype_sum, hp,
    Fintype.expect_eq_sum_div_card]
  have hnum : (∑ x : {x : Ω // given x = true}, if event x.val then μ.weight x.val else 0) =
      c * ∑ x : {x : Ω // given x = true}, if event x.val then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [hconstant x.val x.property]
    cases event x.val <;> simp
  rw [hnum]
  field_simp [hc, hn]

/-- A proved bijection with the actual affine matrix slice identifies the
conditional target probability with that slice's complete uniform average. -/
theorem condition_probability_equiv {Y : Type*} [Fintype Y]
    (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) (c : ℝ)
    (hconstant : ∀ x, given x = true → μ.weight x = c)
    (e : {x : Ω // given x = true} ≃ Y) (target : Y → Bool)
    (hevent : ∀ x, event x.val = target (e x)) :
    (μ.condition given positive).probability event =
      𝔼 y : Y, if target y then (1 : ℝ) else 0 := by
  rw [condition_probability_uniform μ given event positive c hconstant]
  apply Fintype.expect_equiv e
  intro x
  rw [hevent x]

end
end UniqueGamesTheorem.Decoder.UniformConditioning

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_VisibleTransferLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.VisibleTransfer

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Ω D : Type*} [Fintype Ω] [Fintype D]

omit [Fintype D] in
theorem fiberMass_nonnegative (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) (event : Ω → Bool) : 0 ≤ fiberMass μ observe d event :=
  μ.probability_nonnegative _

omit [Fintype D] in
theorem fiberMass_mono (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    fiberMass μ observe d event ≤ fiberMass μ observe d event' := by
  apply μ.probability_mono
  intro x hx
  simp only [fiberEvent, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
  exact ⟨hx.1, h x hx.2⟩

theorem sum_fiberMass (μ : FiniteDistribution Ω) (observe : Ω → D)
    (event : Ω → Bool) :
    ∑ d, fiberMass μ observe d event = μ.probability event := by
  classical
  unfold fiberMass FiniteDistribution.probability fiberEvent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases event x <;> simp

theorem observation_weight (μ : FiniteDistribution Ω) (observe : Ω → D) (d : D) :
    (μ.pushforward observe).weight d = fiberMass μ observe d (fun _ => true) := by
  classical
  simp [FiniteDistribution.pushforward, fiberMass, FiniteDistribution.probability,
    fiberEvent]

/-- The positive part of the witness margin is paid for by the probability of
the actual observed data, rather than by the larger hidden sample space. -/
theorem witness_margin_le_visible_probability
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    μ.probability (fun x => slice x && targetHit x) - threshold * μ.probability slice ≤
      (μ.pushforward observe).probability (visibleWitness μ observe slice targetHit threshold) := by
  classical
  have pointwise (d : D) :
      fiberMass μ observe d (fun x => slice x && targetHit x) -
          threshold * fiberMass μ observe d slice ≤
        if visibleWitness μ observe slice targetHit threshold d then
          (μ.pushforward observe).weight d else 0 := by
    have hs := fiberMass_nonnegative μ observe d slice
    have hm := fiberMass_nonnegative μ observe d (fun x => slice x && targetHit x)
    have hms : fiberMass μ observe d (fun x => slice x && targetHit x) ≤
        fiberMass μ observe d slice := by
      apply fiberMass_mono
      intro x hx
      simp only [Bool.and_eq_true] at hx
      exact hx.1
    have hmo : fiberMass μ observe d (fun x => slice x && targetHit x) ≤
        (μ.pushforward observe).weight d := by
      rw [observation_weight]
      exact fiberMass_mono μ observe d (fun _ _ => rfl)
    by_cases hgood : visibleWitness μ observe slice targetHit threshold d = true
    · simp only [hgood, ↓reduceIte]
      exact (sub_le_self _ (mul_nonneg hthreshold hs)).trans hmo
    · simp only [hgood, Bool.false_eq_true, ↓reduceIte]
      by_cases hpos : 0 < fiberMass μ observe d slice
      · have hnot : ¬ threshold * fiberMass μ observe d slice ≤
            fiberMass μ observe d (fun x => slice x && targetHit x) := by
          intro hle
          exact hgood (by simp [visibleWitness, hpos, hle])
        linarith
      · have hzero : fiberMass μ observe d slice = 0 := le_antisymm (le_of_not_gt hpos) hs
        rw [hzero, mul_zero, sub_zero]
        exact hms.trans_eq hzero
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun d _ => pointwise d
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_fiberMass,
    FiniteDistribution.probability] using hsum

omit [Fintype D] in
/-- On every selected datum the conditional distribution is defined on an
actual nonempty positive-mass slice and has the promised target agreement. -/
theorem visibleWitness_conditional
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (d : D)
    (h : visibleWitness μ observe slice targetHit threshold d = true) :
    ∃ hpositive : 0 < μ.probability (fiberEvent observe d slice),
      threshold ≤ (μ.condition (fiberEvent observe d slice) hpositive).probability targetHit := by
  classical
  have hh : 0 < fiberMass μ observe d slice ∧
      threshold * fiberMass μ observe d slice ≤
        fiberMass μ observe d (fun x => slice x && targetHit x) := by
    simpa only [visibleWitness, decide_eq_true_eq] using h
  unfold fiberMass at hh
  refine ⟨hh.1, ?_⟩
  rw [FiniteDistribution.probability_condition]
  have hsame : (fun x => fiberEvent observe d slice x && targetHit x) =
      fiberEvent observe d (fun x => slice x && targetHit x) := by
    funext x
    simp [fiberEvent, Bool.and_assoc]
  rw [hsame]
  exact (le_div_iff₀ hh.1).mpr hh.2

/-- A pair of full-table event probabilities transfers with error
`(1 + threshold) * TV`. This estimate precedes all conditioning. -/
theorem margin_transfer (μ ν : FiniteDistribution Ω)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    μ.probability (fun x => slice x && targetHit x) - threshold * μ.probability slice -
        (1 + threshold) * μ.totalVariation ν ≤
      ν.probability (fun x => slice x && targetHit x) - threshold * ν.probability slice := by
  have hm := μ.probability_sub_le_totalVariation ν (fun x => slice x && targetHit x)
  have hs := ν.probability_sub_le_totalVariation μ slice
  rw [FiniteDistribution.totalVariation_comm] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hthreshold
  nlinarith

/-- The whole-table comparison and the exact finite disintegration combine
without any assumption on conditional projection laws. -/
theorem wholeTable_transfer_to_visibleWitness
    {Γ : Type*} [Fintype Γ]
    (unrestricted : FiniteDistribution Ω) (actual : FiniteDistribution Γ)
    (pad : Γ → Ω) (observe : Γ → D) (slice targetHit : Ω → Bool)
    (threshold γ : ℝ) (hthreshold : 0 ≤ threshold)
    (hmargin : γ ≤
      unrestricted.probability (fun x => slice x && targetHit x) -
        threshold * unrestricted.probability slice -
        (1 + threshold) * unrestricted.totalVariation (actual.pushforward pad)) :
    γ ≤ (actual.pushforward observe).probability
      (visibleWitness actual observe (fun x => slice (pad x))
        (fun x => targetHit (pad x)) threshold) := by
  have transferred := margin_transfer unrestricted (actual.pushforward pad)
    slice targetHit threshold hthreshold
  simp only [FiniteDistribution.probability_pushforward] at transferred
  exact (hmargin.trans transferred).trans
    (witness_margin_le_visible_probability actual observe
      (fun x => slice (pad x)) (fun x => targetHit (pad x)) threshold hthreshold)

theorem projected_witness_mass
    {Γ : Type*} [Fintype Γ]
    (unrestricted : FiniteDistribution Ω) (actual : FiniteDistribution Γ)
    (pad : Γ → Ω) (observe : Γ → D) (slice targetHit : Ω → Bool)
    (α g₀ c : ℝ) (hα : 0 ≤ α)
    (hslice : g₀ * c ≤ unrestricted.probability slice)
    (hagreement : (α / 2) * unrestricted.probability slice ≤
      unrestricted.probability (fun x => slice x && targetHit x))
    (herror : (1 + α / 4) * unrestricted.totalVariation (actual.pushforward pad) ≤
      α * g₀ * c / 8) :
    α * g₀ * c / 8 ≤ (actual.pushforward observe).probability
      (visibleWitness actual observe (fun x => slice (pad x))
        (fun x => targetHit (pad x)) (α / 4)) := by
  apply wholeTable_transfer_to_visibleWitness unrestricted actual pad observe slice targetHit
    (α / 4) (α * g₀ * c / 8) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hslice (show 0 ≤ α / 4 by positivity)
  nlinarith

end
end UniqueGamesTheorem.Decoder.VisibleTransfer

end

section

namespace UniqueGamesTheorem.Decoder.UniformFibers

open Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω D Y : Type*}

theorem selectedFiberEquiv_point (observe : Ω → D) (d : D) (slice : Ω → Bool)
    (e : Y ≃ {x : Ω // observe x = d})
    (x : {x : Ω // VisibleTransfer.fiberEvent observe d slice x = true}) :
    (e (selectedFiberEquiv observe d slice e x).val).val = x.val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- Conditioning after fixing the complete datum and the selected column
event leaves precisely the uniform restricted private fiber. -/
theorem conditional_probability [Fintype Ω] [Fintype Y]
    (μ : FiniteDistribution Ω) (observe : Ω → D) (d : D)
    (slice event : Ω → Bool)
    (positive : 0 < μ.probability (VisibleTransfer.fiberEvent observe d slice))
    (c : ℝ) (hconstant : ∀ x, observe x = d → μ.weight x = c)
    (e : Y ≃ {x : Ω // observe x = d}) :
    (μ.condition (VisibleTransfer.fiberEvent observe d slice) positive).probability event =
      𝔼 y : {y : Y // slice (e y).val = true},
        if event (e y.val).val then (1 : ℝ) else 0 := by
  apply UniformConditioning.condition_probability_equiv μ
    (VisibleTransfer.fiberEvent observe d slice) event positive c
    (fun x hx => hconstant x (by
      have h : observe x = d ∧ slice x = true := by
        simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
      exact h.1))
    (selectedFiberEquiv observe d slice e)
    (fun y => event (e y.val).val)
  intro x
  rw [selectedFiberEquiv_point]

end
end UniqueGamesTheorem.Decoder.UniformFibers

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualAdviceUpperLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The clean-coordinate upper bound for the actual private-decoding policies.
At every fixed public map `A`, the visible coefficient space is
`Vector d × A.range`.  Its cardinality is at most `2^(d+rs)`, including when
`A` is rank deficient.  The true independent uniform maps `T,M`, the
Bernoulli mask, and all iid occurrence/position draws are retained by the
proved sampling equality, before averaging over the uniform public map.
-/

namespace UniqueGamesTheorem.Decoder.ActualAdviceUpper

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

theorem fullInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    fullInput S A occ ((AdviceLaw.visibleMap A T M).comp
      (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) =
      AdviceExperiment.leftObservation (ActualGame.rhs S) (actualDraw S A J occ slot T M) :=
  rfl

theorem projectedInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    projectedInput S A J (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M) =
      (AdviceExperiment.rightObservation (ActualGame.names S)
        (actualDraw S A J occ slot T M)).2 :=
  rfl

/-- The product of the two local policy kernels is literally the private
decoder's observed agreement probability, before any expectations are taken. -/
theorem policyAgreement_actual (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) (J : Finset (Fin k))
    (occ : Fin k → Fin S.occurrences) (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    (((policies S labeling good A).first J occ
        ((AdviceLaw.visibleMap A T M).comp
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))).product
      ((policies S labeling good A).second J
        (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M))).probability
        (fun answers => decide
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot answers.1.val =
            answers.2.val)) =
      VisiblePolicies.observedAgreement S labeling good (actualDraw S A J occ slot T M) := by
  dsimp only [policies, sourceIncidence]
  rw [fullInput_actual S A J occ slot T M, projectedInput_actual S A J occ slot T M]
  rfl

/-- The clean experiment's indexed slot is exactly the actual bit projection;
this includes the third-position parity intercept. -/
theorem source_projection_eq (S : Source) (J : Finset (Fin k))
    (draw : Fin k → Fin S.occurrences × Fin 3) :
    Clean.ActualAdviceBridge.projection (sourceIncidence S) J draw =
      RawPrivateTable.projection J (ActualGame.rhs S) (fun j => (draw j).1)
        (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) := by
  simp only [Clean.ActualAdviceBridge.projection, sourceIncidence,
    RawPrivateTable.projection, ActualGame.rhs, toBit_ofBit]

theorem fixed_public_map_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (A : Alphabet s →ₗ[F2] Vector rs)
    (policy : Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  rw [AdviceLaw.actualSuccess_eq_cleanSuccess]
  exact Clean.ActualAdviceBound.stochastic_success_le_dimension_finite g ω policy
    β hβ₀ hβ₁ distinct hopt d rs (Clean.AdviceImageLaw.visible_card_binary_le d rs A)

/-- Rank deficiency is allowed separately at every public-map outcome. -/
theorem public_map_average_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : (A : Alphabet s →ₗ[F2] Vector rs) →
      Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A
          (policy A) β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  calc
    _ ≤ (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun _ => (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k) :=
      Clean.ActualAdviceBridge.expectation_mono _
        (fun A => fixed_public_map_bound g ω A (policy A) β hβ₀ hβ₁ distinct hopt)
    _ = _ := by
      rw [FiniteDistribution.expectation, ← Finset.sum_mul,
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).normalized, one_mul]

/-- The actual policies selected from the two separate observations obey the
bound under uniform occurrence IDs and every independent private response. -/
theorem actual_source_average_bound (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => AdviceLaw.actualSuccess
          (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
          (sourceIncidence S) A (policies S labeling good A) β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k :=
  public_map_average_bound (sourceIncidence S) (FiniteDistribution.uniform (Fin S.occurrences))
    (policies S labeling good) β hβ₀ hβ₁ distinct hopt

end

end UniqueGamesTheorem.Decoder.ActualAdviceUpper

end

section

/-!
The stochastic clean upper bound applies to the literal agreement of the two
actual local decoders.  The equality below retains every sampled mask, all
occurrence/position draws, and both independently uniform target maps.
-/

namespace UniqueGamesTheorem.Decoder.ActualAdviceSampling

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource ActualAdviceUpper

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

theorem fixedMapSuccess_eq_product {O N D : Type}
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [AddCommGroup D] [Module F2 D] [Fintype D]
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (policy : Clean.ActualAdviceStochasticBridge.Policies k g D)
    (J : Finset (Fin k)) (Y : RawPartnerTarget.RawPoint J →ₗ[F2] D) :
    Clean.ActualAdviceStochasticBridge.fixedMapSuccess μ g policy J Y =
      (FiniteDistribution.table (fun _ : Fin k => μ)).expectation (fun draw =>
        ((policy.first J (fun j => (draw j).1)
          (Y.comp (Clean.ActualAdviceBridge.projection g J draw))).product
          (policy.second J (Clean.ActualAdviceBridge.displayedQuestion g J draw) Y)).probability
          (fun answers => decide
            (Clean.ActualAdviceBridge.projection g J draw answers.1.val = answers.2.val))) := by
  unfold Clean.ActualAdviceStochasticBridge.fixedMapSuccess
  apply FiniteDistribution.expectation_congr
  intro draw
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum,
    mul_ite, decide_eq_true_eq, mul_one, mul_zero]

theorem fixedMapSuccess_eq_observed (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs) (J : Finset (Fin k))
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    Clean.ActualAdviceStochasticBridge.fixedMapSuccess μ (sourceIncidence S)
      (policies S labeling good A) J (AdviceLaw.visibleMap A T M) =
      (FiniteDistribution.table (fun _ : Fin k => μ)).expectation (fun draw =>
        VisiblePolicies.observedAgreement S labeling good
          (actualDraw S A J (fun j => (draw j).1)
            (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) T M)) := by
  rw [fixedMapSuccess_eq_product]
  apply FiniteDistribution.expectation_congr
  intro draw
  rw [source_projection_eq]
  exact policyAgreement_actual S labeling good A J (fun j => (draw j).1)
    (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) T M

theorem actualSuccess_eq_sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    AdviceLaw.actualSuccess μ (sourceIncidence S) A (policies S labeling good A)
        β hβ₀ hβ₁ = sampledAgreement S labeling good μ A β hβ₀ hβ₁ := by
  unfold AdviceLaw.actualSuccess sampledAgreement
  apply FiniteDistribution.expectation_congr
  intro mask
  apply FiniteDistribution.expectation_congr
  intro TM
  exact fixedMapSuccess_eq_observed S labeling good μ A _ TM.1 TM.2

/-- The dimension bound for the true average of the actual observation-local
decoders, including all ranks of the uniformly sampled public row map. -/
theorem sampledAgreement_average_bound (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
      (fun A => sampledAgreement S labeling good
        (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
        A β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  simp_rw [← actualSuccess_eq_sampledAgreement]
  exact actual_source_average_bound S labeling good β hβ₀ hβ₁ distinct hopt

end

end UniqueGamesTheorem.Decoder.ActualAdviceSampling

end

section

/-! The complete-data conditional law of the actual projected experiment.
The residual private matrix is uniform even when the occurrence law is
weighted and the public row map has deficient rank. -/

namespace UniqueGamesTheorem.Decoder.ActualConditionalLaw

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

section Conditioning

variable {k : ℕ} {Id K W R : Type}
    [Fintype Id] [AddCommGroup K] [Module F2 K] [Fintype K]
    [AddCommGroup W] [Module F2 W] [Fintype W]
    [AddCommGroup R] [Module F2 R] [Fintype R]

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.ActualConditionalLaw.homFintype
theorem probability_condition_complete
    (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (d : AdviceLaw.CompleteData k Id K W R)
    (slice event : AdviceLaw.FullSeed k Id K W R → Bool)
    (positive : 0 < (AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve d slice)) :
    ((AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').condition
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve d slice) positive).probability event =
        𝔼 N : {N : AdviceLaw.PrivateMap d // slice (AdviceLaw.completeAssemble d N) = true},
          if event (AdviceLaw.completeAssemble d N.val) then (1 : ℝ) else 0 := by
  exact UniformFibers.conditional_probability
    (AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ')
    AdviceLaw.completeObserve d slice event positive
    (AdviceLaw.completeWeight occurrences publicLaw β d)
    (AdviceLaw.fullSeed_weight_fiber occurrences publicLaw β hβ hβ' d)
    (AdviceLaw.completeFiberEquiv d)

end Conditioning

section Policy

variable {k s d r : ℕ}

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.ActualConditionalLaw.homFintype
/-- Both provers' answers, and their equality predicate, are fixed on the
complete observation fiber. Only the hidden matrix varies within that fiber. -/
theorem observedAgreement_completeDraw (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (N N' : AdviceLaw.PrivateMap data) :
    VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data N) =
      VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data N') := by
  unfold VisiblePolicies.observedAgreement
  rw [AdviceLaw.completeDraw_left, AdviceLaw.completeDraw_left]
  simp only [AdviceExperiment.rightObservation, AdviceLaw.completeDraw_rows]
  rfl

theorem datumAgreement_nonneg (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) :
    0 ≤ datumAgreement S labeling good data :=
  FiniteDistribution.probability_nonnegative _ _

/-- The actual success observable factors through the complete visible datum;
this justifies integrating a lower bound over visible-witness probability. -/
theorem observedAgreement_seed (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (x : AdviceLaw.FullSeed k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) :
    VisiblePolicies.observedAgreement S labeling good
      (AdviceLaw.seedToActualDraw x.1.1 x.1.2 x.2) =
        datumAgreement S labeling good (AdviceLaw.completeObserve x) := by
  let y := AdviceLaw.fullSeedCoordinatesEquiv x
  have hx : AdviceLaw.completeAssemble y.1 y.2 = x :=
    AdviceLaw.fullSeedCoordinatesEquiv.symm_apply_apply x
  rw [← hx, AdviceLaw.completeDraw_seed]
  change VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw y.1 y.2) =
    datumAgreement S labeling good (AdviceLaw.completeObserve (AdviceLaw.completeAssemble y.1 y.2))
  rw [AdviceLaw.completeObserve_assemble]
  exact observedAgreement_completeDraw S labeling good y.1 y.2 0

end Policy
end
end UniqueGamesTheorem.Decoder.ActualConditionalLaw

end

section

/-! The selected full-table events pulled back to the genuine projected
experiment. The comparison space forgets the projection, while complete data
retains it only for the subsequent finite conditional-law argument. -/

namespace UniqueGamesTheorem.Decoder.ActualSeedEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype_r466345_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
theorem targetHit_eq_selectedMatch (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) :
    targetHit S k s d r labeling α x = decide
      ((Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
        (SelectedPolicies.fullTable S labeling
          (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
        (LinearMap.toMatrix' (draw x).rowMap)
        (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))) :=
  rfl

/-- Positive selected-slice mass automatically supplies actual good left
advice; goodness is not an independent projected experiment assumption. -/
theorem slice_good (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) (hx : slice S k s d r labeling α x = true) :
    SelectedPolicies.GoodAdvice S labeling α
      (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x)) := by
  rw [slice_eq_selectedEvent] at hx
  have h := (Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent_good
    (SelectedPolicies.fullTable S labeling
      (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
    (LinearMap.toMatrix' (draw x).rowMap)
    (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))
    (of_decide_eq_true hx)
  change (Inverse.RowErasureMatrix.family s (1 + 2 * k) r).GoodAdvice
    (SelectedPolicies.fullTable S labeling
      (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
    (LinearMap.toMatrix' (draw x).rowMap)
    (MatrixCoordinates.mapEquiv k r
      ((draw x).rowMap.comp (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x))))
  rw [MatrixCoordinates.mapEquiv_rowAdvice]
  exact h

end
end UniqueGamesTheorem.Decoder.ActualSeedEvents

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualSeedPointwise
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Pointwise and uniform-law identification of the retained projection seed with
the actual decoder draw. Auxiliary slots at full positions affect neither the
projection nor the displayed target question. The entire target map is retained
when it is repacked into its independent hidden and complement components.
-/

namespace UniqueGamesTheorem.Decoder.ActualSeedPointwise

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

theorem rawProjection_congr_slots {k : Nat} (rhsB : Fin k → Bool)
    (J : Finset (Fin k)) (slot slot' : Fin k → PartnerProjection.Slot)
    (h : ∀ j, j ∈ J → slot j = slot' j) :
    RawPartnerTarget.rawProjection rhsB J slot =
      RawPartnerTarget.rawProjection rhsB J slot' := by
  have hp : PartnerLinear.projection rhsB (PartnerMapCoordinates.activeOf J) slot =
      PartnerLinear.projection rhsB (PartnerMapCoordinates.activeOf J) slot' := by
    apply LinearMap.ext
    intro x
    change PartnerProjection.project rhsB (PartnerMapCoordinates.activeOf J) slot x =
      PartnerProjection.project rhsB (PartnerMapCoordinates.activeOf J) slot' x
    apply PartnerProjection.partner_ext
    · rfl
    · rfl
    · funext j
      by_cases hj : j ∈ J
      · simp [PartnerProjection.project, PartnerMapCoordinates.activeOf, hj, h j hj]
      · simp [PartnerProjection.project, PartnerMapCoordinates.activeOf, hj]
  simp only [RawPartnerTarget.rawProjection, hp]

theorem supported_congr_slots {k : Nat} {Id Name : Type}
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (occ : Fin k → Id)
    (slot slot' : Fin k → PartnerProjection.Slot)
    (h : ∀ j, j ∈ J → slot j = slot' j) :
    RawPrivateTable.supported J names occ slot =
      RawPrivateTable.supported J names occ slot' := by
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ J
  · simp [RawPrivateTable.supported, RawPrivateTable.displayed, hj, h j hj]
  · simp [RawPrivateTable.supported, RawPrivateTable.displayed, hj]

variable {k s d rs : Nat}

/-- This applies to every hidden draw, with all its other data fixed. -/
theorem observedAgreement_changePositions (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector rs))
    (slot : Fin k → PartnerProjection.Slot)
    (hslot : ∀ j, j ∈ draw.singletons → draw.positions j = slot j) :
    VisiblePolicies.observedAgreement S labeling good draw =
      VisiblePolicies.observedAgreement S labeling good { draw with positions := slot } := by
  cases draw with
  | mk J occ positions A M T =>
    have hp := rawProjection_congr_slots (fun j => toBit (ActualGame.rhs S (occ j)))
      J positions slot hslot
    have hs := supported_congr_slots J (ActualGame.names S) occ positions slot hslot
    simp only [VisiblePolicies.observedAgreement, AdviceExperiment.leftObservation,
      AdviceExperiment.rightObservation, AdviceExperiment.projection,
      RawPrivateTable.projection, hp, hs]
    rfl

/-- Seed and actual-draw agreement before averaging any sampled map. -/
theorem seedAgreement_pointwise (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (occ : Fin k → Fin S.occurrences) (A : Alphabet s →ₗ[F2] Vector rs)
    (choices : Fin k → PaddedLaw.ProjectionChoice)
    (slot : Fin k → PartnerProjection.Slot)
    (hslot : ∀ j, j ∈ PaddedLaw.choiceMask choices →
      PaddedLaw.choiceSlots choices j = slot j)
    (Y : RawPartnerTarget.RawPoint (PaddedLaw.choiceMask choices) →ₗ[F2]
      (Alphabet s × Vector d)) :
    VisiblePolicies.observedAgreement S labeling good
        (AdviceLaw.seedToActualDraw occ A ⟨choices, Y⟩) =
      VisiblePolicies.observedAgreement S labeling good
        (ActualAdviceUpper.actualDraw S A (PaddedLaw.choiceMask choices) occ slot
          ((LinearMap.snd F2 (Alphabet s) (Vector d)).comp Y)
          ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp Y)) :=
  observedAgreement_changePositions S labeling good
    (AdviceLaw.seedToActualDraw occ A ⟨choices, Y⟩) slot hslot

private theorem seedAgreement_repack_at (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (occ : Fin k → Fin S.occurrences) (A : Alphabet s →ₗ[F2] Vector rs)
    (choices : Fin k → PaddedLaw.ProjectionChoice) (J : Finset (Fin k))
    (hJ : PaddedLaw.choiceMask choices = J)
    (slot : Fin k → PartnerProjection.Slot)
    (hslot : ∀ j, j ∈ PaddedLaw.choiceMask choices →
      PaddedLaw.choiceSlots choices j = slot j) :
    (FiniteDistribution.uniform
      (RawPartnerTarget.RawPoint (PaddedLaw.choiceMask choices) →ₗ[F2]
        (Alphabet s × Vector d))).expectation (fun Y =>
          VisiblePolicies.observedAgreement S labeling good
            (AdviceLaw.seedToActualDraw occ A ⟨choices, Y⟩)) =
      (FiniteDistribution.uniform
        ((RawPartnerTarget.RawPoint J →ₗ[F2] Vector d) ×
          (RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s))).expectation (fun TM =>
            VisiblePolicies.observedAgreement S labeling good
              (ActualAdviceUpper.actualDraw S A J occ slot TM.1 TM.2)) := by
  subst J
  simp only [FiniteDistribution.expectation_uniform, ← Fintype.expect_eq_sum_div_card]
  apply Fintype.expect_equiv
    ((LinearMap.prodEquiv F2).toEquiv.symm.trans (Equiv.prodComm _ _))
  intro Y
  exact seedAgreement_pointwise S labeling good occ A choices slot hslot Y

/-- Exact uniform-law identification with Bernoulli-mask and iid-slot sampling.
All dependent mask transport is confined to this theorem. -/
theorem seedAgreement_repack (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (occ : Fin k → Fin S.occurrences) (A : Alphabet s →ₗ[F2] Vector rs)
    (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    (FiniteDistribution.uniform
      (RawPartnerTarget.RawPoint
        (PaddedLaw.choiceMask (AdviceLaw.choicesOfMaskSlots mask slots)) →ₗ[F2]
          (Alphabet s × Vector d))).expectation (fun Y =>
            VisiblePolicies.observedAgreement S labeling good
              (AdviceLaw.seedToActualDraw occ A
                ⟨AdviceLaw.choicesOfMaskSlots mask slots, Y⟩)) =
      (FiniteDistribution.uniform
        ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
          (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2]
            Alphabet s))).expectation (fun TM =>
              VisiblePolicies.observedAgreement S labeling good
                (ActualAdviceUpper.actualDraw S A (Clean.NativeExperiment.maskSet mask)
                  occ (fun j => Clean.ActualAdviceBridge.indexSlot (slots j)) TM.1 TM.2)) := by
  apply seedAgreement_repack_at S labeling good occ A
    (AdviceLaw.choicesOfMaskSlots mask slots) (Clean.NativeExperiment.maskSet mask)
    (AdviceLaw.choices_mask mask slots)
  intro j hj
  have hmask : mask j = true := by
    rw [AdviceLaw.choices_mask] at hj
    simpa only [Clean.NativeExperiment.maskSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using hj
  exact AdviceLaw.choices_active_slot mask slots j hmask

end
end UniqueGamesTheorem.Decoder.ActualSeedPointwise

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualSeedSamplingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The complete seed used for the lower-bound conditioning argument and the
mask/slot/map experiment used for the clean upper bound have exactly the same
actual decoder success. Unused positions are removed only by the pointwise
observation equality; occurrence IDs and their ordered local copies remain.
-/

namespace UniqueGamesTheorem.Decoder.ActualSeedSampling

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource ActualAdviceUpper ActualAdviceSampling

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

theorem uniform_occurrence_slots {O : Type} [Fintype O] [Nonempty O]
    (H : (Fin k → O × Fin 3) → ℝ) :
    (FiniteDistribution.table (fun _ : Fin k =>
      Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform O))).expectation H =
      (FiniteDistribution.uniform (Fin k → O)).expectation (fun occ =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation
          (fun slots => H (fun j => (occ j, slots j)))) := by
  change (((FiniteDistribution.uniform O).product
    (FiniteDistribution.uniform (Fin 3))).iid k).expectation H = _
  rw [Clean.NativeExperiment.expectation_iid_product,
    FiniteDistribution.iid_uniform, FiniteDistribution.iid_uniform]

theorem sampledAgreement_eq_separated (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    sampledAgreement S labeling good
      (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
      A β hβ₀ hβ₁ =
      ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin S.occurrences)).expectation (fun occ =>
          (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
            (FiniteDistribution.uniform
              ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
                (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
              (drawAgreement S labeling good A mask occ slots)))) := by
  unfold sampledAgreement
  apply FiniteDistribution.expectation_congr
  intro mask
  calc
    _ = (FiniteDistribution.uniform
        ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
          (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
        (fun TM => (FiniteDistribution.uniform (Fin k → Fin S.occurrences)).expectation
          (fun occ => (FiniteDistribution.uniform (Fin k → Fin 3)).expectation
            (fun slots => drawAgreement S labeling good A mask occ slots TM))) := by
      apply FiniteDistribution.expectation_congr
      intro TM
      exact uniform_occurrence_slots _
    _ = _ := by
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro occ
      exact FiniteDistribution.expectation_comm _ _ _

/-- Exact sampler join: the complete hidden seed used by conditioning has
the same success as the genuine local-policy experiment used by the upper
bound, with no extra hidden-data conditioning on either side. -/
theorem fullSeedLaw_eq_sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
      (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
      (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)) β hβ₀ hβ₁).expectation
      (fun seed => VisiblePolicies.observedAgreement S labeling good
        (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) =
      (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => sampledAgreement S labeling good
          (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
          A β hβ₀ hβ₁) := by
  unfold AdviceLaw.fullSeedLaw
  rw [FiniteDistribution.expectation_product, FiniteDistribution.expectation_product,
    FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro A
  rw [sampledAgreement_eq_separated]
  calc
    _ = (FiniteDistribution.uniform (Fin k → Fin S.occurrences)).expectation (fun occ =>
        ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
          (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
            (FiniteDistribution.uniform
              ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
                (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
              (drawAgreement S labeling good A mask occ slots)))) := by
      apply FiniteDistribution.expectation_congr
      intro occ
      rw [AdviceLaw.projectionSeed_mask_slots_expectation]
      apply FiniteDistribution.expectation_congr
      intro mask
      apply FiniteDistribution.expectation_congr
      intro slots
      exact ActualSeedPointwise.seedAgreement_repack S labeling good occ A mask slots
    _ = _ := FiniteDistribution.expectation_comm _ _ _

theorem fullSeedLaw_upper (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
      (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
      (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)) β hβ₀ hβ₁).expectation
      (fun seed => VisiblePolicies.observedAgreement S labeling good
        (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  rw [fullSeedLaw_eq_sampledAgreement]
  exact sampledAgreement_average_bound S labeling good β hβ₀ hβ₁ distinct hopt

end

end UniqueGamesTheorem.Decoder.ActualSeedSampling

end

section

/-! Whole-table variation for the exact projected seed law in the selected
event coordinates. The projection is averaged out before the comparison. -/

namespace UniqueGamesTheorem.Decoder.ActualSeedVariation

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

theorem uniform_pushforward_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (e : X ≃ Y) :
    (FiniteDistribution.uniform X).pushforward e = FiniteDistribution.uniform Y := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  simp only [FiniteDistribution.transport, FiniteDistribution.uniform,
    Fintype.card_congr e]

theorem totalVariation_pushforward_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (μ ν : FiniteDistribution X) (e : X ≃ Y) :
    (μ.pushforward e).totalVariation (ν.pushforward e) = μ.totalVariation ν := by
  rw [FiniteDistribution.pushforward_equiv, FiniteDistribution.pushforward_equiv]
  unfold FiniteDistribution.totalVariation FiniteDistribution.transport
  congr 1
  exact e.symm.sum_comp (fun x => |μ.weight x - ν.weight x|)

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.ActualSeedVariation.homFintype
/-- Three independent uniform samples are uniform on their full product. -/
theorem ideal_full_uniform (S : Source) (k s d r : ℕ) :
    AdviceLaw.withKernel
      ((FiniteDistribution.uniform (ActualGame.Question S k)).product
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)))
      (fun _ => FiniteDistribution.uniform (ActualGame.Map k s d)) =
        FiniteDistribution.uniform (ActualEvents.FullTableSample S k s d r) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro p
  simp only [AdviceLaw.withKernel, FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul]
  ring

theorem ideal_pad_coordinates (S : Source) (k s d r : ℕ) :
    (AdviceLaw.withKernel
      ((FiniteDistribution.uniform (ActualGame.Question S k)).product
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)))
      (fun _ => FiniteDistribution.uniform (ActualGame.Map k s d))).pushforward
        (ActualEvents.fullTableEquiv S k s d r) = ActualEvents.unrestricted S k s d r := by
  rw [ideal_full_uniform]
  exact uniform_pushforward_equiv _

theorem actual_totalVariation_le_slope (S : Source) (k s d r : ℕ)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (ActualEvents.unrestricted S k s d r).totalVariation
      ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward (ActualSeedEvents.pad S k s d r)) ≤
        Foundations.Information.totalVariation
          (SparseLaw.independentWeights
            (SparseLaw.mixture β (SparseLaw.singletonPairWeights (Ambient s d))) k)
          (SparseLaw.uniformWeights (Fin k → Ambient s d × Ambient s d)) := by
  rw [FiniteDistribution.totalVariation_comm]
  have h := AdviceLaw.fullSeed_totalVariation_le_slope (V := Ambient s d)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r))
    (fun i => toBit (ActualGame.rhs S i)) β hβ hβ'
  rw [← ideal_pad_coordinates S k s d r]
  change ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward
      (fun x => ActualEvents.fullTableEquiv S k s d r
        (AdviceLaw.fullSeedPad (fun i => toBit (ActualGame.rhs S i)) x))).totalVariation _ ≤ _
  rw [← FiniteDistribution.pushforward_comp, totalVariation_pushforward_equiv]
  convert h using 1 <;> congr 4
  exact Subsingleton.elim _ _

end
end UniqueGamesTheorem.Decoder.ActualSeedVariation

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_SelectedFiberLaw
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual conditional selected-fiber agreement

The selected event is the full-table event used by the total-variation
comparison. On a positive complete-data fiber it becomes the uniform actual
affine row/column slice. The selector is fixed by the left observation; the
extra complete data and a supporting matrix occur only in this analysis.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.SelectedFiberLaw

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Inverse UniqueGamesTheorem.Foundations.Games
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates ActualSeedEvents
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

/-- The universe finset is independent of the chosen finite enumeration.
The instances are explicit so elaboration need not unfold either enumeration. -/
private theorem univ_congr {X : Type*} (i j : Fintype X) :
    @Finset.univ X i = @Finset.univ X j := by
  cases Subsingleton.elim i j
  rfl

variable {k s d r : ℕ}

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.SelectedFiberLaw.homFintype
/-- On the selected event, the actual full-table target-hit predicate equals
projected affine equality with the very same normalized coefficient/intercept. -/
theorem target_assemble_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (N : AdviceLaw.PrivateMap data)
    (hN : slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true) :
    targetHit S k s d r labeling α (AdviceLaw.completeAssemble data N) = true ↔
      TableKeysRestoration.projectedAnswer S k s d labeling (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) ((datumMatrix S data N).prod data.2.2.1) =
        datumMatrix S data N (datumProjection S data
          (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).coefficient) +
          (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept := by
  have hp := (slice_assemble_iff S labeling α hα hsmall data hgood N).mp hN
  rw [targetHit_eq_selectedMatch]
  change decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
      (fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S)
        (AdviceLaw.completeDraw data N))) α (LinearMap.toMatrix' data.1.2)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)))) = true ↔ _
  rw [datumLeft_eq, decide_eq_true_eq]
  refine (SelectedDecoding.selectedMatch_iff_normalized S labeling α hα hsmall
    (datumLeft S data) hgood _ (datumMatrix_rowAdvice S data N)).trans ?_
  have hp' : mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)) ∈
      (RowErasureMatrix.family s (1 + 2 * k) r).points
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood) := hp
  simp only [hp', true_and, LinearEquiv.symm_apply_apply]
  rw [show fullTable S labeling (datumLeft S data)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data))) =
      TableKeysRestoration.projectedAnswer S k s d labeling (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) ((datumMatrix S data N).prod data.2.2.1) from
    ProjectedColumnSlice.fullTable_padded S labeling (AdviceLaw.completeDraw data 0) (datumMatrix S data N)]
  rfl

/-- Positive mass supplies a supporting private coordinate in the selected
fiber; neither a hidden matrix nor good advice is an additional premise. -/
theorem exists_selected_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (data : Datum S k s d r)
    (positive : 0 < (law S k s d r β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))) :
    ∃ N : AdviceLaw.PrivateMap data,
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true := by
  have hex : ∃ x : Seed S k s d r,
      VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α) x = true := by
    by_contra hn
    have he : VisibleTransfer.fiberEvent AdviceLaw.completeObserve data
        (slice S k s d r labeling α) = fun _ => false := by
      funext x
      apply Bool.eq_false_iff.mpr
      intro hx
      exact hn ⟨x, hx⟩
    rw [he, FiniteDistribution.probability_false] at positive
    exact (lt_irrefl 0) positive
  obtain ⟨x, hx⟩ := hex
  have hx' : AdviceLaw.completeObserve x = data ∧ slice S k s d r labeling α x = true := by
    simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
  let N := (AdviceLaw.completeFiberEquiv data).symm ⟨x, hx'.1⟩
  have he : AdviceLaw.completeAssemble data N = x :=
    congrArg Subtype.val ((AdviceLaw.completeFiberEquiv data).apply_symm_apply ⟨x, hx'.1⟩)
  exact ⟨N, he.symm ▸ hx'.2⟩

theorem good_of_selected_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data)
    (hN : slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true) :
    GoodAdvice S labeling α (datumLeft S data) := by
  have hg := slice_good S k s d r labeling α (AdviceLaw.completeAssemble data N) hN
  change GoodAdvice S labeling α
    (AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data N)) at hg
  rw [datumLeft_eq] at hg
  exact hg

/-- Exact conditional target probability, with no assumed uniformity premise. -/
theorem conditional_eq_transferred (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true)
    (positive : 0 < (law S k s d r β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))) :
    ((law S k s d r β hβ hβ').condition
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))
        positive).probability (targetHit S k s d r labeling α) =
      SelectedDecoding.transferredAgreement S labeling (AdviceLaw.completeDraw data 0)
        (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood)
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept
        (datumMatrix S data Nstar) := by
  have enumeration : ActualAdviceUpper.publicMapFintype s r =
      (ActualConditionalLaw.homFintype : Fintype (Alphabet s →ₗ[F2] Vector r)) :=
    Subsingleton.elim _ _
  unfold law at positive ⊢
  revert positive
  rw [enumeration]
  intro positive
  refine (ActualConditionalLaw.probability_condition_complete
    (k := k) (Id := Fin S.occurrences) (K := Alphabet s) (W := Vector d) (R := Vector r)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (@FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)
      ActualConditionalLaw.homFintype inferInstance) β hβ hβ' data
    (slice S k s d r labeling α) (targetHit S k s d r labeling α) positive).trans ?_
  let : Fintype (RawPartnerTarget.RawPoint (PaddedLaw.choiceMask data.2.1) →ₗ[F2] Alphabet s) :=
    homFintype
  let : Fintype (RowErasureSliceQuotient.AffineSlice data.1.2
      ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
        (datumProjection S data)) (datumMatrix S data Nstar)) :=
    SelectedDecoding.affineSliceFintype _ _ _
  let f : {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true} → ℝ :=
    fun N => if targetHit S k s d r labeling α (AdviceLaw.completeAssemble data N.val) = true
      then 1 else 0
  let g : RowErasureSliceQuotient.AffineSlice data.1.2
      ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
        (datumProjection S data)) (datumMatrix S data Nstar) → ℝ :=
    fun M => if TableKeysRestoration.projectedAnswer S k s d labeling
        (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) (M.val.prod data.2.2.1) =
        M.val (datumProjection S data
          (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).coefficient) +
          (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept
      then 1 else 0
  have he : (𝔼 N, f N) = 𝔼 M, g M := by
    refine Fintype.expect_equiv
      (selectedPrivateEquiv S labeling α hα hsmall data hgood Nstar hstar) f g ?_
    intro N
    dsimp only [f, g]
    simp only [selectedPrivateEquiv_val]
    exact TransferredDecoding.indicator_congr _ _ _ _
      (target_assemble_iff S labeling α hα hsmall data hgood N.val N.property)
  calc
    _ = 𝔼 N, f N := by
      apply Finset.expect_congr (by ext N; simp only [Finset.mem_univ])
      intro N _
      exact TransferredDecoding.indicator_congr _ _ _ _ Iff.rfl
    _ = 𝔼 M, g M := he
    _ = _ := by
      unfold SelectedDecoding.transferredAgreement
      apply Finset.expect_congr (univ_congr _ _)
      intro M _
      exact TransferredDecoding.indicator_congr _ _ _ _ Iff.rfl

/-- Every complete visible datum selected by the actual witness event pays the
private-decoding success constant. Good advice and a nonempty transferred
slice follow from positivity and are not additional hypotheses. -/
theorem visibleWitness_decoding (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (data : Datum S k s d r)
    (hvisible : VisibleTransfer.visibleWitness (law S k s d r β hβ hβ')
      AdviceLaw.completeObserve (slice S k s d r labeling α)
      (targetHit S k s d r labeling α) (α / 4) data = true) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (s * r) / (2 : ℝ) ^ r ≤
      ActualConditionalLaw.datumAgreement S labeling (goodPredicate S labeling α hα hsmall) data := by
  obtain ⟨positive, hagree⟩ := VisibleTransfer.visibleWitness_conditional
    (law S k s d r β hβ hβ') AdviceLaw.completeObserve
    (slice S k s d r labeling α) (targetHit S k s d r labeling α) (α / 4) data hvisible
  obtain ⟨Nstar, hstar⟩ := exists_selected_private S labeling α β hβ hβ' data positive
  have hgood := good_of_selected_private S labeling α data Nstar hstar
  rw [conditional_eq_transferred S labeling α hα hsmall β hβ hβ' data hgood Nstar hstar positive] at hagree
  apply SelectedDecoding.observedAgreement_lower S labeling α hα hsmall
    (AdviceLaw.completeDraw data 0) hgood (datumMatrix S data Nstar) ?_ hagree
  exact (datumMatrix_rows S data Nstar).trans (datumMatrix_rows S data 0).symm

end UniqueGamesTheorem.Decoder.SelectedFiberLaw

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualProjectedTransfer
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The full selected-witness argument on the actual projected experiment.
The variation comparison precedes all conditioning. Its visible event then
pays the independent private decoder success on every selected datum. -/

namespace UniqueGamesTheorem.Decoder.ActualProjectedTransfer

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_r466345_2 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
/-- The actual complete-data event has positive mass depending only on the
fixed inverse and alphabet parameters. -/
theorem visible_mass (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
    ConstantSelection.visibleMass α g₀ s r ≤
      ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward AdviceLaw.completeObserve).probability
        (VisibleTransfer.visibleWitness (ActualSeedEvents.law S k s d r β hβ hβ')
          AdviceLaw.completeObserve (ActualSeedEvents.slice S k s d r labeling α)
          (ActualSeedEvents.targetHit S k s d r labeling α) (α / 4)) := by
  have htv := (ActualSeedVariation.actual_totalVariation_le_slope S k s d r β hβ hβ').trans hvariation
  have h := VisibleTransfer.projected_witness_mass
    (ActualEvents.unrestricted S k s d r) (ActualSeedEvents.law S k s d r β hβ hβ')
    (ActualSeedEvents.pad S k s d r) AdviceLaw.completeObserve
    (ActualEvents.sliceEvent S k s d r labeling α) (ActualEvents.targetHit S k s d r labeling α)
    α g₀ (1 / (2 : ℝ) ^ (s * r)) hα.le
    (ActualEvents.slice_probability_lower S k s d r labeling α g₀ hgood)
    (ActualEvents.target_probability_lower S k s d r labeling α)
    (ConstantSelection.variationBudget_suffices hα s r htv)
  have hc : α * g₀ * (1 / (2 : ℝ) ^ (s * r)) / 8 =
      ConstantSelection.visibleMass α g₀ s r := by
    unfold ConstantSelection.visibleMass
    ring
  rw [hc] at h
  exact h

/-- Integrating a pointwise lower bound over a genuine probability event. -/
theorem event_expectation_lower {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (event : Ω → Bool) (f : Ω → ℝ)
    (γ₁ γ₂ : ℝ) (hγ₂ : 0 ≤ γ₂) (hf : ∀ x, 0 ≤ f x)
    (hmass : γ₁ ≤ μ.probability event)
    (hpoint : ∀ x, event x = true → γ₂ ≤ f x) :
    γ₁ * γ₂ ≤ μ.expectation f := by
  have hweighted : μ.probability event * γ₂ ≤ μ.expectation f := by
    unfold FiniteDistribution.probability FiniteDistribution.expectation
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : event x = true
    · simp only [hx, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left (hpoint x hx) (μ.nonnegative x)
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, zero_mul]
      exact mul_nonneg (μ.nonnegative x) (hf x)
  exact (mul_le_mul_of_nonneg_right hmass hγ₂).trans hweighted

/-- End-to-end lower bound for actual local stochastic responses. No hidden
matrix, selected witness, or opposing observation is passed to a prover. -/
theorem actual_success_lower (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
    ConstantSelection.decodingMass α g₀ s r ≤
      (ActualSeedEvents.law S k s d r β hβ hβ').expectation
        (fun seed => VisiblePolicies.observedAgreement S labeling
          (SelectedPolicies.goodPredicate S labeling α hα hsmall)
          (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) := by
  let μ := ActualSeedEvents.law S k s d r β hβ hβ'
  let good := SelectedPolicies.goodPredicate S labeling α hα hsmall
  have h := event_expectation_lower (μ.pushforward AdviceLaw.completeObserve)
    (VisibleTransfer.visibleWitness μ AdviceLaw.completeObserve
      (ActualSeedEvents.slice S k s d r labeling α)
      (ActualSeedEvents.targetHit S k s d r labeling α) (α / 4))
    (ActualConditionalLaw.datumAgreement S labeling good)
    (ConstantSelection.visibleMass α g₀ s r) (ConstantSelection.conditionalMass α s r)
    (ConstantSelection.conditionalMass_pos hα s r).le
    (ActualConditionalLaw.datumAgreement_nonneg S labeling good)
    (visible_mass S labeling α g₀ β hα hβ hβ' hgood hvariation)
    (SelectedFiberLaw.visibleWitness_decoding S labeling α hα hsmall β hβ hβ')
  rw [FiniteDistribution.expectation_pushforward] at h
  unfold ConstantSelection.decodingMass
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply FiniteDistribution.expectation_congr
  intro seed
  exact ActualConditionalLaw.observedAgreement_seed S labeling good seed

end
end UniqueGamesTheorem.Decoder.ActualProjectedTransfer

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Outer.SourceIncidence

open UniqueGamesTheorem.Reduction ActualSource
open UniqueGamesTheorem.Foundations Games Target PCP
open UniqueGamesTheorem.Soundness.IncidenceExtraction
open UniqueGamesTheorem.Clean.IncidenceGap
open scoped BigOperators

noncomputable section

theorem names_distinct (S : Source) (hS : S.DistinctNames) :
    ∀ o i j, (incidence S).name o i = (incidence S).name o j → i = j := by
  intro o i j hij
  obtain ⟨h12, h13, h23⟩ := hS o
  fin_cases i <;> fin_cases j <;>
    simp_all [incidence, ActualGame.names, eq_comm]

end
end UniqueGamesTheorem.Outer.SourceIncidence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualMatrixContradiction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The contradiction uses the same actual seed and local decoder on both
sides. Its lower bound comes from full-table variation followed by visible
conditioning; its upper bound comes from the exact incidence sampler. -/

namespace UniqueGamesTheorem.Decoder.ActualMatrixContradiction

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

theorem law_expectation_eq (S : Source) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (f : ActualSeedEvents.Seed S k s d r → ℝ) :
    expectationOf (ActualSeedEvents.law S k s d r β hβ hβ') f =
      expectationOf (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
        (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ') f := by
  simp only [expectationOf, FiniteDistribution.expectation, ActualSeedEvents.law,
    AdviceLaw.fullSeedLaw, FiniteDistribution.product, FiniteDistribution.uniform]

theorem contradiction_oai (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : ActualProjectedTransfer.slopeVariation k s d β ≤
      ConstantSelection.variationBudget α g₀ s r)
    (hrate : (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k <
      ConstantSelection.decodingMass α g₀ s r)
    (hdistinct : S.DistinctNames)
    (hopt : Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) : False := by
  have hlower := ActualProjectedTransfer.actual_success_lower S labeling α g₀ β
    hα hsmall hβ hβ' hgood hvariation
  have hnames : ∀ o i j, (ActualAdviceUpper.sourceIncidence S).name o i =
      (ActualAdviceUpper.sourceIncidence S).name o j → i = j :=
    Outer.SourceIncidence.names_distinct S hdistinct
  have hupper := ActualSeedSampling.fullSeedLaw_upper S labeling
    (SelectedPolicies.goodPredicate S labeling α hα hsmall) β hβ hβ' hnames hopt
  have hbound : ConstantSelection.decodingMass α g₀ s r ≤
      (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k := by
    apply hlower.trans
    change expectationOf (ActualSeedEvents.law S k s d r β hβ hβ') _ ≤ _
    rw [law_expectation_eq]
    exact hupper
  exact (not_lt_of_ge hbound) hrate

end
end UniqueGamesTheorem.Decoder.ActualMatrixContradiction

end

end OAI
end

theorem solution : type_of% @OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.contradiction_oai := @OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.contradiction_oai
