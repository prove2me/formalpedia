-- Prove2me | solution 1 for OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:03:53.927022+00:00
-- url     : https://prove2.me/submissions/fa99c3b7-a324-40b2-98a1-fa76e24a9834

import Mathlib
import Definitions.Def_OAIQ085D027

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_MatrixCharacters
attribute [-instance] _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear

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

end DFVSGames.Fourier.MatrixCharacters
end

noncomputable section

namespace DFVSGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open DFVSGames.Fourier.MatrixCharacters

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [Fintype (F →ₗ[F2] E)] in
theorem linear_complexCoeff_character (S T : F →ₗ[F2] E) :
    fourierCoeff (linearTraceCharacter S : (E →ₗ[F2] F) → ℂ)
      (linearTraceCharacter T) = if T = S then 1 else 0 := by
  classical
  simp only [fourierCoeff, linearTraceCharacter_star, ← AddChar.add_apply,
    ← linearTraceCharacter_add, Fintype.expect_eq_sum_div_card,
    sum_linearTraceCharacter, linearMap_add_eq_zero_iff]
  by_cases h : S = T
  · subst T
    simp
  · simp [h, Ne.symm h]

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sum {J : Type*} (s : Finset J)
    (f : J → (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (∑ j ∈ s, f j) S = ∑ j ∈ s, linearCoeff (f j) S := by
  simp only [linearCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_smul (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (c • f) S = c * linearCoeff f S := by
  simp only [linearCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_character (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => (linearTraceCharacter S X).re) T =
      if T = S then 1 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [linearCoeff_complex]
  simp only [linearTraceCharacter_real, linear_complexCoeff_character]
  split_ifs <;> simp

end DFVSGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Derivatives
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

@[simp] theorem coeff_synthesis (a : (F →ₗ[F2] E) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (synthesis a) T = a T := by
  unfold synthesis
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem synthesis_energy (a : (F →ₗ[F2] E) → ℝ) :
    (𝔼 X, synthesis a X ^ 2) = ∑ T, a T ^ 2 := by
  rw [← linear_parseval]
  simp

@[simp] theorem coeff_component (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (component P f) T = if P T then linearCoeff f T else 0 := by
  exact coeff_synthesis _ _

theorem component_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X ^ 2) = ∑ T with P T, linearCoeff f T ^ 2 := by
  rw [component, synthesis_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

theorem component_energy_le (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  rw [component_energy, ← linear_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun T _ _ => sq_nonneg _)

theorem rankComponent_energy (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankComponent i f X ^ 2) =
      ∑ T with Module.finrank F2 T.range = i, linearCoeff f T ^ 2 := by
  unfold rankComponent
  rw [component_energy]
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro T _
    rfl

end
end DFVSGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyImageSplit
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
@[simp] theorem coeff_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (smallComponent ι f) T = smallCoeff ι f T :=
  coeff_synthesis _ _

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in

theorem smallComponent_energy (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, smallComponent ι f X ^ 2) =
      ∑ T ∈ Finset.univ.filter (fun T : F →ₗ[F2] I => Function.Surjective T),
        linearCoeff f (ι.comp T) ^ 2 := by
  rw [smallComponent, synthesis_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T <;> simp [smallCoeff, hT]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in

theorem ker_comp_of_injective (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (T : F →ₗ[F2] I) : (ι.comp T).ker = T.ker :=
  LinearMap.ker_comp_of_ker_eq_bot T (LinearMap.ker_eq_bot.mpr hι)

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSKernelOrbits

noncomputable section

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

theorem rangeEquivOfKerEq_apply (S T : F →ₗ[K] E) (hker : S.ker = T.ker) (x : F) :
    (rangeEquivOfKerEq S T hker ⟨S x, ⟨x, rfl⟩⟩ : E) = T x := by
  change (T.quotKerEquivRange ((Submodule.quotEquivOfEq S.ker T.ker hker)
    (S.quotKerEquivRange.symm ⟨S x, ⟨x, rfl⟩⟩)) : E) = T x
  have hs : (⟨S x, ⟨x, rfl⟩⟩ : S.range) =
      S.quotKerEquivRange (Submodule.Quotient.mk x) := rfl
  rw [hs, LinearEquiv.symm_apply_apply]
  rfl

theorem exists_postcomp_equiv_of_ker_eq (S T : F →ₗ[K] E)
    [FiniteDimensional K S.range] (hker : S.ker = T.ker) :
    ∃ g : E ≃ₗ[K] E, g.toLinearMap.comp S = T := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    (rangeEquivOfKerEq S T hker)
  refine ⟨g, ?_⟩
  ext x
  change g (S x) = T x
  exact (hg ⟨S x, ⟨x, rfl⟩⟩).symm.trans (rangeEquivOfKerEq_apply S T hker x)

end
end DFVSGames.Inverse.KMSKernelOrbits

namespace DFVSGames.Inverse.KMSBasisInvariant
noncomputable section
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem character_change (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E)
    (X : E →ₗ[F2] F) :
    linearTraceCharacter (g.toLinearMap.comp S) X =
      linearTraceCharacter S (X.comp g.toLinearMap) := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)]

theorem coefficient_change (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E) :
    linearCoeff f (g.toLinearMap.comp S) = linearCoeff f S := by
  unfold linearCoeff
  apply Fintype.expect_equiv (primalChange g)
  intro X
  change f X * (linearTraceCharacter (g.toLinearMap.comp S) X).re =
    f (X.comp g.toLinearMap) * (linearTraceCharacter S (X.comp g.toLinearMap)).re
  rw [character_change, hf g X]

end
end DFVSGames.Inverse.KMSBasisInvariant

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyFiber
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSKernelOrbitsFourier

open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant
open DFVSGames.Inverse.KMSKernelOrbits

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)]

theorem coefficient_eq_of_ker_eq (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (S T : F →ₗ[F2] E) (hker : S.ker = T.ker) :
    linearCoeff f S = linearCoeff f T := by
  obtain ⟨g, hg⟩ := exists_postcomp_equiv_of_ker_eq S T hker
  have h := coefficient_change f hf g S
  rw [hg] at h
  exact h.symm

end
end DFVSGames.Inverse.KMSKernelOrbitsFourier

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open DFVSGames.Fourier.MatrixCharacters

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]

theorem pointPad_injective (ι : J →ₗ[F2] E) (hι : Function.Injective ι) :
    Function.Injective (pointPad ι) := by
  intro x y h
  exact hι (congrArg Prod.fst h)

theorem pointLift_comp_prod (ι : J →ₗ[F2] E) (T : F →ₗ[F2] J)
    (ell : F →ₗ[F2] F2) :
    (pointLift ι).comp (T.prod ell) = (ι.comp T).prod ell := by
  ext x <;> rfl

theorem surjective_of_surjective_prod (T : F →ₗ[F2] J)
    (ell : F →ₗ[F2] F2) (h : Function.Surjective (T.prod ell)) :
    Function.Surjective T := by
  intro y
  obtain ⟨x, hx⟩ := h (y, 0)
  exact ⟨x, congrArg Prod.fst hx⟩

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

theorem sum_frequency_prod {A : Type*} [AddCommMonoid A]
    [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] F2)]
    [Fintype (F →ₗ[F2] (E × F2))]
    (g : (F →ₗ[F2] (E × F2)) → A) :
    ∑ S, g S = ∑ T : F →ₗ[F2] E, ∑ ell : F →ₗ[F2] F2, g (T.prod ell) := by
  rw [← frequencyProdEquiv.sum_comp g, Fintype.sum_prod_type]
  rfl

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem tracePair_pointAppend (T : F →ₗ[F2] E) (ell : F →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    linearTracePair (pointAppend X a) (T.prod ell) =
      linearTracePair X T + ell a := by
  have hc : (pointAppend X a).comp (T.prod ell) =
      X.comp T + ell.smulRight a := by
    ext x
    rfl
  simp only [linearTracePair, hc, map_add, LinearMap.trace_smulRight]

omit [FiniteDimensional F2 E] in
theorem character_pointAppend (T : F →ₗ[F2] E) (ell : F →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    (linearTraceCharacter (T.prod ell) (pointAppend X a)).re =
      (linearTraceCharacter T X).re * (binarySign (ell a)).re := by
  simp [linearTraceCharacter_apply, tracePair_pointAppend, binarySign_add,
    Complex.mul_re]

omit [FiniteDimensional F2 E] in
theorem tracePair_pointShift (T : F →ₗ[F2] E) (φ : E →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    linearTracePair (X + φ.smulRight a) T = linearTracePair X T + φ (T a) := by
  have hc : (X + φ.smulRight a).comp T =
      X.comp T + (φ.comp T).smulRight a := by
    ext x
    rfl
  simp only [linearTracePair, hc, map_add, LinearMap.trace_smulRight,
    LinearMap.comp_apply]

omit [FiniteDimensional F2 E] in
theorem character_pointShift (T : F →ₗ[F2] E) (φ : E →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    (linearTraceCharacter T (X + φ.smulRight a)).re =
      (linearTraceCharacter T X).re * (binarySign (φ (T a))).re := by
  simp [linearTraceCharacter_apply, tracePair_pointShift, binarySign_add,
    Complex.mul_re]

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((E × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (E × F2))]
  [Fintype (F →ₗ[F2] F2)]

omit [Fintype (E →ₗ[F2] F)] in

theorem pointRestrict_eq_synthesis (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F) :
    pointRestrict f a = synthesis (fun T : F →ₗ[F2] E =>
      ∑ ell : F →ₗ[F2] F2, linearCoeff f (T.prod ell) * (binarySign (ell a)).re) := by
  funext X
  change f (pointAppend X a) = _
  rw [← linear_fourier_inversion f (pointAppend X a), sum_frequency_prod]
  simp only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro ell _
  rw [character_pointAppend]
  ring

theorem coeff_pointRestrict (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F)
    (T : F →ₗ[F2] E) :
    linearCoeff (pointRestrict f a) T =
      ∑ ell : F →ₗ[F2] F2, linearCoeff f (T.prod ell) * (binarySign (ell a)).re := by
  rw [pointRestrict_eq_synthesis, coeff_synthesis]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]

theorem sum_dependentRows [Fintype (F →ₗ[F2] F2)] [Fintype (J →ₗ[F2] F2)]
    (T : F →ₗ[F2] J) (hT : Function.Surjective T)
    (g : (F →ₗ[F2] F2) → ℝ) :
    (∑ ell, if ¬ Function.Surjective (T.prod ell) then g ell else 0) =
      ∑ φ : J →ₗ[F2] F2, g (φ.comp T) := by
  calc
    _ = ∑ ell ∈ Finset.univ.filter (fun ell => ¬ Function.Surjective (T.prod ell)),
        g ell := (Finset.sum_filter _ _).symm
    _ = ∑ ell : {ell : F →ₗ[F2] F2 // ¬ Function.Surjective (T.prod ell)},
        g ell.val := Finset.sum_subtype _ (by simp) _
    _ = _ := ((dependentRowEquiv T hT).sum_comp (fun ell => g ell.val)).symm

theorem sum_rows_split [Fintype (F →ₗ[F2] F2)] [Fintype (J →ₗ[F2] F2)]
    (T : F →ₗ[F2] J) (hT : Function.Surjective T)
    (g : (F →ₗ[F2] F2) → ℝ) :
    (∑ ell, g ell) =
      (∑ ell, if Function.Surjective (T.prod ell) then g ell else 0) +
        ∑ φ : J →ₗ[F2] F2, g (φ.comp T) := by
  rw [← sum_dependentRows T hT g, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  by_cases h : Function.Surjective (T.prod ell) <;> simp [h]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 J]
  [Fintype ((E × F2) →ₗ[F2] F)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 J] in

theorem coeff_dependent_extension (ι : J →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : F →ₗ[F2] J) (φ : J →ₗ[F2] F2) :
    linearCoeff f ((ι.comp T).prod (φ.comp T)) =
      linearCoeff f ((pointPad ι).comp T) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  ext x
  change (ι (T x), φ (T x)) = (0, 0) ↔ (ι (T x), (0 : F2)) = (0, 0)
  constructor
  · intro h
    have hfst := congrArg (fun z : E × F2 => z.1) h
    exact Prod.ext hfst rfl
  · intro h
    have hfst := congrArg (fun z : E × F2 => z.1) h
    have hTx : T x = 0 := hι (by simpa using hfst)
    simp [hTx]

variable [Fintype (F →ₗ[F2] F2)] [Fintype (J →ₗ[F2] F2)]

omit [FiniteDimensional F2 J] in
theorem point_row_recursion (ι : J →ₗ[F2] E) (hι : Function.Injective ι)
    (f : ((E × F2) →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : F →ₗ[F2] J) (hT : Function.Surjective T)
    (X : J →ₗ[F2] F) (a : F) :
    (∑ ell : F →ₗ[F2] F2,
      linearCoeff f ((ι.comp T).prod ell) * (binarySign (ell a)).re) *
        (linearTraceCharacter T X).re =
      (∑ ell : F →ₗ[F2] F2,
        (if Function.Surjective (T.prod ell)
          then linearCoeff f ((ι.comp T).prod ell) else 0) *
            (linearTraceCharacter (T.prod ell) (pointAppend X a)).re) +
      ∑ φ : J →ₗ[F2] F2, linearCoeff f ((pointPad ι).comp T) *
        (linearTraceCharacter T (X + φ.smulRight a)).re := by
  calc
    _ = ∑ ell : F →ₗ[F2] F2, linearCoeff f ((ι.comp T).prod ell) *
        (linearTraceCharacter (T.prod ell) (pointAppend X a)).re := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ell _
      rw [character_pointAppend]
      ring
    _ = _ := by
      rw [sum_rows_split T hT]
      congr 1
      · apply Finset.sum_congr rfl
        intro ell _
        split_ifs <;> simp
      · apply Finset.sum_congr rfl
        intro φ _
        rw [coeff_dependent_extension ι hι f hf, character_pointAppend,
          character_pointShift]
        rfl

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (F →ₗ[F2] (E × F2))]
  [Fintype (J →ₗ[F2] F)] [Fintype (F →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (J × F2))]

omit [Fintype (J →ₗ[F2] F)] [Fintype (J × F2 →ₗ[F2] F)] in

omit [FiniteDimensional F2 J] in
theorem point_restriction_recursion_add (ι : J →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (X : J →ₗ[F2] F) (a : F) :
    smallComponent ι (pointRestrict f a) X =
      smallComponent (pointLift ι) f (pointAppend X a) +
        ∑ φ : J →ₗ[F2] F2, smallComponent (pointPad ι) f (X + φ.smulRight a) := by
  simp only [smallComponent, synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_frequency_prod (fun S : F →ₗ[F2] (J × F2) =>
    smallCoeff (pointLift ι) f S * (linearTraceCharacter S (pointAppend X a)).re)]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (J →ₗ[F2] F2)))
    (t := (Finset.univ : Finset (F →ₗ[F2] J))), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T
  · simp only [smallCoeff, hT, ite_true, if_true, coeff_pointRestrict, pointLift_comp_prod]
    exact point_row_recursion ι hι f hf T hT X a
  · have hprod : ∀ ell : F →ₗ[F2] F2, ¬ Function.Surjective (T.prod ell) :=
      fun ell h => hT (surjective_of_surjective_prod T ell h)
    simp [smallCoeff, hT, hprod]

omit [Fintype (J →ₗ[F2] F)] [Fintype (J × F2 →ₗ[F2] F)] in

omit [FiniteDimensional F2 J] in
theorem point_restriction_recursion (ι : J →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (X : J →ₗ[F2] F) (a : F) :
    smallComponent (pointLift ι) f (pointAppend X a) =
      smallComponent ι (pointRestrict f a) X -
        ∑ φ : J →ₗ[F2] F2, smallComponent (pointPad ι) f (X + φ.smulRight a) := by
  have h := point_restriction_recursion_add ι hι f hf X a
  linarith

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem coeff_translate (f : (E →ₗ[F2] F) → ℝ) (Z : E →ₗ[F2] F)
    (T : F →ₗ[F2] E) :
    linearCoeff (fun X => f (X + Z)) T =
      linearCoeff f T * (linearTraceCharacter T Z).re := by
  have he : (fun X => f (X + Z)) =
      synthesis (fun S => linearCoeff f S * (linearTraceCharacter S Z).re) := by
    funext X
    rw [← linear_fourier_inversion f (X + Z)]
    simp only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro S _
    have hi (Y : E →ₗ[F2] F) : (linearTraceCharacter S Y).im = 0 := by
      simp
    rw [AddChar.map_add_eq_mul, Complex.mul_re, hi X, hi Z]
    ring
  rw [he, coeff_synthesis]

theorem sliceEnergy_translate (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (Z : E →ₗ[F2] F) :
    sliceEnergy P (fun X => f (X + Z)) = sliceEnergy P f := by
  unfold sliceEnergy
  apply Finset.sum_congr rfl
  intro T _
  rw [coeff_translate, mul_pow]
  have hs : (linearTraceCharacter T Z).re ^ 2 = 1 := by
    simp only [linearTraceCharacter_apply, binarySign]
    split_ifs <;> norm_num
  rw [hs, mul_one]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in

theorem sliceEnergy_sub_sum_le {J : Type*} [Fintype J]
    (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    (g : J → (E →ₗ[F2] F) → ℝ) :
    sliceEnergy P (fun X => f X - ∑ j, g j X) ≤
      2 * (sliceEnergy P f + (Fintype.card J : ℝ) * ∑ j, sliceEnergy P (g j)) := by
  have hc (T : F →ₗ[F2] E) :
      linearCoeff (fun X => f X - ∑ j, g j X) T =
        linearCoeff f T - ∑ j, linearCoeff (g j) T := by
    simp only [linearCoeff, sub_mul, Finset.sum_mul, Finset.expect_sub_distrib,
      Finset.expect_sum_comm]
  have hp (T : F →ₗ[F2] E) :
      (linearCoeff f T - ∑ j, linearCoeff (g j) T) ^ 2 ≤
        2 * (linearCoeff f T ^ 2 + (Fintype.card J : ℝ) *
          ∑ j, linearCoeff (g j) T ^ 2) := by
    have hcs : (∑ j, linearCoeff (g j) T) ^ 2 ≤
        (Fintype.card J : ℝ) * ∑ j, linearCoeff (g j) T ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : J => (1 : ℝ)) (fun j => linearCoeff (g j) T)
    nlinarith [sq_nonneg (linearCoeff f T + ∑ j, linearCoeff (g j) T)]
  calc
    _ ≤ ∑ T with P T, 2 * (linearCoeff f T ^ 2 + (Fintype.card J : ℝ) *
        ∑ j, linearCoeff (g j) T ^ 2) := by
      apply Finset.sum_le_sum
      intro T _
      rw [hc]
      exact hp T
    _ = _ := by
      unfold sliceEnergy
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_comm (s := Finset.univ.filter P) (t := Finset.univ)]

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSFourthMomentMixedRestriction
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

theorem coprod_add_shift (a : A →ₗ[F2] F) (X : I →ₗ[F2] F)
    (Z : (A × I) →ₗ[F2] F) :
    a.coprod X + Z =
      (a + Z.comp (LinearMap.inl F2 A I)).coprod
        (X + Z.comp (LinearMap.inr F2 A I)) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨u, v⟩
  change a u + X v + Z (u, v) =
    (a u + Z (u, 0)) + (X v + Z (0, v))
  have hZ : Z (u, v) = Z (u, 0) + Z (0, v) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using Z.map_add (u, 0) (0, v)
  rw [hZ]
  abel

theorem partialRestrict_translate
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (Z : (A × I) →ₗ[F2] F) :
    partialRestrict (fun Y => f (Y + Z)) a =
      fun X => partialRestrict f (a + Z.comp (LinearMap.inl F2 A I))
        (X + Z.comp (LinearMap.inr F2 A I)) := by
  funext X
  change f (a.coprod X + Z) =
    f ((a + Z.comp (LinearMap.inl F2 A I)).coprod
      (X + Z.comp (LinearMap.inr F2 A I)))
  rw [coprod_add_shift]

theorem partialRestrict_sub_sum {J : Type*} [Fintype J]
    (f : ((A × I) →ₗ[F2] F) → ℝ)
    (g : J → ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict (fun Y => f Y - ∑ j, g j Y) a =
      fun X => partialRestrict f a X - ∑ j, partialRestrict (g j) a X := rfl

variable [FiniteDimensional F2 I] [FiniteDimensional F2 F]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

theorem sliceEnergy_partialRestrict_translate
    (P : (F →ₗ[F2] I) → Prop)
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (Z : (A × I) →ₗ[F2] F) :
    sliceEnergy P (partialRestrict (fun Y => f (Y + Z)) a) =
      sliceEnergy P (partialRestrict f (a + Z.comp (LinearMap.inl F2 A I))) := by
  rw [partialRestrict_translate, sliceEnergy_translate]

theorem sliceEnergy_partialRestrict_sub_translates_le {J : Type*} [Fintype J]
    (P : (F →ₗ[F2] I) → Prop)
    (f : ((A × I) →ₗ[F2] F) → ℝ)
    (g : J → ((A × I) →ₗ[F2] F) → ℝ)
    (a : A →ₗ[F2] F) (Z : J → (A × I) →ₗ[F2] F) :
    sliceEnergy P (partialRestrict (fun Y => f Y - ∑ j, g j (Y + Z j)) a) ≤
      2 * (sliceEnergy P (partialRestrict f a) +
        (Fintype.card J : ℝ) * ∑ j, sliceEnergy P
          (partialRestrict (g j) (a + (Z j).comp (LinearMap.inl F2 A I)))) := by
  rw [partialRestrict_sub_sum]
  have h := sliceEnergy_sub_sum_le P (partialRestrict f a)
    (fun j => partialRestrict (fun Y => g j (Y + Z j)) a)
  simpa only [sliceEnergy_partialRestrict_translate] using h

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSFourthMomentZoomTransport
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E E' F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]

theorem ambient_character_transport (h : E ≃ₗ[F2] E')
    (S : F →ₗ[F2] E) (X : E' →ₗ[F2] F) :
    linearTraceCharacter (h.toLinearMap.comp S) X =
      linearTraceCharacter S (X.comp h.toLinearMap) := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

theorem ambient_basisInvariant_transport (h : E ≃ₗ[F2] E')
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant (fun X : E' →ₗ[F2] F =>
      f (X.comp h.toLinearMap)) := by
  intro g X
  let k : E ≃ₗ[F2] E := (h.trans g).trans h.symm
  have hc : (X.comp g.toLinearMap).comp h.toLinearMap =
      (X.comp h.toLinearMap).comp k.toLinearMap := by
    ext x
    simp [k]
  change f ((X.comp g.toLinearMap).comp h.toLinearMap) = f (X.comp h.toLinearMap)
  rw [hc]
  exact hf k (X.comp h.toLinearMap)

variable [Fintype (E →ₗ[F2] F)] [Fintype (E' →ₗ[F2] F)]

theorem ambient_coeff_transport (h : E ≃ₗ[F2] E')
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (fun X : E' →ₗ[F2] F => f (X.comp h.toLinearMap))
      (h.toLinearMap.comp S) = linearCoeff f S := by
  unfold linearCoeff
  apply Fintype.expect_equiv (ambientPrimalEquiv h)
  intro X
  change f (X.comp h.toLinearMap) * (linearTraceCharacter (h.toLinearMap.comp S) X).re =
    f (X.comp h.toLinearMap) * (linearTraceCharacter S (X.comp h.toLinearMap)).re
  rw [ambient_character_transport]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] E')]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] E')] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
theorem smallCoeff_ambient_transport (h : E ≃ₗ[F2] E') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff (h.toLinearMap.comp ι)
      (fun X : E' →ₗ[F2] F => f (X.comp h.toLinearMap)) T = smallCoeff ι f T := by
  unfold smallCoeff
  split_ifs
  · rw [LinearMap.comp_assoc, ambient_coeff_transport]
  · rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] E')] [Fintype (I →ₗ[F2] F)] in

theorem smallComponent_ambient_transport (h : E ≃ₗ[F2] E') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    smallComponent (h.toLinearMap.comp ι)
      (fun X : E' →ₗ[F2] F => f (X.comp h.toLinearMap)) = smallComponent ι f := by
  unfold smallComponent
  congr 1
  funext T
  exact smallCoeff_ambient_transport h ι f T

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSFourthMoment

noncomputable section
open scoped Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

variable {A0 A I F : Type*}
  [AddCommGroup A0] [Module F2 A0]
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

theorem coprod_comp_pointShuffle (e : (A0 × F2) ≃ₗ[F2] A)
    (a : A →ₗ[F2] F) (X : I →ₗ[F2] F) :
    (a.coprod X).comp (pointShuffle e).toLinearMap =
      pointAppend (((a.comp e.toLinearMap).comp (LinearMap.inl F2 A0 F2)).coprod X)
        (a (e (0, 1))) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨⟨u, v⟩, c⟩
  change a (e (u, c)) + X v =
    (a (e (u, 0)) + X v) + c • a (e (0, 1))
  have hp : (u, c) = (u, (0 : F2)) + c • ((0 : A0), (1 : F2)) := by
    simp
  have ha : a (e (u, c)) = a (e (u, 0)) + c • a (e (0, 1)) := by
    rw [hp]
    simp only [map_add, map_smul]
  rw [ha]
  abel

theorem partialRestrict_pointRestrict_pointShuffleTransport
    (e : (A0 × F2) ≃ₗ[F2] A)
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict
      (pointRestrict (pointShuffleTransport e f) (a (e (0, 1))))
      ((a.comp e.toLinearMap).comp (LinearMap.inl F2 A0 F2)) =
        partialRestrict f a := by
  funext X
  change f ((pointAppend
    (((a.comp e.toLinearMap).comp (LinearMap.inl F2 A0 F2)).coprod X)
    (a (e (0, 1)))).comp (pointShuffle e).symm.toLinearMap) = f (a.coprod X)
  rw [← coprod_comp_pointShuffle]
  congr 1
  apply LinearMap.ext
  intro p
  change (a.coprod X) ((pointShuffle e) ((pointShuffle e).symm p)) = (a.coprod X) p
  rw [LinearEquiv.apply_symm_apply]

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant

variable {E F I J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
theorem fixedFrequencyEnergy_nonneg (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    0 ≤ fixedFrequencyEnergy ι f π A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in

theorem fixedFrequencyEnergy_eq (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A =
      ∑ T ∈ Finset.univ.filter (fun T : F →ₗ[F2] I => π.comp T = A ∧ Function.Surjective T),
        linearCoeff f (ι.comp T) ^ 2 := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T <;> by_cases hA : π.comp T = A <;>
    simp [smallCoeff, hT, hA]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in

theorem fixedFrequencyEnergy_eq_zero_of_not_surjective
    (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (A : F →ₗ[F2] J) (hA : ¬ Function.Surjective A) :
    fixedFrequencyEnergy ι f π A = 0 := by
  rw [fixedFrequencyEnergy_eq]
  apply Finset.sum_eq_zero
  intro T hT
  have ht := (Finset.mem_filter.mp hT).2
  exact (hA (ht.1 ▸ hπ.comp ht.2)).elim

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in

theorem fixedFrequencyEnergy_zero (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    fixedFrequencyEnergy ι f (0 : I →ₗ[F2] J) 0 =
      𝔼 X, smallComponent ι f X ^ 2 := by
  rw [smallComponent, synthesis_energy]
  simp [fixedFrequencyEnergy]

end
end DFVSGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHyperplaneExtensions
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.FullGame.edge_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.SourceInstance.edge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E F B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 B]

theorem character_codomain_composition (J : B →ₗ[F2] F)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] B) :
    linearTraceCharacter S (J.comp X) = linearTraceCharacter (S.comp J) X := by
  simp only [linearTraceCharacter_apply]
  congr 1
  rw [linearTracePair_swap (J.comp X) S, linearTracePair_swap X (S.comp J)]
  simp only [linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)] in

theorem coefficient_codomain_pullback (J : B →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) (T : B →ₗ[F2] E) :
    linearCoeff (fun X => f (J.comp X)) T =
      ∑ S : F →ₗ[F2] E, if S.comp J = T then linearCoeff f S else 0 := by
  have hexpand : (fun X => f (J.comp X)) =
      ∑ S : F →ₗ[F2] E, linearCoeff f S •
        (fun X => (linearTraceCharacter (S.comp J) X).re) := by
    funext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simpa only [character_codomain_composition] using
      (linear_fourier_inversion f (J.comp X)).symm
  rw [hexpand, linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.comp J = T
  · simp [hS]
  · simp [hS, Ne.symm hS]

omit [Fintype (B →ₗ[F2] E)] in
theorem coefficient_codomain_pullback_fiber (J : B →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) (T : B →ₗ[F2] E) :
    linearCoeff (fun X => f (J.comp X)) T =
      ∑ S : {S : F →ₗ[F2] E // S.comp J = T}, linearCoeff f S.val := by
  rw [coefficient_codomain_pullback]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun S _ => S.val) ?_ ?_ ?_ ?_
  · intro S _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.property⟩
  · intro S _ R _ h
    exact Subtype.ext h
  · intro S hS
    exact ⟨⟨S, (Finset.mem_filter.mp hS).2⟩, Finset.mem_univ _, rfl⟩
  · intro S _
    rfl

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E B : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup B] [Module F2 B]

theorem ker_hyperplaneExtend_of_notMem (z : B →ₗ[F2] E) {v : E}
    (hv : v ∉ z.range) :
    (hyperplaneExtend z v).ker = z.ker.prod (⊥ : Submodule F2 F2) := by
  have hv0 : v ≠ 0 := fun h => hv (h.symm ▸ z.range.zero_mem)
  have hd : Disjoint z.range (LinearMap.toSpanSingleton F2 E v).range := by
    rw [LinearMap.range_toSpanSingleton]
    exact Submodule.disjoint_span_singleton_of_notMem hv
  rw [hyperplaneExtend, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
    LinearMap.ker_toSpanSingleton F2 hv0]

variable [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] (B × F2))]

theorem coefficient_hyperplaneExtend_eq (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {u v : E} (hu : u ∉ z.range) (hv : v ∉ z.range) :
    linearCoeff f (hyperplaneExtend z u) = linearCoeff f (hyperplaneExtend z v) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  rw [ker_hyperplaneExtend_of_notMem z hu, ker_hyperplaneExtend_of_notMem z hv]

variable [Fintype E]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] B × F2)] in

theorem card_hyperplaneExtension_outside (z : B →ₗ[F2] E) :
    (Finset.univ.filter (fun v : E => v ∉ z.range)).card =
      Fintype.card E - Fintype.card z.range := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_subtype_compl (fun v : E => v ∈ z.range)

theorem sum_hyperplaneExtend_outside (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    (∑ u with u ∉ z.range, linearCoeff f (hyperplaneExtend z u)) =
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) *
        linearCoeff f (hyperplaneExtend z v) := by
  calc
    _ = ∑ _u ∈ Finset.univ.filter (fun u : E => u ∉ z.range),
        linearCoeff f (hyperplaneExtend z v) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact coefficient_hyperplaneExtend_eq f hf z (Finset.mem_filter.mp hu).2 hv
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_hyperplaneExtension_outside]

theorem sum_hyperplaneExtend (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    (∑ u : E, linearCoeff f (hyperplaneExtend z u)) =
      (∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u)) +
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) *
        linearCoeff f (hyperplaneExtend z v) := by
  rw [← sum_hyperplaneExtend_outside f hf z hv]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun u => u ∈ z.range) (fun u => linearCoeff f (hyperplaneExtend z u))).symm

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSAnalytic

variable {E B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [Fintype E]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)] in
theorem coefficient_hyperplane_restriction
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (z : B →ₗ[F2] E) :
    linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z =
      ∑ u : E, linearCoeff f (hyperplaneExtend z u) := by
  rw [coefficient_codomain_pullback_fiber]
  exact ((hyperplaneExtensionEquiv z).sum_comp
    (fun S => linearCoeff f S.val)).symm

omit [Fintype (B →ₗ[F2] E)] in
theorem coefficient_zoomOut_mul
    (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) *
        linearCoeff f (hyperplaneExtend z v) =
      linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z -
        ∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u) := by
  rw [coefficient_hyperplane_restriction, sum_hyperplaneExtend f hf z hv]
  ring

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant
open DFVSGames.Inverse.KMSFourthMoment

theorem sub_sum_sq_le_card_mul {C : Type*} [Fintype C]
    (x : ℝ) (a : C → ℝ) :
    (x - ∑ c, a c) ^ 2 ≤
      ((Fintype.card C : ℝ) + 1) * (x ^ 2 + ∑ c, a c ^ 2) := by
  let b : Option C → ℝ := fun c => c.elim x (fun c => -a c)
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Option C))
    (fun _ => (1 : ℝ)) b
  simpa [b, Fintype.sum_option, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

variable {E B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [Fintype E]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)] in
theorem coefficient_zoomOut_sq_bound
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (z : B →ₗ[F2] E) {v : E} (hv : v ∉ z.range) :
    (((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) ^ 2) *
        linearCoeff f (hyperplaneExtend z v) ^ 2 ≤
      ((Fintype.card z.range : ℝ) + 1) *
        (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z ^ 2 +
          ∑ u : z.range, linearCoeff f (hyperplaneExtend z u.val) ^ 2) := by
  have hrec := coefficient_zoomOut_mul f hf z hv
  rw [Finset.sum_subtype (p := fun u : E => u ∈ z.range) _ (by simp)
    (fun u : E => linearCoeff f (hyperplaneExtend z u))] at hrec
  calc
    _ = ((((Fintype.card E - Fintype.card z.range : ℕ) : ℝ)) *
        linearCoeff f (hyperplaneExtend z v)) ^ 2 := (mul_pow _ _ _).symm
    _ = (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z -
        ∑ u : z.range, linearCoeff f (hyperplaneExtend z u.val)) ^ 2 := by rw [hrec]
    _ ≤ _ := sub_sum_sq_le_card_mul _ _

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)

variable {E B J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J]

theorem lastVector_not_mem_left_range (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) : ι (0, 1) ∉ (leftEmbedding ι).range := by
  rintro ⟨j, hj⟩
  have h : (j, (0 : F2)) = (0, 1) := hι hj
  exact zero_ne_one (congrArg Prod.snd h)

theorem card_lifted_range [Fintype E] [Fintype J]
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    Fintype.card ((leftEmbedding ι).comp z).range = Fintype.card J :=
  (Fintype.card_congr (liftedRangeEquiv ι hι z hz)).symm

theorem sum_lifted_range [Fintype E] [Fintype J]
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) (a : E → ℝ) :
    (∑ u : ((leftEmbedding ι).comp z).range, a u.val) =
      ∑ j : J, a (leftEmbedding ι j) :=
  ((liftedRangeEquiv ι hι z hz).sum_comp (fun u => a u.val)).symm

theorem hyperplaneExtend_left_comp (ι : (J × F2) →ₗ[F2] E)
    (z : B →ₗ[F2] J) (w : J) :
    hyperplaneExtend ((leftEmbedding ι).comp z) (leftEmbedding ι w) =
      (leftEmbedding ι).comp (hyperplaneExtend z w) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  simp [hyperplaneExtend, map_add, map_smul]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]

theorem hyperplaneExtend_old_injective (w : J) :
    Function.Injective (fun z : B →ₗ[F2] J => hyperplaneExtend z w) := by
  intro z z' h
  have hc := congrArg
    (fun T : (B × F2) →ₗ[F2] J => T.comp (LinearMap.inl F2 B F2)) h
  simpa only [hyperplaneExtend_comp_inl] using hc

theorem hyperplaneExtend_surjective {z : B →ₗ[F2] J}
    (hz : Function.Surjective z) (w : J) :
    Function.Surjective (hyperplaneExtend z w) := by
  intro y
  obtain ⟨b, hb⟩ := hz y
  refine ⟨(b, 0), ?_⟩
  simpa using hb

theorem comp_hyperplaneExtend (π : J →ₗ[F2] K) (z : B →ₗ[F2] J) (w : J) :
    π.comp (hyperplaneExtend z w) = hyperplaneExtend (π.comp z) (π w) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  simp [LinearMap.comp_apply]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (B →ₗ[F2] J)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype ((B × F2) →ₗ[F2] E)] [Fintype (J →ₗ[F2] (B × F2))] in
theorem dependent_extension_energy_le
    (ι : J →ₗ[F2] E) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (π : J →ₗ[F2] K) (A0 : B →ₗ[F2] K) (w : J) :
    (∑ z : B →ₗ[F2] J with π.comp z = A0 ∧ Function.Surjective z,
      linearCoeff f (ι.comp (hyperplaneExtend z w)) ^ 2) ≤
        fixedFrequencyEnergy ι f π (hyperplaneExtend A0 (π w)) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A0 ∧ Function.Surjective z
  let Q : Finset ((B × F2) →ₗ[F2] J) :=
    Finset.univ.filter fun T =>
      π.comp T = hyperplaneExtend A0 (π w) ∧ Function.Surjective T
  have hsub : P.image (fun z => hyperplaneExtend z w) ⊆ Q := by
    intro T hT
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hT
    have hp := (Finset.mem_filter.mp hz).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, hyperplaneExtend_surjective hp.2 w⟩
    rw [comp_hyperplaneExtend, hp.1]
  rw [fixedFrequencyEnergy_eq]
  change (∑ z ∈ P, linearCoeff f (ι.comp (hyperplaneExtend z w)) ^ 2) ≤
    ∑ T ∈ Q, linearCoeff f (ι.comp T) ^ 2
  calc
    _ = ∑ T ∈ P.image (fun z => hyperplaneExtend z w),
        linearCoeff f (ι.comp T) ^ 2 := by
      rw [Finset.sum_image]
      exact fun z _ z' _ h => hyperplaneExtend_old_injective w h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun T _ _ => sq_nonneg _)

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]

omit [FiniteDimensional F2 J] [Fintype (J →ₗ[F2] B × F2)] [Fintype (B × F2 →ₗ[F2] J)] [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)] in

omit [Fintype (B →ₗ[F2] E)] in
theorem coefficient_lifted_zoomOut_sq_bound
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    (((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
        linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2 ≤
      ((Fintype.card J : ℝ) + 1) *
        (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X))
            ((leftEmbedding ι).comp z) ^ 2 +
          ∑ w : J, linearCoeff f ((leftEmbedding ι).comp (hyperplaneExtend z w)) ^ 2) := by
  have hv : ι (0, 1) ∉ ((leftEmbedding ι).comp z).range := by
    rw [range_left_comp_of_surjective ι z hz]
    exact lastVector_not_mem_left_range ι hι
  have h := coefficient_zoomOut_sq_bound f hf ((leftEmbedding ι).comp z) hv
  rw [card_lifted_range ι hι z hz,
    sum_lifted_range ι hι z hz
      (fun u => linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) u) ^ 2)] at h
  simpa only [hyperplaneExtend_left_comp] using h

omit [Fintype (J →ₗ[F2] B)] [FiniteDimensional F2 J]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype (B →ₗ[F2] E)] in
theorem fixedCharacter_step_sum
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    (((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
        (∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] J =>
            π.comp z = A ∧ Function.Surjective z),
          linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2) ≤
      ((Fintype.card J : ℝ) + 1) *
        (fixedFrequencyEnergy (leftEmbedding ι)
          (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A +
        ∑ w : J, fixedFrequencyEnergy (leftEmbedding ι) f π (hyperplaneExtend A (π w))) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A ∧ Function.Surjective z
  change _ * (∑ z ∈ P, _) ≤ _
  calc
    _ ≤ ∑ z ∈ P, ((Fintype.card J : ℝ) + 1) *
        (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X))
            ((leftEmbedding ι).comp z) ^ 2 +
          ∑ w : J, linearCoeff f ((leftEmbedding ι).comp (hyperplaneExtend z w)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      exact coefficient_lifted_zoomOut_sq_bound ι hι f hf z
        (Finset.mem_filter.mp hz).2.2
    _ = ((Fintype.card J : ℝ) + 1) *
        ((∑ z ∈ P, linearCoeff
          (fun X => f ((LinearMap.inl F2 B F2).comp X)) ((leftEmbedding ι).comp z) ^ 2) +
        ∑ w : J, ∑ z ∈ P,
          linearCoeff f ((leftEmbedding ι).comp (hyperplaneExtend z w)) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · rw [fixedFrequencyEnergy_eq]
      · apply Finset.sum_le_sum
        intro w _
        exact dependent_extension_energy_le (leftEmbedding ι) f π A w

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {B J K E : Type*}
  [AddCommGroup B] [Module F2 B] [AddCommGroup J] [Module F2 J]
  [AddCommGroup K] [Module F2 K] [AddCommGroup E] [Module F2 E]

theorem ker_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    (blockFrequency z w).ker = z.ker.prod (⊥ : Submodule F2 F2) := by
  ext ⟨b, c⟩
  change ((z b + c • w, c) = (0, 0)) ↔ (z b = 0 ∧ c = 0)
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨by simpa using h, rfl⟩
  · rintro ⟨h, rfl⟩
    simpa using h

variable [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] (B × F2))]

theorem coefficient_blockFrequency_eq (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] J) (u v : J) :
    linearCoeff f (ι.comp (blockFrequency z u)) =
      linearCoeff f (ι.comp (blockFrequency z v)) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hι),
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hι),
    ker_blockFrequency, ker_blockFrequency]

variable [FiniteDimensional F2 B] [FiniteDimensional F2 J] [Fintype J]
  [Fintype ((B × F2) →ₗ[F2] E)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [FiniteDimensional F2 B] [FiniteDimensional F2 J] [Fintype (B × F2 →ₗ[F2] E)] [Fintype (J × F2 →ₗ[F2] B × F2)] in

theorem fixedFrequencyEnergy_block (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    fixedFrequencyEnergy ι f (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
      (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) =
      (Fintype.card π.ker : ℝ) * ∑ z : CompatibleOldFrequency π A,
        linearCoeff f (ι.comp (blockFrequency z.val 0)) ^ 2 := by
  let e := compatibleBlockFrequencyEquiv π A
  calc
    _ = ∑ T : CompatibleBlockFrequency π A, linearCoeff f (ι.comp T.val) ^ 2 := by
      unfold fixedFrequencyEnergy
      rw [← Finset.sum_subtype (Finset.univ.filter (fun T : (B × F2) →ₗ[F2] (J × F2) =>
          Function.Surjective T ∧
            (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
              A.prodMap (LinearMap.id : F2 →ₗ[F2] F2))) (by simp)
          (fun T => linearCoeff f (ι.comp T) ^ 2),
        Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      by_cases hs : Function.Surjective T <;>
        by_cases hp : (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
            A.prodMap (LinearMap.id : F2 →ₗ[F2] F2) <;> simp [smallCoeff, hs, hp]
    _ = ∑ p : CompatibleOldFrequency π A × π.ker,
        linearCoeff f (ι.comp (blockFrequency p.1.val p.2.val)) ^ 2 := by
      apply Fintype.sum_equiv e
      intro T
      exact congrArg (fun R : (B × F2) →ₗ[F2] (J × F2) =>
        linearCoeff f (ι.comp R) ^ 2) (congrArg Subtype.val (e.symm_apply_apply T)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [coefficient_blockFrequency_eq ι hι f hf _ _ 0]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]

theorem comp_blockFrequency_zero (ι : (J × F2) →ₗ[F2] E) (z : B →ₗ[F2] J) :
    ι.comp (blockFrequency z 0) =
      hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1)) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  change ι (z b + c • 0, c) = ι (z b, 0) + c • ι (0, 1)
  simp only [smul_zero, add_zero]
  rw [← map_smul, ← map_add]
  congr 1
  simp

variable [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [Fintype ((J × F2) →ₗ[F2] (B × F2))] [Fintype (J →ₗ[F2] B)]
  [FiniteDimensional F2 J] [Fintype (J →ₗ[F2] (B × F2))] [Fintype (B →ₗ[F2] E)] in
theorem fixedFrequencyEnergy_product_step
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    (((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
        fixedFrequencyEnergy ι f (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
          (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) ≤
      (Fintype.card π.ker : ℝ) * (((Fintype.card J : ℝ) + 1) *
        (fixedFrequencyEnergy (leftEmbedding ι)
          (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A +
        ∑ w : J, fixedFrequencyEnergy (leftEmbedding ι) f π (hyperplaneExtend A (π w)))) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A ∧ Function.Surjective z
  have hsum : (∑ z : CompatibleOldFrequency π A,
      linearCoeff f (ι.comp (blockFrequency z.val 0)) ^ 2) =
      ∑ z ∈ P,
        linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2 := by
    rw [← Finset.sum_subtype (p := fun z : B →ₗ[F2] J =>
      Function.Surjective z ∧ π.comp z = A) P (by intro z; simp [P, and_comm])
      (fun z => linearCoeff f (ι.comp (blockFrequency z 0)) ^ 2)]
    apply Finset.sum_congr rfl
    intro z _
    rw [comp_blockFrequency_zero]
  rw [fixedFrequencyEnergy_block ι hι f hf π A, hsum]
  calc
    _ = (Fintype.card π.ker : ℝ) *
        ((((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
          ∑ z ∈ P, linearCoeff f
            (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (fixedCharacter_step_sum ι hι f hf π A)
      (Nat.cast_nonneg _)

end
end DFVSGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticSmallTransport
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters
  (linearTraceCharacter linearTraceCharacter_apply linearTracePair)

variable {E F I I' J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup I'] [Module F2 I']
  [AddCommGroup J] [Module F2 J]

theorem surjective_smallFrequencyEquiv_iff (e : I ≃ₗ[F2] I') (T : F →ₗ[F2] I) :
    Function.Surjective (e.toLinearMap.comp T) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (e y)
    exact ⟨x, e.injective hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h (e.symm y)
    refine ⟨x, ?_⟩
    change e (T x) = y
    rw [hx, e.apply_symm_apply]

theorem smallFrequency_transport_comp (e : I ≃ₗ[F2] I') (π : I →ₗ[F2] J)
    (T : F →ₗ[F2] I) :
    (π.comp e.symm.toLinearMap).comp (e.toLinearMap.comp T) = π.comp T := by
  ext x
  simp

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 I']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I' →ₗ[F2] F)] [Fintype (F →ₗ[F2] I')]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [FiniteDimensional F2 I'] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] [Fintype (I' →ₗ[F2] F)] [Fintype (F →ₗ[F2] I')] in

theorem smallCoeff_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff (ι.comp e.symm.toLinearMap) f (e.toLinearMap.comp T) =
      smallCoeff ι f T := by
  unfold smallCoeff
  rw [surjective_smallFrequencyEquiv_iff, smallFrequency_transport_comp]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [FiniteDimensional F2 I'] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (I' →ₗ[F2] F)] in

theorem fixedFrequencyEnergy_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy (ι.comp e.symm.toLinearMap) f
      (π.comp e.symm.toLinearMap) A = fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (smallFrequencyEquiv (F := F) e)
  intro T
  simp only [smallFrequencyEquiv_apply, smallFrequency_transport_comp,
    smallCoeff_transport]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 I']
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (I' →ₗ[F2] F)]

theorem smallComponent_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (X : I' →ₗ[F2] F) :
    smallComponent (ι.comp e.symm.toLinearMap) f X =
      smallComponent ι f (X.comp e.toLinearMap) := by
  unfold smallComponent synthesis
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv (smallFrequencyEquiv (F := F) e)
  intro T
  simp only [smallFrequencyEquiv_apply, smallCoeff_transport,
    linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

theorem smallComponent_precomp_equiv (g : I ≃ₗ[F2] I') (ι : I' →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (X : I →ₗ[F2] F) :
    smallComponent (ι.comp g.toLinearMap) f X =
      smallComponent ι f (X.comp g.symm.toLinearMap) := by
  simpa only [LinearEquiv.symm_symm] using smallComponent_transport g.symm ι f X

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSPointComplement

noncomputable section
open DFVSGames.Integration.BinaryLinear (F2)
open KMSAnalytic (pointLift)

variable {E I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

theorem exists_aligned_point_equiv (ι : (I × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) :
    ∃ U : Submodule F2 E, ∃ e : (U × F2) ≃ₗ[F2] E,
      ∃ κ : I →ₗ[F2] U, Function.Injective κ ∧
        e.toLinearMap.comp (pointLift κ) = ι := by
  let z : I →ₗ[F2] E := ι.comp (LinearMap.inl F2 I F2)
  let v : E := ι (0, 1)
  have hv : v ∉ z.range := by
    rintro ⟨x, hx⟩
    have hx' : ι (x, 0) = ι (0, 1) := hx
    have h01 : (0 : F2) = 1 := congrArg Prod.snd (hι hx')
    exact zero_ne_one h01
  have hv0 : v ≠ 0 := by
    intro h
    apply hv
    rw [h]
    exact z.range.zero_mem
  obtain ⟨U, hU, hc⟩ := (Submodule.disjoint_span_singleton_of_notMem hv).exists_isCompl
  let κ : I →ₗ[F2] U := z.codRestrict U (fun x => hU ⟨x, rfl⟩)
  let e : (U × F2) ≃ₗ[F2] E := pointEquivOfIsCompl U v hv0 hc
  refine ⟨U, e, κ, ?_, ?_⟩
  · intro x y h
    have hxy : ι (x, 0) = ι (y, 0) := congrArg Subtype.val h
    exact congrArg Prod.fst (hι hxy)
  · apply LinearMap.ext
    rintro ⟨x, c⟩
    change ι (x, 0) + c • ι (0, 1) = ι (x, c)
    rw [← map_smul, ← map_add]
    congr 1
    ext <;> simp

theorem exists_point_equiv [FiniteDimensional F2 E]
    (h : 0 < Module.finrank F2 E) :
    ∃ U : Submodule F2 E, ∃ _e : (U × F2) ≃ₗ[F2] E,
      Module.finrank F2 U + 1 = Module.finrank F2 E := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  obtain ⟨U, hc⟩ := (Submodule.span F2 {v}).exists_isCompl
  let e := pointEquivOfIsCompl U v hv hc.symm
  refine ⟨U, e, ?_⟩
  simpa only [Module.finrank_prod, Module.finrank_self] using e.finrank_eq

end
end DFVSGames.Inverse.KMSPointComplement

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

variable {E E0 F A A0 I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E0] [Module F2 E0]
  [AddCommGroup F] [Module F2 F] [AddCommGroup A] [Module F2 A]
  [AddCommGroup A0] [Module F2 A0] [AddCommGroup I] [Module F2 I]

theorem exists_mixed_aligned_point (ι : (A × I) →ₗ[F2] E)
    (hι : Function.Injective ι) (eA : (A0 × F2) ≃ₗ[F2] A) :
    ∃ U : Submodule F2 E, ∃ eE : (U × F2) ≃ₗ[F2] E,
      ∃ κ : (A0 × I) →ₗ[F2] U, Function.Injective κ ∧
        eE.toLinearMap.comp (pointLift κ) =
          ι.comp (pointShuffle eA).toLinearMap :=
  KMSPointComplement.exists_aligned_point_equiv
    (ι.comp (pointShuffle eA).toLinearMap) (hι.comp (pointShuffle eA).injective)

variable [FiniteDimensional F2 E] [FiniteDimensional F2 E0]
  [FiniteDimensional F2 F] [FiniteDimensional F2 A]
  [FiniteDimensional F2 A0] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((E0 × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (E0 × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (((A0 × I) × F2) →ₗ[F2] F)]
  [Fintype (F →ₗ[F2] ((A0 × I) × F2))]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E0] [FiniteDimensional F2 F]
  [FiniteDimensional F2 A] [FiniteDimensional F2 A0] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] (E0 × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (((A0 × I) × F2) →ₗ[F2] F)]

theorem smallComponent_mixed_aligned (ι : (A × I) →ₗ[F2] E)
    (eA : (A0 × F2) ≃ₗ[F2] A) (eE : (E0 × F2) ≃ₗ[F2] E)
    (κ : (A0 × I) →ₗ[F2] E0)
    (halign : eE.toLinearMap.comp (pointLift κ) =
      ι.comp (pointShuffle eA).toLinearMap) (f : (E →ₗ[F2] F) → ℝ) :
    smallComponent (pointLift κ)
      (fun X : (E0 × F2) →ₗ[F2] F => f (X.comp eE.symm.toLinearMap)) =
      pointShuffleTransport eA (smallComponent ι f) := by
  have he : eE.symm.toLinearMap.comp (ι.comp (pointShuffle eA).toLinearMap) =
      pointLift κ := by
    rw [← halign]
    apply LinearMap.ext
    intro x
    simp
  have htransport := smallComponent_ambient_transport
    (E := E) (E' := E0 × F2) (F := F) (I := (A0 × I) × F2)
    eE.symm (ι.comp (pointShuffle eA).toLinearMap) f
  rw [he] at htransport
  rw [htransport]
  funext X
  exact smallComponent_precomp_equiv (I := (A0 × I) × F2) (I' := A × I)
    (E := E) (F := F) (pointShuffle eA) ι f X

theorem partialRestrict_smallComponent_mixed_aligned (ι : (A × I) →ₗ[F2] E)
    (eA : (A0 × F2) ≃ₗ[F2] A) (eE : (E0 × F2) ≃ₗ[F2] E)
    (κ : (A0 × I) →ₗ[F2] E0)
    (halign : eE.toLinearMap.comp (pointLift κ) =
      ι.comp (pointShuffle eA).toLinearMap)
    (f : (E →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict (smallComponent ι f) a =
      partialRestrict (pointRestrict (smallComponent (pointLift κ)
        (fun X : (E0 × F2) →ₗ[F2] F => f (X.comp eE.symm.toLinearMap)))
        (a (eA (0, 1))))
        ((a.comp eA.toLinearMap).comp (LinearMap.inl F2 A0 F2)) := by
  rw [smallComponent_mixed_aligned ι eA eE κ halign f,
    partialRestrict_pointRestrict_pointShuffleTransport]

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSAnalytic

variable {A I : Type*} [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [Subsingleton A]

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 A] [FiniteDimensional F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (F →ₗ[F2] E)] [Fintype ((A × I) →ₗ[F2] F)]
  [Fintype (I →ₗ[F2] F)] in
theorem partialRestrict_smallComponent_zeroFixed (ι : (A × I) →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict (smallComponent ι f) a =
      smallComponent (ι.comp (LinearMap.inr F2 A I)) f := by
  funext X
  have hmap : a.coprod X =
      X.comp (zeroFixedEquiv (A := A) (I := I)).symm.toLinearMap := by
    apply LinearMap.ext
    rintro ⟨u, x⟩
    have hu : u = 0 := Subsingleton.elim _ _
    simp [hu]
  change smallComponent ι f (a.coprod X) = _
  rw [hmap]
  exact (smallComponent_precomp_equiv (zeroFixedEquiv (A := A) (I := I)) ι f X).symm

omit [FiniteDimensional F2 A] [FiniteDimensional F2 E]
  [Fintype (F →ₗ[F2] E)] [Fintype ((A × I) →ₗ[F2] F)] in
theorem mixedEnergy_zeroFixed (ι : (A × I) →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J) :
    sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) =
      fixedFrequencyEnergy (ι.comp (LinearMap.inr F2 A I)) f π ν := by
  rw [partialRestrict_smallComponent_zeroFixed]
  simp only [sliceEnergy, fixedFrequencyEnergy, coeff_smallComponent]

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

variable {E F A I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup A] [Module F2 A] [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 A] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((E × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (E × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (((A × I) × F2) →ₗ[F2] F)]
  [Fintype (F →ₗ[F2] ((A × I) × F2))]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (F →ₗ[F2] F2)] [Fintype ((A × I) →ₗ[F2] F2)]

omit [FiniteDimensional F2 A] [Fintype ((A × I) →ₗ[F2] F)]
  [Fintype (((A × I) × F2) →ₗ[F2] F)]

theorem mixed_point_sliceEnergy_le (ι : (A × I) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (a : A →ₗ[F2] F) (b : F)
    (P : (F →ₗ[F2] I) → Prop) :
    sliceEnergy P (partialRestrict
      (pointRestrict (smallComponent (pointLift ι) f) b) a) ≤
      2 * (sliceEnergy P (partialRestrict (smallComponent ι (pointRestrict f b)) a) +
        (Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) *
          ∑ φ : (A × I) →ₗ[F2] F2, sliceEnergy P
            (partialRestrict (smallComponent (pointPad ι) f)
              (a + (φ.smulRight b).comp (LinearMap.inl F2 A I)))) := by
  have he : pointRestrict (smallComponent (pointLift ι) f) b =
      fun X => smallComponent ι (pointRestrict f b) X -
        ∑ φ : (A × I) →ₗ[F2] F2,
          smallComponent (pointPad ι) f (X + φ.smulRight b) := by
    funext X
    exact point_restriction_recursion ι hι f hf X b
  rw [he]
  exact sliceEnergy_partialRestrict_sub_translates_le P
    (smallComponent ι (pointRestrict f b))
    (fun _ : (A × I) →ₗ[F2] F2 => smallComponent (pointPad ι) f)
    a (fun φ => φ.smulRight b)

theorem mixed_point_sliceEnergy_le_of_bounds (ι : (A × I) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (a : A →ₗ[F2] F) (b : F)
    (P : (F →ₗ[F2] I) → Prop) (H₀ H₁ : ℝ)
    (h₀ : sliceEnergy P
      (partialRestrict (smallComponent ι (pointRestrict f b)) a) ≤ H₀)
    (h₁ : ∀ a' : A →ₗ[F2] F,
      sliceEnergy P (partialRestrict (smallComponent (pointPad ι) f) a') ≤ H₁) :
    sliceEnergy P (partialRestrict
      (pointRestrict (smallComponent (pointLift ι) f) b) a) ≤
      2 * (H₀ + (Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) ^ 2 * H₁) := by
  apply (mixed_point_sliceEnergy_le ι hι f hf a b P).trans
  have hs : (∑ φ : (A × I) →ₗ[F2] F2, sliceEnergy P
      (partialRestrict (smallComponent (pointPad ι) f)
        (a + (φ.smulRight b).comp (LinearMap.inl F2 A I)))) ≤
      (Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) * H₁ := by
    calc
      _ ≤ ∑ _φ : (A × I) →ₗ[F2] F2, H₁ :=
        Finset.sum_le_sum (fun φ _ => h₁ _)
      _ = _ := by simp
  calc
    _ ≤ 2 * (H₀ + (Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) *
        ((Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) * H₁)) := by
      gcongr
    _ = _ := by ring

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment

theorem mixedStepFactor_nonneg (R : ℕ) : 0 ≤ mixedStepFactor R := by
  unfold mixedStepFactor
  positivity

theorem one_le_mixedStepFactor (R : ℕ) : 1 ≤ mixedStepFactor R := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem mixed_step_factor_bound (R t n : ℕ) (ht : t ≤ 2 * R) (hn : n ≤ R) :
    2 * ((2 : ℝ) ^ t + ((2 : ℝ) ^ n) ^ 2) ≤ mixedStepFactor R := by
  have ht' : (2 : ℝ) ^ t ≤ 2 ^ (2 * R) :=
    pow_le_pow_right₀ (by norm_num) ht
  have hn' : ((2 : ℝ) ^ n) ^ 2 ≤ 2 ^ (2 * R) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have he : mixedStepFactor R = 4 * (2 : ℝ) ^ (2 * R) := by
    unfold mixedStepFactor
    rw [pow_add]
    ring
  rw [he]
  linarith

theorem mixed_weighted_step {M A B q w n C : ℝ}
    (hq : 0 ≤ q) (hw : 0 ≤ w)
    (hrec : M ≤ 2 * (A + n ^ 2 * B))
    (hA : w * A ≤ C) (hB : (q * w) * B ≤ C) :
    (q * w) * M ≤ 2 * (q + n ^ 2) * C := by
  calc
    (q * w) * M ≤ (q * w) * (2 * (A + n ^ 2 * B)) :=
      mul_le_mul_of_nonneg_left hrec (mul_nonneg hq hw)
    _ = 2 * (q * (w * A) + n ^ 2 * ((q * w) * B)) := by ring
    _ ≤ 2 * (q * C + n ^ 2 * C) := by
      gcongr
    _ = 2 * (q + n ^ 2) * C := by ring

theorem mixed_weighted_step_pow (R s ell t n : ℕ) (H ε M A B : ℝ)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (ht : t ≤ 2 * R) (hn : n ≤ R)
    (hrec : M ≤ 2 * (A + ((2 : ℝ) ^ n) ^ 2 * B))
    (hA : (2 : ℝ) ^ (t * ell) * A ≤ H * mixedStepFactor R ^ s * ε)
    (hB : (2 : ℝ) ^ (t * (ell + 1)) * B ≤ H * mixedStepFactor R ^ s * ε) :
    (2 : ℝ) ^ (t * (ell + 1)) * M ≤ H * mixedStepFactor R ^ (s + 1) * ε := by
  have he : (2 : ℝ) ^ (t * (ell + 1)) = 2 ^ t * 2 ^ (t * ell) := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
    ring
  have hc : 0 ≤ H * mixedStepFactor R ^ s * ε :=
    mul_nonneg (mul_nonneg hH (pow_nonneg (mixedStepFactor_nonneg R) _)) hε
  have h := mixed_weighted_step (q := (2 : ℝ) ^ t)
    (w := (2 : ℝ) ^ (t * ell)) (n := (2 : ℝ) ^ n)
    (by positivity) (by positivity) hrec hA (by simpa only [he] using hB)
  rw [← he] at h
  calc
    _ ≤ 2 * ((2 : ℝ) ^ t + ((2 : ℝ) ^ n) ^ 2) *
        (H * mixedStepFactor R ^ s * ε) := h
    _ ≤ mixedStepFactor R * (H * mixedStepFactor R ^ s * ε) :=
      mul_le_mul_of_nonneg_right (mixed_step_factor_bound R t n ht hn) hc
    _ = _ := by rw [pow_succ]; ring

end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSBasisInvariant

universe u v
variable {E : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]

theorem HomogeneousRestrictionBound.codomain_pullback
    [FiniteDimensional F2 B] (r s : ℕ) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound (r + s) ε f)
    (J : B →ₗ[F2] F) (hJ : Function.Injective J)
    (hcodim : Module.finrank F2 F ≤ Module.finrank F2 B + s) :
    HomogeneousRestrictionBound r ε (fun X : E →ₗ[F2] B => f (J.comp X)) := by
  intro C _ _ _ _ K hK hdim
  have hdim' : Module.finrank F2 F ≤ Module.finrank F2 C + (r + s) := by omega
  simpa only [LinearMap.comp_assoc] using hf C (J.comp K) (hJ.comp hK) hdim'

theorem HomogeneousRestrictionBound.energy_le
    [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)]
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound r ε f) : (𝔼 X, f X ^ 2) ≤ ε := by
  simpa using hf F (LinearMap.id : F →ₗ[F2] F) Function.injective_id
    (Nat.le_add_right (Module.finrank F2 F) r)

theorem basisInvariant_codomain_pullback (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (J : B →ₗ[F2] F) :
    IsBasisInvariant (fun X : E →ₗ[F2] B => f (J.comp X)) := by
  intro g X
  simpa only [LinearMap.comp_assoc] using hf g (J.comp X)

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open DFVSGames.Fourier.MatrixCharacters

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

theorem pointAppend_comp_basis (X : E →ₗ[F2] F) (a : F) (g : E ≃ₗ[F2] E) :
    pointAppend (X.comp g.toLinearMap) a =
      (pointAppend X a).comp (g.prodCongr (LinearEquiv.refl F2 F2)).toLinearMap := by
  apply LinearMap.ext
  intro x
  rfl

theorem pointRestrict_invariant (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (a : F) :
    KMSBasisInvariant.IsBasisInvariant (pointRestrict f a) := by
  intro g X
  change f (pointAppend (X.comp g.toLinearMap) a) = f (pointAppend X a)
  rw [pointAppend_comp_basis]
  exact hf (g.prodCongr (LinearEquiv.refl F2 F2)) (pointAppend X a)

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic

universe u v
variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

theorem AffineDensityBound.mono {r s : ℕ} (hrs : r ≤ s) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : AffineDensityBound s ε f) :
    AffineDensityBound r ε f := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  exact hf D C L hL J hJ T (by omega)

theorem AffineDensityBound.homogeneous [FiniteDimensional F2 E]
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound r ε f) : HomogeneousRestrictionBound r ε f := by
  intro C _ _ _ _ J hJ hdim
  have h := hf E C (LinearMap.id : E →ₗ[F2] E) Function.surjective_id
    J hJ 0 (by omega)
  simpa using h

theorem AffineDensityBound.pointRestrict [FiniteDimensional F2 E]
    (r : ℕ) (ε : ℝ) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound (r + 1) ε f) (a : F) :
    AffineDensityBound r ε (pointRestrict f a) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  let L' : (E × F2) →ₗ[F2] D := L.comp (LinearMap.fst F2 E F2)
  have hL' : Function.Surjective L' := by
    intro y
    obtain ⟨x, hx⟩ := hL y
    exact ⟨(x, 0), hx⟩
  have hdim' : Module.finrank F2 (E × F2) + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + (r + 1) := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  have he (X : D →ₗ[F2] C) :
      pointAppend (T + J.comp (X.comp L)) a =
        pointAppend T a + J.comp (X.comp L') := by
    apply LinearMap.ext
    intro p
    rcases p with ⟨x, c⟩
    simp only [pointAppend_apply, LinearMap.add_apply, LinearMap.comp_apply,
      L', LinearMap.fst_apply]
    abel
  have h := hf D C L' hL' J hJ (pointAppend T a) hdim'
  simpa only [KMSAnalytic.pointRestrict, he] using h

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)

universe u v
variable {E E' : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup B] [Module F2 B]

theorem AffineDensityBound.domain_equiv
    [FiniteDimensional F2 E] [FiniteDimensional F2 E']
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound r ε f) (e : E ≃ₗ[F2] E') :
    AffineDensityBound r ε (fun X : E' →ₗ[F2] F => f (X.comp e.toLinearMap)) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  have hdim' : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + r := by
    rw [e.finrank_eq]
    exact hdim
  have h := hf D C (L.comp e.toLinearMap) (hL.comp e.surjective) J hJ
    (T.comp e.toLinearMap) hdim'
  simpa only [LinearMap.add_comp, LinearMap.comp_assoc] using h

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

universe u v

variable {F : Type v} {I J : Type u}
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 F] [FiniteDimensional F2 I] [FiniteDimensional F2 J]
  [Fintype F] [Fintype I] [Fintype J]

attribute [local instance] OAI.DFVSGames.Inverse.KMSFourthMoment.mapFintype
omit [FiniteDimensional F2 J] [Fintype J] in

theorem mixed_bound_of_character_bound (R : ℕ) (H ε : ℝ)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J)
    (hπ : Function.Surjective π)
    (hbase : ∀ (E : Type u) [AddCommGroup E] [Module F2 E]
      [FiniteDimensional F2 E] [Fintype E],
      ∀ (ι : I →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), KMSBasisInvariant.IsBasisInvariant f →
      AffineDensityBound (Module.finrank F2 I) ε f →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π ν ≤ H * ε) :
    ∀ (n : ℕ) (E : Type u) [AddCommGroup E] [Module F2 E]
      [FiniteDimensional F2 E] [Fintype E]
      (A : Type u) [AddCommGroup A] [Module F2 A]
      [FiniteDimensional F2 A] [Fintype A],
      Module.finrank F2 A = n →
      ∀ (ι : (A × I) →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), KMSBasisInvariant.IsBasisInvariant f →
      AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f →
      ∀ (a : A →ₗ[F2] F), Module.finrank F2 A + Module.finrank F2 I ≤ R →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
          H * mixedStepFactor R ^ n * ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ _ A _ _ _ _ hAn ι hι f hf hd a hr
    by_cases hn : n = 0
    · have hz : Module.finrank F2 A = 0 := hAn.trans hn
      let : Subsingleton A := Module.finrank_zero_iff.mp hz
      have hi : Function.Injective (ι.comp (LinearMap.inr F2 A I)) := by
        intro x y hxy
        exact congrArg Prod.snd (hι hxy)
      have hd0 : AffineDensityBound (Module.finrank F2 I) ε f := by simpa [hz] using hd
      rw [mixedEnergy_zeroFixed]
      simpa only [hn, pow_zero, mul_one] using
        hbase E (ι.comp (LinearMap.inr F2 A I)) hi f hf hd0
    · have hp : 0 < Module.finrank F2 A := by omega
      obtain ⟨A0, eA, hAdrop⟩ := KMSPointComplement.exists_point_equiv hp
      change Module.finrank F2 A0 + 1 = Module.finrank F2 A at hAdrop
      obtain ⟨E0, eE, κ, hκ, halign⟩ := exists_mixed_aligned_point ι hι eA
      let f' : ((E0 × F2) →ₗ[F2] F) → ℝ :=
        fun X => f (X.comp eE.symm.toLinearMap)
      let a0 : A0 →ₗ[F2] F := (a.comp eA.toLinearMap).comp (LinearMap.inl F2 A0 F2)
      let b : F := a (eA (0, 1))
      let r0 := Module.finrank F2 A0 + Module.finrank F2 I
      let t := Module.finrank F2 I + Module.finrank F2 J
      have hs : Module.finrank F2 A0 < n := by omega
      have hr0 : r0 ≤ R := by dsimp [r0]; omega
      have hf' : KMSBasisInvariant.IsBasisInvariant f' :=
        ambient_basisInvariant_transport eE.symm f hf
      have hd' : AffineDensityBound (r0 + 1) ε f' := by
        have h := AffineDensityBound.domain_equiv _ ε f hd eE.symm
        have he : Module.finrank F2 A + Module.finrank F2 I = r0 + 1 := by
          dsimp [r0]; omega
        simpa only [he] using h
      have hdp : AffineDensityBound r0 ε (pointRestrict f' b) :=
        AffineDensityBound.pointRestrict r0 ε f' hd' b
      have hdo : AffineDensityBound r0 ε f' :=
        AffineDensityBound.mono (Nat.le_succ r0) ε f' hd'
      have hdimE : Module.finrank F2 E = Module.finrank F2 E0 + 1 := by
        simpa only [Module.finrank_prod, Module.finrank_self] using eE.finrank_eq.symm
      have ht : t ≤ 2 * R := by
        have hji : Module.finrank F2 J ≤ Module.finrank F2 I :=
          LinearMap.finrank_le_finrank_of_surjective hπ
        dsimp [t]
        omega
      have hcard : (Fintype.card ((A0 × I) →ₗ[F2] F2) : ℝ) = (2 : ℝ) ^ r0 := by
        rw [Module.card_eq_pow_finrank (K := F2)]
        simp [Module.finrank_prod, r0, F2, ZMod.card]
      let C := H * mixedStepFactor R ^ Module.finrank F2 A0 * ε
      let W0 : ℝ := 2 ^ (t * Module.finrank F2 E0)
      let W1 : ℝ := 2 ^ (t * (Module.finrank F2 E0 + 1))
      have hW0 : 0 < W0 := by dsimp [W0]; positivity
      have hW1 : 0 < W1 := by dsimp [W1]; positivity
      have hfirst : sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent κ (pointRestrict f' b)) a0) ≤ C / W0 := by
        apply (le_div_iff₀ hW0).mpr
        have h := ih (Module.finrank F2 A0) hs E0 A0 rfl κ hκ
          (pointRestrict f' b) (pointRestrict_invariant f' hf' b) hdp a0 hr0
        simpa only [C, W0, t, mul_comm] using h
      have hsecond (a' : A0 →ₗ[F2] F) : sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent (pointPad κ) f') a') ≤ C / W1 := by
        apply (le_div_iff₀ hW1).mpr
        have h := ih (Module.finrank F2 A0) hs (E0 × F2) A0 rfl
          (pointPad κ) (pointPad_injective κ hκ) f' hf' hdo a' hr0
        simpa only [C, W1, t, Module.finrank_prod, Module.finrank_self, mul_comm] using h
      have hrec := mixed_point_sliceEnergy_le_of_bounds κ hκ f' hf' a0 b
        (fun T => π.comp T = ν) (C / W0) (C / W1) hfirst hsecond
      rw [hcard] at hrec
      have hweighted := mixed_weighted_step_pow R (Module.finrank F2 A0)
        (Module.finrank F2 E0) t r0 H ε _ (C / W0) (C / W1)
        hH hε ht hr0 hrec
        (by change W0 * (C / W0) ≤ C; rw [mul_div_cancel₀ _ (ne_of_gt hW0)])
        (by change W1 * (C / W1) ≤ C; rw [mul_div_cancel₀ _ (ne_of_gt hW1)])
      rw [partialRestrict_smallComponent_mixed_aligned ι eA eE κ halign f a]
      simpa only [hdimE, ← hAn, ← hAdrop, f', a0, b, t] using hweighted

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSKernelFiberDefs
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical

section FiniteFibers

variable {A B J : Type*} [Fintype A] [Fintype B] [Fintype J]

theorem sum_comp_eq_fiber_card (p : A → J) (b : J → ℝ) :
    (∑ x, b (p x)) =
      ∑ j, ((Finset.univ.filter fun x => p x = j).card : ℝ) * b j := by
  calc
    (∑ x, b (p x)) = ∑ x, ∑ j, if p x = j then b j else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = ∑ j, ∑ x, if p x = j then b j else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp

theorem sum_sq_eq_fiber_card (p : A → J) (a : A → ℝ) (b : J → ℝ)
    (hab : ∀ x, a x = b (p x)) :
    (∑ x, a x ^ 2) =
      ∑ j, ((Finset.univ.filter fun x => p x = j).card : ℝ) * b j ^ 2 := by
  simpa only [hab] using sum_comp_eq_fiber_card p (fun j => b j ^ 2)

theorem sum_sq_eq_uniform_fiber_card (p : A → J) (a : A → ℝ) (b : J → ℝ)
    (hab : ∀ x, a x = b (p x)) (n : ℕ)
    (hn : ∀ j, (Finset.univ.filter fun x => p x = j).card = n) :
    (∑ x, a x ^ 2) = (n : ℝ) * ∑ j, b j ^ 2 := by
  rw [sum_sq_eq_fiber_card p a b hab, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hn]

theorem fiber_constant_energy_cross_mul (p : A → J) (q : B → J)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (a : A → ℝ) (b : B → ℝ)
    (hab : ∀ x y, p x = q y → a x = b y)
    (nA nB : ℕ)
    (hA : ∀ j, (Finset.univ.filter fun x => p x = j).card = nA)
    (hB : ∀ j, (Finset.univ.filter fun y => q y = j).card = nB) :
    (nB : ℝ) * (∑ x, a x ^ 2) = (nA : ℝ) * ∑ y, b y ^ 2 := by
  let c : J → ℝ := fun j => b (Classical.choose (hq j))
  have ha : ∀ x, a x = c (p x) := by
    intro x
    exact hab x (Classical.choose (hq (p x)))
      (Classical.choose_spec (hq (p x))).symm
  have hb : ∀ y, b y = c (q y) := by
    intro y
    obtain ⟨x, hx⟩ := hp (q y)
    exact (hab x y hx).symm.trans (by simpa only [hx] using ha x)
  rw [sum_sq_eq_uniform_fiber_card p a c ha nA hA,
    sum_sq_eq_uniform_fiber_card q b c hb nB hB]
  ring

end FiniteFibers

open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalyticKernelCount

noncomputable section

variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

theorem range_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E) :
    (J.comp K.mkQ).range = J.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨K.mkQ x, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    exact ⟨x, rfl⟩

theorem quotientInjection_comp_finrank (K : Submodule R F)
    (J : (F ⧸ K) →ₗ[R] E) (hJ : Function.Injective J) :
    Module.finrank R (J.comp K.mkQ).range = Module.finrank R (F ⧸ K) := by
  rw [range_comp_mkQ]
  exact LinearMap.finrank_range_of_inj hJ

end
end DFVSGames.Inverse.KMSAnalyticKernelCount

namespace DFVSGames.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount

noncomputable section

variable {F E I : Type*}
  [AddCommGroup F] [Module F2 F] [FiniteDimensional F2 F]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I]

theorem rankKernel_surjective
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    Function.Surjective (rankKernel (F := F) (E := E) (I := I)) := by
  classical
  obtain ⟨j, hj⟩ :=
    (finrank_le_iff_exists_linearMap (R := F2) (M := I) (M' := E)).mp hdim
  intro K
  let J : (F ⧸ K.val) →ₗ[F2] E := j.comp (quotientEquiv K).toLinearMap
  have hJ : Function.Injective J := hj.comp (quotientEquiv K).injective
  refine ⟨⟨J.comp K.val.mkQ, ?_⟩, ?_⟩
  · exact (quotientInjection_comp_finrank K.val J hJ).trans K.property
  · apply Subtype.ext
    exact ker_comp_mkQ K.val J hJ

theorem fullKernel_surjective :
    Function.Surjective (fullKernel (F := F) (I := I)) := by
  classical
  intro K
  let T : F →ₗ[F2] I := (quotientEquiv K).toLinearMap.comp K.val.mkQ
  have hT : Function.Surjective T :=
    (quotientEquiv K).surjective.comp K.val.mkQ_surjective
  refine ⟨⟨T, hT⟩, ?_⟩
  apply Subtype.ext
  exact ker_comp_mkQ K.val (quotientEquiv K).toLinearMap (quotientEquiv K).injective

end
end DFVSGames.Inverse.KMSKernelFiberCard

namespace DFVSGames.Inverse.KMSInjectionCount

open scoped BigOperators

noncomputable section

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E]

theorem beta_eq_product [FiniteDimensional F2 I] [Finite E]
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    beta I E = ∏ j : Fin (Module.finrank F2 I),
      (2 ^ Module.finrank F2 E - 2 ^ j.val) := by
  unfold beta
  rw [Nat.card_congr (injectiveEquivIndependent I E (Module.finBasis F2 I))]
  simpa only [F2, ZMod.card] using
    (card_linearIndependent (K := F2) (V := E) hdim)

end
end DFVSGames.Inverse.KMSInjectionCount

namespace DFVSGames.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount KMSInjectionCount
open scoped Classical

noncomputable section

variable {F E I J : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]

variable [FiniteDimensional F2 F] [FiniteDimensional F2 I]

theorem natCard_fixedKernel_eq_beta (K : KernelClass F I) :
    Nat.card {S : F →ₗ[F2] E // S.ker = K.val} = beta I E :=
  Nat.card_congr (fixedKernelEquivInjection K)

theorem rankKernel_fiber_card [Fintype (F →ₗ[F2] E)]
    (K : KernelClass F I) :
    (Finset.univ.filter (fun S : RankFrequency F E I => rankKernel S = K)).card =
      beta I E := by
  calc
    _ = Fintype.card {S : RankFrequency F E I // rankKernel S = K} :=
      (Fintype.card_subtype _).symm
    _ = Nat.card {S : RankFrequency F E I // rankKernel S = K} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {S : F →ₗ[F2] E // S.ker = K.val} :=
      Nat.card_congr (rankFiberEquivFixedKernel K)
    _ = beta I E := natCard_fixedKernel_eq_beta K

theorem fullKernel_fiber_card [Fintype (F →ₗ[F2] I)]
    (K : KernelClass F I) :
    (Finset.univ.filter (fun T : FullFrequency F I => fullKernel T = K)).card =
      beta I I := by
  calc
    _ = Fintype.card {T : FullFrequency F I // fullKernel T = K} :=
      (Fintype.card_subtype _).symm
    _ = Nat.card {T : FullFrequency F I // fullKernel T = K} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {T : F →ₗ[F2] I // T.ker = K.val} :=
      Nat.card_congr (fullFiberEquivFixedKernel K)
    _ = beta I I := natCard_fixedKernel_eq_beta K

end
end DFVSGames.Inverse.KMSKernelFiberCard

namespace DFVSGames.Inverse.KMSInjectionCount

open scoped BigOperators

theorem binary_factor_lower {d n j : ℕ} (hj : j < d) (hdn : d ≤ n) :
    2 ^ (n - d) ≤ 2 ^ n - 2 ^ j := by
  have hn : 0 < n := by omega
  have hjn : j ≤ n - 1 := by omega
  have hdn' : n - d ≤ n - 1 := by omega
  calc
    2 ^ (n - d) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) hdn'
    _ = 2 ^ n - 2 ^ (n - 1) := (Nat.two_pow_sub_two_pow_pred hn).symm
    _ ≤ 2 ^ n - 2 ^ j :=
      Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide) hjn) _

noncomputable section

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 I] [Finite E]

theorem beta_le_pow (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    beta I E ≤ 2 ^ (Module.finrank F2 E * Module.finrank F2 I) := by
  rw [beta_eq_product I E hdim]
  calc
    _ ≤ ∏ _j : Fin (Module.finrank F2 I), 2 ^ Module.finrank F2 E := by
      apply Finset.prod_le_prod'
      intro j _
      exact Nat.sub_le _ _
    _ = _ := by simp [← pow_mul]

theorem beta_ge_pow (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    2 ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) ≤
      beta I E := by
  rw [beta_eq_product I E hdim]
  calc
    _ = ∏ _j : Fin (Module.finrank F2 I),
        2 ^ (Module.finrank F2 E - Module.finrank F2 I) := by
      simp [← pow_mul, Nat.mul_comm]
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro j _
      exact binary_factor_lower j.isLt hdim

theorem beta_self_le [Finite I] :
    beta I I ≤ 2 ^ (Module.finrank F2 I * Module.finrank F2 I) :=
  beta_le_pow I I le_rfl

end
end DFVSGames.Inverse.KMSInjectionCount

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant
open DFVSGames.Inverse.KMSKernelOrbitsFourier
open DFVSGames.Inverse.KMSKernelFiberCard (KernelClass FullFrequency RankFrequency
  fullKernel rankKernel fullKernel_surjective rankKernel_surjective
  fullKernel_fiber_card rankKernel_fiber_card)
open DFVSGames.Inverse.KMSInjectionCount (beta)

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Finite E] [Finite F] [Finite I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (KernelClass F I)]

omit [Finite E] [Finite F] [Finite I] in

theorem smallComponent_energy_cross_mul (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) :
    (beta I E : ℝ) * (𝔼 X, smallComponent ι f X ^ 2) =
      (beta I I : ℝ) * (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have h := fiber_constant_energy_cross_mul
    (fullKernel (F := F) (I := I)) (rankKernel (F := F) (E := E) (I := I))
    fullKernel_surjective (rankKernel_surjective hdim)
    (fun T : FullFrequency F I => linearCoeff f (ι.comp T.val))
    (fun S : RankFrequency F E I => linearCoeff f S.val)
    (fun T S hTS => coefficient_eq_of_ker_eq f hf _ _
      ((ker_comp_of_injective ι hι T.val).trans
        (congrArg Subtype.val hTS)))
    (beta I I) (beta I E)
    (fun K => by
      have hc := fullKernel_fiber_card (F := F) (I := I) K
      convert hc using 1 ; congr 1 ; ext T ; simp)
    (fun K => by
      have hc := rankKernel_fiber_card (F := F) (E := E) (I := I) K
      convert hc using 1 ; congr 1 ; ext T ; simp)
  rw [smallComponent_energy, rankComponent_energy]
  rw [Finset.sum_subtype (p := fun T : F →ₗ[F2] I => Function.Surjective T) _ (by simp) (fun T : F →ₗ[F2] I => linearCoeff f (ι.comp T) ^ 2),
    Finset.sum_subtype (p := fun S : F →ₗ[F2] E => Module.finrank F2 S.range = Module.finrank F2 I) _ (by simp) (fun S : F →ₗ[F2] E => linearCoeff f S ^ 2)]
  exact h

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSInjectionCount

noncomputable section

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 I] [Finite E]

theorem pow_dim_mul_le_pow_sq_mul_beta
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * (beta I E : ℝ) := by
  have hexp : Module.finrank F2 I * Module.finrank F2 I +
      Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I) =
      Module.finrank F2 I * Module.finrank F2 E := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hdim]
  have hnat : 2 ^ (Module.finrank F2 I * Module.finrank F2 E) ≤
      2 ^ (Module.finrank F2 I * Module.finrank F2 I) * beta I E := by
    calc
      _ = 2 ^ (Module.finrank F2 I * Module.finrank F2 I) *
          2 ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) := by
        rw [← pow_add, hexp]
      _ ≤ _ := Nat.mul_le_mul_left _ (beta_ge_pow I E hdim)
  exact_mod_cast hnat

theorem pow_mul_le_of_beta_cross_mul [Finite I]
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hcross : (beta I E : ℝ) * x = (beta I I : ℝ) * y) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) * x ≤
      (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) * y := by
  have hq : 0 ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) :=
    pow_nonneg (by norm_num) _
  have hself : (beta I I : ℝ) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) := by
    exact_mod_cast beta_self_le I
  calc
    _ ≤ ((2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * (beta I E : ℝ)) * x :=
      mul_le_mul_of_nonneg_right (pow_dim_mul_le_pow_sq_mul_beta I E hdim) hx
    _ = (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * ((beta I I : ℝ) * y) := by
      rw [mul_assoc, hcross]
    _ ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) *
        ((2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hself hy) hq
    _ = _ := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

end
end DFVSGames.Inverse.KMSInjectionCount

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSBasisInvariant

universe u v w x
variable {E : Type u} {F : Type v} {I : Type w} {J : Type x}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 J]
  [Finite E] [Finite F] [Finite I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (KMSKernelFiberCard.KernelClass F I)]

omit [Finite F] in
theorem smallComponent_energy_base_bound (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (ε : ℝ)
    (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) *
        (𝔼 X, smallComponent ι f X ^ 2) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have henergy : (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) ≤ ε :=
    (component_energy_le (fun T : F →ₗ[F2] E =>
      Module.finrank F2 T.range = Module.finrank F2 I) f).trans (hg.energy_le _ _ _)
  have hε : 0 ≤ ε := (Finset.expect_nonneg (fun _ _ => sq_nonneg _)).trans henergy
  have hbase := KMSInjectionCount.pow_mul_le_of_beta_cross_mul I E hdim
    (Finset.expect_nonneg (fun _ _ => sq_nonneg (smallComponent ι f _)))
    (Finset.expect_nonneg (fun _ _ => sq_nonneg (rankComponent (Module.finrank F2 I) f _)))
    (smallComponent_energy_cross_mul ι hι f hf)
  calc
    _ ≤ (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := hbase
    _ ≤ (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) * ε :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by nlinarith)) hε

omit [Finite F] in
theorem fixedFrequencyEnergy_zero_dim_bound (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (ε : ℝ)
    (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) (hJ : Module.finrank F2 J = 0) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π A ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  let : Subsingleton J := Module.finrank_zero_iff.mp hJ
  have hπ : π = 0 := Subsingleton.elim _ _
  have hA : A = 0 := Subsingleton.elim _ _
  rw [hπ, hA, fixedFrequencyEnergy_zero, hJ, Nat.add_zero]
  exact smallComponent_energy_base_bound ι hι f hf ε hg

end
end DFVSGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticCodomainTransport
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

theorem fixedCharacter_constant_step (n m ell : ℕ) (hnell : n < ell) :
    (2 : ℝ) ^ n * ((2 : ℝ) ^ n + 1) ^ 2 * (2 : ℝ) ^ (4 * n * n) /
        ((((2 : ℝ) ^ ell - (2 : ℝ) ^ n) ^ 2) * (2 : ℝ) ^ ((n + m) * ell)) ≤
      (2 : ℝ) ^ (4 * (n + 1) * (n + 1)) /
        (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) := by
  let A : ℝ := (2 : ℝ) ^ ell
  let B : ℝ := (2 : ℝ) ^ n
  let C : ℝ := (2 : ℝ) ^ (4 * n * n)
  let C' : ℝ := (2 : ℝ) ^ (4 * (n + 1) * (n + 1))
  let P : ℝ := (2 : ℝ) ^ ((n + m) * ell)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hAB : 2 * B ≤ A := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnell
    simpa only [pow_succ, mul_comm] using h
  have hdiff : 0 < A - B := by linarith
  have hplus : (B + 1) ^ 2 ≤ 4 * B ^ 2 := by
    have hs := mul_self_le_mul_self (show 0 ≤ B + 1 by positivity)
      (show B + 1 ≤ 2 * B by linarith)
    nlinarith only [hs]
  have hsquare : A ^ 2 ≤ 4 * (A - B) ^ 2 := by
    have hs := mul_self_le_mul_self (show 0 ≤ A / 2 by positivity)
      (show A / 2 ≤ A - B by linarith)
    nlinarith only [hs]
  have hcoeff : B * (B + 1) ^ 2 * C ≤ 4 * B ^ 3 * C := by
    calc
      _ ≤ B * (4 * B ^ 2) * C := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hplus hB.le) hC.le
      _ = _ := by ring
  have hconst : 16 * B ^ 3 * C ≤ C' := by
    calc
      _ = (2 : ℝ) ^ (4 + 3 * n + 4 * n * n) := by
        dsimp [B, C]
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hmain : B * (B + 1) ^ 2 * C * A ^ 2 ≤ C' * (A - B) ^ 2 := by
    calc
      _ ≤ (4 * B ^ 3 * C) * A ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg A)
      _ ≤ (4 * B ^ 3 * C) * (4 * (A - B) ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = (16 * B ^ 3 * C) * (A - B) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hconst (sq_nonneg _)
  have hpower : (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) = A ^ 2 * P := by
    dsimp [A, P]
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  change B * (B + 1) ^ 2 * C / ((A - B) ^ 2 * P) ≤
    C' / (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [hpower]
  calc
    _ = (B * (B + 1) ^ 2 * C * A ^ 2) * P := by ring
    _ ≤ (C' * (A - B) ^ 2) * P := mul_le_mul_of_nonneg_right hmain hP.le
    _ = _ := by ring

end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [FiniteDimensional F2 J] [FiniteDimensional F2 K]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [Fintype (B →ₗ[F2] E)] [Fintype (J →ₗ[F2] (B × F2))]
  [Fintype (J →ₗ[F2] B)] [Fintype ((J × F2) →ₗ[F2] (B × F2))] in
theorem fixedFrequencyEnergy_product_bound
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) (ε : ℝ) (hε : 0 ≤ ε)
    (hfirst : (2 : ℝ) ^ ((Module.finrank F2 J + Module.finrank F2 K) *
        Module.finrank F2 E) * fixedFrequencyEnergy (leftEmbedding ι)
        (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 J * Module.finrank F2 J) * ε)
    (hlower : ∀ w : J, (2 : ℝ) ^ ((Module.finrank F2 J + Module.finrank F2 K) *
        Module.finrank F2 E) * fixedFrequencyEnergy (leftEmbedding ι) f π
        (hyperplaneExtend A (π w)) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 J * Module.finrank F2 J) * ε) :
    (2 : ℝ) ^ ((Module.finrank F2 (J × F2) + Module.finrank F2 (K × F2)) *
        Module.finrank F2 E) * fixedFrequencyEnergy ι f
        (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
        (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 (J × F2) * Module.finrank F2 (J × F2)) * ε := by
  let n := Module.finrank F2 J
  let m := Module.finrank F2 K
  let ell := Module.finrank F2 E
  let P : ℝ := 2 ^ ((n + m) * ell)
  let C : ℝ := 2 ^ (4 * n * n)
  let N : ℝ := 2 ^ n
  let D : ℝ := 2 ^ ell - 2 ^ n
  let a := fixedFrequencyEnergy (leftEmbedding ι)
    (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A
  let b := fun w : J => fixedFrequencyEnergy (leftEmbedding ι) f π
    (hyperplaneExtend A (π w))
  let t := fixedFrequencyEnergy ι f
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
    (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
  have hnell : n < ell := by
    have hdim := LinearMap.finrank_le_finrank_of_injective hι
    rw [Module.finrank_prod, Module.finrank_self] at hdim
    exact hdim
  have hcardE : Fintype.card E = 2 ^ ell := by
    rw [Module.card_eq_pow_finrank (K := F2)]
    simp only [F2, ZMod.card, ell]
  have hcardJ : Fintype.card J = 2 ^ n := by
    rw [Module.card_eq_pow_finrank (K := F2)]
    simp only [F2, ZMod.card, n]
  have hcardle : Fintype.card J ≤ Fintype.card E := by
    rw [hcardJ, hcardE]
    exact Nat.pow_le_pow_right (by decide) hnell.le
  have hcardJR : (Fintype.card J : ℝ) = N := by
    rw [hcardJ]
    simp only [Nat.cast_pow, Nat.cast_ofNat, N]
  have hdiff : ((Fintype.card E - Fintype.card J : ℕ) : ℝ) = D := by
    rw [Nat.cast_sub hcardle, hcardE, hcardJ]
    simp only [Nat.cast_pow, Nat.cast_ofNat, D]
  have hker : (Fintype.card π.ker : ℝ) ≤ N := by
    rw [← hcardJR]
    exact_mod_cast Fintype.card_le_of_injective (fun x : π.ker => (x : J))
      Subtype.val_injective
  have hP : 0 < P := by dsimp [P]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hD : 0 < D := by
    dsimp [D]
    exact sub_pos.mpr (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hnell)
  have ha : 0 ≤ a := fixedFrequencyEnergy_nonneg _ _ _ _
  have hb : 0 ≤ ∑ w : J, b w :=
    Finset.sum_nonneg (fun w _ => fixedFrequencyEnergy_nonneg _ _ _ _)
  have hsum : P * (a + ∑ w : J, b w) ≤ (N + 1) * (C * ε) := by
    calc
      _ = P * a + ∑ w : J, P * b w := by rw [mul_add, Finset.mul_sum]
      _ ≤ C * ε + ∑ _w : J, C * ε :=
        add_le_add hfirst (Finset.sum_le_sum (fun w _ => hlower w))
      _ = (N + 1) * (C * ε) := by simp only [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hcardJR]; ring
  have hrec : D ^ 2 * t ≤ (Fintype.card π.ker : ℝ) * ((N + 1) * (a + ∑ w : J, b w)) := by
    simpa only [hdiff, hcardJR] using fixedFrequencyEnergy_product_step ι hι f hf π A
  have hweighted : (D ^ 2 * P) * t ≤ N * (N + 1) ^ 2 * C * ε := by
    calc
      _ = P * (D ^ 2 * t) := by ring
      _ ≤ P * ((Fintype.card π.ker : ℝ) * ((N + 1) * (a + ∑ w : J, b w))) :=
        mul_le_mul_of_nonneg_left hrec hP.le
      _ ≤ P * (N * ((N + 1) * (a + ∑ w : J, b w))) := by
        apply mul_le_mul_of_nonneg_left _ hP.le
        exact mul_le_mul_of_nonneg_right hker (mul_nonneg (by positivity) (add_nonneg ha hb))
      _ = (N * (N + 1)) * (P * (a + ∑ w : J, b w)) := by ring
      _ ≤ (N * (N + 1)) * ((N + 1) * (C * ε)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have ht : t ≤ (N * (N + 1) ^ 2 * C / (D ^ 2 * P)) * ε := by
    calc
      t ≤ (N * (N + 1) ^ 2 * C * ε) / (D ^ 2 * P) :=
        (le_div_iff₀ (show 0 < D ^ 2 * P by positivity)).mpr
          (by simpa only [mul_comm] using hweighted)
      _ = _ := by ring
  have hc := fixedCharacter_constant_step n m ell hnell
  change N * (N + 1) ^ 2 * C / (D ^ 2 * P) ≤
    (2 : ℝ) ^ (4 * (n + 1) * (n + 1)) /
      (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) at hc
  have hfinal := ht.trans (mul_le_mul_of_nonneg_right hc hε)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
  change (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) * t ≤
    (2 : ℝ) ^ (4 * (n + 1) * (n + 1)) * ε
  have hresult := (le_div_iff₀
    (show 0 < (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) by positivity)).mp
      (show t ≤ ((2 : ℝ) ^ (4 * (n + 1) * (n + 1)) * ε) /
        (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) from hfinal.trans_eq (by ring))
  simpa only [mul_comm] using hresult

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E F F' I J : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]

theorem surjective_comp_codomainEquiv_iff (e : F ≃ₗ[F2] F') (T : F' →ₗ[F2] I) :
    Function.Surjective (T.comp e.toLinearMap) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨e x, hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    refine ⟨e.symm x, ?_⟩
    simpa using hx

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E)]

omit [Fintype (F' →ₗ[F2] E)] in
theorem linearCoeff_codomainTransport (e : F ≃ₗ[F2] F')
    (f : (E →ₗ[F2] F) → ℝ) (S' : F' →ₗ[F2] E) :
    linearCoeff (codomainTransport e f) S' = linearCoeff f (S'.comp e.toLinearMap) := by
  unfold codomainTransport
  rw [KMSFourthMoment.coefficient_codomain_pullback]
  have hc : (S'.comp e.toLinearMap).comp e.symm.toLinearMap = S' := by ext x; simp
  rw [Finset.sum_eq_single (S'.comp e.toLinearMap)]
  · rw [ite_eq_left hc]
  · intro S _ hS
    apply ite_eq_right
    intro h
    apply hS
    apply LinearMap.ext
    intro x
    simpa using congrArg (fun R : F' →ₗ[F2] E => R (e x)) h
  · intro h
    exact (h (Finset.mem_univ _)).elim

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype (E →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E)] in

theorem basisInvariant_codomainTransport (e : F ≃ₗ[F2] F')
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant (codomainTransport e f) := by
  intro g X
  change f (e.symm.toLinearMap.comp (X.comp g.toLinearMap)) =
    f (e.symm.toLinearMap.comp X)
  rw [← LinearMap.comp_assoc]
  exact hf g (e.symm.toLinearMap.comp X)

variable [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [FiniteDimensional F2 I] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)] in
omit [Fintype (F' →ₗ[F2] E)] in
theorem smallCoeff_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F' →ₗ[F2] I) :
    smallCoeff ι (codomainTransport e f) T =
      smallCoeff ι f (T.comp e.toLinearMap) := by
  unfold smallCoeff
  rw [surjective_comp_codomainEquiv_iff]
  split_ifs
  · rw [linearCoeff_codomainTransport, LinearMap.comp_assoc]
  · rfl

omit [FiniteDimensional F2 I] [Fintype (I →ₗ[F2] F)] [Fintype (I →ₗ[F2] F')]
  [Fintype (F' →ₗ[F2] E)] in
theorem fixedFrequencyEnergy_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι (codomainTransport e f) π (A.comp e.symm.toLinearMap) =
      fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (codomainFrequencyEquiv (I := I) e)
  intro T
  have hp : π.comp (T.comp e.symm.toLinearMap) = A.comp e.symm.toLinearMap ↔
      π.comp T = A := by
    rw [← LinearMap.comp_assoc]
    exact (codomainFrequencyEquiv (I := J) e).injective.eq_iff
  simp only [codomainFrequencyEquiv_apply, smallCoeff_codomainTransport,
    codomainFrequency_cancel, hp]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)

universe u v w x y
variable {E : Type u} {F F' : Type v} {I : Type w} {J : Type x} {J' : Type y}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J] [AddCommGroup J'] [Module F2 J']

theorem HomogeneousRestrictionBound.mono {r s : ℕ} (hrs : r ≤ s) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : HomogeneousRestrictionBound s ε f) :
    HomogeneousRestrictionBound r ε f := by
  intro C _ _ _ _ L hL hd
  exact hf C L hL (by omega)

theorem HomogeneousRestrictionBound.codomain_equiv
    [FiniteDimensional F2 F] [FiniteDimensional F2 F']
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound r ε f) (e : F ≃ₗ[F2] F') :
    HomogeneousRestrictionBound r ε (codomainTransport e f) := by
  intro C _ _ _ _ L hL hd
  have hd' : Module.finrank F2 F ≤ Module.finrank F2 C + r := by
    rw [e.finrank_eq]
    exact hd
  simpa only [codomainTransport, LinearMap.comp_assoc] using
    hf C (e.symm.toLinearMap.comp L) (e.symm.injective.comp hL) hd'

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
theorem fixedFrequencyEnergy_postcomp_injective (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J)
    (e : J →ₗ[F2] J') (he : Function.Injective e) :
    fixedFrequencyEnergy ι f (e.comp π) (e.comp A) =
      fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    exact he (congrArg (fun L : F →ₗ[F2] J' => L x) h)
  · intro h
    rw [LinearMap.comp_assoc, h]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalyticFunctionalSplit

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

theorem finrank_eq_ker_add_one [FiniteDimensional K F]
    (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    Module.finrank K F = Module.finrank K a.ker + 1 := by
  have h := (splitEquiv a t ht).finrank_eq
  simpa [Module.finrank_prod] using h

end DFVSGames.Inverse.KMSAnalyticFunctionalSplit

namespace DFVSGames.Inverse.KMSAnalyticCompatibleSplitting

noncomputable section

variable {I F K : Type*}
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup K] [Module F2 K]

namespace CompatibleSplitting

variable {π : I →ₗ[F2] K} {A : F →ₗ[F2] K}

theorem leftMap_surjective (s : CompatibleSplitting π A) :
    Function.Surjective s.leftMap := by
  intro y
  obtain ⟨x, hx⟩ := s.left_surjective y.val
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change s.functional (π x) = 0
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact hx

theorem left_symm_apply (s : CompatibleSplitting π A) (x : s.J × F2) :
    π (s.leftEquiv.symm x) = s.targetEquiv.symm (s.leftMap x.1, x.2) := by
  change π ((x.1 : I) + x.2 • s.leftVector) = π x.1 + x.2 • s.targetVector
  rw [map_add, map_smul, s.leftVector_image]

theorem right_symm_apply (s : CompatibleSplitting π A) (x : s.B × F2) :
    A (s.rightEquiv.symm x) = s.targetEquiv.symm (s.rightMap x.1, x.2) := by
  change A ((x.1 : F) + x.2 • s.rightVector) = A x.1 + x.2 • s.targetVector
  rw [map_add, map_smul, s.rightVector_image]

theorem left_conjugation (s : CompatibleSplitting π A) :
    s.targetEquiv.toLinearMap.comp (π.comp s.leftEquiv.symm.toLinearMap) =
      s.leftMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2) := by
  apply LinearMap.ext
  intro x
  change s.targetEquiv (π (s.leftEquiv.symm x)) = (s.leftMap x.1, x.2)
  rw [s.left_symm_apply, s.targetEquiv.apply_symm_apply]

theorem right_conjugation (s : CompatibleSplitting π A) :
    s.targetEquiv.toLinearMap.comp (A.comp s.rightEquiv.symm.toLinearMap) =
      s.rightMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2) := by
  apply LinearMap.ext
  intro x
  change s.targetEquiv (A (s.rightEquiv.symm x)) = (s.rightMap x.1, x.2)
  rw [s.right_symm_apply, s.targetEquiv.apply_symm_apply]

theorem target_finrank [FiniteDimensional F2 K] (s : CompatibleSplitting π A) :
    Module.finrank F2 K = Module.finrank F2 s.K0 + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one s.functional s.targetVector
    s.functional_targetVector

theorem left_finrank [FiniteDimensional F2 I] (s : CompatibleSplitting π A) :
    Module.finrank F2 I = Module.finrank F2 s.J + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one (s.functional.comp π) s.leftVector
    (by change s.functional (π s.leftVector) = 1
        rw [s.leftVector_image, s.functional_targetVector])

end CompatibleSplitting

end
end DFVSGames.Inverse.KMSAnalyticCompatibleSplitting

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSBasisInvariant

universe u v w x

variable {E : Type u} [AddCommGroup E] [Module F2 E]
  [FiniteDimensional F2 E] [Fintype E]

attribute [local instance] OAI.DFVSGames.Inverse.KMSAnalytic.mapFintype
private theorem fixedFrequencyEnergy_bound_induction_inline_KMSAnalyticCharacterInduction :
    ∀ (n : ℕ) (F : Type v) [AddCommGroup F] [Module F2 F]
      [FiniteDimensional F2 F] [Fintype F]
      (I : Type w) [AddCommGroup I] [Module F2 I]
      [FiniteDimensional F2 I] [Fintype I]
      (J : Type x) [AddCommGroup J] [Module F2 J]
      [FiniteDimensional F2 J] [Fintype J],
      Module.finrank F2 J = n →
      ∀ (ι : I →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), IsBasisInvariant f →
      ∀ (ε : ℝ), HomogeneousRestrictionBound (Module.finrank F2 I) ε f →
      ∀ (π : I →ₗ[F2] J), Function.Surjective π → ∀ A : F →ₗ[F2] J,
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
          fixedFrequencyEnergy ι f π A ≤
        (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F _ _ _ _ I _ _ _ _ J _ _ _ _ hJn ι hι f hf ε hg π hπ A
    let : Finite (KMSKernelFiberCard.KernelClass F I) :=
      Finite.of_surjective (KMSKernelFiberCard.fullKernel (F := F) (I := I))
        (KMSKernelFiberCard.fullKernel_surjective (F := F) (I := I))
    let : Fintype (KMSKernelFiberCard.KernelClass F I) := Fintype.ofFinite _
    have hε : 0 ≤ ε := (Finset.expect_nonneg (fun _ _ => sq_nonneg _)).trans
      (HomogeneousRestrictionBound.energy_le _ ε f hg)
    by_cases hn : n = 0
    · exact fixedFrequencyEnergy_zero_dim_bound ι hι f hf ε hg π A (hJn.trans hn)
    by_cases hA : Function.Surjective A
    · have hp : 0 < Module.finrank F2 J := by omega
      let s := KMSAnalyticCompatibleSplitting.chooseSplit π A hπ hA hp
      let ι' : (s.J × F2) →ₗ[F2] E := ι.comp s.leftEquiv.symm.toLinearMap
      let f' : (E →ₗ[F2] (s.B × F2)) → ℝ := codomainTransport s.rightEquiv f
      have hι' : Function.Injective ι' := hι.comp s.leftEquiv.symm.injective
      have hf' : IsBasisInvariant f' := basisInvariant_codomainTransport s.rightEquiv f hf
      have hg' : HomogeneousRestrictionBound (Module.finrank F2 s.J + 1) ε f' := by
        have h := HomogeneousRestrictionBound.codomain_equiv _ ε f hg s.rightEquiv
        simpa only [s.left_finrank] using h
      have hs : Module.finrank F2 s.K0 < n := by
        have hdim : Module.finrank F2 J = Module.finrank F2 s.K0 + 1 := s.target_finrank
        omega
      have hgfirst : HomogeneousRestrictionBound (Module.finrank F2 s.J) ε
          (fun X : E →ₗ[F2] s.B => f' ((LinearMap.inl F2 s.B F2).comp X)) :=
        HomogeneousRestrictionBound.codomain_pullback _ 1 ε f' hg'
          (LinearMap.inl F2 s.B F2) (by intro x y h; exact congrArg Prod.fst h)
          (by simp only [Module.finrank_prod, Module.finrank_self]; omega)
      have hglower : HomogeneousRestrictionBound (Module.finrank F2 s.J) ε f' :=
        HomogeneousRestrictionBound.mono (Nat.le_succ _) ε f' hg'
      have hfirst := ih (Module.finrank F2 s.K0) hs s.B s.J s.K0 rfl
        (leftEmbedding ι') (leftEmbedding_injective ι' hι')
        (fun X : E →ₗ[F2] s.B => f' ((LinearMap.inl F2 s.B F2).comp X))
        (basisInvariant_codomain_pullback f' hf' (LinearMap.inl F2 s.B F2))
        ε hgfirst s.leftMap s.leftMap_surjective s.rightMap
      have hlower (w : s.J) := ih (Module.finrank F2 s.K0) hs (s.B × F2) s.J s.K0 rfl
        (leftEmbedding ι') (leftEmbedding_injective ι' hι') f' hf'
        ε hglower s.leftMap s.leftMap_surjective (hyperplaneExtend s.rightMap (s.leftMap w))
      have hrec := fixedFrequencyEnergy_product_bound ι' hι' f' hf'
        s.leftMap s.rightMap ε hε hfirst hlower
      have htransport : fixedFrequencyEnergy ι' f'
          (s.leftMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
          (s.rightMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) =
          fixedFrequencyEnergy ι f π A := by
        rw [← s.left_conjugation, ← s.right_conjugation,
          fixedFrequencyEnergy_postcomp_injective _ _ _ _ s.targetEquiv.toLinearMap
            s.targetEquiv.injective]
        change fixedFrequencyEnergy (ι.comp s.leftEquiv.symm.toLinearMap)
          (codomainTransport s.rightEquiv f) (π.comp s.leftEquiv.symm.toLinearMap)
          (A.comp s.rightEquiv.symm.toLinearMap) = _
        rw [fixedFrequencyEnergy_codomainTransport, fixedFrequencyEnergy_transport]
      rw [htransport, ← s.leftEquiv.finrank_eq, ← s.targetEquiv.finrank_eq] at hrec
      exact hrec
    · rw [fixedFrequencyEnergy_eq_zero_of_not_surjective ι f π hπ A hA, mul_zero]
      positivity

theorem fixedFrequencyEnergy_le_of_homogeneous
    {F : Type v} [AddCommGroup F] [Module F2 F]
    [FiniteDimensional F2 F] [Fintype F]
    {I : Type w} [AddCommGroup I] [Module F2 I]
    [FiniteDimensional F2 I] [Fintype I]
    {J : Type x} [AddCommGroup J] [Module F2 J]
    [FiniteDimensional F2 J] [Fintype J]
    (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBasisInvariant f)
    (ε : ℝ) (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f)
    (π : I →ₗ[F2] J) (hπ : Function.Surjective π) (A : F →ₗ[F2] J) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π A ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε :=
  fixedFrequencyEnergy_bound_induction_inline_KMSAnalyticCharacterInduction (Module.finrank F2 J) F I J rfl ι hι f hf ε hg π hπ A

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

universe u v
attribute [local instance] mapFintype

variable {E A I J : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 A]
  [FiniteDimensional F2 I] [FiniteDimensional F2 J] [FiniteDimensional F2 F]
  [Fintype E] [Fintype A] [Fintype I] [Fintype J] [Fintype F]

theorem mixed_slice_bound (R : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ι : (A × I) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f)
    (a : A →ₗ[F2] F) (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (ν : F →ₗ[F2] J) (hr : Module.finrank F2 A + Module.finrank F2 I ≤ R) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
      sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
        (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ Module.finrank F2 A * ε := by
  have hi : Module.finrank F2 I ≤ R := by omega
  have hpow : (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) ≤
      2 ^ (4 * R * R) := by
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hi) hi
  apply mixed_bound_of_character_bound R ((2 : ℝ) ^ (4 * R * R)) ε
    (by positivity) hε π ν hπ ?_ (Module.finrank F2 A) E A rfl ι hι f hf hd a hr
  intro E' _ _ _ _ κ hκ g hg hgd
  exact (fixedFrequencyEnergy_le_of_homogeneous κ hκ g hg ε
    (AffineDensityBound.homogeneous _ ε g hgd) π hπ ν).trans
      (mul_le_mul_of_nonneg_right hpow hε)

theorem mixed_slice_bound_uniform (R : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ι : (A × I) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f)
    (a : A →ₗ[F2] F) (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (ν : F →ₗ[F2] J) (hr : Module.finrank F2 A + Module.finrank F2 I ≤ R) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
      sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
        mixedRankConstant R * ε := by
  apply (mixed_slice_bound R ε hε ι hι f hf hd a π hπ ν hr).trans
  unfold mixedRankConstant
  have hp : mixedStepFactor R ^ Module.finrank F2 A ≤ mixedStepFactor R ^ R :=
    pow_le_pow_right₀ (one_le_mixedStepFactor R) (by omega)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity)) hε

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyMixed
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Inverse.KMSFourthMoment

universe u v w

attribute [local instance] mixedMapFintype

variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

theorem uniformMixedBound_of_affineDensityBound_oai (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound r ε f) :
    UniformMixedBound r (mixedRankConstant r * ε) f := by
  intro A I J _ _ _ _ _ _ _ _ _ _ _ _ ι hι a π hπ ν hr
  exact mixed_slice_bound_uniform r ε hε ι hι f hf
    (AffineDensityBound.mono hr ε f hd) a π hπ ν hr

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end OAI
end

theorem solution.{u, v} : type_of% @OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound_oai.{u, v} := @OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound_oai.{u, v}
