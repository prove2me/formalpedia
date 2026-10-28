-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:48:54.892987+00:00
-- url     : https://prove2.me/submissions/330b5aa3-cf2e-4535-b86b-c079580cd49d

import Mathlib
import Definitions.Def_OAIQ3Ro002

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section

open scoped InnerProductSpace CStarAlgebra
open ContinuousLinearMap

open MeasureTheory Filter
open scoped BigOperators Topology


variable {Ω : Type*} [MeasurableSpace Ω]

section Rectangle

variable {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄]

open ContinuousLinearMap

theorem rectangle_square_identities
    (F : H₂ →L[ℂ] H₁) (G : H₄ →L[ℂ] H₃)
    (K : H₃ →L[ℂ] H₁) (N : H₄ →L[ℂ] H₂)
    (h₁ : F ∘L N = K ∘L G) (h₂ : F.adjoint ∘L K = N ∘L G.adjoint) :
    (K ∘L K.adjoint) ∘L F = F ∘L (N ∘L N.adjoint) ∧
    (K.adjoint ∘L K) ∘L G = G ∘L (N.adjoint ∘L N) ∧
    (F.adjoint ∘L F) ∘L N = N ∘L (G.adjoint ∘L G) ∧
    (F ∘L F.adjoint) ∘L K = K ∘L (G ∘L G.adjoint) := by
  have h₂' : K.adjoint ∘L F = G ∘L N.adjoint := by
    simpa only [adjoint_comp, adjoint_adjoint] using congrArg adjoint h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (K ∘L K.adjoint) ∘L F = K ∘L (K.adjoint ∘L F) := comp_assoc _ _ _
      _ = K ∘L (G ∘L N.adjoint) := congrArg (K ∘L ·) h₂'
      _ = (K ∘L G) ∘L N.adjoint := (comp_assoc _ _ _).symm
      _ = (F ∘L N) ∘L N.adjoint := congrArg (· ∘L N.adjoint) h₁.symm
      _ = F ∘L (N ∘L N.adjoint) := comp_assoc _ _ _
  · calc
      (K.adjoint ∘L K) ∘L G = K.adjoint ∘L (K ∘L G) := comp_assoc _ _ _
      _ = K.adjoint ∘L (F ∘L N) := congrArg (K.adjoint ∘L ·) h₁.symm
      _ = (K.adjoint ∘L F) ∘L N := (comp_assoc _ _ _).symm
      _ = (G ∘L N.adjoint) ∘L N := congrArg (· ∘L N) h₂'
      _ = G ∘L (N.adjoint ∘L N) := comp_assoc _ _ _
  · calc
      (F.adjoint ∘L F) ∘L N = F.adjoint ∘L (F ∘L N) := comp_assoc _ _ _
      _ = F.adjoint ∘L (K ∘L G) := congrArg (F.adjoint ∘L ·) h₁
      _ = (F.adjoint ∘L K) ∘L G := (comp_assoc _ _ _).symm
      _ = (N ∘L G.adjoint) ∘L G := congrArg (· ∘L G) h₂
      _ = N ∘L (G.adjoint ∘L G) := comp_assoc _ _ _
  · calc
      (F ∘L F.adjoint) ∘L K = F ∘L (F.adjoint ∘L K) := comp_assoc _ _ _
      _ = F ∘L (N ∘L G.adjoint) := congrArg (F ∘L ·) h₂
      _ = (F ∘L N) ∘L G.adjoint := (comp_assoc _ _ _).symm
      _ = (K ∘L G) ∘L G.adjoint := congrArg (· ∘L G.adjoint) h₁
      _ = K ∘L (G ∘L G.adjoint) := comp_assoc _ _ _

end Rectangle

section EssentialRanges

variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup J] [NormedSpace ℂ J]

theorem HasEssentialTotalRange.cancel_left {μ : Measure X}
    {F : X → E →L[ℂ] H} (hF : HasEssentialTotalRange μ F)
    {A B : H →L[ℂ] J} (h : ∀ᵐ x ∂μ, A ∘L F x = B ∘L F x) : A = B := by
  have hker : (A - B).ker = ⊤ := by
    apply hF (A - B).ker (A - B).isClosed_ker
    filter_upwards [h] with x hx
    rintro y ⟨v, rfl⟩
    change A (F x v) - B (F x v) = 0
    exact sub_eq_zero.mpr (DFunLike.congr_fun hx v)
  apply sub_eq_zero.mp
  ext v
  have hv : v ∈ (A - B).ker := by rw [hker]; trivial
  exact hv

theorem essentially_constant_of_intertwining
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (μC : Measure C) (μX : Measure X) (μD : Measure D)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μX] [IsProbabilityMeasure μD]
    (F : X → E →L[ℂ] H) (A : C → H →L[ℂ] H) (B : D → E →L[ℂ] E)
    (hF : HasEssentialTotalRange μX F)
    (h : ∀ᵐ p ∂μC.prod (μX.prod μD),
      A p.1 ∘L F p.2.1 = F p.2.1 ∘L B p.2.2) :
    ∃ Q : H →L[ℂ] H, ∀ᵐ c ∂μC, A c = Q := by
  have h' : ∀ᵐ c ∂μC, ∀ᵐ x ∂μX, ∀ᵐ d ∂μD,
      A c ∘L F x = F x ∘L B d :=
    (Measure.ae_ae_of_ae_prod h).mono fun _ hc => Measure.ae_ae_of_ae_prod hc
  obtain ⟨c₀, hc₀⟩ := h'.exists
  refine ⟨A c₀, h'.mono fun c hc => ?_⟩
  apply hF.cancel_left
  filter_upwards [hc, hc₀] with x hx hx₀
  obtain ⟨d, hd, hd₀⟩ := (hx.and hx₀).exists
  exact hd.trans hd₀.symm

end EssentialRanges

section HilbertEssentialRanges

variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem HasEssentialTotalRange.eq_zero_of_adjoint_ae_eq_zero
    {μ : Measure X} {F : X → E →L[ℂ] H} (hF : HasEssentialTotalRange μ F)
    {v : H} (hv : ∀ᵐ x ∂μ, (F x).adjoint v = 0) : v = 0 := by
  have hh : innerSL ℂ v = (0 : H →L[ℂ] ℂ) := by
    apply hF.cancel_left
    filter_upwards [hv] with x hx
    ext w
    change inner ℂ v (F x w) = 0
    rw [← ContinuousLinearMap.adjoint_inner_left, hx, inner_zero_left]
  exact inner_self_eq_zero.mp (DFunLike.congr_fun hh v)

theorem fixed_source_square_injective {μ : Measure X} (F : X → E →L[ℂ] H)
    (hF : HasEssentialTotalRange μ (fun x => (F x).adjoint))
    (Q : E →L[ℂ] E) (hQ : ∀ᵐ x ∂μ, (F x).adjoint ∘L F x = Q) :
    Function.Injective Q := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply hF.eq_zero_of_adjoint_ae_eq_zero
  filter_upwards [hQ] with x hx
  rw [ContinuousLinearMap.adjoint_adjoint]
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hz : (F x).adjoint (F x v) = 0 := by
    change ((F x).adjoint ∘L F x) v = 0
    rw [hx]
    exact hv
  rw [hz, inner_zero_right]

theorem essentially_constant_right_of_intertwining
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (μC : Measure C) (μX : Measure X) (μD : Measure D)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μX] [IsProbabilityMeasure μD]
    (F : X → E →L[ℂ] H) (A : C → H →L[ℂ] H) (B : D → E →L[ℂ] E)
    (hF : HasEssentialTotalRange μX (fun x => (F x).adjoint))
    (h : ∀ᵐ p ∂μC.prod (μX.prod μD),
      A p.1 ∘L F p.2.1 = F p.2.1 ∘L B p.2.2) :
    ∃ Q : E →L[ℂ] E, ∀ᵐ d ∂μD, B d = Q := by
  obtain ⟨c₀, hc₀⟩ := (Measure.ae_ae_of_ae_prod h).exists
  have hh : ∀ᵐ p ∂μD.prod μX, A c₀ ∘L F p.2 = F p.2 ∘L B p.1 := by
    have hh' : ∀ᵐ p ∂(μD.prod μX).map Prod.swap,
        A c₀ ∘L F p.1 = F p.1 ∘L B p.2 := by
      rw [Measure.prod_swap]
      exact hc₀
    exact ae_of_ae_map measurable_swap.aemeasurable hh'
  have h' := Measure.ae_ae_of_ae_prod hh
  obtain ⟨d₀, hd₀⟩ := h'.exists
  refine ⟨B d₀, h'.mono fun d hd => ?_⟩
  have heq : (B d).adjoint = (B d₀).adjoint := by
    apply hF.cancel_left
    filter_upwards [hd, hd₀] with x hx hx₀
    have hh := congrArg adjoint (hx.symm.trans hx₀)
    simpa only [adjoint_comp] using hh
  simpa only [adjoint_adjoint] using congrArg adjoint heq

end HilbertEssentialRanges

variable {X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄]

theorem hasFixedInjectiveSquares_of_fixed
    (μ : Measure X) (F : X → H₂ →L[ℂ] H₁)
    (hF : HasEssentialTotalRange μ F)
    (hFa : HasEssentialTotalRange μ (fun x => (F x).adjoint))
    (hP : ∃ P, ∀ᵐ x ∂μ, (F x).adjoint ∘L F x = P)
    (hQ : ∃ Q, ∀ᵐ x ∂μ, F x ∘L (F x).adjoint = Q) :
    HasFixedInjectiveSquares μ F := by
  obtain ⟨P, hP⟩ := hP
  obtain ⟨Q, hQ⟩ := hQ
  refine ⟨P, Q, fixed_source_square_injective F hFa P hP, ?_, hP, hQ⟩
  apply fixed_source_square_injective (fun x => (F x).adjoint) (by simpa using hF) Q
  simpa using hQ

theorem fixed_squares_of_product_identities
    (μX : Measure X) (μY : Measure Y) (μC : Measure C) (μD : Measure D)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
    (F : X → H₂ →L[ℂ] H₁) (G : Y → H₄ →L[ℂ] H₃)
    (K : C → H₃ →L[ℂ] H₁) (N : D → H₄ →L[ℂ] H₂)
    (hF : HasEssentialTotalRange μX F)
    (hFa : HasEssentialTotalRange μX (fun x => (F x).adjoint))
    (hG : HasEssentialTotalRange μY G)
    (hGa : HasEssentialTotalRange μY (fun y => (G y).adjoint))
    (hK : HasEssentialTotalRange μC K)
    (hKa : HasEssentialTotalRange μC (fun c => (K c).adjoint))
    (hN : HasEssentialTotalRange μD N)
    (hNa : HasEssentialTotalRange μD (fun d => (N d).adjoint))
    (h₁ : ∀ᵐ p ∂μC.prod (μX.prod μD),
      (K p.1 ∘L (K p.1).adjoint) ∘L F p.2.1 =
        F p.2.1 ∘L (N p.2.2 ∘L (N p.2.2).adjoint))
    (h₂ : ∀ᵐ p ∂μC.prod (μY.prod μD),
      ((K p.1).adjoint ∘L K p.1) ∘L G p.2.1 =
        G p.2.1 ∘L ((N p.2.2).adjoint ∘L N p.2.2))
    (h₃ : ∀ᵐ p ∂μX.prod (μD.prod μY),
      ((F p.1).adjoint ∘L F p.1) ∘L N p.2.1 =
        N p.2.1 ∘L ((G p.2.2).adjoint ∘L G p.2.2))
    (h₄ : ∀ᵐ p ∂μX.prod (μC.prod μY),
      (F p.1 ∘L (F p.1).adjoint) ∘L K p.2.1 =
        K p.2.1 ∘L (G p.2.2 ∘L (G p.2.2).adjoint)) :
    HasFixedInjectiveSquares μX F ∧ HasFixedInjectiveSquares μY G ∧
    HasFixedInjectiveSquares μC K ∧ HasFixedInjectiveSquares μD N := by
  have hKK := essentially_constant_of_intertwining μC μX μD F
    (fun c => K c ∘L (K c).adjoint) (fun d => N d ∘L (N d).adjoint) hF h₁
  have hNN := essentially_constant_right_of_intertwining μC μX μD F
    (fun c => K c ∘L (K c).adjoint) (fun d => N d ∘L (N d).adjoint) hFa h₁
  have hKK' := essentially_constant_of_intertwining μC μY μD G
    (fun c => (K c).adjoint ∘L K c) (fun d => (N d).adjoint ∘L N d) hG h₂
  have hNN' := essentially_constant_right_of_intertwining μC μY μD G
    (fun c => (K c).adjoint ∘L K c) (fun d => (N d).adjoint ∘L N d) hGa h₂
  have hFF' := essentially_constant_of_intertwining μX μD μY N
    (fun x => (F x).adjoint ∘L F x) (fun y => (G y).adjoint ∘L G y) hN h₃
  have hGG' := essentially_constant_right_of_intertwining μX μD μY N
    (fun x => (F x).adjoint ∘L F x) (fun y => (G y).adjoint ∘L G y) hNa h₃
  have hFF := essentially_constant_of_intertwining μX μC μY K
    (fun x => F x ∘L (F x).adjoint) (fun y => G y ∘L (G y).adjoint) hK h₄
  have hGG := essentially_constant_right_of_intertwining μX μC μY K
    (fun x => F x ∘L (F x).adjoint) (fun y => G y ∘L (G y).adjoint) hKa h₄
  exact ⟨hasFixedInjectiveSquares_of_fixed μX F hF hFa hFF' hFF,
    hasFixedInjectiveSquares_of_fixed μY G hG hGa hGG' hGG,
    hasFixedInjectiveSquares_of_fixed μC K hK hKa hKK' hKK,
    hasFixedInjectiveSquares_of_fixed μD N hN hNa hNN' hNN⟩

end

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Arrays
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnGroupKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.rowPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.splitRowKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Saturating.instNonemptyDataKind _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section

open MeasureTheory ProbabilityTheory
universe u
namespace ArrayObjects

section

attribute [instance] InitialLaws.probability

attribute [instance] Object.probability

end


end ArrayObjects

open scoped InnerProductSpace

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

namespace ConditionalTransport
variable {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

omit [MeasurableSpace Ω] in

theorem comap_le_of_factor {f : Ω → A} {g : Ω → C} {p : C → A}
    (hp : Measurable p) (h : f = p ∘ g) :
    MeasurableSpace.comap f inferInstance ≤ MeasurableSpace.comap g inferInstance := by
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hp.comap_le

end ConditionalTransport

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)


lemma row_reveal (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (a : I) (ha : a ∉ R) (n : ℕ) :
    HasCondDistrib (plane (n + 1) 0 a)
      (fun y => (amap M.par (n + 2) y, parents M R (n + 1) y))
      (((M.ownKernel (n + 1)).comap (plane (n + 1) 0 a)
        (measurable_plane _ _ _)).prodMkRight (R → Arr I M.Y (n + 1)))
      (M.law (n + 2)) := by
  let N := object M hM R hR a ha
  let e := objectExtension M hM R hR a ha
  let p : Arr I (Parameter M R) (n + 1) → Arr I M.U (n + 1) :=
    amap (fun z => z.1 a) (n + 1)
  have hpm : Measurable p := measurable_amap ((measurable_pi_apply a).comp measurable_fst) _
  have hs := hM.hasCondDistrib e n .parameter
    (amap M.par (n + 1)) (amap (parameter M R) (n + 1)) id p
    (measurable_amap M.measurable_par _) (measurable_amap (measurable_parameter M R) _)
    measurable_id hpm rfl rfl rfl
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (N.law (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩)
    (measurable_amap (measurable_parameter M R) _) hs
  have h := hp.measurableEquiv_comp_right (parameterEquiv M R (n + 1))
  change HasCondDistrib ((id ∘ amap (Function.eval a) (n + 1)) ∘ roll (n + 1))
    (parameterEquiv M R (n + 1) ∘ amap (parameter M R) (n + 1) ∘ roll (n + 1))
    (((M.ownKernel (n + 1)).comap p hpm).comap (parameterEquiv M R (n + 1)).symm
      (parameterEquiv M R (n + 1)).symm.measurable) (M.law (n + 2)) at h
  rw [Function.id_comp, select_roll, parameterEquiv_observation] at h
  have hk : (((M.ownKernel (n + 1)).comap p hpm).comap
      (parameterEquiv M R (n + 1)).symm (parameterEquiv M R (n + 1)).symm.measurable) =
      (((M.ownKernel (n + 1)).comap (plane (n + 1) 0 a)
        (measurable_plane _ _ _)).prodMkRight (R → Arr I M.Y (n + 1))) := by
    ext z : 1
    change M.ownKernel (n + 1) (p ((parameterEquiv M R (n + 1)).symm z)) =
      M.ownKernel (n + 1) (plane (n + 1) 0 a z.1)
    congr 1
    funext v
    change z.1 (Fin.cons a v) = z.1 ((0 : Fin (n + 2)).insertNth a v)
    rw [Fin.insertNth_zero']
  rw [hk] at h
  exact h

theorem rows_conditional (hM : M.IsSaturated) (J : Finset I)
    (hJ : J ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => fun a : J => plane (n + 1) 0 (a : I) y)
      (amap M.par (n + 2))
      (FiniteKernel.pi (fun a : J => (M.ownKernel (n + 1)).comap
        (plane (n + 1) 0 (a : I)) (measurable_plane _ _ _))) (M.law (n + 2)) := by
  apply ConditionalReveal.finite_reveal (M.law (n + 2)) (amap M.par (n + 2))
    (measurable_amap M.measurable_par _)
    (fun a : I => plane (n + 1) 0 a)
    (fun a : I => (M.ownKernel (n + 1)).comap (plane (n + 1) 0 a)
      (measurable_plane _ _ _)) J
  intro R hRJ a ha haR
  have hstrict : R ⊂ J := (Finset.ssubset_iff_subset_ne).mpr ⟨hRJ, by
    intro he; subst R; exact haR ha⟩
  have hcardR := Finset.card_lt_card hstrict
  have hcardJ := Finset.card_lt_card
    ((Finset.ssubset_iff_subset_ne).mpr ⟨Finset.subset_univ J, hJ⟩)
  rw [Finset.card_univ] at hcardJ
  exact row_reveal M hM R (by omega) a haR n

end ArrayObjects.Object.Rolled

namespace ConditionalReveal
variable {Ω D B ι : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
  [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [DecidableEq ι]

omit [MeasurableSpace Ω] [StandardBorelSpace B] [Nonempty B] in
lemma comap_union_reveal (E : Ω → D) (y : ι → Ω → B) (P S : Finset ι) :
    MeasurableSpace.comap (fun ω => (E ω, fun i : ↥(P ∪ S) => y i ω)) inferInstance =
    MeasurableSpace.comap (fun ω => ((E ω, fun i : P => y i ω), fun i : S => y i ω))
      inferInstance := by
  simp only [inferInstance, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk,
    MeasurableSpace.comap_process_pi]
  have hu : (⨆ i : ↥(P ∪ S), MeasurableSpace.comap (y i) inferInstance) =
      (⨆ i : P, MeasurableSpace.comap (y i) inferInstance) ⊔
      (⨆ i : S, MeasurableSpace.comap (y i) inferInstance) := by
    apply le_antisymm
    · refine iSup_le (fun i => ?_)
      rcases Finset.mem_union.mp i.property with hi | hi
      · apply le_sup_of_le_left
        exact le_iSup_of_le (⟨i, hi⟩ : P) le_rfl
      · apply le_sup_of_le_right
        exact le_iSup_of_le (⟨i, hi⟩ : S) le_rfl
    · apply sup_le
      · exact iSup_le (fun i => le_iSup_of_le ⟨i, Finset.mem_union_left S i.property⟩ le_rfl)
      · exact iSup_le (fun i => le_iSup_of_le ⟨i, Finset.mem_union_right P i.property⟩ le_rfl)
  rw [hu, sup_assoc]

theorem finite_reveal_with_parents (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → D) (hE : Measurable E) (y : ι → Ω → B)
    (hy : ∀ i, Measurable (y i)) (κ : ι → Kernel D B) [∀ i, IsMarkovKernel (κ i)]
    (P A : Finset ι)
    (h : ∀ S ⊆ A, ∀ i ∈ A, i ∉ S →
      HasCondDistrib (y i) (fun ω => (E ω, fun j : ↥(P ∪ S) => y j ω))
        ((κ i).prodMkRight (↥(P ∪ S) → B)) μ) :
    HasCondDistrib (fun ω => fun i : A => y i ω)
      (fun ω => (E ω, fun j : P => y j ω))
      (FiniteKernel.pi (fun i : A => (κ i).prodMkRight (P → B))) μ := by
  apply finite_reveal μ (fun ω => (E ω, fun j : P => y j ω))
    (hE.prodMk (Measurable.of_eval (fun j => hy j))) y
    (fun i => (κ i).prodMkRight (P → B)) A
  intro S hS i hi hiS
  apply ConditionalTransport.recondition
    (hE.prodMk (Measurable.of_eval (fun j : ↥(P ∪ S) => hy j)))
    ((hE.prodMk (Measurable.of_eval (fun j : P => hy j))).prodMk
      (Measurable.of_eval (fun j : S => hy j))) (hy i) (h S hS i hi hiS)
  · exact comap_union_reveal E y P S
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end ConditionalReveal

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_single_missing (hM : M.IsSaturated) (P A : Finset I)
    (hPA : Disjoint P A) (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (n : ℕ) (j : I) :
    HasCondDistrib (fun y => fun a : A => missingRow M n j a y)
      (revealData M P n j)
      (FiniteKernel.pi (fun a : A => (rowKernel M n j a).prodMkRight
        (P → Arr I M.Y n))) (M.law (n + 2)) := by
  apply ConditionalReveal.finite_reveal_with_parents (M.law (n + 2)) (rawData M n j)
    (measurable_rawData M n j) (fun a => missingRow M n j a)
    (fun a => measurable_missingRow M n j a) (fun a => rowKernel M n j a) P A
  intro S hSA a ha haS
  have haP : a ∉ P := fun hp => Finset.disjoint_left.mp hPA hp ha
  have hcS : S.card < A.card := Finset.card_lt_card
    ((Finset.ssubset_iff_subset_ne).mpr ⟨hSA, by intro he; subst S; exact haS ha⟩)
  have hcU := Finset.card_union_le P S
  have hc : (P ∪ S).card + 2 ≤ Fintype.card I := by omega
  have haU : a ∉ P ∪ S := by simpa only [Finset.mem_union, not_or] using And.intro haP haS
  exact parent_reveal M hM (P ∪ S) (isConditional M hM (P ∪ S) hc) a haU
    (insert_proper _ hc a haU) n j

end ArrayObjects.Object.Rolled

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in

lemma plane_first_last (n : ℕ) (a j : I) :
    plane (Y := M.Y) n 0 a ∘ plane (n + 1) (Fin.last (n + 1)) j =
      plane n (Fin.last n) j ∘ plane (n + 1) 0 a := by
  funext y v
  change y ((Fin.last (n + 1)).insertNth j ((0 : Fin (n + 1)).insertNth a v)) =
    y ((0 : Fin (n + 2)).insertNth a ((Fin.last n).insertNth j v))
  simp only [Fin.insertNth_last', Fin.insertNth_zero']
  rw [cons_snoc]

end ArrayObjects.Object.Rolled

namespace FiniteKernel
variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem pi_split {S T W : Finset ι} (hS : S ⊆ W) (hT : T ⊆ W)
    (hST : Disjoint S T) (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] :
    (pi (fun i : W => κ i)).map
      (fun y => ((fun i : S => y ⟨i, hS i.property⟩), (fun i : T => y ⟨i, hT i.property⟩))) =
      (pi (fun i : S => κ i)) ×ₖ (pi (fun i : T => κ i)) := by
  let e : S ⊕ T ↪ W := ⟨Sum.elim
    (fun i : S => (⟨i, hS i.property⟩ : W))
    (fun i : T => (⟨i, hT i.property⟩ : W)), by
      intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : W => (z : ι)) hab))
        | inr b =>
          have he : (a : ι) = b := congrArg (fun z : W => (z : ι)) hab
          exact False.elim (Finset.disjoint_left.mp hST a.property (he ▸ b.property))
      | inr a =>
        cases b with
        | inl b =>
          have he : (a : ι) = b := congrArg (fun z : W => (z : ι)) hab
          exact False.elim (Finset.disjoint_left.mp hST b.property (he ▸ a.property))
        | inr b => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : W => (z : ι)) hab))⟩
  ext x : 1
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply]
  change (Measure.pi (fun i : W => κ i x)).map _ =
    (Measure.pi (fun i : S => κ i x)).prod (Measure.pi (fun i : T => κ i x))
  have he := measure_pi_precomp (fun i : W => κ i x) e
  have hh := (measurePreserving_sumPiEquivProdPi (fun i : S ⊕ T => κ (e i) x)).map_eq
  rw [← he, Measure.map_map (MeasurableEquiv.sumPiEquivProdPi (fun _ : S ⊕ T => Y)).measurable
    (Measurable.of_eval (fun i => measurable_pi_apply (e i)))] at hh
  exact hh
end FiniteKernel

namespace ConditionalReveal
variable {ι Ω X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y]

theorem disjoint_families (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → X) (y : ι → Ω → Y)
    (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)]
    {S T W : Finset ι} (hS : S ⊆ W) (hT : T ⊆ W) (hST : Disjoint S T)
    (h : HasCondDistrib (fun ω => fun i : W => y i ω) E
      (FiniteKernel.pi (fun i : W => κ i)) μ) :
    HasCondDistrib (fun ω => fun i : T => y i ω)
      (fun ω => (E ω, fun i : S => y i ω))
      ((FiniteKernel.pi (fun i : T => κ i)).prodMkRight (S → Y)) μ := by
  have hh := h.comp_left (show Measurable (fun z : W → Y =>
      ((fun i : S => z ⟨i, hS i.property⟩), (fun i : T => z ⟨i, hT i.property⟩))) from by fun_prop)
  rw [FiniteKernel.pi_split hS hT hST κ, ← ConditionalScreens.compProd_prodMkRight] at hh
  exact hh.of_compProd
end ConditionalReveal

namespace ConditionalScreens
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]

theorem screened_marginal {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : Ω → X} {y : Ω → Y} {z : Ω → Z}
    (hx : Measurable x) (hy : Measurable y)
    {κ η : Kernel X Z} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : HasCondDistrib z (fun ω => (x ω, y ω)) (κ.prodMkRight Y) μ)
    (hη : HasCondDistrib z x η μ) :
    HasCondDistrib z (fun ω => (x ω, y ω)) (η.prodMkRight Y) μ := by
  have hκ : HasCondDistrib z x κ μ := h.comp_right
  have hke : κ =ᵐ[μ.map x] η :=
    (condDistrib_ae_eq_of_measure_eq_compProd hκ.aemeasurable_fst hκ.aemeasurable_snd hκ.map_eq).symm.trans
      (condDistrib_ae_eq_of_measure_eq_compProd hη.aemeasurable_fst hη.aemeasurable_snd hη.map_eq)
  refine ⟨h.aemeasurable, h.map_eq.trans (Measure.compProd_congr ?_)⟩
  have hf : (μ.map (fun ω => (x ω, y ω))).map Prod.fst = μ.map x := by
    rw [Measure.map_map measurable_fst (hx.prodMk hy)]
    rfl
  rw [← hf] at hke
  exact ae_of_ae_map measurable_fst.aemeasurable hke
end ConditionalScreens

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem columns_with_parents (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (n : ℕ)
    (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes (n + 1) J) (parentData M R n)
      (FiniteKernel.pi (fun j : J => columnKernel M R n j)) (M.law (n + 2)) := by
  have hi : ∀ S : Finset I, S ⊂ R → IsConditional M S := by
    intro S hS
    apply isConditional M hM S
    have hc := Finset.card_lt_card hS
    omega
  have hc := proper_conditional M hM R hR hi n J hJ
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (law M (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩)
    (measurable_amap (measurable_parameter M R) _) hc
  have hd := hp.measurableEquiv_comp_right (parameterEquiv M R (n + 1))
  have h := hd.comp_left (Measurable.of_eval (fun j : J =>
    (roll n).symm.measurable.comp (measurable_pi_apply j)))
  have ho : (fun z : J → Arr I (State M) n => fun j => (roll n).symm (z j)) ∘
      planes n J ∘ roll (n + 1) = planes (n + 1) J := by
    rw [planes_roll]
    funext y j
    exact (roll n).symm_apply_apply _
  change HasCondDistrib
    ((fun z : J → Arr I (State M) n => fun j => (roll n).symm (z j)) ∘
      planes n J ∘ roll (n + 1))
    (parameterEquiv M R (n + 1) ∘ amap (parameter M R) (n + 1) ∘ roll (n + 1))
    _ (M.law (n + 2)) at h
  rw [ho, parameterEquiv_observation] at h
  change HasCondDistrib (planes (n + 1) J) (parentData M R n) _ (M.law (n + 2)) at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext p : 1
  rw [Kernel.map_apply _ (Measurable.of_eval (fun j : J =>
    (roll n).symm.measurable.comp (measurable_pi_apply j)))]
  change Measure.pi (fun j : J => columnKernel M R n j p) =
    (Measure.pi (fun j : J => ownPosterior M R n
      (plane n (Fin.last n) j ((parameterEquiv M R (n + 1)).symm p)))).map _
  simp only [Function.comp_def]
  rw [Measure.pi_map_pi (fun _ => (roll n).symm.measurable.aemeasurable)]
  simp only [columnKernel, Kernel.comap_apply, Function.comp_apply,
    Kernel.map_apply _ (roll n).symm.measurable]


omit [DecidableEq I] in
lemma columnRestrict_planes (A J : Finset I) (n : ℕ) :
    columnRestrict M A J n ∘ planes (n + 1) J = cells M A J n := by
  funext y j a
  exact congrFun (plane_first_last M n a j) y

theorem group_marginal_with_parents (hM : M.IsSaturated) (P A J : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (cells M A J n) (parentData M P n)
      ((groupMarginal M A J n).prodMkRight (P → Arr I M.Y (n + 1))) (M.law (n + 2)) := by
  have h := ConditionalReveal.disjoint_families (M.law (n + 2)) (amap M.par (n + 2))
    (fun a => plane (n + 1) 0 a)
    (fun a => (M.ownKernel (n + 1)).comap (plane (n + 1) 0 a) (measurable_plane _ _ _))
    Finset.subset_union_left Finset.subset_union_right hPA
    (rows_conditional M hM (P ∪ A) hproper n)
  have hh := h.comp_left (measurable_rowRestrict M A J n)
  rw [Kernel.map_prodMkRight] at hh
  exact hh

theorem group_intermediate_marginal (hM : M.IsSaturated) (P A C J : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hproper : P ∪ A ≠ Finset.univ) (hCJ : Disjoint C J) (hcols : C ∪ J ≠ Finset.univ)
    (n : ℕ) :
    HasCondDistrib (cells M A J n)
      (fun y => (parentData M P n y, planes (n + 1) C y))
      (((groupMarginal M A J n).prodMkRight (P → Arr I M.Y (n + 1))).prodMkRight
        (C → Arr I M.Y (n + 1))) (M.law (n + 2)) := by
  have h := ConditionalReveal.disjoint_families (M.law (n + 2)) (parentData M P n)
    (fun j => plane (n + 1) (Fin.last (n + 1)) j) (columnKernel M P n)
    Finset.subset_union_left Finset.subset_union_right hCJ
    (columns_with_parents M hM P hP n (C ∪ J) hcols)
  have hk := h.comp_left (measurable_columnRestrict M A J n)
  rw [Kernel.map_prodMkRight] at hk
  change HasCondDistrib (columnRestrict M A J n ∘ planes (n + 1) J)
    (fun y => (parentData M P n y, planes (n + 1) C y))
    (((FiniteKernel.pi (fun j : J => columnKernel M P n j)).map
      (columnRestrict M A J n)).prodMkRight (C → Arr I M.Y (n + 1))) (M.law (n + 2)) at hk
  rw [columnRestrict_planes] at hk
  have : IsMarkovKernel ((FiniteKernel.pi (fun j : J => columnKernel M P n j)).map
      (columnRestrict M A J n)) := Kernel.IsMarkovKernel.map _ (measurable_columnRestrict M A J n)
  exact ConditionalScreens.screened_marginal (measurable_parentData M P n)
    (measurable_planes _ _) hk (group_marginal_with_parents M hM P A J hPA hproper n)


omit [DecidableEq I] in
lemma groupSelect_observation (P A C : Finset I) (n : ℕ) :
    groupSelect M P A C n ∘ wholeGroupData M P C n = groupData M A C n := by
  funext y
  apply Prod.ext
  · rfl
  · exact congrFun (columnRestrict_planes M A C n) y

lemma revealParent_observation (P : Finset I) (n : ℕ) (j : I) :
    revealParent M P n j ∘ revealData M P n j = parentData M P n := by
  change (parameterEquiv M P (n + 1) ∘ Prod.fst) ∘
    (revealToRoll M P n j ∘ revealData M P n j) = _
  rw [revealToRoll_observation]
  exact parameterEquiv_observation M P (n + 1)

lemma revealSelect_observation (P A C J : Finset I) (n : ℕ) (j : I)
    (hC : C ⊆ Outside j) (hJ : J ⊆ Outside j) :
    revealSelect M P A C J n j hC hJ ∘ revealData M P n j =
      fun y => (wholeGroupData M P C n y, cells M A J n y) := by
  funext y
  apply Prod.ext
  · apply Prod.ext
    · exact congrFun (revealParent_observation M P n j) y
    · rfl
  · funext k a
    exact congrFun (plane_first_last M n a k) y

theorem grouped_missing_after_retain (hM : M.IsSaturated) (P A C J : Finset I)
    (hPA : Disjoint P A) (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (n : ℕ) (j : I) (hCJ : C ∪ J = Outside j) :
    HasCondDistrib (fun y => fun a : A => missingRow M n j a y)
      (fun y => (wholeGroupData M P C n y, cells M A J n y))
      ((groupLastKernel M A C J n j hCJ).comap (wholeLastSelect M P A C J n)
        (measurable_wholeLastSelect M P A C J n)) (M.law (n + 2)) := by
  have hC : C ⊆ Outside j := hCJ ▸ Finset.subset_union_left
  have hJ : J ⊆ Outside j := hCJ ▸ Finset.subset_union_right
  have h := grouped_single_missing M hM P A hPA hcard n j
  have he : (FiniteKernel.pi (fun a : A => (rowKernel M n j a).prodMkRight (P → Arr I M.Y n))) =
      (((groupLastKernel M A C J n j hCJ).comap (wholeLastSelect M P A C J n)
        (measurable_wholeLastSelect M P A C J n)).comap
          (revealSelect M P A C J n j hC hJ) (measurable_revealSelect M P A C J n j hC hJ)) := by
    ext p : 1
    change Measure.pi _ = Measure.pi _
    congr 1
    funext a
    change (condDistrib _ _ _) (rowData M n j a p.1) =
      (condDistrib _ _ _) (groupLastData M A C J n j hCJ a
        (wholeLastSelect M P A C J n (revealSelect M P A C J n j hC hJ p)))
    congr 1
    apply Prod.ext
    · funext v
      simp [groupLastData, wholeLastSelect, groupSelect, revealSelect, rowData,
        revealParent, parameterEquiv, revealToRoll, plane, Fin.insertNth_zero']
    · funext k
      simp only [groupLastData, wholeLastSelect, groupSelect, columnRestrict, revealSelect, rowData]
      split_ifs <;> rfl
  rw [he] at h
  have hh := h.comp_right
  rw [revealSelect_observation] at hh
  exact hh

end ArrayObjects.Object.Rolled

namespace ConditionalScreens
variable {Ω D E Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
  [MeasurableSpace E] [MeasurableSpace Y] [MeasurableSpace Z]

lemma compProd_comap (κ : Kernel E Y) (η : Kernel (E × Y) Z)
    [IsMarkovKernel κ] [IsMarkovKernel η] (f : D → E) (hf : Measurable f) :
    κ.comap f hf ⊗ₖ η.comap (Prod.map f id) (hf.prodMap measurable_id) =
      (κ ⊗ₖ η).comap f hf := by
  ext d s hs
  rw [Kernel.compProd_apply hs]
  change (∫⁻ y, η (f d, y) (Prod.mk y ⁻¹' s) ∂κ (f d)) = (κ ⊗ₖ η) (f d) s
  exact (Kernel.compProd_apply hs κ η (f d)).symm

theorem canonical_screen [StandardBorelSpace Y] [Nonempty Y]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {y : Ω → Y} {d : Ω → D}
    (hd : Measurable d) (f : D → E) (hf : Measurable f)
    {κ : Kernel E Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y d (κ.comap f hf) μ) :
    HasCondDistrib y d ((condDistrib y (f ∘ d) μ).comap f hf) μ := by
  have hκ := h.comp_right
  have he : κ =ᵐ[μ.map (f ∘ d)] condDistrib y (f ∘ d) μ :=
    (condDistrib_ae_eq_of_measure_eq_compProd hκ.aemeasurable_fst hκ.aemeasurable_snd hκ.map_eq).symm
  rw [← Measure.map_map hf hd] at he
  refine ⟨h.aemeasurable, h.map_eq.trans (Measure.compProd_congr ?_)⟩
  exact ae_of_ae_map hf.aemeasurable he
end ConditionalScreens

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma joinOutput_observation (A J : Finset I) (n : ℕ) (j : I) :
    joinOutput M A J n j ∘ (fun y => (cells M A J n y, fun a : A => missingRow M n j a y)) =
      cells M A (insert j J) n := by
  funext y k a
  simp only [Function.comp_apply, joinOutput, cells]
  split_ifs with h
  · simp [h]
  · rfl

theorem grouped_cell_locality (hM : M.IsSaturated) (P A C J : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hdisj : Disjoint C J)
    (n : ℕ) (j : I) (hCJ : C ∪ J = Outside j) :
    HasCondDistrib (cells M A (insert j J) n) (wholeGroupData M P C n)
      ((condDistrib (cells M A (insert j J) n) (groupData M A C n) (M.law (n + 2))).comap
        (groupSelect M P A C n) (measurable_groupSelect M P A C n)) (M.law (n + 2)) := by
  have hcols : C ∪ J ≠ Finset.univ := by
    rw [hCJ]
    simp [Outside]
  have hW := group_intermediate_marginal M hM P A C J hP hPA hproper hdisj hcols n
  have hZ := grouped_missing_after_retain M hM P A C J hPA hcard n j hCJ
  have h := ConditionalScreens.chain hW hZ
  have hke : (((groupMarginal M A J n).prodMkRight (P → Arr I M.Y (n + 1))).prodMkRight
        (C → Arr I M.Y (n + 1))) =
      ((groupMarginal M A J n).prodMkRight (C → A → Arr I M.Y n)).comap
        (groupSelect M P A C n) (measurable_groupSelect M P A C n) := by
    ext p : 1
    rfl
  rw [hke] at h
  change HasCondDistrib _ (wholeGroupData M P C n)
    (((groupMarginal M A J n).prodMkRight (C → A → Arr I M.Y n)).comap
      (groupSelect M P A C n) (measurable_groupSelect M P A C n) ⊗ₖ
      (groupLastKernel M A C J n j hCJ).comap (Prod.map (groupSelect M P A C n) id)
        ((measurable_groupSelect M P A C n).prodMap measurable_id)) _ at h
  rw [ConditionalScreens.compProd_comap] at h
  have hh := h.comp_left (measurable_joinOutput M A J n j)
  rw [joinOutput_observation, ← Kernel.comap_map_comm _ _ (measurable_joinOutput M A J n j)] at hh
  have : IsMarkovKernel
      (((groupMarginal M A J n).prodMkRight (C → A → Arr I M.Y n) ⊗ₖ
        groupLastKernel M A C J n j hCJ).map (joinOutput M A J n j)) :=
    Kernel.IsMarkovKernel.map _ (measurable_joinOutput M A J n j)
  have hv := ConditionalScreens.canonical_screen (measurable_wholeGroupData M P C n)
    (groupSelect M P A C n) (measurable_groupSelect M P A C n) hh
  rw [groupSelect_observation] at hv
  exact hv

end ArrayObjects.Object.Rolled
end

open MeasureTheory ProbabilityTheory

namespace ConditionalFibres
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {η : Kernel U Ω} [IsMarkovKernel η] {κ : Kernel (U × X) Y} [IsMarkovKernel κ]

omit [StandardBorelSpace X] [StandardBorelSpace Y] [IsProbabilityMeasure μ] [IsMarkovKernel κ] in
lemma chain {α : Kernel U X} [IsMarkovKernel α]
    (hx : HasCondDistrib x u α μ)
    (hy : HasCondDistrib y (fun ω => (u ω, x ω)) κ μ) :
    HasCondDistrib (fun ω => (x ω, y ω)) u (α ⊗ₖ κ) μ := by
  refine ⟨hx.aemeasurable_fst.prodMk
    (hx.aemeasurable_snd.prodMk hy.aemeasurable_snd), ?_⟩
  calc
    μ.map (fun ω => (u ω, x ω, y ω)) =
        (μ.map (fun ω => ((u ω, x ω), y ω))).map MeasurableEquiv.prodAssoc := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hy.aemeasurable]
      rfl
    _ = ((μ.map u ⊗ₘ α) ⊗ₘ κ).map MeasurableEquiv.prodAssoc := by
      rw [hy.map_eq, hx.map_eq]
    _ = μ.map u ⊗ₘ (α ⊗ₖ κ) := Measure.compProd_assoc'

theorem disintegrate (hx : Measurable x) (hy : Measurable y)
    (hη : HasCondDistrib id u η μ)
    (hκ : HasCondDistrib y (fun ω => (u ω, x ω)) κ μ) :
    ∀ᵐ a ∂μ.map u, HasCondDistrib y x (κ.sectR a) (η a) := by
  let : IsMarkovKernel (η.map x) := Kernel.IsMarkovKernel.map η hx
  let : IsMarkovKernel (η.map (fun ω => (x ω, y ω))) :=
    Kernel.IsMarkovKernel.map η (hx.prodMk hy)
  have hpair := chain (hη.comp_left hx) hκ
  have hother := hη.comp_left (hx.prodMk hy)
  have he : η.map (fun ω => (x ω, y ω)) =ᵐ[μ.map u] (η.map x) ⊗ₖ κ :=
    Kernel.ae_eq_of_compProd_eq (hother.map_eq.symm.trans hpair.map_eq)
  filter_upwards [he] with a ha
  refine ⟨(hx.prodMk hy).aemeasurable, ?_⟩
  rw [Kernel.map_apply _ (hx.prodMk hy), Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.map_apply _ hx] at ha
  exact ha

theorem marginal (hx : Measurable x) (hη : HasCondDistrib id u η μ)
    {α : Kernel U X} [IsMarkovKernel α] (hα : HasCondDistrib x u α μ) :
    ∀ᵐ a ∂μ.map u, MeasurePreserving x (η a) (α a) := by
  let : IsMarkovKernel (η.map x) := Kernel.IsMarkovKernel.map η hx
  have he : η.map x =ᵐ[μ.map u] α :=
    Kernel.ae_eq_of_compProd_eq ((hη.comp_left hx).map_eq.symm.trans hα.map_eq)
  filter_upwards [he] with a ha
  exact ⟨hx, (Kernel.map_apply η hx a).symm.trans ha⟩

end ConditionalFibres

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Joinings
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


section
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y} {z : X → Z}

lemma operator_adjoint (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    (operator hx hy).adjoint = operator hy hx := by simp [operator]

lemma pull_adjoint_pull (hx : MeasurePreserving x μ ν) :
    (pull hx).adjoint ∘L pull hx = ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (pull hx)).mp
  intro g
  exact Lp.norm_compMeasurePreserving g hx

lemma pull_comp (hx : MeasurePreserving x μ ν) (hz : MeasurePreserving z ν τ) :
    pull (hz.comp hx) = pull hx ∘L pull hz := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.compMeasurePreserving_comp_apply f hz hx

lemma inner_operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    inner ℂ g (operator hx hy h) = ∫ ω, inner ℂ (g (x ω)) (h (y ω)) ∂μ := by
  change inner ℂ g ((pull hx).adjoint (pull hy h)) = _
  rw [adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving g hx, Lp.coeFn_compMeasurePreserving h hy]
    with ω hg hh
  change inner ℂ (Lp.compMeasurePreserving x hx g ω) (Lp.compMeasurePreserving y hy h ω) = _
  rw [hg, hh]
  rfl

lemma operator_pullback {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {f : Ω' → Ω} (hf : MeasurePreserving f μ' μ)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    operator (hx.comp hf) (hy.comp hf) = operator hx hy := by
  simp only [operator]
  rw [pull_comp hf hx, pull_comp hf hy, adjoint_comp]
  calc
    ((pull hx).adjoint ∘L (pull hf).adjoint) ∘L (pull hf ∘L pull hy) =
        (pull hx).adjoint ∘L (((pull hf).adjoint ∘L pull hf) ∘L pull hy) := by
      simp only [comp_assoc]
    _ = (pull hx).adjoint ∘L pull hy := by rw [pull_adjoint_pull, id_comp]

end
section

variable {Ω X Y : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y}
  {x : Ω → X} {y : Ω → Y}

lemma pull_range (hx : MeasurePreserving x μ ν) :
    LinearMap.range (pull hx).toLinearMap =
      lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    have hm : StronglyMeasurable[MeasurableSpace.comap x inferInstance] (fun ω => g (x ω)) :=
      g.1.stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)
    exact hm.aestronglyMeasurable.congr (Lp.coeFn_compMeasurePreserving g hx).symm
  · intro hf
    have hm := mem_lpMeas_iff_aestronglyMeasurable.mp hf
    obtain ⟨g, hg, he⟩ := hm.stronglyMeasurable_mk.exists_eq_measurable_comp
    have hfe : f =ᵐ[μ] g ∘ x := hm.ae_eq_mk.trans (Filter.Eventually.of_forall (congrFun he))
    have hLp : MemLp g 2 ν := by
      rw [← hx.map_eq]
      exact (memLp_map_measure_iff hg.aestronglyMeasurable hx.aemeasurable).mpr
        ((memLp_congr_ae hfe).mp (Lp.memLp f))
    refine ⟨hLp.toLp g, ?_⟩
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving (hLp.toLp g) hx).trans
      ((hx.quasiMeasurePreserving.ae_eq_comp hLp.coeFn_toLp).trans hfe.symm)

lemma pull_adjoint_projection (hx : MeasurePreserving x μ ν) (f : Lp ℂ 2 μ) :
    pull hx ((pull hx).adjoint f) =
      (condExpL2 ℂ ℂ hx.measurable.comap_le f : Lp ℂ 2 μ) := by
  let S := lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ
  let : Fact (MeasurableSpace.comap x inferInstance ≤ mΩ) := ⟨hx.measurable.comap_le⟩
  change _ = S.starProjection f
  apply (S.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_).symm
  · change _ ∈ lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ
    rw [← pull_range hx]
    exact ⟨(pull hx).adjoint f, rfl⟩
  · intro u hu
    change u ∈ lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ at hu
    rw [← pull_range hx] at hu
    obtain ⟨g, rfl⟩ := hu
    rw [inner_sub_left]
    change inner ℂ f (pull hx g) -
      inner ℂ (pull hx ((pull hx).adjoint f)) (pull hx g) = 0
    rw [← adjoint_inner_left, ← adjoint_inner_left]
    change inner ℂ ((pull hx).adjoint f) g -
      inner ℂ (((pull hx).adjoint ∘L pull hx) ((pull hx).adjoint f)) g = 0
    rw [pull_adjoint_pull]
    simp

lemma operator_ae_eq_condExp [IsFiniteMeasure μ]
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) (h : Lp ℂ 2 ρ) :
    (fun ω => operator hx hy h (x ω)) =ᵐ[μ]
      μ[(fun ω => h (y ω)) | MeasurableSpace.comap x inferInstance] := by
  have hp := pull_adjoint_projection hx (pull hy h)
  have hc := (Lp.memLp (pull hy h)).condExpL2_ae_eq_condExp (𝕜 := ℂ) hx.measurable.comap_le
  rw [Lp.toLp_coeFn, ← hp] at hc
  exact (Lp.coeFn_compMeasurePreserving (operator hx hy h) hx).symm.trans
    (hc.trans (condExp_congr_ae (Lp.coeFn_compMeasurePreserving h hy)))


end
section

variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [MeasurableSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure X} {ρ : Measure Y}
  {τ : Measure Z} {x : Ω → X} {y : Ω → Y} {z : X → Z}

lemma condExp_of_kernel (hx : Measurable x) {κ : Kernel X Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x κ μ) (g : Y → ℂ) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω => g (y ω)) μ) :
    μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      (fun ω => ∫ v, g v ∂κ (x ω)) := by
  have he : condDistrib y x μ =ᵐ[μ.map x] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd h.aemeasurable_fst h.aemeasurable_snd h.map_eq
  have he' := ae_of_ae_map hx.aemeasurable he
  filter_upwards [condExp_ae_eq_integral_condDistrib hx h.aemeasurable_snd hg hgi, he']
    with ω hω heω
  exact hω.trans (by rw [heω])

lemma screened_condExp (hx : Measurable x) (hz : Measurable z)
    {κ : Kernel Z Y} [IsMarkovKernel κ] (h : HasCondDistrib y x (κ.comap z hz) μ)
    (g : Y → ℂ) (hg : StronglyMeasurable g) (hgi : Integrable (fun ω => g (y ω)) μ) :
    μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      μ[(fun ω => g (y ω)) | MeasurableSpace.comap (z ∘ x) inferInstance] :=
  (condExp_of_kernel hx h g hg hgi).trans
    (condExp_of_kernel (hz.comp hx) h.comp_right g hg hgi).symm

theorem screened_operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hz : MeasurePreserving z ν τ) {κ : Kernel Z Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x (κ.comap z hz.measurable) μ) :
    operator hx hy = pull hz ∘L operator (hz.comp hx) hy := by
  apply ContinuousLinearMap.ext
  intro g
  apply (Lp.compMeasurePreservingₗᵢ ℂ x hx).injective
  change pull hx (operator hx hy g) = (pull hx ∘L pull hz) (operator (hz.comp hx) hy g)
  rw [← pull_comp]
  apply Lp.ext
  have hgi : Integrable (fun ω => g (y ω)) μ :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ((Lp.memLp g).comp_measurePreserving hy)
  have hce := screened_condExp hx.measurable hz.measurable h g g.1.stronglyMeasurable hgi
  exact (Lp.coeFn_compMeasurePreserving _ hx).trans
    ((operator_ae_eq_condExp hx hy g).trans
      (hce.trans ((operator_ae_eq_condExp (hz.comp hx) hy g).symm.trans
        (Lp.coeFn_compMeasurePreserving _ (hz.comp hx)).symm)))


end


lemma operator_comp_right {Ω S A : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace A] {μ : Measure Ω} {ν : Measure S} {ρ : Measure A}
    {T : Type*} [MeasurableSpace T] {τ : Measure T}
    {s : Ω → S} {t : Ω → T} {a : T → A}
    (hs : MeasurePreserving s μ ν) (ht : MeasurePreserving t μ τ)
    (ha : MeasurePreserving a τ ρ) :
    operator hs (ha.comp ht) = operator hs ht ∘L pull ha := by
  unfold operator
  rw [pull_comp ht ha]
  simp only [comp_assoc]

variable {Ω S T A B C D : Type*}
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
  [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
  [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
  [MeasurableSpace D] [StandardBorelSpace D] [Nonempty D]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {νs : Measure S} {νt : Measure T}
  {νa : Measure A} {νb : Measure B} {νc : Measure C} {νd : Measure D}
  {s : Ω → S} {t : Ω → T} {a : S → A} {b : S → B} {c : T → C} {d : T → D}

theorem square_rectangle
    (hs : MeasurePreserving s μ νs) (ht : MeasurePreserving t μ νt)
    (ha : MeasurePreserving a νs νa) (hb : MeasurePreserving b νs νb)
    (hc : MeasurePreserving c νt νc) (hd : MeasurePreserving d νt νd)
    {κac : Kernel A C} [IsMarkovKernel κac] {κbd : Kernel B D} [IsMarkovKernel κbd]
    {κca : Kernel C A} [IsMarkovKernel κca] {κdb : Kernel D B} [IsMarkovKernel κdb]
    (hac : HasCondDistrib (c ∘ t) s (κac.comap a ha.measurable) μ)
    (hbd : HasCondDistrib (d ∘ t) s (κbd.comap b hb.measurable) μ)
    (hca : HasCondDistrib (a ∘ s) t (κca.comap c hc.measurable) μ)
    (hdb : HasCondDistrib (b ∘ s) t (κdb.comap d hd.measurable) μ) :
    let F := operator (ha.comp hs) (hc.comp ht)
    let G := operator (hb.comp hs) (hd.comp ht)
    let K := operator ha hb
    let N := operator hc hd
    F ∘L N = K ∘L G ∧ F.adjoint ∘L K = N ∘L G.adjoint := by
  dsimp only
  let Q := operator hs ht
  let F := operator (ha.comp hs) (hc.comp ht)
  let G := operator (hb.comp hs) (hd.comp ht)
  have haf : Q ∘L pull hc = pull ha ∘L F := by
    rw [← operator_comp_right]
    exact screened_operator hs (hc.comp ht) ha hac
  have hbf : Q ∘L pull hd = pull hb ∘L G := by
    rw [← operator_comp_right]
    exact screened_operator hs (hd.comp ht) hb hbd
  have har : Q.adjoint ∘L pull ha = pull hc ∘L F.adjoint := by
    dsimp only [Q, F]
    rw [operator_adjoint, operator_adjoint, ← operator_comp_right]
    exact screened_operator ht (ha.comp hs) hc hca
  have hbr : Q.adjoint ∘L pull hb = pull hd ∘L G.adjoint := by
    dsimp only [Q, G]
    rw [operator_adjoint, operator_adjoint, ← operator_comp_right]
    exact screened_operator ht (hb.comp hs) hd hdb
  have hara : (pull ha).adjoint ∘L Q = F ∘L (pull hc).adjoint := by
    have hh := congrArg ContinuousLinearMap.adjoint har
    simpa only [adjoint_comp, adjoint_adjoint] using hh
  have hafa : (pull hc).adjoint ∘L Q.adjoint = F.adjoint ∘L (pull ha).adjoint := by
    simpa only [adjoint_comp] using congrArg ContinuousLinearMap.adjoint haf
  constructor
  · change F ∘L ((pull hc).adjoint ∘L pull hd) =
      ((pull ha).adjoint ∘L pull hb) ∘L G
    calc
      _ = ((pull ha).adjoint ∘L Q) ∘L pull hd := by rw [hara]; simp only [comp_assoc]
      _ = _ := by rw [comp_assoc, hbf]; simp only [comp_assoc]
  · change F.adjoint ∘L ((pull ha).adjoint ∘L pull hb) =
      ((pull hc).adjoint ∘L pull hd) ∘L G.adjoint
    calc
      _ = ((pull hc).adjoint ∘L Q.adjoint) ∘L pull hb := by
        rw [hafa]; simp only [comp_assoc]
      _ = _ := by rw [comp_assoc, hbr]; simp only [comp_assoc]


end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory

section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma fullGroupedLocality (hM : M.IsSaturated) (P A C D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hCD : Disjoint C D)
    (hcover : C ∪ D = Finset.univ) (hD : D.Nonempty) (n : ℕ) :
    HasCondDistrib (cells M A D n) (wholeGroupData M P C n)
      ((condDistrib (cells M A D n) (groupData M A C n) (M.law (n+2))).comap
        (groupSelect M P A C n) (measurable_groupSelect M P A C n)) (M.law (n+2)) := by
  obtain ⟨j,hj⟩ := hD
  have hd : Disjoint C (D.erase j) := hCD.mono_right (Finset.erase_subset _ _)
  have hcj : C ∪ D.erase j = Outside j := by
    ext i
    have hjC : j ∉ C := fun h => Finset.disjoint_left.mp hCD h hj
    have hi : i ∈ C ∨ i ∈ D := Finset.mem_union.mp (hcover ▸ Finset.mem_univ i)
    simp only [Finset.mem_union, Finset.mem_erase, Outside, Finset.mem_erase,
      Finset.mem_univ, and_true]
    constructor
    · rintro (h | h)
      · exact fun e => hjC (e ▸ h)
      · exact h.1
    · intro h
      rcases hi with hi | hi
      · exact Or.inl hi
      · exact Or.inr ⟨h,hi⟩
  have h := grouped_cell_locality M hM P A C (D.erase j) hP hPA hcard hproper hd n j hcj
  erw [Finset.insert_erase hj] at h
  exact h

lemma wholeSplit_field (P R S : Finset I) (n : ℕ) :
    MeasurableSpace.comap (wholeGroupData M P (R ∪ S) n) inferInstance =
      MeasurableSpace.comap (fun y => (wholeGroupData M P R n y, planes (n+1) S y)) inferInstance := by
  apply le_antisymm
  · apply ConditionalTransport.comap_le_of_factor
      (p := fun v : WholeGroupData M P R n × (S → Arr I M.Y (n+1)) =>
        (v.1.1, tupleUnion R S (v.1.2,v.2))) (by fun_prop)
    funext y
    apply Prod.ext
    · rfl
    · funext i
      simp only [Function.comp_apply, wholeGroupData,tupleUnion,planes]
      split_ifs <;> rfl
  · apply ConditionalTransport.comap_le_of_factor
      (p := fun v : WholeGroupData M P (R ∪ S) n =>
        ((v.1,tupleSelect R (R∪S) Finset.subset_union_left v.2),
          tupleSelect S (R∪S) Finset.subset_union_right v.2)) (by fun_prop)
    rfl

lemma splitRowScreen (hM : M.IsSaturated) (P A R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hCD : Disjoint (R ∪ S) D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hD : D.Nonempty) (n : ℕ) :
    HasCondDistrib (cells M A D n)
      (fun y => (wholeGroupData M P R n y, planes (n+1) S y))
      ((splitRowKernel M P A R S D n).comap
        (Prod.map id (columnRestrict M A S n)) (by fun_prop)) (M.law (n+2)) := by
  apply ConditionalTransport.recondition (measurable_wholeGroupData M P (R∪S) n)
    (by fun_prop) (measurable_cells M A D n)
    (fullGroupedLocality M hM P A (R∪S) D hP hPA hcard hproper hCD hcover hD n)
    (wholeSplit_field M P R S n)
  apply Filter.Eventually.of_forall
  intro y
  change (condDistrib (cells M A D n) (groupData M A (R∪S) n) (M.law (n+2)))
      (groupSelect M P A (R∪S) n (wholeGroupData M P (R∪S) n y)) =
    (condDistrib (cells M A D n) (groupData M A (R∪S) n) (M.law (n+2))) _
  congr 1
  apply Prod.ext
  · rfl
  · funext i a
    simp only [groupSelect,splitOwnData,Prod.map_apply,Function.id_def,wholeGroupData,
      tupleUnion,columnRestrict,planes]
    split_ifs <;> rfl

lemma splitRowScreen_fibre (hM : M.IsSaturated) (P A R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hCD : Disjoint (R ∪ S) D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hD : D.Nonempty) (n : ℕ) :
    ∀ᵐ u ∂(M.law (n+2)).map (wholeGroupData M P R n),
      HasCondDistrib (cells M A D n) (planes (n+1) S)
        (((splitRowKernel M P A R S D n).sectR u).comap
          (columnRestrict M A S n) (measurable_columnRestrict M A S n))
        (condDistrib id (wholeGroupData M P R n) (M.law (n+2)) u) := by
  have hη := (show HasCondDistrib id (wholeGroupData M P R n)
      (condDistrib id (wholeGroupData M P R n) (M.law (n+2))) (M.law (n+2)) from
      ⟨(by fun_prop), (compProd_map_condDistrib (μ := M.law (n+2)) measurable_id.aemeasurable).symm⟩)
  exact ConditionalFibres.disintegrate (measurable_planes _ _) (measurable_cells M A D n)
    hη (splitRowScreen M hM P A R S D hP hPA hcard hproper hCD hcover hD n)

lemma cellMarginal_fibre (hM : M.IsSaturated) (P A R S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hproper : P ∪ A ≠ Finset.univ) (hRS : Disjoint R S)
    (hcols : R ∪ S ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ u ∂(M.law (n+2)).map (wholeGroupData M P R n),
      MeasurePreserving (columnRestrict M A S n)
        ((squareFibre M P R n u).map (planes (n+1) S)) (cellLaw M A S n u.1.1) := by
  have hη : HasCondDistrib id (wholeGroupData M P R n) (squareFibre M P R n) (M.law (n+2)) :=
    ⟨(by fun_prop), (compProd_map_condDistrib (μ := M.law (n+2)) measurable_id.aemeasurable).symm⟩
  have h := ConditionalFibres.marginal (measurable_cells M A S n) hη
    (group_intermediate_marginal M hM P A R S hP hPA hproper hRS hcols n)
  filter_upwards [h] with u hu
  refine ⟨measurable_columnRestrict M A S n, ?_⟩
  rw [Measure.map_map (measurable_columnRestrict M A S n) (measurable_planes _ _),
    columnRestrict_planes]
  exact hu.map_eq

theorem grouped_rectangle (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A) (hPB : Disjoint P B)
    (hcardA : P.card + A.card + 1 ≤ Fintype.card I)
    (hcardB : P.card + B.card + 1 ≤ Fintype.card I)
    (hproperA : P ∪ A ≠ Finset.univ) (hproperB : P ∪ B ≠ Finset.univ)
    (hRS : Disjoint R S) (hRD : Disjoint R D) (hSD : Disjoint S D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hS : S.Nonempty) (hD : D.Nonempty) (n : ℕ) :
    ∀ᵐ u ∂(M.law (n+2)).map (wholeGroupData M P R n),
      let μ := squareFibre M P R n u
      let hs : MeasurePreserving (planes (n+1) S) μ (μ.map (planes (n+1) S)) :=
        ⟨measurable_planes _ _, rfl⟩
      let ht : MeasurePreserving (planes (n+1) D) μ (μ.map (planes (n+1) D)) :=
        ⟨measurable_planes _ _, rfl⟩
      ∃ (ha : MeasurePreserving (columnRestrict M A S n) (μ.map (planes (n+1) S)) (cellLaw M A S n u.1.1))
        (hb : MeasurePreserving (columnRestrict M B S n) (μ.map (planes (n+1) S)) (cellLaw M B S n u.1.1))
        (hc : MeasurePreserving (columnRestrict M A D n) (μ.map (planes (n+1) D)) (cellLaw M A D n u.1.1))
        (hd : MeasurePreserving (columnRestrict M B D n) (μ.map (planes (n+1) D)) (cellLaw M B D n u.1.1)),
        let F := JoiningOperator.operator (ha.comp hs) (hc.comp ht)
        let G := JoiningOperator.operator (hb.comp hs) (hd.comp ht)
        let K := JoiningOperator.operator ha hb
        let N := JoiningOperator.operator hc hd
        F ∘L N = K ∘L G ∧ F.adjoint ∘L K = N ∘L G.adjoint := by
  have hSD' : Disjoint (R ∪ S) D := Finset.disjoint_union_left.mpr ⟨hRD,hSD⟩
  have hDS' : Disjoint (R ∪ D) S := Finset.disjoint_union_left.mpr ⟨hRS,hSD.symm⟩
  have hcover' : (R ∪ D) ∪ S = Finset.univ := by simpa only [Finset.union_right_comm] using hcover
  have hproperRS : R ∪ S ≠ Finset.univ := by
    intro h
    obtain ⟨d,hd⟩ := hD
    exact Finset.disjoint_left.mp hSD' (h ▸ Finset.mem_univ d) hd
  have hproperRD : R ∪ D ≠ Finset.univ := by
    intro h
    obtain ⟨s,hs⟩ := hS
    exact Finset.disjoint_left.mp hDS' (h ▸ Finset.mem_univ s) hs
  filter_upwards [cellMarginal_fibre M hM P A R S hP hPA hproperA hRS hproperRS n,
    cellMarginal_fibre M hM P B R S hP hPB hproperB hRS hproperRS n,
    cellMarginal_fibre M hM P A R D hP hPA hproperA hRD hproperRD n,
    cellMarginal_fibre M hM P B R D hP hPB hproperB hRD hproperRD n,
    splitRowScreen_fibre M hM P A R S D hP hPA hcardA hproperA hSD' hcover hD n,
    splitRowScreen_fibre M hM P B R S D hP hPB hcardB hproperB hSD' hcover hD n,
    splitRowScreen_fibre M hM P A R D S hP hPA hcardA hproperA hDS' hcover' hS n,
    splitRowScreen_fibre M hM P B R D S hP hPB hcardB hproperB hDS' hcover' hS n]
    with u ha hb hc hd hac hbd hca hdb
  refine ⟨ha,hb,hc,hd,?_⟩
  apply JoiningOperator.square_rectangle
    (hs := ⟨measurable_planes _ _, rfl⟩) (ht := ⟨measurable_planes _ _, rfl⟩)
    (κac := (splitRowKernel M P A R S D n).sectR u)
    (κbd := (splitRowKernel M P B R S D n).sectR u)
    (κca := (splitRowKernel M P A R D S n).sectR u)
    (κdb := (splitRowKernel M P B R D S n).sectR u)
  · simpa only [columnRestrict_planes] using hac
  · simpa only [columnRestrict_planes] using hbd
  · simpa only [columnRestrict_planes] using hca
  · simpa only [columnRestrict_planes] using hdb
end

universe u
variable {I : Type u} [Fintype I] [retained7 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rowPair_conditional (hM : M.IsSaturated) (P A R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hCD : Disjoint R (S∪D))
    (hcover : R ∪ (S∪D) = Finset.univ) (hSD : (S∪D).Nonempty) (n : ℕ) :
    HasCondDistrib (fun y => (cells M A S n y,cells M A D n y)) (wholeGroupData M P R n)
      ((rowPairKernel M A R S D n).comap (groupSelect M P A R n)
        (measurable_groupSelect M P A R n)) (M.law (n+2)) := by
  let f : (↥(S∪D) → A → Arr I M.Y n) → (S → A → Arr I M.Y n) × (D → A → Arr I M.Y n) :=
    fun y => (tupleSelect S (S∪D) Finset.subset_union_left y,
      tupleSelect D (S∪D) Finset.subset_union_right y)
  have hf : Measurable f := by fun_prop
  have h := (fullGroupedLocality M hM P A R (S∪D) hP hPA hcard hproper hCD hcover hSD n).comp_left hf
  rw [← Kernel.comap_map_comm _ _ hf] at h
  have : IsMarkovKernel ((condDistrib (cells M A (S∪D) n) (groupData M A R n) (M.law (n+2))).map f) :=
    Kernel.IsMarkovKernel.map _ hf
  have h' := ConditionalScreens.canonical_screen (measurable_wholeGroupData M P R n)
    (groupSelect M P A R n) (measurable_groupSelect M P A R n) h
  rw [groupSelect_observation] at h'
  exact h'

omit [DecidableEq I] in
lemma parameterEquiv_plane (P : Finset I) (n : ℕ) (j : I) (v : ParentData M P n) :
    parameterEquiv M P n (plane n (Fin.last n) j ((parameterEquiv M P (n+1)).symm v)) =
      (plane (n+1) (Fin.last (n+1)) j v.1,
        fun p : P => plane n (Fin.last n) j (v.2 p)) := by
  apply Prod.ext
  · funext w
    simp [parameterEquiv, plane, Fin.insertNth_last', cons_snoc]
  · rfl

include retained7 in
lemma columnKernel_eq_posterior (P : Finset I) (n : ℕ) (j : I) (v : ParentData M P n) :
    columnKernel M P n j v = posterior M P n
      (plane (n+1) (Fin.last (n+1)) j v.1,
        fun p : P => plane n (Fin.last n) j (v.2 p)) := by
  let _ := retained7
  simp only [columnKernel,Kernel.comap_apply,Function.comp_apply,
    Kernel.map_apply _ (roll n).symm.measurable,ownPosterior, Kernel.map_apply _ (roll n).measurable]
  rw [Measure.map_map (roll n).symm.measurable (roll n).measurable,
    MeasurableEquiv.symm_comp_self,Measure.map_id,parameterEquiv_plane]

lemma columns_group_screen (hM : M.IsSaturated) (P R S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hRS : Disjoint R S)
    (hproper : R ∪ S ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (planes (n+1) S) (wholeGroupData M P R n)
      ((columnGroupKernel M P S n).comap (columnOwnData M P R S n)
        (measurable_columnOwnData M P R S n)) (M.law (n+2)) := by
  have h := ConditionalReveal.disjoint_families (M.law (n+2)) (parentData M P n)
    (fun j => plane (n+1) (Fin.last (n+1)) j) (columnKernel M P n)
    Finset.subset_union_left Finset.subset_union_right hRS
    (columns_with_parents M hM P hP n (R∪S) hproper)
  have he : (columnGroupKernel M P S n).comap (columnOwnData M P R S n)
      (measurable_columnOwnData M P R S n) =
      (FiniteKernel.pi (fun j : S => columnKernel M P n j)).prodMkRight (R → Arr I M.Y (n+1)) := by
    ext v : 1
    change Measure.pi (fun j : S => posterior M P n _) =
      Measure.pi (fun j : S => columnKernel M P n j v.1)
    congr 1
    funext j
    exact (columnKernel_eq_posterior M P n j v.1).symm
  rw [he]
  exact h

end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace

section

variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
  (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)

lemma family_eq (u : U) (hx : MeasurePreserving Prod.fst (κ u) ν)
    (hy : MeasurePreserving Prod.snd (κ u) ρ) : family κ ν ρ u = operator hx hy := by
  classical
  unfold family
  split_ifs with h
  · rfl
  · exact (h ⟨hx, hy⟩).elim

end


lemma family_eq_of_joint {Ω U A B : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} {ν : Measure A} {ρ : Measure B} {a : Ω → A} {b : Ω → B}
    (κ : Kernel U (A × B)) (u : U)
    (hab : MeasurePreserving (fun ω => (a ω, b ω)) μ (κ u))
    (ha : MeasurePreserving Prod.fst (κ u) ν) (hb : MeasurePreserving Prod.snd (κ u) ρ) :
    family κ ν ρ u = operator (ha.comp hab) (hb.comp hab) := by
  rw [family_eq κ ν ρ u ha hb]
  exact (operator_pullback hab ha hb).symm

end JoiningOperator

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma columnPairRestrict_planes (A B S : Finset I) (n : ℕ) :
    (fun y => (columnRestrict M A S n y,columnRestrict M B S n y)) ∘ planes (n+1) S =
      fun y => (cells M A S n y,cells M B S n y) := by
  funext y
  exact Prod.ext (congrFun (columnRestrict_planes M A S n) y)
    (congrFun (columnRestrict_planes M B S n) y)

lemma columnPair_conditional (hM : M.IsSaturated) (P A B R S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hRS : Disjoint R S)
    (hproper : R ∪ S ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => (cells M A S n y,cells M B S n y)) (wholeGroupData M P R n)
      ((columnPairKernel M P A B S n).comap (columnOwnData M P R S n)
        (measurable_columnOwnData M P R S n)) (M.law (n+2)) := by
  have h := (columns_group_screen M hM P R S hP hRS hproper n).comp_left
    ((measurable_columnRestrict M A S n).prodMk (measurable_columnRestrict M B S n))
  rw [← Kernel.comap_map_comm _ _ (by fun_prop)] at h
  simpa only [columnPairKernel,columnPairRestrict_planes] using h

omit [DecidableEq I] in
lemma pair_fst_push {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} {ρ : Measure (A × B)} {ν : Measure A} {a : Ω → A} {b : Ω → B}
    (hab : MeasurePreserving (fun ω => (a ω,b ω)) μ ρ) (ha : MeasurePreserving a μ ν) :
    MeasurePreserving Prod.fst ρ ν := by
  refine ⟨measurable_fst,?_⟩
  rw [← hab.map_eq,Measure.map_map measurable_fst hab.measurable]
  exact ha.map_eq

omit [DecidableEq I] in
lemma pair_snd_push {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} {ρ : Measure (A × B)} {ν : Measure B} {a : Ω → A} {b : Ω → B}
    (hab : MeasurePreserving (fun ω => (a ω,b ω)) μ ρ) (hb : MeasurePreserving b μ ν) :
    MeasurePreserving Prod.snd ρ ν := by
  refine ⟨measurable_snd,?_⟩
  rw [← hab.map_eq,Measure.map_map measurable_snd hab.measurable]
  exact hb.map_eq

theorem grouped_family_rectangle (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A) (hPB : Disjoint P B)
    (hcardA : P.card + A.card + 1 ≤ Fintype.card I)
    (hcardB : P.card + B.card + 1 ≤ Fintype.card I)
    (hproperA : P ∪ A ≠ Finset.univ) (hproperB : P ∪ B ≠ Finset.univ)
    (hRS : Disjoint R S) (hRD : Disjoint R D) (hSD : Disjoint S D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hS : S.Nonempty) (hD : D.Nonempty) (n : ℕ) :
    ∀ᵐ u ∂(M.law (n+2)).map (wholeGroupData M P R n),
      let F := rowEdge M A R S D n u.1.1 (groupSelect M P A R n u)
      let G := rowEdge M B R S D n u.1.1 (groupSelect M P B R n u)
      let K := columnEdge M P A B S n u.1.1 (columnOwnData M P R S n u)
      let N := columnEdge M P A B D n u.1.1 (columnOwnData M P R D n u)
      JoiningOperator.IsRectangle F G K N := by
  have hRSD : Disjoint R (S∪D) := Finset.disjoint_union_right.mpr ⟨hRS,hRD⟩
  have hcover' : R ∪ (S∪D) = Finset.univ := by simpa only [Finset.union_assoc] using hcover
  have hproperRS : R ∪ S ≠ Finset.univ := by
    intro h
    obtain ⟨d,hd⟩ := hD
    exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨hRD,hSD⟩) (h ▸ Finset.mem_univ d) hd
  have hproperRD : R ∪ D ≠ Finset.univ := by
    intro h
    obtain ⟨s,hs⟩ := hS
    exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨hRS,hSD.symm⟩) (h ▸ Finset.mem_univ s) hs
  have hη : HasCondDistrib id (wholeGroupData M P R n) (squareFibre M P R n) (M.law (n+2)) :=
    ⟨(by fun_prop), (compProd_map_condDistrib (μ := M.law (n+2)) measurable_id.aemeasurable).symm⟩
  have hF := ConditionalFibres.marginal ((measurable_cells M A S n).prodMk (measurable_cells M A D n)) hη
    (rowPair_conditional M hM P A R S D hP hPA hcardA hproperA hRSD hcover' (hS.mono Finset.subset_union_left) n)
  have hG := ConditionalFibres.marginal ((measurable_cells M B S n).prodMk (measurable_cells M B D n)) hη
    (rowPair_conditional M hM P B R S D hP hPB hcardB hproperB hRSD hcover' (hS.mono Finset.subset_union_left) n)
  have hK := ConditionalFibres.marginal ((measurable_cells M A S n).prodMk (measurable_cells M B S n)) hη
    (columnPair_conditional M hM P A B R S hP hRS hproperRS n)
  have hN := ConditionalFibres.marginal ((measurable_cells M A D n).prodMk (measurable_cells M B D n)) hη
    (columnPair_conditional M hM P A B R D hP hRD hproperRD n)
  filter_upwards [grouped_rectangle M hM P A B R S D hP hPA hPB hcardA hcardB hproperA hproperB
    hRS hRD hSD hcover hS hD n,hF,hG,hK,hN] with u hu hf hg hk hn
  obtain ⟨ha,hb,hc,hd,hr⟩ := hu
  let hs : MeasurePreserving (planes (n+1) S) (squareFibre M P R n u)
      ((squareFibre M P R n u).map (planes (n+1) S)) := ⟨measurable_planes _ _,rfl⟩
  let ht : MeasurePreserving (planes (n+1) D) (squareFibre M P R n u)
      ((squareFibre M P R n u).map (planes (n+1) D)) := ⟨measurable_planes _ _,rfl⟩
  have hks : MeasurePreserving (fun y => (columnRestrict M A S n y,columnRestrict M B S n y))
      ((squareFibre M P R n u).map (planes (n+1) S))
      (columnPairKernel M P A B S n (columnOwnData M P R S n u)) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_map (by fun_prop) (measurable_planes _ _)]
    rw [columnPairRestrict_planes]
    exact hk.map_eq
  have hnt : MeasurePreserving (fun y => (columnRestrict M A D n y,columnRestrict M B D n y))
      ((squareFibre M P R n u).map (planes (n+1) D))
      (columnPairKernel M P A B D n (columnOwnData M P R D n u)) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_map (by fun_prop) (measurable_planes _ _)]
    rw [columnPairRestrict_planes]
    exact hn.map_eq
  simp only [← columnRestrict_planes M A S n, ← columnRestrict_planes M A D n] at hf
  simp only [← columnRestrict_planes M B S n, ← columnRestrict_planes M B D n] at hg
  dsimp only [rowEdge,columnEdge,JoiningOperator.IsRectangle]
  rw [JoiningOperator.family_eq_of_joint (rowPairKernel M A R S D n) (groupSelect M P A R n u) hf (pair_fst_push hf (ha.comp hs)) (pair_snd_push hf (hc.comp ht)),
    JoiningOperator.family_eq_of_joint (rowPairKernel M B R S D n) (groupSelect M P B R n u) hg (pair_fst_push hg (hb.comp hs)) (pair_snd_push hg (hd.comp ht)),
    JoiningOperator.family_eq_of_joint _ _ hks (pair_fst_push hks ha) (pair_snd_push hks hb),
    JoiningOperator.family_eq_of_joint _ _ hnt (pair_fst_push hnt hc) (pair_snd_push hnt hd)]
  exact hr
end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory
namespace ConditionalFibres
variable {Ω U X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → U}
  {η : Kernel U Ω} [IsMarkovKernel η]

lemma ae_ae (hη : HasCondDistrib id u η μ) {p : Ω → Prop} (hp : ∀ᵐ ω ∂μ, p ω) :
    ∀ᵐ a ∂μ.map u, ∀ᵐ ω ∂η a, p ω := by
  have hs : MeasurePreserving Prod.snd (μ.map u ⊗ₘ η) μ := by
    refine ⟨measurable_snd, ?_⟩
    rw [← hη.map_eq, AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hη.aemeasurable]
    exact Measure.map_id
  exact Measure.ae_ae_of_ae_compProd (hs.quasiMeasurePreserving.ae hp)

lemma parameter_fixed [StandardBorelSpace U] (hu : Measurable u)
    (hη : HasCondDistrib id u η μ) :
    ∀ᵐ a ∂μ.map u, ∀ᵐ ω ∂η a, u ω = a := by
  apply Measure.ae_ae_of_ae_compProd (p := fun q => u q.2 = q.1)
  rw [← hη.map_eq]
  exact (ae_map_iff hη.aemeasurable (measurableSet_eq_fun (hu.comp measurable_snd) measurable_fst)).mpr
    (Filter.Eventually.of_forall fun _ => rfl)

lemma indep_of_screen [StandardBorelSpace X] [StandardBorelSpace Y]
    {x : Ω → X} {y : Ω → Y} {α : Kernel U Y} [IsMarkovKernel α]
    (hx : Measurable x) (hy : Measurable y)
    (hη : HasCondDistrib id u η μ)
    (h : HasCondDistrib y (fun ω => (u ω,x ω)) (α.prodMkRight X) μ) :
    ∀ᵐ a ∂μ.map u, IndepFun x y (η a) := by
  filter_upwards [disintegrate hx hy hη h] with a ha
  have he : (α.prodMkRight X).sectR a = Kernel.const X (α a) := by
    ext x : 1
    rfl
  rw [he] at ha
  apply (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable).mpr
  rw [ha.map_eq, ha.hasLaw_of_const.map_eq, Measure.compProd_const]

lemma triple_product {x : Ω → X} {y : Ω → Y} {z : Ω → Z}
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (hxy : IndepFun x y μ) (hxyz : IndepFun (fun ω => (x ω,y ω)) z μ) :
    MeasurePreserving (fun ω => (x ω,y ω,z ω)) μ
      ((μ.map x).prod ((μ.map y).prod (μ.map z))) := by
  refine ⟨hx.prodMk (hy.prodMk hz),?_⟩
  have h := hxyz.map_prod_eq_prod_map_map (hx.prodMk hy).aemeasurable hz.aemeasurable
  rw [hxy.map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable] at h
  have h' := congrArg (fun ν => ν.map MeasurableEquiv.prodAssoc) h
  rw [Measure.map_map (by fun_prop) ((hx.prodMk hy).prodMk hz), Measure.prodAssoc_prod] at h'
  exact h'

end ConditionalFibres

namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rows_indep_fibre (hM : M.IsSaturated) (P A : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (parents M P (n+1)) (parents M A (n+1)) (M.ownKernel (n+2) e) := by
  have h := ConditionalReveal.disjoint_families (M.law (n+2)) (amap M.par (n+2))
    (fun a => plane (n+1) 0 a)
    (fun a => (M.ownKernel (n+1)).comap (plane (n+1) 0 a) (measurable_plane _ _ _))
    Finset.subset_union_left Finset.subset_union_right hPA
    (rows_conditional M hM (P∪A) hproper n)
  exact ConditionalFibres.indep_of_screen (measurable_parents M P _) (measurable_parents M A _)
    (M.ownKernel_conditional (n+2)) h

lemma columns_indep_fibre (S D : Finset I)
    (hSD : Disjoint S D) (hproper : S ∪ D ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (planes (n+1) S) (planes (n+1) D) (M.ownKernel (n+2) e) := by
  have h := ConditionalReveal.disjoint_families (M.law (n+2)) (amap M.par (n+2))
    (fun j => plane (n+1) (Fin.last (n+1)) j)
    (fun j => (M.ownKernel (n+1)).comap (plane (n+1) (Fin.last (n+1)) j) (measurable_plane _ _ _))
    Finset.subset_union_left Finset.subset_union_right hSD
    (M.planes_conditional (n+1) (S∪D) hproper)
  exact ConditionalFibres.indep_of_screen (measurable_planes _ _) (measurable_planes _ _)
    (M.ownKernel_conditional (n+2)) h

lemma cells_indep_rows_fibre (hM : M.IsSaturated) (P A S R : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (cells M P S n) (cells M A R n) (M.ownKernel (n+2) e) := by
  filter_upwards [rows_indep_fibre M hM P A hPA hproper n] with e he
  exact he.comp (measurable_rowRestrict M P S n) (measurable_rowRestrict M A R n)

lemma cells_indep_columns_fibre (P A S R : Finset I)
    (hSR : Disjoint S R) (hproper : S ∪ R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (cells M P S n) (cells M A R n) (M.ownKernel (n+2) e) := by
  filter_upwards [columns_indep_fibre M S R hSR hproper n] with e he
  simpa only [columnRestrict_planes] using
    he.comp (measurable_columnRestrict M P S n) (measurable_columnRestrict M A R n)

lemma cells_colpair_indep_row_fibre (hM : M.IsSaturated) (P A S D R : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (fun y => (cells M P S n y,cells M P D n y)) (cells M A R n)
        (M.ownKernel (n+2) e) := by
  filter_upwards [rows_indep_fibre M hM P A hPA hproper n] with e he
  exact he.comp ((measurable_rowRestrict M P S n).prodMk (measurable_rowRestrict M P D n))
    (measurable_rowRestrict M A R n)

lemma cells_rowpair_indep_column_fibre (A B P R S : Finset I)
    (hRS : Disjoint R S) (hproper : R ∪ S ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (fun y => (cells M A R n y,cells M B R n y)) (cells M P S n)
        (M.ownKernel (n+2) e) := by
  filter_upwards [columns_indep_fibre M R S hRS hproper n] with e he
  have h := he.comp ((measurable_columnRestrict M A R n).prodMk
    (measurable_columnRestrict M B R n)) (measurable_columnRestrict M P S n)
  simpa only [columnPairRestrict_planes,columnRestrict_planes] using h

theorem grouped_product_triples (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hPA : Disjoint P A) (hPB : Disjoint P B) (hAB : Disjoint A B)
    (hproperPA : P ∪ A ≠ Finset.univ) (hproperPB : P ∪ B ≠ Finset.univ)
    (hproperAB : A ∪ B ≠ Finset.univ)
    (hRS : Disjoint R S) (hRD : Disjoint R D) (hSD : Disjoint S D)
    (hproperRS : R ∪ S ≠ Finset.univ) (hproperRD : R ∪ D ≠ Finset.univ)
    (hproperSD : S ∪ D ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      let μ := M.ownKernel (n+2) e
      let x := cells M A R n
      let y := cells M B R n
      let c := cells M P S n
      let d := cells M P D n
      MeasurePreserving (fun ω => (c ω,d ω,x ω)) μ
        ((μ.map c).prod ((μ.map d).prod (μ.map x))) ∧
      MeasurePreserving (fun ω => (c ω,d ω,y ω)) μ
        ((μ.map c).prod ((μ.map d).prod (μ.map y))) ∧
      MeasurePreserving (fun ω => (x ω,y ω,c ω)) μ
        ((μ.map x).prod ((μ.map y).prod (μ.map c))) ∧
      MeasurePreserving (fun ω => (x ω,y ω,d ω)) μ
        ((μ.map x).prod ((μ.map y).prod (μ.map d))) := by
  filter_upwards [cells_colpair_indep_row_fibre M hM P A S D R hPA hproperPA n,
    cells_colpair_indep_row_fibre M hM P B S D R hPB hproperPB n,
    cells_rowpair_indep_column_fibre M A B P R S hRS hproperRS n,
    cells_rowpair_indep_column_fibre M A B P R D hRD hproperRD n,
    cells_indep_rows_fibre M hM A B R R hAB hproperAB n,
    cells_indep_columns_fibre M P P S D hSD hproperSD n] with e hxa hxb hcs hds hxy hcd
  exact ⟨ConditionalFibres.triple_product (by fun_prop) (by fun_prop) (by fun_prop) hcd hxa,
    ConditionalFibres.triple_product (by fun_prop) (by fun_prop) (by fun_prop) hcd hxb,
    ConditionalFibres.triple_product (by fun_prop) (by fun_prop) (by fun_prop) hxy hcs,
    ConditionalFibres.triple_product (by fun_prop) (by fun_prop) (by fun_prop) hxy hds⟩


theorem grouped_fibre_rectangle (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A) (hPB : Disjoint P B)
    (hcardA : P.card + A.card + 1 ≤ Fintype.card I)
    (hcardB : P.card + B.card + 1 ≤ Fintype.card I)
    (hproperA : P ∪ A ≠ Finset.univ) (hproperB : P ∪ B ≠ Finset.univ)
    (hRS : Disjoint R S) (hRD : Disjoint R D) (hSD : Disjoint S D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hS : S.Nonempty) (hD : D.Nonempty) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ y ∂M.ownKernel (n+2) e,
        JoiningOperator.IsRectangle
          (fibreRowEdge M A R S D n e (cells M A R n y))
          (fibreRowEdge M B R S D n e (cells M B R n y))
          (fibreColumnEdge M P A B S n e (cells M P S n y))
          (fibreColumnEdge M P A B D n e (cells M P D n y)) := by
  have h := ae_of_ae_map (measurable_wholeGroupData M P R n).aemeasurable
    (grouped_family_rectangle M hM P A B R S D hP hPA hPB hcardA hcardB hproperA hproperB
      hRS hRD hSD hcover hS hD n)
  filter_upwards [ConditionalFibres.ae_ae (M.ownKernel_conditional (n+2)) h,
    ConditionalFibres.parameter_fixed (measurable_amap M.measurable_par _) (M.ownKernel_conditional (n+2))]
    with e he hp
  filter_upwards [he,hp] with y hy hparam
  have ha := congrFun (groupSelect_observation M P A R n) y
  have hb := congrFun (groupSelect_observation M P B R n) y
  dsimp only [Function.comp_apply] at ha hb
  change JoiningOperator.IsRectangle
    (rowEdge M A R S D n (amap M.par (n+2) y) (groupSelect M P A R n (wholeGroupData M P R n y)))
    (rowEdge M B R S D n (amap M.par (n+2) y) (groupSelect M P B R n (wholeGroupData M P R n y)))
    (columnEdge M P A B S n (amap M.par (n+2) y) (columnOwnData M P R S n (wholeGroupData M P R n y)))
    (columnEdge M P A B D n (amap M.par (n+2) y) (columnOwnData M P R D n (wholeGroupData M P R n y))) at hy
  rw [ha,hb] at hy
  change JoiningOperator.IsRectangle
    (rowEdge M A R S D n (amap M.par (n+2) y) (amap M.par (n+2) y,cells M A R n y))
    (rowEdge M B R S D n (amap M.par (n+2) y) (amap M.par (n+2) y,cells M B R n y))
    (columnEdge M P A B S n (amap M.par (n+2) y) (amap M.par (n+2) y,cells M P S n y))
    (columnEdge M P A B D n (amap M.par (n+2) y) (amap M.par (n+2) y,cells M P D n y)) at hy
  rw [hparam] at hy
  exact hy

end ArrayObjects.Object.Rolled
end

section

open MeasureTheory Filter ContinuousLinearMap
open scoped InnerProductSpace Topology

section EssentialKernel
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem essentialKernel.ae_annihilate [SecondCountableTopology E]
    (μ : Measure X) (A : X → E →L[ℂ] H) :
    ∀ᵐ x ∂μ, ∀ v : essentialKernel μ A, A x v = 0 := by
  let K := essentialKernel μ A
  have h (n : ℕ) : ∀ᵐ x ∂μ, A x (TopologicalSpace.denseSeq K n) = 0 :=
    (TopologicalSpace.denseSeq K n).property
  filter_upwards [ae_all_iff.mpr h] with x hx
  have hh : (fun v : K => A x v) = (fun _ : K => (0 : H)) := by
    apply (TopologicalSpace.denseRange_denseSeq K).equalizer
      ((A x).continuous.comp continuous_subtype_val) continuous_const
    funext n
    exact hx n
  intro v
  exact congrFun hh v
end EssentialKernel

section EssentialRange
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

lemma essentialRange.ae_range_le [SecondCountableTopology H]
    (μ : Measure X) (F : X → E →L[ℂ] H) :
    ∀ᵐ x ∂μ, LinearMap.range (F x).toLinearMap ≤ essentialRange μ F := by
  filter_upwards [essentialKernel.ae_annihilate μ (fun x => (F x).adjoint)] with x hx
  rintro v ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  intro z hz
  change inner ℂ z (F x w) = 0
  rw [← adjoint_inner_left, hx ⟨z, hz⟩, inner_zero_left]

lemma essentialRange.le_of_ae_range (μ : Measure X) (F : X → E →L[ℂ] H)
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H))
    (hF : ∀ᵐ x ∂μ, LinearMap.range (F x).toLinearMap ≤ V) :
    essentialRange μ F ≤ V := by
  let : CompleteSpace V := hV.completeSpace_coe
  have h : Vᗮ ≤ essentialKernel μ (fun x => (F x).adjoint) := by
    intro v hv
    change ∀ᵐ x ∂μ, (F x).adjoint v = 0
    filter_upwards [hF] with x hx
    apply ext_inner_right ℂ
    intro w
    rw [inner_zero_left, adjoint_inner_left]
    exact V.inner_left_of_mem_orthogonal (hx ⟨w, rfl⟩) hv
  simpa only [essentialRange, Submodule.orthogonal_orthogonal] using Submodule.orthogonal_le h

omit [CompleteSpace J] in
lemma essentialRange.le_comap_of_ae_comp (μ : Measure X) (F : X → E →L[ℂ] H)
    (A : H →L[ℂ] J) (V : Submodule ℂ J) (hV : IsClosed (V : Set J))
    (hF : ∀ᵐ x ∂μ, LinearMap.range (A ∘L F x).toLinearMap ≤ V) :
    essentialRange μ F ≤ V.comap A.toLinearMap := by
  apply essentialRange.le_of_ae_range μ F _ (hV.preimage A.continuous)
  filter_upwards [hF] with x hx
  rintro v ⟨w, rfl⟩
  exact hx ⟨w, rfl⟩
end EssentialRange

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projection_intertwines (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : ∀ v ∈ V, A v ∈ W) (hAa : ∀ w ∈ W, A.adjoint w ∈ V) :
    W.starProjection ∘L A = A ∘L V.starProjection := by
  ext v
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hA _ (V.starProjection_apply_mem v)
  · change A v - A (V.starProjection v) ∈ Wᗮ
    rw [← map_sub]
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    rw [← adjoint_inner_left]
    exact V.inner_right_of_mem_orthogonal (hAa w hw) (V.sub_starProjection_mem_orthogonal v)

end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


lemma kernel_measurableSet_eq_const {U X : Type*} [MeasurableSpace U] [MeasurableSpace X]
    [StandardBorelSpace X] (κ : Kernel U X) [IsMarkovKernel κ]
    (ν : Measure X) [IsProbabilityMeasure ν] : MeasurableSet {u | κ u = ν} := by
  let e := embeddingReal X
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal X
  let η : Kernel U ℝ := κ.map e
  have : IsMarkovKernel η := Kernel.IsMarkovKernel.map κ he.measurable
  have : IsProbabilityMeasure (ν.map e) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) he.measurable.aemeasurable
  have eq_iff (u : U) : κ u = ν ↔ ∀ q : ℚ, η u (Set.Iic (q : ℝ)) = ν.map e (Set.Iic (q : ℝ)) := by
    constructor
    · intro h q
      simp [η, Kernel.map_apply κ he.measurable, h]
    · intro h
      apply he.map_injective
      have h' : η u = ν.map e := by
        apply ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat Real.isPiSystem_Iic_rat
        · intro S hS
          simp only [Set.iUnion_singleton_eq_range, Set.mem_range] at hS
          obtain ⟨q, rfl⟩ := hS
          exact h q
        · simp
      simpa [η, Kernel.map_apply κ he.measurable] using h'
  simp_rw [eq_iff]
  simp_rw [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun q => measurableSet_eq_fun
    (Kernel.measurable_coe η measurableSet_Iic) measurable_const)

lemma stronglyMeasurable_of_inner {U H : Type*} [MeasurableSpace U]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H] {f : U → H}
    (hf : ∀ h : H, StronglyMeasurable (fun u => inner ℂ h (f u))) :
    StronglyMeasurable f := by
  borelize H
  let e : H → ℕ → ℂ := fun h n => inner ℂ (TopologicalSpace.denseSeq H n) h
  have hec : Continuous e := by fun_prop
  have hei : Function.Injective e := by
    intro v w h
    have hh : (fun z : H => inner ℂ z v) = (fun z : H => inner ℂ z w) := by
      apply (TopologicalSpace.denseRange_denseSeq H).equalizer (by fun_prop) (by fun_prop)
      exact h
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_sub_right, congrFun hh (v - w), sub_self]
  exact ((hec.measurableEmbedding hei).measurable_comp_iff.mp
    (Measurable.of_eval (fun n => (hf (TopologicalSpace.denseSeq H n)).measurable))).stronglyMeasurable

variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y]
  (κ : Kernel U (X × Y)) [IsMarkovKernel κ] (ν : Measure X) (ρ : Measure Y)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

lemma family_good_measurable : MeasurableSet {u |
    MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ} := by
  have : IsMarkovKernel (κ.map Prod.fst) := Kernel.IsMarkovKernel.map κ measurable_fst
  have : IsMarkovKernel (κ.map Prod.snd) := Kernel.IsMarkovKernel.map κ measurable_snd
  convert (kernel_measurableSet_eq_const (κ.map Prod.fst) ν).inter
    (kernel_measurableSet_eq_const (κ.map Prod.snd) ρ) using 1
  all_goals try with_reducible_and_instances rfl
  ext u
  simp only [Set.mem_ofPred, Set.mem_inter_iff, Kernel.map_apply _ measurable_fst,
    Kernel.map_apply _ measurable_snd]
  exact and_congr ⟨fun h => h.map_eq, fun h => ⟨measurable_fst, h⟩⟩
    ⟨fun h => h.map_eq, fun h => ⟨measurable_snd, h⟩⟩

lemma family_inner_stronglyMeasurable (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    StronglyMeasurable (fun u => inner ℂ g (family κ ν ρ u h)) := by
  classical
  have hf : StronglyMeasurable (fun p : X × Y => inner ℂ (g p.1) (h p.2)) :=
    (g.1.stronglyMeasurable.comp_measurable measurable_fst).inner
      (h.1.stronglyMeasurable.comp_measurable measurable_snd)
  convert (hf.integral_kernel (κ := κ)).indicator (family_good_measurable κ ν ρ) using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  unfold family
  split_ifs with hu
  · rw [Set.indicator_of_mem (show u ∈ {u | MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ} from hu)]
    exact inner_operator hu.1 hu.2 g h
  · simp [hu]

lemma family_stronglyMeasurable [SecondCountableTopology (Lp ℂ 2 ν)] (h : Lp ℂ 2 ρ) :
    StronglyMeasurable (fun u => family κ ν ρ u h) :=
  stronglyMeasurable_of_inner (fun g => family_inner_stronglyMeasurable κ ν ρ g h)


end JoiningOperator

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

lemma VectorMeasurable.adjoint [SecondCountableTopology E]
    {F : X → E →L[ℂ] H} (hF : VectorMeasurable F) :
    VectorMeasurable (fun x => (F x).adjoint) := by
  intro w
  apply JoiningOperator.stronglyMeasurable_of_inner
  intro v
  simpa only [adjoint_inner_right] using (hF v).inner stronglyMeasurable_const

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.apply [SecondCountableTopology E]
    {F : X → E →L[ℂ] H} (hF : VectorMeasurable F) {v : X → E}
    (hv : StronglyMeasurable v) : StronglyMeasurable (fun x => F x (v x)) := by
  borelize E
  exact (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun x => (F x).continuous) hF).comp_measurable (hv.measurable.prodMk measurable_id)

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace J] in
lemma VectorMeasurable.comp [SecondCountableTopology H]
    {F : X → H →L[ℂ] J} {G : X → E →L[ℂ] H}
    (hF : VectorMeasurable F) (hG : VectorMeasurable G) :
    VectorMeasurable (fun x => F x ∘L G x) := fun v => hF.apply (hG v)

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.comap {Y : Type*} [MeasurableSpace Y]
    {F : X → E →L[ℂ] H} (hF : VectorMeasurable F) {f : Y → X}
    (hf : Measurable f) : VectorMeasurable (F ∘ f) :=
  fun v => (hF v).comp_measurable hf

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.measurableSet_eq [SecondCountableTopology E] [SecondCountableTopology H]
    {F G : X → E →L[ℂ] H} (hF : VectorMeasurable F) (hG : VectorMeasurable G) :
    MeasurableSet {x | F x = G x} := by
  borelize H
  have heq (x : X) : F x = G x ↔ ∀ n : ℕ,
      F x (TopologicalSpace.denseSeq E n) = G x (TopologicalSpace.denseSeq E n) := by
    constructor
    · intro h n; rw [h]
    · intro h
      apply DFunLike.ext'
      exact (TopologicalSpace.denseRange_denseSeq E).equalizer
        (F x).continuous (G x).continuous (funext h)
  simp_rw [heq, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_eq_fun
    (hF _).measurable (hG _).measurable)

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.measurableSet_range_le [SecondCountableTopology E]
    {F : X → E →L[ℂ] H} (hF : VectorMeasurable F)
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) :
    MeasurableSet {x | LinearMap.range (F x).toLinearMap ≤ V} := by
  borelize H
  have heq (x : X) : LinearMap.range (F x).toLinearMap ≤ V ↔
      ∀ n : ℕ, F x (TopologicalSpace.denseSeq E n) ∈ V := by
    constructor
    · intro h n; exact h ⟨_, rfl⟩
    · intro h
      have hall : ∀ v : E, F x v ∈ V := by
        intro v
        exact (TopologicalSpace.denseRange_denseSeq E).induction_on v
          (hV.preimage (F x).continuous) h
      rintro v ⟨w, rfl⟩
      exact hall w
  simp_rw [heq, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => (hF _).measurable hV.measurableSet)
end

namespace ArrayObjects.Object.Rolled
open scoped ENNReal
open MeasureTheory ProbabilityTheory
local instance instFactNeENNRealOfNatTop : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma cells_conditional (hM : M.IsSaturated) (A S : Finset I)
    (hA : A ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (cells M A S n) (amap M.par (n+2)) (groupMarginal M A S n) (M.law (n+2)) := by
  exact (rows_conditional M hM A hA n).comp_left (measurable_rowRestrict M A S n)

lemma cells_fibre_marginal (hM : M.IsSaturated) (A S : Finset I)
    (hA : A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      MeasurePreserving (cells M A S n) (M.ownKernel (n+2) e) (cellLaw M A S n e) :=
  ConditionalFibres.marginal (measurable_cells M A S n) (M.ownKernel_conditional (n+2))
    (cells_conditional M hM A S hA n)

omit [DecidableEq I] in
lemma fibreRowEdge_eq (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    fibreRowEdge M A R S D n e = JoiningOperator.family ((rowPairKernel M A R S D n).sectR e)
      (cellLaw M A S n e) (cellLaw M A D n e) := by
  ext x h
  rfl

omit [DecidableEq I] in
lemma fibreColumnEdge_eq (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    fibreColumnEdge M P A B S n e = JoiningOperator.family ((columnPairKernel M P A B S n).sectR e)
      (cellLaw M A S n e) (cellLaw M B S n e) := by
  ext x h
  rfl

omit [DecidableEq I] in
lemma fibreRowEdge_measurable (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    VectorMeasurable (fibreRowEdge M A R S D n e) := by
  rw [fibreRowEdge_eq]
  exact JoiningOperator.family_stronglyMeasurable _ _ _

omit [DecidableEq I] in
lemma fibreColumnEdge_measurable (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    VectorMeasurable (fibreColumnEdge M P A B S n e) := by
  rw [fibreColumnEdge_eq]
  exact JoiningOperator.family_stronglyMeasurable _ _ _

end ArrayObjects.Object.Rolled

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
section Propagate
variable {Z X Y E H J K : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma essentialRange.ae_intertwining (μZ : Measure Z) (μX : Measure X) (μY : Measure Y)
    [SFinite μZ] [SFinite μX] [SFinite μY]
    (A : Z → E →L[ℂ] H) (F : X → J →L[ℂ] H) (G : Y → K →L[ℂ] E)
    (h1 : ∀ᵐ p ∂μZ.prod μY,
      LinearMap.range (A p.1 ∘L G p.2).toLinearMap ≤ essentialRange μX F)
    (h2 : ∀ᵐ p ∂μZ.prod μX,
      LinearMap.range ((A p.1).adjoint ∘L F p.2).toLinearMap ≤ essentialRange μY G) :
    ∀ᵐ z ∂μZ, (essentialRange μX F).starProjection ∘L A z =
      A z ∘L (essentialRange μY G).starProjection := by
  filter_upwards [Measure.ae_ae_of_ae_prod h1, Measure.ae_ae_of_ae_prod h2] with z hz1 hz2
  apply projection_intertwines
  · intro v hv
    exact essentialRange.le_comap_of_ae_comp μY G (A z) _ (essentialRange.isClosed μX F) hz1 hv
  · intro w hw
    exact essentialRange.le_comap_of_ae_comp μX F (A z).adjoint _ (essentialRange.isClosed μY G) hz2 hw

lemma essentialRange.own_intertwines [SecondCountableTopology E] [SecondCountableTopology H]
    (μ : Measure Z) (F : Z → E →L[ℂ] H) :
    ∀ᵐ z ∂μ, (essentialRange μ F).starProjection ∘L F z =
      F z ∘L (essentialRange μ (fun z => (F z).adjoint)).starProjection := by
  filter_upwards [essentialRange.ae_range_le μ F,
    essentialRange.ae_range_le μ (fun z => (F z).adjoint)] with z hz hza
  apply projection_intertwines
  · intro v _; exact hz ⟨v, rfl⟩
  · intro w _; exact hza ⟨w, rfl⟩
end Propagate

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace E] [CompleteSpace H] in
lemma maps_of_intertwines (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : W.starProjection ∘L A = A ∘L V.starProjection) : ∀ v ∈ V, A v ∈ W := by
  intro v hv
  apply W.starProjection_eq_self_iff.mp
  have h := congrArg (fun B : E →L[ℂ] H => B v) hA
  simpa only [comp_apply, V.starProjection_eq_self_iff.mpr hv] using h

lemma adjoint_intertwines (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : W.starProjection ∘L A = A ∘L V.starProjection) :
    V.starProjection ∘L A.adjoint = A.adjoint ∘L W.starProjection := by
  have h := congrArg adjoint hA
  simpa only [adjoint_comp, (isSelfAdjoint_starProjection V).adjoint_eq,
    (isSelfAdjoint_starProjection W).adjoint_eq] using h.symm

lemma inf_intertwines (A : E →L[ℂ] H)
    (V₁ V₂ : Submodule ℂ E) (W₁ W₂ : Submodule ℂ H)
    [V₁.HasOrthogonalProjection] [V₂.HasOrthogonalProjection]
    [W₁.HasOrthogonalProjection] [W₂.HasOrthogonalProjection]
    [(V₁ ⊓ V₂).HasOrthogonalProjection] [(W₁ ⊓ W₂).HasOrthogonalProjection]
    (h1 : W₁.starProjection ∘L A = A ∘L V₁.starProjection)
    (h2 : W₂.starProjection ∘L A = A ∘L V₂.starProjection) :
    (W₁ ⊓ W₂).starProjection ∘L A = A ∘L (V₁ ⊓ V₂).starProjection := by
  apply projection_intertwines
  · intro v hv
    exact ⟨maps_of_intertwines A V₁ W₁ h1 v hv.1, maps_of_intertwines A V₂ W₂ h2 v hv.2⟩
  · intro w hw
    exact ⟨maps_of_intertwines A.adjoint W₁ V₁ (adjoint_intertwines A V₁ W₁ h1) w hw.1,
      maps_of_intertwines A.adjoint W₂ V₂ (adjoint_intertwines A V₂ W₂ h2) w hw.2⟩
end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma compress_adjoint (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [CompleteSpace V] [CompleteSpace W] :
    (compress A V W).adjoint = compress A.adjoint W V := by
  simp only [compress, adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, comp_assoc]

omit [CompleteSpace E] [CompleteSpace H] in
lemma compress_apply (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : W.starProjection ∘L A = A ∘L V.starProjection) (v : V) :
    (compress A V W v : H) = A v := by
  change W.starProjection (A v) = A v
  simpa only [comp_apply, V.starProjection_mem_subspace_eq_self] using
    congrArg (fun B : E →L[ℂ] H => B v) hA

omit [CompleteSpace E] [CompleteSpace H] in
lemma compress_onto (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : W.starProjection ∘L A = A ∘L V.starProjection) (v : E) :
    compress A V W (V.orthogonalProjectionOnto v) = W.orthogonalProjectionOnto (A v) := by
  change W.orthogonalProjectionOnto (A (V.starProjection v)) = _
  rw [← show W.starProjection (A v) = A (V.starProjection v) from
    congrArg (fun B : E →L[ℂ] H => B v) hA]
  exact Submodule.orthogonalProjectionOnto_starProjection_of_le le_rfl _

lemma compressed_total_range (μ : Measure X) (F : X → E →L[ℂ] H)
    (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hW : W ≤ essentialRange μ F)
    (hF : ∀ᵐ x ∂μ, W.starProjection ∘L F x = F x ∘L V.starProjection) :
    HasEssentialTotalRange μ (fun x => compress (F x) V W) := by
  intro C hC hCF
  have h : essentialRange μ F ≤ C.comap W.orthogonalProjectionOnto.toLinearMap := by
    apply essentialRange.le_of_ae_range μ F _ (hC.preimage W.orthogonalProjectionOnto.continuous)
    filter_upwards [hF, hCF] with x hx hcx
    rintro w ⟨v, rfl⟩
    change W.orthogonalProjectionOnto (F x v) ∈ C
    rw [← compress_onto (F x) V W hx v]
    exact hcx ⟨_, rfl⟩
  apply top_unique
  intro w _
  have hw := h (hW w.property)
  change W.orthogonalProjectionOnto (w : H) ∈ C at hw
  simpa only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using hw
end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

omit [MeasurableSpace D] [SFinite μD] in
lemma rectangle_column_intertwines
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hcy : MeasurePreserving (fun ω => (c ω, y ω)) μ (μC.prod μY))
    (hcx : MeasurePreserving (fun ω => (c ω, x ω)) μ (μC.prod μX))
    (hF : VectorMeasurable F) (hG : VectorMeasurable G) (hK : VectorMeasurable K)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    ∀ᵐ a ∂μC, (essentialRange μX F).starProjection ∘L K a =
      K a ∘L (essentialRange μY G).starProjection := by
  apply essentialRange.ae_intertwining μC μX μY K F G
  · have hp := ((hK.comap measurable_fst).comp (hG.comap measurable_snd)).measurableSet_range_le
      (essentialRange μX F) (essentialRange.isClosed μX F)
    rw [← hcy.map_eq]
    apply (ae_map_iff hcy.measurable.aemeasurable
      (show MeasurableSet {p : C × Y | LinearMap.range (K p.1 ∘L G p.2).toLinearMap ≤ essentialRange μX F} from hp)).mpr
    filter_upwards [h1, hx.quasiMeasurePreserving.ae (essentialRange.ae_range_le μX F)] with ω he hr
    rw [← he]
    rintro v ⟨w, rfl⟩
    exact hr ⟨N (d ω) w, rfl⟩
  · have hp := ((hK.adjoint.comap measurable_fst).comp (hF.comap measurable_snd)).measurableSet_range_le
      (essentialRange μY G) (essentialRange.isClosed μY G)
    rw [← hcx.map_eq]
    apply (ae_map_iff hcx.measurable.aemeasurable
      (show MeasurableSet {p : C × X | LinearMap.range ((K p.1).adjoint ∘L F p.2).toLinearMap ≤ essentialRange μY G} from hp)).mpr
    filter_upwards [h2, hy.quasiMeasurePreserving.ae (essentialRange.ae_range_le μY G)] with ω he hr
    have hea := congrArg adjoint he
    simp only [adjoint_comp, adjoint_adjoint] at hea
    rw [hea]
    rintro v ⟨w, rfl⟩
    exact hr ⟨(N (d ω)).adjoint w, rfl⟩

lemma rectangle_all_intertwines
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hcy : MeasurePreserving (fun ω => (c ω, y ω)) μ (μC.prod μY))
    (hcx : MeasurePreserving (fun ω => (c ω, x ω)) μ (μC.prod μX))
    (hdy : MeasurePreserving (fun ω => (d ω, y ω)) μ (μD.prod μY))
    (hdx : MeasurePreserving (fun ω => (d ω, x ω)) μ (μD.prod μX))
    (hF : VectorMeasurable F) (hG : VectorMeasurable G)
    (hK : VectorMeasurable K) (hN : VectorMeasurable N)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    (∀ᵐ a ∂μC, (essentialRange μX F).starProjection ∘L K a =
      K a ∘L (essentialRange μY G).starProjection) ∧
    (∀ᵐ a ∂μD, (essentialRange μX (fun a => (F a).adjoint)).starProjection ∘L N a =
      N a ∘L (essentialRange μY (fun a => (G a).adjoint)).starProjection) ∧
    (∀ᵐ a ∂μX, (essentialRange μC K).starProjection ∘L F a =
      F a ∘L (essentialRange μD N).starProjection) ∧
    (∀ᵐ a ∂μY, (essentialRange μC (fun a => (K a).adjoint)).starProjection ∘L G a =
      G a ∘L (essentialRange μD (fun a => (N a).adjoint)).starProjection) := by
  have h2a : ∀ᵐ ω ∂μ, (K (c ω)).adjoint ∘L F (x ω) =
      G (y ω) ∘L (N (d ω)).adjoint := by
    filter_upwards [h2] with ω hω
    simpa only [adjoint_comp, adjoint_adjoint] using congrArg adjoint hω
  refine ⟨rectangle_column_intertwines hx hy hcy hcx hF hG hK h1 h2, ?_, ?_, ?_⟩
  · apply rectangle_column_intertwines (F := fun a => (F a).adjoint)
      (G := fun a => (G a).adjoint) (K := N) (N := K) hx hy hdy hdx hF.adjoint hG.adjoint hN h2
    simpa only [adjoint_adjoint] using h1
  · apply rectangle_column_intertwines (F := K) (G := N) (K := F) (N := G) hc hd
      ((Measure.measurePreserving_swap (μ := μD) (ν := μX)).comp hdx)
      ((Measure.measurePreserving_swap (μ := μC) (ν := μX)).comp hcx) hK hN hF
      (h1.mono fun _ h => h.symm) h2a
  · apply rectangle_column_intertwines (F := fun a => (K a).adjoint)
      (G := fun a => (N a).adjoint) (K := G) (N := F) hc hd
      ((Measure.measurePreserving_swap (μ := μD) (ν := μY)).comp hdy)
      ((Measure.measurePreserving_swap (μ := μC) (ν := μY)).comp hcy) hK.adjoint hN.adjoint hG
      h2a (by simpa only [adjoint_adjoint] using h1.mono fun _ h => h.symm)
end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace J] in
lemma compress_comp (A : H →L[ℂ] J) (B : E →L[ℂ] H)
    (U : Submodule ℂ E) (V : Submodule ℂ H) (W : Submodule ℂ J)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hB : V.starProjection ∘L B = B ∘L U.starProjection) :
    compress A V W ∘L compress B U V = compress (A ∘L B) U W := by
  apply ContinuousLinearMap.ext
  intro u
  change W.orthogonalProjectionOnto (A (compress B U V u)) = _
  rw [compress_apply B U V hB]
  rfl

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.compress {F : X → E →L[ℂ] H} (hF : VectorMeasurable F)
    (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] :
    VectorMeasurable (fun x => compress (F x) V W) := by
  intro v
  exact W.orthogonalProjectionOnto.continuous.comp_stronglyMeasurable (hF v)

end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

local notation "V₁" => essentialRange μX F
local notation "V₂" => essentialRange μX (fun a => adjoint (F a))
local notation "V₃" => essentialRange μY G
local notation "V₄" => essentialRange μY (fun a => adjoint (G a))
local notation "W₁" => essentialRange μC K
local notation "W₂" => essentialRange μD N
local notation "W₃" => essentialRange μC (fun a => adjoint (K a))
local notation "W₄" => essentialRange μD (fun a => adjoint (N a))
local notation "D₁" => (V₁ ⊓ W₁)
local notation "D₂" => (V₂ ⊓ W₂)
local notation "D₃" => (V₃ ⊓ W₃)
local notation "D₄" => (V₄ ⊓ W₄)
local notation "FR" => (fun a => compress (F a) D₂ D₁)
local notation "GR" => (fun a => compress (G a) D₄ D₃)
local notation "KR" => (fun a => compress (K a) D₃ D₁)
local notation "NR" => (fun a => compress (N a) D₄ D₂)

lemma rectangle_active_intersections
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hcy : MeasurePreserving (fun ω => (c ω, y ω)) μ (μC.prod μY))
    (hcx : MeasurePreserving (fun ω => (c ω, x ω)) μ (μC.prod μX))
    (hdy : MeasurePreserving (fun ω => (d ω, y ω)) μ (μD.prod μY))
    (hdx : MeasurePreserving (fun ω => (d ω, x ω)) μ (μD.prod μX))
    (hF : VectorMeasurable F) (hG : VectorMeasurable G)
    (hK : VectorMeasurable K) (hN : VectorMeasurable N)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    (∀ᵐ a ∂μX, (D₁).starProjection ∘L F a = F a ∘L (D₂).starProjection) ∧
    (∀ᵐ a ∂μY, (D₃).starProjection ∘L G a = G a ∘L (D₄).starProjection) ∧
    (∀ᵐ a ∂μC, (D₁).starProjection ∘L K a = K a ∘L (D₃).starProjection) ∧
    (∀ᵐ a ∂μD, (D₂).starProjection ∘L N a = N a ∘L (D₄).starProjection) := by
  obtain ⟨hK', hN', hF', hG'⟩ := rectangle_all_intertwines hx hy hc hd hcy hcx hdy hdx
    hF hG hK hN h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hF', essentialRange.own_intertwines μX F] with a ha hb
    exact inf_intertwines (F a) V₂ W₂ V₁ W₁ hb ha
  · filter_upwards [hG', essentialRange.own_intertwines μY G] with a ha hb
    exact inf_intertwines (G a) V₄ W₄ V₃ W₃ hb ha
  · filter_upwards [hK', essentialRange.own_intertwines μC K] with a ha hb
    exact inf_intertwines (K a) V₃ W₃ V₁ W₁ ha hb
  · filter_upwards [hN', essentialRange.own_intertwines μD N] with a ha hb
    exact inf_intertwines (N a) V₄ W₄ V₂ W₂ ha hb

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_rectangle
    (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hiG : ∀ᵐ a ∂μY, (D₃).starProjection ∘L G a = G a ∘L (D₄).starProjection)
    (hiK : ∀ᵐ a ∂μC, (D₁).starProjection ∘L K a = K a ∘L (D₃).starProjection)
    (hiN : ∀ᵐ a ∂μD, (D₂).starProjection ∘L N a = N a ∘L (D₄).starProjection)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    (∀ᵐ ω ∂μ, FR (x ω) ∘L NR (d ω) = KR (c ω) ∘L GR (y ω)) ∧
    (∀ᵐ ω ∂μ, (FR (x ω)).adjoint ∘L KR (c ω) = NR (d ω) ∘L (GR (y ω)).adjoint) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hy.quasiMeasurePreserving.ae hiG, hd.quasiMeasurePreserving.ae hiN, h1]
      with ω hg hn he
    rw [compress_comp _ _ _ _ _ hn, compress_comp _ _ _ _ _ hg, he]
  · filter_upwards [hc.quasiMeasurePreserving.ae hiK, hy.quasiMeasurePreserving.ae hiG, h2]
      with ω hk hg he
    rw [compress_adjoint, compress_adjoint, compress_comp _ _ _ _ _ hk,
      compress_comp _ _ _ _ _ (adjoint_intertwines _ _ _ hg), he]

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_total_F
    (hiF : ∀ᵐ a ∂μX, (D₁).starProjection ∘L F a = F a ∘L (D₂).starProjection) :
    HasEssentialTotalRange μX FR ∧ HasEssentialTotalRange μX (fun a => (FR a).adjoint) := by
  refine ⟨compressed_total_range μX F D₂ D₁ inf_le_left hiF, ?_⟩
  simpa only [compress_adjoint] using
    (compressed_total_range μX (fun a => adjoint (F a)) D₁ D₂ inf_le_left
      (hiF.mono fun a h => adjoint_intertwines (F a) D₂ D₁ h))

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_total_G
    (hi : ∀ᵐ a ∂μY, (D₃).starProjection ∘L G a = G a ∘L (D₄).starProjection) :
    HasEssentialTotalRange μY GR ∧ HasEssentialTotalRange μY (fun a => (GR a).adjoint) := by
  refine ⟨compressed_total_range μY G D₄ D₃ inf_le_left hi, ?_⟩
  simpa only [compress_adjoint] using
    (compressed_total_range μY (fun a => (G a).adjoint) D₃ D₄ inf_le_left
      (hi.mono fun a h => adjoint_intertwines (G a) D₄ D₃ h))

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_total_K
    (hi : ∀ᵐ a ∂μC, (D₁).starProjection ∘L K a = K a ∘L (D₃).starProjection) :
    HasEssentialTotalRange μC KR ∧ HasEssentialTotalRange μC (fun a => (KR a).adjoint) := by
  refine ⟨compressed_total_range μC K D₃ D₁ inf_le_right hi, ?_⟩
  simpa only [compress_adjoint] using
    (compressed_total_range μC (fun a => (K a).adjoint) D₁ D₃ inf_le_right
      (hi.mono fun a h => adjoint_intertwines (K a) D₃ D₁ h))

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_total_N
    (hi : ∀ᵐ a ∂μD, (D₂).starProjection ∘L N a = N a ∘L (D₄).starProjection) :
    HasEssentialTotalRange μD NR ∧ HasEssentialTotalRange μD (fun a => (NR a).adjoint) := by
  refine ⟨compressed_total_range μD N D₄ D₂ inf_le_right hi, ?_⟩
  simpa only [compress_adjoint] using
    (compressed_total_range μD (fun a => (N a).adjoint) D₂ D₄ inf_le_right
      (hi.mono fun a h => adjoint_intertwines (N a) D₄ D₂ h))

end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
section Descent
variable {Ω X E H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [SecondCountableTopology E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SecondCountableTopology H]
  {μ : Measure Ω} {ν : Measure X} {f : Ω → X} {A B : X → E →L[ℂ] H}
lemma VectorMeasurable.ae_eq_of_map (hf : MeasurePreserving f μ ν)
    (hA : VectorMeasurable A) (hB : VectorMeasurable B)
    (h : ∀ᵐ ω ∂μ, A (f ω) = B (f ω)) : A =ᵐ[ν] B := by
  rw [← hf.map_eq]
  exact (ae_map_iff hf.measurable.aemeasurable (hA.measurableSet_eq hB)).mpr h
end Descent

variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

lemma fixed_squares_of_rectangle
    (hcxd : MeasurePreserving (fun ω => (c ω, x ω, d ω)) μ (μC.prod (μX.prod μD)))
    (hcyd : MeasurePreserving (fun ω => (c ω, y ω, d ω)) μ (μC.prod (μY.prod μD)))
    (hxdy : MeasurePreserving (fun ω => (x ω, d ω, y ω)) μ (μX.prod (μD.prod μY)))
    (hxcy : MeasurePreserving (fun ω => (x ω, c ω, y ω)) μ (μX.prod (μC.prod μY)))
    (hFm : VectorMeasurable F) (hGm : VectorMeasurable G)
    (hKm : VectorMeasurable K) (hNm : VectorMeasurable N)
    (hF : HasEssentialTotalRange μX F)
    (hFa : HasEssentialTotalRange μX fun a => (F a).adjoint)
    (hG : HasEssentialTotalRange μY G)
    (hGa : HasEssentialTotalRange μY fun a => (G a).adjoint)
    (hK : HasEssentialTotalRange μC K)
    (hKa : HasEssentialTotalRange μC fun a => (K a).adjoint)
    (hN : HasEssentialTotalRange μD N)
    (hNa : HasEssentialTotalRange μD fun a => (N a).adjoint)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    HasFixedInjectiveSquares μX F ∧ HasFixedInjectiveSquares μY G ∧
      HasFixedInjectiveSquares μC K ∧ HasFixedInjectiveSquares μD N := by
  have hs := (h1.and h2).mono (fun ω h => rectangle_square_identities
    (F (x ω)) (G (y ω)) (K (c ω)) (N (d ω)) h.1 h.2)
  apply fixed_squares_of_product_identities μX μY μC μD F G K N hF hFa hG hGa hK hKa hN hNa
  · apply VectorMeasurable.ae_eq_of_map hcxd
      (((hKm.comp hKm.adjoint).comap measurable_fst).comp
        (hFm.comap measurable_snd.fst))
      ((hFm.comap measurable_snd.fst).comp
        ((hNm.comp hNm.adjoint).comap measurable_snd.snd))
    exact hs.mono fun _ h => h.1
  · apply VectorMeasurable.ae_eq_of_map hcyd
      (((hKm.adjoint.comp hKm).comap measurable_fst).comp
        (hGm.comap measurable_snd.fst))
      ((hGm.comap measurable_snd.fst).comp
        ((hNm.adjoint.comp hNm).comap measurable_snd.snd))
    exact hs.mono fun _ h => h.2.1
  · apply VectorMeasurable.ae_eq_of_map hxdy
      (((hFm.adjoint.comp hFm).comap measurable_fst).comp
        (hNm.comap measurable_snd.fst))
      ((hNm.comap measurable_snd.fst).comp
        ((hGm.adjoint.comp hGm).comap measurable_snd.snd))
    exact hs.mono fun _ h => h.2.2.1
  · apply VectorMeasurable.ae_eq_of_map hxcy
      (((hFm.comp hFm.adjoint).comap measurable_fst).comp
        (hKm.comap measurable_snd.fst))
      ((hKm.comap measurable_snd.fst).comp
        ((hGm.comp hGm.adjoint).comap measurable_snd.snd))
    exact hs.mono fun _ h => h.2.2.2
end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

local notation "V₁" => essentialRange μX F
local notation "V₂" => essentialRange μX (fun a => adjoint (F a))
local notation "V₃" => essentialRange μY G
local notation "V₄" => essentialRange μY (fun a => adjoint (G a))
local notation "W₁" => essentialRange μC K
local notation "W₂" => essentialRange μD N
local notation "W₃" => essentialRange μC (fun a => adjoint (K a))
local notation "W₄" => essentialRange μD (fun a => adjoint (N a))
local notation "D₁" => (V₁ ⊓ W₁)
local notation "D₂" => (V₂ ⊓ W₂)
local notation "D₃" => (V₃ ⊓ W₃)
local notation "D₄" => (V₄ ⊓ W₄)
local notation "FR" => (fun a => compress (F a) D₂ D₁)
local notation "GR" => (fun a => compress (G a) D₄ D₃)
local notation "KR" => (fun a => compress (K a) D₃ D₁)
local notation "NR" => (fun a => compress (N a) D₄ D₂)

theorem restricted_fixed_squares
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hcy : MeasurePreserving (fun ω => (c ω, y ω)) μ (μC.prod μY))
    (hcx : MeasurePreserving (fun ω => (c ω, x ω)) μ (μC.prod μX))
    (hdy : MeasurePreserving (fun ω => (d ω, y ω)) μ (μD.prod μY))
    (hdx : MeasurePreserving (fun ω => (d ω, x ω)) μ (μD.prod μX))
    (hcxd : MeasurePreserving (fun ω => (c ω, x ω, d ω)) μ (μC.prod (μX.prod μD)))
    (hcyd : MeasurePreserving (fun ω => (c ω, y ω, d ω)) μ (μC.prod (μY.prod μD)))
    (hxdy : MeasurePreserving (fun ω => (x ω, d ω, y ω)) μ (μX.prod (μD.prod μY)))
    (hxcy : MeasurePreserving (fun ω => (x ω, c ω, y ω)) μ (μX.prod (μC.prod μY)))
    (hF : VectorMeasurable F) (hG : VectorMeasurable G)
    (hK : VectorMeasurable K) (hN : VectorMeasurable N)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    HasFixedInjectiveSquares μX FR ∧ HasFixedInjectiveSquares μY GR ∧
      HasFixedInjectiveSquares μC KR ∧ HasFixedInjectiveSquares μD NR := by
  obtain ⟨hFi,hGi,hKi,hNi⟩ := rectangle_active_intersections hx hy hc hd hcy hcx hdy hdx
    hF hG hK hN h1 h2
  obtain ⟨hr1,hr2⟩ := restricted_rectangle hy hc hd hGi hKi hNi h1 h2
  obtain ⟨hFt,hFat⟩ := restricted_total_F hFi
  obtain ⟨hGt,hGat⟩ := restricted_total_G hGi
  obtain ⟨hKt,hKat⟩ := restricted_total_K hKi
  obtain ⟨hNt,hNat⟩ := restricted_total_N hNi
  exact fixed_squares_of_rectangle hcxd hcyd hxdy hxcy
    (hF.compress _ _) (hG.compress _ _) (hK.compress _ _) (hN.compress _ _)
    hFt hFat hGt hGat hKt hKat hNt hNat hr1 hr2
end

section

namespace TriplePartition
variable {I : Type*} [Fintype I] [DecidableEq I] (s : TriplePartition I)
lemma properPA : s.P ∪ s.A ≠ Finset.univ := by
  intro h
  obtain ⟨b,hb⟩ := s.nonemptyB
  exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨s.disjointPB,s.disjointAB⟩)
    (h ▸ Finset.mem_univ b) hb
lemma properPB : s.P ∪ s.B ≠ Finset.univ := by
  intro h
  obtain ⟨a,ha⟩ := s.nonemptyA
  exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨s.disjointPA,s.disjointAB.symm⟩)
    (h ▸ Finset.mem_univ a) ha
lemma properAB : s.A ∪ s.B ≠ Finset.univ := by
  intro h
  obtain ⟨p,hp⟩ := s.nonemptyP
  exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨s.disjointPA.symm,s.disjointPB.symm⟩)
    (h ▸ Finset.mem_univ p) hp
lemma properP : s.P ≠ Finset.univ := by
  intro h
  apply s.properPA
  simp [h]
lemma properA : s.A ≠ Finset.univ := by
  intro h
  apply s.properPA
  simp [h]
lemma properB : s.B ≠ Finset.univ := by
  intro h
  apply s.properPB
  simp [h]
lemma cardPA : s.P.card + s.A.card + 1 ≤ Fintype.card I := by
  have := s.card_eq
  have := Finset.card_pos.mpr s.nonemptyB
  omega
lemma cardPB : s.P.card + s.B.card + 1 ≤ Fintype.card I := by
  have := s.card_eq
  have := Finset.card_pos.mpr s.nonemptyA
  omega
end TriplePartition

open MeasureTheory
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  [SFinite ν] [SFinite ρ] [SFinite η]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}
lemma MeasurePreserving.triple_swap_right
    (h : MeasurePreserving (fun ω => (x ω,y ω,z ω)) μ (ν.prod (ρ.prod η))) :
    MeasurePreserving (fun ω => (x ω,z ω,y ω)) μ (ν.prod (η.prod ρ)) := by
  exact ((MeasurePreserving.id ν).prod (Measure.measurePreserving_swap (μ := ρ) (ν := η))).comp h
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
local instance instFactNeENNRealOfNatTop_1 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_restricted_fixed_squares_oai (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      let μX := cellLaw M rows.A cols.P n e
      let μY := cellLaw M rows.B cols.P n e
      let μC := cellLaw M rows.P cols.A n e
      let μD := cellLaw M rows.P cols.B n e
      let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
      let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
      let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
      let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
      HasFixedInjectiveSquares μX (rectangleRestrictF μX μC μD F K N) ∧
      HasFixedInjectiveSquares μY (rectangleRestrictG μY μC μD G K N) ∧
      HasFixedInjectiveSquares μC (rectangleRestrictK μX μY μC F G K) ∧
      HasFixedInjectiveSquares μD (rectangleRestrictN μX μY μD F G N) := by
  filter_upwards [grouped_fibre_rectangle M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.cardP rows.disjointPA rows.disjointPB rows.cardPA rows.cardPB rows.properPA rows.properPB
      cols.disjointPA cols.disjointPB cols.disjointAB cols.cover cols.nonemptyA cols.nonemptyB n,
    grouped_product_triples M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.disjointPA rows.disjointPB rows.disjointAB rows.properPA rows.properPB rows.properAB
      cols.disjointPA cols.disjointPB cols.disjointAB cols.properPA cols.properPB cols.properAB n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n,
    cells_indep_rows_fibre M hM rows.P rows.A cols.A cols.P rows.disjointPA rows.properPA n,
    cells_indep_rows_fibre M hM rows.P rows.B cols.A cols.P rows.disjointPB rows.properPB n,
    cells_indep_rows_fibre M hM rows.P rows.A cols.B cols.P rows.disjointPA rows.properPA n,
    cells_indep_rows_fibre M hM rows.P rows.B cols.B cols.P rows.disjointPB rows.properPB n]
      with e hr ht hx hy hc hd hcx hcy hdx hdy
  dsimp only at *
  rcases ht with ⟨hcdx,hcdy,hxyc,hxyd⟩
  simp only [hx.map_eq,hy.map_eq,hc.map_eq,hd.map_eq] at hcdx hcdy hxyc hxyd
  exact restricted_fixed_squares hx hy hc hd
    ⟨hc.measurable.prodMk hy.measurable, by
      rw [←hc.map_eq,←hy.map_eq]
      exact hcy.map_prod_eq_prod_map_map hc.measurable.aemeasurable hy.measurable.aemeasurable⟩
    ⟨hc.measurable.prodMk hx.measurable, by
      rw [←hc.map_eq,←hx.map_eq]
      exact hcx.map_prod_eq_prod_map_map hc.measurable.aemeasurable hx.measurable.aemeasurable⟩
    ⟨hd.measurable.prodMk hy.measurable, by
      rw [←hd.map_eq,←hy.map_eq]
      exact hdy.map_prod_eq_prod_map_map hd.measurable.aemeasurable hy.measurable.aemeasurable⟩
    ⟨hd.measurable.prodMk hx.measurable, by
      rw [←hd.map_eq,←hx.map_eq]
      exact hdx.map_prod_eq_prod_map_map hd.measurable.aemeasurable hx.measurable.aemeasurable⟩
    (Rokhlin.MeasurePreserving.triple_swap_right hcdx)
    (Rokhlin.MeasurePreserving.triple_swap_right hcdy)
    (Rokhlin.MeasurePreserving.triple_swap_right hxyd)
    (Rokhlin.MeasurePreserving.triple_swap_right hxyc)
    (fibreRowEdge_measurable M _ _ _ _ _ _) (fibreRowEdge_measurable M _ _ _ _ _ _)
    (fibreColumnEdge_measurable M _ _ _ _ _ _) (fibreColumnEdge_measurable M _ _ _ _ _ _)
    (hr.mono fun _ h => h.1) (hr.mono fun _ h => h.2)
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares_oai.{u} := @OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares_oai.{u}
