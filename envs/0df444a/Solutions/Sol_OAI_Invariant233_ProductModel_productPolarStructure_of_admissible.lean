-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.productPolarStructure_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:03.39691+00:00
-- url     : https://prove2.me/submissions/9eff72b4-a187-40d2-90fc-1083934c0e9f

import Mathlib
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Set.Countable
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_ProductModel_productPolarStructure_of_weightOrbitDiffuse

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ErgodicAtoms
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Function MeasureTheory

namespace Invariant233.ErgodicAtoms

variable {X : Type*} [m : MeasurableSpace X] {μ : Measure X}

theorem ae_eq_univ_of_measurable_atom
    [IsFiniteMeasure μ] {T : X → X}
    (hT : ∀ n : ℕ, 0 < n → Ergodic T^[n] μ)
    (m₀ : MeasurableSpace X) (hm₀ : m₀ ≤ m)
    (hT₀ : @Measurable X X m₀ m₀ T)
    {s : Set X} (hs₀ : @MeasurableSet X m₀ s) (hpos : μ s ≠ 0)
    (hatom : ∀ t : Set X, @MeasurableSet X m₀ t → t ⊆ s →
      μ t = 0 ∨ μ (s \ t) = 0) :
    s =ᵐ[μ] Set.univ := by
  let : MeasurableSpace X := m
  have hs : MeasurableSet s := hm₀ s hs₀
  have hT1 : MeasurePreserving T μ μ := by
    simpa using (hT 1 (by decide)).toMeasurePreserving
  obtain ⟨n, hn, hinter⟩ :=
    hT1.conservative.exists_gt_measure_inter_ne_zero hs.nullMeasurableSet hpos 0
  have hint₀ : @MeasurableSet X m₀ (s ∩ T^[n] ⁻¹' s) :=
    hs₀.inter ((hT₀.iterate n) hs₀)
  have hnull : μ (s \ (s ∩ T^[n] ⁻¹' s)) = 0 :=
    (hatom _ hint₀ inter_subset_left).resolve_left hinter
  have hle : s ≤ᵐ[μ] T^[n] ⁻¹' s := by
    apply ae_le_set.mpr
    simpa only [inter_comm s, sdiff_inter_self_eq_sdiff] using hnull
  rcases (hT n hn).ae_empty_or_univ_of_ae_le_preimage hs.nullMeasurableSet hle with h | h
  · exact False.elim (hpos (by simpa using measure_congr h))
  · exact h

theorem ae_empty_or_univ_of_conull_atom
    (m₀ : MeasurableSpace X)
    {s : Set X} (hs₀ : @MeasurableSet X m₀ s) (hfull : s =ᵐ[μ] Set.univ)
    (hatom : ∀ t : Set X, @MeasurableSet X m₀ t → t ⊆ s →
      μ t = 0 ∨ μ (s \ t) = 0)
    {t : Set X} (ht₀ : @MeasurableSet X m₀ t) :
    t =ᵐ[μ] (∅ : Set X) ∨ t =ᵐ[μ] Set.univ := by
  let : MeasurableSpace X := m
  have hinter : (s ∩ t : Set X) =ᵐ[μ] t :=
    inter_ae_eq_right_of_ae_eq_univ hfull
  rcases hatom (s ∩ t) (hs₀.inter ht₀) inter_subset_left with h | h
  · left
    apply ae_eq_empty.mpr
    rwa [measure_congr hinter] at h
  · right
    have hle : s ≤ᵐ[μ] t := by
      apply ae_le_set.mpr
      simpa only [inter_comm s, sdiff_inter_self_eq_sdiff] using h
    exact EventuallyLE.antisymm (subset_univ t).eventuallyLE (hfull.symm.le.trans hle)

theorem exists_nontrivial_measurable_subset
    [IsFiniteMeasure μ] {T : X → X}
    (hT : ∀ n : ℕ, 0 < n → Ergodic T^[n] μ)
    (m₀ : MeasurableSpace X) (hm₀ : m₀ ≤ m)
    (hT₀ : @Measurable X X m₀ m₀ T)
    (hnontrivial : ∃ t : Set X, @MeasurableSet X m₀ t ∧ μ t ≠ 0 ∧ μ tᶜ ≠ 0)
    {s : Set X} (hs₀ : @MeasurableSet X m₀ s) (hpos : μ s ≠ 0) :
    ∃ t : Set X, @MeasurableSet X m₀ t ∧ t ⊆ s ∧ μ t ≠ 0 ∧ μ (s \ t) ≠ 0 := by
  let : MeasurableSpace X := m
  by_contra hsplit
  have hatom : ∀ t : Set X, @MeasurableSet X m₀ t → t ⊆ s →
      μ t = 0 ∨ μ (s \ t) = 0 := by
    intro t ht hts
    by_cases hzero : μ t = 0
    · exact Or.inl hzero
    · right
      by_contra hcomp
      exact hsplit ⟨t, ht, hts, hzero, hcomp⟩
  have hfull := ae_eq_univ_of_measurable_atom hT m₀ hm₀ hT₀ hs₀ hpos hatom
  obtain ⟨t, ht, htpos, htcomp⟩ := hnontrivial
  rcases ae_empty_or_univ_of_conull_atom m₀ hs₀ hfull hatom ht with h | h
  · exact htpos (ae_eq_empty.mp h)
  · exact htcomp (ae_eq_univ.mp h)

end Invariant233.ErgodicAtoms

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ExtendedExponential
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.negLogCost_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal

namespace Invariant233

theorem extendedExpNeg_eq_zero_iff (a : ℝ≥0∞) :
    (EReal.exp (-(a : EReal))).toReal = 0 ↔ a = ∞ := by
  by_cases ha : a = ∞
  · simp [ha]
  · rw [extendedExpNeg_eq_exp_toReal a ha]
    simp [Real.exp_ne_zero, ha]

theorem negLogCost_extendedExpNeg (a : ℝ≥0∞) :
    negLogCost ((EReal.exp (-(a : EReal))).toReal) = a := by
  by_cases ha : a = ∞
  · simp [ha, negLogCost]
  · rw [extendedExpNeg_eq_exp_toReal a ha]
    simp only [negLogCost, Real.exp_ne_zero, ite_false, if_false,
      abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg]
    exact ENNReal.ofReal_toReal ha

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_MultiplicationPurePoint
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory

namespace Invariant233.MultiplicationPurePoint

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem topologicalClosure_iSup_eigenspace_eq_top_of_basis
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ E)
    (f : ι → X → ℂ) (hf : ∀ i, Measurable (f i))
    {C : Set ℂ} (hC : C.Countable)
    (hmem : ∀ i, ∀ᵐ x ∂μ, f i x ∈ C)
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hT : ∀ (v : Lp E 2 μ) i, ∀ᵐ x ∂μ,
      inner ℂ (b i) (T v x) = f i x * inner ℂ (b i) (v x)) :
    (⨆ y : C, Module.End.eigenspace T.toLinearMap y.val).topologicalClosure = ⊤ := by
  let : Countable C := hC.to_subtype
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  have hfiber (i : ι) (y : C) :
      ∀ᵐ x ∂μ, f i x = y.val → inner ℂ (b i) (v x) = 0 := by
    let s : Set X := f i ⁻¹' {y.val}
    have hs : MeasurableSet s := hf i (measurableSet_singleton _)
    let P : E →L[ℂ] E := InnerProductSpace.rankOne ℂ (b i) (b i)
    have hvp : MemLp (fun x => inner ℂ (b i) (v x) • b i) 2 μ := P.comp_memLp v
    have hvi : MemLp (s.indicator (fun x => inner ℂ (b i) (v x) • b i)) 2 μ :=
      hvp.indicator hs
    let w : Lp E 2 μ :=
      MemLp.toLp (s.indicator (fun x => inner ℂ (b i) (v x) • b i)) hvi
    have hw : (w : X → E) =ᵐ[μ] s.indicator (fun x => inner ℂ (b i) (v x) • b i) :=
      hvi.coeFn_toLp
    have heigen : w ∈ Module.End.eigenspace T.toLinearMap y.val := by
      rw [Module.End.mem_eigenspace_iff]
      apply Lp.ext
      have hTall : ∀ᵐ x ∂μ, ∀ j, inner ℂ (b j) (T w x) =
          f j x * inner ℂ (b j) (w x) := ae_all_iff.2 (hT w)
      filter_upwards [hTall, Lp.coeFn_smul y.val w, hw] with x hTx hsx hwx
      change (T w : X → E) x = (y.val • w : Lp E 2 μ) x
      rw [hsx]
      apply b.repr.injective
      ext j
      rw [b.repr_apply_apply, b.repr_apply_apply, hTx j]
      change f j x * inner ℂ (b j) (w x) = inner ℂ (b j) (y.val • w x)
      rw [inner_smul_right]
      by_cases hx : x ∈ s
      · have hwv : w x = inner ℂ (b i) (v x) • b i :=
          hwx.trans (Set.indicator_of_mem hx _)
        by_cases hji : j = i
        · subst j
          have hxy : f i x = y.val := hx
          rw [hxy]
        · rw [hwv, inner_smul_right, b.orthonormal.inner_eq_zero hji]
          simp only [mul_zero]
      · have hw0 : w x = 0 := hwx.trans (Set.indicator_of_notMem hx _)
        simp only [hw0, inner_zero_right, mul_zero]
    have hinner : inner ℂ w v = 0 :=
      (Submodule.mem_orthogonal _ _).1 hv w (Submodule.mem_iSup_of_mem y heigen)
    have hself : inner ℂ w w = inner ℂ w v := by
      rw [L2.inner_def, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hw] with x hwx
      by_cases hx : x ∈ s
      · have hwv : w x = inner ℂ (b i) (v x) • b i :=
          hwx.trans (Set.indicator_of_mem hx _)
        rw [hwv, inner_smul_left, inner_smul_right, inner_smul_left]
        rw [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
        norm_num
      · have hw0 : w x = 0 := hwx.trans (Set.indicator_of_notMem hx _)
        simp only [hw0, inner_zero_left]
    have hw_eq_zero : w = 0 := inner_self_eq_zero.1 (hself.trans hinner)
    have hwzero : (w : X → E) =ᵐ[μ] 0 := by
      rw [hw_eq_zero]
      exact Lp.coeFn_zero E 2 μ
    filter_upwards [hw, hwzero] with x hwx hz hx
    have hxs : x ∈ s := hx
    have hsmul : inner ℂ (b i) (v x) • b i = 0 :=
      (hwx.trans (Set.indicator_of_mem hxs _)).symm.trans hz
    have hnorm : b i ≠ 0 := by
      intro hzero
      have := b.orthonormal.norm_eq_one i
      simp only [hzero, norm_zero, zero_ne_one] at this
    exact (smul_eq_zero.1 hsmul).resolve_right hnorm
  have hall : ∀ᵐ x ∂μ, ∀ (i : ι) (y : C), f i x = y.val → inner ℂ (b i) (v x) = 0 :=
    ae_all_iff.2 (fun i => ae_all_iff.2 (hfiber i))
  have hmemall : ∀ᵐ x ∂μ, ∀ i, f i x ∈ C := ae_all_iff.2 hmem
  apply Lp.ext
  filter_upwards [hmemall, hall, Lp.coeFn_zero E 2 μ] with x hx hall hz
  rw [hz]
  apply b.repr.injective
  ext i
  rw [b.repr_apply_apply, b.repr_apply_apply]
  change inner ℂ (b i) (v x) = inner ℂ (b i) 0
  rw [inner_zero_right]
  exact hall i ⟨f i x, hx i⟩ rfl

end Invariant233.MultiplicationPurePoint

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_GeneratedVonNeumann
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Pointwise

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem vonNeumannGenerated_le (s : Set (H →L[ℂ] H)) (M : VonNeumannAlgebra H)
    (hs : s ⊆ M) : vonNeumannGenerated s ≤ M := by
  change (vonNeumannGenerated s : Set (H →L[ℂ] H)) ⊆ M
  rw [coe_vonNeumannGenerated, ← M.centralizer_centralizer]
  apply Set.centralizer_subset
  apply Set.centralizer_subset
  intro T hT
  rcases hT with hT | hT
  · exact hs hT
  · have hstar : star T ∈ s := hT
    simpa using (star_mem (hs hstar) : star (star T) ∈ M)

@[simp]
theorem vonNeumannGenerated_coe (M : VonNeumannAlgebra H) :
    vonNeumannGenerated (M : Set (H →L[ℂ] H)) = M := by
  apply le_antisymm
  · exact vonNeumannGenerated_le _ _ (Set.Subset.refl _)
  · exact subset_vonNeumannGenerated _

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_JointEigenprojection
attribute [-instance] _root_.OAI.Invariant233.AffiliatedTransport.instCompleteSpaceSubtypeMemSubmoduleComplexClosedImageOn _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in

theorem map_mem_jointEigenspace {D : ι → H →L[ℂ] H} {ev : ι → ℂ}
    {T : H →L[ℂ] H} (hT : ∀ i, Commute (D i) T)
    {x : H} (hx : x ∈ jointEigenspace D ev) : T x ∈ jointEigenspace D ev := by
  rw [mem_jointEigenspace] at hx ⊢
  intro i
  calc
    D i (T x) = T (D i x) := DFunLike.congr_fun (hT i).eq x
    _ = ev i • T x := by rw [hx i, map_smul]

theorem jointEigenprojection_mem_generated (D : ι → H →L[ℂ] H) (ev : ι → ℂ) :
    jointEigenprojection D ev ∈ vonNeumannGenerated (Set.range D) := by
  rw [VonNeumannAlgebra.IsStarProjection.mem_iff
    (isStarProjection_jointEigenprojection D ev)]
  intro T hT
  change (jointEigenspace D ev).starProjection.range ∈ Module.End.invtSubmodule T
  rw [Submodule.range_starProjection]
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  apply map_mem_jointEigenspace
  intro i
  exact ((mem_commutant_vonNeumannGenerated_iff _ T).mp hT (D i) ⟨i, rfl⟩).1

theorem exists_mul_jointEigenprojection_ne_zero {A : Type*}
    (D : ι → H →L[ℂ] H) (ev : A → ι → ℂ)
    (hdense : (⨆ a, jointEigenspace D (ev a)).topologicalClosure = ⊤)
    (p : H →L[ℂ] H) (hp : p ≠ 0) :
    ∃ a, p * jointEigenprojection D (ev a) ≠ 0 := by
  by_contra! h
  apply hp
  have hker : (⨆ a, jointEigenspace D (ev a)) ≤ p.ker := by
    apply iSup_le
    intro a x hx
    change p x = 0
    have hxq : jointEigenprojection D (ev a) x = x :=
      Submodule.starProjection_eq_self_iff.mpr hx
    have heq := DFunLike.congr_fun (h a) x
    simpa only [mul_apply_eq_comp, hxq, zero_apply] using heq
  have htop : (⊤ : Submodule ℂ H) ≤ p.ker := by
    rw [← hdense]
    exact Submodule.topologicalClosure_minimal _ hker p.isClosed_ker
  ext x
  exact htop (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H))

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteOrbitAtomic
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233

variable {X κ : Type*} [MeasurableSpace X] {μ : Measure X} [Countable κ]

theorem isSelfAdjoint_of_real_sequence_diagonal
    (g : κ → X → ℝ)
    (T : Lp (lp (fun _ : κ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : κ => ℂ) 2) 2 μ)
    (hT : ∀ (v : Lp (lp (fun _ : κ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, T v x k = (g k x : ℂ) * v x k) :
    IsSelfAdjoint T := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  change inner ℂ (T v) w = inner ℂ v (T w)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  have hv : ∀ᵐ x ∂μ, ∀ k, T v x k = (g k x : ℂ) * v x k := ae_all_iff.2 (hT v)
  have hw : ∀ᵐ x ∂μ, ∀ k, T w x k = (g k x : ℂ) * w x k := ae_all_iff.2 (hT w)
  filter_upwards [hv, hw] with x hvx hwx
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [hvx k, hwx k]
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

theorem commute_of_sequence_diagonal
    (g h : κ → X → ℂ)
    (S T : Lp (lp (fun _ : κ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : κ => ℂ) 2) 2 μ)
    (hS : ∀ (v : Lp (lp (fun _ : κ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, S v x k = g k x * v x k)
    (hT : ∀ (v : Lp (lp (fun _ : κ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, T v x k = h k x * v x k) : Commute S T := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  have hST : ∀ᵐ x ∂μ, ∀ k, S (T v) x k = g k x * T v x k := ae_all_iff.2 (hS (T v))
  have hTS : ∀ᵐ x ∂μ, ∀ k, T (S v) x k = h k x * S v x k := ae_all_iff.2 (hT (S v))
  have hSv : ∀ᵐ x ∂μ, ∀ k, S v x k = g k x * v x k := ae_all_iff.2 (hS v)
  have hTv : ∀ᵐ x ∂μ, ∀ k, T v x k = h k x * v x k := ae_all_iff.2 (hT v)
  filter_upwards [hST, hTS, hSv, hTv] with x hSTx hTSx hSvx hTvx
  apply lp.ext
  funext k
  change S (T v) x k = T (S v) x k
  rw [hSTx k, hTSx k, hSvx k, hTvx k]
  ring

theorem commute_of_mem_generated_selfAdjoint_family
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : I → H →L[ℂ] H) (hD : ∀ i, IsSelfAdjoint (D i))
    (hDD : ∀ i j, Commute (D i) (D j))
    {S T : H →L[ℂ] H} (hS : S ∈ vonNeumannGenerated (Set.range D))
    (hT : T ∈ vonNeumannGenerated (Set.range D)) : Commute S T := by
  have hle : vonNeumannGenerated (Set.range D) ≤
      (vonNeumannGenerated (Set.range D)).commutant := by
    apply vonNeumannGenerated_le
    rintro _ ⟨i, rfl⟩
    change D i ∈ (vonNeumannGenerated (Set.range D)).commutant
    rw [mem_commutant_vonNeumannGenerated_iff]
    rintro _ ⟨j, rfl⟩
    exact ⟨(hDD j i).eq, by simpa only [(hD j).star_eq] using (hDD j i).eq⟩
  exact VonNeumannAlgebra.mem_commutant_iff.mp (hle hT) S hS

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_OrbitMeasurable
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Function MeasureTheory
open scoped ENNReal

namespace Invariant233

variable {X Y : Type*} [m : MeasurableSpace X] [mY : MeasurableSpace Y]

omit m in

theorem measurable_orbit_observable (σ : Equiv.Perm X) (f : X → Y) (n : ℤ) :
    @Measurable X Y (orbitMeasurableSpace σ f) mY (fun x => f ((σ ^ n) x)) :=
  Measurable.of_comap_le (le_iSup (fun n : ℤ =>
    MeasurableSpace.comap (fun x => f ((σ ^ n) x)) mY) n)

omit m in

theorem measurable_base_observable (σ : Equiv.Perm X) (f : X → Y) :
    @Measurable X Y (orbitMeasurableSpace σ f) mY f := by
  simpa using measurable_orbit_observable σ f 0

theorem measurable_perm_zpow (σ : Equiv.Perm X)
    (hσ : Measurable σ) (hinv : Measurable σ.symm) (n : ℤ) :
    Measurable (σ ^ n) := by
  cases n with
  | ofNat n => simpa [Equiv.Perm.coe_pow] using hσ.iterate n
  | negSucc n =>
      simpa [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow] using hinv.iterate (n + 1)

theorem orbitMeasurableSpace_le (σ : Equiv.Perm X) {f : X → Y}
    (hσ : Measurable σ) (hinv : Measurable σ.symm) (hf : Measurable f) :
    orbitMeasurableSpace σ f ≤ m := by
  apply iSup_le
  intro n
  exact (hf.comp (measurable_perm_zpow σ hσ hinv n)).comap_le

omit m in

theorem measurable_perm_zpow_orbit (σ : Equiv.Perm X) (f : X → Y) (k : ℤ) :
    @Measurable X X (orbitMeasurableSpace σ f) (orbitMeasurableSpace σ f) ((σ ^ k : Equiv.Perm X) : X → X) := by
  apply Measurable.of_comap_le
  unfold orbitMeasurableSpace
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro n
  rw [MeasurableSpace.comap_comp]
  have heq : (fun x => f ((σ ^ n) x)) ∘ (σ ^ k) =
      fun x => f ((σ ^ (n + k)) x) := by
    funext x
    simp only [comp_apply, zpow_add, Equiv.Perm.mul_apply]
  rw [heq]
  exact le_iSup (fun n : ℤ =>
    MeasurableSpace.comap (fun x => f ((σ ^ n) x)) mY) (n + k)

theorem exists_nontrivial_set_of_not_ae_constant
    [Nonempty Y] [MeasurableSpace.CountablySeparated Y]
    {μ : Measure X} (m₀ : MeasurableSpace X) {f : X → Y}
    (hf : @Measurable X Y m₀ mY f)
    (hnonconstant : ¬ ∃ c : Y, f =ᵐ[μ] Function.const X c) :
    ∃ s : Set X, @MeasurableSet X m₀ s ∧ μ s ≠ 0 ∧ μ sᶜ ≠ 0 := by
  let : MeasurableSpace X := m
  by_contra hsets
  apply hnonconstant
  refine Filter.exists_eventuallyEq_const_of_forall_separating MeasurableSet ?_
  intro U hU
  have hpre : @MeasurableSet X m₀ (f ⁻¹' U) := hf hU
  by_cases hz : μ (f ⁻¹' U) = 0
  · right
    exact Filter.eventuallyEq_empty.mp (ae_eq_empty.mpr hz)
  · left
    have hc : μ (f ⁻¹' U)ᶜ = 0 := by
      by_contra hc
      exact hsets ⟨f ⁻¹' U, hpre, hz, hc⟩
    exact eventuallyEq_univ.mp (ae_eq_univ.mpr hc)

theorem orbitMeasurableSpace_atomless
    [Nonempty Y] [MeasurableSpace.CountablySeparated Y]
    {μ : Measure X} [IsFiniteMeasure μ]
    (σ : Equiv.Perm X) (hσ : Measurable σ) (hinv : Measurable σ.symm)
    (htotal : ∀ n : ℕ, 0 < n → Ergodic (σ : X → X)^[n] μ)
    {f : X → Y} (hf : Measurable f)
    (hnonconstant : ¬ ∃ c : Y, f =ᵐ[μ] Function.const X c)
    {s : Set X} (hs : @MeasurableSet X (orbitMeasurableSpace σ f) s)
    (hpos : μ s ≠ 0) :
    ∃ t : Set X, @MeasurableSet X (orbitMeasurableSpace σ f) t ∧
      t ⊆ s ∧ μ t ≠ 0 ∧ μ (s \ t) ≠ 0 := by
  apply ErgodicAtoms.exists_nontrivial_measurable_subset htotal
    (orbitMeasurableSpace σ f) (orbitMeasurableSpace_le σ hσ hinv hf) ?_ ?_ hs hpos
  · simpa using measurable_perm_zpow_orbit σ f 1
  · exact exists_nontrivial_set_of_not_ae_constant (orbitMeasurableSpace σ f)
      (measurable_base_observable σ f) hnonconstant

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_PolarStructure
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators

namespace InvariantProjection.PolarStructure

theorem countable_finite_drop_values {ι : Type*} [Countable ι] (c : ι → ℝ) :
    (Set.range (fun s : Finset ι => Real.exp (-(∑ i ∈ s, c i)))).Countable :=
  Set.countable_range _

theorem ae_countable_range_of_finite_drops {X ι : Type*} [MeasurableSpace X]
    [Countable ι] {μ : Measure X} (c : ι → ℝ) (f : X → ℝ)
    (hf : ∀ᵐ x ∂μ, ∃ s : Finset ι, f x = Real.exp (-(∑ i ∈ s, c i))) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ᵐ x ∂μ, f x ∈ S := by
  refine ⟨Set.range (fun s : Finset ι => Real.exp (-(∑ i ∈ s, c i))),
    countable_finite_drop_values c, ?_⟩
  filter_upwards [hf] with x hx
  obtain ⟨s, hs⟩ := hx
  exact ⟨s, hs.symm⟩

theorem mem_iff_of_eq_of_measurable_comap
    {X Y : Type*} [MeasurableSpace Y] (f : X → Y) {t : Set X}
    (ht : MeasurableSet[MeasurableSpace.comap f inferInstance] t)
    {x z : X} (hxz : f x = f z) : x ∈ t ↔ z ∈ t := by
  obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht
  change f x ∈ B ↔ f z ∈ B
  rw [hxz]

theorem fiber_is_atom_in_comap
    {X Y : Type*} [MeasurableSpace Y] (f : X → Y) (y : Y)
    {t : Set X} (ht : MeasurableSet[MeasurableSpace.comap f inferInstance] t)
    (htsub : t ⊆ f ⁻¹' {y}) : t = ∅ ∨ t = f ⁻¹' {y} := by
  by_cases ht0 : t = ∅
  · exact Or.inl ht0
  · right
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 ht0
    apply Set.Subset.antisymm htsub
    intro z hz
    have hxy : f x = y := htsub hx
    have hzy : f z = y := hz
    exact (mem_iff_of_eq_of_measurable_comap f ht (hxy.trans hzy.symm)).1 hx

end InvariantProjection.PolarStructure

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_OrbitFiberNull
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Function MeasureTheory

namespace Invariant233

variable {X Y : Type*} [m : MeasurableSpace X] [MeasurableSpace Y]
  [Nonempty Y] [MeasurableSpace.CountablySeparated Y] [MeasurableSingletonClass Y]
  {μ : Measure X} [IsFiniteMeasure μ]

theorem orbit_joint_fiber_measure_zero
    (σ : Equiv.Perm X) (hσ : Measurable σ) (hinv : Measurable σ.symm)
    (htotal : ∀ n : ℕ, 0 < n → Ergodic (σ : X → X)^[n] μ)
    {f : X → Y} (hf : Measurable f)
    (hnonconstant : ¬ ∃ c : Y, f =ᵐ[μ] Function.const X c)
    (z : ℤ → Y) :
    μ {x | ∀ n : ℤ, f ((σ ^ n) x) = z n} = 0 := by
  let F : X → (ℤ → Y) := fun x n => f ((σ ^ n) x)
  have hspace : MeasurableSpace.comap F inferInstance = orbitMeasurableSpace σ f := by
    exact MeasurableSpace.comap_process_pi (fun n x => f ((σ ^ n) x))
  have hs : @MeasurableSet X (orbitMeasurableSpace σ f) (F ⁻¹' {z}) := by
    rw [← hspace]
    exact ⟨{z}, measurableSet_singleton z, rfl⟩
  have hnull : μ (F ⁻¹' {z}) = 0 := by
    by_contra hpos
    obtain ⟨t, ht, hsub, htpos, hdiff⟩ :=
      orbitMeasurableSpace_atomless σ hσ hinv htotal hf hnonconstant hs hpos
    have ht' : MeasurableSet[MeasurableSpace.comap F inferInstance] t := by
      rwa [hspace]
    rcases InvariantProjection.PolarStructure.fiber_is_atom_in_comap F z ht' hsub with
      hzero | hfull
    · exact htpos (by simp [hzero])
    · exact hdiff (by simp [hfull])
  have heq : {x | ∀ n : ℤ, f ((σ ^ n) x) = z n} = F ⁻¹' {z} := by
    ext x
    exact (funext_iff : F x = z ↔ ∀ n, F x n = z n).symm
  rwa [heq]

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_PurePointDiffuse
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in

theorem jointEigenspace_const_unit (D : H →L[ℂ] H) (z : ℂ) :
    jointEigenspace (fun _ : Unit => D) (fun _ => z) =
      Module.End.eigenspace D.toLinearMap z := by
  ext x
  simp only [mem_jointEigenspace, Module.End.mem_eigenspace_iff,
    ContinuousLinearMap.coe_coe, forall_const]

theorem projectionAtom_range_le_eigenspace
    {M : VonNeumannAlgebra H} (hab : IsAbelianVonNeumannAlgebra M)
    {p D : H →L[ℂ] H} (hp : IsProjectionAtom M p) (hD : D ∈ M)
    (hpure : HasCountablyAtomicSpectralType D) :
    ∃ z : ℂ, p.range ≤ Module.End.eigenspace D.toLinearMap z := by
  obtain ⟨S, _hS, hdense⟩ := hpure
  have hdense' :
      (⨆ z : S, jointEigenspace (fun _ : Unit => D) (fun _ => (z : ℂ))).topologicalClosure = ⊤ := by
    simpa only [jointEigenspace_const_unit] using hdense
  obtain ⟨z, hz⟩ := exists_mul_jointEigenprojection_ne_zero
    (fun _ : Unit => D) (fun z : S => fun _ => (z : ℂ)) hdense' p hp.2.2.1
  let q := jointEigenprojection (fun _ : Unit => D) (fun _ => (z : ℂ))
  have hqm : q ∈ M := by
    apply vonNeumannGenerated_le (Set.range (fun _ : Unit => D)) M ?_
      (jointEigenprojection_mem_generated (fun _ : Unit => D) (fun _ => (z : ℂ)))
    rintro A ⟨u, rfl⟩
    exact hD
  have hqproj : IsStarProjection q := isStarProjection_jointEigenprojection _ _
  have hpq : Commute p q := hab p q hp.1 hqm
  have hsub : (p * q) * p = p * q := by
    rw [mul_assoc, ← hpq.eq, ← mul_assoc, hp.2.1.isIdempotentElem.eq]
  have heq : p * q = p :=
    (hp.2.2.2 (p * q) (mul_mem hp.1 hqm) (hp.2.1.mul hqproj hpq) hsub).resolve_left hz
  refine ⟨z, ?_⟩
  rintro x ⟨y, rfl⟩
  have hfix : q (p y) = p y := by
    have h := DFunLike.congr_fun (hpq.eq.symm.trans heq) y
    exact h
  have hx : p y ∈ jointEigenspace (fun _ : Unit => D) (fun _ => (z : ℂ)) :=
    Submodule.starProjection_eq_self_iff.mp hfix
  rwa [jointEigenspace_const_unit] at hx

theorem projectionAtom_range_le_jointEigenspace
    {M : VonNeumannAlgebra H} (hab : IsAbelianVonNeumannAlgebra M)
    (D : ι → H →L[ℂ] H) (hD : ∀ i, D i ∈ M)
    (hpure : ∀ i, HasCountablyAtomicSpectralType (D i))
    {p : H →L[ℂ] H} (hp : IsProjectionAtom M p) :
    ∃ ev : ι → ℂ, p.range ≤ jointEigenspace D ev := by
  choose ev hev using fun i => projectionAtom_range_le_eigenspace hab hp (hD i) (hpure i)
  refine ⟨ev, ?_⟩
  intro x hx
  rw [mem_jointEigenspace]
  intro i
  exact Module.End.mem_eigenspace_iff.mp (hev i hx)

theorem isDiffuse_of_purePoint_no_jointEigenvectors
    {M : VonNeumannAlgebra H} (hab : IsAbelianVonNeumannAlgebra M)
    (D : ι → H →L[ℂ] H) (hD : ∀ i, D i ∈ M)
    (hpure : ∀ i, HasCountablyAtomicSpectralType (D i))
    (hjoint : ∀ ev : ι → ℂ, jointEigenspace D ev = ⊥) :
    IsDiffuseVonNeumannAlgebra M := by
  intro p hp
  obtain ⟨ev, hev⟩ := projectionAtom_range_le_jointEigenspace hab D hD hpure hp
  rw [hjoint ev] at hev
  apply hp.2.2.1
  ext x
  exact hev ⟨x, rfl⟩

theorem generated_isDiffuse_of_purePoint_no_jointEigenvectors
    (D : ι → H →L[ℂ] H)
    (hab : IsAbelianVonNeumannAlgebra (vonNeumannGenerated (Set.range D)))
    (hpure : ∀ i, HasCountablyAtomicSpectralType (D i))
    (hjoint : ∀ ev : ι → ℂ, jointEigenspace D ev = ⊥) :
    IsDiffuseVonNeumannAlgebra (vonNeumannGenerated (Set.range D)) := by
  exact isDiffuse_of_purePoint_no_jointEigenvectors hab D
    (fun i => subset_vonNeumannGenerated _ ⟨i, rfl⟩) hpure hjoint

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentRotation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Invariant233.IndependentRotation

theorem irrational_finsupp_rat_sum {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (c : ι →₀ ℚ) (hc : c ≠ 0) :
    Irrational (c.sum (fun i q => (q : ℝ) * θ i)) := by
  rintro ⟨r, hr⟩
  let l : Option ι →₀ ℚ := c.optionElim (-r)
  have hl : Finsupp.linearCombination ℚ (fun o : Option ι => o.elim 1 θ) l = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_option_index_smul]
    simp only [l, Finsupp.optionElim_apply_eq_elim, Option.elim_none,
      Finsupp.some_optionElim, Option.elim_some, Rat.smul_def, Rat.cast_neg, mul_one]
    linarith
  exact (Finsupp.optionElim_ne_zero_of_right (-r) c hc)
    ((linearIndependent_iff.mp hθ) l hl)

theorem irrational_finsupp_int_sum {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (hv : v ≠ 0) :
    Irrational (v.sum (fun i n => (n : ℝ) * θ i)) := by
  let c : ι →₀ ℚ := v.mapRange (fun n : ℤ => (n : ℚ)) (by simp)
  have hc : c ≠ 0 := by
    intro h
    apply hv
    ext i
    have hi := DFunLike.congr_fun h i
    dsimp [c] at hi
    exact_mod_cast hi
  have h := irrational_finsupp_rat_sum hθ c hc
  simpa [c, Finsupp.sum_mapRange_index] using h

end Invariant233.IndependentRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ErgodicCharacterCriterion
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Invariant233.Characters

theorem integral_eq_zero_of_eigenfunction {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {σ : X → X} (hσ : MeasurePreserving σ μ μ)
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) {z : ℂ} (hz : z ≠ 1)
    (heigen : ∀ᵐ x ∂μ, f (σ x) = z * f x) :
    (∫ x, f x ∂μ) = 0 := by
  have hfm : AEStronglyMeasurable f (μ.map σ) := by rwa [hσ.map_eq]
  have hmap := integral_map hσ.measurable.aemeasurable hfm
  rw [hσ.map_eq] at hmap
  have heq : (∫ x, f x ∂μ) = z * ∫ x, f x ∂μ := by
    calc
      _ = ∫ x, f (σ x) ∂μ := hmap
      _ = ∫ x, z * f x ∂μ := integral_congr_ae heigen
      _ = _ := integral_const_mul z f
  have hzero : (1 - z) * (∫ x, f x ∂μ) = 0 := by
    calc
      _ = (∫ x, f x ∂μ) - z * (∫ x, f x ∂μ) := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hz.symm)

theorem eq_zero_of_dense_inner {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : E) (χ : ι → E)
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hinner : ∀ i, inner ℂ v (χ i) = 0) : v = 0 := by
  let L : E →L[ℂ] ℂ := innerSL ℂ v
  have hspan : Submodule.span ℂ (Set.range χ) ≤ L.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hinner i
  have htop := (Submodule.span ℂ (Set.range χ)).topologicalClosure_minimal
    hspan L.isClosed_ker
  rw [hdense] at htop
  have hv : L v = 0 := htop (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ E))
  exact inner_self_eq_zero.mp hv

theorem ergodic_of_dense_L2_eigenfunctions {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {σ : X → X}
    (hσ : MeasurePreserving σ μ μ) (i₀ : ι) (χ : ι → X → ℂ) (z : ι → ℂ)
    (hχ : ∀ i, MemLp (χ i) 2 μ)
    (hconst : χ i₀ =ᵐ[μ] fun _ => 1)
    (hdense : (Submodule.span ℂ
      (Set.range (fun i => (hχ i).toLp (χ i)))).topologicalClosure = ⊤)
    (hz : ∀ i, i ≠ i₀ → z i ≠ 1)
    (heigen : ∀ i, i ≠ i₀ → ∀ᵐ x ∂μ, χ i (σ x) = z i * χ i x) :
    Ergodic σ μ := by
  classical
  refine ⟨hσ, ⟨?_⟩⟩
  intro s hs hinv
  let p : ℝ := μ.real s
  let u : Lp ℂ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
  let e : Lp ℂ 2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) 1
  have hσs : MeasurePreserving σ (μ.restrict s) (μ.restrict s) := by
    simpa only [hinv] using hσ.restrict_preimage hs
  have hpair : ∀ i,
      inner ℂ u ((hχ i).toLp (χ i)) = (p : ℂ) * inner ℂ e ((hχ i).toLp (χ i)) := by
    intro i
    have hfull : inner ℂ e ((hχ i).toLp (χ i)) = ∫ x, χ i x ∂μ := by
      rw [L2.inner_indicatorConstLp_one, setIntegral_univ]
      exact integral_congr_ae (hχ i).coeFn_toLp
    have hset : inner ℂ u ((hχ i).toLp (χ i)) = ∫ x in s, χ i x ∂μ := by
      rw [L2.inner_indicatorConstLp_one]
      exact integral_congr_ae ((hχ i).coeFn_toLp.filter_mono (ae_mono Measure.restrict_le_self))
    rw [hfull, hset]
    by_cases hi : i = i₀
    · subst i
      rw [integral_congr_ae hconst,
        integral_congr_ae (hconst.filter_mono (ae_mono Measure.restrict_le_self))]
      simp [p]
    · have hzero := integral_eq_zero_of_eigenfunction hσ (hχ i).aestronglyMeasurable
        (hz i hi) (heigen i hi)
      have hzeros := integral_eq_zero_of_eigenfunction hσs
        (hχ i).aestronglyMeasurable.restrict (hz i hi)
        ((heigen i hi).filter_mono (ae_mono Measure.restrict_le_self))
      rw [hzero, hzeros, mul_zero]
  have heq : u = (p : ℂ) • e := by
    apply sub_eq_zero.mp
    apply eq_zero_of_dense_inner (u - (p : ℂ) • e)
      (fun i => (hχ i).toLp (χ i)) hdense
    intro i
    rw [inner_sub_left, inner_smul_left, hpair i]
    simp
  have huu : inner ℂ u u = (p : ℂ) := by
    change inner ℂ (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ))
      (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)) = _
    rw [L2.inner_indicatorConstLp_indicatorConstLp]
    simp [p]
  have heu : inner ℂ e u = (p : ℂ) := by
    change inner ℂ (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℂ))
      (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)) = _
    rw [L2.inner_indicatorConstLp_indicatorConstLp]
    simp [p]
  have hpalg := congrArg (fun v : Lp ℂ 2 μ => inner ℂ v u) heq
  rw [huu, inner_smul_left, heu] at hpalg
  have hpalg' := congrArg Complex.re hpalg
  simp at hpalg'
  have hp01 : p = 0 ∨ p = 1 := by
    have hpzero : p * (p - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hpzero with hp | hp
    · exact Or.inl hp
    · exact Or.inr (sub_eq_zero.mp hp)
  apply eventuallyConst_set.mpr
  rcases hp01 with hp | hp
  · right
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using (measureReal_eq_zero_iff (μ := μ)).mp hp
  · left
    rw [ae_iff]
    have hpc : μ.real sᶜ = 0 := by rw [measureReal_compl hs, probReal_univ]; exact sub_eq_zero.mpr hp.symm
    exact (measureReal_eq_zero_iff (μ := μ)).mp hpc

theorem ergodic_of_dense_continuous_eigenfunctions {X ι : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]
    {σ : X → X} (hσ : MeasurePreserving σ μ μ)
    (i₀ : ι) (χ : ι → C(X, ℂ)) (z : ι → ℂ)
    (hconst : χ i₀ = 1)
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hz : ∀ i, i ≠ i₀ → z i ≠ 1)
    (heigen : ∀ i, i ≠ i₀ → ∀ x, χ i (σ x) = z i * χ i x) :
    Ergodic σ μ := by
  let hχ : ∀ i, MemLp (χ i) 2 μ := fun i => ContinuousMap.memLp μ ℂ (χ i)
  have hlp : (fun i => (hχ i).toLp (χ i)) =
      (fun i => ContinuousMap.toLp 2 μ ℂ (χ i)) := by
    funext i
    apply Lp.ext
    exact (hχ i).coeFn_toLp.trans (ContinuousMap.coeFn_toLp μ (χ i)).symm
  have hdenseLp : (Submodule.span ℂ
      (Set.range (fun i => (hχ i).toLp (χ i)))).topologicalClosure = ⊤ := by
    rw [hlp]
    have hd := (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).topologicalClosure_map_submodule hdense
    rw [Submodule.map_span, ← Set.range_comp'] at hd
    exact hd
  refine ergodic_of_dense_L2_eigenfunctions hσ i₀ (fun i => χ i) z hχ ?_ hdenseLp hz ?_
  · exact Eventually.of_forall fun x => by rw [hconst]; rfl
  · intro i hi
    exact Eventually.of_forall (heigen i hi)

end Invariant233.Characters

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductCharacters
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.ProductRotation

open scoped BigOperators ComplexConjugate
open Set Algebra Submodule

variable {ι : Type*}

theorem characterPhase_add (v : ι →₀ ℤ) (x y : ι → UnitAddCircle) :
    characterPhase v (x + y) = characterPhase v x + characterPhase v y := by
  simp [characterPhase, Finsupp.sum_add]

theorem characterPhase_add_index (v w : ι →₀ ℤ) (x : ι → UnitAddCircle) :
    characterPhase (v + w) x = characterPhase v x + characterPhase w x := by
  classical
  simp [characterPhase, Finsupp.sum_add_index, add_zsmul]

theorem productCharacter_add (v : ι →₀ ℤ) (x y : ι → UnitAddCircle) :
    productCharacter v (x + y) = productCharacter v x * productCharacter v y := by
  simp [productCharacter, characterPhase_add, AddCircle.toCircle_add]

theorem productCharacter_add_index (v w : ι →₀ ℤ) :
    productCharacter (v + w) = productCharacter v * productCharacter w := by
  ext x
  simp [productCharacter, characterPhase_add_index, AddCircle.toCircle_add]

theorem productCharacter_neg (v : ι →₀ ℤ) :
    productCharacter (-v) = star (productCharacter v) := by
  ext x
  simp [productCharacter, characterPhase, Finsupp.sum_neg_index,
    Finsupp.sum_neg, AddCircle.toCircle_neg]
  exact Circle.coe_inv_eq_conj _

theorem productFourierAlgebra_separatesPoints :
    (productFourierAlgebra ι).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_, ⟨productCharacter (Finsupp.single i 1),
    StarAlgebra.subset_adjoin ℂ _ ⟨Finsupp.single i 1, rfl⟩, rfl⟩, ?_⟩
  intro heq
  apply hi
  apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
  apply Subtype.coe_injective
  simpa only [productCharacter_single_one] using heq

theorem productFourierAlgebra_closure_eq_top :
    (productFourierAlgebra ι).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    productFourierAlgebra_separatesPoints

theorem productFourierAlgebra_toSubmodule :
    (productFourierAlgebra ι).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (productCharacter (ι := ι))) := by
  classical
  rw [productFourierAlgebra, StarAlgebra.adjoin_eq_span]
  congr 1
  apply Set.Subset.antisymm
  · intro f hf
    induction hf using Submonoid.closure_induction with
    | mem f hf =>
      rcases hf with hf | hf
      · exact hf
      · obtain ⟨v, hv⟩ := hf
        exact ⟨-v, by rw [productCharacter_neg, hv, star_star]⟩
    | one => exact ⟨0, productCharacter_zero⟩
    | mul f g hf hg ihf ihg =>
      obtain ⟨v, rfl⟩ := ihf
      obtain ⟨w, rfl⟩ := ihg
      exact ⟨v + w, productCharacter_add_index v w⟩
  · intro f hf
    exact Submonoid.subset_closure (Or.inl hf)

theorem span_productCharacter_closure_eq_top :
    (Submodule.span ℂ (Set.range (productCharacter (ι := ι)))).topologicalClosure = ⊤ := by
  rw [← productFourierAlgebra_toSubmodule]
  exact congr_arg (fun A : StarSubalgebra ℂ C((ι → UnitAddCircle), ℂ) =>
    A.toSubalgebra.toSubmodule) productFourierAlgebra_closure_eq_top

theorem mul_sum_ne_int (θ : ι → ℝ)
    (hθ : ∀ (v : ι →₀ ℤ) (k : ℤ),
      v.sum (fun i z => (z : ℝ) * θ i) = k → v = 0)
    {v : ι →₀ ℤ} (hv : v ≠ 0) {q : ℤ} (hq : q ≠ 0) (k : ℤ) :
    (q : ℝ) * v.sum (fun i z => (z : ℝ) * θ i) ≠ (k : ℝ) := by
  intro heq
  have hz : q • v = 0 := hθ (q • v) k (by
    rw [Finsupp.sum_smul_index (fun _ => by simp)]
    simpa only [Int.cast_mul, mul_assoc, Finsupp.sum, Finset.mul_sum] using heq)
  exact (smul_ne_zero hq hv) hz

theorem characterPhase_coe (v : ι →₀ ℤ) (θ : ι → ℝ) :
    characterPhase v (fun i => (θ i : UnitAddCircle)) =
      ((v.sum (fun i z => (z : ℝ) * θ i) : ℝ) : UnitAddCircle) := by
  change v.sum (fun i n => n • (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (θ i)) =
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (v.sum (fun i z => (z : ℝ) * θ i))
  rw [map_finsuppSum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [zsmul_eq_mul] using
    (map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (v i) (θ i)).symm

theorem productCharacter_ne_one (θ : ι → ℝ)
    (hθ : ∀ (v : ι →₀ ℤ) (k : ℤ),
      v.sum (fun i z => (z : ℝ) * θ i) = k → v = 0)
    {v : ι →₀ ℤ} (hv : v ≠ 0) {q : ℤ} (hq : q ≠ 0) :
    productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) ≠ 1 := by
  intro heq
  have hphase : characterPhase v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) = 0 := by
    apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
    apply Subtype.coe_injective
    simpa [productCharacter] using heq
  rw [characterPhase_coe, AddCircle.coe_eq_zero_iff] at hphase
  obtain ⟨k, hk⟩ := hphase
  apply mul_sum_ne_int θ hθ hv hq k
  simpa only [Finsupp.sum, Finset.mul_sum, zsmul_eq_mul, mul_one,
    mul_left_comm, mul_assoc] using hk.symm

theorem productCharacter_translation (v : ι →₀ ℤ) (θ : ι → ℝ) (q : ℤ)
    (x : ι → UnitAddCircle) :
    productCharacter v (fun i => x i + (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) =
      productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) *
        productCharacter v x := by
  rw [mul_comm, ← productCharacter_add]
  congr 1

end InvariantProjection.ProductRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductErgodicity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.ProductRotation

open MeasureTheory

variable {ι : Type*}

theorem integer_affine_independent {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (m : ℤ)
    (heq : v.sum (fun i z => (z : ℝ) * θ i) = m) : v = 0 := by
  by_contra hv
  exact (Invariant233.IndependentRotation.irrational_finsupp_int_sum hθ v hv).ne_int m heq

theorem measurePreserving_product_translation (a : ι → UnitAddCircle) :
    MeasurePreserving (fun x : ι → UnitAddCircle => x + a)
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  have hcoord (i : ι) : MeasurePreserving
      (fun x : UnitAddCircle => x + a i) volume volume :=
    measurePreserving_add_right volume _
  refine ⟨Measurable.of_eval (fun i => (measurable_pi_apply i).add_const _), ?_⟩
  change (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))).map
      (fun x i => x i + a i) = _
  rw [Measure.infinitePi_map_pi _ (fun i => (hcoord i).measurable)]
  simp only [(hcoord _).map_eq]

theorem product_rotation_integer_ergodic [Countable ι] {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    {q : ℤ} (hq : q ≠ 0) :
    Ergodic (fun x : ι → UnitAddCircle =>
      fun i => x i + (((q : ℝ) * θ i : ℝ) : UnitAddCircle))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  apply Invariant233.Characters.ergodic_of_dense_continuous_eigenfunctions
    (measurePreserving_product_translation (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)))
    (0 : ι →₀ ℤ) productCharacter
    (fun v => productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)))
    productCharacter_zero span_productCharacter_closure_eq_top
  · intro v hv
    exact productCharacter_ne_one θ (integer_affine_independent hθ) hv hq
  · intro v _ x
    exact productCharacter_translation v θ q x

theorem product_rotation_totalErgodic [Countable ι] {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    {n : ℕ} (hn : 0 < n) :
    Ergodic (fun x : ι → UnitAddCircle => fun i => x i + (θ i : UnitAddCircle))^[n]
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  change Ergodic (fun x : ι → UnitAddCircle => x + fun i => (θ i : UnitAddCircle))^[n] _
  rw [add_right_iterate]
  have hcoe : (fun i => (((n : ℝ) * θ i : ℝ) : UnitAddCircle)) =
      n • (fun i => (θ i : UnitAddCircle)) := by
    funext i
    simpa only [Pi.smul_apply, nsmul_eq_mul] using
      (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := n) (x := θ i))
  have he := product_rotation_integer_ergodic hθ (q := (n : ℤ))
    (by exact_mod_cast Nat.ne_of_gt hn)
  simp only [Int.cast_natCast] at he
  change Ergodic (fun x : ι → UnitAddCircle =>
    x + (fun i => (((n : ℝ) * θ i : ℝ) : UnitAddCircle))) _ at he
  rwa [hcoe] at he

end InvariantProjection.ProductRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductBaseDynamics
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ProductModel

open MeasureTheory

theorem measurePreserving_rotation (θ : ℕ → ℝ) :
    MeasurePreserving (rotation θ) baseMeasure baseMeasure :=
  InvariantProjection.ProductRotation.measurePreserving_product_translation
    (fun i => (θ i : UnitAddCircle))

theorem rotation_totalErgodic {θ : ℕ → ℝ}
    (hθ : JointlyRationallyIndependent θ) {n : ℕ} (hn : 0 < n) :
    Ergodic (rotation θ)^[n] baseMeasure :=
  InvariantProjection.ProductRotation.product_rotation_totalErgodic hθ hn

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRepresentative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem measurePreserving_productRepresentative {ι : Type*} (i : ι) :
    MeasurePreserving
      (fun x : ι → UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  exact measurePreserving_circleRepresentative.comp
    (measurePreserving_eval_infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)) i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CocycleSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.CocycleSupport

theorem uniform_floor_ne_zero_le (t : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ≤
      ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  rw [Measure.restrict_apply hm]
  rcases le_or_gt 0 t with ht | ht
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico (1 - t) 1) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨?_, hx1⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, abs_of_nonneg ht]
        congr 1
        ring
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico 0 (-t)) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨hx0, ?_⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, sub_zero, abs_of_neg ht]

theorem ae_finite_support_of_tsum_ne_top {Ω ι A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Zero A]
    (μ : Measure Ω) (a : ι → Ω → A)
    (h : (∑' i, μ {x | a i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => a i x)).Finite := by
  exact ae_finite_setOfPred_mem h

theorem ae_all_finite_support_of_tsum_ne_top {Ω ι K A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Countable K] [Zero A]
    (μ : Measure Ω) (a : K → ι → Ω → A)
    (h : ∀ k, (∑' i, μ {x | a k i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ k, (Function.support (fun i => a k i x)).Finite := by
  rw [ae_all_iff]
  intro k
  exact ae_finite_support_of_tsum_ne_top μ (a k) (h k)

theorem measure_floor_ne_zero_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : Ω → ℝ) (hu : Measurable u)
    (hlaw : μ.map u = volume.restrict (Ico (0 : ℝ) 1)) (t : ℝ) :
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} ≤ ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  calc
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} =
        (μ.map u) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
      (Measure.map_apply hu hm).symm
    _ = (volume.restrict (Ico (0 : ℝ) 1))
        {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} := by rw [hlaw]
    _ ≤ ENNReal.ofReal |t| := uniform_floor_ne_zero_le t

theorem ae_all_int_finite_floor_support {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (u : ι → Ω → ℝ) (hu : ∀ i, Measurable (u i))
    (hlaw : ∀ i, μ.map (u i) = volume.restrict (Ico (0 : ℝ) 1))
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => (⌊u i x + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  apply ae_all_finite_support_of_tsum_ne_top
  intro k
  apply ne_top_of_le_ne_top ((hθ.mul_left |(k : ℝ)|).tsum_ofReal_ne_top)
  apply ENNReal.tsum_le_tsum
  intro i
  simpa only [abs_mul, abs_of_nonneg (hθ0 i)] using
    measure_floor_ne_zero_le μ (u i) (hu i) (hlaw i) ((k : ℝ) * θ i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem ae_product_all_int_finite_floor_support {ι : Type*} [Countable ι]
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))),
      ∀ k : ℤ,
        (Function.support (fun i =>
          (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  exact ae_all_int_finite_floor_support
    (Ω := ι → UnitAddCircle) (ι := ι)
    (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
    (fun i => (measurePreserving_productRepresentative i).measurable)
    (fun i => (measurePreserving_productRepresentative i).map_eq)
    θ hθ0 hθ

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FloorCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace FloorCocycle

theorem floor_add_eq_indicator {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u < 1) (t : ℝ) :
    ⌊u + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ u then 1 else 0 := by
  have hsplit : ⌊u + t⌋ = ⌊u + Int.fract t⌋ + ⌊t⌋ := by
    rw [← Int.floor_add_intCast]
    congr 1
    rw [add_assoc, Int.fract_add_floor]
  rw [hsplit]
  split_ifs with h
  · have hf : ⌊u + Int.fract t⌋ = 1 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [Int.fract_lt_one t]
    rw [hf]
    omega
  · have hf : ⌊u + Int.fract t⌋ = 0 := by
      apply Int.floor_eq_zero_iff.mpr
      constructor
      · exact add_nonneg hu₀ (Int.fract_nonneg t)
      · linarith
    rw [hf]
    omega

end FloorCocycle
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function

namespace Invariant233.FiniteSupportCocycle

theorem summable_weighted_int {I : Type*} (c : I → ℝ) {a : I → ℤ}
    (ha : HasFiniteSupport a) : Summable (fun i ↦ c i * (a i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  exact HasFiniteSupport.mul_right c (ha.fun_comp (by simp))

end Invariant233.FiniteSupportCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

theorem representative_mem_Ico (x : UnitAddCircle) :
    representative x ∈ Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

theorem representative_add (x : UnitAddCircle) (t : ℝ) :
    representative (x + (t : UnitAddCircle)) = Int.fract (representative x + t) := by
  have hx : x + (t : UnitAddCircle) =
      ((representative x + t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_representative]
  rw [hx]
  change ((AddCircle.equivIco (1 : ℝ) 0
    ((representative x + t : ℝ) : UnitAddCircle)) : ℝ) = _
  simpa only [div_one, mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (representative x + t))

theorem cocycleVersion_pos {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) :
    0 < cocycleVersion θ c k x :=
  Real.exp_pos _

theorem cocycleVersion_eq_finite_sum {I : Type*}
    (θ c : I → ℝ) (k : ℤ) (x : Space I) (s : Finset I)
    (hs : ∀ i ∉ s, ⌊representative (x i) + (k : ℝ) * θ i⌋ = 0) :
    cocycleVersion θ c k x =
      Real.exp (-∑ i ∈ s, c i * (⌊representative (x i) + (k : ℝ) * θ i⌋ : ℝ)) := by
  unfold cocycleVersion
  rw [tsum_eq_sum (s := s) (fun i hi ↦ by rw [hs i hi]; simp)]

theorem exists_finset_cocycleVersion_one {I : Type*}
    (θ c : I → ℝ) (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (x : Space I)
    (hx : HasFiniteSupport (fun i ↦ ⌊representative (x i) + θ i⌋)) :
    ∃ s : Finset I, cocycleVersion θ c 1 x = Real.exp (-∑ i ∈ s, c i) := by
  classical
  let s := hx.toFinset
  have hs : ∀ i ∉ s, ⌊representative (x i) + (1 : ℝ) * θ i⌋ = 0 := by
    intro i hi
    have hnot : i ∉ Function.support (fun j ↦ ⌊representative (x j) + θ j⌋) := by
      exact fun hmem ↦ hi (hx.mem_toFinset.mpr hmem)
    simpa only [Function.mem_support, not_not, one_mul] using hnot
  refine ⟨s, ?_⟩
  rw [cocycleVersion_eq_finite_sum θ c 1 x s (by simpa using hs)]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hne : ⌊representative (x i) + θ i⌋ ≠ 0 := by
    exact hx.mem_toFinset.mp hi
  have hzero : ⌊θ i⌋ = 0 := Int.floor_eq_zero_iff.mpr (hθ i)
  have hfloor : ⌊representative (x i) + θ i⌋ = 1 := by
    rw [FloorCocycle.floor_add_eq_indicator (representative_mem_Ico (x i)).1
      (representative_mem_Ico (x i)).2, hzero] at hne ⊢
    split_ifs at hne ⊢ <;> simp_all
  simp only [Int.cast_one, one_mul, hfloor, mul_one]

theorem ae_exists_finset_cocycleVersion_one {I : Type*} [Countable I]
    (θ c : I → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hθ : Summable θ) :
    ∀ᵐ x ∂haar I, ∃ s : Finset I,
      cocycleVersion θ c 1 x = Real.exp (-∑ i ∈ s, c i) := by
  have hall := CocycleSupport.ae_product_all_int_finite_floor_support
    θ (fun i ↦ (hθ01 i).1) hθ
  filter_upwards [hall] with x hx
  apply exists_finset_cocycleVersion_one θ c hθ01 x
  simpa only [HasFiniteSupport, representative, Int.cast_one, one_mul] using hx 1

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductWeightBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

theorem cost_summand_nonneg (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base) (i : ℕ) :
    0 ≤ c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) := by
  apply mul_nonneg (hc i)
  have hf : (0 : ℤ) ≤ ⌊circleRepresentative (x i) + θ i⌋ := by
    apply Int.floor_nonneg.mpr
    exact add_nonneg (ProductCocycle.representative_mem_Ico (x i)).1 (hθ i)
  exact_mod_cast hf

theorem logarithmicCost_eq_ofReal_tsum (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    logarithmicCost θ c x =
      ENNReal.ofReal (∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ)) := by
  exact (ENNReal.ofReal_tsum_of_nonneg
    (cost_summand_nonneg θ c hθ hc x)
    (FiniteSupportCocycle.summable_weighted_int c hx)).symm

theorem weight_eq_cocycleVersion_of_finite_support (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    weight θ c x = ProductCocycle.cocycleVersion θ c 1 x := by
  have hnonneg : 0 ≤ ∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) :=
    tsum_nonneg (cost_summand_nonneg θ c hθ hc x)
  unfold weight
  rw [logarithmicCost_eq_ofReal_tsum θ c hθ hc x hx,
    EReal.coe_ennreal_ofReal, max_eq_left hnonneg, ← EReal.coe_neg,
    EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [ProductCocycle.cocycleVersion, Int.cast_one, one_mul,
    circleRepresentative, ProductCocycle.representative]

theorem negLogCost_weight (θ c : ℕ → ℝ) (x : Base) :
    negLogCost (weight θ c x) = logarithmicCost θ c x :=
  negLogCost_extendedExpNeg _

theorem weight_ae_eq_cocycleVersion (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    weight θ c =ᵐ[baseMeasure] ProductCocycle.cocycleVersion θ c 1 := by
  have hall := CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  filter_upwards [hall] with x hx
  apply weight_eq_cocycleVersion_of_finite_support θ c hθ0 hc x
  simpa only [HasFiniteSupport, circleRepresentative, Int.cast_one, one_mul] using hx 1

theorem ae_weight_pos (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, 0 < weight θ c x := by
  filter_upwards [weight_ae_eq_cocycleVersion θ c hθ0 hc hθ] with x hx
  rw [hx]
  exact ProductCocycle.cocycleVersion_pos θ c 1 x

theorem weight_eq_zero_iff (θ c : ℕ → ℝ) (x : Base) :
    weight θ c x = 0 ↔ logarithmicCost θ c x = ∞ :=
  extendedExpNeg_eq_zero_iff _

theorem ae_exists_finset_weight (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, ∃ s : Finset ℕ, weight θ c x = Real.exp (-∑ i ∈ s, c i) := by
  filter_upwards [weight_ae_eq_cocycleVersion θ c (fun i ↦ (hθ01 i).1) hc hθ,
    ProductCocycle.ae_exists_finset_cocycleVersion_one θ c hθ01 hθ] with x hx hfin
  simpa only [hx] using hfin

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductOrbitFiberNull
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

private theorem orbitPerm_zpow (θ : ℕ → ℝ) (n : ℤ) (x : Base) :
    (orbitPerm θ ^ n) x = rotationIterate θ n x := by
  cases n with
  | ofNat n =>
    change ((Equiv.addRight (fun i => (θ i : Circle))) ^ n) x = _
    rw [Equiv.Perm.coe_pow]
    change (fun x : Base => x + fun i => (θ i : Circle))^[n] x = _
    rw [add_right_iterate]
    ext i
    change x i + n • (θ i : Circle) = x i + (((n : ℤ) : ℝ) * θ i : ℝ)
    rw [← AddCircle.coe_nsmul]
    simp [nsmul_eq_mul]
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    change ((Equiv.addRight (fun i => (θ i : Circle))).symm ^ (n + 1)) x = _
    rw [Equiv.addRight_symm, Equiv.Perm.coe_pow]
    change (fun x : Base => x + -(fun i => (θ i : Circle)))^[n + 1] x = _
    rw [add_right_iterate]
    ext i
    change x i + (n + 1) • (-(θ i : Circle)) =
      x i + (((Int.negSucc n : ℤ) : ℝ) * θ i : ℝ)
    rw [← AddCircle.coe_neg, ← AddCircle.coe_nsmul]
    congr 2
    simp [nsmul_eq_mul]
    ring

theorem rotation_joint_fiber_measure_zero
    {Y : Type*} [MeasurableSpace Y] [Nonempty Y]
    [MeasurableSpace.CountablySeparated Y] [MeasurableSingletonClass Y]
    {θ : ℕ → ℝ} (hθ : JointlyRationallyIndependent θ)
    {f : Base → Y} (hf : Measurable f)
    (hnonconstant : ¬ ∃ c : Y, f =ᵐ[baseMeasure] Function.const Base c)
    (z : ℤ → Y) :
    baseMeasure {x | ∀ n : ℤ, f (rotationIterate θ n x) = z n} = 0 := by
  have hm : Measurable (orbitPerm θ) := (measurePreserving_rotation θ).measurable
  have hi : Measurable (orbitPerm θ).symm := by
    change Measurable (fun x : Base => x - fun i => (θ i : Circle))
    fun_prop
  have he : ∀ n : ℕ, 0 < n → Ergodic (orbitPerm θ : Base → Base)^[n] baseMeasure := by
    intro n hn
    exact rotation_totalErgodic hθ hn
  simpa only [orbitPerm_zpow] using
    orbit_joint_fiber_measure_zero (orbitPerm θ) hm hi he hf hnonconstant z

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal lp Topology

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)

variable {a C hC ha hm}

theorem fieldShift_ae (m : ℤ) (f : Lp Hilbert 2 μ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f =ᵐ[μ]
      fun x => shift m (f x) :=
  ContinuousLinearMap.coeFn_compLp _ f

theorem fieldShift_add (m n : ℤ) :
    (shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ =
      (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
        (shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  ext f
  filter_upwards [fieldShift_ae (m + n) f,
    fieldShift_ae m ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f),
    fieldShift_ae n f] with x hmn hm hn
  change ((shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x =
    ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
      ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f)) x
  rw [hmn, hm, hn]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (f x)) (shift_add m n)

theorem fieldShift_zero :
    (shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ = 1 := by
  ext f
  filter_upwards [fieldShift_ae 0 f] with x hx
  change ((shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x = f x
  rw [hx]
  change (shift 0).toLinearIsometry.toContinuousLinearMap (f x) = f x
  rw [shift_zero]
  rfl

theorem fieldShift_norm_map (m : ℤ) (f : Lp Hilbert 2 μ) :
    ‖(shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ,
      ‖((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x‖ = ‖f x‖ := by
    filter_upwards [fieldShift_ae m f] with x hx
    rw [hx, (shift m).norm_map]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldShift_mem_unitary (m : ℤ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ∈
      unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  let A := (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  let B := (shift (-m)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hA : IsUnit A := ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  apply hA.mem_unitary_iff_star_mul_self.mpr
  change ContinuousLinearMap.adjoint A ∘L A = 1
  exact A.norm_map_iff_adjoint_comp_self.mp (fieldShift_norm_map m)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductFinitePolar
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem rotationIterate_measurePreserving_polar (θ : ℕ → ℝ) (k : ℤ) :
    MeasurePreserving (rotationIterate θ k) baseMeasure baseMeasure := by
  let : circleMeasure.IsAddRightInvariant := by
    unfold circleMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  constructor
  · apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply i).add_const _
  · unfold baseMeasure rotationIterate
    rw [Measure.infinitePi_map_pi (fun _ : ℕ => circleMeasure)
      (f := fun i (x : Circle) => x + (((k : ℝ) * θ i : ℝ) : Circle))
      (fun i => measurable_id.add_const _)]
    congr 1
    funext i
    exact (measurePreserving_add_right circleMeasure (((k : ℝ) * θ i : ℝ) : Circle)).map_eq

theorem shiftOperator_star_eq : star shiftOperator = signedShift (-1) := by
  have hu := WeightedShift.fieldShift_mem_unitary (μ := baseMeasure) 1
  have hleft : star shiftOperator * shiftOperator = 1 := (Unitary.mem_iff.mp hu).1
  have hright : shiftOperator * signedShift (-1) = 1 := by
    change signedShift 1 * signedShift (-1) = 1
    rw [← WeightedShift.fieldShift_add]
    simpa using (WeightedShift.fieldShift_zero (μ := baseMeasure))
  calc
    star shiftOperator = star shiftOperator * 1 := (mul_one _).symm
    _ = star shiftOperator * (shiftOperator * signedShift (-1)) := by rw [hright]
    _ = signedShift (-1) := by rw [← mul_assoc, hleft, one_mul]

theorem shiftOperator_pow_eq (n : ℕ) : shiftOperator ^ n = signedShift n := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero] using
      (WeightedShift.fieldShift_zero (μ := baseMeasure)).symm
  | succ n ih =>
      rw [pow_succ, ih]
      change signedShift (n : ℤ) * signedShift 1 = signedShift (n + 1 : ℕ)
      rw [← WeightedShift.fieldShift_add]
      simp only [Nat.cast_add, Nat.cast_one]

theorem star_shiftOperator_pow_eq (n : ℕ) : star shiftOperator ^ n = signedShift (-(n : ℤ)) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero, neg_zero] using
      (WeightedShift.fieldShift_zero (μ := baseMeasure)).symm
  | succ n ih =>
      rw [pow_succ, ih, shiftOperator_star_eq]
      rw [← WeightedShift.fieldShift_add]
      rw [show -(n : ℤ) + -1 = -((n + 1 : ℕ) : ℤ) by omega]

theorem polarConjugate_eq_signedShift (B : Hilbert →L[ℂ] Hilbert) (n : ℤ) :
    polarConjugate shiftOperator B n = signedShift n * B * signedShift (-n) := by
  unfold polarConjugate
  split_ifs with hn
  · rw [shiftOperator_pow_eq, star_shiftOperator_pow_eq, Int.toNat_of_nonneg hn]
  · rw [shiftOperator_pow_eq, star_shiftOperator_pow_eq, Int.toNat_of_nonneg (by omega : 0 ≤ -n)]
    simp only [neg_neg]

theorem multiplier_coordinate_ae (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (v : Hilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      multiplier θ g C hC hg hb v x k = g (rotationIterate θ k x) * v x k := by
  exact WeightedShift.fieldDiagonal_coordinate_ae _ _ _ _ _ v

theorem polarConjugate_multiplier_coordinate_ae
    (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (n : ℤ) (v : Hilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      polarConjugate shiftOperator (multiplier θ g C hC hg hb) n v x k =
        g (rotationIterate θ (k - n) x) * v x k := by
  rw [polarConjugate_eq_signedShift]
  let B := multiplier θ g C hC hg hb
  filter_upwards [WeightedShift.fieldShift_ae n (B (signedShift (-n) v)),
    multiplier_coordinate_ae θ g C hC hg hb (signedShift (-n) v),
    WeightedShift.fieldShift_ae (-n) v] with x hs hbval ht k
  change signedShift n (B (signedShift (-n) v)) x k = _
  rw [hs, WeightedShift.shift_apply, hbval, ht, WeightedShift.shift_apply]
  simp only [sub_neg_eq_add, sub_add_cancel]

theorem fullPolarAlgebra_multiplier_abelian
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C) :
    IsAbelianVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb)) := by
  let D := polarConjugate shiftOperator (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb)
  have hD (n : ℤ) (v : Hilbert) (k : ℤ) : ∀ᵐ x ∂baseMeasure,
      D n v x k = (f (rotationIterate θ (k - n) x) : ℂ) * v x k :=
    (polarConjugate_multiplier_coordinate_ae θ _ C hC hf.complex_ofReal hb n v).mono
      (fun x hx => hx k)
  have hself (n : ℤ) : IsSelfAdjoint (D n) :=
    isSelfAdjoint_of_real_sequence_diagonal _ _ (hD n)
  have hcomm (m n : ℤ) : Commute (D m) (D n) :=
    commute_of_sequence_diagonal _ _ _ _ (hD m) (hD n)
  intro S T hS hT
  exact commute_of_mem_generated_selfAdjoint_family D hself hcomm hS hT

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductPolarRange
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ProductModel

theorem ae_weight_mem_countable (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) :
    ∃ S : Set ℝ, S.Countable ∧ S ⊆ Ioc (0 : ℝ) 1 ∧
      ∀ᵐ x ∂baseMeasure, weight θ c x ∈ S := by
  obtain ⟨S, hS, hrange⟩ :=
    InvariantProjection.PolarStructure.ae_countable_range_of_finite_drops c
      (weight θ c) (ae_exists_finset_weight θ c hθ01 hc hθ)
  refine ⟨S ∩ Ioc (0 : ℝ) 1, hS.mono inter_subset_left,
    inter_subset_right, ?_⟩
  filter_upwards [hrange, ae_weight_pos θ c (fun i ↦ (hθ01 i).1) hc hθ]
    with x hx hpos
  exact ⟨hx, hpos, (weight_mem_Icc θ c x).2⟩

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductWeightPolar
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductModel

theorem star_shift_weightedOperator_eq_multiplier (θ c : ℕ → ℝ) :
    star shiftOperator * weightedOperator θ c =
      multiplier θ (fun x ↦ (weight θ c x : ℂ)) 1 (by norm_num)
        (measurable_weight θ c).complex_ofReal (weight_complex_norm_le_one θ c) := by
  have hu : star shiftOperator * shiftOperator = 1 :=
    (Unitary.mem_iff.mp (WeightedShift.fieldShift_mem_unitary (μ := baseMeasure) 1)).1
  simp only [weightedOperator, ← ContinuousLinearMap.mul_def]
  rw [← mul_assoc, hu, one_mul]

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductPolarDiffuse
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem polarConjugate_multiplier_hasCountablyAtomicSpectralType
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hcount : ∃ R : Set ℝ, R.Countable ∧ ∀ᵐ x ∂baseMeasure, f x ∈ R)
    (n : ℤ) :
    HasCountablyAtomicSpectralType
      (polarConjugate shiftOperator
        (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb) n) := by
  obtain ⟨R, hR, hmem⟩ := hcount
  let S : Set ℂ := Complex.ofReal '' R
  have hS : S.Countable := hR.image _
  refine ⟨S, hS, ?_⟩
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hbasis (v : Fiber) (k : ℤ) : inner ℂ (b k) v = v k :=
    (b.repr_apply_apply v k).symm
  have hmeas (k : ℤ) : Measurable (fun x => (f (rotationIterate θ (k - n) x) : ℂ)) :=
    hf.complex_ofReal.comp (rotationIterate_measurePreserving_polar θ (k - n)).measurable
  have hrange (k : ℤ) :
      ∀ᵐ x ∂baseMeasure, (f (rotationIterate θ (k - n) x) : ℂ) ∈ S := by
    filter_upwards [(rotationIterate_measurePreserving_polar θ (k - n)).quasiMeasurePreserving.ae hmem]
      with x hx
    exact Set.mem_image_of_mem Complex.ofReal hx
  apply MultiplicationPurePoint.topologicalClosure_iSup_eigenspace_eq_top_of_basis b
    (fun k x => (f (rotationIterate θ (k - n) x) : ℂ)) hmeas hS hrange
  intro v k
  simpa only [hbasis] using
    (polarConjugate_multiplier_coordinate_ae θ _ C hC hf.complex_ofReal hb n v).mono
      (fun x hx => hx k)

theorem coefficient_fiber_null_of_orbit_fiber_null
    (θ : ℕ → ℝ) (f : Base → ℝ)
    (hnull : ∀ z : ℤ → ℝ,
      baseMeasure {x | ∀ n : ℤ, f (rotationIterate θ n x) = z n} = 0)
    (ev : ℤ → ℂ) (k : ℤ) :
    baseMeasure {x | ∀ n : ℤ, (f (rotationIterate θ (k - n) x) : ℂ) = ev n} = 0 := by
  apply measure_mono_null _ (hnull (fun m => (ev (k - m)).re))
  intro x hx m
  have h := congrArg Complex.re (hx (k - m))
  simpa only [sub_sub_cancel, Complex.ofReal_re] using h

theorem jointEigenspace_polarConjugates_eq_bot_of_null_fibers
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hnull : ∀ z : ℤ → ℝ,
      baseMeasure {x | ∀ n : ℤ, f (rotationIterate θ n x) = z n} = 0)
    (ev : ℤ → ℂ) :
    jointEigenspace (polarConjugate shiftOperator
      (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb)) ev = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have heigen := mem_jointEigenspace.mp hv
  have hcoord : ∀ n : ℤ, ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (f (rotationIterate θ (k - n) x) : ℂ) * v x k = ev n * v x k := by
    intro n
    filter_upwards [polarConjugate_multiplier_coordinate_ae θ _ C hC
      hf.complex_ofReal hb n v, Lp.coeFn_smul (ev n) v] with x hx hs k
    have h := congrArg (fun w : Hilbert => w x k) (heigen n)
    rw [hx, hs] at h
    exact h
  have havoid : ∀ k : ℤ, ∀ᵐ x ∂baseMeasure,
      ¬ ∀ n : ℤ, (f (rotationIterate θ (k - n) x) : ℂ) = ev n := by
    intro k
    exact measure_eq_zero_iff_ae_notMem.mp
      (coefficient_fiber_null_of_orbit_fiber_null θ f hnull ev k)
  have hvzero : v = 0 := by
    apply Lp.ext
    filter_upwards [ae_all_iff.mpr hcoord, ae_all_iff.mpr havoid,
      Lp.coeFn_zero Fiber 2 baseMeasure] with x hx hav hz
    rw [hz]
    apply lp.ext
    funext k
    change v x k = 0
    by_contra hvk
    apply hav k
    intro n
    exact mul_right_cancel₀ hvk (hx n k)
  exact hvzero

theorem fullPolarAlgebra_multiplier_diffuse_of_null_fibers
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hcount : ∃ R : Set ℝ, R.Countable ∧ ∀ᵐ x ∂baseMeasure, f x ∈ R)
    (hnull : ∀ z : ℤ → ℝ,
      baseMeasure {x | ∀ n : ℤ, f (rotationIterate θ n x) = z n} = 0) :
    IsDiffuseVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator
        (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb)) := by
  apply generated_isDiffuse_of_purePoint_no_jointEigenvectors
  · exact fullPolarAlgebra_multiplier_abelian θ f C hC hf hb
  · exact polarConjugate_multiplier_hasCountablyAtomicSpectralType θ f C hC hf hb hcount
  · exact jointEigenspace_polarConjugates_eq_bot_of_null_fibers θ f C hC hf hb hnull

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductWeightNonconstant
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton _root_.OAI.Invariant233.negLogCost_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem logarithmicCost_coordinate_increase
    (θ c : ℕ → ℝ) (j : ℕ) (x y : Base)
    (hxy : ∀ i, i ≠ j → y i = x i)
    (hx : ⌊circleRepresentative (x j) + θ j⌋ = (0 : ℤ))
    (hy : ⌊circleRepresentative (y j) + θ j⌋ = (1 : ℤ)) :
    logarithmicCost θ c y = ENNReal.ofReal (c j) + logarithmicCost θ c x := by
  unfold logarithmicCost
  rw [ENNReal.tsum_eq_add_tsum_ite j]
  conv_rhs => arg 2; rw [ENNReal.tsum_eq_add_tsum_ite j]
  simp only [hx, hy, Int.cast_zero, Int.cast_one, mul_zero, mul_one,
    ENNReal.ofReal_zero, zero_add]
  congr 1
  apply tsum_congr
  intro i
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, hxy i hij]

theorem measure_representative_cylinder (j : ℕ) {a : ℝ} (ha : a ≤ 1) :
    baseMeasure {x | circleRepresentative (x j) ∈ Ico (0 : ℝ) a} =
      ENNReal.ofReal a := by
  have hmp : MeasurePreserving
      (fun x : Base => circleRepresentative (x j)) baseMeasure
      (volume.restrict (Ico (0 : ℝ) 1)) :=
    CocycleSupport.measurePreserving_productRepresentative j
  change baseMeasure ((fun x : Base => circleRepresentative (x j)) ⁻¹' Ico (0 : ℝ) a) = _
  rw [← Measure.map_apply hmp.measurable measurableSet_Ico, hmp.map_eq,
    Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr (Ico_subset_Ico le_rfl ha), Real.volume_Ico, sub_zero]

theorem weight_not_ae_constant_of_ae_ne_zero
    (θ c : ℕ → ℝ) (j : ℕ) (hθj : 0 < θ j ∧ θ j < 1) (hcj : 0 < c j)
    (hne : ∀ᵐ x ∂baseMeasure, weight θ c x ≠ 0) :
    ¬ ∃ a : ℝ, weight θ c =ᵐ[baseMeasure] Function.const Base a := by
  rintro ⟨a, ha⟩
  let α : ℕ → ℝ := fun i => if i = j then 1 - θ j else 0
  let σ : Base → Base := rotation α
  have hmp : MeasurePreserving σ baseMeasure baseMeasure := measurePreserving_rotation α
  let d : ℝ := min (θ j) (1 - θ j)
  have hdpos : 0 < d := lt_min hθj.1 (by linarith [hθj.2])
  have hdθ : d ≤ θ j := min_le_left _ _
  have hdθ' : d ≤ 1 - θ j := min_le_right _ _
  have hd1 : d ≤ 1 := le_trans hdθ hθj.2.le
  have hs : baseMeasure {x | circleRepresentative (x j) ∈ Ico (0 : ℝ) d} ≠ 0 := by
    rw [measure_representative_cylinder j hd1]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hdpos)
  have hall : ∀ᵐ x ∂baseMeasure,
      weight θ c x = a ∧ weight θ c (σ x) = a ∧ weight θ c x ≠ 0 := by
    filter_upwards [ha, hmp.quasiMeasurePreserving.ae ha, hne] with x hx hy hn
    exact ⟨hx, hy, hn⟩
  obtain ⟨x, hx, hxvalue, hyvalue, hxne⟩ :=
    ((frequently_ae_iff.mpr hs).and_eventually hall).exists
  have hj : σ x j = x j + ((1 - θ j : ℝ) : Circle) := by simp [σ, rotation, α]
  have hother (i : ℕ) (hij : i ≠ j) : σ x i = x i := by
    simp [σ, rotation, α, hij]
  have hrep : circleRepresentative (σ x j) = circleRepresentative (x j) + (1 - θ j) := by
    rw [hj]
    change ProductCocycle.representative (x j + ((1 - θ j : ℝ) : Circle)) = _
    rw [ProductCocycle.representative_add]
    apply Int.fract_eq_self.mpr
    change 0 ≤ circleRepresentative (x j) + (1 - θ j) ∧
      circleRepresentative (x j) + (1 - θ j) < 1
    constructor <;> linarith [hx.1, hx.2]
  have hfloorx : ⌊circleRepresentative (x j) + θ j⌋ = (0 : ℤ) := by
    apply Int.floor_eq_zero_iff.mpr
    constructor <;> linarith [hx.1, hx.2]
  have hfloory : ⌊circleRepresentative (σ x j) + θ j⌋ = (1 : ℤ) := by
    rw [hrep]
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith [hx.1, hx.2]
  have hincrease := logarithmicCost_coordinate_increase θ c j x (σ x) hother hfloorx hfloory
  have hequal : logarithmicCost θ c (σ x) = logarithmicCost θ c x := by
    rw [← negLogCost_weight, ← negLogCost_weight, hxvalue, hyvalue]
  have hfinite : logarithmicCost θ c x ≠ ∞ := fun h =>
    hxne ((weight_eq_zero_iff θ c x).mpr h)
  have hlt := ENNReal.lt_add_right hfinite (ne_of_gt (ENNReal.ofReal_pos.mpr hcj))
  rw [add_comm, ← hincrease, hequal] at hlt
  exact (lt_irrefl _) hlt

theorem weight_not_ae_constant (θ c : ℕ → ℝ)
    (hadm : AdmissibleAnglesAndCosts θ c) :
    ¬ ∃ a : ℝ, weight θ c =ᵐ[baseMeasure] Function.const Base a := by
  apply weight_not_ae_constant_of_ae_ne_zero θ c 0
    ⟨(hadm.1 0).1, (hadm.1 0).2.1⟩ (hadm.1 0).2.2
  exact (ae_weight_pos θ c (fun i => (hadm.1 i).1.le)
    (fun i => (hadm.1 i).2.2.le) hadm.2.1).mono (fun _ hx => hx.ne')

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductPolarComplete
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel

theorem productPolarStructure_of_weight_not_ae_constant
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c)
    (hnonconstant : ¬ ∃ a : ℝ, weight θ c =ᵐ[baseMeasure] Function.const Base a) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  apply productPolarStructure_of_weightOrbitDiffuse θ c
    (fun i => ⟨(hadm.1 i).1.le, (hadm.1 i).2.1⟩)
    (fun i => (hadm.1 i).2.2.le) hadm.2.1
  rw [star_shift_weightedOperator_eq_multiplier]
  obtain ⟨S, hS, -, hmem⟩ := ae_weight_mem_countable θ c
    (fun i => ⟨(hadm.1 i).1.le, (hadm.1 i).2.1⟩)
    (fun i => (hadm.1 i).2.2.le) hadm.2.1
  exact fullPolarAlgebra_multiplier_diffuse_of_null_fibers θ (weight θ c) 1
    (by norm_num) (measurable_weight θ c) (weight_complex_norm_le_one θ c)
    ⟨S, hS, hmem⟩
    (rotation_joint_fiber_measure_zero hadm.2.2 (measurable_weight θ c) hnonconstant)

theorem productPolarStructure_of_admissible_oai
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) :=
  productPolarStructure_of_weight_not_ae_constant θ c hadm
    (weight_not_ae_constant θ c hadm)

end Invariant233.ProductModel

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.productPolarStructure_of_admissible_oai := @OAI.Invariant233.ProductModel.productPolarStructure_of_admissible_oai
