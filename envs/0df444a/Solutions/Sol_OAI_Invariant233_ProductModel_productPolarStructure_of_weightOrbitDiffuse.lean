-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.productPolarStructure_of_weightOrbitDiffuse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:08.195056+00:00
-- url     : https://prove2.me/submissions/2655921e-f458-4afb-908a-24e9b8959419

import Mathlib
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

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

theorem topologicalClosure_iSup_jointEigenspace_eq_top_of_basis
    {ι J : Type*} [Countable ι] [Countable J] (b : HilbertBasis ι ℂ E)
    (f : ι → X → J → ℂ) (hf : ∀ i, Measurable (f i))
    {C : Set (J → ℂ)} (hC : C.Countable)
    (hmem : ∀ i, ∀ᵐ x ∂μ, f i x ∈ C)
    (T : J → Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hT : ∀ (j : J) (v : Lp E 2 μ) i, ∀ᵐ x ∂μ,
      inner ℂ (b i) (T j v x) = f i x j * inner ℂ (b i) (v x)) :
    (⨆ y : C, ⨅ j : J, Module.End.eigenspace (T j).toLinearMap (y.val j)).topologicalClosure = ⊤ := by
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
    have heigen : w ∈ ⨅ j : J, Module.End.eigenspace (T j).toLinearMap (y.val j) := by
      rw [Submodule.mem_iInf]
      intro j
      rw [Module.End.mem_eigenspace_iff]
      apply Lp.ext
      have hTall : ∀ᵐ x ∂μ, ∀ k, inner ℂ (b k) (T j w x) =
          f k x j * inner ℂ (b k) (w x) := ae_all_iff.2 (hT j w)
      filter_upwards [hTall, Lp.coeFn_smul (y.val j) w, hw] with x hTx hsx hwx
      change (T j w : X → E) x = (y.val j • w : Lp E 2 μ) x
      rw [hsx]
      apply b.repr.injective
      ext k
      rw [b.repr_apply_apply, b.repr_apply_apply, hTx k]
      change f k x j * inner ℂ (b k) (w x) = inner ℂ (b k) (y.val j • w x)
      rw [inner_smul_right]
      by_cases hx : x ∈ s
      · have hwv : w x = inner ℂ (b i) (v x) • b i :=
          hwx.trans (Set.indicator_of_mem hx _)
        by_cases hki : k = i
        · subst k
          have hxy : f i x = y.val := hx
          rw [hxy]
        · rw [hwv, inner_smul_right, b.orthonormal.inner_eq_zero hki]
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

theorem topologicalClosure_iSup_jointEigenspace_eq_top_of_sequence
    {ι J : Type*} [Countable ι] [Countable J]
    (f : ι → X → J → ℂ) (hf : ∀ i, Measurable (f i))
    {C : Set (J → ℂ)} (hC : C.Countable)
    (hmem : ∀ i, ∀ᵐ x ∂μ, f i x ∈ C)
    (T : J → Lp (lp (fun _ : ι => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ι => ℂ) 2) 2 μ)
    (hT : ∀ j (v : Lp (lp (fun _ : ι => ℂ) 2) 2 μ) i,
      ∀ᵐ x ∂μ, T j v x i = f i x j * v x i) :
    (⨆ y : C, ⨅ j : J, Module.End.eigenspace (T j).toLinearMap (y.val j)).topologicalClosure = ⊤ := by
  let b : HilbertBasis ι ℂ (lp (fun _ : ι => ℂ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb (v : lp (fun _ : ι => ℂ) 2) (i : ι) : inner ℂ (b i) v = v i :=
    (b.repr_apply_apply v i).symm
  apply topologicalClosure_iSup_jointEigenspace_eq_top_of_basis b f hf hC hmem T
  intro j v i
  simpa only [hb] using hT j v i

theorem finite_orbit_family_dense_jointEigenspaces
    {J : Type*} [Finite J] (n : J → ℤ)
    (σ : ℤ → X → X) (hσ : ∀ k, MeasurePreserving (σ k) μ μ)
    (f : X → ℂ) (hf : Measurable f)
    (hcount : ∃ C : Set ℂ, C.Countable ∧ ∀ᵐ x ∂μ, f x ∈ C)
    (T : J → Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ)
    (hT : ∀ j (v : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, T j v x k = f (σ (k - n j) x) * v x k) :
    ∃ C : Set (J → ℂ), C.Countable ∧
      (⨆ y : C, ⨅ j : J, Module.End.eigenspace (T j).toLinearMap (y.val j)).topologicalClosure = ⊤ := by
  obtain ⟨C, hC, hmem⟩ := hcount
  let R : Set (J → ℂ) := {g | ∀ j, g j ∈ C}
  have hR : R.Countable := Set.countable_pi (fun _ => hC)
  refine ⟨R, hR, ?_⟩
  apply topologicalClosure_iSup_jointEigenspace_eq_top_of_sequence
    (fun k x j => f (σ (k - n j) x)) _ hR _ T hT
  · intro k
    exact Measurable.of_eval (fun j => hf.comp (hσ (k - n j)).measurable)
  · intro k
    exact ae_all_iff.2 (fun j => (hσ (k - n j)).quasiMeasurePreserving.ae hmem)

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

theorem commute_starProjection_of_reducing (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (T : H →L[ℂ] H)
    (hT : ∀ x ∈ K, T x ∈ K) (hTstar : ∀ x ∈ K, star T x ∈ K) :
    Commute K.starProjection T := by
  apply ContinuousLinearMap.ext
  intro x
  change K.starProjection (T x) = T (K.starProjection x)
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · apply hT
    exact Submodule.coe_mem (K.orthogonalProjectionOnto x)
  · have horth : Kᗮ ∈ Module.End.invtSubmodule T.toLinearMap :=
      ContinuousLinearMap.orthogonal_mem_invtSubmodule hTstar
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at horth
    rw [← map_sub]
    exact horth _ (K.sub_starProjection_mem_orthogonal x)

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

theorem jointEigenprojection_mem_commutant (D : ι → H →L[ℂ] H) (ev : ι → ℂ)
    (hD : ∀ i, IsSelfAdjoint (D i)) :
    jointEigenprojection D ev ∈ (vonNeumannGenerated (Set.range D)).commutant := by
  rw [mem_commutant_vonNeumannGenerated_iff]
  rintro _ ⟨i, rfl⟩
  have h : Commute (jointEigenprojection D ev) (D i) := by
    apply commute_starProjection_of_reducing
    · intro x hx
      rw [(mem_jointEigenspace.mp hx) i]
      exact (jointEigenspace D ev).smul_mem _ hx
    · intro x hx
      rw [(hD i).star_eq, (mem_jointEigenspace.mp hx) i]
      exact (jointEigenspace D ev).smul_mem _ hx
  exact ⟨h.eq.symm, by simpa only [(hD i).star_eq] using h.eq.symm⟩

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

theorem atomic_generated_of_jointEigenprojection_atoms {A : Type*}
    (D : ι → H →L[ℂ] H) (ev : A → ι → ℂ)
    (hD : ∀ i, IsSelfAdjoint (D i))
    (hdense : (⨆ a, jointEigenspace D (ev a)).topologicalClosure = ⊤)
    (hatom : ∀ a, jointEigenprojection D (ev a) ≠ 0 →
      IsProjectionAtom (vonNeumannGenerated (Set.range D)) (jointEigenprojection D (ev a))) :
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated (Set.range D)) := by
  intro p hp hpp hp0
  obtain ⟨a, ha⟩ := exists_mul_jointEigenprojection_ne_zero D ev hdense p hp0
  let q := jointEigenprojection D (ev a)
  have hqm : q ∈ vonNeumannGenerated (Set.range D) := jointEigenprojection_mem_generated D _
  have hqp : IsStarProjection q := isStarProjection_jointEigenprojection D _
  have hq0 : q ≠ 0 := by
    intro hq
    apply ha
    change p * q = 0
    rw [hq, mul_zero]
  have hpq : Commute p q :=
    VonNeumannAlgebra.mem_commutant_iff.mp (jointEigenprojection_mem_commutant D _ hD) p hp
  have hqa := hatom a hq0
  have hpqq : (p * q) * q = p * q := by
    rw [mul_assoc, hqp.isIdempotentElem.eq]
  have hpeq : p * q = q :=
    (hqa.2.2.2 (p * q) (mul_mem hp hqm) (hpp.mul hqp hpq) hpqq).resolve_left ha
  exact ⟨q, hqa, hpq.eq.symm.trans hpeq⟩

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_JointEigenspaceAlgebra
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open InnerProductSpace

namespace Invariant233.JointEigenspaceAlgebra

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commute_rankOne_of_same_eigenvalue
    {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {eig : ℝ} {x y : H}
    (hx : A x = (eig : ℂ) • x) (hy : A y = (eig : ℂ) • y) :
    Commute A (rankOne ℂ x y) := by
  apply ContinuousLinearMap.ext
  intro z
  change A (rankOne ℂ x y z) = rankOne ℂ x y (A z)
  rw [rankOne_apply, rankOne_apply, map_smul, hx]
  have hadj : A.adjoint = A := hA.star_eq
  rw [← A.adjoint_inner_left z y, hadj, hy, inner_smul_left]
  simp only [Complex.conj_ofReal, smul_smul]
  rw [mul_comm]

theorem exists_scalar_on_common_eigenspace
    (A : I → H →L[ℂ] H) (hA : ∀ i, IsSelfAdjoint (A i))
    (eig : I → ℝ) (K : Submodule ℂ H)
    (hK : ∀ i, ∀ x ∈ K, A i x = (eig i : ℂ) • x)
    {B : H →L[ℂ] H}
    (hB : B ∈ Set.centralizer (Set.centralizer (Set.range A))) :
    ∃ c : ℂ, ∀ x ∈ K, B x = c • x := by
  classical
  by_cases hK0 : K = ⊥
  · refine ⟨0, ?_⟩
    intro x hx
    have hx0 : x = 0 := by simpa [hK0] using hx
    simp [hx0]
  · obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
    let d : ℂ := inner ℂ x x
    have hd : d ≠ 0 := by
      dsimp [d]
      exact inner_self_ne_zero.mpr hx0
    refine ⟨inner ℂ x (B x) / d, ?_⟩
    intro y hyK
    have hrank : rankOne ℂ y x ∈ Set.centralizer (Set.range A) := by
      intro C hC
      obtain ⟨i, rfl⟩ := hC
      exact (commute_rankOne_of_same_eigenvalue (hA i) (hK i y hyK) (hK i x hxK)).eq
    have hcomm := hB (rankOne ℂ y x) hrank
    have heq : d • B y = inner ℂ x (B x) • y := by
      have heval := congrArg (fun C : H →L[ℂ] H => C x) hcomm
      simpa only [mul_apply_eq_comp, rankOne_apply, map_smul] using heval.symm
    calc
      B y = d⁻¹ • (d • B y) := by simp [hd]
      _ = d⁻¹ • (inner ℂ x (B x) • y) := by rw [heq]
      _ = (inner ℂ x (B x) / d) • y := by
        rw [smul_smul, div_eq_mul_inv, mul_comm]

theorem eq_zero_or_eq_joint_projection_of_le
    (A : I → H →L[ℂ] H) (hA : ∀ i, IsSelfAdjoint (A i))
    (eig : I → ℝ) (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (hK : ∀ i, ∀ x ∈ K, A i x = (eig i : ℂ) • x)
    {q : H →L[ℂ] H} (hq : IsStarProjection q)
    (hqmem : q ∈ Set.centralizer (Set.centralizer (Set.range A)))
    (hle : q ≤ K.starProjection) : q = 0 ∨ q = K.starProjection := by
  have hp : IsStarProjection K.starProjection := isStarProjection_starProjection
  by_cases hp0 : K.starProjection = 0
  · left
    exact le_antisymm (hp0 ▸ hle) hq.nonneg
  · obtain ⟨c, hc⟩ := exists_scalar_on_common_eigenspace A hA eig K hK hqmem
    have hqp : q * K.starProjection = q := (hq.le_iff_mul_eq_left hp).1 hle
    have hqeq : q = c • K.starProjection := by
      rw [← hqp]
      apply ContinuousLinearMap.ext
      intro x
      exact hc _ (K.starProjection_apply_mem x)
    have hscalar : (c * c) • K.starProjection = c • K.starProjection := by
      have hidem := hq.isIdempotentElem.eq
      rw [hqeq] at hidem
      simpa only [smul_mul_assoc, mul_smul_comm, smul_smul,
        K.isIdempotentElem_starProjection.eq] using hidem
    have hcid : IsIdempotentElem c := smul_left_injective ℂ hp0 hscalar
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hcid with hc0 | hc1
    · left
      simpa [hc0] using hqeq
    · right
      simpa [hc1] using hqeq

end Invariant233.JointEigenspaceAlgebra

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_JointProjectionAtomic
attribute [-instance] _root_.OAI.Invariant233.AffiliatedTransport.instCompleteSpaceSubtypeMemSubmoduleComplexClosedImageOn _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace Invariant233

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem coe_generated_range_selfAdjoint (D : ι → H →L[ℂ] H)
    (hD : ∀ i, IsSelfAdjoint (D i)) :
    (vonNeumannGenerated (Set.range D) : Set (H →L[ℂ] H)) =
      Set.centralizer (Set.centralizer (Set.range D)) := by
  rw [coe_vonNeumannGenerated]
  have hstar : star (Set.range D) ⊆ Set.range D := by
    intro T hT
    change star T ∈ Set.range D at hT
    obtain ⟨i, hi⟩ := hT
    refine ⟨i, ?_⟩
    calc
      D i = star (D i) := (hD i).star_eq.symm
      _ = T := by rw [hi, star_star]
  rw [Set.union_eq_left.mpr hstar]

theorem jointEigenprojection_isProjectionAtom (D : ι → H →L[ℂ] H)
    (hD : ∀ i, IsSelfAdjoint (D i)) (ev : ι → ℂ)
    (hp0 : jointEigenprojection D ev ≠ 0) :
    IsProjectionAtom (vonNeumannGenerated (Set.range D)) (jointEigenprojection D ev) := by
  have hK0 : jointEigenspace D ev ≠ ⊥ := by
    intro hK
    apply hp0
    ext x
    have hx := (jointEigenspace D ev).starProjection_apply_mem x
    change (jointEigenspace D ev).starProjection x = 0
    exact (le_of_eq hK) hx
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
  have hreal : ∀ i, ((ev i).re : ℂ) = ev i := by
    intro i
    apply Complex.conj_eq_iff_re.mp
    apply (hD i).isSymmetric.conj_eigenvalue_eq_self
    apply Module.End.hasEigenvalue_of_hasEigenvector
    exact ⟨Module.End.mem_eigenspace_iff.mpr ((mem_jointEigenspace.mp hxK) i), hx0⟩
  refine ⟨jointEigenprojection_mem_generated D ev,
    isStarProjection_jointEigenprojection D ev, hp0, ?_⟩
  intro q hqm hqp hle
  apply JointEigenspaceAlgebra.eq_zero_or_eq_joint_projection_of_le
    D hD (fun i => (ev i).re) (jointEigenspace D ev)
  · intro i y hy
    rw [hreal i]
    exact (mem_jointEigenspace.mp hy) i
  · exact hqp
  · change q ∈ (vonNeumannGenerated (Set.range D) : Set (H →L[ℂ] H)) at hqm
    rwa [coe_generated_range_selfAdjoint D hD] at hqm
  · exact (hqp.le_iff_mul_eq_left (isStarProjection_jointEigenprojection D ev)).mpr hle

theorem atomic_generated_of_dense_jointEigenspaces {A : Type*}
    (D : ι → H →L[ℂ] H) (ev : A → ι → ℂ)
    (hD : ∀ i, IsSelfAdjoint (D i))
    (hdense : (⨆ a, jointEigenspace D (ev a)).topologicalClosure = ⊤) :
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated (Set.range D)) := by
  apply atomic_generated_of_jointEigenprojection_atoms D ev hD hdense
  intro a
  exact jointEigenprojection_isProjectionAtom D hD (ev a)

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

theorem finite_orbit_diagonal_algebra_atomic_and_commutative
    {J : Type*} [Finite J] (n : J → ℤ)
    (σ : ℤ → X → X) (hσ : ∀ k, MeasurePreserving (σ k) μ μ)
    (f : X → ℝ) (hf : Measurable f)
    (hcount : ∃ C : Set ℝ, C.Countable ∧ ∀ᵐ x ∂μ, f x ∈ C)
    (D : J → Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ)
    (hD : ∀ j (v : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, D j v x k = (f (σ (k - n j) x) : ℂ) * v x k) :
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated (Set.range D)) ∧
      ∀ S ∈ vonNeumannGenerated (Set.range D),
        ∀ T ∈ vonNeumannGenerated (Set.range D), Commute S T := by
  have hself (j : J) : IsSelfAdjoint (D j) :=
    isSelfAdjoint_of_real_sequence_diagonal (fun k x => f (σ (k - n j) x)) (D j) (hD j)
  have hcomm (i j : J) : Commute (D i) (D j) :=
    commute_of_sequence_diagonal
      (fun k x => (f (σ (k - n i) x) : ℂ))
      (fun k x => (f (σ (k - n j) x) : ℂ)) (D i) (D j) (hD i) (hD j)
  constructor
  · have hcomplex : ∃ C : Set ℂ, C.Countable ∧ ∀ᵐ x ∂μ, (f x : ℂ) ∈ C := by
      obtain ⟨C, hC, hmem⟩ := hcount
      refine ⟨Complex.ofReal '' C, hC.image _, ?_⟩
      filter_upwards [hmem] with x hx
      exact Set.mem_image_of_mem Complex.ofReal hx
    obtain ⟨C, _hC, hdense⟩ :=
      MultiplicationPurePoint.finite_orbit_family_dense_jointEigenspaces n σ hσ
        (fun x => (f x : ℂ)) (Complex.continuous_ofReal.measurable.comp hf) hcomplex D hD
    apply atomic_generated_of_dense_jointEigenspaces D (fun y : C => y.val) hself
    simpa only [jointEigenspace] using hdense
  · intro S hS T hT
    exact commute_of_mem_generated_selfAdjoint_family D hself hcomm hS hT

end Invariant233

end

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
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_PolarFactor
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.PolarFactor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem star_mul_self_unitary_mul (U : unitary (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    star ((U : H →L[ℂ] H) * A) * ((U : H →L[ℂ] H) * A) = star A * A := by
  rw [star_mul]
  calc
    (star A * star (U : H →L[ℂ] H)) * ((U : H →L[ℂ] H) * A) =
        star A * (star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) * A := by
          simp only [mul_assoc]
    _ = star A * A := by simp

theorem abs_unitary_mul (U : unitary (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    CFC.abs ((U : H →L[ℂ] H) * A) = CFC.abs A := by
  unfold CFC.abs
  rw [star_mul_self_unitary_mul]

theorem abs_unitary_mul_of_nonneg (U : unitary (H →L[ℂ] H))
    (A : H →L[ℂ] H) (hA : 0 ≤ A) :
    CFC.abs ((U : H →L[ℂ] H) * A) = A := by
  rw [abs_unitary_mul, CFC.abs_of_nonneg A hA]

end Invariant233.PolarFactor

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_WeightedShiftPolar
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal InnerProductSpace ComplexOrder
namespace Invariant233.WeightedShift.PolarSupport

local instance hilbertNontrivial_r64fe46_1 : Nontrivial Hilbert := by
  refine ⟨⟨0, lp.single 2 0 1, ?_⟩⟩
  intro h
  have hh := congrArg (fun ξ : Hilbert => ξ 0) h
  simp at hh
local instance weightedShiftPolarRealModule_r64fe46_1 : Module ℝ (Hilbert →L[ℂ] Hilbert) :=
  Module.complexToReal (Hilbert →L[ℂ] Hilbert)
local instance weightedShiftPolarFunctionalCalculus_r64fe46_1 : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert →L[ℂ] Hilbert) IsSelfAdjoint := by
  infer_instance
private theorem star_diagonal_polar (w : Weight) :
    star (diagonal w) = diagonal (star w) := by
  ext ξ k
  have hsingle : diagonal w (lp.single 2 k 1) = lp.single 2 k (w k) := by
    ext j
    by_cases hj : j = k
    · subst j; simp
    · simp [lp.single_apply, hj]
  have h := (diagonal w).adjoint_inner_right (lp.single 2 k 1) ξ
  rw [hsingle, lp.inner_single_left, lp.inner_single_left] at h
  simpa [ContinuousLinearMap.star_eq_adjoint, lp.star_apply, mul_comm] using h

private theorem diagonal_mul_polar (w v : Weight) :
    diagonal (w * v) = diagonal w * diagonal v := by
  ext ξ k
  simp [mul_assoc]

theorem star_sqrtRealWeight_mul (w : Weight) (hw : ∀ k, 0 ≤ w k) :
    star (sqrtRealWeight w) * sqrtRealWeight w = w := by
  ext k
  have hk := Complex.nonneg_iff.mp (hw k)
  apply Complex.ext
  · simp [sqrtRealWeight, Real.mul_self_sqrt hk.1]
  · simpa [sqrtRealWeight, lp.star_apply] using hk.2

theorem diagonal_nonneg (w : Weight) (hw : ∀ k, 0 ≤ w k) :
    0 ≤ diagonal w := by
  rw [← star_sqrtRealWeight_mul w hw, diagonal_mul_polar, ← star_diagonal_polar]
  exact star_mul_self_nonneg _

end Invariant233.WeightedShift.PolarSupport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_FieldDiagonalPolar
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace ComplexOrder
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldDiagonal_nonneg (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)
    (hpos : ∀ᵐ x ∂μ, ∀ k, 0 ≤ a x k) :
    0 ≤ fieldDiagonal a C hC ha hm := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply ContinuousLinearMap.isPositive_def.mpr
  constructor
  · intro f g
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [fieldDiagonal_ae a C hC ha hm f,
      fieldDiagonal_ae a C hC ha hm g, hpos] with x hf hg hx
    change inner ℂ ((fieldDiagonal a C hC ha hm f) x) (g x) =
      inner ℂ (f x) ((fieldDiagonal a C hC ha hm g) x)
    rw [hf, hg]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (PolarSupport.diagonal_nonneg (a x) hx) |>.isSymmetric (f x) (g x)
  · intro f
    change 0 ≤ (inner ℂ (fieldDiagonal a C hC ha hm f) f).re
    rw [L2.inner_def]
    change 0 ≤ RCLike.re (∫ x, inner ℂ ((fieldDiagonal a C hC ha hm f) x) (f x) ∂μ)
    rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) (fieldDiagonal a C hC ha hm f) f)]
    apply integral_nonneg_of_ae
    filter_upwards [fieldDiagonal_ae a C hC ha hm f, hpos] with x hf hx
    rw [hf]
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (PolarSupport.diagonal_nonneg (a x) hx)).re_inner_nonneg_left (f x)

theorem star_global_shift (n : ℤ) :
    star ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ) =
      (shift (-n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  symm
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldShift_ae (-n) f, fieldShift_ae n g] with x hf hg
  rw [hf, hg]
  have hinv : shift (-n) (f x) = (shift n).symm (f x) := by
    apply (shift n).injective
    ext k
    simp [shift_apply]
  rw [hinv]
  have h := (shift n).inner_map_map ((shift n).symm (f x)) (g x)
  simpa only [(shift n).apply_symm_apply] using h.symm

theorem global_shift_mem_unitary (n : ℤ) :
    (shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ∈
      unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  apply Unitary.mem_iff.mpr
  rw [star_global_shift, ← fieldShift_add, ← fieldShift_add]
  simpa using And.intro (fieldShift_zero (μ := μ)) (fieldShift_zero (μ := μ))

attribute [local instance] OAI.Invariant233.WeightedShift.fieldDiagonalPolarRealModule
attribute [local instance] OAI.Invariant233.WeightedShift.fieldDiagonalPolarFunctionalCalculus
theorem abs_global_shift_mul_fieldDiagonal (n : ℤ) (a : X → Weight)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)
    (hpos : ∀ᵐ x ∂μ, ∀ k, 0 ≤ a x k) :
    CFC.abs ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
      fieldDiagonal a C hC ha hm) = fieldDiagonal a C hC ha hm :=
  PolarFactor.abs_unitary_mul_of_nonneg
    ⟨_, global_shift_mem_unitary n⟩ _ (fieldDiagonal_nonneg a C hC ha hm hpos)

end Invariant233.WeightedShift

end

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

end InvariantProjection.PolarStructure

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

theorem finitePolarAlgebra_multiplier_atomic
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hcount : ∃ R : Set ℝ, R.Countable ∧ ∀ᵐ x ∂baseMeasure, f x ∈ R)
    (F : Finset ℤ) :
    IsAbelianVonNeumannAlgebra
      (finitePolarAlgebra shiftOperator (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb) F) ∧
    IsAtomicVonNeumannAlgebra
      (finitePolarAlgebra shiftOperator (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb) F) := by
  let B := multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb
  let D : F → Hilbert →L[ℂ] Hilbert := fun j => polarConjugate shiftOperator B j.val
  have hD : ∀ j (v : Hilbert) k, ∀ᵐ x ∂baseMeasure,
      D j v x k = (f (rotationIterate θ (k - j.val) x) : ℂ) * v x k := by
    intro j v k
    exact (polarConjugate_multiplier_coordinate_ae θ _ C hC hf.complex_ofReal hb j.val v).mono
      (fun x hx => hx k)
  obtain ⟨hat, hab⟩ := finite_orbit_diagonal_algebra_atomic_and_commutative
    (fun j : F => j.val) (rotationIterate θ) (rotationIterate_measurePreserving_polar θ)
    f hf hcount D hD
  have hgen : {A | ∃ n ∈ F, A = polarConjugate shiftOperator B n} = Set.range D := by
    ext A
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, j.property, rfl⟩
  change IsAbelianVonNeumannAlgebra (vonNeumannGenerated _) ∧
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated _)
  rw [hgen]
  exact ⟨fun S T hS hT => hab S hS T hT, hat⟩

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

theorem multiplier_hasCountablyAtomicSpectralType
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hcount : ∃ R : Set ℝ, R.Countable ∧ ∀ᵐ x ∂baseMeasure, f x ∈ R) :
    HasCountablyAtomicSpectralType
      (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb) := by
  obtain ⟨R, hR, hmem⟩ := hcount
  let S : Set ℂ := Complex.ofReal '' R
  have hS : S.Countable := hR.image _
  refine ⟨S, hS, ?_⟩
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hbasis (v : Fiber) (k : ℤ) : inner ℂ (b k) v = v k :=
    (b.repr_apply_apply v k).symm
  have hmeas (k : ℤ) : Measurable (fun x => (f (rotationIterate θ k x) : ℂ)) := by
    exact hf.complex_ofReal.comp (rotationIterate_measurePreserving_polar θ k).measurable
  have hrange (k : ℤ) : ∀ᵐ x ∂baseMeasure, (f (rotationIterate θ k x) : ℂ) ∈ S := by
    filter_upwards [(rotationIterate_measurePreserving_polar θ k).quasiMeasurePreserving.ae hmem]
      with x hx
    exact Set.mem_image_of_mem Complex.ofReal hx
  apply MultiplicationPurePoint.topologicalClosure_iSup_eigenspace_eq_top_of_basis b
    (fun k x => (f (rotationIterate θ k x) : ℂ)) hmeas hS hrange
  intro v k
  simpa only [hbasis] using
    (multiplier_coordinate_ae θ _ C hC hf.complex_ofReal hb v).mono (fun x hx => hx k)

theorem multiplier_injective_of_ae_ne_zero
    (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hne : ∀ᵐ x ∂baseMeasure, g x ≠ 0) :
    Function.Injective (multiplier θ g C hC hg hb) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Lp.ext
  have hcoord : ∀ᵐ x ∂baseMeasure, ∀ k, g (rotationIterate θ k x) ≠ 0 :=
    ae_all_iff.mpr fun k => (rotationIterate_measurePreserving_polar θ k).quasiMeasurePreserving.ae hne
  have hout : (multiplier θ g C hC hg hb v : Base → Fiber) =ᵐ[baseMeasure] 0 := by
    rw [hv]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [multiplier_coordinate_ae θ g C hC hg hb v, hcoord, hout,
    Lp.coeFn_zero Fiber 2 baseMeasure] with x hx hn hz hzero
  rw [hzero]
  apply lp.ext
  funext k
  have hprod : g (rotationIterate θ k x) * v x k = 0 := by
    rw [← hx k, hz]
    rfl
  exact (mul_eq_zero.mp hprod).resolve_left (hn k)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductPolarModulusComplex
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexOrder
namespace Invariant233.ProductModel.GlobalPolarSupport

attribute [local instance] OAI.Invariant233.ProductModel.GlobalPolarSupport.productPolarModulusComplexRealModule
local instance productPolarModulusComplexFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ (Hilbert →L[ℂ] Hilbert) IsSelfAdjoint := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem operatorModulus_shift_mul_multiplier (θ : ℕ → ℝ) (g : Base → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hpos : ∀ x, 0 ≤ g x) :
    operatorModulus (shiftOperator * multiplier θ g C hC hg hb) =
      multiplier θ g C hC hg hb := by
  change CFC.abs (shiftOperator * multiplier θ g C hC hg hb) = _
  apply WeightedShift.abs_global_shift_mul_fieldDiagonal
  exact Filter.Eventually.of_forall fun x k => hpos (rotationIterate θ k x)

theorem shiftOperator_mem_unitary : shiftOperator ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  WeightedShift.global_shift_mem_unitary 1

theorem weightedOperator_eq_shift_mul_modulus (θ c : ℕ → ℝ) :
    weightedOperator θ c = shiftOperator * operatorModulus (weightedOperator θ c) := by
  simp only [weightedOperator, ← ContinuousLinearMap.mul_def]
  rw [operatorModulus_shift_mul_multiplier]
  intro x
  exact Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg, rfl⟩

theorem operatorModulus_weightedOperator (θ c : ℕ → ℝ)
    (hg : Measurable fun x => (weight θ c x : ℂ))
    (hb : ∀ x, ‖(weight θ c x : ℂ)‖ ≤ 1) :
    operatorModulus (weightedOperator θ c) =
      multiplier θ (fun x => (weight θ c x : ℂ)) 1 (by norm_num) hg hb := by
  change operatorModulus (shiftOperator *
    multiplier θ (fun x => (weight θ c x : ℂ)) 1 (by norm_num) hg hb) = _
  apply operatorModulus_shift_mul_multiplier
  intro x
  exact Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg, rfl⟩

end Invariant233.ProductModel.GlobalPolarSupport

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

theorem finitePolarAlgebra_weight_atomic (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (F : Finset ℤ) :
    IsAbelianVonNeumannAlgebra
      (finitePolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c) F) ∧
    IsAtomicVonNeumannAlgebra
      (finitePolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c) F) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  obtain ⟨S, hS, -, hmem⟩ := ae_weight_mem_countable θ c hθ01 hc hθ
  exact finitePolarAlgebra_multiplier_atomic θ (weight θ c) 1 (by norm_num)
    (measurable_weight θ c) (weight_complex_norm_le_one θ c) ⟨S, hS, hmem⟩ F

theorem fullPolarAlgebra_weight_abelian (θ c : ℕ → ℝ) :
    IsAbelianVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c)) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  exact fullPolarAlgebra_multiplier_abelian θ (weight θ c) 1 (by norm_num)
    (measurable_weight θ c) (weight_complex_norm_le_one θ c)

theorem weight_hasCountablyAtomicSpectralType (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) :
    HasCountablyAtomicSpectralType (star shiftOperator * weightedOperator θ c) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  obtain ⟨S, hS, -, hmem⟩ := ae_weight_mem_countable θ c hθ01 hc hθ
  exact multiplier_hasCountablyAtomicSpectralType θ (weight θ c) 1 (by norm_num)
    (measurable_weight θ c) (weight_complex_norm_le_one θ c) ⟨S, hS, hmem⟩

theorem weight_multiplier_injective (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    Function.Injective (star shiftOperator * weightedOperator θ c) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  apply multiplier_injective_of_ae_ne_zero
  filter_upwards [ae_weight_pos θ c hθ0 hc hθ] with x hx
  exact_mod_cast hx.ne'

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductPolarAssembly
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductModel

theorem operatorModulus_eq_star_shift_weightedOperator (θ c : ℕ → ℝ) :
    operatorModulus (weightedOperator θ c) = star shiftOperator * weightedOperator θ c := by
  rw [star_shift_weightedOperator_eq_multiplier]
  exact GlobalPolarSupport.operatorModulus_weightedOperator θ c
    (measurable_weight θ c).complex_ofReal (weight_complex_norm_le_one θ c)

theorem productPolarStructure_of_fullPolarDiffuse
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hdiff : IsDiffuseVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (operatorModulus (weightedOperator θ c)))) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  have hu := Unitary.mem_iff.mp GlobalPolarSupport.shiftOperator_mem_unitary
  have hmod := operatorModulus_eq_star_shift_weightedOperator θ c
  refine ⟨hu.1, hu.2, GlobalPolarSupport.weightedOperator_eq_shift_mul_modulus θ c,
    ?_, ?_, ?_, ?_, hdiff⟩
  · rw [hmod]
    exact weight_multiplier_injective θ c (fun i => (hθ01 i).1) hc hθ
  · rw [hmod]
    exact weight_hasCountablyAtomicSpectralType θ c hθ01 hc hθ
  · intro F
    rw [hmod]
    exact finitePolarAlgebra_weight_atomic θ c hθ01 hc hθ F
  · rw [hmod]
    exact fullPolarAlgebra_weight_abelian θ c

theorem productPolarStructure_of_weightOrbitDiffuse_oai
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hdiff : IsDiffuseVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c))) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  apply productPolarStructure_of_fullPolarDiffuse θ c hθ01 hc hθ
  rwa [operatorModulus_eq_star_shift_weightedOperator]

end Invariant233.ProductModel

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.productPolarStructure_of_weightOrbitDiffuse_oai := @OAI.Invariant233.ProductModel.productPolarStructure_of_weightOrbitDiffuse_oai
