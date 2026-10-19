-- Prove2me | solution 1 for OAI.KervaireCurrentHomotopy.integral_eval_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:00:49.813988+00:00
-- url     : https://prove2.me/submissions/ebc1e011-b96e-4ed5-9bc2-a2ee344939de

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean:L126-L185
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireCurrentHomotopy.integral_eval_constant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Theorems.Thm_OAI_KervaireClosedCurrent_contDiff_multilinear_eval
import Theorems.Thm_OAI_KervaireHaarFlow_hasDerivAt_integral_compact

-- ---- from OAI.GroupTheory.Kervaire.HaarCurrents ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology

namespace KervaireHaarFlow

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

omit [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S] [NormedSpace ℝ E] in
lemma hasCompactSupport_of_compact (f : S → E) : HasCompactSupport f :=
  (isClosed_closure : IsClosed (tsupport f)).isCompact

omit [SecondCountableTopology S] [NormedSpace ℝ E] in
lemma continuous_integrable {f : S → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (hasCompactSupport_of_compact f)

end KervaireHaarFlow

open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff

namespace KervaireClosedCurrent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Evaluation of a smooth form on smooth vector fields is smooth. -/
lemma contDiff_eval_fields {n : ℕ} {form : E → E [⋀^Fin n]→L[ℝ] F}
    {V : Fin n → E → E} (hf : ContDiff ℝ ∞ form) (hV : ∀ i, ContDiff ℝ ∞ (V i)) :
    ContDiff ℝ ∞ (fun x ↦ form x (V · x)) := by
  exact contDiff_multilinear_eval
    ((toContinuousMultilinearMapCLM ℝ : (E [⋀^Fin n]→L[ℝ] F) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F).contDiff.comp hf) hV

end KervaireClosedCurrent

namespace KervaireCurrentHomotopy
open KervaireClosedCurrent KervaireHaarFlow VectorField ContinuousAlternatingMap
open scoped ContDiff

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

/-- A moving-frame homotopy formula for a closed current, proved from the actual exterior
 derivative identity and differentiation under a compact-parameter integral. -/
lemma integral_eval_constant {n : ℕ} {e : S → E} (he : Continuous e)
    {form : (ℝ × E) → (ℝ × E) [⋀^Fin (n+1)]→L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ form)
    {V : Fin (n+2) → (ℝ × E) → (ℝ × E)} (hV : ∀ i, ContDiff ℝ ∞ (V i))
    (hVzero : ∀ p, V 0 p = (1, 0))
    (hdiv : ∀ (t : ℝ) (i : Fin (n+2)), i ≠ 0 → ∀ (g : (ℝ × E) → ℝ),
      ContDiff ℝ ∞ g →
      (∫ x, fderiv ℝ g (t,e x) (V i (t,e x)) ∂μ) = 0)
    (hbracket : ∀ (t : ℝ) (x : S) (i j : Fin (n+1)), i ≤ j →
      form (t,e x) (Matrix.vecCons (lieBracket ℝ (V i.castSucc) (V j.succ) (t,e x))
        (j.removeNth (i.castSucc.removeNth (fun l ↦ V l (t,e x))))) = 0)
    (hclosed : ∀ (t : ℝ) (x : S),
      extDeriv form (t,e x) (fun l ↦ V l (t,e x)) = 0) (t₀ t₁ : ℝ) :
    (∫ x, form (t₀,e x) ((0 : Fin (n+2)).removeNth (fun l ↦ V l (t₀,e x))) ∂μ) =
    (∫ x, form (t₁,e x) ((0 : Fin (n+2)).removeNth (fun l ↦ V l (t₁,e x))) ∂μ) := by
  let g (i : Fin (n+2)) (p : ℝ × E) := form p (i.removeNth (V · p))
  have hg (i) : ContDiff ℝ ∞ (g i) := contDiff_eval_fields hf (fun _ ↦ hV _)
  let f (t : ℝ) (x : S) := g 0 (t,e x)
  let df (t : ℝ) (x : S) := fderiv ℝ (g 0) (t,e x) (1,0)
  have hc : Continuous (fun p : ℝ × S ↦ (p.1,e p.2)) :=
    continuous_fst.prodMk (he.comp continuous_snd)
  have hfc : Continuous (Function.uncurry f) := (hg 0).continuous.comp hc
  have hdc : Continuous (Function.uncurry df) :=
    ((hg 0).continuous_fderiv (by simp)).comp hc |>.clm_apply continuous_const
  have hfd (t : ℝ) (x : S) : HasDerivAt (fun u ↦ f u x) (df t x) t := by
    exact ((hg 0).differentiable (by simp) (t,e x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (e x)))
  have formula (t : ℝ) (x : S) :
      (∑ i : Fin (n+2), (-1 : ℝ)^i.val * fderiv ℝ (g i) (t,e x) (V i (t,e x))) = 0 := by
    have hb : (∑ i : Fin (n+1), ∑ j ≥ i, (-1 : ℤ)^(i+j : ℕ) •
        form (t,e x) (Matrix.vecCons (lieBracket ℝ (V i.castSucc) (V j.succ) (t,e x))
          (j.removeNth (i.castSucc.removeNth (fun l ↦ V l (t,e x)))))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j hj
      rw [hbracket t x i j (Finset.mem_Ici.mp hj), smul_zero]
    have h := extDeriv_apply_vectorField (hf.differentiable (by simp) (t,e x))
      (fun i ↦ (hV i).differentiable (by simp) (t,e x))
    rw [hclosed t x, hb, sub_zero] at h
    simpa only [g, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one,
      smul_eq_mul] using h.symm
  have hdi (t : ℝ) : (∫ x, df t x ∂μ) = 0 := by
    have hint (i : Fin (n+2)) : Integrable
        (fun x ↦ (-1 : ℝ)^i.val * fderiv ℝ (g i) (t,e x) (V i (t,e x))) μ :=
      continuous_integrable (continuous_const.mul
        ((((hg i).continuous_fderiv (by simp)).comp (continuous_const.prodMk he)).clm_apply
          ((hV i).continuous.comp (continuous_const.prodMk he))))
    have hsum := congrArg (fun a : S → ℝ ↦ ∫ x, a x ∂μ) (funext (formula t))
    rw [integral_zero, integral_finsetSum _ (fun i _ ↦ hint i), Fin.sum_univ_succ] at hsum
    have hz (i : Fin (n+1)) : (∫ x, (-1 : ℝ)^i.succ.val *
         fderiv ℝ (g i.succ) (t,e x) (V i.succ (t,e x)) ∂μ) = 0 := by
      rw [integral_const_mul, hdiv t i.succ (Fin.succ_ne_zero _) _ (hg _), mul_zero]
    simpa only [Fin.val_zero, pow_zero, one_mul, hz, Finset.sum_const_zero,
      add_zero, hVzero, df] using hsum
  have hd (t : ℝ) : HasDerivAt (fun u ↦ ∫ x, f u x ∂μ) 0 t := by
    simpa only [hdi] using hasDerivAt_integral_compact (μ := μ) hfc hdc hfd t
  exact is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) t₀ t₁

end KervaireCurrentHomotopy

namespace KervaireHaarFlow

open NormedSpace
open scoped ContDiff

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

attribute [local instance] OAI.KervaireHaarFlow.instNormedAlgebraRat_oAI
variable [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireHaarFlow

namespace KervaireUnitaryHaarCurrent
open MeasureTheory VectorField
open scoped ContDiff
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

variable [CompleteSpace B] [StarRing B] [ContinuousStar B] [StarModule ℝ B]
  [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireUnitaryHaarCurrent

namespace KervaireCompactUnitary
variable {B : Type*} [CStarAlgebra B] [FiniteDimensional ℂ B]

end KervaireCompactUnitary

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireCurrentHomotopy
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open KervaireClosedCurrent KervaireHaarFlow VectorField ContinuousAlternatingMap
open scoped ContDiff


theorem solution : type_of% @_root_.OAI.KervaireCurrentHomotopy.integral_eval_constant := @_root_.OAI.KervaireCurrentHomotopy.integral_eval_constant
