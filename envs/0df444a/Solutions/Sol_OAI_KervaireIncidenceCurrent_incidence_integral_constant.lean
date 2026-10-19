-- Prove2me | solution 1 for OAI.KervaireIncidenceCurrent.incidence_integral_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:19:51.441195+00:00
-- url     : https://prove2.me/submissions/11f48bcb-57d6-4b41-851c-3a5c2706f4bf

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceTangent.lean:L319-L345
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireIncidenceCurrent.incidence_integral_constant. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Theorems.Thm_OAI_KervaireHorizontalCurrent_integral_pullback_constant
import Theorems.Thm_OAI_KervaireIncidenceCurrent_contDiff_incidence
import Theorems.Thm_OAI_KervaireIncidenceCurrent_fderiv_direction_bracket

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

end KervaireHaarFlow

open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff

namespace KervaireClosedCurrent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end KervaireClosedCurrent

namespace KervaireCurrentHomotopy
-- [generator] trimmed: open KervaireClosedCurrent KervaireHaarFlow VectorField ContinuousAlternatingMap
open KervaireHaarFlow VectorField ContinuousAlternatingMap
open scoped ContDiff

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

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

lemma isCompact_unitary : IsCompact (unitary B : Set B) := by
  apply (isCompact_closedBall (0 : B) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  nontriviality B
  exact (CStarRing.norm_of_mem_unitary hu).le

/-- The unitary group of a finite-dimensional complex C⋆-algebra is compact. -/
lemma compactSpace : CompactSpace (unitary B) :=
  isCompact_iff_compactSpace.mp isCompact_unitary

end KervaireCompactUnitary

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.IncidenceSpaces ----
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
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

lemma incidence_unitary {f : ℝ × Mat K → Mat (K ⊕ R)}
    (hf : ∀ t (X : unitary (Mat K)), f (t,(X : Mat K)) ∈ unitary (Mat (K ⊕ R)))
    (t : ℝ) (p : unitary (Alg K R)) : incidence f (t,(p : Alg K R)) ∈ unitary (Mat (K ⊕ R)) := by
  obtain ⟨hX,hQ,hT⟩ := unitary_alg_parts p
  exact (unitary _).mul_mem ((unitary _).mul_mem ((unitary _).mul_mem (hf t ⟨_,hX⟩) hQ)
    (diag_unitary ((unitary _).one_mem) (Unitary.star_mem hT))) (Unitary.star_mem hQ)

end KervaireIncidenceCurrent

open scoped ComplexOrder
namespace KervaireSkewTrace
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
local notation "S" => skewAdjoint.submodule ℝ M

lemma pairing_apply (a b : S) : pairing a b = -(Matrix.trace ((a : M)*(b : M))).re := rfl

lemma pairing_self (a : S) : pairing a a = (Matrix.trace ((a : M)ᴴ*(a : M))).re := by
  have ha : (a : M)ᴴ = -(a : M) := a.property
  simp [ha, pairing_apply]

lemma pairing_self_eq_zero_iff (a : S) : pairing a a = 0 ↔ a = 0 := by
  rw [pairing_self]
  have hp := Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self (a : M)).trace_nonneg
  constructor
  · intro h
    apply Subtype.ext
    apply trace_conjTranspose_mul_self_eq_zero_iff.mp
    apply Complex.ext h
    exact hp.2.symm
  · rintro rfl
    simp

lemma bracket_pair_left (a b : S) : pairing (bracket a b) a = 0 := by
  change -(trace (((a : M)*(b : M)-(b : M)*(a : M))*(a : M))).re = 0
  rw [sub_mul, trace_sub, trace_mul_cycle (b : M) (a : M) (a : M)]
  simp

lemma bracket_pair_right (a b : S) : pairing (bracket a b) b = 0 := by
  change -(trace (((a : M)*(b : M)-(b : M)*(a : M))*(b : M))).re = 0
  rw [sub_mul, trace_sub, trace_mul_cycle (a : M) (b : M) (b : M)]
  simp

lemma pairing_eq_repr_mul {J : Type*} [Fintype J] (b : Basis J ℝ S)
    (hb : (pairing (I := I)).IsOrthoᵢ b) (a : S) (i : J) :
    pairing a (b i) = b.repr a i * pairing (b i) (b i) := by
  classical
  conv_lhs => rw [← b.sum_repr a]
  simp only [LinearMap.map_sum₂, LinearMap.map_smul₂, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [hb hji, mul_zero]
  · simp

lemma bracket_repr_left {J : Type*} [Fintype J] (b : Basis J ℝ S)
    (hb : (pairing (I := I)).IsOrthoᵢ b) (i j : J) :
    b.repr (bracket (b i) (b j)) i = 0 := by
  have h := bracket_pair_left (b i) (b j)
  rw [pairing_eq_repr_mul b hb] at h
  exact (mul_eq_zero.mp h).resolve_right (fun hz ↦ b.ne_zero i ((pairing_self_eq_zero_iff _).mp hz))

lemma bracket_repr_right {J : Type*} [Fintype J] (b : Basis J ℝ S)
    (hb : (pairing (I := I)).IsOrthoᵢ b) (i j : J) :
    b.repr (bracket (b i) (b j)) j = 0 := by
  have h := bracket_pair_right (b i) (b j)
  rw [pairing_eq_repr_mul b hb] at h
  exact (mul_eq_zero.mp h).resolve_right (fun hz ↦ b.ne_zero j ((pairing_self_eq_zero_iff _).mp hz))

end KervaireSkewTrace
namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

variable {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

omit [Fintype IZ] in
lemma effectiveBracket_repr_left (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (T : unitary (Mat R)) (i j : IK ⊕ IR ⊕ IZ) :
    (horizontalBasis bK bR bZ).repr
      (effectiveBracket T (horizontalBasis bK bR bZ i) (horizontalBasis bK bR bZ j)) i = 0 := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [horizontalBasis, Basis.prod_apply, effectiveBracket,
      KervaireSkewTrace.bracket_repr_left bK hbK, KervaireSkewTrace.bracket_repr_left bR hbR]

omit [Fintype IZ] in
lemma effectiveBracket_repr_right (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (T : unitary (Mat R)) (i j : IK ⊕ IR ⊕ IZ) :
    (horizontalBasis bK bR bZ).repr
      (effectiveBracket T (horizontalBasis bK bR bZ i) (horizontalBasis bK bR bZ j)) j = 0 := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [horizontalBasis, Basis.prod_apply, effectiveBracket,
      KervaireSkewTrace.bracket_repr_right bK hbK, KervaireSkewTrace.bracket_repr_right bR hbR]

end KervaireIncidenceCurrent

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.IncidenceTangent ----
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
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

omit [Fintype IZ] in
lemma basis_bracket_condition {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (p : unitary (Alg K R)) (i j : Fin (n+1)) :
    let b := (horizontalBasis bK bR bZ).reindex e
    ∃ c : Fin (n+1) → ℝ, c i = 0 ∧ c j = 0 ∧
      fderiv ℝ (incidence f) (t,(p : Alg K R))
        (0,(p : Alg K R)*((direction (b i) : Alg K R)*(direction (b j) : Alg K R)-
          (direction (b j) : Alg K R)*(direction (b i) : Alg K R))) =
        ∑ l, c l • fderiv ℝ (incidence f) (t,(p : Alg K R))
          (0,(p : Alg K R)*(direction (b l) : Alg K R)) := by
  intro b
  let T : unitary (Mat R) := ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩
  let v := effectiveBracket T (b i) (b j)
  refine ⟨fun l ↦ b.repr v l,?_,?_,?_⟩
  · simpa only [b,v,Basis.repr_reindex_apply,Basis.reindex_apply] using
      effectiveBracket_repr_left bK bR bZ hbK hbR T (e.symm i) (e.symm j)
  · simpa only [b,v,Basis.repr_reindex_apply,Basis.reindex_apply] using
      effectiveBracket_repr_right bK bR bZ hbK hbR T (e.symm i) (e.symm j)
  · rw [fderiv_direction_bracket hf]
    change horizontalDifferential f t p v = ∑ l, b.repr v l • horizontalDifferential f t p (b l)
    simpa only [_root_.map_sum,_root_.map_smul] using
      congrArg (horizontalDifferential f t p) (b.sum_repr v).symm

end KervaireIncidenceCurrent

namespace KervaireFixedSpace
open Matrix
variable {K R : Type*}
end KervaireFixedSpace
namespace KervaireIncidenceCurrent
open MeasureTheory
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

omit [Fintype IZ] in
lemma incidence_integral_constant {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (hu : ∀ t (X : unitary (Mat K)), f (t,(X : Mat K)) ∈ unitary (Mat (K ⊕ R)))
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (t₀ t₁ : ℝ) :
    let b := (horizontalBasis bK bR bZ).reindex e
    (∫ p : unitary (Alg K R), form (incidence f (t₀,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence f) (t₀,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) =
    (∫ p : unitary (Alg K R), form (incidence f (t₁,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence f) (t₁,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) := by
  intro b
  let : CompactSpace (unitary (Alg K R)) := KervaireCompactUnitary.compactSpace
  apply KervaireHorizontalCurrent.integral_pullback_constant (fun i ↦ direction (b i))
    (contDiff_incidence hf) (incidence_unitary hu) _ _ form hform t₀ t₁
  · let L : Horizontal K R ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat (K ⊕ R)) :=
      KervaireFixedSpace.degreeDerivativeEquiv (K := K) (R := R) 1 one_ne_zero
    let c : Basis (Fin (n+1)) ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))) := b.map L
    have h : Module.finrank ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))) = n+1 := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis c
    exact h.le
  · intro t p i j _
    exact basis_bracket_condition bK bR bZ e hbK hbR hf t p i j

end KervaireIncidenceCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireIncidenceCurrent
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
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open MeasureTheory


theorem solution : type_of% @_root_.OAI.KervaireIncidenceCurrent.incidence_integral_constant := @_root_.OAI.KervaireIncidenceCurrent.incidence_integral_constant
