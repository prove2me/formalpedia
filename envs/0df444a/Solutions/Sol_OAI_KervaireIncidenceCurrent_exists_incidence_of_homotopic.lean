-- Prove2me | solution 1 for OAI.KervaireIncidenceCurrent.exists_incidence_of_homotopic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:32:47.101104+00:00
-- url     : https://prove2.me/submissions/f6fa166e-459e-4d81-9563-6eed425e4218

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/CurrentExistence.lean:L143-L157
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireIncidenceCurrent.exists_incidence_of_homotopic. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Theorems.Thm_OAI_KervaireCurrentExistence_mem_range_of_integral_invariant
import Theorems.Thm_OAI_KervaireIncidenceCurrent_contDiff_incidence
import Theorems.Thm_OAI_KervaireIncidenceCurrent_fderiv_model_gauge
import Theorems.Thm_OAI_KervaireIncidenceCurrent_incidence_integral_constant
import Theorems.Thm_OAI_KervaireIncidenceCurrent_model_fiber_blocks
import Theorems.Thm_OAI_KervaireUnitaryExponential_exists_smooth_path
import Theorems.Thm_OAI_KervaireUnitaryHomotopy_fderiv_horizontal_congr

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

end KervaireIncidenceCurrent

open scoped ComplexOrder
namespace KervaireSkewTrace
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
local notation "S" => skewAdjoint.submodule ℝ M

lemma pairing_apply (a b : S) : pairing a b = -(Matrix.trace ((a : M)*(b : M))).re := rfl

lemma pairing_symm : LinearMap.IsSymm (pairing (I := I)) := by
  constructor
  intro a b
  simp only [pairing_apply, trace_mul_comm (a : M) (b : M), RingHom.id_apply]

/-- Orthogonal bases exist without selecting an orientation or changing matrix norms. -/
lemma exists_orthogonal_basis : ∃ b : Basis (Fin (Module.finrank ℝ S)) ℝ S,
    (pairing (I := I)).IsOrthoᵢ b :=
  LinearMap.BilinForm.exists_orthogonal_basis pairing_symm

end KervaireSkewTrace
namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

variable {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

end KervaireIncidenceCurrent

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.UnitaryHomotopy ----
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
open scoped ContDiff

namespace KervaireUnitaryHomotopy
variable (B C : Type*) [CStarAlgebra B] [CStarAlgebra C]

variable {B C}

section Differential
variable {E D : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
  [StarRing E] [ContinuousStar E] [StarModule ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
attribute [local instance] OAI.KervaireUnitaryHomotopy.instNormedAlgebraRat_oAI
end Differential

lemma invariant_of_elementary {D : Type*} (I : UMap B C → D)
    (hI : ∀ F G, Elementary F G → I F = I G)
    {F G : UMap B C} (h : Homotopic F G) : I F = I G := by
  induction h with
  | rel F G h => exact hI F G h
  | refl F => rfl
  | symm F G _ ih => exact ih.symm
  | trans F G H _ _ ih ih' => exact ih.trans ih'

end KervaireUnitaryHomotopy

namespace KervaireIncidenceCurrent

section
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

omit [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))] in
lemma incidence_restrict_congr {f g : ℝ × Mat K → Mat (K ⊕ R)} (t s : ℝ)
    (h : ∀ X : unitary (Mat K), f (t,(X : Mat K)) = g (s,(X : Mat K)))
    (p : unitary (Alg K R)) : incidence f (t,(p : Alg K R)) = incidence g (s,(p : Alg K R)) := by
  unfold incidence
  rw [h ⟨p.val.1,(unitary_alg_parts p).1⟩]

omit [Fintype IK] [Fintype IR] [Fintype IZ] [IsFiniteMeasure μ] [IsMulRightInvariant μ]
  [BorelSpace (unitary (Alg K R))] in
lemma incidence_endpoint_integral {n : ℕ} (b : Fin n → Horizontal K R)
    {f g : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (t s : ℝ) (heq : ∀ X : unitary (Mat K), f (t,(X : Mat K)) = g (s,(X : Mat K)))
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin n]→L[ℝ] ℝ) :
    (∫ p : unitary (Alg K R), form (incidence f (t,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence f) (t,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) =
    (∫ p : unitary (Alg K R), form (incidence g (s,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence g) (s,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) := by
  apply integral_congr_ae
  filter_upwards with p
  rw [incidence_restrict_congr t s heq p]
  congr 1
  funext i
  exact fderiv_horizontal_congr (contDiff_incidence hf) (contDiff_incidence hg) t s
    (incidence_restrict_congr t s heq) p (direction (b i))

omit [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))] in
lemma contDiff_timeless (F : UMap (Mat K) (Mat (K ⊕ R))) : ContDiff ℝ ∞ (timeless F) :=
  F.smooth.comp contDiff_snd

omit [Fintype IZ] in
lemma current_eq_of_elementary {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (F G : UMap (Mat K) (Mat (K ⊕ R)))
    (h : Elementary F G) :
    current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form F =
      current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form G := by
  obtain ⟨H,hH,hU,h0,h1⟩ := h
  unfold current
  rw [← incidence_endpoint_integral (μ := μ) _ hH (contDiff_timeless F) 0 0 h0 form,
    ← incidence_endpoint_integral (μ := μ) _ hH (contDiff_timeless G) 1 0 h1 form]
  exact incidence_integral_constant (μ := μ) bK bR bZ e hbK hbR hH hU form hform 0 1

omit [Fintype IZ] in
lemma current_eq_of_homotopic {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) {F G : UMap (Mat K) (Mat (K ⊕ R))}
    (h : Homotopic F G) :
    current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form F =
      current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form G :=
  invariant_of_elementary (current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form)
    (current_eq_of_elementary bK bR bZ e hbK hbR form hform) h

end

variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

lemma contDiff_model : ContDiff ℝ ∞ (model (K := K) (R := R)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × Mat K ↦ diag p.2 (-1))
  simp only [diag_eq_corner]
  exact ((in11 (K := K) (R := R)).contDiff.comp contDiff_snd).add contDiff_const

lemma model_incidence_gauge (t : ℝ) (U : unitary (Mat K)) (V : unitary (Mat R)) :
    incidence model (t,(gaugePoint U V : Alg K R)) = 1 := by
  change diag 1 (-1) * diag (U : Mat K) (V : Mat R) * diag 1 (star (-1 : Mat R)) *
    star (diag (U : Mat K) (V : Mat R)) = 1
  simp only [diag_star,diag_mul,star_neg,star_one,one_mul,neg_mul,mul_one,mul_neg,neg_neg,
    U.property.2,V.property.2,diag_one]

end KervaireIncidenceCurrent

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.IncidenceDegree ----
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
open scoped ContDiff

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

lemma tangentVolume_equiv_ne_zero {J : Type*} [Fintype J] [DecidableEq J]
    (b : Basis J ℝ (Horizontal K R))
    (c : Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))))
    (L : Horizontal K R ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat (K ⊕ R))) :
    tangentVolume c (fun j ↦ (L (b j) : Mat (K ⊕ R))) ≠ 0 := by
  change c.det (fun j ↦ skewPart (L (b j) : Mat (K ⊕ R))) ≠ 0
  simp only [skewPart_coe]
  exact (c.isUnit_det (b.map L)).ne_zero

lemma model_jacobian_ne_zero {J : Type*} [Fintype J] [DecidableEq J]
    (b : Basis J ℝ (Horizontal K R))
    (c : Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))))
    (t : ℝ) (U : unitary (Mat K)) (V : unitary (Mat R)) :
    tangentVolume c (fun j ↦ fderiv ℝ (incidence model) (t,(gaugePoint U V : Alg K R))
      (0,(gaugePoint U V : Alg K R)*(direction (b j) : Alg K R))) ≠ 0 := by
  simp only [fderiv_model_gauge]
  exact tangentVolume_equiv_ne_zero b c (modelHorizontalEquiv U V)

lemma model_fiber_iff (X : Mat K) (Q : unitary (Mat (K ⊕ R))) (T : unitary (Mat R)) :
    diag X (-1) * (Q : Mat (K ⊕ R)) = (Q : Mat (K ⊕ R)) * diag 1 (T : Mat R) ↔
      X = 1 ∧ (T : Mat R) = -1 ∧ ∃ (U : unitary (Mat K)) (V : unitary (Mat R)),
        (Q : Mat (K ⊕ R)) = diag (U : Mat K) (V : Mat R) := by
  constructor
  · intro h
    have hQ := Q.property
    rw [← fromBlocks_toBlocks (Q : Mat (K ⊕ R))] at h hQ
    obtain ⟨hX,hB,hC,hT,hA,hD⟩ := model_fiber_blocks _ _ _ _ _ _ hQ h
    refine ⟨hX,hT,⟨_,hA⟩,⟨_,hD⟩,?_⟩
    change (Q : Mat (K ⊕ R)) = diag (Q : Mat (K ⊕ R)).toBlocks₁₁ (Q : Mat (K ⊕ R)).toBlocks₂₂
    calc
      _ = fromBlocks (Q : Mat (K ⊕ R)).toBlocks₁₁ (Q : Mat (K ⊕ R)).toBlocks₁₂
          (Q : Mat (K ⊕ R)).toBlocks₂₁ (Q : Mat (K ⊕ R)).toBlocks₂₂ := (fromBlocks_toBlocks _).symm
      _ = _ := by rw [hB,hC]; rfl
  · rintro ⟨rfl,hT,U,V,hQ⟩
    rw [hQ,hT,diag_mul,diag_mul]
    simp

end KervaireIncidenceCurrent

open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireUnitaryExponential
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.KervaireUnitaryExponential.instNormedAlgebraRat_oAI
lemma matrix_exists_smooth_path {I : Type*} [Fintype I] [DecidableEq I]
    (u : unitary (Matrix I I ℂ)) :
    ∃ p : ℝ → Matrix I I ℂ, ContDiff ℝ ∞ p ∧ p 0 = 1 ∧ p 1 = (u : Matrix I I ℂ) ∧
      ∀ t, p t ∈ unitary (Matrix I I ℂ) :=
  exists_smooth_path u (Matrix.finite_spectrum _)

end KervaireUnitaryExponential

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {J : Type*} [Fintype J] [DecidableEq J]

lemma continuous_jacobian (b : Basis J ℝ (Horizontal K R))
    (c : Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))))
    {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    Continuous (jacobian b c f t) := by
  apply (tangentVolume c).toContinuousMultilinearMap.cont.comp
  apply continuous_pi
  intro j
  exact (((contDiff_incidence hf).continuous_fderiv (by simp)).comp
    (continuous_const.prodMk continuous_id)).clm_apply
      (continuous_const.prodMk (continuous_id.mul continuous_const))

lemma model_fiber_gauge (t : ℝ) (p : unitary (Alg K R))
    (hp : incidence model (t,(p : Alg K R)) = 1) :
    ∃ (U : unitary (Mat K)) (V : unitary (Mat R)), p = gaugePoint U V := by
  let Q : unitary (Mat (K ⊕ R)) := ⟨p.val.2.1,(unitary_alg_parts p).2.1⟩
  let T : unitary (Mat R) := ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩
  have hQ (D : Mat (K ⊕ R)) : star (Q : Mat (K ⊕ R))*((Q : Mat (K ⊕ R))*D) = D := by
    rw [← mul_assoc,Q.property.1,one_mul]
  have hdiag : diag (1 : Mat K) (star (T : Mat R))*diag 1 (T : Mat R) = 1 := by
    rw [diag_mul,one_mul,T.property.1,diag_one]
  have heq : diag p.val.1 (-1)*(Q : Mat (K ⊕ R)) = (Q : Mat (K ⊕ R))*diag 1 (T : Mat R) := by
    have hh := congrArg (fun M : Mat (K ⊕ R) ↦ M*(Q : Mat (K ⊕ R))*diag 1 (T : Mat R)) hp
    change diag p.val.1 (-1)*(Q : Mat (K ⊕ R))*diag 1 (star (T : Mat R))*star (Q : Mat (K ⊕ R)) *
      (Q : Mat (K ⊕ R))*diag 1 (T : Mat R) = _ at hh
    simpa only [mul_assoc,hQ,hdiag,mul_one,one_mul] using hh
  obtain ⟨hX,hT,U,V,hUV⟩ := (model_fiber_iff p.val.1 Q T).mp heq
  refine ⟨U,V,Subtype.ext ?_⟩
  exact Prod.ext hX (Prod.ext hUV hT)

lemma model_jacobian_base (b : Basis J ℝ (Horizontal K R)) (t : ℝ) :
    jacobian b (modelVolumeBasis b) model t (gaugePoint (1 : unitary (Mat K)) (1 : unitary (Mat R)) : Alg K R) = 1 := by
  unfold jacobian
  simp only [fderiv_model_gauge]
  change (modelVolumeBasis b).det
    (fun j ↦ skewPart (modelHorizontalEquiv 1 1 (b j) : Mat (K ⊕ R))) = 1
  simp only [skewPart_coe]
  exact (modelVolumeBasis b).det_self

lemma model_jacobian_pos_gauge (b : Basis J ℝ (Horizontal K R)) (t : ℝ)
    (U : unitary (Mat K)) (V : unitary (Mat R)) :
    0 < jacobian b (modelVolumeBasis b) model t (gaugePoint U V : Alg K R) := by
  obtain ⟨u,hu,hu0,hu1,huU⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path U
  obtain ⟨v,hv,hv0,hv1,hvU⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path V
  let p : ℝ → Alg K R := fun s ↦ (1,diag (u s) (v s),-1)
  let j : ℝ → ℝ := fun s ↦ jacobian b (modelVolumeBasis b) model t (p s)
  have hp : Continuous p := by
    apply continuous_const.prodMk
    apply Continuous.prodMk _ continuous_const
    simp only [diag_eq_corner]
    exact ((in11 (K := K) (R := R)).continuous.comp hu.continuous).add
      ((in22 (K := K) (R := R)).continuous.comp hv.continuous)
  have hj : Continuous j := (continuous_jacobian b (modelVolumeBasis b) contDiff_model t).comp hp
  have hj0 : j 0 = 1 := by
    change jacobian b (modelVolumeBasis b) model t (1,diag (u 0) (v 0),-1) = 1
    rw [hu0,hv0]
    exact model_jacobian_base b t
  have hj1 : j 1 = jacobian b (modelVolumeBasis b) model t (gaugePoint U V : Alg K R) := by
    change jacobian _ _ _ _ (1,diag (u 1) (v 1),-1) = _
    rw [hu1,hv1]
    rfl
  have hne (s : ℝ) : j s ≠ 0 :=
    model_jacobian_ne_zero b (modelVolumeBasis b) t ⟨u s,huU s⟩ ⟨v s,hvU s⟩
  by_contra hn
  have hn' : j 1 ≤ 0 := by rw [hj1]; exact le_of_not_gt hn
  obtain ⟨s,_,hs⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 from zero_le_one)
    hj.continuousOn (show (0 : ℝ) ∈ Set.Icc (j 1) (j 0) from ⟨hn',by rw [hj0]; norm_num⟩)
  exact hne s hs

lemma model_jacobian_pos_fiber (b : Basis J ℝ (Horizontal K R)) (t : ℝ)
    (p : unitary (Alg K R)) (hp : incidence model (t,(p : Alg K R)) = 1) :
    0 < jacobian b (modelVolumeBasis b) model t (p : Alg K R) := by
  obtain ⟨U,V,rfl⟩ := model_fiber_gauge t p hp
  exact model_jacobian_pos_gauge b t U V

end KervaireIncidenceCurrent

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.CurrentExistence ----
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
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace KervaireCurrentExistence

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

end KervaireCurrentExistence

namespace KervaireIncidenceCurrent
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

lemma exists_incidence_of_homotopic_basis
    {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
    (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
    (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
    (bZ : Basis IZ ℝ (Matrix R K ℂ))
    {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (F : UMap (Mat K) (Mat (K ⊕ R))) (hF : Homotopic modelMap F) :
    ∃ p : unitary (Alg K R), incidence (timeless F) (0,(p : Alg K R)) = 1 := by
  classical
  let : CompactSpace (unitary (Alg K R)) := KervaireCompactUnitary.compactSpace
  let : MeasurableSpace (unitary (Alg K R)) := borel _
  let : BorelSpace (unitary (Alg K R)) := ⟨rfl⟩
  let μ : Measure (unitary (Alg K R)) := (Measure.haar (G := unitary (Alg K R))).inv
  let b := (horizontalBasis bK bR bZ).reindex e
  let c := modelVolumeBasis b
  have hn := KervaireCurrentExistence.mem_range_of_integral_invariant (μ := μ)
    (f₀ := fun p : unitary (Alg K R) ↦ incidence model (0,(p : Alg K R)))
    (f₁ := fun p : unitary (Alg K R) ↦ incidence (timeless F) (0,(p : Alg K R)))
    (j₀ := fun p : unitary (Alg K R) ↦ jacobian b c model 0 (p : Alg K R))
    (j₁ := fun p : unitary (Alg K R) ↦ jacobian b c (timeless F) 0 (p : Alg K R))
    ((contDiff_incidence contDiff_model).continuous.comp (continuous_const.prodMk continuous_subtype_val))
    ((contDiff_incidence (contDiff_timeless F)).continuous.comp (continuous_const.prodMk continuous_subtype_val))
    ((continuous_jacobian b c contDiff_model 0).comp continuous_subtype_val)
    1 ⟨gaugePoint 1 1,model_incidence_gauge 0 1 1⟩
    (model_jacobian_pos_fiber b 0) ?_
  · exact hn
  · intro φ hφ _
    have hi := current_eq_of_homotopic (μ := μ) bK bR bZ e hbK hbR
      (fun y ↦ φ y • tangentVolume c) (hφ.smul contDiff_const) hF
    have hm : timeless (modelMap (K := K) (R := R)) = (model : ℝ × Mat K → Mat (K ⊕ R)) := rfl
    simpa only [current,ContinuousAlternatingMap.smul_apply,smul_eq_mul,hm,jacobian,b] using hi

lemma skew_finrank_pos [Nonempty K] :
    0 < Module.finrank ℝ (skewAdjoint.submodule ℝ (Mat K)) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  let a : skewAdjoint.submodule ℝ (Mat K) := ⟨Complex.I • (1 : Mat K),by
    change star (Complex.I • (1 : Mat K)) = -(Complex.I • (1 : Mat K))
    simp⟩
  refine ⟨a,?_⟩
  intro h
  have hz := congrArg (fun a : skewAdjoint.submodule ℝ (Mat K) ↦ (a : Mat K)) h
  have hi := congrFun (congrFun hz (Classical.arbitrary K)) (Classical.arbitrary K)
  simp [a] at hi

lemma exists_incidence_of_homotopic [Nonempty K]
    (F : UMap (Mat K) (Mat (K ⊕ R))) (hF : Homotopic modelMap F) :
    ∃ p : unitary (Alg K R), incidence (timeless F) (0,(p : Alg K R)) = 1 := by
  classical
  obtain ⟨bK,hbK⟩ := KervaireSkewTrace.exists_orthogonal_basis (I := K)
  obtain ⟨bR,hbR⟩ := KervaireSkewTrace.exists_orthogonal_basis (I := R)
  let bZ := Module.finBasis ℝ (Matrix R K ℂ)
  let J := Fin (Module.finrank ℝ (skewAdjoint.submodule ℝ (Mat K))) ⊕
    Fin (Module.finrank ℝ (skewAdjoint.submodule ℝ (Mat R))) ⊕ Fin (Module.finrank ℝ (Matrix R K ℂ))
  have hc : 0 < Fintype.card J := by
    simpa only [J,Fintype.card_sum,Fintype.card_fin] using
      lt_of_lt_of_le (skew_finrank_pos (K := K)) (Nat.le_add_right _ _)
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
  let e : J ≃ Fin (n+1) := (Fintype.equivFin J).trans (finCongr hn)
  exact exists_incidence_of_homotopic_basis bK bR bZ e hbK hbR F hF

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
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open MeasureTheory KervaireUnitaryHomotopy


theorem solution : type_of% @_root_.OAI.KervaireIncidenceCurrent.exists_incidence_of_homotopic := @_root_.OAI.KervaireIncidenceCurrent.exists_incidence_of_homotopic
