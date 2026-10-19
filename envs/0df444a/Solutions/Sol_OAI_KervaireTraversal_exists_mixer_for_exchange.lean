-- Prove2me | solution 1 for OAI.KervaireTraversal.exists_mixer_for_exchange
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:42:52.055497+00:00
-- url     : https://prove2.me/submissions/69b285a9-d70f-44bf-bcfd-ea17b6bfc799

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Traversal.lean:L169-L194
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireTraversal.exists_mixer_for_exchange. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Theorems.Thm_OAI_KervaireFixed_fixedDim_reindex
import Theorems.Thm_OAI_KervaireIncidenceCurrent_exists_incidence_of_homotopic
import Theorems.Thm_OAI_KervaireSignPairing_sign_count
import Theorems.Thm_OAI_KervaireTraversal_offDiagonal_representation
import Theorems.Thm_OAI_KervaireUnitaryExponential_exists_smooth_path

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

lemma homotopic_of_elementary {F G : UMap B C} (h : Elementary F G) : Homotopic F G :=
  Relation.EqvGen.rel _ _ h

lemma homotopic_symm {F G : UMap B C} (h : Homotopic F G) : Homotopic G F :=
  Relation.EqvGen.symm _ _ h
lemma homotopic_trans {F G H : UMap B C} (h : Homotopic F G) (h' : Homotopic G H) :
    Homotopic F H := Relation.EqvGen.trans _ _ _ h h'

section Differential
variable {E D : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
  [StarRing E] [ContinuousStar E] [StarModule ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
attribute [local instance] OAI.KervaireUnitaryHomotopy.instNormedAlgebraRat_oAI
end Differential

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

end

variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

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

end KervaireIncidenceCurrent

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.SignedIncidence ----
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

namespace KervaireIncidenceCurrent

section
open KervaireUnitaryHomotopy
variable {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

lemma pair_cancel (Y : unitary (Mat L)) :
    diag (Y : Mat L) 1 * (swapBlocks (L := L) : Mat (L ⊕ L)) * diag 1 (star (Y : Mat L)) *
      star (swapBlocks (L := L) : Mat (L ⊕ L)) = 1 := by
  have hY : (Y : Mat L) * (Y : Mat L).conjTranspose = 1 := Y.property.2
  simp [swapBlocks,diag,star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply,← Matrix.fromBlocks_one,hY]

lemma paired_elementary_core (Y : UMap (Mat K) (Mat L)) :
    Elementary (pairedMap Y) (coreMap (K := K) (L := L)) := by
  obtain ⟨p,hp,hp0,hp1,hpu⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path
    (swapBlocks (L := L))
  refine ⟨fun q ↦ diag q.2 (diag (Y q.2) 1 * p q.1 * diag 1 (star (Y q.2)) * star (p q.1)),?_,?_,?_,?_⟩
  · exact contDiff_diag contDiff_snd (((contDiff_diag (Y.smooth.comp contDiff_snd) contDiff_const).mul
      (hp.comp contDiff_fst) |>.mul (contDiff_diag contDiff_const ((starL ℝ).contDiff.comp (Y.smooth.comp contDiff_snd)))).mul
      ((starL ℝ).contDiff.comp (hp.comp contDiff_fst)))
  · intro t X
    apply diag_unitary X.property
    apply (unitary _).mul_mem
    · apply (unitary _).mul_mem
      · exact (unitary _).mul_mem (diag_unitary (Y.unitary X) (by simp)) (hpu t)
      · exact diag_unitary (by simp) (by simpa only [Unitary.star_mem_iff] using Y.unitary X)
    · simpa only [Unitary.star_mem_iff] using hpu t
  · intro X
    simp only [hp0,mul_one,star_one,diag_mul,mul_one,one_mul]
    rfl
  · intro X
    dsimp only
    rw [hp1,pair_cancel ⟨Y X,Y.unitary X⟩]
    rfl

lemma core_elementary_model :
    Elementary (coreMap (K := K) (L := L)) (modelMap (K := K) (R := L ⊕ L)) := by
  obtain ⟨p,hp,hp0,hp1,hpu⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path
    (-1 : unitary (Mat (L ⊕ L)))
  refine ⟨fun q ↦ diag q.2 (p q.1),contDiff_diag contDiff_snd (hp.comp contDiff_fst),?_,?_,?_⟩
  · intro t X
    exact diag_unitary X.property (hpu t)
  · intro X
    dsimp only
    rw [hp0]
    rfl
  · intro X
    dsimp only
    rw [hp1]
    rfl

lemma elementary_rightMul {I : Type*} [Fintype I] [DecidableEq I]
    (F : UMap (Mat K) (Mat I)) (P : unitary (Mat I)) : Elementary F (rightMulMap F P) := by
  obtain ⟨p,hp,hp0,hp1,hpu⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path P
  refine ⟨fun q ↦ F q.2 * p q.1,(F.smooth.comp contDiff_snd).mul (hp.comp contDiff_fst),?_,?_,?_⟩
  · intro t X
    exact (unitary _).mul_mem (F.unitary X) (hpu t)
  · intro X
    simp [hp0]
  · intro X
    dsimp only
    rw [hp1]
    rfl

lemma model_homotopic_paired_mul (Y : UMap (Mat K) (Mat L))
    (P : unitary (Mat (K ⊕ (L ⊕ L)))) :
    Homotopic (modelMap (K := K) (R := L ⊕ L)) (rightMulMap (pairedMap Y) P) :=
  homotopic_trans (homotopic_symm (homotopic_of_elementary core_elementary_model))
    (homotopic_trans (homotopic_symm (homotopic_of_elementary (paired_elementary_core Y)))
      (homotopic_of_elementary (elementary_rightMul (pairedMap Y) P)))

end

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma includeFirst_injective : Function.Injective (includeFirst (K := K) (R := R)) := by
  intro v w h
  exact funext fun k ↦ congrFun h (Sum.inl k)

omit [DecidableEq R] in
lemma diag_mulVec_includeFirst (T : Mat R) (v : K → ℂ) :
    diag 1 T *ᵥ includeFirst v = includeFirst (R := R) v := by
  simp only [diag,includeFirst,LinearMap.coe_mk,AddHom.coe_mk,Matrix.fromBlocks_mulVec,
    Function.comp_def,Matrix.one_mulVec,Matrix.zero_mulVec,add_zero,zero_add]
  congr 1
  exact Matrix.mulVec_zero _

lemma rank_of_incidence {f : ℝ × Mat K → Mat (K ⊕ R)} (t : ℝ)
    (p : unitary (Alg K R)) (hp : incidence f (t,(p : Alg K R)) = 1) :
    Fintype.card K ≤ Module.finrank ℂ
      (LinearMap.ker ((f (t,p.val.1)).mulVecLin - LinearMap.id)) := by
  let Q : unitary (Mat (K ⊕ R)) := ⟨p.val.2.1,(unitary_alg_parts p).2.1⟩
  let T : unitary (Mat R) := ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩
  have hQ (D : Mat (K ⊕ R)) : star (Q : Mat (K ⊕ R))*((Q : Mat (K ⊕ R))*D) = D := by
    rw [← mul_assoc,Q.property.1,one_mul]
  have hdiag : diag (1 : Mat K) (star (T : Mat R))*diag 1 (T : Mat R) = 1 := by
    rw [diag_mul,one_mul,T.property.1,diag_one]
  have heq : f (t,p.val.1)*(Q : Mat (K ⊕ R)) = (Q : Mat (K ⊕ R))*diag 1 (T : Mat R) := by
    have hh := congrArg (fun M : Mat (K ⊕ R) ↦ M*(Q : Mat (K ⊕ R))*diag 1 (T : Mat R)) hp
    change f (t,p.val.1)*(Q : Mat (K ⊕ R))*diag 1 (star (T : Mat R))*star (Q : Mat (K ⊕ R)) *
      (Q : Mat (K ⊕ R))*diag 1 (T : Mat R) = _ at hh
    simpa only [mul_assoc,hQ,hdiag,mul_one,one_mul] using hh
  have hiQ : Function.Injective (Q.val.mulVecLin) := by
    intro v w h
    have hh := congrArg (fun v ↦ star Q.val *ᵥ v) h
    simpa only [Matrix.mulVecLin_apply,Matrix.mulVec_mulVec,Q.property.1,Matrix.one_mulVec] using hh
  let L : (K → ℂ) →ₗ[ℂ] LinearMap.ker ((f (t,p.val.1)).mulVecLin - LinearMap.id) :=
    LinearMap.codRestrict _ (Q.val.mulVecLin.comp includeFirst) (by
      intro v
      change f (t,p.val.1) *ᵥ (Q.val *ᵥ includeFirst v) - Q.val *ᵥ includeFirst v = 0
      rw [Matrix.mulVec_mulVec,heq,← Matrix.mulVec_mulVec,diag_mulVec_includeFirst,sub_self])
  have hL : Function.Injective L := by
    intro v w h
    apply includeFirst_injective (R := R)
    apply hiQ
    exact congrArg Subtype.val h
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,mul_one] using LinearMap.finrank_le_finrank_of_injective hL

end

open KervaireUnitaryHomotopy
variable {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
lemma exists_paired_fixed [Nonempty K] (Y : UMap (Mat K) (Mat L))
    (P : unitary (Mat (K ⊕ (L ⊕ L)))) :
    ∃ X : unitary (Mat K), Fintype.card K ≤ Module.finrank ℂ
      (LinearMap.ker ((((pairedMap Y) X * P)).mulVecLin - LinearMap.id)) := by
  obtain ⟨p,hp⟩ := exists_incidence_of_homotopic (rightMulMap (pairedMap Y) P)
    (model_homotopic_paired_mul Y P)
  refine ⟨⟨p.val.1,(unitary_alg_parts p).1⟩,?_⟩
  exact rank_of_incidence (f := timeless (rightMulMap (pairedMap Y) P)) 0 p hp
end KervaireIncidenceCurrent

namespace KervaireSignPairing

section
open Matrix
variable {I K : Type*} [Fintype I]

lemma signsEquiv_pos (s : I → ℤ) (hc) (j : Unit ⊕ negative s) :
    s (signsEquiv s hc (.inl j)) = 1 := by
  change s ((positiveEquiv s hc) j) = 1
  exact ((positiveEquiv s hc) j).property
lemma signsEquiv_neg (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hc) (j : negative s) : s (signsEquiv s hc (.inr j)) = -1 := by
  exact (hs j).resolve_left j.property

end

open Matrix KervaireIncidenceCurrent KervaireUnitaryHomotopy
open scoped Matrix.Norms.L2Operator
variable {I K D : Type*} [Fintype I] [Fintype K] [Fintype D]
  [DecidableEq I] [DecidableEq K] [DecidableEq D]

omit [Fintype K] [Fintype D] [DecidableEq I] [DecidableEq K] [DecidableEq D] in
lemma coordinates_inl (s : I → ℤ) (hc) (k : K) :
    coordinates s hc (.inl k) = (k,signsEquiv s hc (.inl (.inl ()))) := rfl
omit [Fintype K] [Fintype D] [DecidableEq I] [DecidableEq K] [DecidableEq D] in
lemma coordinates_middle (s : I → ℤ) (hc) (k : K) (j : negative s) :
    coordinates s hc (.inr (.inl (k,j))) = (k,signsEquiv s hc (.inl (.inr j))) := rfl
omit [Fintype K] [Fintype D] [DecidableEq I] [DecidableEq K] [DecidableEq D] in
lemma coordinates_last (s : I → ℤ) (hc) (k : K) (j : negative s) :
    coordinates s hc (.inr (.inr (k,j))) = (k,signsEquiv s hc (.inr j)) := rfl

omit [Fintype K] [DecidableEq K] in
lemma signedMatrix_coordinates (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) (X : Mat K) :
    (signedMatrix s X).submatrix (coordinates s hc) (coordinates s hc) =
      diag X (diag (repeatMatrix (D := negative s) X) (star (repeatMatrix (D := negative s) X))) := by
  classical
  ext i j
  rcases i with i | ⟨i,i'⟩ | ⟨i,i'⟩ <;> rcases j with j | ⟨j,j'⟩ | ⟨j,j'⟩ <;>
    simp [Matrix.submatrix_apply,signedMatrix,coordinates_inl,coordinates_middle,coordinates_last,
      signsEquiv_pos,signsEquiv_neg s hs,KervaireIncidenceCurrent.diag,Matrix.fromBlocks,repeatMatrix,
      blockDiagonal_apply,star_eq_conjTranspose]

end KervaireSignPairing

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.FixedSpaces ----
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
open Matrix

namespace KervaireFixed

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
end

section
open Matrix
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
end

section
open KervaireIncidenceCurrent KervaireSignPairing KervaireUnitaryHomotopy
open scoped Matrix.Norms.L2Operator
variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

lemma exists_signed_fixed_pos [Nonempty K] (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : ∑ i, s i = 1)
    (P : unitary (Mat (K × I))) :
    ∃ X : unitary (Mat K), Fintype.card K ≤ fixedDim (signedMatrix s (X : Mat K) * (P : Mat (K × I))) := by
  classical
  let e := coordinates (K := K) s (sign_count s hs hsum)
  let Q := reindexUnitary e.symm P
  obtain ⟨X,hX⟩ := exists_paired_fixed (repeatMap (K := K) (D := negative s)) Q
  refine ⟨X,?_⟩
  change Fintype.card K ≤ fixedDim ((pairedMap (repeatMap (K := K) (D := negative s))) X * (Q : Mat (K ⊕ ((K × negative s) ⊕ (K × negative s))))) at hX
  have hD : (pairedMap (repeatMap (K := K) (D := negative s))) X =
      Matrix.reindex e.symm e.symm (signedMatrix s (X : Mat K)) :=
    (signedMatrix_coordinates s hs (sign_count s hs hsum) (X : Mat K)).symm
  have hM : (pairedMap (repeatMap (K := K) (D := negative s))) X * (Q : Mat (K ⊕ ((K × negative s) ⊕ (K × negative s)))) =
      Matrix.reindex e.symm e.symm (signedMatrix s (X : Mat K) * (P : Mat (K × I))) := by
    rw [hD]
    exact (map_mul (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (signedMatrix s (X : Mat K)) P).symm
  rw [hM,fixedDim_reindex] at hX
  exact hX

omit [Fintype I] [Fintype K] [DecidableEq K] in
lemma signedMatrix_neg (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (X : Mat K) :
    signedMatrix (fun i ↦ -s i) X = signedMatrix s (star X) := by
  unfold signedMatrix
  congr 1
  funext i
  rcases hs i with h | h <;> simp [h]

lemma exists_signed_fixed [Nonempty K] (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (P : unitary (Mat (K × I))) :
    ∃ X : unitary (Mat K), Fintype.card K ≤ fixedDim (signedMatrix s (X : Mat K) * (P : Mat (K × I))) := by
  rcases hsum with hsum | hsum
  · exact exists_signed_fixed_pos s hs hsum P
  · have hs' (i : I) : -s i = 1 ∨ -s i = -1 := by
      rcases hs i with h | h <;> simp [h]
    have hsum' : ∑ i, -s i = 1 := by rw [Finset.sum_neg_distrib,hsum]; norm_num
    obtain ⟨X,hX⟩ := exists_signed_fixed_pos (fun i ↦ -s i) hs' hsum' P
    refine ⟨star X,?_⟩
    rw [signedMatrix_neg s hs] at hX
    exact hX
end

open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma doubleFixedMap_injective (D P : unitary (Matrix I I ℂ)) :
    Function.Injective (doubleFixedMap D P) := by
  intro v w h
  have hh := congrArg Subtype.val h
  have h1 : (v.1 : I → ℂ) = w.1 := funext fun i ↦ congrFun hh (Sum.inl i)
  have h2 : (star D : Matrix I I ℂ).mulVec v.2 = (star D : Matrix I I ℂ).mulVec w.2 :=
    funext fun i ↦ congrFun hh (Sum.inr i)
  have hi := congrArg (D : Matrix I I ℂ).mulVec h2
  simp only [mulVec_mulVec] at hi
  exact Prod.ext (Subtype.ext h1) (Subtype.ext (by simpa [D.property.2] using hi))

lemma two_mul_fixedDim_le (D P : unitary (Matrix I I ℂ)) :
    2 * fixedDim ((D : Matrix I I ℂ) * (P : Matrix I I ℂ)) ≤
      fixedDim ((fromBlocks 0 (D : Matrix I I ℂ) (star D : Matrix I I ℂ) 0) *
        (fromBlocks 0 (star P : Matrix I I ℂ) (P : Matrix I I ℂ) 0)) := by
  have h := LinearMap.finrank_le_finrank_of_injective (doubleFixedMap_injective D P)
  simpa only [Module.finrank_prod, ← two_mul, fixedDim, fixedSpace] using h
end KervaireFixed

namespace KervaireMatrix
open KervaireFixed KervaireSpectral KervaireRegular
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.Traversal ----
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
open Matrix

namespace KervaireTraversal

section
open Matrix KervaireFixed KervaireSignPairing
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K]
omit [Fintype I] [Fintype K] in
lemma mixer_coordinates (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (X : Matrix K K ℂ) :
    Matrix.reindex (coordinates (K := K) s).symm (coordinates (K := K) s).symm (mixer X) =
      fromBlocks 0 (signedMatrix (fun i ↦ -s i) X) (star (signedMatrix (fun i ↦ -s i) X)) 0 := by
  ext (⟨k,i⟩ | ⟨k,i⟩) (⟨l,j⟩ | ⟨l,j⟩) <;>
    rcases hs i with hi | hi <;> rcases hs j with hj | hj <;>
    by_cases hij : i = j <;>
    simp_all [Matrix.reindex_apply,coordinates,mixer,signedMatrix,
      blockDiagonal_apply,fromBlocks,eq_comm,Matrix.star_apply]

lemma signedMatrix_unitary (s : I → ℤ) (X : unitary (Matrix K K ℂ)) :
    signedMatrix s (X : Matrix K K ℂ) ∈ unitary (Matrix (K × I) (K × I) ℂ) := by
  have hu (i : I) : (if s i = 1 then (X : Matrix K K ℂ) else star (X : Matrix K K ℂ)) ∈ unitary _ := by
    split
    · exact X.property
    · exact Unitary.star_mem X.property
  constructor <;>
    simp only [signedMatrix,star_eq_conjTranspose,blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  · convert (blockDiagonal_one (m := K) (o := I) (α := ℂ)) using 1
    exact congrArg blockDiagonal (funext fun i ↦ (hu i).1)
  · convert (blockDiagonal_one (m := K) (o := I) (α := ℂ)) using 1
    exact congrArg blockDiagonal (funext fun i ↦ (hu i).2)

lemma exists_mixer_fixed [Nonempty K] (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (P : unitary (Matrix (K × I) (K × I) ℂ)) :
    ∃ X : unitary (Matrix K K ℂ),
      2 * Fintype.card K ≤ fixedDim (mixer (X : Matrix K K ℂ) *
        Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ))) := by
  have hn (i : I) : -s i = 1 ∨ -s i = -1 := by rcases hs i with h | h <;> simp [h]
  have hnsum : (∑ i, -s i) = 1 ∨ (∑ i, -s i) = -1 := by
    rw [Finset.sum_neg_distrib]
    rcases hsum with h | h <;> simp [h]
  obtain ⟨X,hX⟩ := exists_signed_fixed (fun i ↦ -s i) hn hnsum P
  let D : unitary (Matrix (K × I) (K × I) ℂ) :=
    ⟨signedMatrix (fun i ↦ -s i) (X : Matrix K K ℂ), signedMatrix_unitary _ X⟩
  have hD := two_mul_fixedDim_le D P
  refine ⟨X,?_⟩
  have hr := fixedDim_reindex (coordinates (K := K) s).symm
    (mixer (X : Matrix K K ℂ) * Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ)))
  have hm : Matrix.reindex (coordinates (K := K) s).symm (coordinates s).symm
      (mixer (X : Matrix K K ℂ) * Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ))) =
      Matrix.reindex (coordinates s).symm (coordinates s).symm (mixer (X : Matrix K K ℂ)) * exchange (P : Matrix (K × I) (K × I) ℂ) := by
    rw [show Matrix.reindex (coordinates s).symm (coordinates s).symm
      (mixer (X : Matrix K K ℂ) * Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ))) =
      Matrix.reindex (coordinates s).symm (coordinates s).symm (mixer (X : Matrix K K ℂ)) *
      Matrix.reindex (coordinates s).symm (coordinates s).symm (Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ))) from
      map_mul (Matrix.reindexAlgEquiv ℂ ℂ (coordinates s).symm) _ _]
    congr 1
    ext i j
    simp [Matrix.reindex_apply]
  rw [hm,mixer_coordinates s hs] at hr
  rw [← hr]
  exact (Nat.mul_le_mul_left 2 hX).trans hD
end

section
open Matrix KervaireFixed
open scoped Classical
variable {E : Type*} [Fintype E] [DecidableEq E]

end

open Matrix KervaireFixed
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
attribute [local instance] OAI.KervaireTraversal.instDecidableEqSlots
/-- The exact mixing step for an arbitrary scalar band involution exchanging
positive and negative traversal slots. No monomial restriction is imposed on X. -/
lemma exists_mixer_for_exchange (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (T : Matrix (Slots I K) (Slots I K) ℂ)
    (hTs : star T = T) (hTu : T ∈ unitary (Matrix (Slots I K) (Slots I K) ℂ))
    (h₀ : ∀ i j, T (coordinates s (.inl i)) (coordinates s (.inl j)) = 0)
    (h₁ : ∀ i j, T (coordinates s (.inr i)) (coordinates s (.inr j)) = 0) :
    ∃ X : unitary (Matrix K K ℂ), 2 * Fintype.card K ≤ fixedDim (mixer (X : Matrix K K ℂ) * T) := by
  let e := coordinates (K := K) s
  let N := Matrix.reindex e.symm e.symm T
  have hNs : star N = N := by
    dsimp only [N]
    rw [show star (Matrix.reindex e.symm e.symm T) = Matrix.reindex e.symm e.symm (star T) from
      Matrix.conjTranspose_reindex e.symm e.symm T,hTs]
  have hNu : N ∈ unitary (Matrix ((K × I) ⊕ (K × I)) ((K × I) ⊕ (K × I)) ℂ) :=
    (reindexUnitary e.symm ⟨T,hTu⟩).property
  obtain ⟨P,hP⟩ := offDiagonal_representation N hNs hNu h₀ h₁
  obtain ⟨X,hX⟩ := exists_mixer_fixed s hs hsum P
  refine ⟨X,?_⟩
  have he : Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ)) = T := by
    change Matrix.reindex e e (fromBlocks 0 (star (P : Matrix (K × I) (K × I) ℂ)) P 0) = T
    rw [← hP]
    ext i j
    simp [N,Matrix.reindex_apply]
  rwa [he] at hX
end KervaireTraversal

namespace KervaireMatrix
open Matrix KervaireRegular
open scoped Classical
variable {D : Type*} [Fintype D]

variable {A : Type*} [Group A]
end KervaireMatrix

namespace KervaireMixing
open Matrix KervaireMatrix KervaireRegular KervaireFixed
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A] [Nonempty I] [Nonempty K]
attribute [local instance] OAI.KervaireMixing.instDecidableEqSlot
end KervaireMixing

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireTraversal
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
open Matrix
open Matrix KervaireFixed
open scoped Classical
attribute [local instance] OAI.KervaireTraversal.instDecidableEqSlots


theorem solution : type_of% @_root_.OAI.KervaireTraversal.exists_mixer_for_exchange := @_root_.OAI.KervaireTraversal.exists_mixer_for_exchange
