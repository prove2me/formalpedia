-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.four_comparison_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T04:23:42.595016+00:00
-- url     : https://prove2.me/submissions/0c5b33c3-62a9-4a33-8bc2-f73b1017cdde

import Mathlib
import Definitions.Def_LaughlinGap
import Definitions.Def_OAIQ030L035

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging. -/

noncomputable section


namespace LaughlinGap.Averaging
open scoped BigOperators InnerProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma coordinates_inner (A B : Matrix ι ι ℝ) :
    inner ℝ (coordinates A) (coordinates B) = (A.transpose * B).trace := by
  change inner ℝ (WithLp.toLp 2 (fun ij : ι × ι => A ij.1 ij.2))
    (WithLp.toLp 2 (fun ij : ι × ι => B ij.1 ij.2)) = _
  simp only [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma average_mem (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    average S A ∈ S := by
  have hm := (invariantSpace S).starProjection_apply_mem (coordinates A)
  obtain ⟨B, hB, he⟩ := hm
  have hab : average S A = B := by
    change coordinates.symm ((invariantSpace S).starProjection (coordinates A)) = B
    rw [← he]
    exact coordinates.symm_apply_apply B
  exact hab ▸ hB

lemma average_orthogonal (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (A : Matrix ι ι ℝ) {B : Matrix ι ι ℝ} (hB : B ∈ S) :
    ((A - average S A).transpose * B).trace = 0 := by
  rw [← coordinates_inner, map_sub]
  have hB' : coordinates B ∈ invariantSpace S := ⟨B, hB, rfl⟩
  have he := (invariantSpace S).starProjection_inner_eq_zero (coordinates A) (coordinates B) hB'
  simpa [average] using he

lemma average_unique (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (A B : Matrix ι ι ℝ) (hB : B ∈ S)
    (h : ∀ C ∈ S, ((A-B).transpose * C).trace = 0) :
    average S A = B := by
  apply coordinates.injective
  change (invariantSpace S).starProjection (coordinates A) = coordinates B
  apply (invariantSpace S).eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨B, hB, rfl⟩
  · rintro _ ⟨C,hC,rfl⟩
    rw [← map_sub]
    change inner ℝ (coordinates (A-B)) (coordinates C) = 0
    rw [coordinates_inner]
    exact h C hC

lemma average_transpose (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    average S A.transpose = (average S A).transpose := by
  apply average_unique S A.transpose (average S A).transpose
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (star_mem (average_mem S A) : star (average S A) ∈ S)
  · intro C hC
    have ht : C.transpose ∈ S := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using (star_mem hC : star C ∈ S)
    have h := average_orthogonal S A ht
    rw [← Matrix.transpose_sub, Matrix.transpose_transpose]
    rw [← Matrix.trace_transpose, Matrix.transpose_mul] at h
    rw [Matrix.transpose_transpose, Matrix.trace_mul_comm] at h
    exact h

lemma average_isHermitian (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : (average S A).IsHermitian := by
  change (average S A).conjTranspose = average S A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← average_transpose]
  rw [show A.transpose = A from by simpa [Matrix.IsHermitian] using hA]

lemma trace_mul_average (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (A : Matrix ι ι ℝ) {B : Matrix ι ι ℝ} (hB : B ∈ S) :
    (A * B).trace = (average S A * B).trace := by
  have h := average_orthogonal S A.transpose hB
  rw [average_transpose, ← Matrix.transpose_sub, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.trace_sub] at h
  exact sub_eq_zero.mp h

lemma trace_mul_posSemidef {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  let U : Matrix ι ι ℝ := hB.1.eigenvectorUnitary
  have hAU := hA.conjTranspose_mul_mul_same U
  have hdiag : ∀ i, 0 ≤ (U.conjTranspose * A * U) i i := fun i => hAU.diag_nonneg
  have he : (A * B).trace = ((U.conjTranspose * A * U) *
      Matrix.diagonal hB.1.eigenvalues).trace := by
    conv_lhs => arg 1; rhs; rw [hB.1.spectral_theorem]
    change (A * (U * Matrix.diagonal hB.1.eigenvalues * U.conjTranspose)).trace = _
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [he]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hdiag i) (hB.eigenvalues_nonneg i))

lemma cfc_mem (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A : Matrix ι ι ℝ} (hA : A ∈ S) (f : ℝ → ℝ) : cfc f A ∈ S := by
  let : IsClosed (S : Set (Matrix ι ι ℝ)) :=
    S.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  exact _root_.cfc_mem (𝕜' := ℝ) f hA

lemma trace_mul_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f A).trace = ∑ i, hA.eigenvalues i * f (hA.eigenvalues i) := by
  have ht (M : Matrix ι ι ℝ) :
      (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary M).trace = M.trace := by
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.star_mul_self_of_mem (SetLike.coe_mem _), one_mul]
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc]
  conv_lhs => arg 1; lhs; rw [hA.spectral_theorem]
  rw [← map_mul, ht, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rfl

lemma cfc_nonnegative {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) : (cfc f A).PosSemidef := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  exact Matrix.posSemidef_diagonal_iff.mpr (fun i => hf _)

theorem average_positive (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : (average S A).PosSemidef := by
  classical
  have hY := average_isHermitian S hA.isHermitian
  rw [hY.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hn
  have hn : hY.eigenvalues i < 0 := lt_of_not_ge hn
  let f : ℝ → ℝ := fun x => if x = hY.eigenvalues i then 1 else 0
  have hf : ∀ x, 0 ≤ f x := by intro x; dsimp [f]; split_ifs <;> norm_num
  have hpos := trace_mul_posSemidef hA (cfc_nonnegative hY f hf)
  rw [trace_mul_average S A (cfc_mem S (average_mem S A) f), trace_mul_cfc hY] at hpos
  have hle : ∀ j : ι, hY.eigenvalues j * f (hY.eigenvalues j) ≤ 0 := by
    intro j
    dsimp [f]
    split_ifs with he
    · rw [he, mul_one]; exact hn.le
    · simp
  have hstrict : (∑ j, hY.eigenvalues j * f (hY.eigenvalues j)) < 0 := by
    apply Finset.sum_neg' (fun j _ => hle j)
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simpa [f] using hn
  exact (not_lt_of_ge hpos) hstrict

lemma average_trace (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    (average S A).trace = A.trace := by
  have h := trace_mul_average S A (one_mem S)
  simpa using h.symm

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma adjointMap_inner (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    inner ℝ (coordinates (F A)) (coordinates B) =
      inner ℝ (coordinates A) (coordinates (adjointMap F B)) := by
  let F' := coordinates.toLinearMap.comp (F.comp coordinates.symm.toLinearMap)
  exact (LinearMap.adjoint_inner_right F' (coordinates A) (coordinates B)).symm

theorem average_natural (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (T : StarSubalgebra ℝ (Matrix κ κ ℝ)) (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A ∈ S, F A ∈ T) (hF' : ∀ B ∈ T, adjointMap F B ∈ S)
    (A : Matrix ι ι ℝ) : average T (F A) = F (average S A) := by
  apply average_unique T (F A) (F (average S A)) (hF _ (average_mem S A))
  intro B hB
  rw [← map_sub, ← coordinates_inner, adjointMap_inner, coordinates_inner]
  exact average_orthogonal S A (hF' B hB)

lemma commutator_adjoint (L A B : Matrix ι ι ℝ) :
    inner ℝ (coordinates (commutator L A)) (coordinates B) =
      inner ℝ (coordinates A) (coordinates (commutator L.transpose B)) := by
  simp only [coordinates_inner, commutator, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.transpose_sub, Matrix.transpose_mul, sub_mul, mul_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_cycle' A.transpose B L.transpose]
  simp only [Matrix.mul_assoc]

omit [DecidableEq ι] in
lemma coordinates_eq_zero_of_inner {B : Matrix ι ι ℝ}
    (h : ∀ A, inner ℝ (coordinates A) (coordinates B) = 0) : B = 0 := by
  have he := inner_self_eq_zero.mp (h B)
  apply coordinates.injective
  simpa using he

lemma commutator_intertwines_adjoint {L : Matrix ι ι ℝ} {M : Matrix κ κ ℝ}
    (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A, F (commutator L.transpose A) = commutator M.transpose (F A))
    (B : Matrix κ κ ℝ) :
    commutator L (adjointMap F B) = adjointMap F (commutator M B) := by
  apply sub_eq_zero.mp
  apply coordinates_eq_zero_of_inner
  intro A
  rw [map_sub, inner_sub_right]
  apply sub_eq_zero.mpr
  rw [← adjointMap_inner]
  have hM := commutator_adjoint M.transpose (F A) B
  simp only [Matrix.transpose_transpose] at hM
  rw [← hM, ← hF, adjointMap_inner]
  have he := commutator_adjoint L.transpose A (adjointMap F B)
  simpa only [Matrix.transpose_transpose] using he.symm

lemma map_rotationCommutant {L : Matrix ι ι ℝ} {M : Matrix κ κ ℝ}
    (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A, F (commutator L A) = commutator M (F A))
    (hF' : ∀ A, F (commutator L.transpose A) = commutator M.transpose (F A))
    {A : Matrix ι ι ℝ} (hA : A ∈ rotationCommutant L) :
    F A ∈ rotationCommutant M := by
  rw [rotationCommutant_mem] at hA ⊢
  constructor
  · rw [← hF, hA.1, map_zero]
  · rw [← hF', hA.2, map_zero]

theorem rotation_average_natural {L : Matrix ι ι ℝ} {M : Matrix κ κ ℝ}
    (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A, F (commutator L A) = commutator M (F A))
    (hF' : ∀ A, F (commutator L.transpose A) = commutator M.transpose (F A))
    (A : Matrix ι ι ℝ) :
    average (rotationCommutant M) (F A) = F (average (rotationCommutant L) A) := by
  apply average_natural
  · intro B hB
    exact map_rotationCommutant F hF hF' hB
  · intro B hB
    rw [rotationCommutant_mem] at hB ⊢
    constructor
    · rw [commutator_intertwines_adjoint F hF', hB.1, map_zero]
    · have hh : ∀ A, F (commutator L.transpose.transpose A) =
          commutator M.transpose.transpose (F A) := by simpa using hF
      rw [commutator_intertwines_adjoint F hh, hB.2, map_zero]

end LaughlinGap.Averaging

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Occupation
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.basisContraction_apply_empty _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.extendLocal_add _root_.OAI.LaughlinGap.Occupation.extendLocal_adjoint _root_.OAI.LaughlinGap.Occupation.extendLocal_mul _root_.OAI.LaughlinGap.Occupation.extendLocal_one _root_.OAI.LaughlinGap.Occupation.extendLocal_smul _root_.OAI.LaughlinGap.Occupation.extendLocal_zero _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.fullContraction_add _root_.OAI.LaughlinGap.Occupation.fullContraction_single _root_.OAI.LaughlinGap.Occupation.fullContraction_smul _root_.OAI.LaughlinGap.Occupation.fullContraction_zero _root_.OAI.LaughlinGap.Occupation.inner_vacuum_left _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorInclusion_apply _root_.OAI.LaughlinGap.Occupation.sectorInclusion_apply_label _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.Occupation.slice_apply _root_.OAI.LaughlinGap.Occupation.slice_extendLocal _root_.OAI.LaughlinGap.Occupation.vacuum_norm _root_.OAI.LaughlinGap.Occupation.word_cons _root_.OAI.LaughlinGap.Occupation.word_nil _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.RealOccupation.complexify_creation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Occupation. -/

noncomputable section


namespace LaughlinGap
namespace Occupation
open scoped BigOperators InnerProduct

theorem transition_norm_le {n : ℕ} (j : Fin n) (ε : Bool) (x : Hilbert n) :
    ‖transition j ε x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    (∑ A, ‖transition j ε x A‖ ^ 2) ≤ ∑ A, ‖x (flip j A)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro A _
      rw [transition_apply]
      split_ifs
      · simp
      · simp
    _ = _ := Equiv.sum_comp (flip j) (fun A => ‖x A‖ ^ 2)

theorem transition_complement {n : ℕ} (j : Fin n) (ε : Bool) :
    transition j ε ∘ₗ transition j (!ε) + transition j (!ε) ∘ₗ transition j ε =
      LinearMap.id := by
  ext x A
  change transition j ε (transition j (!ε) x) A +
    transition j (!ε) (transition j ε x) A = x A
  cases ε <;> by_cases hj : j ∈ A <;> simp [transition_apply, hj, ← mul_assoc]

theorem annihilation_creation_CAR {n : ℕ} (i j : Fin n) :
    annihilation i ∘ₗ creation j + creation j ∘ₗ annihilation i =
      if i = j then LinearMap.id else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using transition_complement i false
  · rw [ite_eq_right hij, transition_anticommute_of_ne hij false true]
    exact neg_add_cancel _

theorem double_annihilation_norm_le {n : ℕ} (j k : Fin n) (x : Hilbert n) :
    ‖annihilation k (annihilation j x)‖ ≤ ‖x‖ :=
  (transition_norm_le k false _).trans (transition_norm_le j false x)

end Occupation
end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Basic
attribute [-instance] _root_.OAI.LaughlinGap.Spin.instDecidableEqOrbitalTriple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Basic. -/

noncomputable section


namespace LaughlinGap
export _root_.OAI.Laughlin (Configuration State Antisymmetric pairCoefficient pairAmplitude energy SpinorVariables bracket laughlinPolynomial monomialExponent laughlinVector distanceToLaughlinSq )
open scoped BigOperators

theorem orbitalTriple_card (D : ℕ) :
    Fintype.card (OrbitalTriple D) =
      ∑ n ∈ Finset.range (D + 1), (n + 1) / 2 := by
  rw [← Fintype.card_congr (orbitalTripleEquiv D), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => (n + 1) / 2) (D + 1)

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NormalOrder
attribute [-simp] _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Order. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma sum_increasing_pairs {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    2 * (∑ a : PairLabel n, f a.val.1 a.val.2) = ∑ i, ∑ j, f i j := by
  classical
  have htri : (∑ a : PairLabel n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
      (by simp) (fun a => f a.1 a.2)]
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  rw [htri]
  conv_rhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]
  ring

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Occupation. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complexify_injective : Function.Injective (complexify (ι := ι)) := by
  intro A B h
  apply_fun Matrix.toEuclideanLin.symm at h
  simp only [complexify, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearEquiv.symm_apply_apply] at h
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

lemma complexify_positive {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (complexify A).IsPositive := by
  rw [complexify, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.isPositive_toEuclideanLin_iff]
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.map_mul]
  have he : (star B).map (algebraMap ℝ ℂ) =
      (B.map (algebraMap ℝ ℂ)).conjTranspose := by
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma annihilation_creation {n : ℕ} (i j : Fin n) :
    annihilation i * creation j + creation j * annihilation i = if i=j then 1 else 0 := by
  apply complexify_injective
  simp only [map_add, map_mul, complexify_annihilation, complexify_creation, apply_ite,
    map_one, map_zero]
  by_cases h : i=j <;> simpa [h, Module.End.one_eq_id, Module.End.mul_eq_comp] using
    Occupation.annihilation_creation_CAR i j

lemma annihilation_anticommute {n : ℕ} (i j : Fin n) :
    annihilation i * annihilation j = -(annihilation j * annihilation i) := by
  apply complexify_injective
  simp only [map_mul, map_neg, complexify_annihilation]
  exact Occupation.annihilation_anticommute i j

lemma secondQuantization_transpose {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    (secondQuantization L).transpose = secondQuantization L.transpose := by
  simp only [secondQuantization, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.transpose_mul, creation, Matrix.transpose_apply, Matrix.transpose_transpose]
  rw [Finset.sum_comm]

lemma elementary_commutator_annihilation {n : ℕ} (i j k : Fin n) :
    (creation i * annihilation j) * annihilation k -
      annihilation k * (creation i * annihilation j) =
        -(if k=i then annihilation j else 0) := by
  have h := annihilation_creation k i
  have h' := annihilation_anticommute j k
  have hm := congrArg (fun B : FockMatrix n => B * annihilation j) h
  simp only [add_mul] at hm
  rw [← mul_assoc] 
  rw [mul_assoc (creation i), h', mul_neg, ← mul_assoc]
  rw [sub_eq_add_neg, ← neg_add, add_comm, hm]
  split_ifs <;> simp

lemma commutator_annihilation {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Averaging.commutator (secondQuantization L) (annihilation k) =
      -∑ j, L k j • annihilation j := by
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk,
    secondQuantization, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, ← Finset.sum_sub_distrib, ← smul_sub,
    elementary_commutator_annihilation, smul_neg, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_ite, smul_zero]
  simp

lemma commutator_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L A B : Matrix ι ι ℝ) :
    Averaging.commutator L (A*B) = Averaging.commutator L A * B + A * Averaging.commutator L B := by
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk]
  noncomm_ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CovariantLift
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariant Lift. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
lemma lift_rankOne [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (x y : ι → ℝ) :
    lift B (Matrix.vecMulVec x y) = (combination B x).transpose * combination B y := by
  simp only [lift, combination, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply,
    Matrix.transpose_sum, Matrix.transpose_smul, Matrix.sum_mul, Matrix.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

lemma lift_positive (B : ι → Matrix κ κ ℝ) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : (lift B A).PosSemidef := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have he : star C * C = ∑ k, Matrix.vecMulVec (fun i => C k i) (fun i => C k i) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [he, map_sum]
  apply Matrix.posSemidef_sum
  intro k hk
  rw [lift_rankOne]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (combination B (fun i => C k i))

lemma commutator_transpose (L A : Matrix κ κ ℝ) :
    commutator L A.transpose = -(commutator L.transpose A).transpose := by
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  abel

omit [DecidableEq ι] in
lemma Covariant.transpose [DecidableEq ι] {L : Matrix κ κ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L D B) :
    Covariant L.transpose D.transpose B where
  lower i := h.raise i
  raise i := by simpa using h.lower i

lemma Covariant.commutator_lift {L : Matrix κ κ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L D B) (A : Matrix ι ι ℝ) :
    commutator L (lift B A) = lift B (commutator D A) := by
  have ht (i : ι) : commutator L (B i).transpose = ∑ k, D k i • (B k).transpose := by
    rw [commutator_transpose, h.raise, Matrix.transpose_neg, neg_neg]
    simp only [Matrix.transpose_sum, Matrix.transpose_smul]
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [map_sum, map_smul, commutator_mul, ht, h.lower, Matrix.sum_mul,
    Matrix.mul_neg, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← sub_eq_add_neg, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply,
    Matrix.mul_apply, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]
  congr 1
  · conv_lhs =>
      rw [Finset.sum_comm]
      arg 2
      ext j
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_comm

theorem Covariant.average_lift {L : Matrix κ κ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L D B) (A : Matrix ι ι ℝ) :
    average (rotationCommutant L) (lift B A) = lift B (average (rotationCommutant D) A) := by
  apply rotation_average_natural
  · exact fun A => (h.commutator_lift A).symm
  · exact fun A => (h.transpose.commutator_lift A).symm

theorem annihilation_covariant {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    Covariant (secondQuantization L) L annihilation where
  lower i := commutator_annihilation L i
  raise i := by rw [secondQuantization_transpose]; exact commutator_annihilation L.transpose i

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntertwiningSpin
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec _root_.OAI.LaughlinGap.Spin.nestedBasis_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intertwining Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

namespace LadderMap
variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
variable {S : LadderSystem ι} {T : LadderSystem κ} {U : LadderSystem σ}

lemma weight (A : LadderMap S T) (x : ι → ℝ) :
    T.weight (A.toLinearMap x) = A.toLinearMap (S.weight x) := by
  rw [T.weight_eq, A.raise, A.lower, S.weight_eq, map_sub, A.lower, A.raise]

lemma casimir (A : LadderMap S T) (x : ι → ℝ) :
    T.casimir (A.toLinearMap x) = A.toLinearMap (S.casimir x) := by
  simp only [LadderSystem.casimir_apply, A.weight, A.lower, A.raise, map_add, map_smul]

lemma raw (A : LadderMap S T) (x : ι → ℝ) (l : ℕ) :
    T.raw (A.toLinearMap x) l = A.toLinearMap (S.raw x l) := by
  induction l with
  | zero => rfl
  | succ l ih => rw [LadderSystem.raw_succ, LadderSystem.raw_succ, ih, A.lower]

lemma normalized (A : LadderMap S T) (x : ι → ℝ) (d l : ℕ) :
    T.normalized (A.toLinearMap x) d l = A.toLinearMap (S.normalized x d l) := by
  simp only [LadderSystem.normalized, map_smul, A.raw]

end LadderMap

theorem coupledTensor_expansion (n m : ℕ)
    (y : (Fin (n+1) × Fin (m+1)) → ℝ) :
    (∑ i : CoupledIndex n m,
      dotProduct (coupledTensor n m i.1.val i.2.val) y •
        coupledTensor n m i.1.val i.2.val) = y := by
  funext pq
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) => x pq)
    ((coupledBasis n m).sum_repr (WithLp.toLp 2 y))
  simpa only [OrthonormalBasis.repr_apply_apply, coupledBasis_apply, coupledFamily,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.smul_apply, WithLp.toLp_ofLp, Pi.smul_apply,
    smul_eq_mul, dotProduct, mul_comm] using h

lemma spinCasimir_injective :
    Function.Injective (fun d : ℕ => (d : ℝ)*(d+2)) := by
  intro d e h
  have hd : (0 : ℝ) ≤ d := by positivity
  have he : (0 : ℝ) ≤ e := by positivity
  have hs : 0 < (d : ℝ)+e+2 := by positivity
  have hh : ((d : ℝ)-e)*((d : ℝ)+e+2) = 0 := by nlinarith
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hs.ne')
  exact_mod_cast heq

theorem coupledHighest_eigenline {n m z : ℕ} (hz : z ≤ min n m)
    {y : (Fin (n+1) × Fin (m+1)) → ℝ}
    (hyH : (tensorSpin n m).weight y = ((n+m-2*z : ℕ) : ℝ) • y)
    (hyC : (tensorSpin n m).casimir y =
      (((n+m-2*z : ℕ) : ℝ)*((n+m-2*z : ℕ)+2)) • y) :
    y = dotProduct (highestTensor n m z) y • highestTensor n m z := by
  classical
  let iz : CoupledIndex n m := ⟨⟨z,by omega⟩,0⟩
  calc
    y = ∑ i : CoupledIndex n m,
        dotProduct (coupledTensor n m i.1.val i.2.val) y •
          coupledTensor n m i.1.val i.2.val := (coupledTensor_expansion n m y).symm
    _ = dotProduct (highestTensor n m z) y • highestTensor n m z := by
      apply Finset.sum_eq_single iz
      · intro i _ hne
        obtain ⟨w,k⟩ := i
        have hw : w.val ≤ min n m := Nat.le_of_lt_succ w.isLt
        have hk : k.val ≤ n+m-2*w.val := Nat.le_of_lt_succ k.isLt
        have horth : dotProduct (coupledTensor n m w.val k.val) y = 0 := by
          by_cases hwz : w.val=z
          · have hk0 : k.val ≠ 0 := by
              intro hk0
              apply hne
              apply Sigma.ext
              · exact Fin.ext hwz
              · apply (Fin.heq_ext_iff (by dsimp [iz]; omega)).mpr
                exact hk0
            apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).weight_adjoint
              (coupledTensor_weight hw hk) hyH
            simp only [hwz]
            intro hh
            apply hk0
            have : (k.val : ℝ) = 0 := by linarith
            exact_mod_cast this
          · apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).casimir_adjoint
              (coupledTensor_casimir hw hk) hyC
            intro hh
            have HD := spinCasimir_injective hh
            have := le_min_iff.mp hw
            have := le_min_iff.mp hz
            omega
        rw [horth, zero_smul]
      · simp

lemma LadderSystem.raw_smul {ι : Type*} [Fintype ι] (S : LadderSystem ι)
    (c : ℝ) (x : ι → ℝ) (l : ℕ) : S.raw (c • x) l = c • S.raw x l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [S.raw_succ, ih, map_smul, S.raw_succ]

lemma LadderSystem.normalized_smul {ι : Type*} [Fintype ι] (S : LadderSystem ι)
    (c : ℝ) (x : ι → ℝ) (d l : ℕ) :
    S.normalized (c • x) d l = c • S.normalized x d l := by
  simp only [LadderSystem.normalized, S.raw_smul, smul_comm c]

theorem tensorSpin_schur {n m z l : ℕ} (hz : z ≤ min n m) (hl : l ≤ n+m-2*z)
    (A : LadderMap (tensorSpin n m) (tensorSpin n m)) :
    A.toLinearMap (coupledTensor n m z l) =
      dotProduct (highestTensor n m z) (A.toLinearMap (highestTensor n m z)) •
        coupledTensor n m z l := by
  have hh : A.toLinearMap (highestTensor n m z) =
      dotProduct (highestTensor n m z) (A.toLinearMap (highestTensor n m z)) •
        highestTensor n m z := by
    apply coupledHighest_eigenline hz
    · rw [A.weight, highestTensor_weight hz, map_smul]
    · rw [A.casimir]
      have hc := coupledTensor_casimir hz (by omega : 0 ≤ n+m-2*z)
      rw [coupledTensor_zero] at hc
      rw [hc, map_smul]
  rw [coupledTensor_eq_normalized hz hl, ← A.normalized]
  conv_lhs => rw [hh, LadderSystem.normalized_smul]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpinAveraging
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

lemma toMatrix_transposeMap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    LinearMap.toMatrix' (transposeMap A) = (LinearMap.toMatrix' A).transpose := by
  ext i j
  simp only [LinearMap.toMatrix'_apply, transposeMap, Matrix.transpose_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  change dotProduct (A _) (Pi.single j 1) = _
  rw [dotProduct_single_one]
  apply congrArg (fun x : ι → ℝ => A x j)
  funext k
  by_cases hk : i=k <;> simp [hk, eq_comm]

lemma coupledEmbedding_entry {n m z : ℕ} (hz : z ≤ min n m)
    (a : Fin (n+1) × Fin (m+1)) (l : Fin (n+m-2*z+1)) :
    LinearMap.toMatrix' (coupledEmbedding hz).toLinearMap a l = coupledTensor n m z l.val a := by
  rw [LinearMap.toMatrix'_apply, coupledEmbedding_apply]
  simp [Pi.single_apply, ite_apply]

lemma tensorProjection_eq {n m z : ℕ} (hz : z ≤ min n m) :
    tensorProjection hz = ∑ l : Fin (n+m-2*z+1),
      Matrix.vecMulVec (coupledTensor n m z l.val) (coupledTensor n m z l.val) := by
  simp only [tensorProjection, LadderMap.comp, LadderMap.transpose,
    LinearMap.toMatrix'_comp, toMatrix_transposeMap]
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coupledEmbedding_entry,
    Matrix.sum_apply, Matrix.vecMulVec_apply]

lemma trace_mul_rankOne {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    (A * Matrix.vecMulVec x y).trace = dotProduct y (A.mulVec x) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CovariantFamily
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariant Family. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin

variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

omit [DecidableEq ι] in
lemma Covariant.combination_lower [DecidableEq ι] {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix σ σ ℝ} (h : Covariant L D B) (x : ι → ℝ) :
    commutator L (combination B x) = -combination B (D.transpose.mulVec x) := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    h.lower, smul_neg, Finset.smul_sum, smul_smul, Finset.sum_neg_distrib,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

lemma Covariant.combination_raise {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix σ σ ℝ} (h : Covariant L D B) (x : ι → ℝ) :
    commutator L.transpose (combination B x) = -combination B (D.mulVec x) := by
  simpa using h.transpose.combination_lower x

omit [DecidableEq κ] [Fintype σ] [DecidableEq σ] in
lemma combination_embeddingFamily [DecidableEq κ] [Fintype σ] [DecidableEq σ]
    {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (B : κ → Matrix σ σ ℝ) (x : ι → ℝ) :
    combination (embeddingFamily A B) x = combination B (A.toLinearMap x) := by
  rw [A.toLinearMap.pi_apply_eq_sum_univ x, map_sum]
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, embeddingFamily, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : (Pi.single i 1 : ι → ℝ) = (fun j => if i=j then 1 else 0) := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [hs]

lemma Covariant.embedding {L : Matrix σ σ ℝ} {S : LadderSystem ι}
    {T : LadderSystem κ} {B : κ → Matrix σ σ ℝ}
    (h : Covariant L (loweringMatrix T) B) (A : LadderMap S T) :
    Covariant L (loweringMatrix S) (embeddingFamily A B) where
  lower i := by
    change commutator L (combination B _) = _
    rw [h.combination_lower, loweringMatrix_transpose, LinearMap.toMatrix'_mulVec]
    change -combination B (T.raise (A.toLinearMap (Pi.single i 1))) = _
    rw [A.raise, ← combination_embeddingFamily]
    congr 1
    simp only [combination, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have he := congrArg (fun M : Matrix ι ι ℝ => M j i) (loweringMatrix_transpose S)
    simpa only [Matrix.transpose_apply, loweringMatrix, LinearMap.toMatrix'_apply] using he.symm
  raise i := by
    change commutator L.transpose (combination B _) = _
    rw [h.combination_raise, loweringMatrix, LinearMap.toMatrix'_mulVec]
    change -combination B (T.lower (A.toLinearMap (Pi.single i 1))) = _
    rw [A.lower, ← combination_embeddingFamily]
    rfl

lemma loweringMatrix_tensor (S : LadderSystem ι) (T : LadderSystem κ)
    (i j : ι × κ) :
    loweringMatrix (S.tensor T) i j =
      (if i.2=j.2 then loweringMatrix S i.1 j.1 else 0) +
      (if i.1=j.1 then loweringMatrix T i.2 j.2 else 0) := by
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  simp only [loweringMatrix, LinearMap.toMatrix'_apply, LadderSystem.tensor,
    LinearMap.add_apply, onFirstEnd_apply, onSecondEnd_apply, Pi.add_apply]
  have hf : (fun a : ι => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (a,i₂)) =
      if i₂=j₂ then Pi.single j₁ 1 else 0 := by
    funext a
    by_cases he : i₂=j₂ <;> simp [he, Pi.single_apply, Prod.mk.injEq, eq_comm]
  have hs : (fun a : κ => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (i₁,a)) =
      if i₁=j₁ then Pi.single j₂ 1 else 0 := by
    funext a
    by_cases he : i₁=j₁ <;> simp [he, Pi.single_apply, Prod.mk.injEq, eq_comm]
  change S.lower (fun a => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (a,i₂)) i₁ +
    T.lower (fun a => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (i₁,a)) i₂ = _
  rw [hf, hs]
  split_ifs <;> simp_all

lemma product_commutator {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ} {E : Matrix κ κ ℝ}
    {B : ι → Matrix σ σ ℝ} {C : κ → Matrix σ σ ℝ}
    (hB : ∀ i, commutator L (B i) = -∑ j, D i j • B j)
    (hC : ∀ i, commutator L (C i) = -∑ j, E i j • C j) (i : ι × κ) :
    commutator L (productFamily B C i) =
      -∑ j : ι × κ, ((if i.2=j.2 then D i.1 j.1 else 0) +
        (if i.1=j.1 then E i.2 j.2 else 0)) • productFamily B C j := by
  simp only [productFamily, commutator_mul, hB, hC, neg_mul, Matrix.mul_neg,
    Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm,
    Fintype.sum_prod_type, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, Finset.sum_const_zero, Finset.sum_ite_eq]
  abel

lemma Covariant.product {L : Matrix σ σ ℝ} {S : LadderSystem ι} {T : LadderSystem κ}
    {B : ι → Matrix σ σ ℝ} {C : κ → Matrix σ σ ℝ}
    (hB : Covariant L (loweringMatrix S) B) (hC : Covariant L (loweringMatrix T) C) :
    Covariant L (loweringMatrix (S.tensor T)) (productFamily B C) where
  lower i := by simpa only [loweringMatrix_tensor] using product_commutator hB.lower hC.lower i
  raise i := by
    simpa only [Matrix.transpose_apply, loweringMatrix_tensor, eq_comm] using
      product_commutator hB.transpose.lower hC.transpose.lower i

omit [DecidableEq ι] in
lemma Covariant.smul [DecidableEq ι] {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix σ σ ℝ} (h : Covariant L D B) (r : ℝ) :
    Covariant L D (fun i => r • B i) where
  lower i := by simp only [map_smul, h.lower, smul_neg, Finset.smul_sum, smul_comm r]
  raise i := by simp only [map_smul, h.raise, smul_neg, Finset.smul_sum, smul_comm r]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IrrepAveraging
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Irrep Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

lemma standardLadderSystem_casimir (n : ℕ) (x : Fin (n+1) → ℝ) :
    (standardLadderSystem n).casimir x = ((n : ℝ)*(n+2)) • x := by
  funext p
  simp only [LadderSystem.casimir_apply, standardLadderSystem, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, weight_apply, lowering_raising_apply]
  ring

theorem standardLadderMap_eq_zero {n m : ℕ} (hnm : n ≠ m)
    (A : LadderMap (standardLadderSystem n) (standardLadderSystem m)) :
    A.toLinearMap = 0 := by
  apply LinearMap.ext
  intro x
  have h := A.casimir x
  rw [standardLadderSystem_casimir, standardLadderSystem_casimir, map_smul] at h
  have hne : (m : ℝ)*(m+2) ≠ (n : ℝ)*(n+2) := by
    intro he
    exact hnm (spinCasimir_injective he).symm
  funext j
  have he := congrFun h j
  change (m : ℝ)*(m+2)*A.toLinearMap x j = (n : ℝ)*(n+2)*A.toLinearMap x j at he
  exact (mul_left_cancel₀ (sub_ne_zero.mpr hne) (by nlinarith :
    ((m : ℝ)*(m+2)-(n : ℝ)*(n+2)) * A.toLinearMap x j =
      ((m : ℝ)*(m+2)-(n : ℝ)*(n+2))*0))

lemma ladderStep_pos (n : ℕ) (p : Fin n) : 0 < ladderStep n p := by
  apply Real.sqrt_pos.mpr
  have hp : (p.val : ℝ) < n := by exact_mod_cast p.isLt
  exact mul_pos (by positivity) (by linarith)

lemma weight_single (n : ℕ) (i : Fin (n+1)) :
    weight n (Pi.single i 1) = ((n : ℝ)-2*i.val) • Pi.single i 1 := by
  funext j
  by_cases h : i=j
  · subst j; simp
  · simp [h, eq_comm]

lemma lowering_single (n : ℕ) (p : Fin n) :
    lowering n (Pi.single p.castSucc 1) = ladderStep n p • Pi.single p.succ 1 := by
  funext j
  cases j using Fin.cases with
  | zero => simp
  | succ j =>
    by_cases h : j=p
    · subst j; simp
    · have hn : p.val ≠ j.val := by intro hp; apply h; exact (Fin.ext hp).symm
      simp [Fin.ext_iff, hn, eq_comm]

theorem standardLadderMap_schur {n : ℕ}
    (A : LadderMap (standardLadderSystem n) (standardLadderSystem n)) (x : Fin (n+1) → ℝ) :
    A.toLinearMap x = A.toLinearMap (Pi.single 0 1) 0 • x := by
  let c : Fin (n+1) → ℝ := fun i => A.toLinearMap (Pi.single i 1) i
  have hd (i : Fin (n+1)) : A.toLinearMap (Pi.single i 1) = c i • Pi.single i 1 := by
    have hw := A.weight (Pi.single i 1)
    change weight n (A.toLinearMap (Pi.single i 1)) = A.toLinearMap (weight n _) at hw
    rw [weight_single, map_smul] at hw
    funext j
    by_cases h : i=j
    · subst j; simp [c]
    · have hv : i.val ≠ j.val := by exact fun he => h (Fin.ext he)
      have he := congrFun hw j
      simp only [weight_apply, Pi.smul_apply, smul_eq_mul] at he
      have hne : ((n : ℝ)-2*j.val)-((n : ℝ)-2*i.val) ≠ 0 := by
        intro he
        apply hv
        exact_mod_cast (by linarith : (i.val : ℝ)=j.val)
      have hz : A.toLinearMap (Pi.single i 1) j = 0 := by
        apply (mul_eq_zero.mp (show (((n : ℝ)-2*j.val)-((n : ℝ)-2*i.val)) *
          A.toLinearMap (Pi.single i 1) j = 0 by nlinarith)).resolve_left hne
      simp [hz, h, eq_comm]
  have hc : ∀ i, c i = c 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have he := A.lower (Pi.single i.castSucc 1)
      change lowering n (A.toLinearMap (Pi.single i.castSucc 1)) = A.toLinearMap (lowering n _) at he
      rw [hd, map_smul, lowering_single, map_smul, hd] at he
      have hh := congrFun he i.succ
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at hh
      have hci : c i.succ = c i.castSucc := by
        nlinarith [ladderStep_pos n i]
      exact hci.trans ih
  rw [A.toLinearMap.pi_apply_eq_sum_univ x]
  have hs (i : Fin (n+1)) : (fun j => if i=j then (1:ℝ) else 0) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  simp only [hs, hd, hc, smul_smul]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, Pi.smul_apply, c, mul_comm]

theorem standardSpin_average (n : ℕ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    average (rotationCommutant (loweringMatrix (standardLadderSystem n))) A =
      (A.trace / (n+1 : ℕ)) • 1 := by
  let S := rotationCommutant (loweringMatrix (standardLadderSystem n))
  let Y := average S A
  let L := commutantLadderMap (standardLadderSystem n) (average_mem S A)
  let c := L.toLinearMap (Pi.single 0 1) 0
  have he : Y = c • 1 := by
    apply Matrix.mulVec_injective
    funext x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hv := standardLadderMap_schur L x
    change Matrix.toLin' Y x = c • x at hv
    rwa [Matrix.toLin'_apply] at hv
  have hc : c = A.trace / (n+1 : ℕ) := by
    have ht := average_trace S A
    change Y.trace = A.trace at ht
    rw [he, Matrix.trace_smul, Matrix.trace_one] at ht
    apply (eq_div_iff (by positivity : ((n+1 : ℕ) : ℝ) ≠ 0)).mpr
    simpa using ht
  exact he.trans (congrArg (fun t : ℝ => t • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) hc)

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

theorem pairCoefficient_binomial {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-1)
    (i j : Fin (Q+1)) :
    pairCoefficient Q p i j = if i.val+j.val=p+1 then
      ((i.val : ℝ)-j.val)*Real.sqrt (Q.choose i.val : ℝ)*Real.sqrt (Q.choose j.val : ℝ) /
        Real.sqrt (2*Q*((2*Q-2).choose p : ℝ)) else 0 := by
  have hch : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show p ≤ 2*Q-2 by omega)).ne'
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  have hrad :
      (((Q.descFactorial i.val : ℝ)*(Q.descFactorial j.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*
          (i.val.factorial : ℝ)*(j.val.factorial : ℝ))) =
      ((Q.choose i.val : ℝ)*Q.choose j.val) / ((Q : ℝ)*((2*Q-2).choose p : ℝ)) := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  unfold pairCoefficient
  split_ifs
  · rw [hrad, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity :
        0 ≤ (Q.choose i.val : ℝ)),
      show (2 : ℝ)*Q*((2*Q-2).choose p : ℝ) =
        2*(Q*((2*Q-2).choose p : ℝ)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · rfl

lemma sqrt_choose_lowering {Q k : ℕ} (hk : k < Q) :
    Real.sqrt (((k : ℝ)+1)*((Q : ℝ)-k))*Real.sqrt (Q.choose k : ℝ) =
      ((k : ℝ)+1)*Real.sqrt (Q.choose (k+1) : ℝ) := by
  have hq : (k : ℝ) ≤ Q := by exact_mod_cast hk.le
  have hc : (Q.choose (k+1) : ℝ)*((k : ℝ)+1) =
      (Q.choose k : ℝ)*((Q : ℝ)-k) := by
    have H := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq Q k)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le] using H
  rw [← Real.sqrt_mul (by positivity : 0 ≤ ((k : ℝ)+1)*((Q : ℝ)-k))]
  rw [show (((k : ℝ)+1)*((Q : ℝ)-k))*(Q.choose k : ℝ) =
      (((k : ℝ)+1)^2)*(Q.choose (k+1) : ℝ) by nlinarith [hc]]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

lemma binomialPairTensor_swap (Q p : ℕ) (i j : Fin (Q+1)) :
    binomialPairTensor Q p (j,i) = -binomialPairTensor Q p (i,j) := by
  unfold binomialPairTensor
  by_cases h : i.val+j.val=p+1
  · simp only [h, Nat.add_comm j.val i.val, ite_true]
    ring
  · simp [h, Nat.add_comm j.val i.val]

lemma binomialPairTensor_lower_first (Q p : ℕ) (i j : Fin (Q+1)) :
    lowering Q (fun a => binomialPairTensor Q p (a,j)) i =
      if i.val+j.val=p+2 then
        (i.val : ℝ)*((i.val : ℝ)-1-j.val)*Real.sqrt (Q.choose i.val : ℝ)*
          Real.sqrt (Q.choose j.val : ℝ) else 0 := by
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    rw [lowering_succ]
    simp only [binomialPairTensor, Fin.val_castSucc, Fin.val_succ]
    by_cases h : i.val+j.val=p+1
    · rw [ite_eq_left h, ite_eq_left (by omega : i.val+1+j.val=p+2)]
      simp only [Nat.cast_add, Nat.cast_one, ladderStep]
      have hc := sqrt_choose_lowering i.isLt
      calc
        _ = (((i.val : ℝ)-j.val)*Real.sqrt (Q.choose j.val : ℝ)) *
            (Real.sqrt (((i.val : ℝ)+1)*((Q : ℝ)-i.val))*Real.sqrt (Q.choose i.val : ℝ)) := by ring
        _ = _ := by rw [hc]; ring
    · rw [ite_eq_right h, ite_eq_right (by omega : ¬i.val+1+j.val=p+2), mul_zero]

theorem binomialPairTensor_lower (Q p : ℕ) :
    (tensorSpin Q Q).lower (binomialPairTensor Q p) =
      ((p : ℝ)+1) • binomialPairTensor Q (p+1) := by
  funext ⟨i,j⟩
  rw [tensorSpin_lower, binomialPairTensor_lower_first]
  have hswap : (fun a => binomialPairTensor Q p (i,a)) =
      -(fun a => binomialPairTensor Q p (a,i)) := by
    funext a
    exact binomialPairTensor_swap Q p a i
  rw [hswap, map_neg]
  simp only [Pi.neg_apply]
  rw [binomialPairTensor_lower_first]
  simp only [binomialPairTensor, Pi.smul_apply, smul_eq_mul]
  by_cases h : i.val+j.val=p+2
  · simp only [ite_eq_left h, ite_eq_left (by omega : j.val+i.val=p+2)]
    have hc : (i.val : ℝ)+j.val=(p : ℝ)+2 := by exact_mod_cast h
    rw [show (p : ℝ)+1=(i.val : ℝ)+j.val-1 by linarith]
    ring
  · simp only [ite_eq_right h, ite_eq_right (by omega : ¬j.val+i.val=p+2), neg_zero, zero_add, mul_zero]

lemma physicalPairTensor_binomial {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-1) :
    physicalPairTensor Q p =
      (1/Real.sqrt (2*Q*((2*Q-2).choose p : ℝ))) • binomialPairTensor Q p := by
  funext ⟨i,j⟩
  simp only [physicalPairTensor, pairCoefficient_binomial hQ hp, binomialPairTensor,
    Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

lemma pairNormalization_step {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-2) :
    (1/Real.sqrt (2*Q*((2*Q-2).choose p : ℝ)))*((p : ℝ)+1) =
      Real.sqrt (((p : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-p))*
        (1/Real.sqrt (2*Q*((2*Q-2).choose (p+1) : ℝ))) := by
  have hc := sqrt_choose_lowering hp
  have hs0 : Real.sqrt (((2*Q-2).choose p : ℝ)) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    exact_mod_cast Nat.choose_pos hp.le
  have hs1 : Real.sqrt (((2*Q-2).choose (p+1) : ℝ)) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    exact_mod_cast Nat.choose_pos hp
  simp only [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2*Q)]
  field_simp
  nlinarith [congrArg (fun a => a*Real.sqrt (2*(Q : ℝ))) hc]

theorem physicalPairTensor_lower {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-2) :
    (tensorSpin Q Q).lower (physicalPairTensor Q p) =
      Real.sqrt (((p : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-p)) • physicalPairTensor Q (p+1) := by
  rw [physicalPairTensor_binomial hQ (by omega), map_smul, binomialPairTensor_lower,
    physicalPairTensor_binomial hQ (by omega), smul_smul, smul_smul,
    pairNormalization_step hQ hp]

lemma highestWeight_first_one {Q : ℕ} (hQ : 0 < Q) :
    highestWeight Q Q 1 1 = 1 := by
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  simp only [highestWeight, Nat.choose_self, Nat.cast_one, Finset.prod_range_one,
    one_mul, highestFactor, Nat.cast_zero, sub_zero]
  rw [show (Q : ℝ)-1+0+1 = Q by ring, div_self hQr]

lemma highestNormalization_first {Q : ℕ} (hQ : 0 < Q) :
    highestNormalization Q Q 1 = 2 := by
  norm_num [highestNormalization, Finset.sum_range_succ, highestWeight_first_one hQ]

lemma sqrt_Q_over_sqrt_twoQ {Q : ℕ} (hQ : 0 < Q) :
    Real.sqrt (Q : ℝ)/Real.sqrt (2*Q : ℝ) = 1/Real.sqrt 2 := by
  have hQr : Real.sqrt (Q : ℝ) ≠ 0 := by positivity
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

theorem physicalPairTensor_zero {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalPairTensor Q 0 = highestTensor Q Q 1 := by
  have hQ0 : 0 < Q := by omega
  funext ⟨i,j⟩
  simp only [physicalPairTensor, pairCoefficient_binomial hQ (by omega : 0 < 2*Q-1),
    highestTensor]
  by_cases h : i.val+j.val=1
  · rw [ite_eq_left h, ite_eq_left h]
    rcases (show i.val=0 ∧ j.val=1 ∨ i.val=1 ∧ j.val=0 by omega) with hij | hij
    · simp only [hij.1, hij.2, Nat.cast_zero, Nat.cast_one, zero_sub,
        Nat.choose_zero_right, Nat.choose_one_right, mul_one, highestCoefficient,
        highestWeight_zero, highestNormalization_first hQ0]
      simp only [Nat.sub_zero, pow_one, Real.sqrt_one, one_mul, neg_mul, neg_div]
      exact congrArg Neg.neg (sqrt_Q_over_sqrt_twoQ hQ0)
    · simp only [hij.1, hij.2, Nat.cast_zero, Nat.cast_one, sub_zero,
        Nat.choose_zero_right, Nat.choose_one_right, mul_one, one_mul, highestCoefficient,
        highestWeight_first_one hQ0, highestNormalization_first hQ0,
        Nat.sub_self, pow_zero, Real.sqrt_one]
      exact sqrt_Q_over_sqrt_twoQ hQ0
  · simp only [ite_eq_right h]

theorem physicalPairTensor_eq_coupled {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    physicalPairTensor Q p = coupledTensor Q Q 1 p := by
  have hz : 1 ≤ min Q Q := by omega
  have hd : Q+Q-2*1=2*Q-2 := by omega
  rw [coupledTensor_eq_normalized hz (by omega), hd]
  induction p with
  | zero => rw [LadderSystem.normalized_zero, physicalPairTensor_zero hQ]
  | succ p ih =>
    have hl : p < 2*Q-2 := by omega
    have ha : Real.sqrt (((p : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-p)) ≠ 0 := by
      apply (Real.sqrt_pos.mpr _).ne'
      have hpr : (p : ℝ) < (2*Q-2 : ℕ) := by exact_mod_cast hl
      exact mul_pos (by positivity) (by linarith)
    rw [LadderSystem.normalized_succ _ _ hl, ← ih (by omega), physicalPairTensor_lower hQ hl,
      smul_smul, one_div_mul_cancel ha, one_smul]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma pairInclusion_apply {Q : ℕ} (hQ : 2 ≤ Q) (a : Fin (2*Q-2+1) → ℝ) :
    (pairInclusion hQ).toLinearMap a =
      ∑ p : Fin (2*Q-2+1), a p • physicalPairTensor Q p.val := by
  simp only [pairInclusion, LadderSystem.embeddingMap, LadderSystem.embedding_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [physicalPairTensor_eq_coupled hQ (Nat.le_of_lt_succ p.isLt),
    coupledTensor_eq_normalized (by omega : 1 ≤ min Q Q) (by omega : p.val ≤ Q+Q-2*1)]
  congr 2
  omega

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PhysicalAveraging
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Averaging. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin

lemma physicalPair_embedding {Q : ℕ} (hQ : 2 ≤ Q) (p : Fin (2*Q-2+1)) :
    physicalPair Q p.val = (1/Real.sqrt 2) •
      embeddingFamily (pairInclusion hQ) (productFamily annihilation annihilation) p := by
  simp only [embeddingFamily, pairInclusion_apply, Pi.single_apply,
    ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem physicalPair_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (standardLadderSystem (2*Q-2)))
      (fun p : Fin (2*Q-2+1) => physicalPair Q p.val) := by
  have ha := annihilation_covariant (loweringMatrix (standardLadderSystem Q))
  have hp := (ha.product ha).embedding (pairInclusion hQ)
  have he : (fun p : Fin (2*Q-2+1) => physicalPair Q p.val) =
      (fun p => (1/Real.sqrt 2) • embeddingFamily (pairInclusion hQ)
        (productFamily annihilation annihilation) p) := funext (physicalPair_embedding hQ)
  rw [he]
  exact hp.smul (1/Real.sqrt 2)

lemma lift_identity {ι κ : Type*} (B : ι → Matrix κ κ ℝ) [Fintype ι] [DecidableEq ι]
    [Fintype κ] : lift B 1 = ∑ i, (B i).transpose * B i := by
  simp [lift, Matrix.one_apply, ite_smul]

lemma physicalPair_sum {Q : ℕ} (hQ : 2 ≤ Q) :
    (∑ p : Fin (2*Q-2+1), (physicalPair Q p.val).transpose * physicalPair Q p.val) =
      physicalHamiltonian Q := by
  let e : Fin (2*Q-2+1) ≃ Fin (2*Q-1) := finCongr (by omega)
  exact e.sum_comp (fun p => (physicalPair Q p.val).transpose * physicalPair Q p.val)

lemma physicalPair_single {Q : ℕ} (hQ : 2 ≤ Q) (p : Fin (2*Q-2+1)) :
    average (rotationCommutant (fockLowering Q))
      ((physicalPair Q p.val).transpose * physicalPair Q p.val) =
      (1/(2*Q-1 : ℕ) : ℝ) • physicalHamiltonian Q := by
  let B := fun p : Fin (2*Q-2+1) => physicalPair Q p.val
  have hc : combination B (Pi.single p 1) = physicalPair Q p.val := by
    simp [combination, B, Pi.single_apply, ite_smul]
  rw [← hc, ← lift_rankOne B, (physicalPair_covariant hQ).average_lift,
    standardSpin_average, Matrix.trace_vecMulVec]
  simp only [dotProduct_single_one, Pi.single_eq_same, map_smul]
  rw [lift_identity, physicalPair_sum hQ]
  rw [show 2*Q-2+1=2*Q-1 by omega]

lemma physicalPair_single_val {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-1) :
    average (rotationCommutant (fockLowering Q))
      ((physicalPair Q p).transpose * physicalPair Q p) =
      (1/(2*Q-1 : ℕ) : ℝ) • physicalHamiltonian Q :=
  physicalPair_single hQ ⟨p,by omega⟩

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_HighestRatios
attribute [-simp] _root_.OAI.LaughlinGap.Spin.highestCoefficient_zero_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Highest Ratios. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma highest_numerator_product {m z : ℕ} (hz : z ≤ m) (p : ℕ) :
    (∏ k ∈ Finset.range p, ((m : ℝ)-z+k+1)) =
      ((m-z+p).descFactorial p : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.prod_range_succ, ih]
    rw [show m-z+(p+1) = (m-z+p)+1 by omega, Nat.succ_descFactorial_succ]
    push_cast
    rw [Nat.cast_sub hz]
    ring

lemma highest_denominator_product {n p : ℕ} (hp : p ≤ n) :
    (∏ k ∈ Finset.range p, ((n : ℝ)-k)) = (n.descFactorial p : ℝ) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Nat.cast_sub ((Finset.mem_range.mp hk).le.trans hp)]

theorem highestWeight_factorial {n m z p : ℕ} (hz : z ≤ min n m) (hp : p ≤ z) :
    highestWeight n m z p = (z.choose p : ℝ) *
      ((m-z+p).descFactorial p : ℝ) / (n.descFactorial p : ℝ) := by
  simp only [highestWeight, highestFactor, Finset.prod_div_distrib,
    highest_numerator_product (le_min_iff.mp hz).2 p,
    highest_denominator_product (hp.trans (le_min_iff.mp hz).1), mul_div_assoc]

lemma highestCoefficient_zero_ne {n m z : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z 0 ≠ 0 := by
  simp only [highestCoefficient, highestWeight_zero, Real.sqrt_one, mul_one, Nat.sub_zero]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Real.sqrt_pos.mpr (highestNormalization_pos hz)).ne'

theorem highestCoefficient_ratio {n m z p : ℕ} (_hz : z ≤ min n m) (hp : p ≤ z) :
    highestCoefficient n m z p = highestCoefficient n m z 0 *
      ((-1 : ℝ)^p * Real.sqrt (highestWeight n m z p)) := by
  have he : (-1 : ℝ)^(z-p) = (-1 : ℝ)^z * (-1 : ℝ)^p := by
    have hzz : z=(z-p)+p := by omega
    conv_rhs => rw [hzz, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [highestCoefficient, highestWeight_zero, Real.sqrt_one, mul_one, Nat.sub_zero]
  rw [he]
  ring

lemma highestCoefficient_last {n m z : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z z = highestCoefficient n m z 0 *
      ((-1 : ℝ)^z * Real.sqrt ((m.descFactorial z : ℝ)/(n.descFactorial z : ℝ))) := by
  rw [highestCoefficient_ratio hz (le_refl z), highestWeight_factorial hz (le_refl z),
    Nat.sub_add_cancel (le_min_iff.mp hz).2, Nat.choose_self, Nat.cast_one, one_mul]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairDecomposition
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec _root_.OAI.LaughlinGap.Spin.highestCoefficient_zero_zero _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Decomposition. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

lemma highestCoefficient_last_equal_spin {Q r : ℕ} (hr : r ≤ Q) :
    highestCoefficient Q Q r r = (-1 : ℝ)^r * highestCoefficient Q Q r 0 := by
  have hf : (Q.descFactorial r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hr).ne'
  rw [highestCoefficient_last (by simpa using hr), div_self hf, Real.sqrt_one, mul_one,
    mul_comm]

theorem coupledTensor_swap {Q r l : ℕ} (hr : r ≤ Q) (hl : l ≤ Q+Q-2*r)
    (i j : Fin (Q+1)) :
    coupledTensor Q Q r l (j,i) = (-1 : ℝ)^r * coupledTensor Q Q r l (i,j) := by
  have h0 := tensorSpin_schur (by simpa using hr : r ≤ min Q Q)
    (Nat.zero_le _) (tensorSwap Q)
  let r' : Fin (Q+1) := ⟨r, by omega⟩
  have hc := congrFun h0 (0,r')
  simp only [coupledTensor_zero, tensorSwap, highestTensor, LinearMap.coe_mk,
    AddHom.coe_mk, Fin.val_zero, r', zero_add, add_zero, ite_true, Pi.smul_apply,
    smul_eq_mul] at hc
  have hb : dotProduct (highestTensor Q Q r)
      ((tensorSwap Q).toLinearMap (highestTensor Q Q r)) = (-1 : ℝ)^r := by
    apply mul_right_cancel₀ (highestCoefficient_zero_ne (by simpa using hr : r ≤ min Q Q))
    exact hc.symm.trans (highestCoefficient_last_equal_spin hr)
  have h := congrFun (tensorSpin_schur (by simpa using hr : r ≤ min Q Q) hl
    (tensorSwap Q)) (i,j)
  rw [hb] at h
  exact h

lemma coupledTensor_antisymmetric {Q r l : ℕ} (hr : r ≤ Q) (hl : l ≤ Q+Q-2*r)
    (hodd : Odd r) (i j : Fin (Q+1)) :
    coupledTensor Q Q r l (j,i) = -coupledTensor Q Q r l (i,j) := by
  rw [coupledTensor_swap hr hl, hodd.neg_one_pow, neg_one_mul]

lemma coupledTensor_diag_zero {Q r l : ℕ} (hr : r ≤ Q) (hl : l ≤ Q+Q-2*r)
    (hodd : Odd r) (i : Fin (Q+1)) : coupledTensor Q Q r l (i,i) = 0 := by
  have h := coupledTensor_antisymmetric hr hl hodd i i
  linarith

lemma orbitalPair_inner {Q r s l k : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hl : l ≤ Q+Q-2*r) (hk : k ≤ Q+Q-2*s) (hro : Odd r) (hso : Odd s) :
    (∑ a : PairLabel (Q+1), orbitalPairCoefficient Q r l a * orbitalPairCoefficient Q s k a) =
      dotProduct (coupledTensor Q Q r l) (coupledTensor Q Q s k) := by
  have hsum := sum_increasing_pairs
    (fun i j : Fin (Q+1) => coupledTensor Q Q r l (i,j) * coupledTensor Q Q s k (i,j))
    (by intro i j; rw [coupledTensor_antisymmetric hr hl hro j i,
      coupledTensor_antisymmetric hs hk hso j i]; ring)
    (by intro i; rw [coupledTensor_diag_zero hr hl hro i, zero_mul])
  have he (a : PairLabel (Q+1)) :
      orbitalPairCoefficient Q r l a * orbitalPairCoefficient Q s k a =
      2 * (coupledTensor Q Q r l (a.val.1,a.val.2) *
        coupledTensor Q Q s k (a.val.1,a.val.2)) := by
    unfold orbitalPairCoefficient
    linear_combination (coupledTensor Q Q r l (a.val.1,a.val.2) *
      coupledTensor Q Q s k (a.val.1,a.val.2)) *
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  simp only [he, ← Finset.mul_sum]
  rw [hsum]
  simp only [dotProduct, Fintype.sum_prod_type]

theorem orbitalPair_orthonormal {Q r s : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hro : Odd r) (hso : Odd s)
    (l : Fin (Q+Q-2*r+1)) (k : Fin (Q+Q-2*s+1)) :
    (∑ a : PairLabel (Q+1), orbitalPairCoefficient Q r l.val a *
      orbitalPairCoefficient Q s k.val a) = if r=s ∧ l.val=k.val then 1 else 0 := by
  rw [orbitalPair_inner hr hs (Nat.le_of_lt_succ l.isLt) (Nat.le_of_lt_succ k.isLt) hro hso]
  by_cases hrs : r=s
  · subst s
    by_cases hlk : l.val=k.val
    · have : l=k := Fin.ext hlk
      subst k
      simp only [and_self, ite_true]
      exact coupledTensor_norm_sq (by simpa using hr) (Nat.le_of_lt_succ l.isLt)
    · rw [ite_eq_right (by simpa using hlk)]
      exact coupledTensor_orthogonal_same_spin (by simpa using hr)
        (Nat.le_of_lt_succ l.isLt) (Nat.le_of_lt_succ k.isLt) hlk
  · rw [ite_eq_right (by simp [hrs])]
    exact coupledTensor_orthogonal_distinct_spin (by simpa using hr) (by simpa using hs)
      (Nat.le_of_lt_succ l.isLt) (Nat.le_of_lt_succ k.isLt) hrs

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourSpin
attribute [-simp] _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation Filter Topology

lemma orbitalPair_orthonormal_twice {Q r s : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hro : Odd r) (hso : Odd s)
    (l : Fin (2*Q-2*r+1)) (k : Fin (2*Q-2*s+1)) :
    (∑ a : PairLabel (Q+1), orbitalPairCoefficient Q r l.val a *
      orbitalPairCoefficient Q s k.val a) = if r=s ∧ l.val=k.val then 1 else 0 := by
  exact orbitalPair_orthonormal hr hs hro hso
    ⟨l.val, by omega⟩ ⟨k.val, by omega⟩

lemma pairFactorInclusion_isometry {Q n r : ℕ} (hr : r ≤ Q) (ho : Odd r)
    (x y : (Fin (n+1) × Fin (2*Q-2*r+1)) → ℝ) :
    dotProduct (pairFactorInclusion Q n r x) (pairFactorInclusion Q n r y) =
      dotProduct x y := by
  classical
  simp only [dotProduct, Fintype.sum_prod_type, pairFactorInclusion]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans _ (by simp : (∑ k : Fin (2*Q-2*r+1),
    ∑ l : Fin (2*Q-2*r+1), x (p,l) * y (p,k) * if k=l then (1:ℝ) else 0) = _)
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  have he := orbitalPair_orthonormal_twice hr hr ho ho k l
  simp only [true_and, Fin.val_inj] at he
  rw [← he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma pairFactorInclusion_orthogonal {Q n r s : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hro : Odd r) (hso : Odd s) (hrs : r ≠ s)
    (x : (Fin (n+1) × Fin (2*Q-2*r+1)) → ℝ)
    (y : (Fin (n+1) × Fin (2*Q-2*s+1)) → ℝ) :
    dotProduct (pairFactorInclusion Q n r x) (pairFactorInclusion Q n s y) = 0 := by
  simp only [dotProduct, Fintype.sum_prod_type, pairFactorInclusion,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l hl
  have he := orbitalPair_orthonormal_twice hr hs hro hso l k
  simp only [hrs, false_and, ite_false] at he
  calc
    _ = (x (p,l) * y (p,k)) * ∑ a : PairLabel (Q+1),
        orbitalPairCoefficient Q r l.val a * orbitalPairCoefficient Q s k.val a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = 0 := by rw [he, mul_zero]

theorem fourBodyCoupled_coefficient {Q D T r : ℕ} (hrD : r ≤ D)
    (hDT : D ≤ T) (hT : T ≤ Q) (p : Fin (2*Q-2+1)) (a : PairLabel (Q+1)) :
    fourBodyCoupled Q D T r (p,a) =
      fourBodyCoefficient Q D T r p.val a.val.1.val a.val.2.val := by
  classical
  unfold fourBodyCoupled pairFactorInclusion fourBodyCoefficient
  by_cases hw : r ≤ a.val.1.val+a.val.2.val ∧ p.val+a.val.1.val+a.val.2.val=T
  · rw [ite_eq_left hw]
    let l : Fin (2*Q-2*r+1) := ⟨a.val.1.val+a.val.2.val-r, by omega⟩
    rw [Finset.sum_eq_single l]
    · simp only [orbitalPairCoefficient, coupledTensor]
      rw [ite_eq_left (by dsimp [l]; omega), ite_eq_left (by dsimp [l]; omega)]
      dsimp [l]
      ring
    · intro k hk hkl
      have he : a.val.1.val+a.val.2.val ≠ r+k.val := by
        intro he
        apply hkl
        apply Fin.ext
        dsimp [l]
        omega
      simp only [orbitalPairCoefficient, coupledTensor, ite_eq_right he, mul_zero]
    · simp
  · rw [ite_eq_right hw]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [coupledTensor, orbitalPairCoefficient]
    split_ifs with h₁ h₂ h₂ <;> try simp
    exfalso
    exact hw ⟨by omega, by omega⟩

lemma fourBodyCoupled_norm_sq {Q D T r : ℕ} (hr : r ≤ Q) (hro : Odd r)
    (hz : D-r ≤ min (2*Q-2) (2*Q-2*r))
    (hl : T-D ≤ (2*Q-2)+(2*Q-2*r)-2*(D-r)) :
    dotProduct (fourBodyCoupled Q D T r) (fourBodyCoupled Q D T r) = 1 := by
  rw [fourBodyCoupled, pairFactorInclusion_isometry hr hro]
  exact coupledTensor_norm_sq hz hl

lemma fourBodyCoupled_orthogonal {Q D T r s : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hro : Odd r) (hso : Odd s) (h : r ≠ s) :
    dotProduct (fourBodyCoupled Q D T r) (fourBodyCoupled Q D T s) = 0 := by
  exact pairFactorInclusion_orthogonal hr hs hro hso h _ _

theorem fourBodyHighestFamily_orthonormal {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    Orthonormal ℝ (fourBodyHighestFamily Q D) := by
  rw [orthonormal_iff_ite]
  intro r s
  simp only [fourBodyHighestFamily, EuclideanSpace.inner_toLp_toLp]
  by_cases he : r=s
  · subst s
    rw [ite_eq_left rfl]
    apply fourBodyCoupled_norm_sq (by omega) r.property
    · have : 1 ≤ r.val.val := r.property.pos
      omega
    · omega
  · rw [ite_eq_right he]
    exact fourBodyCoupled_orthogonal (by omega) (by omega) s.property r.property
      (by intro h; apply he; exact Subtype.ext (Fin.ext h.symm))

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntertwinerAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intertwiner Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma LadderMap.matrix_lower {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : loweringMatrix T * A.matrix = A.matrix * loweringMatrix S := by
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, loweringMatrix, LadderMap.matrix, Matrix.toLin'_toMatrix']
  exact LinearMap.ext A.lower

lemma LadderMap.matrix_raise {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : (loweringMatrix T).transpose * A.matrix =
      A.matrix * (loweringMatrix S).transpose := by
  simp only [loweringMatrix_transpose]
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, LadderMap.matrix, Matrix.toLin'_toMatrix']
  exact LinearMap.ext A.raise

@[simp] lemma LadderMap.transpose_matrix {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : A.transpose.matrix = A.matrix.transpose := toMatrix_transposeMap _

lemma copyLift_commutator {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) (X : Matrix ι ι ℝ) :
    copyLift A B (commutator (loweringMatrix S) X) =
      commutator (loweringMatrix T) (copyLift A B X) := by
  have ht := B.transpose.matrix_lower
  rw [LadderMap.transpose_matrix] at ht
  simp only [copyLift, LinearMap.coe_mk, AddHom.coe_mk, Averaging.commutator,
    Matrix.mul_sub, Matrix.sub_mul]
  rw [← Matrix.mul_assoc A.matrix (loweringMatrix S), ← A.matrix_lower,
    Matrix.mul_assoc (loweringMatrix T), Matrix.mul_assoc (loweringMatrix T),
    Matrix.mul_assoc A.matrix X]
  simp only [Matrix.mul_assoc, ht]

lemma copyLift_commutator_transpose {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) (X : Matrix ι ι ℝ) :
    copyLift A B (commutator (loweringMatrix S).transpose X) =
      commutator (loweringMatrix T).transpose (copyLift A B X) := by
  have ht := B.transpose.matrix_raise
  rw [LadderMap.transpose_matrix] at ht
  simp only [copyLift, LinearMap.coe_mk, AddHom.coe_mk, Averaging.commutator,
    Matrix.mul_sub, Matrix.sub_mul]
  rw [← Matrix.mul_assoc A.matrix (loweringMatrix S).transpose, ← A.matrix_raise,
    Matrix.mul_assoc (loweringMatrix T).transpose, Matrix.mul_assoc (loweringMatrix T).transpose,
    Matrix.mul_assoc A.matrix X]
  simp only [Matrix.mul_assoc, ht]

theorem copyLift_average {n : ℕ} {T : LadderSystem κ}
    (A B : LadderMap (standardLadderSystem n) T) (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    average (rotationCommutant (loweringMatrix T)) (copyLift A B X) =
      (X.trace / (n+1 : ℕ)) • (A.matrix * B.matrix.transpose) := by
  rw [rotation_average_natural (copyLift A B) (copyLift_commutator A B)
    (copyLift_commutator_transpose A B), standardSpin_average]
  simp [copyLift]

omit [DecidableEq κ] in
lemma copyLift_rankOne {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) (x y : ι → ℝ) :
    copyLift A B (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (A.toLinearMap x) (B.toLinearMap y) := by
  simp only [copyLift, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, LadderMap.matrix_mulVec, Matrix.vecMul_transpose]

lemma trace_rankOne_mul {σ : Type*} [Fintype σ] (x y : σ → ℝ) (C : Matrix σ σ ℝ) :
    (Matrix.vecMulVec x y * C).trace = dotProduct y (C.mulVec x) := by
  rw [Matrix.trace_mul_comm, trace_mul_rankOne]

theorem distinct_copy_average {n m : ℕ} {T : LadderSystem κ} (hnm : n ≠ m)
    (A : LadderMap (standardLadderSystem n) T)
    (B : LadderMap (standardLadderSystem m) T)
    (x : Fin (n+1) → ℝ) (y : Fin (m+1) → ℝ) :
    average (rotationCommutant (loweringMatrix T))
      (Matrix.vecMulVec (A.toLinearMap x) (B.toLinearMap y)) = 0 := by
  apply average_unique _ _ _ (zero_mem _)
  intro C hC
  simp only [sub_zero, Matrix.transpose_vecMulVec, trace_rankOne_mul]
  let L := A.transpose.comp ((commutantLadderMap T hC).comp B)
  have he : L.toLinearMap = 0 := standardLadderMap_eq_zero hnm.symm L
  rw [transposeMap_adjoint]
  have hv := LinearMap.congr_fun he y
  change transposeMap A.toLinearMap (Matrix.toLin' C (B.toLinearMap y)) = 0 at hv
  rw [Matrix.toLin'_apply] at hv
  rw [hv, dotProduct_zero]

theorem equal_copy_average {n : ℕ} {T : LadderSystem κ}
    (A B : LadderMap (standardLadderSystem n) T) (i j : Fin (n+1)) :
    average (rotationCommutant (loweringMatrix T))
      (Matrix.vecMulVec (A.toLinearMap (Pi.single i 1))
        (B.toLinearMap (Pi.single j 1))) =
      (if i=j then (1 : ℝ)/(n+1 : ℕ) else 0) • (A.matrix * B.matrix.transpose) := by
  rw [← copyLift_rankOne, copyLift_average, Matrix.trace_vecMulVec]
  by_cases h : i=j
  · subst j; simp
  · simp [h, eq_comm]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NestedSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct

lemma nestedEmbedding_apply {n m k r z : ℕ} (hr : r ≤ min m k)
    (hz : z ≤ min n (m+k-2*r)) (x : Fin (n+(m+k-2*r)-2*z+1) → ℝ) :
    (nestedEmbedding hr hz).toLinearMap x =
      ∑ l : Fin (n+(m+k-2*r)-2*z+1), x l • nestedTensor n m k r z l.val := by
  funext ⟨a,b⟩
  simp only [nestedEmbedding, LadderMap.comp, LinearMap.coe_comp, Function.comp_apply,
    LadderMap.tensorLeft, onSecondMap_apply, coupledEmbedding_apply, nestedTensor,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

lemma nestedTensor_expansion (n m k : ℕ)
    (x : (Fin (n+1) × (Fin (m+1) × Fin (k+1))) → ℝ) :
    ∑ a : NestedIndex n m k,
      dotProduct (nestedTensor n m k a.1.val a.2.1.val a.2.2.val) x •
        nestedTensor n m k a.1.val a.2.1.val a.2.2.val = x := by
  funext p
  have h := congrArg (fun y : EuclideanSpace ℝ (Fin (n+1) × (Fin (m+1) × Fin (k+1))) => y p)
    ((nestedBasis n m k).sum_repr (WithLp.toLp 2 x))
  simpa only [OrthonormalBasis.repr_apply_apply, nestedBasis_apply, nestedFamily,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.smul_apply, WithLp.toLp_ofLp, Pi.smul_apply,
    smul_eq_mul, dotProduct, mul_comm] using h

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NestedAveraging
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma LadderMap.changeSource_single {n d : ℕ} {S : LadderSystem ι} (h : n=d)
    (A : LadderMap (standardLadderSystem n) S) (i : Fin (d+1)) :
    (A.changeSource h).toLinearMap (Pi.single i 1) =
      A.toLinearMap (Pi.single (⟨i.val,by omega⟩ : Fin (n+1)) 1) := by
  subst d
  rfl

lemma nestedTensor_weight_support (n m k r z l : ℕ)
    (a : Fin (n+1) × (Fin (m+1) × Fin (k+1)))
    (ha : a.1.val+a.2.1.val+a.2.2.val ≠ r+z+l) : nestedTensor n m k r z l a = 0 := by
  unfold nestedTensor
  apply Finset.sum_eq_zero
  intro q hq
  simp only [coupledTensor]
  split_ifs with h₁ h₂ h₂ <;> try simp
  exfalso
  apply ha
  omega

lemma nestedTensor_flip (n Q r z l : ℕ) (hr : r ≤ Q) (_hl : l ≤ n+(2*Q-2*r)-2*z)
    (a : Fin (n+1)) (j k : Fin (Q+1)) :
    nestedTensor n Q Q r z l (a,(k,j)) = (-1:ℝ)^r * nestedTensor n Q Q r z l (a,(j,k)) := by
  unfold nestedTensor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [coupledTensor_swap hr (Nat.le_of_lt_succ q.isLt)]
  ring

lemma nestedAtDeficit_single {n m k D r : ℕ} (hr : r ≤ min m k) (hrD : r ≤ D)
    (hz : D-r ≤ min n (m+k-2*r)) (l : Fin (n+m+k-2*D+1)) :
    (nestedAtDeficit hr hrD hz).toLinearMap (Pi.single l 1) =
      nestedTensor n m k r (D-r) l.val := by
  rw [nestedAtDeficit, LadderMap.changeSource_single, nestedEmbedding_apply]
  simp [Pi.single_apply, ite_smul]

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma Covariant.equal_descendant_average {L : Matrix κ κ ℝ} {S : LadderSystem ι}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L (loweringMatrix S) B) {n : ℕ}
    (A C : LadderMap (standardLadderSystem n) S) (i j : Fin (n+1)) :
    average (rotationCommutant L)
      ((combination B (A.toLinearMap (Pi.single i 1))).transpose *
        combination B (C.toLinearMap (Pi.single j 1))) =
      if i=j then average (rotationCommutant L)
        ((combination B (A.toLinearMap (Pi.single (0 : Fin (n+1)) 1))).transpose *
          combination B (C.toLinearMap (Pi.single (0 : Fin (n+1)) 1))) else 0 := by
  simp only [← lift_rankOne, h.average_lift, equal_copy_average, map_smul]
  split_ifs <;> simp

lemma Covariant.distinct_descendant_average {L : Matrix κ κ ℝ} {S : LadderSystem ι}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L (loweringMatrix S) B) {n m : ℕ}
    (hnm : n ≠ m) (A : LadderMap (standardLadderSystem n) S)
    (C : LadderMap (standardLadderSystem m) S) (x : Fin (n+1) → ℝ) (y : Fin (m+1) → ℝ) :
    average (rotationCommutant L)
      ((combination B (A.toLinearMap x)).transpose * combination B (C.toLinearMap y)) = 0 := by
  rw [← lift_rankOne, h.average_lift, distinct_copy_average hnm, map_zero]

lemma physicalFour_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (nestedSpin (2*Q-2) Q Q)) (physicalFour Q) :=
  ((physicalPair_covariant hQ).product ((annihilation_covariant _).product
    (annihilation_covariant _))).smul (1/Real.sqrt 2)

lemma annihilation_anticommute' {n : ℕ} (j k : Fin n) :
    annihilation k * annihilation j = -(annihilation j * annihilation k) := by
  apply complexify_injective
  simpa only [map_mul, map_neg, complexify_annihilation] using
    Occupation.annihilation_anticommute k j

lemma physicalFour_flip (Q : ℕ) (a : Fin (2*Q-2+1)) (j k : Fin (Q+1)) :
    physicalFour Q (a,(k,j)) = -physicalFour Q (a,(j,k)) := by
  simp only [physicalFour, productFamily]
  rw [annihilation_anticommute' k j, neg_mul, smul_neg]

lemma four_combination_flip (Q : ℕ)
    (x : (Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1))) → ℝ) :
    combination (physicalFour Q) (fun a => x (a.1,(a.2.2,a.2.1))) =
      -combination (physicalFour Q) x := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [physicalFour_flip, smul_neg]

lemma physicalFour_even_null {Q r z l : ℕ} (hr : r ≤ Q) (he : Even r)
    (hl : l ≤ (2*Q-2)+(2*Q-2*r)-2*z) :
    combination (physicalFour Q) (nestedTensor (2*Q-2) Q Q r z l) = 0 := by
  have hf : (fun a : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)) =>
      nestedTensor (2*Q-2) Q Q r z l (a.1,(a.2.2,a.2.1))) =
      nestedTensor (2*Q-2) Q Q r z l := by
    funext a
    rw [nestedTensor_flip _ _ _ _ _ hr hl, he.neg_one_pow, one_mul]
  have hh := four_combination_flip Q (nestedTensor (2*Q-2) Q Q r z l)
  rw [hf] at hh
  have h2 : (2:ℝ) • combination (physicalFour Q) (nestedTensor (2*Q-2) Q Q r z l) = 0 := by
    rw [two_smul ℝ]
    exact eq_neg_iff_add_eq_zero.mp hh
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_LowNested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low Nested. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma lowNestedInclusion_injective {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q) :
    Function.Injective (lowNestedInclusion hQ hT) := by
  intro a b h
  have hr := congrArg (fun x : NestedIndex (2*Q-2) Q Q => x.1.val) h
  have hz := congrArg (fun x : NestedIndex (2*Q-2) Q Q => x.2.1.val) h
  dsimp [lowNestedInclusion] at hr hz
  have hD : a.1=b.1 := Fin.ext (by have := a.2.isLt; have := b.2.isLt; omega)
  rcases a with ⟨D,r⟩
  rcases b with ⟨D',r'⟩
  dsimp at hD
  subst D'
  have : r=r' := Fin.ext hr
  subst r'
  rfl

lemma lowNested_coefficient {Q D T r : ℕ} (hrD : r ≤ D)
    (hDT : D ≤ T) (hT : T ≤ Q)
    (a : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1))) :
    Real.sqrt 2 * nestedTensor (2*Q-2) Q Q r (D-r) (T-D) a =
      fourBodyCoefficient Q D T r a.1.val a.2.1.val a.2.2.val := by
  classical
  unfold nestedTensor fourBodyCoefficient
  by_cases hw : r ≤ a.2.1.val+a.2.2.val ∧ a.1.val+a.2.1.val+a.2.2.val=T
  · rw [ite_eq_left hw]
    let l : Fin (Q+Q-2*r+1) := ⟨a.2.1.val+a.2.2.val-r, by omega⟩
    rw [Finset.sum_eq_single l]
    · simp only [coupledTensor]
      rw [ite_eq_left (by dsimp [l]; omega), ite_eq_left (by dsimp [l]; omega)]
      dsimp [l]
      rw [show Q+Q=2*Q by omega]
      ring
    · intro k hk hkl
      have he : a.2.1.val+a.2.2.val ≠ r+k.val := by
        intro he
        apply hkl
        apply Fin.ext
        dsimp [l]
        omega
      simp only [coupledTensor, ite_eq_right he, mul_zero]
    · simp
  · rw [ite_eq_right hw]
    have he : (∑ k : Fin (Q+Q-2*r+1),
        coupledTensor (2*Q-2) (Q+Q-2*r) (D-r) (T-D) (a.1,k) *
          coupledTensor Q Q r k.val a.2) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [coupledTensor]
      split_ifs with h₁ h₂ h₂ <;> try simp
      exfalso
      exact hw ⟨by omega, by omega⟩
    rw [he, mul_zero]

lemma nestedTensor_low_expansion {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (a : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)))
    (ha : a.1.val+a.2.1.val+a.2.2.val=T) :
    ∑ b : LowNestedIndex T,
      nestedTensor (2*Q-2) Q Q b.2.val (b.1.val-b.2.val) (T-b.1.val) a •
        nestedTensor (2*Q-2) Q Q b.2.val (b.1.val-b.2.val) (T-b.1.val) =
      Pi.single a 1 := by
  classical
  have hex := nestedTensor_expansion (2*Q-2) Q Q (Pi.single a 1)
  simp only [dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hex
  rw [← hex]
  apply Finset.sum_bij_ne_zero (fun b _ _ => lowNestedInclusion hQ hT b)
  · simp
  · intro b hb hb0 c hc hc0 he
    exact lowNestedInclusion_injective hQ hT he
  · intro b hb hb0
    have hw : b.1.val+b.2.1.val+b.2.2.val=T := by
      by_contra he
      have hz := nestedTensor_weight_support (2*Q-2) Q Q b.1.val b.2.1.val b.2.2.val a
        (by omega)
      exact hb0 (by rw [hz, zero_smul])
    let c : LowNestedIndex T := ⟨⟨b.1.val+b.2.1.val, by omega⟩,⟨b.1.val, by dsimp; omega⟩⟩
    have hc : lowNestedInclusion hQ hT c=b := by
      rcases b with ⟨r,⟨z,l⟩⟩
      dsimp at hw
      have hr : (lowNestedInclusion hQ hT c).1=r := Fin.ext rfl
      apply Sigma.ext hr
      apply heq_of_eq
      apply Sigma.ext (Fin.ext (by dsimp [lowNestedInclusion,c]; omega))
      apply (Fin.heq_ext_iff (by dsimp [lowNestedInclusion,c]; omega)).mpr
      dsimp [lowNestedInclusion,c]
      omega
    refine ⟨c, Finset.mem_univ _, ?_, hc⟩
    have hc0 : nestedTensor (2*Q-2) Q Q c.2.val (c.1.val-c.2.val) (T-c.1.val) a •
      nestedTensor (2*Q-2) Q Q c.2.val (c.1.val-c.2.val) (T-c.1.val) ≠ 0 := by
      change nestedTensor (2*Q-2) Q Q (lowNestedInclusion hQ hT c).1.val
        (lowNestedInclusion hQ hT c).2.1.val (lowNestedInclusion hQ hT c).2.2.val a •
        nestedTensor (2*Q-2) Q Q (lowNestedInclusion hQ hT c).1.val
        (lowNestedInclusion hQ hT c).2.1.val (lowNestedInclusion hQ hT c).2.2.val ≠ 0
      rw [hc]
      exact hb0
    exact hc0
  · intros
    rfl

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourAveraging
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Averaging. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma fourAnnihilator_even {Q D T r : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (hD : D ≤ T) (hr : r ≤ D) (he : Even r) : fourAnnihilator Q D T r = 0 := by
  exact physicalFour_even_null (by omega) he (by omega)

lemma fourAnnihilator_eq_embedding {Q D T r : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (hD : D ≤ T) (hr : r ≤ D) :
    fourAnnihilator Q D T r = combination (physicalFour Q)
      ((nestedAtDeficit (show r ≤ min Q Q by omega) hr
        (show D-r ≤ min (2*Q-2) (Q+Q-2*r) by omega)).toLinearMap
          (Pi.single (⟨T-D, by omega⟩ : Fin ((2*Q-2)+Q+Q-2*D+1)) 1)) := by
  rw [nestedAtDeficit_single]
  rfl

lemma fourAnnihilator_average {Q T U D E r s : ℕ} (hQ : 2 ≤ Q)
    (hT : T ≤ Q) (hU : U ≤ Q) (hD : D ≤ T) (hE : E ≤ U)
    (hr : r ≤ D) (hs : s ≤ E) :
    average (rotationCommutant (fockLowering Q))
      ((fourAnnihilator Q D T r).transpose * fourAnnihilator Q E U s) =
      if D=E ∧ T=U then average (rotationCommutant (fockLowering Q))
        ((fourAnnihilator Q D D r).transpose * fourAnnihilator Q E E s) else 0 := by
  classical
  by_cases hDE : D=E
  · subst E
    rw [fourAnnihilator_eq_embedding hQ hT hD hr,
      fourAnnihilator_eq_embedding hQ hU hE hs,
      (physicalFour_covariant hQ).equal_descendant_average,
      fourAnnihilator_eq_embedding hQ (by omega : D ≤ Q) le_rfl hr,
      fourAnnihilator_eq_embedding hQ (by omega : D ≤ Q) le_rfl hs]
    simp only [true_and, Nat.sub_self]
    congr 1
    apply propext
    simp only [Fin.mk.injEq]
    omega
  · rw [ite_eq_right (by tauto), fourAnnihilator_eq_embedding hQ hT hD hr,
      fourAnnihilator_eq_embedding hQ hU hE hs]
    exact (physicalFour_covariant hQ).distinct_descendant_average (by omega) _ _ _ _

lemma rawFour_expansion {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (a : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)))
    (ha : a.1.val+a.2.1.val+a.2.2.val=T) :
    annihilation a.2.2 * annihilation a.2.1 * physicalPair Q a.1.val =
      ∑ D : Fin (T+1), ∑ r : FourCopy D.val,
        fourBodyCoefficient Q D.val T r.val.val a.1.val a.2.1.val a.2.2.val •
          fourAnnihilator Q D.val T r.val.val := by
  classical
  have h := congrArg (combination (physicalFour Q)) (nestedTensor_low_expansion hQ hT a ha)
  simp only [map_sum, map_smul, combination_single] at h
  have h' := congrArg (fun M => Real.sqrt 2 • M) h
  have hn : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hc (D : Fin (T+1)) (r : Fin (D.val+1)) := lowNested_coefficient
    (Nat.le_of_lt_succ r.isLt) (Nat.le_of_lt_succ D.isLt) hT a
  simp only [Fintype.sum_sigma, Finset.smul_sum, smul_smul, hc,
    physicalFour, productFamily] at h'
  rw [mul_one_div_cancel hn, one_smul] at h'
  change (∑ D : Fin (T+1), ∑ r : Fin (D.val+1),
    fourBodyCoefficient Q D.val T r.val a.1.val a.2.1.val a.2.2.val •
      fourAnnihilator Q D.val T r.val) = _ at h'
  rw [← h']
  apply Finset.sum_congr rfl
  intro D hD
  rw [← Finset.sum_subtype (Finset.univ.filter (fun r : Fin (D.val+1) => Odd r.val))
    (by simp) (fun r => fourBodyCoefficient Q D.val T r.val a.1.val a.2.1.val a.2.2.val •
      fourAnnihilator Q D.val T r.val)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases ho : Odd r.val
  · simp [ho]
  · have he : Even r.val := Nat.not_odd_iff_even.mp ho
    rw [ite_eq_right ho, fourAnnihilator_even hQ hT (Nat.le_of_lt_succ D.isLt)
      (Nat.le_of_lt_succ r.isLt) he, smul_zero]

lemma rawFour_cross_average {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (a b : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)))
    (ha : a.1.val+a.2.1.val+a.2.2.val=T)
    (hb : b.1.val+b.2.1.val+b.2.2.val=T) :
    average (rotationCommutant (fockLowering Q))
      ((annihilation a.2.2 * annihilation a.2.1 * physicalPair Q a.1.val).transpose *
        (annihilation b.2.2 * annihilation b.2.1 * physicalPair Q b.1.val)) =
      ∑ D : Fin (T+1), ∑ r : FourCopy D.val, ∑ s : FourCopy D.val,
        (fourBodyCoefficient Q D.val T r.val.val a.1.val a.2.1.val a.2.2.val *
         fourBodyCoefficient Q D.val T s.val.val b.1.val b.2.1.val b.2.2.val) •
        average (rotationCommutant (fockLowering Q))
          ((fourAnnihilator Q D.val D.val r.val.val).transpose *
            fourAnnihilator Q D.val D.val s.val.val) := by
  classical
  rw [rawFour_expansion hQ hT a ha, rawFour_expansion hQ hT b hb]
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_sum, map_smul]
  conv_lhs =>
    arg 2; ext E
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext D
    arg 2; ext E
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext D
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro r hr
  have hblock (E : Fin (T+1)) (s : FourCopy E.val) :=
    fourAnnihilator_average hQ hT hT (Nat.le_of_lt_succ D.isLt)
      (Nat.le_of_lt_succ E.isLt) (Nat.le_of_lt_succ r.val.isLt) (Nat.le_of_lt_succ s.val.isLt)
  simp only [hblock, and_true, Fin.val_inj]
  rw [Finset.sum_eq_single D]
  · simp only [ite_true, mul_comm]
  · intro E hE hED
    apply Finset.sum_eq_zero
    intro s hs
    rw [ite_eq_right (Ne.symm hED), smul_zero]
  · simp

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealPositivity
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Positivity. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma complexify_isPositive_iff (A : Matrix ι ι ℝ) :
    (complexify A).IsPositive ↔ A.PosSemidef := by
  refine ⟨fun h => ?_, complexify_positive⟩
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · have ha : (complexify A).adjoint = complexify A := h.isSymmetric.adjoint_eq
    rw [← complexify_transpose] at ha
    exact (Matrix.isHermitian_iff_isSymm).mpr (complexify_injective ha)
  · have hx := h.re_inner_nonneg_right (WithLp.toLp 2 (fun i => (x i : ℂ)))
    simpa [complexify, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      Matrix.mulVec, dotProduct, Complex.mul_re, Complex.add_re, mul_comm] using hx

omit [DecidableEq ι] in
lemma transpose_square_positive [DecidableEq ι] (B : Matrix ι ι ℝ) :
    (B.transpose * B).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self B

lemma square_diff_positive {A B : Matrix ι ι ℝ}
    (h : ∀ x, ‖complexify B x‖ ≤ ‖complexify A x‖) :
    (A.transpose * A - B.transpose * B).PosSemidef := by
  rw [← complexify_isPositive_iff, map_sub, map_mul, map_mul,
    complexify_transpose, complexify_transpose]
  apply (LinearMap.isPositive_iff_complex _).mpr
  intro x
  rw [LinearMap.sub_apply]
  simp only [Module.End.mul_apply, inner_sub_left, LinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K]
  change (Complex.ofReal ((Complex.ofReal ‖complexify A x‖ ^ 2 -
      Complex.ofReal ‖complexify B x‖ ^ 2).re) =
      Complex.ofReal ‖complexify A x‖ ^ 2 - Complex.ofReal ‖complexify B x‖ ^ 2 ∧
      (0 : ℝ) ≤ (Complex.ofReal ‖complexify A x‖ ^ 2 - Complex.ofReal ‖complexify B x‖ ^ 2).re)
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.ofReal_re]
  exact ⟨trivial, sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h x))⟩

lemma double_annihilation_square_le {n : ℕ} (j k : Fin n) (B : FockMatrix n) :
    (B.transpose * B - (annihilation k * (annihilation j * B)).transpose *
      (annihilation k * (annihilation j * B))).PosSemidef := by
  apply square_diff_positive
  intro x
  simpa only [map_mul, complexify_annihilation, Module.End.mul_apply] using
    Occupation.double_annihilation_norm_le j k (complexify B x)

lemma combination_bessel {σ : Type*} [Fintype σ] [DecidableEq σ]
    (S : Matrix σ ι ℝ) (hS : S * S.transpose = 1) (B : ι → Matrix κ κ ℝ) :
    ((∑ i, (B i).transpose * B i) -
      ∑ r, (combination B (S r)).transpose * combination B (S r)).PosSemidef := by
  have h : (1 - S.transpose * S).PosSemidef := by
    have he : 1 - S.transpose * S =
        (1 - S.transpose * S).transpose * (1 - S.transpose * S) := by
      simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_transpose, sub_mul, mul_sub, one_mul, mul_one]
      rw [Matrix.mul_assoc S.transpose S (S.transpose*S), ← Matrix.mul_assoc S S.transpose S, hS, Matrix.one_mul]
      abel
    rw [he]
    exact transpose_square_positive _
  have he : S.transpose * S = ∑ r, Matrix.vecMulVec (S r) (S r) := by
    ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.sum_apply]
  have hh := lift_positive B h
  rw [map_sub, lift_identity, he, map_sum] at hh
  simpa only [lift_rankOne] using hh

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Bounds. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma average_mono (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A B : Matrix ι ι ℝ} (h : A ≤ B) : average S A ≤ average S B := by
  have hh := average_positive S (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))
  rw [map_sub] at hh
  exact sub_nonneg.mp hh.nonneg

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_AuxiliaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Auxiliary Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma RowEntry.balance {t : Fin 8} (a : RowEntry t) :
    t.val+a.output.val = a.val.1.val+a.val.2.val := by
  dsimp [RowEntry.output]; have := a.property; omega

lemma sum_fin_extend {M : Type*} [AddCommMonoid M] {T K : ℕ} (h : T ≤ K) (f : ℕ → M) :
    (∑ z : Fin (T+1), f z.val) = ∑ z : Fin (K+1), if z.val ≤ T then f z.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range f,
    Fin.sum_univ_eq_sum_range (fun z => if z ≤ T then f z else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext z
  simp only [Finset.mem_range,Finset.mem_filter]
  omega

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Four
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma tensorProjection_positive {n m z : ℕ} (hz : z ≤ min n m) :
    (tensorProjection hz).PosSemidef := by
  rw [tensorProjection_eq]
  apply Matrix.posSemidef_sum
  intro l hl
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    (coupledTensor n m z l.val)

lemma sum_tensorProjection (n m : ℕ) :
    (∑ z : Fin (min n m+1), tensorProjection (Nat.le_of_lt_succ z.isLt)) = 1 := by
  classical
  ext a b
  have h := congrFun (coupledTensor_expansion n m (Pi.single b 1)) a
  simpa only [tensorProjection_eq, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Fintype.sum_sigma, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct_single_one, Pi.single_apply, Matrix.one_apply, eq_comm, mul_comm] using h.symm

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma Covariant.average_highest {n m z : ℕ} (hz : z ≤ min n m)
    {L : Matrix ι ι ℝ} {B : (Fin (n+1) × Fin (m+1)) → Matrix ι ι ℝ}
    (h : Covariant L (loweringMatrix (tensorSpin n m)) B) :
    average (rotationCommutant L)
      ((combination B (highestTensor n m z)).transpose * combination B (highestTensor n m z)) =
    (1/(n+m-2*z+1 : ℕ) : ℝ) • lift B (tensorProjection hz) := by
  have he : (coupledEmbedding hz).toLinearMap (Pi.single (0 : Fin (n+m-2*z+1)) 1) =
      highestTensor n m z := by
    rw [coupledEmbedding_apply]
    simp [Pi.single_apply, ite_smul]
  rw [← lift_rankOne, h.average_lift, ← he, equal_copy_average]
  simp only [ite_true, map_smul]
  simp only [tensorProjection, LadderMap.comp, LadderMap.transpose,
    LinearMap.toMatrix'_comp, toMatrix_transposeMap, LadderMap.matrix]

lemma physicalPairPair_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (tensorSpin (2*Q-2) (2*Q-2)))
      (physicalPairPair Q) := (physicalPair_covariant hQ).product (physicalPair_covariant hQ)

lemma fourAnnihilator_first {Q D T : ℕ} (hQ : 2 ≤ Q) :
    fourAnnihilator Q D T 1 =
      combination (physicalPairPair Q) (coupledTensor (2*Q-2) (2*Q-2) (D-1) (T-D)) := by
  classical
  unfold fourAnnihilator
  unfold nestedTensor
  rw [show Q+Q-2*1=2*Q-2 by omega]
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type,
    physicalFour, productFamily, smul_smul, Finset.sum_mul, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← physicalPairTensor_eq_coupled hQ (Nat.le_of_lt_succ r.isLt)]
  simp only [physicalPairPair, productFamily, physicalPair, combination,
    LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type, Matrix.smul_mul,
    Finset.sum_mul, Finset.smul_sum, smul_smul, Matrix.mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ring

lemma lift_physicalPairPair_one {Q : ℕ} (hQ : 2 ≤ Q) :
    lift (physicalPairPair Q) 1 = fourTarget Q := by
  rw [lift_identity]
  simp only [physicalPairPair, productFamily, Fintype.sum_prod_type, fourTarget]
  let e : Fin (2*Q-2+1) ≃ Fin (2*Q-1) := finCongr (by omega)
  have he := e.sum_comp (fun p : Fin (2*Q-1) => ∑ q : Fin (2*Q-1),
    (physicalPair Q q.val * physicalPair Q p.val).transpose *
      (physicalPair Q q.val * physicalPair Q p.val))
  rw [← he]
  apply Finset.sum_congr rfl
  intro p hp
  exact e.sum_comp (fun q : Fin (2*Q-1) =>
    (physicalPair Q q.val * physicalPair Q p.val).transpose *
      (physicalPair Q q.val * physicalPair Q p.val))

theorem fourTarget_retained {Q K : ℕ} (hQ : 2 ≤ Q) (hK : K ≤ Q) :
    (∑ d : Fin K, ((4*Q-1-2*(d.val+1) : ℕ) : ℝ) •
      average (rotationCommutant (fockLowering Q))
        ((fourAnnihilator Q (d.val+1) (d.val+1) 1).transpose *
          fourAnnihilator Q (d.val+1) (d.val+1) 1)) ≤ fourTarget Q := by
  classical
  have hz (d : Fin K) : d.val ≤ min (2*Q-2) (2*Q-2) := by omega
  have he (d : Fin K) :
    ((4*Q-1-2*(d.val+1) : ℕ) : ℝ) • average (rotationCommutant (fockLowering Q))
      ((fourAnnihilator Q (d.val+1) (d.val+1) 1).transpose *
        fourAnnihilator Q (d.val+1) (d.val+1) 1) =
      lift (physicalPairPair Q) (tensorProjection (hz d)) := by
    rw [fourAnnihilator_first hQ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, coupledTensor_zero]
    rw [(physicalPairPair_covariant hQ).average_highest (hz d), smul_smul]
    have hn : 4*Q-1-2*(d.val+1) = (2*Q-2)+(2*Q-2)-2*d.val+1 := by omega
    rw [hn, mul_one_div_cancel (by positivity), one_smul]
  simp only [he]
  rw [← lift_physicalPairPair_one hQ, ← sum_tensorProjection (2*Q-2) (2*Q-2), map_sum]
  let e : Fin K ↪ Fin (min (2*Q-2) (2*Q-2)+1) :=
    ⟨fun d => ⟨d.val,Nat.lt_succ_of_le (hz d)⟩,
      fun a b he => Fin.ext (congrArg (fun z : Fin (min (2*Q-2) (2*Q-2)+1) => z.val) he)⟩
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (s := Finset.univ.map e) (t := Finset.univ)
    (f := fun z : Fin (min (2*Q-2) (2*Q-2)+1) =>
      lift (physicalPairPair Q) (tensorProjection (Nat.le_of_lt_succ z.isLt)))
    (Finset.subset_univ _) (fun z _ _ => (lift_positive _ (tensorProjection_positive _)).nonneg)
  simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk] using hh

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourHighest
attribute [-simp] _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Highest. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma sum_increasing_matrices {n : ℕ} {κ : Type*} (f : Fin n → Fin n → Matrix κ κ ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (2:ℝ) • (∑ a : Occupation.PairLabel n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, f i j := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Occupation.sum_increasing_pairs (fun i j => f i j x y)
    (fun i j => congrFun (congrFun (hs i j) x) y)
    (fun i => congrFun (congrFun (hd i) x) y)

lemma annihilation_square_zero {n : ℕ} (i : Fin n) : annihilation i * annihilation i = 0 := by
  apply complexify_injective
  rw [map_mul, map_zero, complexify_annihilation]
  exact Occupation.transition_square i false

lemma fourAnnihilator_exterior {Q D T r : ℕ} (hQ : 2 ≤ Q)
    (hT : T ≤ Q) (hD : D ≤ T) (hr : r ≤ D) (ho : Odd r) :
    fourAnnihilator Q D T r =
      ∑ p : Fin (2*Q-2+1), ∑ a : Occupation.PairLabel (Q+1),
        fourBodyCoefficient Q D T r p.val a.val.1.val a.val.2.val •
          (annihilation a.val.2 * annihilation a.val.1 * physicalPair Q p.val) := by
  classical
  simp only [fourAnnihilator, combination, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p hp
  have hf (j k : Fin (Q+1)) :
      nestedTensor (2*Q-2) Q Q r (D-r) (T-D) (p,(k,j)) =
        -nestedTensor (2*Q-2) Q Q r (D-r) (T-D) (p,(j,k)) := by
    rw [nestedTensor_flip _ _ _ _ _ (by omega) (by omega), ho.neg_one_pow, neg_one_mul]
  let f := fun j k : Fin (Q+1) =>
    nestedTensor (2*Q-2) Q Q r (D-r) (T-D) (p,(j,k)) • physicalFour Q (p,(j,k))
  have hs (j k : Fin (Q+1)) : f j k = f k j := by
    dsimp [f]
    rw [hf, physicalFour_flip, neg_smul, smul_neg, neg_neg]
  have hd (j : Fin (Q+1)) : f j j = 0 := by
    simp [f, physicalFour, productFamily, annihilation_square_zero]
  rw [← sum_increasing_matrices f hs hd, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp [f]
  rw [physicalFour, productFamily, productFamily, smul_smul, smul_smul,
    ← lowNested_coefficient hr hD hT (p,(a.val.1,a.val.2))]
  congr 1
  have hn := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  field_simp
  rw [hn]
  ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourAllowance
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Allowance. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct

lemma orbitalTripleFinite_injective {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    Function.Injective (orbitalTripleFinite hQ hD) := by
  intro a b he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun x : FourCoordinates Q => x.1.val) he
  · apply Prod.ext
    · exact congrArg (fun x : FourCoordinates Q => x.2.val.1.val) he
    · exact congrArg (fun x : FourCoordinates Q => x.2.val.2.val) he

lemma sum_orbitalTriple {Q D : ℕ} {M : Type*} [AddCommMonoid M]
    (hQ : 2 ≤ Q) (hD : D ≤ Q) (f : FourCoordinates Q → M)
    (hf : ∀ a, a.1.val+a.2.val.1.val+a.2.val.2.val ≠ D → f a = 0) :
    ∑ b : OrbitalTriple D, f (orbitalTripleFinite hQ hD b) = ∑ a, f a := by
  classical
  apply Finset.sum_bij_ne_zero (fun b _ _ => orbitalTripleFinite hQ hD b)
  · simp
  · intros a _ _ b _ _ he
    exact orbitalTripleFinite_injective hQ hD he
  · intro a ha hfa
    have hw : a.1.val+a.2.val.1.val+a.2.val.2.val=D := by
      by_contra hn; exact hfa (hf a hn)
    let b : OrbitalTriple D := ⟨(a.1.val,a.2.val.1.val,a.2.val.2.val), hw,a.2.property⟩
    have hb : orbitalTripleFinite hQ hD b = a := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext; rfl
    exact ⟨b,Finset.mem_univ _,by rwa [hb],hb⟩
  · simp

lemma fourHighestRows_orthonormal {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    fourHighestRows Q D * (fourHighestRows Q D).transpose = 1 := by
  classical
  ext r s
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  let f := fun a : FourCoordinates Q => fourBodyCoupled Q D D r.val.val a *
    fourBodyCoupled Q D D s.val.val a
  have he (b : OrbitalTriple D) : f (orbitalTripleFinite hQ hD b) =
      fourHighestRows Q D r b * fourHighestRows Q D s b := by
    simp only [f, fourBodyCoupled_coefficient (Nat.le_of_lt_succ r.val.isLt) le_rfl hD,
      fourBodyCoupled_coefficient (Nat.le_of_lt_succ s.val.isLt) le_rfl hD]
    rfl
  rw [← show (∑ b, f (orbitalTripleFinite hQ hD b)) =
    ∑ b, fourHighestRows Q D r b * fourHighestRows Q D s b by simp only [he],
    sum_orbitalTriple hQ hD f]
  · have ho := (orthonormal_iff_ite.mp (fourBodyHighestFamily_orthonormal hQ hD)) s r
    simpa only [fourBodyHighestFamily, EuclideanSpace.inner_toLp_toLp, star_trivial,
      dotProduct, eq_comm] using ho
  · intro a ha
    dsimp [f]
    rw [fourBodyCoupled_coefficient (Nat.le_of_lt_succ r.val.isLt) le_rfl hD]
    simp [fourBodyCoefficient,ha]

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma fourAnnihilator_high_local {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) (r : FourCopy D) :
    fourAnnihilator Q D D r.val.val =
      combination (localFourCoordinates hQ hD) (fourHighestRows Q D r) := by
  classical
  rw [fourAnnihilator_exterior hQ hD le_rfl (Nat.le_of_lt_succ r.val.isLt) r.property]
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk]
  let f := fun a : FourCoordinates Q =>
    fourBodyCoefficient Q D D r.val.val a.1.val a.2.val.1.val a.2.val.2.val •
      (annihilation a.2.val.2 * annihilation a.2.val.1 * physicalPair Q a.1.val)
  change _ = ∑ b, f (orbitalTripleFinite hQ hD b)
  rw [sum_orbitalTriple hQ hD f]
  · exact (Fintype.sum_prod_type f).symm
  · intro a ha
    simp [f, fourBodyCoefficient, ha]

lemma fourHighest_bessel {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    (∑ r : FourCopy D, (fourAnnihilator Q D D r.val.val).transpose *
      fourAnnihilator Q D D r.val.val) ≤
        ∑ b : OrbitalTriple D, (physicalPair Q b.val.1).transpose * physicalPair Q b.val.1 := by
  simp only [fourAnnihilator_high_local hQ hD]
  apply (sub_nonneg.mp (combination_bessel (fourHighestRows Q D)
    (fourHighestRows_orthonormal hQ hD) (localFourCoordinates hQ hD)).nonneg).trans
  apply Finset.sum_le_sum
  intro b hb
  simpa only [localFourCoordinates, orbitalTripleFinite, Matrix.mul_assoc] using
    sub_nonneg.mp (double_annihilation_square_le
      (orbitalTripleFinite hQ hD b).2.val.1 (orbitalTripleFinite hQ hD b).2.val.2
        (physicalPair Q b.val.1)).nonneg

theorem fourHighest_average_bessel {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    ((2*Q-1 : ℕ):ℝ) •
      (∑ r : FourCopy D, average (rotationCommutant (fockLowering Q))
        ((fourAnnihilator Q D D r.val.val).transpose * fourAnnihilator Q D D r.val.val)) ≤
    (Fintype.card (OrbitalTriple D):ℝ) • physicalHamiltonian Q := by
  have h := average_mono (rotationCommutant (fockLowering Q)) (fourHighest_bessel hQ hD)
  simp only [map_sum] at h
  have he (b : OrbitalTriple D) := physicalPair_single_val hQ
    (show b.val.1 < 2*Q-1 by have := b.property; omega)
  simp only [he, ← Finset.sum_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have h' := smul_le_smul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) (2*Q-1))
  have hn : ((2*Q-1 : ℕ):ℝ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  rw [smul_smul]
  congr 1
  field_simp

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourComparison
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

lemma rowFour_cross_average {Q : ℕ} (hQ : 23 ≤ Q) (r : RowData) (a b : RowEntry r.t) :
    average (rotationCommutant (fockLowering Q))
      ((annihilation ⟨b.output.val,by have := b.output.isLt; omega⟩ * rowTriple (by omega) a.val).transpose *
        (annihilation ⟨a.output.val,by have := a.output.isLt; omega⟩ * rowTriple (by omega) b.val)) =
      ∑ D : Fin 24, ∑ s : FourCopy D.val, ∑ t : FourCopy D.val,
        (fourWeightCoefficient Q D.val (a.val.1.val+a.val.2.val+b.output.val) s.val.val
            a.val.1.val a.val.2.val b.output.val *
         fourWeightCoefficient Q D.val (a.val.1.val+a.val.2.val+b.output.val) t.val.val
            b.val.1.val b.val.2.val a.output.val) •
          fourHighestAverage Q D.val s.val.val t.val.val := by
  let T := a.val.1.val+a.val.2.val+b.output.val
  have ht : T ≤ 23 := by have := a.val.1.isLt; have := a.val.2.isLt; have := b.output.isLt; omega
  let a' : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)) :=
    (⟨a.val.1.val,by have := a.val.1.isLt; omega⟩,
      (⟨a.val.2.val,by have := a.val.2.isLt; omega⟩,⟨b.output.val,by have := b.output.isLt; omega⟩))
  let b' : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)) :=
    (⟨b.val.1.val,by have := b.val.1.isLt; omega⟩,
      (⟨b.val.2.val,by have := b.val.2.isLt; omega⟩,⟨a.output.val,by have := a.output.isLt; omega⟩))
  have he : b'.1.val+b'.2.1.val+b'.2.2.val=T := by
    dsimp [b',T]; have := a.balance; have := b.balance; omega
  change average _ ((annihilation a'.2.2 * (annihilation a'.2.1 * physicalPair Q a'.1.val)).transpose *
    (annihilation b'.2.2 * (annihilation b'.2.1 * physicalPair Q b'.1.val))) = _
  rw [← Matrix.mul_assoc (annihilation a'.2.2), ← Matrix.mul_assoc (annihilation b'.2.2),
    rawFour_cross_average (by omega : 2 ≤ Q) (show T ≤ Q by omega) a' b' rfl he]
  change (∑ D : Fin (T+1), ∑ s : FourCopy D.val, ∑ t : FourCopy D.val,
    (fourBodyCoefficient Q D.val T s.val.val a.val.1.val a.val.2.val b.output.val *
      fourBodyCoefficient Q D.val T t.val.val b.val.1.val b.val.2.val a.output.val) •
        fourHighestAverage Q D.val s.val.val t.val.val) = _
  rw [sum_fin_extend ht (fun D => ∑ s : FourCopy D, ∑ t : FourCopy D,
    (fourBodyCoefficient Q D T s.val.val a.val.1.val a.val.2.val b.output.val *
      fourBodyCoefficient Q D T t.val.val b.val.1.val b.val.2.val a.output.val) •
        fourHighestAverage Q D s.val.val t.val.val)]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases h : D.val ≤ T <;> simp [fourWeightCoefficient,h,T]

lemma rowFour_average {Q : ℕ} (hQ : 23 ≤ Q) (r : RowData) :
    average (rotationCommutant (fockLowering Q)) (rowFour (by omega) r) =
      ∑ D : Fin 24, ∑ u : FourCopy D.val, ∑ v : FourCopy D.val,
        rowFourMatrix (fourWeightCoefficient Q) D.val r u v •
          fourHighestAverage Q D.val u.val.val v.val.val := by
  simp only [rowFour, map_neg, map_sum, map_smul, rowFour_cross_average hQ,
    Finset.smul_sum, smul_smul]
  conv_lhs =>
    arg 1; arg 2; ext a
    rw [Finset.sum_comm]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  conv_lhs =>
    arg 1; arg 2; ext a
    rw [Finset.sum_comm]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  conv_lhs =>
    arg 1; arg 2; ext a
    rw [Finset.sum_comm]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [← Finset.sum_smul, rowFourMatrix, neg_smul]
  congr 2
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma fourAverage_eq (Q D : ℕ) (C : Matrix (FourCopy D) (FourCopy D) ℝ) :
    fourAverage Q D C = ∑ u, ∑ v, C u v • fourHighestAverage Q D u.val.val v.val.val := by
  simp only [fourAverage,LinearMap.comp_apply,lift,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,
    fourHighestAverage]

lemma rowFour_average_retained {Q : ℕ} (hQ : 23 ≤ Q) (r : RowData) :
    average (rotationCommutant (fockLowering Q)) (rowFour (by omega) r) =
      ∑ d : Fin 23, fourAverage Q (d.val+1)
        (rowFourMatrix (fourWeightCoefficient Q) (d.val+1) r) := by
  rw [rowFour_average hQ, Fin.sum_univ_succ]
  have hzero (u : FourCopy 0) : False := by have := u.property.pos; have := u.val.isLt; omega
  have hz : (∑ u : FourCopy 0, ∑ v : FourCopy 0,
    rowFourMatrix (fourWeightCoefficient Q) 0 r u v • fourHighestAverage Q 0 u.val.val v.val.val) = 0 :=
      Finset.sum_eq_zero (fun u _ => (hzero u).elim)
  simp only [Fin.val_zero,Fin.val_succ]
  rw [hz,zero_add]
  apply Finset.sum_congr rfl
  intro d hd
  exact (fourAverage_eq _ _ _).symm

lemma fourAverage_copyTarget (Q : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    fourAverage Q D (fourCopyTarget D) = fourHighestAverage Q D 1 1 := by
  classical
  let r : FourCopy D := ⟨⟨1,by omega⟩,show Odd 1 by decide⟩
  have he (s : FourCopy D) : s.val.val=1 ↔ s=r := by
    constructor
    · intro hs; exact Subtype.ext (Fin.ext hs)
    · rintro rfl; rfl
  simp [fourAverage_eq,fourCopyTarget,he,ite_and,r]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Transfer. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

lemma fourDimensionRatio_eq {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    fourDimensionRatio Q D = ((4*Q-1-2*D:ℕ):ℝ)/((2*Q-1:ℕ):ℝ) := by
  rw [fourDimensionRatio,Nat.cast_sub (by omega : 2*D ≤ 4*Q-1),
    Nat.cast_sub (by omega : 1 ≤ 4*Q),Nat.cast_sub (by omega : 1 ≤ 2*Q)]
  norm_cast

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourBoundCore
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Bound Core. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

lemma localPair_average {Q L : ℕ} (hQ : 2 ≤ Q) (hL : L ≤ 2*Q-1) :
    ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
      (∑ p : Fin L, (physicalPair Q p.val).transpose * physicalPair Q p.val) =
        (L:ℝ) • physicalHamiltonian Q := by
  have he (p : Fin L) := physicalPair_single_val hQ (show p.val < 2*Q-1 by omega)
  simp only [map_sum,he,← Finset.sum_smul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    smul_smul]
  congr 1
  have hn : ((2*Q-1:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  field_simp

lemma fourAverage_identity (Q D : ℕ) :
    fourAverage Q D 1 = ∑ r : FourCopy D, fourHighestAverage Q D r.val.val r.val.val := by
  simp only [fourAverage,LinearMap.comp_apply,lift_identity,map_sum,fourHighestAverage]

lemma fourAverage_lower {Q D : ℕ} (hQ : 24 ≤ Q) (C : Matrix (FourCopy D) (FourCopy D) ℝ)
    (ρ : ℝ) (h : -ρ • (∑ p : Fin 24, (physicalPair Q p.val).transpose * physicalPair Q p.val) ≤
        lift (fun r : FourCopy D => fourAnnihilator Q D D r.val.val) C) :
    -(24*ρ) • physicalHamiltonian Q ≤ ((2*Q-1:ℕ):ℝ) • fourAverage Q D C := by
  have hh := smul_le_smul_of_nonneg_left
    (average_mono (rotationCommutant (fockLowering Q)) h)
    (Nat.cast_nonneg (α := ℝ) (2*Q-1))
  simp only [map_smul] at hh
  rw [smul_comm ((2*Q-1:ℕ):ℝ) (-ρ),localPair_average (by omega : 2 ≤ Q) (by omega)] at hh
  convert hh using 1 <;> simp [smul_smul,mul_comm,fourAverage]

lemma retained_orbitalTriple_count_fin :
    (∑ d : Fin 23, Fintype.card (OrbitalTriple (d.val+1))) = 1222 := by
  simp_rw [orbitalTriple_card]
  norm_num [Fin.sum_univ_succ]

lemma fourAllowance_le {Q : ℕ} (hQ : 24 ≤ Q) :
    ((2*Q-1:ℕ):ℝ) • (∑ d : Fin 23, fourAverage Q (d.val+1) 1) ≤
      (1222:ℝ) • physicalHamiltonian Q := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun d (_ : d ∈ (Finset.univ : Finset (Fin 23))) =>
    fourHighest_average_bessel (by omega : 2 ≤ Q) (show d.val+1 ≤ Q by omega))
  simpa only [fourAverage_identity,← Finset.smul_sum,← Finset.sum_smul,
    ← Nat.cast_sum,retained_orbitalTriple_count_fin,fourHighestAverage,Nat.cast_ofNat] using hh

lemma retainedFourTarget_le {Q : ℕ} (hQ : 24 ≤ Q) :
    retainedFourTarget Q ≤ fourTarget Q := fourTarget_retained (by omega) (by omega)

variable {ι : Type*} [Fintype ι]

lemma fourComparison_difference {Q : ℕ} (hQ : 24 ≤ Q) (rows : ι → RowData) (ε : ℝ) :
    ((2*Q-1:ℕ):ℝ) • (∑ d : Fin 23, fourAverage Q (d.val+1) (fourComparison rows ε Q (d.val+1))) =
      retainedFourTarget Q - ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
        (∑ r, rowFour (by omega) (rows r)) +
          ε • (((2*Q-1:ℕ):ℝ) • (∑ d : Fin 23, fourAverage Q (d.val+1) 1)) := by
  simp only [fourComparison,map_add,map_sub,map_smul,map_sum,Finset.smul_sum,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,smul_add,smul_sub,
    rowFour_average_retained (by omega : 23 ≤ Q)]
  rw [Finset.sum_comm (f := fun r (d : Fin 23) => _)]
  congr 2
  · unfold retainedFourTarget
    apply Finset.sum_congr rfl
    intro d hd
    rw [smul_smul,fourAverage_copyTarget Q (by omega),
      fourDimensionRatio_eq (by omega : 2 ≤ Q) (by omega)]
    have hn : ((2*Q-1:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
    congr 1
    field_simp
  · simp only [smul_smul]
    funext d
    rw [mul_comm]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Bound. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

lemma four_comparison_summed {Q : ℕ} (hQ : 24 ≤ Q)
    (rows : ι → RowData) (ε : ℝ) (ρ : Fin 23 → ℝ)
    (hQb : ∀ d : Fin 23,
      -(ρ d) • (∑ p : Fin 24, (physicalPair Q p.val).transpose * physicalPair Q p.val) ≤
        lift (fun r : FourCopy (d.val+1) => fourAnnihilator Q (d.val+1) (d.val+1) r.val.val)
          (fourComparison rows ε Q (d.val+1))) :
    -(24*∑ d, ρ d) • physicalHamiltonian Q ≤
      retainedFourTarget Q - ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
        (∑ r, rowFour (by omega) (rows r)) +
      ε • (((2*Q-1:ℕ):ℝ) • (∑ d : Fin 23, fourAverage Q (d.val+1) 1)) := by
  have hb := Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset (Fin 23))) =>
    fourAverage_lower hQ (fourComparison rows ε Q (d.val+1)) (ρ d) (hQb d))
  simpa only [← Finset.smul_sum,← Finset.sum_smul,Finset.sum_neg_distrib,
    ← Finset.mul_sum,fourComparison_difference hQ] using hb

lemma rearrange_comparison {A : Type*} [AddCommGroup A] [PartialOrder A] [IsOrderedAddMonoid A]
    {x y e r : A} (h : -r ≤ y-x+e) : x ≤ y+e+r := by
  calc
    x = -r+(x+r) := by abel
    _ ≤ (y-x+e)+(x+r) := add_le_add h (le_refl _)
    _ = y+e+r := by abel

lemma four_comparison_pointwise_oai {Q : ℕ} (hQ : 24 ≤ Q)
    (rows : ι → RowData) (ε : ℝ) (hε : 0 ≤ ε) (ρ : Fin 23 → ℝ)
    (hQb : ∀ d : Fin 23,
      -(ρ d) • (∑ p : Fin 24, (physicalPair Q p.val).transpose * physicalPair Q p.val) ≤
        lift (fun r : FourCopy (d.val+1) => fourAnnihilator Q (d.val+1) (d.val+1) r.val.val)
          (fourComparison rows ε Q (d.val+1))) :
    ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
      (∑ r, rowFour (by omega) (rows r)) ≤
        fourTarget Q + (1222*ε+24*∑ d, ρ d) • physicalHamiltonian Q := by
  have hb := four_comparison_summed hQ rows ε ρ hQb
  rw [neg_smul] at hb
  have hh := rearrange_comparison hb
  have he := smul_le_smul_of_nonneg_left (fourAllowance_le hQ) hε
  have ht := add_le_add (retainedFourTarget_le hQ) he
  have h := add_le_add ht (le_refl ((24*∑ d, ρ d) • physicalHamiltonian Q))
  apply hh.trans
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [smul_smul,add_assoc,← add_smul,mul_comm ε]

end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.LaughlinGap.RealOccupation.four_comparison_pointwise_oai.{u_1} := @OAI.LaughlinGap.RealOccupation.four_comparison_pointwise_oai.{u_1}
