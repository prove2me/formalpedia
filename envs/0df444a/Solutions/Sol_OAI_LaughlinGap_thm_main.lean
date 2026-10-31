-- Prove2me | solution 1 for OAI.LaughlinGap.thm_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T04:26:37.929047+00:00
-- url     : https://prove2.me/submissions/eba564a9-2ae9-41e0-81c5-9a62bb3fea44

import Mathlib
import Definitions.Def_LaughlinGap
import Definitions.Def_OAIQ030L003
import Definitions.Def_OAIQ030L034
import Definitions.Def_OAIQ030L035
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_exact_four
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_four_comparison_of_certificates
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_physical_spin_square_split
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_three_comparison_of_strict_traces

section
-- module Solutions.OAIQ030_LG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

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

theorem annihilation_creation {n : ℕ} (i j : Fin n) :
    annihilation i * creation j = (if i = j then 1 else 0) - creation j * annihilation i := by
  exact eq_sub_of_add_eq (annihilation_creation_CAR i j)

theorem annihilation_creation_mul {n : ℕ} (i j : Fin n)
    (X : Module.End ℂ (Hilbert n)) :
    annihilation i * (creation j * X) =
      (if i = j then X else 0) - creation j * (annihilation i * X) := by
  rw [← mul_assoc, annihilation_creation, sub_mul]
  by_cases hij : i = j <;> simp [hij, mul_assoc]

theorem auxiliary_normal_order {n : ℕ} (i k : Fin n)
    (A B : Module.End ℂ (Hilbert n)) :
    (creation i * A).adjoint * (creation k * B) =
      (if i = k then A.adjoint * B else 0) -
      (annihilation k * A).adjoint * (annihilation i * B) := by
  rw [adjoint_mul, creation_adjoint, mul_assoc, annihilation_creation_mul,
    mul_sub, adjoint_mul, annihilation_adjoint, mul_assoc]
  by_cases hik : i = k <;> simp [hik]

theorem auxiliaryRow_square {n : ℕ} {ι : Type*} [Fintype ι] (lam : ℝ)
    (Bt : Module.End ℂ (Hilbert n)) (α : ι → ℝ) (i : ι → Fin n)
    (A : ι → Module.End ℂ (Hilbert n)) :
    (auxiliaryRow lam Bt α i A).adjoint * auxiliaryRow lam Bt α i A =
      ((lam ^ 2 : ℝ) : ℂ) • (Bt.adjoint * Bt) +
      (∑ b, ((lam * α b : ℝ) : ℂ) •
        ((annihilation (i b) * Bt).adjoint * A b + (A b).adjoint * (annihilation (i b) * Bt))) +
      (∑ b, ∑ c, ((α b * α c : ℝ) : ℂ) •
        (if i b = i c then (A b).adjoint * A c else 0)) -
      (∑ b, ∑ c, ((α b * α c : ℝ) : ℂ) •
        ((annihilation (i c) * A b).adjoint * (annihilation (i b) * A c))) := by
  classical
  have hcross (b : ι) :
      Bt.adjoint * (creation (i b) * A b) = (annihilation (i b) * Bt).adjoint * A b := by
    rw [adjoint_mul, annihilation_adjoint, mul_assoc]
  rw [auxiliaryRow, map_add, map_sum]
  simp only [map_smulₛₗ, Complex.conj_ofReal, add_mul, mul_add,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  simp only [smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun c b => ((α c : ℂ) * (α b : ℂ)) • (LinearMap.adjoint (creation (i b) * A b) * (creation (i c) * A c)))]
  simp only [auxiliary_normal_order, smul_sub, Finset.sum_sub_distrib, hcross]
  simp only [adjoint_mul, creation_adjoint, annihilation_adjoint, mul_assoc,
    Complex.ofReal_mul, pow_two]
  simp only [mul_comm]
  abel

end Occupation
end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Basic
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.coordinatesFromTensor_apply _root_.OAI.LaughlinGap.pairMoment_zero
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

theorem distanceToLaughlinSq_le {N Q : ℕ} (ψ : State N Q) (c : ℂ) :
    distanceToLaughlinSq ψ ≤ ∑ a, ‖ψ a - c * laughlinVector N Q a‖ ^ 2 := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨d, rfl⟩
    exact Finset.sum_nonneg (fun a ha => sq_nonneg _)
  · exact ⟨c, rfl⟩

theorem particleWeight_eq {N : ℕ} (k : Fin N) (d : SpinorVariables N →₀ ℕ) :
    Finsupp.weight (particleWeight k) d = d (k, false) + d (k, true) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [particleWeight, Fintype.sum_prod_type, mul_ite, Finset.sum_add_distrib, add_comm]

private theorem particle_pair_count {N : ℕ} (k : Fin N) :
    (∑ i : Fin N, ∑ j : Fin N,
      if i < j then (if i = k then 1 else 0) + (if j = k then 1 else 0) else 0) = N - 1 := by
  classical
  have hterm (i j : Fin N) :
      (if i < j then (if i = k then 1 else 0) + (if j = k then 1 else 0) else 0 : ℕ) =
      (if i = k then if i < j then 1 else 0 else 0) +
      (if j = k then if i < j then 1 else 0 else 0) := by
    split_ifs <;> simp
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  have hlt (i : Fin N) :
      (if k < i then 1 else 0) + (if i < k then 1 else 0) = (if i = k then 0 else 1 : ℕ) := by
    rcases lt_trichotomy i k with hi | rfl | hi
    · simp [hi, not_lt.mpr (le_of_lt hi), ne_of_lt hi]
    · simp
    · simp [hi, not_lt.mpr (le_of_lt hi), ne_of_gt hi]
  simp_rw [hlt]
  simp [Finset.sum_ite, Finset.filter_ne']

theorem bracket_isWeightedHomogeneous {N : ℕ} (k i j : Fin N) :
    MvPolynomial.IsWeightedHomogeneous (particleWeight k) (bracket i j)
      ((if i = k then 1 else 0) + (if j = k then 1 else 0)) := by
  have h1 := (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (particleWeight k) (i, false)).mul
    (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (particleWeight k) (j, true))
  have h2 := (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (particleWeight k) (j, false)).mul
    (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (particleWeight k) (i, true))
  simp only [particleWeight] at h1 h2
  exact h1.sub (by simpa only [add_comm] using h2)

theorem laughlinPolynomial_isWeightedHomogeneous (N : ℕ) (k : Fin N) :
    MvPolynomial.IsWeightedHomogeneous (particleWeight k) (laughlinPolynomial N) (3 * (N - 1)) := by
  classical
  have hcount : (∑ i : Fin N, ∑ j : Fin N,
      if i < j then 3 * ((if i = k then 1 else 0) + (if j = k then 1 else 0)) else 0) =
      3 * (N - 1) := by
    have hterm (i j : Fin N) :
        (if i < j then 3 * ((if i = k then 1 else 0) + (if j = k then 1 else 0)) else 0) =
        3 * (if i < j then ((if i = k then 1 else 0) + (if j = k then 1 else 0)) else 0 : ℕ) := by
      split_ifs <;> simp
    simp_rw [hterm, ← Finset.mul_sum]
    rw [particle_pair_count]
  rw [← hcount]
  unfold laughlinPolynomial
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro i hi
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro j hj
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using (bracket_isWeightedHomogeneous k i j).pow 3
  · simp only [ite_eq_right hij]
    exact MvPolynomial.isWeightedHomogeneous_one ℂ (particleWeight k)

theorem laughlinPolynomial_support_exponents (N : ℕ) (d : SpinorVariables N →₀ ℕ)
    (hd : (laughlinPolynomial N).coeff d ≠ 0) :
    ∃ a : Configuration N (3 * (N - 1)), monomialExponent a = d := by
  have hdeg (k : Fin N) : d (k, false) + d (k, true) = 3 * (N - 1) := by
    simpa only [particleWeight_eq] using (laughlinPolynomial_isWeightedHomogeneous N k) hd
  let a : Configuration N (3 * (N - 1)) := fun k =>
    ⟨d (k, true), by have h := hdeg k; omega⟩
  refine ⟨a, ?_⟩
  ext ⟨k, b⟩
  cases b
  · simp only [monomialExponent, Finsupp.onFinset_apply, Bool.false_eq_true, ↓reduceIte]
    have h := hdeg k
    change 3 * (N - 1) - d (k, true) = d (k, false)
    omega
  · rfl

section PairNormalization
open Polynomial

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q + 1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  by_cases hs : x.val + y.val = p + 1
  · simp only [hs, Nat.add_comm y.val x.val, ↓reduceIte]
    simp only [mul_comm, mul_left_comm, mul_assoc]
    ring
  · simp [hs, Nat.add_comm]

end PairNormalization

theorem kernel_distance_of_square_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (γ : ℝ) (hsq : ∀ x : E, γ * (inner ℂ x (T x)).re ≤ ‖T x‖ ^ 2)
    (x : E) :
    ∃ y : E, T y = 0 ∧ γ * ‖x - y‖ ^ 2 ≤ (inner ℂ x (T x)).re := by
  classical
  let b := hT.isSymmetric.eigenvectorBasis rfl
  let lam := hT.isSymmetric.eigenvalues rfl
  have hdiag (v : E) (i : Fin (Module.finrank ℂ E)) :
      b.repr (T v) i = (lam i : ℂ) * b.repr v i :=
    hT.isSymmetric.eigenvectorBasis_apply_self_apply rfl v i
  have hlambda (i : Fin (Module.finrank ℂ E)) : lam i = 0 ∨ γ ≤ lam i := by
    by_cases hi : lam i = 0
    · exact Or.inl hi
    right
    have hnonneg : 0 ≤ lam i := hT.nonneg_eigenvalues rfl i
    have h := hsq (b i)
    have heig : T (b i) = (lam i : ℂ) • b i :=
      hT.isSymmetric.apply_eigenvectorBasis rfl i
    rw [heig, inner_smul_right, b.inner_eq_one, mul_one] at h
    simp only [Complex.ofReal_re, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      b.norm_eq_one, mul_one, sq_abs] at h
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using h) (lt_of_le_of_ne hnonneg (Ne.symm hi))
  let c : EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) :=
    WithLp.toLp 2 (fun i => if lam i = 0 then b.repr x i else 0)
  let y := b.repr.symm c
  have hyrepr : b.repr y = c := b.repr.apply_symm_apply c
  have hTy : T y = 0 := by
    apply b.repr.injective
    ext i
    rw [hdiag, hyrepr, map_zero]
    change (lam i : ℂ) * (if lam i = 0 then b.repr x i else 0) = 0
    split_ifs with hi <;> simp [hi]
  have henergy : (inner ℂ x (T x)).re = ∑ i, lam i * ‖b.repr x i‖ ^ 2 := by
    rw [← b.repr.inner_map_map, PiLp.inner_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdiag, RCLike.inner_apply, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  refine ⟨y, hTy, ?_⟩
  rw [henergy, ← b.repr.norm_map (x - y), EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simp only [map_sub, hyrepr, PiLp.sub_apply]
  change γ * ‖b.repr x i - (if lam i = 0 then b.repr x i else 0)‖ ^ 2 ≤ _
  obtain hzero | hge := hlambda i
  · simp [hzero]
  · by_cases hzero : lam i = 0
    · simp [hzero]
    · simp only [hzero, ↓reduceIte, sub_zero]
      exact mul_le_mul_of_nonneg_right hge (sq_nonneg _)

theorem tensorMonomialScale_pos {N Q : ℕ} (a : Configuration N Q) :
    0 < tensorMonomialScale a := by
  unfold tensorMonomialScale
  exact Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a i).isLt)))

theorem monomialExponent_injective (N Q : ℕ) :
    Function.Injective (monomialExponent (N := N) (Q := Q)) := by
  intro a b he
  funext k
  apply Fin.ext
  have h := congrArg (fun d : SpinorVariables N →₀ ℕ => d (k, true)) he
  simpa only [monomialExponent, Finsupp.onFinset_apply, ↓reduceIte] using h

@[simp]
theorem coeff_statePolynomial {N Q : ℕ} (ψ : State N Q) (a : Configuration N Q) :
    (statePolynomial ψ).coeff (monomialExponent a) = (tensorMonomialScale a : ℂ) * ψ a := by
  classical
  simp [statePolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, (monomialExponent_injective N Q).eq_iff]

theorem coeff_statePolynomial_of_not_grid {N Q : ℕ} (ψ : State N Q)
    (d : SpinorVariables N →₀ ℕ) (h : ∀ a : Configuration N Q, monomialExponent a ≠ d) :
    (statePolynomial ψ).coeff d = 0 := by
  classical
  simp [statePolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, h]

@[simp]
theorem statePolynomial_laughlinVector (N : ℕ) :
    statePolynomial (laughlinVector N (3 * (N - 1))) = laughlinPolynomial N := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : ∃ a : Configuration N (3 * (N - 1)), monomialExponent a = d
  · obtain ⟨a, rfl⟩ := hd
    rw [coeff_statePolynomial]
    change (tensorMonomialScale a : ℂ) *
      ((laughlinPolynomial N).coeff (monomialExponent a) / (tensorMonomialScale a : ℂ)) = _
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (tensorMonomialScale_pos a)))
  · push Not at hd
    rw [coeff_statePolynomial_of_not_grid _ _ hd]
    by_contra hc
    obtain ⟨a, ha⟩ := laughlinPolynomial_support_exponents N d (Ne.symm hc)
    exact hd a ha

theorem pairAmplitude_eq_of_spectators_eq {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (p : ℕ) (a b : Configuration N Q)
    (h : ∀ k, k ≠ i → k ≠ j → a k = b k) :
    pairAmplitude ψ i j p a = pairAmplitude ψ i j p b := by
  classical
  unfold pairAmplitude
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  congr 2
  funext k
  by_cases hkj : k = j
  · simp [hkj]
  by_cases hki : k = i
  · simp [Function.update_apply, hki]
  simp [hki, hkj, h k hki hkj]

theorem pairAmplitude_anchor {N Q : ℕ} (ψ : State N Q) (i j : Fin N)
    (p : ℕ) (a : Configuration N Q) :
    pairAmplitude ψ i j p (Function.update (Function.update a i 0) j 0) =
      pairAmplitude ψ i j p a := by
  apply pairAmplitude_eq_of_spectators_eq
  intro k hki hkj
  simp [hki, hkj]

theorem energy_eq_zero_iff {N Q : ℕ} (ψ : State N Q) :
    energy ψ = 0 ↔ ∀ i j : Fin N, i < j → ∀ p : ℕ, p < 2 * Q - 1 →
      ∀ a : Configuration N Q, pairAmplitude ψ i j p a = 0 := by
  classical
  constructor
  · intro h i j hij p hp a
    unfold energy at h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (by intro _ _; positivity)).mp h i
      (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (by intro _ _; positivity)).mp hi j
      (Finset.mem_univ j)
    rw [ite_eq_left hij] at hj
    have hpp := (Finset.sum_eq_zero_iff_of_nonneg (by intro _ _; positivity)).mp hj p
      (Finset.mem_range.mpr hp)
    let b := Function.update (Function.update a i 0) j 0
    have hb : b i = 0 ∧ b j = 0 := by
      simp [b, ne_of_lt hij]
    have ha := (Finset.sum_eq_zero_iff_of_nonneg (by intro _ _; positivity)).mp hpp b
      (Finset.mem_univ b)
    rw [ite_eq_left hb] at ha
    rw [pairAmplitude_anchor] at ha
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp ha)
  · intro h
    unfold energy
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with hij
    · apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro a ha
      simp [h i j hij p (Finset.mem_range.mp hp) a]
    · rfl

theorem pairContractions_norm_sq {N Q : ℕ} (ψ : TensorHilbert N Q) :
    ‖pairContractions N Q ψ‖ ^ 2 = energy (WithLp.ofLp ψ) := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [pairContractions, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    Fintype.sum_prod_type]
  unfold energy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, true_and, ↓reduceIte]
    rw [Fin.sum_univ_eq_sum_range (fun p : ℕ =>
      ∑ a : Configuration N Q,
        ‖if a i = 0 ∧ a j = 0 then pairAmplitude (WithLp.ofLp ψ) i j p a else 0‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp
  · simp [hij]

theorem sectorHamiltonian_positive (N Q : ℕ) : LinearMap.IsPositive (𝕜 := ℂ) (E := SectorHilbert N Q) (sectorHamiltonian N Q) :=
  LinearMap.isPositive_adjoint_comp_self (𝕜 := ℂ)
    (E := SectorHilbert N Q) (F := EuclideanSpace ℂ (ContractionIndex N Q)) _

theorem sectorHamiltonian_inner {N Q : ℕ} (ψ : SectorHilbert N Q) :
    (inner ℂ ψ (sectorHamiltonian N Q ψ)).re = energy (WithLp.ofLp ψ.val) := by
  change (inner ℂ ψ ((LinearMap.adjoint (𝕜 := ℂ) (E := SectorHilbert N Q)
    (F := EuclideanSpace ℂ (ContractionIndex N Q)) (sectorContractions N Q)) (sectorContractions N Q ψ))).re = _
  rw [LinearMap.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (sectorContractions N Q ψ)).symm.trans
    (pairContractions_norm_sq ψ.val)

theorem sectorHamiltonian_eq_zero_iff {N Q : ℕ} (ψ : SectorHilbert N Q) :
    sectorHamiltonian N Q ψ = 0 ↔ energy (WithLp.ofLp ψ.val) = 0 := by
  constructor
  · intro h
    rw [← sectorHamiltonian_inner ψ, h]
    simp
  · intro h
    have ha : sectorContractions N Q ψ = 0 := by
      apply norm_eq_zero.mp
      have hnorm : ‖sectorContractions N Q ψ‖ ^ 2 = 0 :=
        (pairContractions_norm_sq ψ.val).trans h
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hnorm
    change (LinearMap.adjoint (𝕜 := ℂ) (E := SectorHilbert N Q)
    (F := EuclideanSpace ℂ (ContractionIndex N Q)) (sectorContractions N Q)) (sectorContractions N Q ψ) = 0
    rw [ha, map_zero]

namespace Chart
open MvPolynomial
open scoped BigOperators

theorem difference_dvd_sub_diagonal {σ : Type*} [DecidableEq σ] (i j : σ)
    (F : MvPolynomial σ ℂ) : difference i j ∣ F - diagonal i j F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [diagonal]
  | add a b ha hb => simpa only [map_add, add_sub_add_comm] using dvd_add ha hb
  | mul_X p k hp =>
    have hx : difference i j ∣ X k - diagonal i j (X k) := by
      by_cases hk : k = j
      · simp [hk, diagonal, difference]
      · simp [diagonal, hk]
    have hd := dvd_add (dvd_mul_of_dvd_left hp (X k))
      (dvd_mul_of_dvd_right hx (diagonal i j p))
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    simp only [map_mul]
    ring

theorem difference_dvd_of_diagonal_eq_zero {σ : Type*} [DecidableEq σ] (i j : σ)
    (F : MvPolynomial σ ℂ) (h : diagonal i j F = 0) : difference i j ∣ F := by
  simpa only [h, sub_zero] using difference_dvd_sub_diagonal i j F

lemma difference_ne_zero {σ : Type*} {i j : σ} (h : i ≠ j) : difference i j ≠ 0 := by
  classical
  intro he
  have hh := congrArg (MvPolynomial.eval (fun k : σ => if k = j then (1 : ℂ) else 0)) he
  simp [difference, h] at hh

lemma diagonal_rename_swap {σ : Type*} [DecidableEq σ] (i j : σ)
    (F : MvPolynomial σ ℂ) :
    diagonal i j (rename (Equiv.swap i j) F) = diagonal i j F := by
  unfold diagonal
  rw [rename_rename]
  have he : Function.update id j i ∘ Equiv.swap i j = Function.update id j i := by
    funext k
    by_cases hki : k = i
    · subst k; by_cases hij : i = j <;> simp [hij]
    by_cases hkj : k = j
    · subst k; simp [Ne.symm hki]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hkj]
  rw [he]

theorem diagonal_eq_zero_of_antisymmetric {σ : Type*} [DecidableEq σ] (i j : σ)
    (F : MvPolynomial σ ℂ) (h : rename (Equiv.swap i j) F = -F) :
    diagonal i j F = 0 := by
  have hd := congrArg (diagonal i j) h
  rw [diagonal_rename_swap, map_neg] at hd
  have hs : (2 : ℂ) • diagonal i j F = 0 := by
    rw [two_smul]
    calc
      diagonal i j F + diagonal i j F = -diagonal i j F + diagonal i j F :=
        congrArg (fun x => x + diagonal i j F) hd
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hs).resolve_left (by norm_num)

lemma rename_difference_swap {σ : Type*} [DecidableEq σ] (i j : σ) :
    rename (Equiv.swap i j) (difference i j) = -difference i j := by
  simp [difference, sub_eq_add_neg]

theorem difference_cube_dvd {σ : Type*} [DecidableEq σ] (i j : σ) (hij : i ≠ j)
    (F : MvPolynomial σ ℂ) (hanti : rename (Equiv.swap i j) F = -F)
    (hderiv : diagonal i j (pderiv j F) = 0) : difference i j ^ 3 ∣ F := by
  obtain ⟨G, hG⟩ := difference_dvd_of_diagonal_eq_zero i j F
    (diagonal_eq_zero_of_antisymmetric i j F hanti)
  have hGsym : rename (Equiv.swap i j) G = G := by
    rw [hG, map_mul, rename_difference_swap, neg_mul] at hanti
    exact mul_left_cancel₀ (difference_ne_zero hij) (neg_inj.mp hanti)
  have hdiagG : diagonal i j G = 0 := by
    rw [hG, pderiv_mul] at hderiv
    simpa [difference, diagonal, hij, Ne.symm hij] using hderiv
  obtain ⟨H, hH⟩ := difference_dvd_of_diagonal_eq_zero i j G hdiagG
  have hHanti : rename (Equiv.swap i j) H = -H := by
    rw [hH, map_mul, rename_difference_swap, neg_mul] at hGsym
    apply mul_left_cancel₀ (difference_ne_zero hij)
    simpa only [mul_neg] using neg_eq_iff_eq_neg.mp hGsym
  obtain ⟨K, hK⟩ := difference_dvd_of_diagonal_eq_zero i j H
    (diagonal_eq_zero_of_antisymmetric i j H hHanti)
  refine ⟨K, ?_⟩
  rw [hG, hH, hK]
  ring

end Chart

section LocalKernel
open MvPolynomial

theorem pairWeightScale_pos {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2 * Q - 1) :
    0 < pairWeightScale Q p := by
  unfold pairWeightScale
  have hc : (0 : ℝ) < ((2 * Q - 2).choose p : ℝ) := by
    exact_mod_cast Nat.choose_pos (show p ≤ 2 * Q - 2 by omega)
  positivity

theorem pairCoefficient_binomial (Q p : ℕ) (x y : Fin (Q + 1)) :
    pairCoefficient Q p x y =
      if x.val + y.val = p + 1 then
        pairWeightScale Q p * ((x.val : ℝ) - y.val) *
          (Real.sqrt (Q.choose x.val : ℝ) * Real.sqrt (Q.choose y.val : ℝ))
      else 0 := by
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hrad :
      (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) =
      ((Q.choose x.val : ℝ) * Q.choose y.val) *
        (1 / ((Q : ℝ) * ((2 * Q - 2).choose p : ℝ))) := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  unfold pairCoefficient
  split_ifs
  · rw [hrad, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    unfold pairWeightScale
    ring
  · rfl

theorem pair_contraction_eq_moment {Q p : ℕ}
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ) * φ x y) =
      (pairWeightScale Q p : ℂ) * pairMoment φ (p + 1) := by
  simp only [pairMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [pairCoefficient_binomial]
  split_ifs
  · push_cast
    ring
  · simp

theorem localPairPolynomial_antisymmetric {Q : ℕ}
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) (hφ : ∀ x y, φ y x = -φ x y) :
    rename (Equiv.swap false true) (localPairPolynomial φ) = - localPairPolynomial φ := by
  classical
  simp only [localPairPolynomial, map_sum, map_mul, map_pow, rename_C, rename_X,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hφ x y]
  simp only [mul_neg, map_neg, neg_mul]
  push_cast
  ring_nf

private theorem diagonal_difference_derivative_monomial (x y : ℕ) (c : ℂ) :
    Chart.diagonal false true
      (pderiv false (C c * X false ^ x * X true ^ y) -
        pderiv true (C c * X false ^ x * X true ^ y)) =
      C (((x : ℂ) - y) * c) * X false ^ (x + y - 1) := by
  simp only [pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self,
    pderiv_X_of_ne (by decide : true ≠ false), pderiv_X_of_ne (by decide : false ≠ true)]
  cases x <;> cases y <;> simp [Chart.diagonal, pow_add, pow_succ] <;> ring_nf

theorem pairMoment_eq_zero_of_contractions {Q : ℕ} (hQ : 2 ≤ Q)
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (h : ∀ p < 2 * Q - 1, ∑ x, ∑ y, (pairCoefficient Q p x y : ℂ) * φ x y = 0)
    (n : ℕ) : pairMoment φ n = 0 := by
  by_cases hn : 0 < n ∧ n < 2 * Q
  · have hp : n - 1 < 2 * Q - 1 := by omega
    have he := h (n - 1) hp
    rw [pair_contraction_eq_moment, Nat.sub_add_cancel hn.1] at he
    exact (mul_eq_zero.mp he).resolve_left
      (Complex.ofReal_ne_zero.mpr (pairWeightScale_pos hQ hp).ne')
  · unfold pairMoment
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    split_ifs with hxy
    · have he : x.val = y.val := by have := x.isLt; have := y.isLt; omega
      simp [he]
    · rfl

theorem localPairPolynomial_diagonal_difference_derivative {Q : ℕ}
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    Chart.diagonal false true
      (pderiv false (localPairPolynomial φ) - pderiv true (localPairPolynomial φ)) =
    ∑ n ∈ Finset.range (2 * Q + 1), C (pairMoment φ n) * X false ^ (n - 1) := by
  classical
  simp only [localPairPolynomial, map_sum, ← Finset.sum_sub_distrib,
    diagonal_difference_derivative_monomial]
  simp only [pairMoment, map_sum, Finset.sum_mul, apply_ite C, map_zero, ite_mul, zero_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  symm
  rw [Finset.sum_eq_single (x.val + y.val)]
  · simp [mul_assoc]
  · intro b hb hne
    simp [Ne.symm hne]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by have := x.isLt; have := y.isLt; omega))).elim

theorem localPairPolynomial_cubic_divisibility {Q : ℕ} (hQ : 2 ≤ Q)
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (hanti : ∀ x y, φ y x = -φ x y)
    (hker : ∀ p < 2 * Q - 1, ∑ x, ∑ y, (pairCoefficient Q p x y : ℂ) * φ x y = 0) :
    Chart.difference false true ^ 3 ∣ localPairPolynomial φ := by
  have ha := localPairPolynomial_antisymmetric φ hanti
  apply Chart.difference_cube_dvd false true (by decide) _ ha
  have hd : Chart.diagonal false true
      (pderiv false (localPairPolynomial φ) - pderiv true (localPairPolynomial φ)) = 0 := by
    rw [localPairPolynomial_diagonal_difference_derivative]
    simp [pairMoment_eq_zero_of_contractions hQ φ hker]
  have hs := pderiv_rename (Equiv.swap false true).injective false (localPairPolynomial φ)
  simp only [Equiv.swap_apply_left, ha, map_neg] at hs
  have hds := congrArg (Chart.diagonal false true) hs
  rw [map_neg, Chart.diagonal_rename_swap] at hds
  rw [map_sub] at hd
  have hz : (2 : MvPolynomial Bool ℂ) *
      Chart.diagonal false true (pderiv true (localPairPolynomial φ)) = 0 := by
    linear_combination -hd - hds
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end LocalKernel

namespace Chart
open MvPolynomial

lemma monomial_as_prod {N Q : ℕ} (a : Configuration N Q) (c : ℂ) :
    monomial (exponent a) c = C c * ∏ i : Fin N, X i ^ (a i).val := by
  rw [monomial_eq, Finsupp.prod_pow]
  rfl

lemma exponent_injective (N Q : ℕ) : Function.Injective (exponent (N := N) (Q := Q)) := by
  intro a b h
  funext k
  apply Fin.ext
  exact congrArg (fun d : Fin N →₀ ℕ => d k) h

@[simp] theorem coeff_statePolynomial {N Q : ℕ} (ψ : State N Q) (a : Configuration N Q) :
    (statePolynomial ψ).coeff (exponent a) = (tensorMonomialScale a : ℂ) * ψ a := by
  classical
  simp [statePolynomial, MvPolynomial.coeff_sum, coeff_monomial, (exponent_injective N Q).eq_iff]

theorem statePolynomial_injective (N Q : ℕ) :
    Function.Injective (statePolynomial (N := N) (Q := Q)) := by
  intro ψ φ h
  funext a
  have ha := congrArg (fun F : MvPolynomial (Fin N) ℂ => F.coeff (exponent a)) h
  simp only [coeff_statePolynomial] at ha
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (tensorMonomialScale_pos a).ne') ha

theorem spinorChart_statePolynomial {N Q : ℕ} (ψ : State N Q) :
    spinorChart N (LaughlinGap.statePolynomial ψ) = statePolynomial ψ := by
  classical
  simp only [LaughlinGap.statePolynomial, map_sum, statePolynomial]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [spinorChart, aeval_monomial]
  simp [Fintype.prod_prod_type, LaughlinGap.monomialExponent, monomial_as_prod]

@[simp] theorem statePolynomial_laughlinVector (N : ℕ) :
    statePolynomial (laughlinVector N (3 * (N - 1))) = laughlinPolynomial N := by
  rw [← spinorChart_statePolynomial, LaughlinGap.statePolynomial_laughlinVector,
    spinorChart_laughlinPolynomial]

theorem statePolynomial_degreeOf_le {N Q : ℕ} (ψ : State N Q) (k : Fin N) :
    (statePolynomial ψ).degreeOf k ≤ Q := by
  classical
  apply degreeOf_le_iff.mpr
  intro d hd
  have hex : ∃ a : Configuration N Q, exponent a = d := by
    by_contra! h
    have hz : (statePolynomial ψ).coeff d = 0 := by
      simp [statePolynomial, MvPolynomial.coeff_sum, coeff_monomial, h]
    exact (mem_support_iff.mp hd) hz
  obtain ⟨a, rfl⟩ := hex
  exact Nat.le_of_lt_succ (a k).isLt

private lemma prod_update_pair {N Q : ℕ} {M : Type*} [CommMonoid M]
    (i j : Fin N) (hij : i ≠ j) (a : Configuration N Q) (x y : Fin (Q + 1))
    (f : Fin N → Fin (Q + 1) → M) :
    (∏ k : Fin N, f k (Function.update (Function.update a i x) j y k)) =
      f i x * f j y * ∏ k ∈ (Finset.univ.erase i).erase j, f k (a k) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)]
  simp only [Function.update_of_ne hij, Function.update_self, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro k hk
  have hi := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hj := (Finset.mem_erase.mp hk).1
  simp [Function.update_of_ne hi, Function.update_of_ne hj]

private lemma monomial_as_normalized_prod {N Q : ℕ} (a : Configuration N Q) (c : ℂ) :
    monomial (exponent a) ((tensorMonomialScale a : ℂ) * c) =
      C c * ∏ k : Fin N, C (Real.sqrt (Q.choose (a k).val : ℝ) : ℂ) * X k ^ (a k).val := by
  rw [monomial_as_prod]
  simp only [tensorMonomialScale, Complex.ofReal_prod, map_mul, map_prod, Finset.prod_mul_distrib]
  ring

theorem statePolynomial_pair_decomposition {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) :
    statePolynomial ψ =
      ∑ a : PairSpectators (Q := Q) i j, spectatorMonomial i j a *
        rename (fun b : Bool => if b then j else i)
          (localPairPolynomial (fun x y => ψ (Function.update (Function.update a.val i x) j y))) := by
  classical
  unfold statePolynomial
  rw [← (pairConfigurationEquiv (Q := Q) i j hij).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [localPairPolynomial, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  change monomial (exponent (Function.update (Function.update a.val i x) j y))
    ((tensorMonomialScale (Function.update (Function.update a.val i x) j y) : ℂ) *
      ψ (Function.update (Function.update a.val i x) j y)) = _
  rw [monomial_as_normalized_prod, prod_update_pair i j hij a.val x y
    (fun k x => C (Real.sqrt (Q.choose x.val : ℝ) : ℂ) * X k ^ x.val)]
  simp only [map_mul, map_pow, rename_C, rename_X, Bool.false_eq_true, ↓reduceIte,
    Complex.ofReal_mul]
  unfold spectatorMonomial
  ring

private lemma update_pair_swap {N Q : ℕ} (a : Configuration N Q)
    (i j : Fin N) (hij : i ≠ j) (x y : Fin (Q + 1)) :
    (Function.update (Function.update a i x) j y) ∘ Equiv.swap i j =
      Function.update (Function.update a i y) j x := by
  funext k
  by_cases hki : k = i
  · simp [hki, hij]
  by_cases hkj : k = j
  · simp [hkj, hij]
  simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj,
    Function.update_of_ne hki, Function.update_of_ne hkj]

theorem difference_cube_dvd_statePolynomial_of_energy_zero {N Q : ℕ} (hQ : 2 ≤ Q)
    (ψ : State N Q) (hψ : Antisymmetric ψ) (hE : energy ψ = 0)
    (i j : Fin N) (hij : i < j) : difference i j ^ 3 ∣ statePolynomial ψ := by
  classical
  rw [statePolynomial_pair_decomposition ψ i j (ne_of_lt hij)]
  apply Finset.dvd_sum
  intro a ha
  apply dvd_mul_of_dvd_right
  have hlocal := localPairPolynomial_cubic_divisibility hQ
    (fun x y => ψ (Function.update (Function.update a.val i x) j y))
    (by
      intro x y
      have h := hψ i j (ne_of_lt hij) (Function.update (Function.update a.val i x) j y)
      rwa [update_pair_swap a.val i j (ne_of_lt hij)] at h)
    (fun p hp => (LaughlinGap.energy_eq_zero_iff ψ).mp hE i j hij p hp a.val)
  have hd := map_dvd (rename (fun b : Bool => if b then j else i)).toRingHom hlocal
  simpa [difference] using hd

theorem difference_irreducible {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Irreducible (difference i j) := by
  have ht : (difference i j).totalDegree = 1 :=
    ((isHomogeneous_X ℂ j).sub (isHomogeneous_X ℂ i)).totalDegree (difference_ne_zero hij)
  apply irreducible_of_totalDegree_eq_one ht
  intro r hr
  apply isUnit_of_dvd_one
  have hs : Finsupp.single i 1 ≠ (Finsupp.single j 1 : Fin N →₀ ℕ) := by
    intro h
    have hc := congrArg (fun d : Fin N →₀ ℕ => d i) h
    simp [hij] at hc
  simpa [difference, coeff_X, hs] using hr (Finsupp.single j 1)

theorem difference_not_dvd {N : ℕ} {i j k l : Fin N} (hij : i < j) (hkl : k < l)
    (hne : (i, j) ≠ (k, l)) : ¬ difference k l ∣ difference i j := by
  have hex : (i ≠ k ∧ i ≠ l) ∨ (j ≠ k ∧ j ≠ l) := by
    by_contra! h
    have hi : i = k ∨ i = l := by tauto
    have hj : j = k ∨ j = l := by tauto
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (lt_irrefl _ hij)
    · exact hne rfl
    · exact (not_lt_of_ge (le_of_lt hkl) hij)
    · exact (lt_irrefl _ hij)
  intro hdiv
  obtain ⟨g, hg⟩ := hdiv
  rcases hex with hi | hj
  · have h := congrArg (eval (fun m : Fin N => if m = i then (1 : ℂ) else 0)) hg
    simp [difference, Ne.symm hi.1, Ne.symm hi.2, (ne_of_lt hij).symm] at h
  · have h := congrArg (eval (fun m : Fin N => if m = j then (1 : ℂ) else 0)) hg
    simp [difference, Ne.symm hj.1, Ne.symm hj.2, ne_of_lt hij] at h

theorem laughlinPolynomial_ne_zero (N : ℕ) : laughlinPolynomial N ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  split_ifs with hij
  · exact pow_ne_zero _ (difference_ne_zero (ne_of_lt hij))
  · exact one_ne_zero

theorem laughlinPolynomial_dvd_of_difference_cubes_dvd {N : ℕ}
    (F : MvPolynomial (Fin N) ℂ) (h : ∀ i j : Fin N, i < j → difference i j ^ 3 ∣ F) :
    laughlinPolynomial N ∣ F := by
  classical
  have heq : laughlinPolynomial N =
      ∏ ij ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2),
        difference ij.1 ij.2 ^ 3 := by
    simp only [Finset.prod_filter, Fintype.prod_prod_type, laughlinPolynomial]
  rw [heq]
  apply Finset.prod_dvd_of_isRelPrime
  · intro ij hij kl hkl hne
    have hij' := (Finset.mem_filter.mp hij).2
    have hkl' := (Finset.mem_filter.mp hkl).2
    exact ((difference_irreducible (ne_of_lt hij')).isRelPrime_iff_not_dvd.mpr
      (difference_not_dvd hkl' hij' hne.symm)).pow
  · intro ij hij
    exact h ij.1 ij.2 (Finset.mem_filter.mp hij).2

lemma difference_degreeOf {N : ℕ} (i j k : Fin N) (hij : i ≠ j) :
    (difference i j).degreeOf k = (if i = k then 1 else 0) + (if j = k then 1 else 0) := by
  by_cases hki : k = i
  · subst k
    have hd := degreeOf_add_eq_of_degreeOf_lt
      (p := -(X i : MvPolynomial (Fin N) ℂ)) (q := X j) (i := i)
      (by simp [degreeOf_X, hij])
    simpa [difference, sub_eq_add_neg, add_comm, Ne.symm hij] using hd
  by_cases hkj : k = j
  · subst k
    have hd := degreeOf_add_eq_of_degreeOf_lt
      (p := (X j : MvPolynomial (Fin N) ℂ)) (q := -X i) (i := j)
      (by simp [degreeOf_X, Ne.symm hij])
    simpa [difference, sub_eq_add_neg, hij] using hd
  have hd := degreeOf_sub_le k (X j : MvPolynomial (Fin N) ℂ) (X i)
  have hz : (difference i j).degreeOf k = 0 := by
    simpa [difference, degreeOf_X, hkj, hki] using hd
  simpa [Ne.symm hki, Ne.symm hkj] using hz

theorem laughlinPolynomial_degreeOf (N : ℕ) (k : Fin N) :
    (laughlinPolynomial N).degreeOf k = 3 * (N - 1) := by
  classical
  have hf (i j : Fin N) : (if i < j then difference i j ^ 3 else 1) ≠ 0 := by
    split_ifs with hij
    · exact pow_ne_zero _ (difference_ne_zero (ne_of_lt hij))
    · exact one_ne_zero
  have hterm (i j : Fin N) :
      degreeOf k (if i < j then difference i j ^ 3 else 1) =
      3 * (if i < j then (if i = k then 1 else 0) + (if j = k then 1 else 0) else 0) := by
    by_cases hij : i < j
    · simp only [ite_eq_left hij]
      rw [degreeOf_pow_eq _ _ _ (difference_ne_zero (ne_of_lt hij)), difference_degreeOf _ _ _ (ne_of_lt hij)]
    · simp [hij]
  unfold laughlinPolynomial
  rw [degreeOf_prod_eq _ _ (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j _ => hf i j))]
  simp_rw [degreeOf_prod_eq _ _ (fun j _ => hf _ j), hterm, ← Finset.mul_sum]
  rw [LaughlinGap.particle_pair_count]

private lemma eq_constant_of_degreeOf_eq_zero {N : ℕ} (G : MvPolynomial (Fin N) ℂ)
    (h : ∀ k, G.degreeOf k = 0) : G = C (G.coeff 0) := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = 0
  · simp [hd]
  have hz : G.coeff d = 0 := by
    by_contra hc
    have hde : d = 0 := by
      apply Finsupp.ext
      intro k
      have hk := monomial_le_degreeOf k (mem_support_iff.mpr hc)
      rw [h k] at hk
      exact Nat.eq_zero_of_le_zero hk
    exact hd hde
  simp [hz, coeff_C, Ne.symm hd]

theorem eq_scalar_laughlin_of_difference_cubes_dvd {N : ℕ}
    (F : MvPolynomial (Fin N) ℂ) (hdeg : ∀ k : Fin N, F.degreeOf k ≤ 3 * (N - 1))
    (hdiv : ∀ i j : Fin N, i < j → difference i j ^ 3 ∣ F) :
    ∃ c : ℂ, F = c • laughlinPolynomial N := by
  obtain ⟨G, hG⟩ := laughlinPolynomial_dvd_of_difference_cubes_dvd F hdiv
  by_cases hG0 : G = 0
  · refine ⟨0, ?_⟩
    simp [hG, hG0]
  have hz : ∀ k : Fin N, G.degreeOf k = 0 := by
    intro k
    have hd := hdeg k
    rw [hG, degreeOf_mul_eq (laughlinPolynomial_ne_zero N) hG0, laughlinPolynomial_degreeOf] at hd
    omega
  refine ⟨G.coeff 0, ?_⟩
  rw [hG, eq_constant_of_degreeOf_eq_zero G hz, mul_comm, C_mul']
  simp

end Chart

theorem energy_zero_imp_laughlin {N : ℕ} (hN : 2 ≤ N)
    (ψ : State N (3 * (N - 1))) (hψ : Antisymmetric ψ) (hE : energy ψ = 0) :
    ∃ c : ℂ, ψ = c • laughlinVector N (3 * (N - 1)) := by
  obtain ⟨c, hc⟩ := Chart.eq_scalar_laughlin_of_difference_cubes_dvd
    (Chart.statePolynomial ψ) (Chart.statePolynomial_degreeOf_le ψ)
    (Chart.difference_cube_dvd_statePolynomial_of_energy_zero (by omega) ψ hψ hE)
  refine ⟨c, (Chart.statePolynomial_injective _ _).eq_iff.mp ?_⟩
  simpa only [Chart.statePolynomial_smul, Chart.statePolynomial_laughlinVector] using hc

theorem laughlin_gap_of_sector_square_estimate {N : ℕ} (hN : 2 ≤ N)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hsq : ∀ x : SectorHilbert N (3 * (N - 1)),
      γ * energy (WithLp.ofLp x.val) ≤ ‖sectorHamiltonian N (3 * (N - 1)) x‖ ^ 2)
    (ψ : State N (3 * (N - 1))) (hψ : Antisymmetric ψ) :
    γ * distanceToLaughlinSq ψ ≤ energy ψ := by
  let x : SectorHilbert N (3 * (N - 1)) := ⟨toTensorHilbert ψ, hψ⟩
  obtain ⟨y, hy, hb⟩ := kernel_distance_of_square_lower_bound
    (sectorHamiltonian N (3 * (N - 1))) (sectorHamiltonian_positive _ _) γ
    (fun z => by rw [sectorHamiltonian_inner]; exact hsq z) x
  have hyE : energy (WithLp.ofLp y.val) = 0 := (sectorHamiltonian_eq_zero_iff y).mp hy
  obtain ⟨c, hc⟩ := energy_zero_imp_laughlin hN (WithLp.ofLp y.val) y.property hyE
  have hycoord (a) : y.val a = c * laughlinVector N (3 * (N - 1)) a :=
    congrFun hc a
  have hn : ‖x - y‖ ^ 2 = ∑ a, ‖ψ a - c * laughlinVector N (3 * (N - 1)) a‖ ^ 2 := by
    change ‖toTensorHilbert ψ - y.val‖ ^ 2 = _
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro a ha
    change ‖ψ a - y.val a‖ ^ 2 = _
    rw [hycoord a]
  rw [sectorHamiltonian_inner, hn] at hb
  exact (mul_le_mul_of_nonneg_left (distanceToLaughlinSq_le ψ c) hγ).trans hb

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpectralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral Bound. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators Topology
open Filter

lemma fallingRatio_eq_prod (Q z : ℕ) :
    fallingRatio Q z = ∏ k ∈ Finset.range z,
      ((Q - k : ℕ) : ℝ) / ((2 * Q - 2 - k : ℕ) : ℝ) := by
  simp [fallingRatio, Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]

lemma fallingRatio_nonneg (Q z : ℕ) : 0 ≤ fallingRatio Q z := by
  unfold fallingRatio
  positivity

theorem fallingRatio_le_two_thirds_pow {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    fallingRatio Q z ≤ (2 / 3 : ℝ) ^ z := by
  rw [fallingRatio_eq_prod]
  calc
    (∏ k ∈ Finset.range z, ((Q - k : ℕ) : ℝ) / ((2 * Q - 2 - k : ℕ) : ℝ)) ≤
        ∏ _k ∈ Finset.range z, (2 / 3 : ℝ) := by
      apply Finset.prod_le_prod
      · intro k hk
        positivity
      · intro k hk
        have hkz := Finset.mem_range.mp hk
        have hkQ : k ≤ Q := by omega
        have hkden : k ≤ 2 * Q - 2 := by omega
        have hden : 0 < ((2 * Q - 2 - k : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < 2 * Q - 2 - k by omega)
        rw [div_le_iff₀ hden]
        rw [Nat.cast_sub hkQ, Nat.cast_sub hkden, Nat.cast_sub (by omega : 2 ≤ 2 * Q)]
        push_cast
        have hQR : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
        have hkR : (0 : ℝ) ≤ k := by positivity
        linarith
    _ = (2 / 3 : ℝ) ^ z := by rw [Finset.prod_const, Finset.card_range]

lemma fallingFactor_tendsto (k : ℕ) :
    Tendsto (fun Q : ℕ => ((Q - k : ℕ) : ℝ) / ((2 * Q - 2 - k : ℕ) : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have ht : Tendsto (fun Q : ℕ => (1 - (k : ℝ) / Q) / (2 - ((k : ℝ) + 2) / Q))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.div_def, sub_zero] using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ) + 2)))
      (by norm_num : (2 : ℝ) - 0 ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k + 3)] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  rw [Nat.cast_sub (by omega : k ≤ Q), Nat.cast_sub (by omega : k ≤ 2 * Q - 2),
    Nat.cast_sub (by omega : 2 ≤ 2 * Q)]
  push_cast
  field_simp [hQ0]
  ring_nf

theorem fallingRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => fallingRatio Q z) atTop (𝓝 ((1 / 2 : ℝ) ^ z)) := by
  simpa only [fallingRatio_eq_prod, Finset.prod_const, Finset.card_range] using
    (tendsto_finsetProd (Finset.range z) (fun k _ => fallingFactor_tendsto k))

theorem threeBodyGramCoefficient_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => threeBodyGramCoefficient Q z)
      atTop (𝓝 ((3 * (z : ℝ) - 1) * (-1 / 2 : ℝ) ^ z)) := by
  have h := ((tendsto_const_nhds (x := (-1 : ℝ) ^ z)).mul (fallingRatio_tendsto z)).mul
    ((tendsto_const_nhds (x := 3 * (z : ℝ) - 1)).sub
      (tendsto_const_div_atTop_nhds_zero_nat ((z : ℝ) * ((z : ℝ) + 1))))
  convert h using 1
  · rfl
  · 
    rw [sub_zero, div_pow, div_pow]
    ring_nf

theorem threeBodyDimensionRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => threeBodyDimensionRatio Q z) atTop (𝓝 (3 / 2 : ℝ)) := by
  have ht : Tendsto (fun Q : ℕ => (3 - (1 + 2 * (z : ℝ)) / Q) / (2 - (1 : ℝ) / Q))
      atTop (𝓝 (3 / 2 : ℝ)) := by
    simpa only [Pi.div_def, sub_zero] using ((tendsto_const_nhds (x := (3 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1 + 2 * (z : ℝ)))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)))
      (by norm_num : (2 : ℝ) - 0 ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  unfold threeBodyDimensionRatio
  field_simp [hQ0]
  ring_nf

theorem threeBodyBracket_nonneg {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) (hz16 : 16 ≤ z) :
    0 ≤ 3 * (z : ℝ) - 1 - (z : ℝ) * ((z : ℝ) + 1) / Q := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hzQ : (z : ℝ) ≤ Q := by exact_mod_cast hz
  have hzR : (16 : ℝ) ≤ z := by exact_mod_cast hz16
  have hdiv : (z : ℝ) * ((z : ℝ) + 1) / Q ≤ (z : ℝ) + 1 := by
    rw [div_le_iff₀ hQpos]
    exact mul_le_mul_of_nonneg_right hzQ (by positivity) |>.trans_eq (mul_comm _ _)
  linarith

theorem threeBodyGramCoefficient_abs_le {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q)
    (hz16 : 16 ≤ z) :
    |threeBodyGramCoefficient Q z| ≤ (2 / 3 : ℝ) ^ z * (3 * (z : ℝ)) := by
  rw [threeBodyGramCoefficient, abs_mul, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (fallingRatio_nonneg Q z),
    abs_of_nonneg (threeBodyBracket_nonneg hQ hz hz16)]
  apply mul_le_mul (fallingRatio_le_two_thirds_pow hQ hz)
  · have hn : (0 : ℝ) ≤ (z : ℝ) * ((z : ℝ) + 1) / Q := by positivity
    linarith
  · exact threeBodyBracket_nonneg hQ hz hz16
  · positivity

lemma threeBodyDimensionRatio_nonneg {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    0 ≤ threeBodyDimensionRatio Q z := by
  have hQR : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hzR : (z : ℝ) ≤ Q := by exact_mod_cast hz
  exact div_nonneg (by linarith) (by linarith)

lemma threeBodyDimensionRatio_le_two {Q z : ℕ} (hQ : 4 ≤ Q) :
    threeBodyDimensionRatio Q z ≤ 2 := by
  have hQR : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  unfold threeBodyDimensionRatio
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Q - 1)]
  have hzR : (0 : ℝ) ≤ z := by positivity
  linarith

lemma threeBodyTailTerm_nonneg {Q : ℕ} (hQ : 4 ≤ Q) (z : ℕ) :
    0 ≤ threeBodyTailTerm Q z := by
  unfold threeBodyTailTerm
  split_ifs with hz
  · exact mul_nonneg (mul_nonneg (threeBodyDimensionRatio_nonneg hQ hz.2.2)
      (abs_nonneg _)) (by positivity)
  · rfl

theorem threeBodyTailTerm_norm_le {Q : ℕ} (hQ : 4 ≤ Q) (z : ℕ) :
    ‖threeBodyTailTerm Q z‖ ≤ 6 * (z : ℝ) * ((z : ℝ) + 1) * (2 / 3 : ℝ) ^ z := by
  rw [Real.norm_of_nonneg (threeBodyTailTerm_nonneg hQ z)]
  unfold threeBodyTailTerm
  split_ifs with hz
  · calc
      _ ≤ 2 * ((2 / 3 : ℝ) ^ z * (3 * (z : ℝ))) * ((z : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (threeBodyDimensionRatio_le_two hQ)
          (threeBodyGramCoefficient_abs_le hQ hz.2.2 (by omega)) (abs_nonneg _)
          (by norm_num)
      _ = _ := by ring
  · positivity

lemma summable_threeBodyTail_majorant :
    Summable (fun z : ℕ => 6 * (z : ℝ) * ((z : ℝ) + 1) * (2 / 3 : ℝ) ^ z) := by
  have hs2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  exact ((hs2.add hs1).mul_left (6 : ℝ)).congr (fun z => by ring)

theorem threeBodyTailTerm_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => threeBodyTailTerm Q z) atTop (𝓝 (threeBodyTailStar z)) := by
  by_cases hz : 17 ≤ z ∧ Odd z
  · have ha := (threeBodyGramCoefficient_tendsto z).abs
    have hzR : (17 : ℝ) ≤ z := by exact_mod_cast hz.1
    have he : |(3 * (z : ℝ) - 1) * (-1 / 2 : ℝ) ^ z| =
        (3 * (z : ℝ) - 1) * (1 / 2 : ℝ) ^ z := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 * (z : ℝ) - 1), abs_pow]
      norm_num
    rw [he] at ha
    have hh := ((threeBodyDimensionRatio_tendsto z).mul ha).mul_const ((z : ℝ) + 1)
    have hlim : (3 / 2 : ℝ) * ((3 * (z : ℝ) - 1) * (1 / 2 : ℝ) ^ z) * ((z : ℝ) + 1) =
        threeBodyTailStar z := by
      simp only [threeBodyTailStar, ite_eq_left hz]
      ring
    rw [hlim] at hh
    apply hh.congr' 
    filter_upwards [eventually_ge_atTop z] with Q hQ
    simp [threeBodyTailTerm, hz.1, hz.2, hQ]
  · have he : ∀ Q, threeBodyTailTerm Q z = 0 := by
      intro Q
      simp only [threeBodyTailTerm]
      rw [ite_eq_right (by tauto)]
    simpa only [he, threeBodyTailStar, ite_eq_right hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

private lemma hasSum_square_quarter :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 4 : ℝ) ^ n) (20 / 27 : ℝ) := by
  have h0 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  convert ((h2.mul_left (2 : ℝ)).sub (h1.mul_left (3 : ℝ))).sub (h0.mul_left (2 : ℝ)) using 1 <;> try rfl
  · ext n
    rw [Nat.cast_choose_two]
    push_cast
    ring
  · norm_num

theorem hasSum_threeBodyTailStar_progression :
    HasSum (fun m : ℕ => threeBodyTailStar (17 + 2 * m)) (61 / 4096 : ℝ) := by
  have h0 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h2 := hasSum_square_quarter
  convert (((h0.mul_left (900 : ℝ)).add (h1.mul_left (208 : ℝ))).add
    (h2.mul_left (12 : ℝ))).mul_left (3 / 262144 : ℝ) using 1 <;> try rfl
  · ext m
    have hm : 17 ≤ 17 + 2 * m ∧ Odd (17 + 2 * m) := by
      constructor
      · omega
      · rw [Nat.odd_iff]; omega
    simp only [threeBodyTailStar, ite_eq_left hm, pow_add, pow_mul]
    push_cast
    norm_num
    ring
  · norm_num

theorem hasSum_threeBodyTailStar : HasSum threeBodyTailStar (61 / 4096 : ℝ) := by
  have hinj : Function.Injective (fun m : ℕ => 17 + 2 * m) := by
    intro a b hab
    dsimp at hab
    omega
  have hout : ∀ z, z ∉ Set.range (fun m : ℕ => 17 + 2 * m) → threeBodyTailStar z = 0 := by
    intro z hz
    have hbad : ¬ (17 ≤ z ∧ Odd z) := by
      rintro ⟨hz17, hzodd⟩
      have hp := Nat.odd_iff.mp hzodd
      apply hz
      exact ⟨(z - 17) / 2, by dsimp; omega⟩
    exact ite_eq_right hbad
  exact (hinj.hasSum_iff hout).mp hasSum_threeBodyTailStar_progression

theorem threeBodyTail_tendsto :
    Tendsto threeBodyTail atTop (𝓝 (61 / 4096 : ℝ)) := by
  have ht := tendsto_tsum_of_dominated_convergence summable_threeBodyTail_majorant
    threeBodyTailTerm_tendsto
    (show ∀ᶠ Q in atTop, ∀ z, ‖threeBodyTailTerm Q z‖ ≤
        6 * (z : ℝ) * ((z : ℝ) + 1) * (2 / 3 : ℝ) ^ z by
      filter_upwards [eventually_ge_atTop 4] with Q hQ z
      exact threeBodyTailTerm_norm_le hQ z)
  rw [hasSum_threeBodyTailStar.tsum_eq] at ht
  have he : threeBodyTail = (fun Q => ∑' z, threeBodyTailTerm Q z) := by
    funext Q
    unfold threeBodyTail
    symm
    apply tsum_eq_sum
    intro z hz
    have hzQ : ¬ z ≤ Q := by
      simp only [Finset.mem_range] at hz
      omega
    simp [threeBodyTailTerm, hzQ]
  rw [he]
  exact ht

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairEnergy
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.fullContraction_add _root_.OAI.LaughlinGap.Occupation.fullContraction_single _root_.OAI.LaughlinGap.Occupation.fullContraction_smul _root_.OAI.LaughlinGap.Occupation.fullContraction_zero _root_.OAI.LaughlinGap.Occupation.inner_vacuum_left _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.Occupation.word_cons _root_.OAI.LaughlinGap.Occupation.word_nil _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Energy. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma annihilation_eq_zero_of_degree_zero {n : ℕ} {x : Hilbert n}
    (hx : Homogeneous 0 x) (j : Fin n) : annihilation j x = 0 := by
  ext A
  by_cases hj : j ∈ A
  · simp [transition_apply, hj]
  · simp only [transition_apply, hj, decide_false, ite_true,
      flip_of_not_mem hj]
    rw [hx (insert j A) (by simp), mul_zero]
    rfl

lemma word_eq_zero_of_degree_lt {n k : ℕ} (js : List (Fin n)) {x : Hilbert n}
    (hx : Homogeneous k x) (hk : k < js.length) : word js x = 0 := by
  induction js generalizing k x with
  | nil => simp at hk
  | cons j js ih =>
    cases k with
    | zero => simp only [word, LinearMap.comp_apply, annihilation_eq_zero_of_degree_zero hx, map_zero]
    | succ k =>
      exact ih (annihilation_homogeneous hx j) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk)

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NormalOrder
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.coordinatesFromTensor_apply _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.RealOccupation.complexify_creation _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index _root_.OAI.LaughlinGap.Spin.spinTripleWedge_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Order. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma homogeneous_smul {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) (c : ℂ) :
    Homogeneous k (c • x) := by
  intro A hA
  simp [hx A hA]

lemma homogeneous_sum {n k : ℕ} {ι : Type*} (s : Finset ι) (x : ι → Hilbert n)
    (hx : ∀ i ∈ s, Homogeneous k (x i)) : Homogeneous k (∑ i ∈ s, x i) := by
  intro A hA
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i hi => hx i hi A hA)

lemma creation_homogeneous {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x)
    (i : Fin n) : Homogeneous (k+1) (creation i x) := by
  intro A hA
  by_cases hi : i ∈ A
  · have hc : (A.erase i).card ≠ k := by
      have hh := Finset.card_erase_add_one hi
      omega
    simp [transition_apply, hi, hx _ hc]
  · simp [transition_apply, hi]

lemma pairContraction_adjoint_homogeneous {n k : ℕ} (v : PairLabel n → ℂ)
    {x : Hilbert n} (hx : Homogeneous k x) :
    Homogeneous (k+2) ((pairContraction v).adjoint x) := by
  simp only [pairContraction, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply]
  apply homogeneous_sum
  intro a _
  apply homogeneous_smul
  simpa only [basicPair, adjoint_mul, annihilation_adjoint, Module.End.mul_apply] using
    creation_homogeneous (creation_homogeneous hx a.val.2) a.val.1

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma pairContraction_eq_pairAnnihilator {n : ℕ} (v : Fin n → Fin n → ℂ) :
    pairContraction (fun a => v a.val.1 a.val.2) = pairAnnihilator v := by
  classical
  simp only [pairContraction, basicPair]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
    (by simp) (fun a => star (v a.1 a.2) • (annihilation a.2 * annihilation a.1))]
  simp only [Finset.sum_filter, Fintype.sum_prod_type, pairAnnihilator]

lemma sectorInclusion_readout {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) :
    sectorInclusion n k (sectorReadout n k x) = x := by
  ext A
  by_cases hA : A.card = k
  · simp [sectorInclusion_apply, hA]
  · simp [sectorInclusion_apply, hA, hx A hA]

lemma pairContraction_homogeneous {n k : ℕ} (v : PairLabel n → ℂ)
    {x : Hilbert n} (hx : Homogeneous (k+2) x) : Homogeneous k (pairContraction v x) := by
  simp only [pairContraction, LinearMap.sum_apply, LinearMap.smul_apply]
  apply homogeneous_sum
  intro a _
  apply homogeneous_smul
  exact annihilation_homogeneous (annihilation_homogeneous hx a.val.1) a.val.2

lemma pairHamiltonian_homogeneous {n k : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) {x : Hilbert n} (hx : Homogeneous (k+2) x) :
    Homogeneous (k+2) (pairHamiltonian v x) := by
  simp only [pairHamiltonian, LinearMap.sum_apply, Module.End.mul_apply]
  exact homogeneous_sum _ _ (fun p _ => pairContraction_adjoint_homogeneous _
    (pairContraction_homogeneous _ hx))

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma sphericalExteriorPairCoefficient_eq_tensor (Q p : ℕ) (i j : Fin (Q+1)) :
    sphericalExteriorPairCoefficient Q p i.val j.val = Real.sqrt 2 * pairCoefficient Q p i j := by
  unfold sphericalExteriorPairCoefficient pairCoefficient
  split_ifs
  · have h : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
  · simp

lemma physicalPair_contraction (Q : ℕ) (p : Fin (2*Q-1)) :
    pairContraction (physicalPairForms Q p) = localPair (Q+1) Q p.val := by
  exact pairContraction_eq_pairAnnihilator (fun x y : Fin (Q+1) =>
    (sphericalExteriorPairCoefficient Q p.val x.val y.val : ℂ))

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma pairContraction_eq_zero_of_degree_lt {n k : ℕ} (v : PairLabel n → ℂ)
    {x : Hilbert n} (hx : Homogeneous k x) (hk : k < 2) : pairContraction v x = 0 := by
  simp only [pairContraction, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro a _
  have he : basicPair a = word [a.val.1,a.val.2] := by
    simp only [basicPair, word_cons, word_nil, one_mul]
  rw [he, word_eq_zero_of_degree_lt _ hx (by simpa using hk), smul_zero]

lemma pairHamiltonian_preserves_degree {n k : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) {x : Hilbert n} (hx : Homogeneous k x) :
    Homogeneous k (pairHamiltonian v x) := by
  by_cases hk : 2 ≤ k
  · obtain ⟨l, rfl⟩ : ∃ l, k = l+2 := ⟨k-2, by omega⟩
    exact pairHamiltonian_homogeneous v hx
  · have he : pairHamiltonian v x = 0 := by
      simp only [pairHamiltonian, LinearMap.sum_apply, Module.End.mul_apply,
        pairContraction_eq_zero_of_degree_lt _ hx (by omega), map_zero, Finset.sum_const_zero]
    rw [he]
    exact fun _ _ => rfl

theorem physicalOccupationHamiltonian_positive (Q : ℕ) :
    (physicalOccupationHamiltonian Q).IsPositive := by
  apply LinearMap.isPositive_sum
  intro p _
  exact LinearMap.isPositive_adjoint_comp_self _

theorem physicalOccupationHamiltonian_inner (Q : ℕ) (x : Hilbert (Q+1)) :
    (inner ℂ x (physicalOccupationHamiltonian Q x)).re =
      localPairEnergy (Q+1) (2*Q-1) Q x := by
  simp only [physicalOccupationHamiltonian, pairHamiltonian, LinearMap.sum_apply,
    inner_sum, Complex.re_sum, localPairEnergy]
  apply Finset.sum_congr rfl
  intro p _
  change (inner ℂ x ((pairContraction (physicalPairForms Q p)).adjoint
    (pairContraction (physicalPairForms Q p) x))).re = _
  rw [LinearMap.adjoint_inner_right, physicalPair_contraction]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Creation
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index _root_.OAI.LaughlinGap.Spin.spinTripleWedge_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Creation. -/

noncomputable section


namespace LaughlinGap
open scoped InnerProduct

lemma unitary_conj_eq_of_quadraticForm {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (A : Module.End ℂ E) (B : Module.End ℂ F)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (h : ∀ x, (inner ℂ (U x) (B (U x))).re = (inner ℂ x (A x)).re) :
    U.symm.toLinearMap ∘ₗ B ∘ₗ U.toLinearMap = A := by
  apply (ext_inner_map _ _).mp
  intro x
  change inner ℂ (U.symm (B (U x))) x = inner ℂ (A x) x
  have hi := U.inner_map_map (U.symm (B (U x))) x
  simp only [LinearIsometryEquiv.apply_symm_apply] at hi
  rw [← hi, ← hB.coe_re_inner_apply_self, ← hA.coe_re_inner_apply_self]
  congr 1
  rw [inner_re_symm, inner_re_symm (𝕜 := ℂ) (A x) x]
  exact h x

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma sum_symmetric_triangle {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin n → Fin n → A) (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) := by
  classical
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  conv_lhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]

lemma orderedPair_contraction (Q p : ℕ) :
    (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), (pairCoefficient Q p i j : ℂ) •
      (annihilation j * annihilation i)) =
    (Real.sqrt 2 : ℂ) • localPair (Q+1) Q p := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  let T : Module.End ℂ (Hilbert (Q+1)) := ∑ i, ∑ j, if i < j then
    (pairCoefficient Q p i j : ℂ) • (annihilation j * annihilation i) else 0
  have he : localPair (Q+1) Q p = (Real.sqrt 2 : ℂ) • T := by
    simp only [localPair, pairAnnihilator, sphericalExteriorPairCoefficient_eq_tensor,
      Complex.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_mul, mul_smul, T,
      Finset.smul_sum, smul_ite, smul_zero]
  rw [sum_symmetric_triangle, he, smul_smul, hs]
  · change T + T = (2:ℂ) • T
    module
  · intro i j
    rw [pairCoefficient_swap Q p i j, annihilation_anticommute i j]
    simp
  · intro i
    simp [pairCoefficient]

lemma update_cons_cons {N Q : ℕ} (a : Configuration N Q) (u v x y : Fin (Q+1)) :
    Function.update (Function.update (Fin.cons u (Fin.cons v a) : Configuration (N+2) Q) (0 : Fin (N+2)) x)
      (1 : Fin (N+2)) y = (Fin.cons x (Fin.cons y a) : Configuration (N+2) Q) := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · simp
  · simp
  · have hk : k.succ.succ ≠ (1 : Fin (N+2)) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_one] at hv
      omega
    simp [Function.update_of_ne hk]

lemma readout_pairAmplitude_head {N Q : ℕ} (x : Hilbert (Q+1)) (p : ℕ)
    (a : Configuration N Q) :
    pairAmplitude (WithLp.ofLp (normalizedReadout (Q+1) (N+2) x))
      0 1 p (Fin.cons 0 (Fin.cons 0 a)) =
      (((Real.sqrt ((N+2).factorial : ℝ))⁻¹ : ℂ) * (Real.sqrt 2 : ℂ)) *
        rawReadout (Q+1) N (localPair (Q+1) Q p x) a := by
  have he := congrArg (fun T : Module.End ℂ (Hilbert (Q+1)) =>
    rawReadout (Q+1) N (T x) a) (orderedPair_contraction Q p)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] at he
  simp only [pairAmplitude, update_cons_cons, normalizedReadout_apply,
    List.ofFn_cons, word_cons, Module.End.mul_apply]
  simp only [rawReadout_apply, Module.End.mul_apply] at he
  change (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), (pairCoefficient Q p i j : ℂ) *
      (((Real.sqrt ((N+2).factorial : ℝ))⁻¹ : ℂ) *
        word (List.ofFn a) (annihilation j (annihilation i x)) ∅)) = _
  calc
    _ = (((Real.sqrt ((N+2).factorial : ℝ))⁻¹ : ℂ)) *
        (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), (pairCoefficient Q p i j : ℂ) *
          word (List.ofFn a) (annihilation j (annihilation i x)) ∅) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [he]; exact (mul_assoc _ _ _).symm

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators InnerProduct

lemma sum_head_anchored {N Q : ℕ} (f : Configuration (N+2) Q → ℝ) :
    (∑ a, if a 0 = 0 ∧ a 1 = 0 then f a else 0) =
      ∑ a : Configuration N Q, f (Fin.cons 0 (Fin.cons 0 a)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (N+2) => Fin (Q+1))).sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ x : Fin (Q+1), ∑ a : Configuration (N+1) Q,
    if x = 0 ∧ a 0 = 0 then f (Fin.cons x a) else 0) = _
  simp only [ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Fin (Q+1))).sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ y : Fin (Q+1), ∑ a : Configuration N Q,
    if y = 0 then f (Fin.cons 0 (Fin.cons y a)) else 0) = _
  simp_rw [Finset.sum_ite_irrel]
  simp

lemma pairAmplitude_perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) (i j : Fin N) (p : ℕ) (a : Configuration N Q) :
    pairAmplitude ψ i j p (a ∘ σ) =
      Equiv.Perm.sign σ • pairAmplitude ψ (σ i) (σ j) p a := by
  have hu (x y : Fin (Q+1)) : Function.update (Function.update (a ∘ σ) i x) j y =
      Function.update (Function.update a (σ i) x) (σ j) y ∘ σ := by
    simp only [Function.update_comp_equiv, Equiv.symm_apply_apply]
  simp only [pairAmplitude, hu, Antisymmetric.perm hψ, Finset.smul_sum, mul_smul_comm]

lemma pairEnergyAt_perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) (i j : Fin N) (p : ℕ) :
    pairEnergyAt ψ i j p = pairEnergyAt ψ (σ i) (σ j) p := by
  let e : Configuration N Q ≃ Configuration N Q :=
    ⟨fun a => a ∘ σ, fun a => a ∘ σ.symm,
      by intro a; ext k; simp, by intro a; ext k; simp⟩
  unfold pairEnergyAt
  rw [← e.sum_comp]
  change (∑ a, if a (σ i) = 0 ∧ a (σ j) = 0 then
    ‖pairAmplitude ψ i j p (a ∘ σ)‖ ^ 2 else 0) = _
  simp only [pairAmplitude_perm hψ, norm_units_zsmul]

lemma exists_perm_head_pair {N : ℕ} (i j : Fin (N+2)) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (N+2)), σ 0 = i ∧ σ 1 = j := by
  let τ : Equiv.Perm (Fin (N+2)) := Equiv.swap 0 i
  have hτ : τ 0 = i := Equiv.swap_apply_left _ _
  have h10 : (1 : Fin (N+2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_one, Fin.val_zero] at hv
    omega
  have hi : i ≠ τ 1 := by rw [← hτ]; exact fun h => h10 (τ.injective h).symm
  refine ⟨Equiv.swap (τ 1) j * τ, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, hτ]
    exact Equiv.swap_apply_of_ne_of_ne hi hij
  · simp

lemma pairEnergyAt_eq_head {N Q : ℕ} {ψ : State (N+2) Q} (hψ : Antisymmetric ψ)
    (i j : Fin (N+2)) (hij : i ≠ j) (p : ℕ) :
    pairEnergyAt ψ i j p = pairEnergyAt ψ 0 1 p := by
  obtain ⟨σ,h0,h1⟩ := exists_perm_head_pair i j hij
  simpa only [h0,h1] using (pairEnergyAt_perm hψ σ 0 1 p).symm

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

theorem readout_pairEnergyAt_head {N Q : ℕ} {x : Hilbert (Q+1)}
    (hx : Homogeneous (N+2) x) (p : Fin (2*Q-1)) :
    pairEnergyAt (WithLp.ofLp (normalizedReadout (Q+1) (N+2) x)) 0 1 p.val =
      (2 * (N.factorial : ℝ) / ((N+2).factorial : ℝ)) *
        ‖localPair (Q+1) Q p.val x‖ ^ 2 := by
  have hs : 0 < Real.sqrt ((N+2).factorial : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos (N+2))
  have hh : Homogeneous N (localPair (Q+1) Q p.val x) := by
    rw [← physicalPair_contraction]
    exact pairContraction_homogeneous _ hx
  rw [pairEnergyAt, sum_head_anchored]
  simp only [readout_pairAmplitude_head, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, abs_of_nonneg (Real.sqrt_nonneg 2),
    mul_pow, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ ((N+2).factorial : ℝ)),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), ← Finset.mul_sum,
    ← EuclideanSpace.norm_sq_eq, rawReadout_norm_sq hh]
  ring

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators InnerProduct

lemma sum_increasing_positions (N : ℕ) (c : ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, if i < j then c else 0) =
      (N.choose 2 : ℝ) * c := by
  rw [← Fintype.sum_prod_type (f := fun ij : Fin N × Fin N => if ij.1 < ij.2 then c else 0),
    ← Finset.sum_filter, Finset.sum_const,
    Fintype.card_product_filter_lt, Fintype.card_fin, nsmul_eq_mul]

lemma energy_eq_pairEnergyAt_head {N Q : ℕ} {ψ : State (N+2) Q}
    (hψ : Antisymmetric ψ) :
    energy ψ = ((N+2).choose 2 : ℝ) *
      ∑ p : Fin (2*Q-1), pairEnergyAt ψ 0 1 p.val := by
  change (∑ i, ∑ j, if i < j then
    ∑ p ∈ Finset.range (2*Q-1), pairEnergyAt ψ i j p else 0) = _
  have he (i j : Fin (N+2)) :
      (if i < j then ∑ p ∈ Finset.range (2*Q-1), pairEnergyAt ψ i j p else 0) =
      if i < j then ∑ p ∈ Finset.range (2*Q-1), pairEnergyAt ψ 0 1 p else 0 := by
    split_ifs with hij
    · simp_rw [pairEnergyAt_eq_head hψ i j (ne_of_lt hij)]
    · rfl
  simp_rw [he]
  rw [sum_increasing_positions, Fin.sum_univ_eq_sum_range]

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

theorem readout_energy {N Q : ℕ} {x : Hilbert (Q+1)} (hx : Homogeneous (N+2) x) :
    energy (WithLp.ofLp (normalizedReadout (Q+1) (N+2) x)) =
      localPairEnergy (Q+1) (2*Q-1) Q x := by
  rw [energy_eq_pairEnergyAt_head (normalizedReadout_antisymmetric x)]
  simp_rw [readout_pairEnergyAt_head hx]
  rw [← Finset.mul_sum, ← mul_assoc]
  have he : ((N+2).choose 2 : ℝ) * 2 * (N.factorial : ℝ) = ((N+2).factorial : ℝ) := by
    have hn := Nat.choose_mul_factorial_mul_factorial (n := N+2) (k := 2) (by omega)
    norm_num only [Nat.add_sub_cancel, Nat.factorial_two] at hn
    exact_mod_cast hn
  have hpos : ((N+2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N+2)
  rw [← mul_div_assoc, ← mul_assoc, he, div_self hpos, one_mul]
  rfl

lemma exteriorHamiltonian_positive (N Q : ℕ) : (exteriorHamiltonian N Q).IsPositive := by
  rw [exteriorHamiltonian, ← sectorInclusion_adjoint]
  exact (physicalOccupationHamiltonian_positive Q).adjoint_conj _

lemma exteriorHamiltonian_inner (N Q : ℕ) (x : ExteriorCoordinates (Q+1) N) :
    (inner ℂ x (exteriorHamiltonian N Q x)).re =
      localPairEnergy (Q+1) (2*Q-1) Q (sectorInclusion (Q+1) N x) := by
  change (inner ℂ x (sectorReadout (Q+1) N
    (physicalOccupationHamiltonian Q (sectorInclusion (Q+1) N x)))).re = _
  rw [← sectorInclusion_adjoint, LinearMap.adjoint_inner_right,
    physicalOccupationHamiltonian_inner]

lemma exteriorHamiltonian_inclusion (N Q : ℕ) (x : ExteriorCoordinates (Q+1) N) :
    sectorInclusion (Q+1) N (exteriorHamiltonian N Q x) =
      physicalOccupationHamiltonian Q (sectorInclusion (Q+1) N x) := by
  apply sectorInclusion_readout
  exact pairHamiltonian_preserves_degree _ (sectorInclusion_homogeneous x)

theorem tensor_exteriorHamiltonian (N Q : ℕ) :
    (exteriorTensorIsometry Q (N+2)).symm.toLinearMap ∘ₗ sectorHamiltonian (N+2) Q ∘ₗ
      (exteriorTensorIsometry Q (N+2)).toLinearMap = exteriorHamiltonian (N+2) Q := by
  apply unitary_conj_eq_of_quadraticForm _ _ _
    (exteriorHamiltonian_positive (N+2) Q).isSymmetric
    (sectorHamiltonian_positive (N+2) Q).isSymmetric
  intro x
  rw [sectorHamiltonian_inner, exteriorHamiltonian_inner]
  exact readout_energy (sectorInclusion_homogeneous x)

lemma exteriorTensorIsometry_intertwines (N Q : ℕ) (x : ExteriorCoordinates (Q+1) (N+2)) :
    sectorHamiltonian (N+2) Q (exteriorTensorIsometry Q (N+2) x) =
      exteriorTensorIsometry Q (N+2) (exteriorHamiltonian (N+2) Q x) := by
  have he := congrArg (fun T : Module.End ℂ (ExteriorCoordinates (Q+1) (N+2)) =>
    exteriorTensorIsometry Q (N+2) (T x)) (tensor_exteriorHamiltonian N Q)
  simpa using he

lemma exteriorTensorIsometry_hamiltonian_norm_sq (N Q : ℕ)
    (x : ExteriorCoordinates (Q+1) (N+2)) :
    ‖sectorHamiltonian (N+2) Q (exteriorTensorIsometry Q (N+2) x)‖ ^ 2 =
      ‖physicalOccupationHamiltonian Q (sectorInclusion (Q+1) (N+2) x)‖ ^ 2 := by
  rw [exteriorTensorIsometry_intertwines, LinearIsometryEquiv.norm_map,
    ← exteriorHamiltonian_inclusion, sectorInclusion_norm_sq]

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

theorem sector_square_of_occupation_square {Q : ℕ} (γ : ℝ)
    (h : ∀ x : Hilbert (Q+1), γ * localPairEnergy (Q+1) (2*Q-1) Q x ≤
      ‖physicalOccupationHamiltonian Q x‖ ^ 2) (N : ℕ) (x : SectorHilbert (N+2) Q) :
    γ * energy (WithLp.ofLp x.val) ≤ ‖sectorHamiltonian (N+2) Q x‖ ^ 2 := by
  let y := (exteriorTensorIsometry Q (N+2)).symm x
  have hy : exteriorTensorIsometry Q (N+2) y = x :=
    (exteriorTensorIsometry Q (N+2)).apply_symm_apply x
  rw [← hy, exteriorTensorIsometry_hamiltonian_norm_sq]
  change γ * energy (WithLp.ofLp (normalizedReadout (Q+1) (N+2)
    (sectorInclusion (Q+1) (N+2) y))) ≤ _
  rw [readout_energy (sectorInclusion_homogeneous y)]
  exact h _

theorem mainTarget_of_uniform_occupation_square_estimate
    (h : ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ x : Hilbert (Q+1),
      (1/25 : ℝ) * localPairEnergy (Q+1) (2*Q-1) Q x ≤
        ‖physicalOccupationHamiltonian Q x‖ ^ 2) : MainTarget := by
  obtain ⟨Q₀,hQ₀⟩ := h
  refine ⟨Q₀+2, by omega, ?_⟩
  intro N hN ψ hψ
  have hN2 : 2 ≤ N := by omega
  obtain ⟨n,rfl⟩ : ∃ n, N = n+2 := ⟨N-2, by omega⟩
  exact laughlin_gap_of_sector_square_estimate hN2 (1/25) (by norm_num)
    (sector_square_of_occupation_square _ (hQ₀ _ (by omega)) n) ψ hψ

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

omit [DecidableEq ι] in
lemma complexify_combination [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (a : ι → ℝ) :
    complexify (combination B a) = ∑ i, (a i : ℂ) • complexify (B i) := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  exact_mod_cast (rfl : a i • complexify (B i) = a i • complexify (B i))

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

end LadderMap

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
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index _root_.OAI.LaughlinGap.Spin.spinTripleWedge_physical_index
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

@[simp] lemma complexify_physicalPair (Q p : ℕ) :
    complexify (physicalPair Q p) = Occupation.localPair (Q+1) Q p := by
  rw [physicalPair, map_smul, complexify_combination]
  simp only [productFamily, map_mul, complexify_annihilation, Fintype.sum_prod_type,
    physicalPairTensor, Occupation.orderedPair_contraction]
  have he : (1/Real.sqrt 2 : ℝ) • ((Real.sqrt 2 : ℂ) • Occupation.localPair (Q+1) Q p) =
      ((1/Real.sqrt 2)*Real.sqrt 2 : ℝ) • Occupation.localPair (Q+1) Q p := by
    rw [mul_smul]; rfl
  rw [he, one_div_mul_cancel (by positivity : Real.sqrt 2 ≠ 0), one_smul]

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

@[simp] lemma complexify_physicalHamiltonian (Q : ℕ) :
    complexify (physicalHamiltonian Q) = Occupation.physicalOccupationHamiltonian Q := by
  simp only [physicalHamiltonian, map_sum, map_mul, complexify_transpose,
    complexify_physicalPair, Occupation.physicalOccupationHamiltonian, Occupation.pairHamiltonian,
    Occupation.physicalPair_contraction]

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

theorem physicalTriple_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (tensorSpin (2*Q-2) Q)) (physicalTriple Q) :=
  (physicalPair_covariant hQ).product (annihilation_covariant _)

end LaughlinGap.RealOccupation

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

lemma annihilation_square_le {n : ℕ} (j : Fin n) (B : FockMatrix n) :
    (B.transpose * B - (annihilation j * B).transpose * (annihilation j * B)).PosSemidef := by
  apply square_diff_positive
  intro x
  simpa only [map_mul, complexify_annihilation, Module.End.mul_apply] using
    Occupation.transition_norm_le j false (complexify B x)

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
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single _root_.OAI.LaughlinGap.Spin.highestCoefficient_zero_zero
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

lemma combination_one_bessel {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : ι → ℝ) (ha : dotProduct a a = 1) (B : ι → Matrix κ κ ℝ) :
    ((∑ i, (B i).transpose * B i) - (combination B a).transpose * combination B a).PosSemidef := by
  let S : Matrix Unit ι ℝ := fun _ => a
  have hS : S * S.transpose = 1 := by
    ext i j
    change (∑ k, a k * a k) = 1
    exact ha
  simpa [S] using combination_bessel S hS B

omit [Fintype ι] [DecidableEq ι] in
lemma highestCombination_range [Fintype ι] [DecidableEq ι] {n m z : ℕ} (hz : z ≤ min n m)
    (B : (Fin (n+1) × Fin (m+1)) → Matrix ι ι ℝ) :
    combination B (highestTensor n m z) =
      ∑ p : Fin (z+1), highestCoefficient n m z p.val •
        B (⟨p.val, by omega⟩,⟨z-p.val,by omega⟩) := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk]
  let f : Fin (z+1) → Fin (n+1) × Fin (m+1) :=
    fun p => (⟨p.val,by omega⟩, ⟨z-p.val,by omega⟩)
  symm
  apply Finset.sum_bij_ne_zero (fun p _ _ => f p)
  · intro p hp hn; exact Finset.mem_univ _
  · intro p hp hn q hq hnq he
    exact Fin.ext (congrArg (fun a : Fin (n+1) × Fin (m+1) => a.1.val) he)
  · intro a ha hn
    have he : a.1.val+a.2.val=z := by
      by_contra he
      simp [highestTensor, he] at hn
    let p : Fin (z+1) := ⟨a.1.val,by omega⟩
    have hf : f p = a := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        dsimp [f,p]
        omega
    refine ⟨p,Finset.mem_univ _,?_,hf⟩
    simpa only [← hf, highestTensor, show (f p).1.val+(f p).2.val=z by dsimp [f]; omega,
      ite_true] using hn
  · intro p hp hn
    simp only [highestTensor, show (f p).1.val+(f p).2.val=z by dsimp [f]; omega, ite_true]
    rfl

lemma threeSpinLift_positive {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (threeSpinLift hQ hz).PosSemidef := by
  apply lift_positive
  rw [tensorProjection_eq]
  apply Matrix.posSemidef_sum
  intro l hl
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    (coupledTensor (2*Q-2) Q z l.val)

lemma threeSpinLift_average_highest {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    average (rotationCommutant (fockLowering Q))
      ((combination (physicalTriple Q) (highestTensor (2*Q-2) Q z)).transpose *
        combination (physicalTriple Q) (highestTensor (2*Q-2) Q z)) =
      (1/((2*Q-2)+Q-2*z+1 : ℕ) : ℝ) • threeSpinLift hQ hz := by
  let hz' : z ≤ min (2*Q-2) Q := by omega
  have he : (coupledEmbedding hz').toLinearMap (Pi.single (0 : Fin ((2*Q-2)+Q-2*z+1)) 1) =
      highestTensor (2*Q-2) Q z := by
    rw [coupledEmbedding_apply]
    simp [Pi.single_apply, ite_smul]
  rw [← lift_rankOne, (physicalTriple_covariant hQ).average_lift, ← he,
    equal_copy_average]
  simp only [ite_true, map_smul]
  simp only [threeSpinLift, tensorProjection, LadderMap.comp, LadderMap.transpose,
    LinearMap.toMatrix'_comp, toMatrix_transposeMap, LadderMap.matrix]

lemma average_mono (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A B : Matrix ι ι ℝ} (h : A ≤ B) : average S A ≤ average S B := by
  have hh := average_positive S (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))
  rw [map_sub] at hh
  exact sub_nonneg.mp hh.nonneg

lemma threeSpinLift_le {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeSpinLift hQ hz ≤
      (threeBodyDimensionRatio Q z * (z+1 : ℕ)) • physicalHamiltonian Q := by
  let hz' : z ≤ min (2*Q-2) Q := by omega
  let a : Fin (z+1) → ℝ := fun p => highestCoefficient (2*Q-2) Q z p.val
  let B : Fin (z+1) → FockMatrix (Q+1) := fun p =>
    annihilation ⟨z-p.val,by omega⟩ * physicalPair Q p.val
  have hn : dotProduct a a = 1 := by
    simp only [a, dotProduct, ← sq]
    rw [Fin.sum_univ_eq_sum_range (fun p => highestCoefficient (2*Q-2) Q z p ^ 2)]
    exact highestCoefficient_sum_sq hz' 
  have hc : combination B a = combination (physicalTriple Q) (highestTensor (2*Q-2) Q z) := by
    rw [highestCombination_range hz']
    rfl
  have hb := (combination_one_bessel a hn B).nonneg
  have hbs : (combination B a).transpose * combination B a ≤
      ∑ p : Fin (z+1), (physicalPair Q p.val).transpose * physicalPair Q p.val := by
    apply (sub_nonneg.mp hb).trans
    apply Finset.sum_le_sum
    intro p hp
    exact sub_nonneg.mp (annihilation_square_le ⟨z-p.val,by omega⟩ (physicalPair Q p.val)).nonneg
  have ha := average_mono (rotationCommutant (fockLowering Q)) hbs
  rw [hc, threeSpinLift_average_highest hQ hz, map_sum] at ha
  have hf (p : Fin (z+1)) : average (rotationCommutant (fockLowering Q))
      ((physicalPair Q p.val).transpose * physicalPair Q p.val) =
      (1/(2*Q-1 : ℕ) : ℝ) • physicalHamiltonian Q :=
    physicalPair_single_val hQ (by omega)
  simp only [hf, ← Finset.sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at ha
  have hd : (0 : ℝ) < ((2*Q-2)+Q-2*z+1 : ℕ) := by positivity
  have hb' := smul_le_smul_of_nonneg_left ha hd.le
  have hr : ((2*Q-2+Q-2*z+1 : ℕ) : ℝ) /
      ((2*Q-1 : ℕ) : ℝ) = threeBodyDimensionRatio Q z := by
    rw [threeBodyDimensionRatio, Nat.cast_add, Nat.cast_sub (by omega : 2*z ≤ 2*Q-2+Q),
      Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ 2*Q), Nat.cast_sub (by omega : 1 ≤ 2*Q)]
    push_cast
    ring
  simp only [smul_smul, mul_one_div_cancel hd.ne', one_smul] at hb'
  convert hb' using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [← hr]
  push_cast
  ring

lemma physicalHamiltonian_positive (Q : ℕ) : (physicalHamiltonian Q).PosSemidef :=
  Matrix.posSemidef_sum _ (fun _ _ => transpose_square_positive _)

lemma threeTailTerm_le {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) (hz16 : 16 ≤ z) :
    -(threeBodyTailTerm Q z) • physicalHamiltonian Q ≤
      (threeBodyGramCoefficient Q z) • threeSpinLift (hQ.trans' (by omega : 2 ≤ 4)) hz := by
  let hQ' : 2 ≤ Q := by omega
  have heq : (-1 : ℝ)^z * fallingRatio Q z *
      (3*(z:ℝ)-1-(z:ℝ)*((z:ℝ)+1)/(Q:ℝ)) = threeBodyGramCoefficient Q z := rfl
  rcases Nat.even_or_odd z with he | ho
  · have hq : 0 ≤ threeBodyGramCoefficient Q z := by
      rw [threeBodyGramCoefficient, he.neg_one_pow, one_mul]
      exact mul_nonneg (fallingRatio_nonneg Q z) (threeBodyBracket_nonneg hQ hz hz16)
    have ht : threeBodyTailTerm Q z = 0 := by
      simp [threeBodyTailTerm, (Nat.not_odd_iff_even.mpr he)]
    rw [ht, neg_zero, zero_smul]
    exact smul_nonneg hq (threeSpinLift_positive hQ' hz).nonneg
  · have h17 : 17 ≤ z := by
      have hn : z ≠ 16 := by rintro rfl; norm_num at ho
      omega
    have hq : threeBodyGramCoefficient Q z ≤ 0 := by
      rw [threeBodyGramCoefficient, ho.neg_one_pow, neg_one_mul, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg (fallingRatio_nonneg Q z) (threeBodyBracket_nonneg hQ hz hz16))
    have hh := smul_le_smul_of_nonneg_left (threeSpinLift_le hQ' hz)
      (abs_nonneg (threeBodyGramCoefficient Q z))
    have hhh := neg_le_neg hh
    simp only [smul_smul, ← neg_smul, abs_of_nonpos hq, neg_neg] at hhh
    convert hhh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    rw [threeBodyTailTerm, ite_eq_left ⟨h17,ho,hz⟩, abs_of_nonpos hq]
    push_cast
    ring

theorem threeTailLift_le {Q : ℕ} (hQ : 4 ≤ Q) :
    -(threeBodyTail Q) • physicalHamiltonian Q ≤ threeTailLift (by omega : 2 ≤ Q) := by
  have hh : (∑ z : Fin (Q+1), -(threeBodyTailTerm Q z.val) • physicalHamiltonian Q) ≤
      threeTailLift (by omega : 2 ≤ Q) := by
    unfold threeTailLift
    apply Finset.sum_le_sum
    intro z hz
    by_cases he : 16 ≤ z.val
    · rw [ite_eq_left he]
      exact threeTailTerm_le hQ (Nat.le_of_lt_succ z.isLt) he
    · have ht : threeBodyTailTerm Q z.val = 0 := by
        simp [threeBodyTailTerm, show ¬ 17 ≤ z.val by omega]
      simp [he,ht]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Finset.sum_smul, Finset.sum_neg_distrib,
    Fin.sum_univ_eq_sum_range (fun z => threeBodyTailTerm Q z)]
  rfl

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

lemma rowSquare_split {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) :
    (rowAnnihilator hQ r).transpose * rowAnnihilator hQ r =
      (r.lam^2) • ((physicalPair Q r.t.val).transpose * physicalPair Q r.t.val) +
      rowThree hQ r + rowFour hQ r := by
  classical
  apply complexify_injective
  let i : RowEntry r.t → Fin (Q+1) := fun a => ⟨a.output.val,by have := a.output.isLt; omega⟩
  have hi (a b : RowEntry r.t) : i a=i b ↔ a.output=b.output := by
    simp only [i,Fin.ext_iff]
  have h := Occupation.auxiliaryRow_square r.lam
    (complexify (physicalPair Q r.t.val)) r.alpha i
    (fun a => complexify (rowTriple hQ a.val))
  have ha : complexify (rowAnnihilator hQ r) =
      Occupation.auxiliaryRow r.lam (complexify (physicalPair Q r.t.val)) r.alpha i
        (fun a => complexify (rowTriple hQ a.val)) := by
    simp only [rowAnnihilator, map_add, map_sum, map_smul, map_mul, complexify_creation,
      Occupation.auxiliaryRow, i]
    rfl
  simp only [map_add, map_smul, map_mul, complexify_transpose, ha]
  rw [h]
  simp only [rowThree,rowFour,map_add,map_sum,map_smul,map_neg,map_mul,
    complexify_transpose, apply_ite, map_zero, hi, rowTriple, complexify_annihilation]
  simp only [i,sub_eq_add_neg,add_assoc]
  rfl

lemma rowSquare_average {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) :
    ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
       ((rowAnnihilator hQ r).transpose * rowAnnihilator hQ r) =
      r.lam^2 • physicalHamiltonian Q +
      ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q)) (rowThree hQ r) +
      ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q)) (rowFour hQ r) := by
  rw [rowSquare_split, map_add, map_add, map_smul,
    physicalPair_single_val (by omega) (by have := r.t.isLt; omega)]
  have hn : ((2*Q-1:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [smul_add, smul_smul]
  congr 2
  field_simp

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealSpinSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Spin Square. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Occupation

@[simp] lemma complexify_physicalTriple (Q : ℕ) (a : Fin (2*Q-2+1) × Fin (Q+1)) :
    complexify (physicalTriple Q a) = Occupation.annihilation a.2 * Occupation.localPair (Q+1) Q a.1.val := by
  simp [physicalTriple, productFamily]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_GlobalBoundCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global Bound Core. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

lemma auxiliary_positive {Q : ℕ} (hQ : 8 ≤ Q) (rows : ι → RowData) :
    0 ≤ rowEta rows • physicalHamiltonian Q + auxiliaryThree hQ rows + auxiliaryFour hQ rows := by
  have hh (r : ι) := smul_nonneg (show (0:ℝ) ≤ ((2*Q-1:ℕ):ℝ) by positivity)
    (average_positive (rotationCommutant (fockLowering Q))
      (transpose_square_positive (rowAnnihilator hQ (rows r)))).nonneg
  simp only [rowSquare_average] at hh
  have h := Finset.sum_nonneg (fun r (_ : r ∈ (Finset.univ : Finset ι)) => hh r)
  simpa only [Finset.sum_add_distrib,← Finset.sum_smul,← Finset.smul_sum,← map_sum,
    rowEta,auxiliaryThree,auxiliaryFour] using h

lemma comparison_additive_step {A : Type*} [AddCommGroup A] [PartialOrder A] [IsOrderedAddMonoid A]
    {h s a b c t η e f τ : A} (hid : s = h+(c+t)+f) (haux : 0 ≤ η+a+b)
    (ha : a ≤ c) (hb : b ≤ f+e) (ht : -τ ≤ t) :
    h-η-τ-e ≤ s := by
  have hr := haux.trans (add_le_add (add_le_add (le_refl η) ha) hb)
  have hh := add_le_add (le_refl (h-η-e)) (add_le_add hr ht)
  convert hh using 1 <;> (try rw [hid]) <;> abel

lemma physical_square_of_comparisons {Q : ℕ} (hQ : 24 ≤ Q)
    (rows : ι → RowData) (δ : ℝ)
    (hthree : auxiliaryThree (by omega) rows ≤ threeRetained (by omega : 15 ≤ Q))
    (hfour : auxiliaryFour (by omega) rows ≤ fourTarget Q + δ • physicalHamiltonian Q) :
    (1-rowEta rows-threeBodyTail Q-δ) • physicalHamiltonian Q ≤
      physicalHamiltonian Q * physicalHamiltonian Q := by
  have ht := threeTailLift_le (by omega : 4 ≤ Q)
  rw [neg_smul] at ht
  have hh := comparison_additive_step (physical_spin_square_split (by omega : 15 ≤ Q))
    (auxiliary_positive (by omega : 8 ≤ Q) rows) hthree hfour ht
  simpa only [sub_smul,one_smul] using hh

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Coupling. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Polynomial
open Polynomial

lemma rootFactorial_pos (n : ℕ) : 0 < rootFactorial n :=
  Real.sqrt_pos.mpr (by exact_mod_cast n.factorial_pos)
lemma rootFactorial_ne_zero (n : ℕ) : rootFactorial n ≠ 0 := (rootFactorial_pos n).ne'

lemma monomialWeight_roots (T p : ℕ) : monomialWeight T p = rootFactorial p * rootFactorial (T-p) :=
  Real.sqrt_mul (by positivity) _

lemma integerCoupling_coeff (c z l p : ℕ) :
    (integerCoupling c z l).coeff p =
      ∑ h ∈ Finset.range (p+1), (-1:ℚ)^(z-h) * (z.choose h) *
        (l.choose (p-h)) * (c:ℚ)^(p-h) := by
  have h₁ (h : ℕ) : ((X-1:ℚ[X])^z).coeff h = (-1:ℚ)^(z-h) * (z.choose h) := by
    simpa [sub_eq_add_neg] using coeff_X_add_C_pow (-1:ℚ) z h
  have h₂ (h : ℕ) : ((C (c:ℚ)*X+1 : ℚ[X])^l).coeff h = (l.choose h : ℚ) * (c:ℚ)^h := by
    have he : ((X+1:ℚ[X])^l).comp (C (c:ℚ)*X) = (C (c:ℚ)*X+1)^l := by simp
    rw [← he,comp_C_mul_X_coeff,coeff_X_add_one_pow]
  simp only [integerCoupling,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,h₁,h₂]
  apply Finset.sum_congr rfl
  intro h hh
  ring

lemma uCoefficient_eq_coeff {z T : ℕ} (hz : z ≤ T) (c p : ℕ) :
    uCoefficient c z T p = (integerCoupling c z (T-z)).coeff p := by
  rw [uCoefficient,ite_eq_left hz,integerCoupling_coeff]

lemma couplingPolynomial_scaled (a b : ℝ) (hb : b ≠ 0) (z l : ℕ) :
    couplingPolynomial a (b*a) z l =
      C (b^z*a^(z+l)/(rootFactorial z*rootFactorial l)) *
        (((X-1)^z*(C (b^2)*X+1)^l).comp (C b⁻¹*X)) := by
  have h₁ : C a * X - C (b*a) = C (b*a) * (C b⁻¹*X-1) := by
    rw [C_mul]
    have hi : (C b : ℝ[X]) * C b⁻¹ = 1 := by rw [← C_mul,mul_inv_cancel₀ hb,C_1]
    linear_combination -(C a * X) * hi
  have h₂ : C (b*a) * X + C a = C a * (C (b^2)*(C b⁻¹*X)+1) := by
    rw [pow_two,C_mul,C_mul]
    have hi : (C b : ℝ[X]) * C b⁻¹ = 1 := by rw [← C_mul,mul_inv_cancel₀ hb,C_1]
    linear_combination -(C a * C b * X) * hi
  have hc : b^z*a^(z+l)/(rootFactorial z*rootFactorial l) =
      (1/(rootFactorial z*rootFactorial l)) * (b*a)^z * a^l := by
    rw [pow_add,mul_pow]; ring
  rw [hc]
  rw [couplingPolynomial,h₁,h₂]
  simp only [mul_comp,pow_comp,sub_comp,add_comp,
    X_comp,C_comp,one_comp,mul_pow,C_mul,C_pow,rootFactorial]
  ring

lemma threeWeightCoefficientStar_rational {z T : ℕ} (hz : z ≤ T) (p : ℕ) :
    RealOccupation.threeWeightCoefficientStar z T p = (uCoefficient 2 z T p : ℝ) *
      (Real.sqrt 2)^z * rootFactorial p * rootFactorial (T-p) /
        ((Real.sqrt 3)^T * (Real.sqrt 2)^p * rootFactorial z * rootFactorial (T-z)) := by
  have hb : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  rw [RealOccupation.threeWeightCoefficientStar,ite_eq_left hz]
  rw [show Real.sqrt 2 / Real.sqrt 3 = Real.sqrt 2 * (1/Real.sqrt 3) by ring,
    couplingPolynomial_scaled _ _ hb,coeff_C_mul,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have he : ((X-1)^z*(C (2:ℝ)*X+1)^(T-z)) =
      (integerCoupling 2 z (T-z)).map (algebraMap ℚ ℝ) := by
    simp [integerCoupling]
  rw [he,comp_C_mul_X_coeff,coeff_map,monomialWeight_roots,
    uCoefficient_eq_coeff hz,Nat.add_sub_of_le hz]
  change _ = (algebraMap ℚ ℝ _) * _ * _ * _ / _
  simp only [one_div,inv_pow]
  ring

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma sqrt_natpow_sq {x : ℝ} (h : 0 ≤ x) (n : ℕ) : (Real.sqrt x ^ n)^2 = x^n := by
  rw [← pow_mul,mul_comm n 2,pow_mul,Real.sq_sqrt h]

lemma threeRowScale_sq (t z i : ℕ) : (threeRowScale t z i)^2 = (threeRowFactor t z i : ℝ) := by
  by_cases h : z ≤ t+i
  · simp only [threeRowScale,threeRowFactor,ite_eq_left h,div_pow,mul_pow,rootFactorial_sq,
      sqrt_natpow_sq (by norm_num : (0:ℝ) ≤ 2),sqrt_natpow_sq (by norm_num : (0:ℝ) ≤ 3)]
    push_cast
    rfl
  · simp [threeRowScale,threeRowFactor,h]

lemma rowNormalization_three {t : Fin 8} (a : RowEntry t) (z : ℕ) :
    rowNormalization t.val a.val.1.val a.val.2.val *
        threeWeightCoefficientStar z (t.val+a.output.val) a.val.1.val =
      (uCoefficient 2 z (t.val+a.output.val) a.val.1.val : ℝ) *
        threeRowScale t.val z a.output.val := by
  by_cases hz : z ≤ t.val+a.output.val
  · have he : t.val+a.output.val-a.val.1.val = a.val.2.val := by have := a.balance; omega
    rw [threeWeightCoefficientStar_rational hz,he,threeRowScale,ite_eq_left hz]
    dsimp [rowNormalization,RowEntry.output]
    field_simp [rootFactorial_ne_zero,Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]

  · simp [threeWeightCoefficientStar,hz,threeRowScale]

lemma threeWeight_row_t (t z i : ℕ) :
    threeWeightCoefficientStar z (t+i) t = (uCoefficient 2 z (t+i) t : ℝ) *
      threeRowScale t z i := by
  by_cases hz : z ≤ t+i
  · rw [threeWeightCoefficientStar_rational hz,threeRowScale,ite_eq_left hz,Nat.add_sub_cancel_left]
    ring
  · simp [threeWeightCoefficientStar,threeRowScale,hz]

lemma sum_fibers_multiply {α β S : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommSemiring S] (o : α → β) (f : α → S) (g : β → S) :
    (∑ i, (∑ a, if o a=i then f a else 0)*g i) = ∑ a, f a*g (o a) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

lemma sum_fibers_trace {α β S : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommSemiring S] (o : α → β) (f : α → S) (g : β → S) :
    (∑ a, f a*g (o a)) + (∑ a, ∑ b, if o a=o b then f a*f b else 0) =
      ∑ i, (∑ a, if o a=i then f a else 0)*((∑ a, if o a=i then f a else 0)+g i) := by
  rw [sum_fibers_multiply]
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_ite,mul_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [eq_comm]

lemma rowTrace_regroup (s : ℕ → ℕ → ℕ → ℝ) (z : ℕ) (r : RowData) :
    rowTrace s z r = ∑ i : Fin 9,
      (∑ a : RowEntry r.t, if a.output=i then r.alpha a*s z (r.t.val+i.val) a.val.1.val else 0)*
      ((∑ a : RowEntry r.t, if a.output=i then r.alpha a*s z (r.t.val+i.val) a.val.1.val else 0) +
        2*r.lam*s z (r.t.val+i.val) r.t.val) := by
  classical
  have hf (i : Fin 9) : (∑ a : RowEntry r.t, if a.output=i then
      r.alpha a*s z (r.t.val+i.val) a.val.1.val else 0) = ∑ a : RowEntry r.t,
        if a.output=i then r.alpha a*s z (r.t.val+a.output.val) a.val.1.val else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · rw [h]
    · rfl
  simp_rw [hf]
  rw [← sum_fibers_trace]
  unfold rowTrace
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    ring
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs with h
    · rw [h]
      ring
    · rfl

lemma RationalRow.threeSum_normalized (r : RationalRow) (z : ℕ) (i : Fin 9) :
    (∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
      threeWeightCoefficientStar z (r.t.val+i.val) a.val.1.val else 0) =
      (r.threeSum z i : ℝ) * threeRowScale r.t.val z i.val := by
  unfold RationalRow.threeSum
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : a.output=i
  · simp only [ite_eq_left h,RationalRow.toReal]
    rw [mul_assoc,← h,rowNormalization_three]
    push_cast
    ring
  · simp [h]

lemma RationalRow.threeTrace_eq (r : RationalRow) (z : ℕ) :
    rowTrace threeWeightCoefficientStar z r.toReal = (r.threeTrace z : ℝ) := by
  rw [rowTrace_regroup]
  simp only [RationalRow.toReal]
  change (∑ i : Fin 9, (∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
    threeWeightCoefficientStar z (r.t.val+i.val) a.val.1.val else 0) *
      ((∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
    threeWeightCoefficientStar z (r.t.val+i.val) a.val.1.val else 0) +
      2*(r.lam:ℝ)*threeWeightCoefficientStar z (r.t.val+i.val) r.t.val)) = _
  simp_rw [r.threeSum_normalized,threeWeight_row_t]
  simp only [RationalRow.threeTrace,Rat.cast_sum,Rat.cast_mul,Rat.cast_add,Rat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← threeRowScale_sq]
  ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalRowComputable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Row Computable. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma sum_row_fiber {S : Type*} [AddCommMonoid S] (t : Fin 8) (i : Fin 9)
    (f : Fin 8 → Fin 9 → S) :
    (∑ a : RowEntry t, if a.output=i then f a.val.1 a.val.2 else 0) =
      ∑ p : Fin 8, ∑ j : Fin 9, if p.val+j.val=t.val+i.val then f p j else 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun a : Fin 8 × Fin 9 =>
    if a.1.val+a.2.val=t.val+i.val then f a.1 a.2 else 0)]
  symm
  apply Finset.sum_congr_set (s := {a : Fin 8 × Fin 9 | t.val ≤ a.1.val+a.2.val ∧
      a.1.val+a.2.val ≤ t.val+8})
  · intro a ha
    change t.val ≤ a.1.val+a.2.val ∧ a.1.val+a.2.val ≤ t.val+8 at ha
    have he : a.1.val+a.2.val=t.val+i.val ↔ RowEntry.output (⟨a,ha⟩ : RowEntry t)=i := by
      simp only [RowEntry.output,Fin.ext_iff]
      omega
    simp only [he]
  · intro a ha
    change ¬ (t.val ≤ a.1.val+a.2.val ∧ a.1.val+a.2.val ≤ t.val+8) at ha
    have hi := i.isLt
    have hn : a.1.val+a.2.val ≠ t.val+i.val := by omega
    simp only [ite_eq_right hn]

lemma sum_fixed_pair {S : Type*} [AddCommMonoid S] (T : ℕ) (p : Fin 8)
    (f : Fin 9 → S) :
    (∑ j : Fin 9, if p.val+j.val=T then f j else 0) =
      if h : p.val ≤ T ∧ T-p.val < 9 then f ⟨T-p.val,h.2⟩ else 0 := by
  classical
  by_cases h : p.val ≤ T ∧ T-p.val < 9
  · rw [dite_eq_left h]
    rw [Finset.sum_eq_single (⟨T-p.val,h.2⟩ : Fin 9)]
    · simp only [Nat.add_sub_of_le h.1,ite_true]
    · intro j hj hn
      have he : p.val+j.val ≠ T := by
        intro he
        apply hn
        apply Fin.ext
        dsimp
        omega
      simp only [ite_eq_right he]
    · simp
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro j hj
    have he : p.val+j.val ≠ T := by have := j.isLt; omega
    simp only [ite_eq_right he]

lemma RationalRow.threeSum_eq_fast (r : RationalRow) (z : ℕ) (i : Fin 9) :
    r.threeSum z i = r.threeSumFast z i := by
  rw [RationalRow.threeSum,sum_row_fiber r.t i (fun p j =>
    r.alpha p j * uCoefficient 2 z (r.t.val+i.val) p.val)]
  simp only [sum_fixed_pair,RationalRow.threeSumFast]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ExactRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma etaRational_value : etaRational = (11530872018309/12500000000000:ℚ) := by decide +kernel

lemma small_margin : (1/25:ℚ) < 1-etaRational-61/4096-1222*(1/200000) := by
  rw [etaRational_value]
  norm_num

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma traceRational_eq (z : ℕ) :
    (traceRational z : ℝ) = ∑ a : Fin 8, rowTrace threeWeightCoefficientStar z (exactRows a).toReal := by
  simp only [RationalRow.threeTrace_eq,RationalRow.threeTrace,RationalRow.threeSum_eq_fast,
    traceRational, exactRows, Rat.cast_sum,Rat.cast_mul,Rat.cast_add,Rat.cast_ofNat]

lemma trace_bound_2 : traceRational 2 < (3/2:ℚ)*(3*2-1)*(-1/2:ℚ)^2 := by decide +kernel
lemma trace_bound_4 : traceRational 4 < (3/2:ℚ)*(3*4-1)*(-1/2:ℚ)^4 := by decide +kernel
lemma trace_bound_5 : traceRational 5 < (3/2:ℚ)*(3*5-1)*(-1/2:ℚ)^5 := by decide +kernel
lemma trace_bound_6 : traceRational 6 < (3/2:ℚ)*(3*6-1)*(-1/2:ℚ)^6 := by decide +kernel
lemma trace_bound_7 : traceRational 7 < (3/2:ℚ)*(3*7-1)*(-1/2:ℚ)^7 := by decide +kernel
lemma trace_bound_8 : traceRational 8 < (3/2:ℚ)*(3*8-1)*(-1/2:ℚ)^8 := by decide +kernel
lemma trace_bound_9 : traceRational 9 < (3/2:ℚ)*(3*9-1)*(-1/2:ℚ)^9 := by decide +kernel
lemma trace_bound_10 : traceRational 10 < (3/2:ℚ)*(3*10-1)*(-1/2:ℚ)^10 := by decide +kernel
lemma trace_bound_11 : traceRational 11 < (3/2:ℚ)*(3*11-1)*(-1/2:ℚ)^11 := by decide +kernel
lemma trace_bound_12 : traceRational 12 < (3/2:ℚ)*(3*12-1)*(-1/2:ℚ)^12 := by decide +kernel
lemma trace_bound_13 : traceRational 13 < (3/2:ℚ)*(3*13-1)*(-1/2:ℚ)^13 := by decide +kernel
lemma trace_bound_14 : traceRational 14 < (3/2:ℚ)*(3*14-1)*(-1/2:ℚ)^14 := by decide +kernel
lemma trace_bound_15 : traceRational 15 < (3/2:ℚ)*(3*15-1)*(-1/2:ℚ)^15 := by decide +kernel

lemma exact_three (z : Fin 16) (h0 : z.val ≠ 0) (h1 : z.val ≠ 1) (h3 : z.val ≠ 3) :
    (∑ a : Fin 8, rowTrace threeWeightCoefficientStar z.val (exactRows a).toReal) <
      (3/2:ℝ)*((3*(z.val:ℝ)-1)*(-1/2:ℝ)^z.val) := by
  rw [← traceRational_eq]
  have h : traceRational z.val < (3/2:ℚ)*(3*(z.val:ℚ)-1)*(-1/2:ℚ)^z.val := by
    fin_cases z
    · exact False.elim (h0 rfl)
    · exact False.elim (h1 rfl)
    · exact trace_bound_2
    · exact False.elim (h3 rfl)
    · exact trace_bound_4
    · exact trace_bound_5
    · exact trace_bound_6
    · exact trace_bound_7
    · exact trace_bound_8
    · exact trace_bound_9
    · exact trace_bound_10
    · exact trace_bound_11
    · exact trace_bound_12
    · exact trace_bound_13
    · exact trace_bound_14
    · exact trace_bound_15
  have hh := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at hh
  nlinarith only [hh]

lemma exact_margin : (1/25:ℝ) <
    1-rowEta (fun a : Fin 8 => (exactRows a).toReal) -61/4096-1222*(1/200000) := by
  have he : rowEta (fun a : Fin 8 => (exactRows a).toReal) = (etaRational:ℝ) := by
    simp [rowEta,etaRational,RationalRow.toReal]
  rw [he]
  have h := (Rat.cast_lt (K := ℝ)).mpr small_margin
  push_cast at h
  exact h

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_GlobalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global Bound. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

theorem physical_square_eventually_of_certificates
    (rows : ι → RowData) (ε γ : ℝ) (hε : 0 ≤ ε)
    (hmargin : γ < 1-rowEta rows-(61/4096:ℝ)-1222*ε)
    (hthree : ∀ z : Fin 16, z.val ≠ 0 → z.val ≠ 1 → z.val ≠ 3 →
      (∑ r, rowTrace threeWeightCoefficientStar z.val (rows r)) <
        (3/2:ℝ) * ((3*(z.val:ℝ)-1)*(-1/2:ℝ)^z.val))
    (hfour : ∀ d : Fin 23, FourCertificate rows ε (d.val+1) (by omega)) :
    ∀ᶠ Q in atTop, γ • physicalHamiltonian Q ≤ physicalHamiltonian Q * physicalHamiltonian Q := by
  obtain ⟨R,hpos,hlimR,hR⟩ := four_comparison_of_certificates rows ε hε hfour
  have hlim : Tendsto (fun Q => 1-rowEta rows-threeBodyTail Q-(1222*ε+R Q)) atTop
      (𝓝 (1-rowEta rows-(61/4096:ℝ)-1222*ε)) := by
    simpa only [add_zero] using (threeBodyTail_tendsto.const_sub (1-rowEta rows)).sub
      (hlimR.const_add (1222*ε))
  filter_upwards [eventually_ge_atTop 24,three_comparison_of_strict_traces rows hthree,hR,
    hlim.eventually (Ioi_mem_nhds hmargin)] with Q hQ h₃ h₄ hγ
  apply le_trans _ (physical_square_of_comparisons hQ rows (1222*ε+R Q) (h₃ (by omega)) (h₄ hQ))
  exact smul_le_smul_of_nonneg_right (le_of_lt hγ) (physicalHamiltonian_positive Q).nonneg

lemma occupation_square_of_real_square {Q : ℕ} (γ : ℝ)
    (h : γ • physicalHamiltonian Q ≤ physicalHamiltonian Q * physicalHamiltonian Q) :
    ∀ x : Occupation.Hilbert (Q+1), γ * Occupation.localPairEnergy (Q+1) (2*Q-1) Q x ≤
      ‖Occupation.physicalOccupationHamiltonian Q x‖^2 := by
  have hp := complexify_positive (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))
  intro x
  have hx := hp.re_inner_nonneg_right x
  simp only [map_sub,map_mul,map_smul,complexify_physicalHamiltonian,
    LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,inner_sub_right,
    inner_smul_right_eq_smul] at hx
  rw [← (Occupation.physicalOccupationHamiltonian_positive Q).isSymmetric x
    (Occupation.physicalOccupationHamiltonian Q x),inner_self_eq_norm_sq_to_K] at hx
  change 0 ≤ ((‖Occupation.physicalOccupationHamiltonian Q x‖:ℂ)^2).re -
    (γ • inner ℂ x (Occupation.physicalOccupationHamiltonian Q x)).re at hx
  rw [← Complex.ofReal_pow,Complex.ofReal_re,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Occupation.physicalOccupationHamiltonian_inner] at hx
  exact sub_nonneg.mp hx

theorem mainTarget_of_finite_certificates
    (rows : ι → RowData) (ε : ℝ) (hε : 0 ≤ ε)
    (hmargin : (1/25:ℝ) < 1-rowEta rows-(61/4096:ℝ)-1222*ε)
    (hthree : ∀ z : Fin 16, z.val ≠ 0 → z.val ≠ 1 → z.val ≠ 3 →
      (∑ r, rowTrace threeWeightCoefficientStar z.val (rows r)) <
        (3/2:ℝ) * ((3*(z.val:ℝ)-1)*(-1/2:ℝ)^z.val))
    (hfour : ∀ d : Fin 23, FourCertificate rows ε (d.val+1) (by omega)) : MainTarget := by
  apply Occupation.mainTarget_of_uniform_occupation_square_estimate
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp
    (physical_square_eventually_of_certificates rows ε (1/25) hε hmargin hthree hfour)
  exact ⟨Q₀,fun Q hQ => occupation_square_of_real_square _ (hQ₀ Q hQ)⟩

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main. -/

noncomputable section


namespace LaughlinGap

theorem thm_main_oai : MainTarget := by
  exact RealOccupation.mainTarget_of_finite_certificates
    (fun a : Fin 8 => (RealOccupation.exactRows a).toReal) (1/200000)
    (by norm_num) RealOccupation.exact_margin RealOccupation.exact_three
    RealOccupation.exact_four

end LaughlinGap

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.thm_main_oai := @OAI.LaughlinGap.thm_main_oai
