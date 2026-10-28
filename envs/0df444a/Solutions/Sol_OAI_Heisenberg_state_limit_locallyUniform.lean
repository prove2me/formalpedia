-- Prove2me | solution 1 for OAI.Heisenberg.state_limit_locallyUniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:42:27.629503+00:00
-- url     : https://prove2.me/submissions/ebc8cb97-6514-474b-a810-f0c7e3dcc92d

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM002
import Theorems.Thm_OAI_Heisenberg_dynamics_converges

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalAlgebra
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical

open scoped ComplexConjugate BigOperators
namespace Heisenberg

lemma localUnit_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d}
    (hx : x ∈ F) (a b : Level ℓ) : localUnit d ℓ x a b ∈ localAlgebra d ℓ F :=
  StarAlgebra.subset_adjoin ℂ _ ⟨x, hx, a, b, rfl⟩

lemma spinZ_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinZ d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k k) _

lemma spinPlus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinPlus d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k.succ k.castSucc) _

lemma spinMinus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinMinus d ℓ x ∈ localAlgebra d ℓ F :=
  star_mem (spinPlus_mem_localAlgebra d ℓ F hx)

lemma spinX_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinX d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).add_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

lemma spinY_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinY d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).sub_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

theorem localAlgebras_commute {d ℓ : ℕ} {F G : Set (Site d)} (hFG : Disjoint F G)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ F) (hB : B ∈ localAlgebra d ℓ G) :
    Commute A B := by
  have hg (x : Site d) (hx : x ∈ F) (a b : Level ℓ) :
      localAlgebra d ℓ G ≤ StarSubalgebra.centralizer ℂ {localUnit d ℓ x a b} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨y, hy, c, e, rfl⟩
    have hxy : x ≠ y := fun h => (Set.disjoint_left.mp hFG hx) (h ▸ hy)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨(localUnits_commute hxy a b c e).eq, by
      rw [star_localUnit]
      exact (localUnits_commute hxy b a c e).eq⟩
  have hle : localAlgebra d ℓ F ≤ StarSubalgebra.centralizer ℂ {B} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨x, hx, a, b, rfl⟩
    have h₁ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hg x hx a b hB)) _ (Set.mem_singleton _)
    have h₂ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp
      (hg x hx a b (star_mem hB))) _ (Set.mem_singleton _)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨h₁.1.symm, h₂.1.symm⟩
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hA)) B (Set.mem_singleton B)).1.symm

lemma singleton_local_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ {x})
    (hB : B ∈ localAlgebra d ℓ {y}) : Commute A B :=
  localAlgebras_commute (Set.disjoint_singleton.mpr hxy) hA hB

lemma nearestNeighbor_ne {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) : x ≠ y := by
  intro he
  subst y
  simp [NearestNeighbor] at h

theorem star_hamiltonian (d ℓ : ℕ) (Λ : Finset (Site d)) :
    star (hamiltonian d ℓ Λ) = hamiltonian d ℓ Λ := by
  classical
  simp only [hamiltonian, star_neg, star_sum, star_add, star_mul,
    star_spinX, star_spinY, star_spinZ]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hxy := nearestNeighbor_ne (Finset.mem_filter.mp he).2.1
  have hX := singleton_local_commute hxy (spinX_mem_localAlgebra d ℓ {e.1} rfl)
    (spinX_mem_localAlgebra d ℓ {e.2} rfl)
  have hY := singleton_local_commute hxy (spinY_mem_localAlgebra d ℓ {e.1} rfl)
    (spinY_mem_localAlgebra d ℓ {e.2} rfl)
  have hZ := singleton_local_commute hxy (spinZ_mem_localAlgebra d ℓ {e.1} rfl)
    (spinZ_mem_localAlgebra d ℓ {e.2} rfl)
  rw [hX.eq, hY.eq, hZ.eq]

lemma imaginaryTime_skew (t : ℝ) : Complex.I * (t : ℂ) ∈ skewAdjoint ℂ := by
  change star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ))
  simp

lemma hamiltonian_selfAdjoint (d ℓ : ℕ) (Λ : Finset (Site d)) :
    IsSelfAdjoint (hamiltonian d ℓ Λ) := star_hamiltonian d ℓ Λ

lemma timeHamiltonian_skew (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    (Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ ∈ skewAdjoint (QuasiLocal d ℓ) :=
  IsSelfAdjoint.smul_mem_skewAdjoint (imaginaryTime_skew t) (hamiltonian_selfAdjoint d ℓ Λ)

lemma finiteUnitary (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ) ∈ unitary (QuasiLocal d ℓ) :=
  NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (timeHamiltonian_skew d ℓ Λ t)

lemma finiteInverseUnitary (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ) ∈ unitary (QuasiLocal d ℓ) := by
  convert finiteUnitary d ℓ Λ (-t) using 1; simp

theorem norm_finiteDynamics (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    ‖finiteDynamics d ℓ Λ t A‖ = ‖A‖ := by
  rw [finiteDynamics, CStarRing.norm_mul_mem_unitary _ (finiteInverseUnitary d ℓ Λ t),
    CStarRing.norm_mem_unitary_mul _ (finiteUnitary d ℓ Λ t)]

lemma finiteDynamics_sub (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A B : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t (A - B) = finiteDynamics d ℓ Λ t A - finiteDynamics d ℓ Λ t B := by
  simp [finiteDynamics, mul_sub, sub_mul]

theorem finiteDynamics_isometry (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    Isometry (finiteDynamics d ℓ Λ t) := by
  apply Isometry.of_dist_eq
  intro A B
  simp only [dist_eq_norm, ← finiteDynamics_sub, norm_finiteDynamics]

lemma bondBound_nonneg (d ℓ : ℕ) : 0 ≤ bondBound d ℓ := by unfold bondBound; positivity

lemma norm_bond_le (d ℓ : ℕ) (x y : Site d) : ‖bond d ℓ x y‖ ≤ bondBound d ℓ := by
  have hX (x : Site d) : ‖spinX d ℓ x‖ = ‖spinX d ℓ 0‖ := by
    simpa using norm_translation d ℓ x (spinX d ℓ 0)
  have hY (x : Site d) : ‖spinY d ℓ x‖ = ‖spinY d ℓ 0‖ := by
    simpa using norm_translation d ℓ x (spinY d ℓ 0)
  have hZ (x : Site d) : ‖spinZ d ℓ x‖ = ‖spinZ d ℓ 0‖ := by
    simpa using norm_translation d ℓ x (spinZ d ℓ 0)
  calc
    ‖bond d ℓ x y‖ ≤ (‖spinX d ℓ x‖*‖spinX d ℓ y‖ +
        ‖spinY d ℓ x‖*‖spinY d ℓ y‖) + ‖spinZ d ℓ x‖*‖spinZ d ℓ y‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)))
        (norm_mul_le _ _))
    _ = bondBound d ℓ := by simp only [hX, hY, hZ, bondBound, pow_two]

lemma bond_mem_local {d ℓ : ℕ} {F : Set (Site d)} {x y : Site d}
    (hx : x ∈ F) (hy : y ∈ F) : bond d ℓ x y ∈ localAlgebra d ℓ F := by
  apply (localAlgebra d ℓ F).add_mem
  · exact (localAlgebra d ℓ F).add_mem
      ((localAlgebra d ℓ F).mul_mem (spinX_mem_localAlgebra d ℓ F hx)
        (spinX_mem_localAlgebra d ℓ F hy))
      ((localAlgebra d ℓ F).mul_mem (spinY_mem_localAlgebra d ℓ F hx)
        (spinY_mem_localAlgebra d ℓ F hy))
  · exact (localAlgebra d ℓ F).mul_mem (spinZ_mem_localAlgebra d ℓ F hx)
      (spinZ_mem_localAlgebra d ℓ F hy)

lemma localAlgebra_mono {d ℓ : ℕ} {F G : Set (Site d)} (h : F ⊆ G) :
    localAlgebra d ℓ F ≤ localAlgebra d ℓ G := by
  apply StarAlgebra.adjoin_mono
  rintro A ⟨x, hx, a, b, rfl⟩
  exact ⟨x, h hx, a, b, rfl⟩

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExponentialEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace SpinEvolution

section
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]

lemma leftRegular_continuous : Continuous (leftRegular : E → E →L[ℂ] E) :=
  (ContinuousLinearMap.mul ℂ E).continuous

lemma rightRegular_continuous : Continuous (rightRegular : Eᵐᵒᵖ → E →L[ℂ] E) :=
  (ContinuousLinearMap.mul ℂ E).flip.continuous.comp MulOpposite.continuous_unop

lemma left_right_commute (H K : E) :
    Commute (leftRegular H) (rightRegular (MulOpposite.op K)) := by
  ext A
  simp [mul_assoc]

variable [CompleteSpace E]

lemma exp_left (H : E) : NormedSpace.exp (leftRegular H) = leftRegular (NormedSpace.exp H) := by
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℂ E
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact (NormedSpace.map_exp leftRegular leftRegular_continuous H).symm

lemma exp_right (H : E) : NormedSpace.exp (rightRegular (MulOpposite.op H)) =
    rightRegular (MulOpposite.op (NormedSpace.exp H)) := by
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℂ E
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  simpa only [NormedSpace.exp_op] using
    (NormedSpace.map_exp (rightRegular (E := E)) rightRegular_continuous
      (MulOpposite.op H)).symm

theorem exp_left_add_right (H K A : E) :
    NormedSpace.exp (leftRegular H + rightRegular (MulOpposite.op K)) A =
      NormedSpace.exp H * A * NormedSpace.exp K := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [NormedSpace.exp_add_of_commute (left_right_commute H K), exp_left, exp_right]
  simp [mul_assoc]

omit [CompleteSpace E] in
lemma time_generator (H : E) (z : ℂ) :
    z • generator H = leftRegular ((z*Complex.I) • H) +
      rightRegular (MulOpposite.op ((-(z*Complex.I)) • H)) := by
  ext A
  simp [generator, smul_add, smul_smul]

theorem exp_generator (H A : E) (z : ℂ) :
    NormedSpace.exp (z • generator H) A =
      NormedSpace.exp ((z*Complex.I) • H) * A * NormedSpace.exp ((-(z*Complex.I)) • H) := by
  rw [time_generator, exp_left_add_right]

end

end SpinEvolution

namespace Heisenberg

lemma nearestNeighbor_symm {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    NearestNeighbor y x := by
  unfold NearestNeighbor at *
  simpa only [abs_sub_comm] using h

lemma nearestNeighbor_coordinate {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    ∃ i, (y i = x i + 1 ∨ y i = x i - 1) ∧ ∀ j, j ≠ i → y j = x j := by
  have hi : ∃ i, x i ≠ y i := by
    by_contra! hh
    have : ∑ i : Fin d, |x i - y i| = (0 : ℤ) := by simp [hh]
    change ∑ i : Fin d, |x i - y i| = (1 : ℤ) at h
    omega
  obtain ⟨i, hi⟩ := hi
  have hain : 1 ≤ |x i-y i| := by
    have hn : x i-y i ≠ 0 := sub_ne_zero.mpr hi
    have := abs_pos.mpr hn
    omega
  have hai : |x i-y i| ≤ 1 := by
    change ∑ i : Fin d, |x i-y i| = (1 : ℤ) at h
    rw [← h]
    exact Finset.single_le_sum (f := fun j : Fin d => |x j - y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  refine ⟨i, ?_, ?_⟩
  · have hab : x i-y i = 1 ∨ x i-y i = -1 := by
      have : |x i-y i| = 1 := le_antisymm hai hain
      exact (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp this
    omega
  · intro j hji
    have hsum : |x i-y i| + |x j-y j| ≤ (1 : ℤ) := by
      change ∑ i : Fin d, |x i-y i| = (1 : ℤ) at h
      rw [← h]
      rw [← Finset.sum_pair (f := fun j : Fin d => |x j-y j|) (Ne.symm hji)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    have : |x j-y j| = 0 := le_antisymm (by omega) (abs_nonneg _)
    exact (sub_eq_zero.mp (abs_eq_zero.mp this)).symm

lemma mem_neighbors_of_nearestNeighbor {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    y ∈ neighbors x := by
  obtain ⟨i, hi, he⟩ := nearestNeighbor_coordinate h
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rcases hi with hi | hi
  · have hy : y = Function.update x i (x i+1) := by
      ext j
      by_cases hj : j = i
      · subst j; simpa using hi
      · simp [Function.update_of_ne hj, he j hj]
    simp [hy]
  · have hy : y = Function.update x i (x i-1) := by
      ext j
      by_cases hj : j = i
      · subst j; simpa using hi
      · simp [Function.update_of_ne hj, he j hj]
    simp [hy]

lemma card_neighbors_le {d : ℕ} (x : Site d) : (neighbors x).card ≤ 2*d := by
  calc
    (neighbors x).card ≤ ∑ i : Fin d,
        ({Function.update x i (x i+1), Function.update x i (x i-1)} : Finset (Site d)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin d, 2 := Finset.sum_le_sum (fun _ _ => Finset.card_le_two)
    _ = 2*d := by simp [mul_comm]

lemma mem_incidentEdges {d : ℕ} {F : Finset (Site d)} {x y : Site d}
    (h : NearestNeighbor x y) (hm : x ∈ F ∨ y ∈ F) : (x,y) ∈ incidentEdges F := by
  rcases hm with hx | hy
  · exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨y, mem_neighbors_of_nearestNeighbor h, rfl⟩)⟩
  · exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x, mem_neighbors_of_nearestNeighbor (nearestNeighbor_symm h), rfl⟩)⟩

lemma card_incidentEdges_le {d : ℕ} (F : Finset (Site d)) :
    (incidentEdges F).card ≤ (4*d)*F.card := by
  calc
    _ ≤ ∑ x ∈ F, (((neighbors x).image (fun y => (x,y))) ∪
        ((neighbors x).image (fun y => (y,x)))).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ F, 4*d := by
      apply Finset.sum_le_sum
      intro x _
      exact (Finset.card_union_le _ _).trans ((add_le_add
        ((Finset.card_image_le).trans (card_neighbors_le x))
        ((Finset.card_image_le).trans (card_neighbors_le x))).trans (by omega))
    _ = (4*d)*F.card := by simp [mul_comm]

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalDynamics
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

lemma norm_commutatorTerm_le (d ℓ : ℕ) (e : Site d × Site d) (A : QuasiLocal d ℓ) :
    ‖commutatorTerm d ℓ e A‖ ≤ 2*bondBound d ℓ*‖A‖ := by
  calc
    _ = ‖bond d ℓ e.1 e.2 * A - A*bond d ℓ e.1 e.2‖ := by
      simp [commutatorTerm, norm_smul]
    _ ≤ ‖bond d ℓ e.1 e.2*A‖+‖A*bond d ℓ e.1 e.2‖ := norm_sub_le _ _
    _ ≤ ‖bond d ℓ e.1 e.2‖*‖A‖+‖A‖*‖bond d ℓ e.1 e.2‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ bondBound d ℓ*‖A‖+‖A‖*bondBound d ℓ :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_bond_le _ _ _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_bond_le _ _ _ _) (norm_nonneg _))
    _ = _ := by ring

lemma finiteGenerator_eq_sum (d ℓ : ℕ) (Λ : Finset (Site d)) (A : QuasiLocal d ℓ) :
    finiteGenerator d ℓ Λ A = ∑ e ∈ volumeEdges Λ, commutatorTerm d ℓ e A := by
  simp only [finiteGenerator, SpinEvolution.generator_apply, hamiltonian,
    commutatorTerm, bond, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum,
    smul_sub, smul_neg, Finset.smul_sum, Finset.sum_sub_distrib, neg_smul, Finset.sum_neg_distrib]

lemma commutatorTerm_mem {d ℓ : ℕ} {F : Finset (Site d)} (e : Site d × Site d)
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) :
    commutatorTerm d ℓ e A ∈ localAlgebra d ℓ (↑(F ∪ {e.1,e.2}) : Set (Site d)) := by
  let G : Set (Site d) := ↑(F ∪ {e.1,e.2})
  have hAg : A ∈ localAlgebra d ℓ G :=
    localAlgebra_mono (by intro x hx; exact Finset.mem_union_left _ hx) hA
  have hb : bond d ℓ e.1 e.2 ∈ localAlgebra d ℓ G := bond_mem_local (by simp [G]) (by simp [G])
  exact (localAlgebra d ℓ G).smul_mem ((localAlgebra d ℓ G).sub_mem
    ((localAlgebra d ℓ G).mul_mem hb hAg) ((localAlgebra d ℓ G).mul_mem hAg hb)) _

lemma commutatorTerm_eq_zero {d ℓ : ℕ} {F : Finset (Site d)} {e : Site d × Site d}
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d)))
    (h1 : e.1 ∉ F) (h2 : e.2 ∉ F) : commutatorTerm d ℓ e A = 0 := by
  have hd : Disjoint ({e.1,e.2} : Set (Site d)) (F : Set (Site d)) := by
    simp only [Set.disjoint_left, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
    rintro x (rfl | rfl) hx <;> contradiction
  have hb : bond d ℓ e.1 e.2 ∈ localAlgebra d ℓ ({e.1,e.2} : Set (Site d)) :=
    bond_mem_local (by simp) (by simp)
  have hc := localAlgebras_commute hd hb hA
  simp only [commutatorTerm, hc.eq, sub_self, smul_zero]

lemma activeEdges_subset_incident {d : ℕ} (Λ F : Finset (Site d)) :
    activeEdges Λ F ⊆ incidentEdges F := by
  intro e he
  obtain ⟨hv, hm⟩ := Finset.mem_filter.mp he
  exact mem_incidentEdges (Finset.mem_filter.mp hv).2.1 hm

lemma finiteGenerator_eq_activeSum {d ℓ : ℕ} (Λ F : Finset (Site d))
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) :
    finiteGenerator d ℓ Λ A = ∑ e ∈ activeEdges Λ F, commutatorTerm d ℓ e A := by
  rw [finiteGenerator_eq_sum]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hv
  have he' : ¬ (e.1 ∈ F ∨ e.2 ∈ F) := by
    intro hm; exact hv (Finset.mem_filter.mpr ⟨he, hm⟩)
  exact commutatorTerm_eq_zero hA (not_or.mp he').1 (not_or.mp he').2

lemma card_union_edge_le {d : ℕ} (F : Finset (Site d)) {e : Site d × Site d}
    (he : e.1 ∈ F ∨ e.2 ∈ F) : (F ∪ {e.1,e.2}).card ≤ F.card+1 := by
  rcases he with h1 | h2
  · have hh : F ∪ {e.1,e.2} = insert e.2 F := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hh]; exact Finset.card_insert_le _ _
  · have hh : F ∪ {e.1,e.2} = insert e.1 F := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hh]; exact Finset.card_insert_le _ _

lemma finiteGenerator_localDecomposition (d ℓ : ℕ) (Λ : Finset (Site d)) :
    SpinEvolution.LocalDecomposition (finiteGenerator d ℓ Λ) (SupportedOnAtMost d ℓ)
      (8*d*bondBound d ℓ) := by
  constructor
  · exact mul_nonneg (by positivity) (bondBound_nonneg _ _)
  · intro k A hA
    obtain ⟨F, hk, hA⟩ := hA
    let I := activeEdges Λ F
    let e : I ≃ Fin I.card := (Fintype.equivFin I).trans (finCongr (Fintype.card_coe I))
    let g : Fin I.card → QuasiLocal d ℓ := fun j => commutatorTerm d ℓ (e.symm j) A
    have hg : ∑ j, g j = ∑ x ∈ I, commutatorTerm d ℓ x A := by
      calc
        ∑ j, g j = ∑ x : I, commutatorTerm d ℓ x A :=
          Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
        _ = _ := Finset.sum_coe_sort I (fun x => commutatorTerm d ℓ x A)
    refine ⟨I.card, g, ?_, ?_, ?_⟩
    · rw [hg]; exact finiteGenerator_eq_activeSum Λ F hA
    · intro j
      refine ⟨F ∪ {(e.symm j).val.1,(e.symm j).val.2}, ?_, commutatorTerm_mem _ hA⟩
      exact (card_union_edge_le F (Finset.mem_filter.mp (e.symm j).property).2).trans (by omega)
    · have hcard : I.card ≤ (4*d)*(k+1) :=
        ((Finset.card_le_card (activeEdges_subset_incident Λ F)).trans
          (card_incidentEdges_le F)).trans (Nat.mul_le_mul_left _ hk)
      calc
        ∑ j, ‖g j‖ ≤ ∑ _ : Fin I.card, 2*bondBound d ℓ*‖A‖ :=
          Finset.sum_le_sum (fun j _ => norm_commutatorTerm_le _ _ _ _)
        _ = (I.card : ℝ)*(2*bondBound d ℓ*‖A‖) := by simp
        _ ≤ ((4*d)*(k+1) : ℝ)*(2*bondBound d ℓ*‖A‖) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcard
          · exact mul_nonneg (mul_nonneg (by norm_num) (bondBound_nonneg _ _)) (norm_nonneg _)
        _ = (8*d*bondBound d ℓ)*(k+1)*‖A‖ := by ring



theorem localCore_dense (d ℓ : ℕ) : Dense (localCore d ℓ : Set (QuasiLocal d ℓ)) := by
  let B := StarAlgebra.adjoin ℂ {A : SpinOperator d ℓ | ∃ x a b, A = matrixUnit d ℓ x a b}
  let f : B →⋆ₐ[ℂ] QuasiLocal d ℓ := StarSubalgebra.inclusion B.le_topologicalClosure
  have hd : DenseRange f := by
    change DenseRange (Set.inclusion B.le_topologicalClosure)
    apply (denseRange_inclusion_iff B.le_topologicalClosure).mpr
    rw [StarSubalgebra.topologicalClosure_coe]
  have hle : B ≤ (localCore d ℓ).map (quasiLocalAlgebra d ℓ).subtype := by
    apply StarAlgebra.adjoin_le
    rintro A ⟨x,a,b,rfl⟩
    exact ⟨localUnit d ℓ x a b, StarAlgebra.subset_adjoin ℂ _ ⟨x,a,b,rfl⟩, rfl⟩
  apply Dense.mono (s₁ := Set.range f) ?_ hd
  rintro A ⟨a,rfl⟩
  obtain ⟨b,hb,he⟩ := hle a.property
  have heq : f a = b := Subtype.ext he.symm
  rwa [heq]

lemma localCore_finite_support {d ℓ : ℕ} {A : QuasiLocal d ℓ}
    (hA : A ∈ localCore d ℓ) : ∃ F : Finset (Site d), A ∈ localAlgebra d ℓ (F : Set (Site d)) := by
  induction hA using StarAlgebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨x,a,b,rfl⟩ := ha
    exact ⟨{x},localUnit_mem_localAlgebra _ _ _ (by simp) _ _⟩
  | algebraMap z => exact ⟨∅, by simpa only [Finset.coe_empty] using
      (localAlgebra d ℓ ∅).algebraMap_mem z⟩
  | add a b ha hb iha ihb =>
    obtain ⟨F,hF⟩ := iha
    obtain ⟨G,hG⟩ := ihb
    refine ⟨F ∪ G,(localAlgebra d ℓ (↑(F ∪ G) : Set (Site d))).add_mem ?_ ?_⟩
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_left _ hx) hF
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_right _ hx) hG
  | mul a b ha hb iha ihb =>
    obtain ⟨F,hF⟩ := iha
    obtain ⟨G,hG⟩ := ihb
    refine ⟨F ∪ G,(localAlgebra d ℓ (↑(F ∪ G) : Set (Site d))).mul_mem ?_ ?_⟩
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_left _ hx) hF
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_right _ hx) hG
  | star a ha iha =>
    obtain ⟨F,hF⟩ := iha
    exact ⟨F,star_mem hF⟩

end Heisenberg

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ThermodynamicDynamics
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

attribute [local instance] OAI.Heisenberg.instIsTopologicalRingContinuousLinearMapComplexIdSubtypeSpinOperatorMemStarSubalgebraQuasiLocal
lemma finiteDynamics_generator (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t A = NormedSpace.exp ((t : ℂ) • finiteGenerator d ℓ Λ) A := by
  rw [finiteGenerator, SpinEvolution.exp_generator]
  simp only [finiteDynamics, mul_comm (t : ℂ) Complex.I]

end Heisenberg

open Filter Topology Metric
namespace EquicontinuousLimits

section
variable {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable {φ : Filter ι} [φ.NeBot]

theorem locallyUniform {F : ι → X → Y} {f : X → Y}
    (he : Equicontinuous F) (hf : ∀ x, Tendsto (fun i => F i x) φ (𝓝 (f x))) :
    TendstoLocallyUniformly F f φ := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  obtain ⟨δ,hδ,hd⟩ := Metric.equicontinuousAt_iff.mp (he x) (ε/4) (by positivity)
  refine ⟨ball x δ,ball_mem_nhds x hδ,?_⟩
  filter_upwards [Metric.tendsto_nhds.mp (hf x) (ε/4) (by positivity)] with i hi
  intro y hy
  have hh : dist (f x) (f y) ≤ ε/4 :=
    le_of_tendsto ((hf x).dist (hf y)) (Filter.Eventually.of_forall fun j => (hd y hy j).le)
  have htriangle := dist_triangle (f y) (f x) (F i y)
  have htriangle' := dist_triangle (f x) (F i x) (F i y)
  rw [dist_comm (F i x) (f x)] at hi
  rw [dist_comm (f y) (f x)] at htriangle
  exact lt_of_le_of_lt htriangle (by linarith [hd y hy i])

end

variable {ι X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {φ : Filter ι} [φ.NeBot]

theorem equicontinuous_apply {L : ι → E →L[ℂ] ℂ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ i, ‖L i‖ ≤ C) {F : ι → X → E}
    (he : Equicontinuous F) : Equicontinuous (fun i x => L i (F i x)) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  have hp : 0 < C+1 := by linarith
  obtain ⟨δ,hδ,hd⟩ := Metric.equicontinuousAt_iff.mp (he x) (ε/(C+1)) (div_pos hε hp)
  refine ⟨δ,hδ,fun y hy i => ?_⟩
  have hb : dist (L i (F i x)) (L i (F i y)) ≤ C*dist (F i x) (F i y) := by
    rw [dist_eq_norm,dist_eq_norm,← map_sub]
    exact ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _))
  have hh := (lt_div_iff₀ hp).mp (hd y hy i)
  exact hb.trans_lt (by nlinarith [(dist_nonneg : 0 ≤ dist (F i x) (F i y))])

end EquicontinuousLimits
open scoped NNReal
namespace SpinEvolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma exponential_derivative (D : E →L[ℂ] E) (A : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • D) A)
      (NormedSpace.exp ((t : ℂ) • D) (D A)) t := by
  let : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _
  have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) D t
  have he := ((ContinuousLinearMap.apply ℂ E A).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s : ℝ => NormedSpace.exp (s • D) A)
    ((NormedSpace.exp (t • D) * D) A) t at he
  have hr (s : ℝ) : (s : ℂ) • D = s • D := IsScalarTower.algebraMap_smul ℂ s D
  simpa only [hr,mul_apply_eq_comp] using he

end SpinEvolution

open scoped NNReal
namespace Heisenberg

lemma finiteDynamics_hasDerivAt (d ℓ : ℕ) (Λ : Finset (Site d))
    (A : QuasiLocal d ℓ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => finiteDynamics d ℓ Λ s A)
      (finiteDynamics d ℓ Λ t (finiteGenerator d ℓ Λ A)) t := by
  simpa only [← finiteDynamics_generator] using
    SpinEvolution.exponential_derivative (finiteGenerator d ℓ Λ) A t

lemma finiteDynamics_local_lipschitz {d ℓ : ℕ} {A : QuasiLocal d ℓ}
    (hA : A ∈ localCore d ℓ) :
    ∃ M : ℝ≥0, ∀ Λ : Finset (Site d), LipschitzWith M (fun t => finiteDynamics d ℓ Λ t A) := by
  obtain ⟨F,hF⟩ := localCore_finite_support hA
  let C : ℝ := 8*d*bondBound d ℓ
  have hC : 0 ≤ C := (finiteGenerator_localDecomposition d ℓ ∅).nonneg
  let M : ℝ≥0 := ⟨C*(F.card+1)*‖A‖, by positivity⟩
  refine ⟨M,fun Λ => lipschitzWith_of_nnnorm_deriv_le
    (fun t => (finiteDynamics_hasDerivAt d ℓ Λ A t).differentiableAt) ?_⟩
  intro t
  rw [(finiteDynamics_hasDerivAt d ℓ Λ A t).deriv]
  change ‖finiteDynamics d ℓ Λ t (finiteGenerator d ℓ Λ A)‖ ≤ M
  rw [norm_finiteDynamics]
  obtain ⟨r,g,hg,_,hbound⟩ := (finiteGenerator_localDecomposition d ℓ Λ).split F.card A
    ⟨F,Nat.le_succ _,hF⟩
  rw [hg]
  exact (norm_sum_le _ _).trans hbound

lemma finiteDynamics_equicontinuous (d ℓ : ℕ) (A : QuasiLocal d ℓ) :
    Equicontinuous (fun Λ : Finset (Site d) => fun t : ℝ => finiteDynamics d ℓ Λ t A) := by
  intro t
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨B,hB,hAB⟩ := (localCore_dense d ℓ).exists_dist_lt A (show 0 < ε/8 by positivity)
  obtain ⟨M,hM⟩ := finiteDynamics_local_lipschitz hB
  have hp : 0 < (4:ℝ)*(M+1) := by positivity
  refine ⟨ε/(4*(M+1)),div_pos hε hp,?_⟩
  intro s hs Λ
  have hl := (hM Λ).dist_le_mul t s
  have htime : dist t s < ε/(4*(M+1)) := by simpa [dist_comm] using hs
  have ht : (M:ℝ)*dist t s < ε/4 := by
    have hm : 0 ≤ (M:ℝ) := M.property
    have hh := (lt_div_iff₀ hp).mp htime
    nlinarith [(dist_nonneg : 0 ≤ dist t s)]
  calc
    dist (finiteDynamics d ℓ Λ t A) (finiteDynamics d ℓ Λ s A) ≤
        dist (finiteDynamics d ℓ Λ t A) (finiteDynamics d ℓ Λ t B) +
        dist (finiteDynamics d ℓ Λ t B) (finiteDynamics d ℓ Λ s B) +
        dist (finiteDynamics d ℓ Λ s B) (finiteDynamics d ℓ Λ s A) := dist_triangle4 _ _ _ _
    _ = dist A B + dist (finiteDynamics d ℓ Λ t B) (finiteDynamics d ℓ Λ s B) + dist B A := by
      rw [(finiteDynamics_isometry d ℓ Λ t).dist_eq,(finiteDynamics_isometry d ℓ Λ s).dist_eq]
    _ < ε := by rw [dist_comm B A]; linarith

theorem dynamics_locallyUniform (d ℓ : ℕ) (A : QuasiLocal d ℓ) :
    TendstoLocallyUniformly (fun n t => finiteDynamics d ℓ (box d n) t A)
      (fun t => dynamics d ℓ t A) Filter.atTop := by
  apply EquicontinuousLimits.locallyUniform
  · intro t
    exact (finiteDynamics_equicontinuous d ℓ A t).comp (fun n => box d n)
  · intro t
    exact dynamics_converges d ℓ t A

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StateCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

namespace Heisenberg

open scoped ComplexOrder

theorem positive_norm_bound {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (φ : E →L[ℂ] ℂ) (hn : φ 1 = 1)
    (hpos : ∀ B, 0 ≤ φ (star B * B)) : ‖φ‖ ≤ 4 := by
  have hp : ∀ A : E, 0 ≤ A → 0 ≤ φ A := by
    intro A hA
    obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
    exact hpos B
  let f : E →ₚ[ℂ] ℂ :=
    { φ.toLinearMap with
      monotone' := by
        intro A B h
        change φ A ≤ φ B
        have h' := hp (B - A) (sub_nonneg.mpr h)
        simpa only [map_sub, sub_nonneg] using h' }
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  obtain ⟨x, hx, hnorm, hA⟩ := CStarAlgebra.exists_sum_four_nonneg A
  conv_lhs => rw [hA, map_sum]
  calc
    ‖∑ i : Fin 4, φ (Complex.I ^ (i : ℕ) • x i)‖ ≤
        ∑ i : Fin 4, ‖φ (Complex.I ^ (i : ℕ) • x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      have hi := PositiveLinearMap.norm_apply_le_of_nonneg f (x i) (hx i)
      change ‖φ (x i)‖ ≤ ‖φ 1‖ * ‖x i‖ at hi
      simpa only [hn, norm_one, one_mul] using hi.trans
        (by simpa only [hn, norm_one, one_mul] using hnorm i)
    _ = 4 * ‖A‖ := by simp

theorem state_norm_bound {d ℓ : ℕ} (ω : State d ℓ) : ‖ω.functional‖ ≤ 4 := by
  let : PartialOrder (QuasiLocal d ℓ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (QuasiLocal d ℓ) := CStarAlgebra.spectralOrderedRing _
  exact positive_norm_bound ω.functional ω.normalized
    (fun B => ⟨(ω.positive B).2, by simpa using (ω.positive B).1.symm⟩)

open scoped InnerProductSpace

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAverageBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma dynamics_continuous (B : QuasiLocal d ℓ) : Continuous (fun t=>dynamics d ℓ t B) :=
  (dynamics_locallyUniform d ℓ B).continuous
    (Filter.Eventually.of_forall (fun n=>(finiteDynamics_equicontinuous d ℓ B).continuous (box d n))).frequently

lemma state_limit_locallyUniform_oai {η : ℕ → State d ℓ} {ω : State d ℓ}
    (hη : ∀ A,Tendsto (fun n=>(η n).functional A) atTop (𝓝 (ω.functional A)))
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ) :
    TendstoLocallyUniformly (fun n t=>(η n).functional (M (dynamics d ℓ t B)))
      (fun t=>ω.functional (M (dynamics d ℓ t B))) atTop := by
  classical
  apply EquicontinuousLimits.locallyUniform
  · apply EquicontinuousLimits.equicontinuous_apply (C:=4) (by norm_num) (fun n=>state_norm_bound (η n))
    intro t
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hh⟩:=Metric.continuousAt_iff.mp (M.continuous.comp (dynamics_continuous B)).continuousAt ε hε
    exact ⟨δ,hδ,fun y hy _=>by rw [dist_comm]; exact hh (by simpa only [dist_comm] using hy)⟩
  · intro t
    exact hη _

end Heisenberg
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.state_limit_locallyUniform_oai := @OAI.Heisenberg.state_limit_locallyUniform_oai
