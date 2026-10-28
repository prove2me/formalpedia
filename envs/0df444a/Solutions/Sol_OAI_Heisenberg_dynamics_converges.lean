-- Prove2me | solution 1 for OAI.Heisenberg.dynamics_converges
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:38:28.846014+00:00
-- url     : https://prove2.me/submissions/b9666565-4e72-4e32-99ee-6a2741ba5f96

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM002

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

lemma exp_time_add (d ℓ : ℕ) (Λ : Finset (Site d)) (s t : ℝ) :
    NormedSpace.exp ((Complex.I * ((s + t : ℝ) : ℂ)) • hamiltonian d ℓ Λ) =
      NormedSpace.exp ((Complex.I * (s : ℂ)) • hamiltonian d ℓ Λ) *
      NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ) := by
  rw [Complex.ofReal_add, mul_add, add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl _).smul_left _ |>.smul_right _)

lemma exp_time_neg (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((Complex.I * ((-t : ℝ) : ℂ)) • hamiltonian d ℓ Λ) =
      NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ) := by
  simp

theorem finiteDynamics_group (d ℓ : ℕ) (Λ : Finset (Site d)) (s t : ℝ) (A : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ (s + t) A =
      finiteDynamics d ℓ Λ s (finiteDynamics d ℓ Λ t A) := by
  simp only [finiteDynamics, ← exp_time_neg, neg_add_rev, exp_time_add]
  simp only [mul_assoc]

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem LocalDecomposition.power_bound {D : E →L[ℂ] E} {Local : ℕ → E → Prop}
    {C : ℝ} (h : LocalDecomposition D Local C) (n k : ℕ) (A : E) (hA : Local k A) :
    ‖(D^n) A‖ ≤ C^n * ((k+1).ascFactorial n : ℝ) * ‖A‖ := by
  induction n generalizing k A with
  | zero => simp
  | succ n ih =>
    obtain ⟨r, g, hsum, hloc, hnorm⟩ := h.split k A hA
    have hc : 0 ≤ C^n * ((k+2).ascFactorial n : ℝ) := mul_nonneg (pow_nonneg h.nonneg _) (Nat.cast_nonneg _)
    calc
      ‖(D^(n+1)) A‖ = ‖∑ i, (D^n) (g i)‖ := by
        rw [pow_succ, mul_apply_eq_comp, hsum, map_sum]
      _ ≤ ∑ i, ‖(D^n) (g i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, C^n * ((k+2).ascFactorial n : ℝ) * ‖g i‖ :=
        Finset.sum_le_sum (fun i _ => ih (k+1) (g i) (hloc i))
      _ = (C^n * ((k+2).ascFactorial n : ℝ)) * ∑ i, ‖g i‖ := by
        rw [Finset.mul_sum]
      _ ≤ (C^n * ((k+2).ascFactorial n : ℝ)) * (C*(k+1)*‖A‖) :=
        mul_le_mul_of_nonneg_left hnorm hc
      _ = C^(n+1) * ((k+1).ascFactorial (n+1) : ℝ) * ‖A‖ := by
        rw [Nat.ascFactorial_succ, ← Nat.succ_ascFactorial]
        push_cast
        ring

lemma summable_ascFactorial {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    Summable (fun n : ℕ => q^n * ((k+1).ascFactorial n : ℝ) / n.factorial) := by
  have heq (n : ℕ) : q^n * ((k+1).ascFactorial n : ℝ) / n.factorial =
      ((k+n).choose k : ℝ) * q^n := by
    rw [Nat.ascFactorial_eq_factorial_mul_choose, ← Nat.choose_symm_add]
    push_cast
    field_simp
  simp_rw [heq]
  have hs : Summable (fun n : ℕ => ((k+n : ℕ) : ℝ)^k * q^n) := by
    have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
    have hs (j : ℕ) : Summable (fun n : ℕ =>
        ((k : ℝ)^j * (k.choose j : ℝ)) * ((n : ℝ)^(k-j) * q^n)) :=
      (summable_pow_mul_geometric_of_norm_lt_one (k-j) hqnorm).mul_left _
    convert (summable_sum (s := Finset.range (k+1)) (fun j _ => hs j)) using 1
    ext n
    rw [Nat.cast_add, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow (k+n) k)
      (pow_nonneg hq n)) hs

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

lemma subset_neighborhood {d : ℕ} (F : Finset (Site d)) : F ⊆ neighborhood F :=
  Finset.subset_union_left

lemma nearestNeighbor_mem_neighborhood {d : ℕ} {F : Finset (Site d)} {x y : Site d}
    (h : NearestNeighbor x y) (hm : x ∈ F ∨ y ∈ F) :
    x ∈ neighborhood F ∧ y ∈ neighborhood F := by
  rcases hm with hx | hy
  · exact ⟨subset_neighborhood F hx, Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨x, hx, mem_neighbors_of_nearestNeighbor h⟩)⟩
  · exact ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨y, hy, mem_neighbors_of_nearestNeighbor (nearestNeighbor_symm h)⟩),
      subset_neighborhood F hy⟩

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



lemma activeEdges_stable {d : ℕ} (Λ F : Finset (Site d))
    (hΛ : neighborhood F ⊆ Λ) : activeEdges Λ F = activeEdges (neighborhood F) F := by
  ext e
  simp only [activeEdges, volumeEdges, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hmem,hnn,hord⟩,hm⟩
    exact ⟨⟨nearestNeighbor_mem_neighborhood hnn hm,hnn,hord⟩,hm⟩
  · rintro ⟨⟨hmem,hnn,hord⟩,hm⟩
    exact ⟨⟨⟨hΛ hmem.1,hΛ hmem.2⟩,hnn,hord⟩,hm⟩

lemma finiteGenerator_stable {d ℓ : ℕ} (Λ F : Finset (Site d))
    (hΛ : neighborhood F ⊆ Λ) {A : QuasiLocal d ℓ}
    (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) :
    finiteGenerator d ℓ Λ A = finiteGenerator d ℓ (neighborhood F) A := by
  rw [finiteGenerator_eq_activeSum Λ F hA,
    finiteGenerator_eq_activeSum (neighborhood F) F hA, activeEdges_stable Λ F hΛ]

lemma finiteGenerator_local {d ℓ : ℕ} (Λ F : Finset (Site d))
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) :
    finiteGenerator d ℓ Λ A ∈ localAlgebra d ℓ (↑(F ∪ Λ) : Set (Site d)) := by
  rw [finiteGenerator_eq_activeSum Λ F hA]
  apply Subalgebra.sum_mem
  intro e he
  have hv : e.1 ∈ Λ ∧ e.2 ∈ Λ :=
    Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
  apply localAlgebra_mono (F := (↑(F ∪ {e.1,e.2}) : Set (Site d))) ?_ (commutatorTerm_mem e hA)
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with hF | rfl | rfl
  · exact Or.inl hF
  · exact Or.inr hv.1
  · exact Or.inr hv.2

theorem eventually_mem_box {d : ℕ} (x : Site d) :
    ∀ᶠ n : ℕ in Filter.atTop, x ∈ box d n := by
  have hl (i : Fin d) : ∀ᶠ n : ℕ in Filter.atTop, (x i).natAbs ≤ n :=
    Filter.eventually_ge_atTop _
  have hh := (Filter.eventually_all).mpr hl
  filter_upwards [hh] with n hn
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h := hn i
  have hcast : ((x i).natAbs : ℤ) ≤ n := by exact_mod_cast h
  exact abs_le.mp (by simpa only [Int.natCast_natAbs] using hcast)

lemma eventually_subset_box {d : ℕ} (F : Finset (Site d)) :
    ∀ᶠ n : ℕ in Filter.atTop, F ⊆ box d n := by
  have h : ∀ x : F, ∀ᶠ n : ℕ in Filter.atTop, (x : Site d) ∈ box d n :=
    fun x => eventually_mem_box (x : Site d)
  filter_upwards [Filter.eventually_all.mpr h] with n hn
  intro x hx
  exact hn ⟨x,hx⟩

theorem local_coefficients_stabilize {d ℓ : ℕ} (F : Finset (Site d))
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) (n : ℕ) :
    ∃ B : QuasiLocal d ℓ, ∀ᶠ m : ℕ in Filter.atTop,
      ((finiteGenerator d ℓ (box d m))^n) A = B := by
  let : Monoid (QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) := inferInstance
  have hh : ∀ n : ℕ, ∃ (G : Finset (Site d)) (B : QuasiLocal d ℓ),
      B ∈ localAlgebra d ℓ (G : Set (Site d)) ∧
      ∀ᶠ m : ℕ in Filter.atTop, ((finiteGenerator d ℓ (box d m))^n) A = B := by
    intro n
    induction n with
    | zero => exact ⟨F,A,hA,by simp⟩
    | succ n ih =>
      obtain ⟨G,B,hB,hlim⟩ := ih
      refine ⟨G ∪ neighborhood G,finiteGenerator d ℓ (neighborhood G) B,
        finiteGenerator_local _ G hB,?_⟩
      filter_upwards [hlim,eventually_subset_box (neighborhood G)] with m hm hmG
      rw [pow_succ', mul_apply_eq_comp, hm]
      exact finiteGenerator_stable _ G hmG hB
  obtain ⟨G,B,hB,hlim⟩ := hh n
  exact ⟨B,hlim⟩

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

namespace SpinEvolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [CompleteSpace E]

omit [CompleteSpace E] in
lemma smul_operator_pow_apply (D : E →L[ℂ] E) (z : ℂ) (n : ℕ) (A : E) :
    ((z • D)^n) A = z^n • (D^n) A := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', mul_apply_eq_comp, smul_apply, ih, map_smul, smul_smul]
    rw [mul_comm]

lemma exponential_operator_series (D : E →L[ℂ] E) (z : ℂ) (A : E) :
    NormedSpace.exp (z • D) A =
      ∑' n : ℕ, ((n.factorial : ℂ)⁻¹ * z^n) • (D^n) A := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  change (ContinuousLinearMap.apply ℂ E A) (∑' n : ℕ,
    (n.factorial : ℂ)⁻¹ • (z • D)^n) = _
  rw [(ContinuousLinearMap.apply ℂ E A).map_tsum
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) (z • D))]
  apply tsum_congr
  intro n
  simp only [ContinuousLinearMap.apply_apply, smul_apply, smul_operator_pow_apply, smul_smul]

theorem local_exponential_converges (D : ℕ → E →L[ℂ] E) (Local : ℕ → E → Prop)
    (C : ℝ) (hD : ∀ m, LocalDecomposition (D m) Local C)
    (k : ℕ) (A : E) (hA : Local k A) (z : ℂ) (hz : ‖z‖*C < 1)
    (hstable : ∀ n : ℕ, ∃ B : E, ∀ᶠ m : ℕ in Filter.atTop, ((D m)^n) A = B) :
    ∃ B : E, Filter.Tendsto (fun m => NormedSpace.exp (z • D m) A)
      Filter.atTop (nhds B) := by
  choose B hB using hstable
  have hc : 0 ≤ C := (hD 0).nonneg
  let q : ℝ := ‖z‖*C
  have hq : 0 ≤ q := mul_nonneg (norm_nonneg _) hc
  let b : ℕ → ℝ := fun n => q^n * ((k+1).ascFactorial n : ℝ) / n.factorial * ‖A‖
  have hb : Summable b := (summable_ascFactorial hq hz k).mul_right ‖A‖
  have hterm (m n : ℕ) : ‖((n.factorial : ℂ)⁻¹ * z^n) • ((D m)^n) A‖ ≤ b n := by
    calc
      _ = ((n.factorial : ℝ)⁻¹ * ‖z‖^n) * ‖((D m)^n) A‖ := by
        simp only [norm_smul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
      _ ≤ ((n.factorial : ℝ)⁻¹ * ‖z‖^n) *
          (C^n * ((k+1).ascFactorial n : ℝ) * ‖A‖) :=
        mul_le_mul_of_nonneg_left ((hD m).power_bound n k A hA) (by positivity)
      _ = b n := by dsimp [b, q]; rw [mul_pow]; ring
  refine ⟨∑' n : ℕ, ((n.factorial : ℂ)⁻¹*z^n) • B n, ?_⟩
  simp_rw [exponential_operator_series]
  apply tendsto_tsum_of_dominated_convergence hb
  · intro n
    apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hB n] with m hm
    exact congrArg (fun X => ((n.factorial : ℂ)⁻¹*z^n) • X) hm.symm
  · exact Filter.Eventually.of_forall hterm

end SpinEvolution
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

namespace IsometricLimits
variable {E : Type*} [MetricSpace E] [CompleteSpace E]

theorem limit_on_dense (F : ℕ → E → E) (hF : ∀ n, Isometry (F n))
    (s : Set E) (hs : Dense s)
    (hlim : ∀ x ∈ s, ∃ y, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds y)) :
    ∀ x, ∃ y, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds y) := by
  intro x
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨a, ha, hax⟩ := hs.exists_dist_lt x (by linarith : 0 < ε/3)
  obtain ⟨b, hb⟩ := hlim a ha
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hb.cauchySeq (ε/3) (by linarith)
  refine ⟨N, fun n hn m hm => ?_⟩
  calc
    dist (F n x) (F m x) ≤ dist (F n x) (F n a) + dist (F n a) (F m a) +
        dist (F m a) (F m x) := dist_triangle4 _ _ _ _
    _ = dist x a + dist (F n a) (F m a) + dist a x := by
      rw [(hF n).dist_eq, (hF m).dist_eq]
    _ < ε := by have := hN n hn m hm; rw [dist_comm a x]; linarith

omit [CompleteSpace E] in

theorem limit_iterate (F : ℕ → E → E) (f : E → E) (hF : ∀ n, Isometry (F n))
    (hlim : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (k : ℕ) (x : E) :
    Filter.Tendsto (fun n => (F n)^[k] x) Filter.atTop (nhds (f^[k] x)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum := (tendsto_iff_dist_tendsto_zero.mp ih).add
      (tendsto_iff_dist_tendsto_zero.mp (hlim (f^[k] x)))
    rw [add_zero] at hsum
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) ?_ hsum
    intro n
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      _ ≤ dist (F n ((F n)^[k] x)) (F n (f^[k] x)) +
          dist (F n (f^[k] x)) (f (f^[k] x)) := dist_triangle _ _ _
      _ = _ := by rw [(hF n).dist_eq]

omit [CompleteSpace E] in

theorem all_times (g : ℕ → ℝ → E → E)
    (hg : ∀ n t, Isometry (g n t))
    (hzero : ∀ n x, g n 0 x = x)
    (hadd : ∀ n s t x, g n (s+t) x = g n s (g n t x))
    (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ∀ t : ℝ, |t| < δ → ∀ x, ∃ y,
      Filter.Tendsto (fun n => g n t x) Filter.atTop (nhds y)) :
    ∀ t : ℝ, ∀ x, ∃ y, Filter.Tendsto (fun n => g n t x) Filter.atTop (nhds y) := by
  intro t x
  obtain ⟨N, hN⟩ := exists_nat_gt (|t|/δ)
  have hN0 : (0 : ℝ) < N := (div_nonneg (abs_nonneg _) hδ.le).trans_lt hN
  let a : ℝ := t/N
  have ha : |a| < δ := by
    dsimp [a]
    rw [abs_div, abs_of_pos hN0, div_lt_iff₀ hN0]
    have := (div_lt_iff₀ hδ).mp hN
    nlinarith
  choose f hf using hsmall a ha
  have hi (n k : ℕ) (x : E) : (g n a)^[k] x = g n ((k : ℝ)*a) x := by
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      have heq : ((k+1 : ℕ) : ℝ)*a = a+(k : ℝ)*a := by push_cast; ring
      rw [heq, hadd]
  refine ⟨f^[N] x, ?_⟩
  have hh := limit_iterate (fun n => g n a) f (fun n => hg n a) hf N x
  simpa only [hi, a, mul_div_cancel₀ t (ne_of_gt hN0)] using hh

end IsometricLimits

namespace Heisenberg

attribute [local instance] OAI.Heisenberg.instIsTopologicalRingContinuousLinearMapComplexIdSubtypeSpinOperatorMemStarSubalgebraQuasiLocal
lemma finiteDynamics_generator (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t A = NormedSpace.exp ((t : ℂ) • finiteGenerator d ℓ Λ) A := by
  rw [finiteGenerator, SpinEvolution.exp_generator]
  simp only [finiteDynamics, mul_comm (t : ℂ) Complex.I]

theorem dynamics_converges_oai (d ℓ : ℕ) : DynamicsConverges d ℓ := by
  let C : ℝ := 8*d*bondBound d ℓ
  have hC : 0 ≤ C := (finiteGenerator_localDecomposition d ℓ (box d 0)).nonneg
  let δ : ℝ := 1/(C+1)
  have hδ : 0 < δ := one_div_pos.mpr (by linarith)
  have hs : ∀ t : ℝ, |t| < δ → ∀ A : QuasiLocal d ℓ, ∃ B,
      Filter.Tendsto (fun n => finiteDynamics d ℓ (box d n) t A) Filter.atTop (nhds B) := by
    intro t ht
    apply IsometricLimits.limit_on_dense (fun n => finiteDynamics d ℓ (box d n) t)
      (fun n => finiteDynamics_isometry _ _ _ _) (localCore d ℓ) (localCore_dense d ℓ)
    intro A hA
    obtain ⟨F,hF⟩ := localCore_finite_support hA
    have hz : ‖(t : ℂ)‖*C < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h := (lt_div_iff₀ (by linarith : 0 < C+1)).mp ht
      nlinarith [abs_nonneg t]
    have hh := SpinEvolution.local_exponential_converges
      (fun n => finiteGenerator d ℓ (box d n)) (SupportedOnAtMost d ℓ) C
      (fun n => finiteGenerator_localDecomposition d ℓ (box d n)) F.card A
      ⟨F,Nat.le_succ _,hF⟩ (t : ℂ) hz (local_coefficients_stabilize F hF)
    simpa only [← finiteDynamics_generator] using hh
  have hall := IsometricLimits.all_times (fun n => finiteDynamics d ℓ (box d n))
    (fun n t => finiteDynamics_isometry _ _ _ _)
    (fun n A => finiteDynamics_zero _ _ _ _)
    (fun n s t A => finiteDynamics_group _ _ _ _ _ _) δ hδ hs
  intro t A
  exact tendsto_nhds_limUnder (hall t A)

end Heisenberg

open Filter Topology Metric
open scoped NNReal

open scoped NNReal
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.dynamics_converges_oai := @OAI.Heisenberg.dynamics_converges_oai
