-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.normal_basis_separation_logarithmic_primitive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:48:06.511042+00:00
-- url     : https://prove2.me/submissions/0c09109e-193e-42ae-816c-eff1b63a5c4a

import Mathlib
import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

section S_E1

open MvPolynomial

namespace PiS36E

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K]
  [Algebra (MvPolynomial σ ℂ) K] [Algebra ℂ K] [IsScalarTower ℂ (MvPolynomial σ ℂ) K]

lemma chain (D : Derivation ℂ K K) (F : MvPolynomial σ ℂ) :
    D (algebraMap (MvPolynomial σ ℂ) K F) =
      ∑ k, algebraMap (MvPolynomial σ ℂ) K (pderiv k F) * D (algebraMap (MvPolynomial σ ℂ) K (X k)) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    have : algebraMap (MvPolynomial σ ℂ) K (C a) = algebraMap ℂ K a := by
      rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial σ ℂ) K]; rfl
    rw [this, Derivation.map_algebraMap]
    simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    rw [map_mul, Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib, pderiv_X]
    have : ∑ k, algebraMap (MvPolynomial σ ℂ) K p *
        algebraMap (MvPolynomial σ ℂ) K (Pi.single (M := fun _ => MvPolynomial σ ℂ) k 1 n) *
        D (algebraMap (MvPolynomial σ ℂ) K (X k)) =
        algebraMap (MvPolynomial σ ℂ) K p * D (algebraMap (MvPolynomial σ ℂ) K (X n)) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
      · simp
    rw [this, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring

lemma totalDegree_pderiv_lt (F : MvPolynomial σ ℂ) (i : σ) (h : pderiv i F ≠ 0) :
    (pderiv i F).totalDegree < F.totalDegree := by
  obtain ⟨s, hs, hdeg⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.2 h)
    (fun s : σ →₀ ℕ => s.sum fun _ e => e)
  rw [totalDegree, hdeg]
  have hc : coeff (s + Finsupp.single i 1) F ≠ 0 := by
    rw [mem_support_iff, coeff_pderiv] at hs
    intro h0; rw [h0, zero_mul] at hs; exact hs rfl
  have := le_totalDegree (mem_support_iff.2 hc)
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at this
  omega

lemma exists_pderiv_ne (F : MvPolynomial σ ℂ) (h : 0 < F.totalDegree) : ∃ i, pderiv i F ≠ 0 := by
  obtain ⟨s, hs, hdeg⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.2 (show F ≠ 0 by
    rintro rfl; simp at h)) (fun s : σ →₀ ℕ => s.sum fun _ e => e)
  have : ∃ i, s i ≠ 0 := by
    by_contra hc; push Not at hc
    have : s = 0 := Finsupp.ext hc
    rw [totalDegree, hdeg, this] at h; simp at h
  obtain ⟨i, hi⟩ := this
  refine ⟨i, fun h0 => ?_⟩
  have := congrArg (coeff (s - Finsupp.single i 1)) h0
  rw [coeff_pderiv, coeff_zero] at this
  have e : s - Finsupp.single i 1 + Finsupp.single i 1 = s := by
    ext j; by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Ne.symm hj]
  rw [e] at this
  rcases mul_eq_zero.1 this with h1 | h1
  · exact (mem_support_iff.1 hs) h1
  · have : (((s - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) + 1 : ℂ) = (((s - Finsupp.single i 1 : σ →₀ ℕ) i + 1 : ℕ) : ℂ) := by push_cast; rfl
    rw [this] at h1; exact (Nat.succ_ne_zero ((s - Finsupp.single i 1 : σ →₀ ℕ) i)) (by exact_mod_cast h1)

/-- A nonzero proper ideal contains an element with a derivative outside it. -/
lemma exists_pderiv_notMem (P : Ideal (MvPolynomial σ ℂ)) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ F ∈ P, ∃ i, pderiv i F ∉ P := by
  by_contra hcon
  push Not at hcon
  have hex : ∃ n, ∃ F ∈ P, F ≠ 0 ∧ F.totalDegree = n := by
    obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    exact ⟨_, F, hF, hF0, rfl⟩
  classical
  let n := Nat.find hex
  obtain ⟨F, hF, hF0, hdeg⟩ := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos F.totalDegree with h0 | h0
  · rw [totalDegree_eq_zero_iff_eq_C] at h0
    have hc : coeff 0 F ≠ 0 := by intro hc; rw [hc, C_0] at h0; exact hF0 h0
    have : IsUnit F := by rw [h0]; exact (isUnit_iff_ne_zero.2 hc).map C
    exact Ideal.IsPrime.ne_top inferInstance (Ideal.eq_top_of_isUnit_mem _ hF this)
  · obtain ⟨i, hi⟩ := exists_pderiv_ne F h0
    have hlt := totalDegree_pderiv_lt F i hi
    have := Nat.find_min' hex ⟨pderiv i F, hcon F hF i, hi, rfl⟩
    omega

end PiS36E

end S_E1

section S_E2

namespace PiS36E

variable {ι K V : Type*} [DecidableEq ι] [Field K] [AddCommGroup V] [Module K V]

lemma greedy (v : ι → V) (U : Finset ι) :
    ∀ T : Finset ι, LinearIndependent K (fun i : (T : Set ι) => v i) →
      ∃ B : Finset ι, T ⊆ B ∧ B ⊆ T ∪ U ∧ LinearIndependent K (fun i : (B : Set ι) => v i) ∧
        Submodule.span K (v '' (B : Set ι)) = Submodule.span K (v '' ((T ∪ U : Finset ι) : Set ι)) := by
  induction U using Finset.induction_on with
  | empty => intro T hT; exact ⟨T, subset_rfl, by simp, hT, by simp⟩
  | insert a U ha ih =>
    intro T hT
    obtain ⟨B0, h1, h2, h3, h4⟩ := ih T hT
    by_cases hva : v a ∈ Submodule.span K (v '' (B0 : Set ι))
    · refine ⟨B0, h1, h2.trans (by intro x; simp; tauto), h3, ?_⟩
      have e : ((T ∪ insert a U : Finset ι) : Set ι) = insert a ((T ∪ U : Finset ι) : Set ι) := by
        ext x; simp
      rw [e, Set.image_insert_eq, Submodule.span_insert, ← h4, sup_eq_right.2]
      rwa [Submodule.span_singleton_le_iff_mem]
    · have haB : a ∉ B0 := fun h => hva (Submodule.subset_span ⟨a, h, rfl⟩)
      refine ⟨insert a B0, h1.trans (Finset.subset_insert _ _), ?_, ?_, ?_⟩
      · intro x hx; rw [Finset.mem_insert] at hx; rcases hx with rfl | hx
        · simp
        · have := h2 hx; simp at this ⊢; tauto
      · rw [Finset.coe_insert]
        refine (linearIndepOn_insert (f := v) (by simpa using haB)).2 ?_
        exact ⟨h3, hva⟩
      · have e : ((T ∪ insert a U : Finset ι) : Set ι) = insert a ((T ∪ U : Finset ι) : Set ι) := by
          ext x; simp
        rw [e, Finset.coe_insert, Set.image_insert_eq, Set.image_insert_eq, Submodule.span_insert,
          Submodule.span_insert, h4]

lemma mem_span_of_rel [Fintype ι] (v : ι → V) (c : ι → K) (h : ∑ k, c k • v k = 0) (i : ι)
    (hc : c i ≠ 0) : v i ∈ Submodule.span K (v '' ((Finset.univ.erase i : Finset ι) : Set ι)) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
  have : v i = -(c i)⁻¹ • ∑ k ∈ Finset.univ.erase i, c k • v k := by
    have h' : ∑ k ∈ Finset.univ.erase i, c k • v k = -(c i • v i) := eq_neg_of_add_eq_zero_right h
    rw [h']; simp [smul_smul, inv_mul_cancel₀ hc]
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨k, hk, rfl⟩

end PiS36E

end S_E2

section S_E3

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace PiS36E

lemma basis_card {m : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v w : Fin (m + 1) → V) (A B : Finset (Fin (m + 1)))
    (hA : LinearIndependent K (fun i : A => v i)) (hB : LinearIndependent K (fun i : B => w i))
    (hs : Submodule.span K (Set.range (fun i : A => v i)) = Submodule.span K (Set.range (fun i : B => w i))) :
    A.card = B.card := by
  have h1 := finrank_span_eq_card hA
  have h2 := finrank_span_eq_card hB
  rw [hs, h2] at h1
  simpa using h1.symm

lemma range_eq_image {ι V : Type*} (v : ι → V) (A : Finset ι) :
    Set.range (fun i : A => v i) = v '' (A : Set ι) := by
  ext x; simp

lemma notMem_of_zero {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V] (v : ι → V)
    (A : Finset ι) (hA : LinearIndependent K (fun i : ((A : Set ι)) => v i)) (j : ι) (hj : v j = 0) :
    j ∉ A := fun h => hA.ne_zero ⟨j, h⟩ hj


lemma span_eq_gen {m : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (col lcol : Fin (m + 1) → V) (y : K) (hy : y ≠ 0)
    (h0 : lcol 0 = y • col 0 + ∑ j : Fin m, col j.succ) (hs : ∀ j : Fin m, lcol j.succ = col j.succ) :
    Submodule.span K (Set.range col) = Submodule.span K (Set.range lcol) := by
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) k
    · have : col 0 = y⁻¹ • (lcol 0 - ∑ j : Fin m, lcol j.succ) := by
        rw [h0]; simp_rw [hs]; rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hy, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨0, rfl⟩)
        (Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨_, rfl⟩))
    · rw [← hs]; exact Submodule.subset_span ⟨_, rfl⟩
  · rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [h0]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨_, rfl⟩)
    · rw [hs]; exact Submodule.subset_span ⟨_, rfl⟩

lemma notin_gen {m : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (col lcol : Fin (m + 1) → V) (i : Fin (m + 1)) (hic : col i ≠ 0)
    (hgt : ∀ j, i < j → col j = 0) (hlgt : ∀ j, i < j → lcol j = 0)
    (hspan : Submodule.span K (Set.range col) = Submodule.span K (Set.range lcol))
    (hex : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      (LinearIndependent K (fun k : A => col k) ∧
        Submodule.span K (Set.range (fun k : A => col k)) = Submodule.span K (Set.range col)) →
      (LinearIndependent K (fun k : B => lcol k) ∧
        Submodule.span K (Set.range (fun k : B => lcol k)) = Submodule.span K (Set.range lcol)) →
      i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    lcol i ∉ Submodule.span K (lcol '' ((Finset.univ.erase i : Finset _) : Set (Fin (m + 1)))) := by
  intro hin
  have hLI1 : LinearIndependent K
      (fun x : (((({i} : Finset (Fin (m + 1))) : Set (Fin (m + 1))))) => col x) := by
    rw [Finset.coe_singleton]; exact (linearIndepOn_singleton_iff _).2 hic
  obtain ⟨A, hA1, -, hA3, hA4⟩ := greedy col Finset.univ _ hLI1
  have hAb : Submodule.span K (Set.range (fun k : A => col k)) = Submodule.span K (Set.range col) := by
    rw [range_eq_image, hA4]; simp [Set.image_univ]
  have hLI0 : LinearIndependent K
      (fun x : (((∅ : Finset (Fin (m + 1))) : Set (Fin (m + 1)))) => lcol x) := by
    rw [Finset.coe_empty]; exact linearIndepOn_empty _ _
  obtain ⟨B, -, hB2, hB3, hB4⟩ := greedy lcol (Finset.univ.erase i) _ hLI0
  have hspanB : Submodule.span K (lcol '' ((Finset.univ.erase i : Finset _) : Set (Fin (m + 1)))) =
      Submodule.span K (Set.range lcol) := by
    apply le_antisymm (Submodule.span_mono (Set.image_subset_range _ _))
    rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩
    by_cases hk : k = i
    · rw [hk]; exact hin
    · exact Submodule.subset_span ⟨k, by simp [hk], rfl⟩
  have hBb : Submodule.span K (Set.range (fun k : B => lcol k)) = Submodule.span K (Set.range lcol) := by
    rw [range_eq_image, hB4, ← hspanB]; simp
  have hcard := basis_card col lcol A B hA3 hB3 (by rw [hAb, hBb, hspan])
  refine hex A B hcard ⟨hA3, hAb⟩ ⟨hB3, hBb⟩ (hA1 (Finset.mem_singleton_self _))
    (fun h => by have := hB2 h; simp at this) (fun j hj => ⟨fun h => ?_, fun h => ?_⟩)
  · exact absurd h (notMem_of_zero _ A hA3 j (hgt j hj))
  · exact absurd h (notMem_of_zero _ B hB3 j (hlgt j hj))

set_option maxHeartbeats 2000000 in
theorem main {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hP : P ≠ ⊥) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hexclusion :
      ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
        coordinateNormalBasisAtPrime P A →
        logarithmicNormalBasisAtPrime P B →
        ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
          (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ z : logarithmicPrimeField P,
      ∀ D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P),
        D z =
          D (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
            (logarithmicPrimeField P) (MvPolynomial.X (0 : Fin (m + 1)))) /
          algebraMap (MvPolynomial (Fin (m + 1)) Complex)
            (logarithmicPrimeField P) (MvPolynomial.X (0 : Fin (m + 1))) := by
  have hι : ∀ F : MvPolynomial (Fin (m + 1)) ℂ,
      algebraMap _ (logarithmicPrimeField P) F = 0 ↔ F ∈ P := by
    intro F
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin (m + 1)) Complex)
      (MvPolynomial (Fin (m + 1)) Complex ⧸ P) (logarithmicPrimeField P)]
    rw [(IsFractionRing.injective (MvPolynomial (Fin (m + 1)) Complex ⧸ P)
      (logarithmicPrimeField P)).eq_iff' (map_zero _)]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hrel : ∀ D : Derivation ℂ (logarithmicPrimeField P) (logarithmicPrimeField P), ∀ F ∈ P,
      ∑ k, algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P) (MvPolynomial.pderiv k F) *
        D (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P) (MvPolynomial.X k)) = 0 := by
    intro D F hF; rw [← chain D F, (hι F).2 hF, map_zero]
  have hy : algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P) (MvPolynomial.X 0) ≠ 0 :=
    fun h => hY ((hι _).1 h)
  have hlc0 : logarithmicNormalColumnAtPrime P 0 =
      algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P) (MvPolynomial.X 0) •
        coordinateNormalColumnAtPrime P 0 + ∑ j : Fin m, coordinateNormalColumnAtPrime P j.succ := by
    funext F
    simp only [logarithmicNormalColumnAtPrime, coordinateNormalColumnAtPrime, logarithmicFrameDerivative,
      Fin.cases_zero, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, map_add, map_mul, map_sum, smul_eq_mul]
  have hlcs : ∀ j : Fin m, logarithmicNormalColumnAtPrime P j.succ = coordinateNormalColumnAtPrime P j.succ := by
    intro j; funext F
    simp only [logarithmicNormalColumnAtPrime, coordinateNormalColumnAtPrime, logarithmicFrameDerivative,
      Fin.cases_succ]
  have hspan : Submodule.span (logarithmicPrimeField P) (Set.range (coordinateNormalColumnAtPrime P)) =
      Submodule.span (logarithmicPrimeField P) (Set.range (logarithmicNormalColumnAtPrime P)) :=
    span_eq_gen _ _ _ hy hlc0 hlcs
  by_cases hcase : ∃ i : Fin (m + 1), i ≠ 0 ∧ coordinateNormalColumnAtPrime P i ≠ 0
  · let S := @Finset.filter _ (fun i : Fin (m + 1) => i ≠ 0 ∧ coordinateNormalColumnAtPrime P i ≠ 0)
      (Classical.decPred _) Finset.univ
    have hS : S.Nonempty := by
      obtain ⟨i, h⟩ := hcase; exact ⟨i, by simp [S, h]⟩
    have hiS := S.max'_mem hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hiS
    obtain ⟨hi0, hic⟩ := hiS
    have hgt : ∀ j, S.max' hS < j → coordinateNormalColumnAtPrime P j = 0 := by
      intro j hj; by_contra hne
      have hj0 : j ≠ 0 := by
        intro h; rw [h] at hj; exact absurd hj (Fin.not_lt_zero _)
      have : j ≤ S.max' hS := S.le_max' j (by simp [S, hne, hj0])
      exact absurd hj (not_lt.2 this)
    have hlgt : ∀ j, S.max' hS < j → logarithmicNormalColumnAtPrime P j = 0 := by
      intro j hj
      have hj0 : j ≠ 0 := by
        intro h; rw [h] at hj; exact absurd hj (Fin.not_lt_zero _)
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj0
      rw [hlcs]; exact hgt _ hj
    have hnotin : logarithmicNormalColumnAtPrime P (S.max' hS) ∉
        Submodule.span (logarithmicPrimeField P)
          (logarithmicNormalColumnAtPrime P '' ((Finset.univ.erase (S.max' hS) : Finset _) : Set (Fin (m + 1)))) :=
      notin_gen _ _ _ hic hgt hlgt hspan (fun A B hc hA hB => hexclusion A B hc hA hB _ hi0)
    obtain ⟨i', hi'⟩ := Fin.exists_succ_eq.2 hi0
    refine ⟨algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P) (MvPolynomial.X i'.succ),
      fun D => ?_⟩
    obtain ⟨y, hydef⟩ : ∃ y, y = algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P)
        (MvPolynomial.X 0) := ⟨_, rfl⟩
    rw [← hydef]
    rw [← hydef] at hy hlc0
    let c : Fin (m + 1) → logarithmicPrimeField P := Matrix.vecCons (D y / y)
      (fun j : Fin m => D (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P)
        (MvPolynomial.X j.succ)) - D y / y)
    have hsum : ∑ k, c k • logarithmicNormalColumnAtPrime P k = 0 := by
      funext F
      have := hrel D F F.2
      rw [Fin.sum_univ_succ] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [Fin.sum_univ_succ]
      simp only [c, Matrix.cons_val_zero, Matrix.cons_val_succ, hlc0, hlcs, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_apply]
      simp only [coordinateNormalColumnAtPrime]
      rw [← hydef] at this
      have e : D y / y * (y * (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P))
          ((MvPolynomial.pderiv 0) (F : MvPolynomial (Fin (m + 1)) ℂ))) =
          (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P))
            ((MvPolynomial.pderiv 0) (F : MvPolynomial (Fin (m + 1)) ℂ)) * D y := by
        field_simp
      rw [mul_add, e, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
      rw [← this]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    have hc : c i'.succ = 0 := by
      by_contra hne
      rw [hi'] at hne
      exact hnotin (mem_span_of_rel _ c hsum _ hne)
    simp only [c, Matrix.cons_val_succ] at hc
    exact sub_eq_zero.1 hc
  · push Not at hcase
    obtain ⟨F, hF, k, hk⟩ := exists_pderiv_notMem P hP
    have hk0 : k = 0 := by
      by_contra h
      have := congrFun (hcase k h) ⟨F, hF⟩
      simp only [coordinateNormalColumnAtPrime, Pi.zero_apply] at this
      exact hk ((hι _).1 this)
    subst hk0
    refine ⟨0, fun D => ?_⟩
    have := hrel D F hF
    rw [Fin.sum_univ_succ] at this
    have hz : ∀ j : Fin m, algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P)
        (MvPolynomial.pderiv j.succ F) = 0 := by
      intro j
      have := congrFun (hcase j.succ (Fin.succ_ne_zero j)) ⟨F, hF⟩
      simp only [coordinateNormalColumnAtPrime, Pi.zero_apply] at this
      exact this
    simp only [hz, zero_mul, Finset.sum_const_zero, add_zero] at this
    have hne : algebraMap (MvPolynomial (Fin (m + 1)) ℂ) (logarithmicPrimeField P)
        (MvPolynomial.pderiv 0 F) ≠ 0 := fun h => hk ((hι _).1 h)
    have hDy := (mul_eq_zero.1 this).resolve_left hne
    rw [hDy, D.map_zero, zero_div]

end PiS36E

end S_E3

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hP : P ≠ ⊥) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hexclusion :
      ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
        coordinateNormalBasisAtPrime P A →
        logarithmicNormalBasisAtPrime P B →
        ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
          (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ z : logarithmicPrimeField P,
      ∀ D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P),
        D z =
          D (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
            (logarithmicPrimeField P) (MvPolynomial.X (0 : Fin (m + 1)))) /
          algebraMap (MvPolynomial (Fin (m + 1)) Complex)
            (logarithmicPrimeField P) (MvPolynomial.X (0 : Fin (m + 1))) :=
  PiS36E.main P hP hY hexclusion
