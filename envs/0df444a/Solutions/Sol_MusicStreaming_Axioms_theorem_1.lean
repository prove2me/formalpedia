-- Prove2me | solution 1 for MusicStreaming.Axioms.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T14:27:01.110287+00:00
-- url     : https://prove2.me/submissions/35c53fbb-f4be-426b-b0cd-3288fd8cc3dd

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

set_option autoImplicit false

namespace MSA41

open MusicStreaming.Axioms

lemma idx_zero {n : ℕ} {I : Index n} (hA : Additivity I) : I 0 = 0 := by
  have h := hA 0 0 (by simp)
  funext i
  have h2 := congrFun h i
  simp only [add_zero, Pi.add_apply] at h2
  simp only [Pi.zero_apply]
  linarith

lemma add_ext {n : ℕ} {I J : Index n} (hI : Additivity I) (hJ : Additivity J)
    (hs : ∀ (j : ℕ) (x : Fin n → ℕ), x ≠ 0 → I (Finsupp.single j x) = J (Finsupp.single j x)) :
    ∀ t, I t = J t := by
  intro t
  induction t using Finsupp.induction with
  | zero => rw [idx_zero hI, idx_zero hJ]
  | single_add a b f ha hb ih =>
    have hd : Disjoint (Finsupp.single a b).support f.support := by
      rw [Finsupp.support_single a hb, Finset.disjoint_singleton_left]; exact ha
    rw [hI _ _ hd, hJ _ _ hd, hs a b hb, ih]

lemma weighted_add {n : ℕ} (ω : ℕ → (Fin n → ℕ) → ℝ) : Additivity (weightedIndex ω) := by
  classical
  intro t₁ t₂ hd
  funext i
  simp only [weightedIndex, Pi.add_apply]
  rw [Finsupp.support_add_eq hd, Finset.sum_union hd]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have : t₂ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hd hj)
    simp [this]
  · apply Finset.sum_congr rfl
    intro j hj
    have : t₁ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hd hj)
    simp [this]

lemma weighted_hom {n : ℕ} (ω : ℕ → (Fin n → ℕ) → ℝ) : Homogeneity (weightedIndex ω) := by
  intro t i i' c _ h
  simp only [weightedIndex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j hj]; ring

lemma weighted_single {n : ℕ} (ω : ℕ → (Fin n → ℕ) → ℝ) (j : ℕ) (x : Fin n → ℕ) (i : Fin n) :
    weightedIndex ω (Finsupp.single j x) i = ω j x * x i := by
  by_cases hx : x = 0
  · subst hx; simp [weightedIndex]
  · simp [weightedIndex, Finsupp.support_single j hx]

lemma smul_weighted {n : ℕ} (ω : ℕ → (Fin n → ℕ) → ℝ) (c : ℝ) (t : Problem n) :
    c • weightedIndex ω t = weightedIndex (fun j x => c * ω j x) t := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, weightedIndex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma proRata_eq {n : ℕ} (t : Problem n) :
    (proRata t : Fin n → ℝ) = weightedIndex (fun (_ : ℕ) (_ : Fin n → ℕ) => (1 : ℝ)) t := by
  funext i
  simp [proRata, artistTotal, weightedIndex]

lemma userCentric_eq {n : ℕ} (t : Problem n) :
    (userCentric t : Fin n → ℝ) =
      weightedIndex (fun (_ : ℕ) (x : Fin n → ℕ) => 1 / ∑ i, (x i : ℝ)) t := by
  funext i
  simp only [userCentric, weightedIndex, userTotal]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

noncomputable def lam {n : ℕ} (I : Index n) (j : ℕ) (x : Fin n → ℕ) : ℝ :=
  (∑ i, I (Finsupp.single j x) i) / (∑ i, (x i : ℝ))

lemma sum_pos_of_ne {n : ℕ} (x : Fin n → ℕ) (hx : x ≠ 0) : 0 < ∑ i, (x i : ℝ) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hx
  simp only [Pi.zero_apply] at hi0
  have h1 : (0 : ℝ) < x i0 := by exact_mod_cast Nat.pos_of_ne_zero hi0
  exact lt_of_lt_of_le h1
    (Finset.single_le_sum (f := fun i => (x i : ℝ)) (fun i _ => Nat.cast_nonneg _)
      (Finset.mem_univ i0))

lemma hom_single {n : ℕ} {I : Index n} (hH : Homogeneity I) (j : ℕ) (x : Fin n → ℕ)
    (hx : x ≠ 0) (i : Fin n) : I (Finsupp.single j x) i = lam I j x * x i := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hx
  simp only [Pi.zero_apply] at hi0
  have hx0 : (0 : ℝ) < x i0 := by exact_mod_cast Nat.pos_of_ne_zero hi0
  have key : ∀ k, I (Finsupp.single j x) k = (I (Finsupp.single j x) i0 / x i0) * x k := by
    intro k
    have := hH (Finsupp.single j x) k i0 ((x k : ℝ) / x i0) (by positivity) (by
      intro j' hj'
      rw [Finsupp.support_single j hx, Finset.mem_singleton] at hj'
      rw [hj', Finsupp.single_eq_same]
      exact (div_mul_cancel₀ _ hx0.ne').symm)
    rw [this]; ring
  have hS := sum_pos_of_ne x hx
  have hsum : ∑ k, I (Finsupp.single j x) k
      = (I (Finsupp.single j x) i0 / x i0) * ∑ k, (x k : ℝ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => key k)
  unfold lam
  rw [hsum, mul_div_assoc, div_self hS.ne', mul_one]
  exact key i

lemma lam_pos {n : ℕ} {I : Index n} (hI : IsIndex I) (j : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0) :
    0 < lam I j x :=
  div_pos (hI _ (Finsupp.single_ne_zero.mpr hx)).2 (sum_pos_of_ne x hx)

lemma partA {n : ℕ} (I : Index n) (hI : IsIndex I) :
    (Homogeneity I ∧ Additivity I ↔
      ∃ ω : ℕ → (Fin n → ℕ) → ℝ, (∀ j x, 0 < ω j x) ∧ ∀ t, I t = weightedIndex ω t) := by
  classical
  constructor
  · rintro ⟨hH, hA⟩
    refine ⟨fun j x => if x = 0 then 1 else lam I j x, ?_, ?_⟩
    · intro j x
      dsimp only
      split_ifs with h
      · exact one_pos
      · exact lam_pos hI j x h
    · apply add_ext hA (weighted_add _)
      intro j x hx
      funext i
      rw [weighted_single, hom_single hH j x hx i]
      simp [hx]
  · rintro ⟨ω, -, hω⟩
    have : I = weightedIndex ω := funext hω
    subst this
    exact ⟨weighted_hom ω, weighted_add ω⟩

lemma weighted_erase {n : ℕ} (ω : ℕ → (Fin n → ℕ) → ℝ) (t : Problem n) (j : ℕ)
    (hj : j ∈ t.support) (i : Fin n) :
    weightedIndex ω (t.erase j) i = weightedIndex ω t i - ω j (t j) * t j i := by
  classical
  simp only [weightedIndex]
  rw [Finsupp.support_erase]
  have h1 : ∑ k ∈ t.support.erase j, ω k ((t.erase j) k) * ((t.erase j) k i : ℝ)
      = ∑ k ∈ t.support.erase j, ω k (t k) * (t k i : ℝ) :=
    Finset.sum_congr rfl (fun k hk => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hk)])
  rw [h1, Finset.sum_erase_eq_sub hj]

lemma proRata_EII {n : ℕ} (c : ℝ) :
    EqualIndividualImpact (weightedIndex (fun (_ : ℕ) (_ : Fin n → ℕ) => c)) := by
  intro t i j j' hj hj' h
  rw [weighted_erase _ t j hj, weighted_erase _ t j' hj', h]

lemma uc_EGI {n : ℕ} (c : ℝ) :
    EqualGlobalImpact
      (weightedIndex (fun (_ : ℕ) (x : Fin n → ℕ) => c * (1 / ∑ i, (x i : ℝ)))) := by
  intro t j j' hj hj'
  have key : ∀ k ∈ t.support,
      ∑ i, weightedIndex (fun (_ : ℕ) (x : Fin n → ℕ) => c * (1 / ∑ i, (x i : ℝ))) (t.erase k) i
        = ∑ i, weightedIndex (fun (_ : ℕ) (x : Fin n → ℕ) => c * (1 / ∑ i, (x i : ℝ))) t i - c := by
    intro k hk
    have hS := sum_pos_of_ne (t k) (Finsupp.mem_support_iff.mp hk)
    simp only [weighted_erase _ t k hk, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.mul_sum]
    field_simp
  rw [key j hj, key j' hj']

lemma two_users {n : ℕ} (j j' : ℕ) (hjj : j ≠ j') (x y : Fin n → ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ t : Problem n, j ∈ t.support ∧ j' ∈ t.support ∧ t j = x ∧ t j' = y ∧
      t.erase j = Finsupp.single j' y ∧ t.erase j' = Finsupp.single j x := by
  refine ⟨Finsupp.single j x + Finsupp.single j' y, ?_⟩
  have tj : (Finsupp.single j x + Finsupp.single j' y) j = x := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hjj, add_zero]
  have tj' : (Finsupp.single j x + Finsupp.single j' y) j' = y := by
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hjj.symm, Finsupp.single_eq_same, zero_add]
  refine ⟨?_, ?_, tj, tj', ?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tj]; exact hx
  · rw [Finsupp.mem_support_iff, tj']; exact hy
  · rw [Finsupp.erase_add, Finsupp.erase_single, Finsupp.erase_single_ne hjj, zero_add]
  · rw [Finsupp.erase_add, Finsupp.erase_single_ne hjj.symm, Finsupp.erase_single, add_zero]

lemma eii_step {n : ℕ} {I : Index n} (hH : Homogeneity I) (hE : EqualIndividualImpact I)
    (j j' : ℕ) (hjj : j ≠ j') (x y : Fin n → ℕ) (hx : x ≠ 0) (hy : y ≠ 0) (i : Fin n)
    (hxy : x i = y i) (hpos : 0 < x i) : lam I j x = lam I j' y := by
  obtain ⟨t, hjm, hjm', tj, tj', e1, e2⟩ := two_users j j' hjj x y hx hy
  have := hE t i j j' hjm hjm' (by rw [tj, tj', hxy])
  rw [e1, e2, hom_single hH j' y hy i, hom_single hH j x hx i, ← hxy] at this
  have hx' : (0 : ℝ) < x i := by exact_mod_cast hpos
  exact (mul_right_cancel₀ hx'.ne' this).symm

lemma eii_const {n : ℕ} (hn : 2 ≤ n) {I : Index n} (hH : Homogeneity I)
    (hE : EqualIndividualImpact I) (j : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0) :
    lam I j x = lam I 0 (fun _ => 1) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  simp only [Pi.zero_apply] at hi
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨k, hk⟩ := exists_ne i
  let y : Fin n → ℕ := Function.update (fun _ => 1) i (x i)
  have hyi : y i = x i := by simp [y]
  have hyk : y k = 1 := by simp [y, hk]
  have hy : y ≠ 0 := fun h => by
    have := congrFun h k
    rw [hyk] at this
    simp at this
  have e_ne : (fun _ : Fin n => (1 : ℕ)) ≠ 0 := fun h => by
    have := congrFun h k
    simp at this
  have s1 : lam I j x = lam I (j + 1) y :=
    eii_step hH hE j (j + 1) (by omega) x y hx hy i hyi.symm (Nat.pos_of_ne_zero hi)
  have s2 : lam I (j + 1) y = lam I (j + 2) (fun _ => 1) :=
    eii_step hH hE (j + 1) (j + 2) (by omega) y _ hy e_ne k (by rw [hyk]) (by rw [hyk]; exact Nat.one_pos)
  have s3 : lam I (j + 2) (fun _ => 1) = lam I 0 (fun _ => 1) :=
    eii_step hH hE (j + 2) 0 (by omega) _ _ e_ne e_ne k rfl Nat.one_pos
  rw [s1, s2, s3]

lemma partB_fwd {n : ℕ} (hn : 2 ≤ n) {I : Index n} (hI : IsIndex I) (hH : Homogeneity I)
    (hA : Additivity I) (hE : EqualIndividualImpact I) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, I t = c • proRata t := by
  have e_ne : (fun _ : Fin n => (1 : ℕ)) ≠ 0 := fun h => by
    have := congrFun h ⟨0, by omega⟩
    simp at this
  refine ⟨lam I 0 (fun _ => 1), lam_pos hI 0 _ e_ne, ?_⟩
  have hW : ∀ t, I t =
      weightedIndex (fun (_ : ℕ) (_ : Fin n → ℕ) => lam I 0 (fun _ => 1) * 1) t := by
    apply add_ext hA (weighted_add _)
    intro j x hx
    funext i
    rw [weighted_single, hom_single hH j x hx i, eii_const hn hH hE j x hx]
    ring
  intro t
  rw [hW t, proRata_eq, smul_weighted]

lemma egi_step {n : ℕ} {I : Index n} (hE : EqualGlobalImpact I) (j j' : ℕ) (hjj : j ≠ j')
    (x y : Fin n → ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∑ i, I (Finsupp.single j x) i = ∑ i, I (Finsupp.single j' y) i := by
  obtain ⟨t, hjm, hjm', _, _, e1, e2⟩ := two_users j j' hjj x y hx hy
  have := hE t j j' hjm hjm'
  rw [e1, e2] at this
  exact this.symm

lemma partC_fwd {n : ℕ} {I : Index n} (hI : IsIndex I) (hH : Homogeneity I)
    (hA : Additivity I) (hE : EqualGlobalImpact I) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, I t = c • userCentric t := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, ?_⟩
    have hW : ∀ t, I t =
        weightedIndex (fun (_ : ℕ) (x : Fin 0 → ℕ) => 1 * (1 / ∑ i, (x i : ℝ))) t := by
      apply add_ext hA (weighted_add _)
      intro j x hx
      exact absurd (funext (fun i => i.elim0)) hx
    intro t
    rw [hW t, userCentric_eq, smul_weighted]
  · have e_ne : (fun _ : Fin n => (1 : ℕ)) ≠ 0 := fun h => by
      have := congrFun h ⟨0, hn⟩
      simp at this
    have hS : ∀ j x, x ≠ 0 →
        ∑ i, I (Finsupp.single j x) i = ∑ i, I (Finsupp.single 0 (fun _ => 1)) i := by
      intro j x hx
      by_cases hj : j = 0
      · subst hj
        rw [egi_step hE 0 1 (by norm_num) x _ hx e_ne, egi_step hE 1 0 (by norm_num) _ _ e_ne e_ne]
      · exact egi_step hE j 0 hj x _ hx e_ne
    refine ⟨∑ i, I (Finsupp.single 0 (fun _ => 1)) i,
      (hI _ (Finsupp.single_ne_zero.mpr e_ne)).2, ?_⟩
    have hW : ∀ t, I t = weightedIndex (fun (_ : ℕ) (x : Fin n → ℕ) =>
        (∑ i, I (Finsupp.single 0 (fun _ => 1)) i) * (1 / ∑ i, (x i : ℝ))) t := by
      apply add_ext hA (weighted_add _)
      intro j x hx
      funext i
      rw [weighted_single, hom_single hH j x hx i]
      unfold lam
      rw [hS j x hx]
      ring
    intro t
    rw [hW t, userCentric_eq, smul_weighted]

end MSA41

open MusicStreaming.Axioms in
theorem solution :
    (∀ (n : ℕ) (I : Index n), IsIndex I →
      (Homogeneity I ∧ Additivity I ↔
        ∃ ω : ℕ → (Fin n → ℕ) → ℝ, (∀ j x, 0 < ω j x) ∧ ∀ t, I t = weightedIndex ω t)) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ I : Index n, IsIndex I →
      (Homogeneity I ∧ Additivity I ∧ EqualIndividualImpact I ↔
        ∃ c : ℝ, 0 < c ∧ ∀ t, I t = c • proRata t)) ∧
    (∀ (n : ℕ) (I : Index n), IsIndex I →
      (Homogeneity I ∧ Additivity I ∧ EqualGlobalImpact I ↔
        ∃ c : ℝ, 0 < c ∧ ∀ t, I t = c • userCentric t)) := by
  refine ⟨fun n I hI => MSA41.partA I hI, fun n hn I hI => ⟨?_, ?_⟩, fun n I hI => ⟨?_, ?_⟩⟩
  · rintro ⟨hH, hA, hE⟩
    exact MSA41.partB_fwd hn hI hH hA hE
  · rintro ⟨c, -, hct⟩
    have : I = weightedIndex (fun (_ : ℕ) (_ : Fin n → ℕ) => c * 1) := by
      funext t
      rw [hct t, MSA41.proRata_eq, MSA41.smul_weighted]
    subst this
    exact ⟨MSA41.weighted_hom _, MSA41.weighted_add _, MSA41.proRata_EII _⟩
  · rintro ⟨hH, hA, hE⟩
    exact MSA41.partC_fwd hI hH hA hE
  · rintro ⟨c, -, hct⟩
    have : I = weightedIndex (fun (_ : ℕ) (x : Fin n → ℕ) => c * (1 / ∑ i, (x i : ℝ))) := by
      funext t
      rw [hct t, MSA41.userCentric_eq, MSA41.smul_weighted]
    subst this
    exact ⟨MSA41.weighted_hom _, MSA41.weighted_add _, MSA41.uc_EGI _⟩
