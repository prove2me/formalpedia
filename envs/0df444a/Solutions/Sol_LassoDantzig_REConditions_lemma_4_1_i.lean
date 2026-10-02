-- Prove2me | solution 1 for LassoDantzig.REConditions.lemma_4_1_i
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T11:59:17.079728+00:00
-- url     : https://prove2.me/submissions/7a3d5b0f-f795-40f6-87e2-2674774f1b82

import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues
import Theorems.Thm_LassoDantzig_REConditions_eq_A1_projection_triangle
import Theorems.Thm_LassoDantzig_REConditions_eq_A3_shelling_bound
import Theorems.Thm_LassoDantzig_REConditions_candes_tao_correlation_bound


set_option maxHeartbeats 1000000

namespace LassoDantzig.REConditions

lemma exists_top_subset {M : ℕ} (δ : Fin M → ℝ) (S : Finset (Fin M))
    (m : ℕ) (hm : m ≤ S.card) :
    ∃ A : Finset (Fin M), A ⊆ S ∧ A.card = m ∧
      ∀ a ∈ A, ∀ b ∈ S \ A, |δ b| ≤ |δ a| := by
  classical
  let l := S.toList.mergeSort (fun a b => decide (|δ b| ≤ |δ a|))
  have hp : l.Perm S.toList := List.mergeSort_perm _ _
  have hlen : l.length = S.card := by simpa using hp.length_eq
  have hnodup : l.Nodup := hp.nodup_iff.mpr S.nodup_toList
  have hsorted : l.Pairwise (fun a b => |δ b| ≤ |δ a|) := by
    simpa [l] using List.pairwise_mergeSort (le := fun a b : Fin M => decide (|δ b| ≤ |δ a|))
      (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab))
      (fun a b => by simpa using le_total (|δ b|) (|δ a|)) S.toList
  have hmem : ∀ a, a ∈ l ↔ a ∈ S := fun a => hp.mem_iff.trans Finset.mem_toList
  refine ⟨(l.take m).toFinset, ?_, ?_, ?_⟩
  · intro a ha
    exact (hmem a).mp (List.mem_of_mem_take (List.mem_toFinset.mp ha))
  · rw [List.toFinset_card_of_nodup hnodup.take, List.length_take, hlen,
      Nat.min_eq_left hm]
  · intro a ha b hb
    have ha' : a ∈ l.take m := List.mem_toFinset.mp ha
    have hb' : b ∈ l.drop m := by
      have hbS := (hmem b).mpr (Finset.mem_sdiff.mp hb).1
      rw [← List.take_append_drop m l, List.mem_append] at hbS
      exact hbS.resolve_left (fun h => (Finset.mem_sdiff.mp hb).2 (List.mem_toFinset.mpr h))
    rw [← List.take_append_drop m l, List.pairwise_append] at hsorted
    exact hsorted.2.2 a ha' b hb'

lemma block_subset {M : ℕ} {S : Finset (Fin M)} {J : ℕ → Finset (Fin M)} {K k : ℕ}
    (h : IsBlockPartition S J K) (hk : k ∈ Finset.Icc 1 K) : J k ⊆ S := by
  intro a ha
  rw [← h.2.2]
  exact Finset.mem_biUnion.mpr ⟨k, hk, ha⟩

lemma prepend_shelling {M : ℕ} (δ : Fin M → ℝ) (S A : Finset (Fin M))
    (m : ℕ) (hA : A ⊆ S) (hcard : A.card = m)
    (hdom : ∀ a ∈ A, ∀ b ∈ S \ A, |δ b| ≤ |δ a|)
    (J : ℕ → Finset (Fin M)) (K : ℕ)
    (hsh : IsShelling δ (S \ A)ᶜ m J K) :
    IsShelling δ Sᶜ m (fun k => if k = 1 then A else J (k - 1)) (K + 1) := by
  classical
  rcases hsh with ⟨hpart, hfull, hlast, hsorted⟩
  have hpart' : IsBlockPartition (S \ A) J K := by simpa using hpart
  have hK := hpart'.1
  have hsub : ∀ k ∈ Finset.Icc 1 K, J k ⊆ S \ A := fun k hk => block_subset hpart' hk
  refine ⟨⟨by omega, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k hk l hl hkl
    have hk' := Finset.mem_Icc.mp hk
    have hl' := Finset.mem_Icc.mp hl
    by_cases hk1 : k = 1
    · subst k
      simp only [if_pos rfl, if_neg (Ne.symm hkl)]
      apply Finset.disjoint_left.mpr
      intro a ha hj
      exact (Finset.mem_sdiff.mp (hsub (l-1) (by simp; omega) hj)).2 ha
    · by_cases hl1 : l = 1
      · subst l
        simp only [if_neg hk1, if_pos rfl]
        apply Finset.disjoint_left.mpr
        intro a hj ha
        exact (Finset.mem_sdiff.mp (hsub (k-1) (by simp; omega) hj)).2 ha
      · simp only [if_neg hk1, if_neg hl1]
        exact hpart'.2.1 (k-1) (by simp; omega) (l-1) (by simp; omega) (by omega)
  · rw [compl_compl]
    ext a
    constructor
    · intro ha
      obtain ⟨k, hk, ha⟩ := Finset.mem_biUnion.mp ha
      have hk' := Finset.mem_Icc.mp hk
      by_cases hk1 : k = 1
      · simpa [hk1] using hA (by simpa [hk1] using ha)
      · exact (Finset.mem_sdiff.mp (hsub (k-1) (by simp; omega) (by simpa [hk1] using ha))).1
    · intro ha
      by_cases haA : a ∈ A
      · exact Finset.mem_biUnion.mpr ⟨1, by simp, by simp [haA]⟩
      · have har : a ∈ S \ A := Finset.mem_sdiff.mpr ⟨ha, haA⟩
        rw [← hpart'.2.2] at har
        obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp har
        have hk' := Finset.mem_Icc.mp hk
        exact Finset.mem_biUnion.mpr ⟨k+1, by simp <;> omega, by simpa [show k ≠ 0 by omega] using hak⟩
  · intro k hk
    have hk' := Finset.mem_Ico.mp hk
    by_cases hk1 : k = 1
    · simpa [hk1] using hcard
    · simp only [if_neg hk1]
      exact hfull (k-1) (by simp; omega)
  · simpa [show K ≠ 0 by omega] using hlast
  · intro k hk l hl hkl a ha b hb
    have hk' := Finset.mem_Icc.mp hk
    have hl' := Finset.mem_Icc.mp hl
    have hl1 : l ≠ 1 := by omega
    by_cases hk1 : k = 1
    · apply hdom a (by simpa [hk1] using ha) b
      exact hsub (l-1) (by simp; omega) (by simpa [hl1] using hb)
    · exact hsorted (k-1) (by simp; omega) (l-1) (by simp; omega) (by omega)
        a (by simpa [hk1] using ha) b (by simpa [hl1] using hb)

lemma exists_shelling_set {M : ℕ} (δ : Fin M → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (S : Finset (Fin M)) : ∃ J K, IsShelling δ Sᶜ m J K := by
  classical
  induction hc : S.card using Nat.strong_induction_on generalizing S with
  | h q ih =>
    by_cases hsmall : S.card ≤ m
    · refine ⟨fun _ => S, 1, ?_⟩
      refine ⟨⟨by omega, ?_, by simp⟩, by simp, hsmall, ?_⟩
      · intro k hk l hl hkl
        simp only [Finset.mem_Icc] at hk hl
        omega
      · intro k hk l hl hkl
        simp only [Finset.mem_Icc] at hk hl
        omega
    · obtain ⟨A, hA, hcard, hdom⟩ := exists_top_subset δ S m (by omega)
      have hlt : (S \ A).card < q := by
        rw [Finset.card_sdiff_of_subset hA, hcard, hc]
        omega
      obtain ⟨J, K, hsh⟩ := ih (S \ A).card hlt (S \ A) rfl
      exact ⟨_, K+1, prepend_shelling δ S A m hA hcard hdom J K hsh⟩

lemma exists_shelling_first {M : ℕ} (δ : Fin M → ℝ) (J0 J1 : Finset (Fin M))
    (m : ℕ) (hm : 1 ≤ m) (htop : IsTopBlock δ J0 J1 m) :
    ∃ J K, IsShelling δ J0 m J K ∧ J 1 = J1 := by
  classical
  obtain ⟨J, K, hsh⟩ := exists_shelling_set δ m hm (J0ᶜ \ J1)
  refine ⟨(fun k => if k = 1 then J1 else J (k-1)), K+1, ?_, by simp⟩
  simpa using prepend_shelling δ J0ᶜ J1 m htop.1 htop.2.1 htop.2.2 J K hsh

end LassoDantzig.REConditions


set_option maxHeartbeats 1000000

namespace LassoDantzig.REConditions

lemma rayleigh_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ)
    (q : ℝ) (hq : q ∈ rayleighSet X u) : 0 ≤ q := by
  rcases hq with ⟨x, -, -, rfl⟩
  unfold gramQuad
  positivity

lemma phiMin_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) :
    0 ≤ phiMin X u := Real.sInf_nonneg (rayleigh_nonneg X u)

lemma phiMax_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) :
    0 ≤ phiMax X u := Real.sSup_nonneg (rayleigh_nonneg X u)

lemma sparse_lower_bound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ)
    (δ : Fin M → ℝ) (S : Finset (Fin M)) (hS : S.card ≤ u) :
    Real.sqrt (phiMin X u) * l2On δ S ≤
      1 / Real.sqrt n * euclNorm (X.mulVec (restrict δ S)) := by
  classical
  let x := restrict δ S
  have hxsum : ∑ j, x j ^ 2 = ∑ j ∈ S, δ j ^ 2 := by
    simp [x, restrict, ite_pow, Finset.sum_ite_mem]
  have hkey : phiMin X u * (∑ j ∈ S, δ j ^ 2) ≤ gramQuad X x := by
    by_cases hz : ∑ j, x j ^ 2 = 0
    · rw [← hxsum, hz, mul_zero]
      unfold gramQuad
      positivity
    · have hpos : 0 < ∑ j, x j ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Ne.symm hz)
      have hsp : sparsity x ≤ u := by
        apply le_trans (Finset.card_le_card ?_) hS
        intro j hj
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        by_contra hjS
        exact hj (by simp [x, restrict, hjS])
      have hsp1 : 1 ≤ sparsity x := by
        apply Finset.card_pos.mpr
        by_contra hc
        rw [Finset.not_nonempty_iff_eq_empty] at hc
        have hx0 : ∀ j, x j = 0 := by
          intro j
          by_contra hj
          have : j ∈ supp x := by simp [supp, hj]
          rw [hc] at this
          simp at this
        simp [hx0] at hz
      have hle : phiMin X u ≤ gramQuad X x / ∑ j, x j ^ 2 := by
        apply csInf_le
        · exact ⟨0, rayleigh_nonneg X u⟩
        · exact ⟨x, hsp1, hsp, rfl⟩
      rw [le_div_iff₀ hpos] at hle
      simpa [hxsum] using hle
  unfold l2On euclNorm
  rw [← Real.sqrt_mul (phiMin_nonneg X u), one_div, ← Real.sqrt_inv,
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  simpa [gramQuad, x, one_div] using hkey

lemma projected_lower_bound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (s m : ℕ) (hm : 1 ≤ m) (c0 : ℝ) (hc0 : 0 < c0)
    (a b : ℝ) (hb : 0 ≤ b)
    (hlower : ∀ δ S, S.card ≤ s+m → a * l2On δ S ≤
      1 / Real.sqrt n * euclNorm (X.mulVec (restrict δ S)))
    (hupper : ∀ δ S T, Disjoint T S → T.card ≤ m → S.card ≤ s+m →
      1 / Real.sqrt n * projNorm X S (X.mulVec (restrict δ T)) ≤ b * l2On δ T)
    (J0 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ)
    (hcone : ConeCond c0 J0 δ) (J1 : Finset (Fin M)) (htop : IsTopBlock δ J0 J1 m) :
    (a - b * c0 * Real.sqrt ((s : ℝ) / m)) * l2On δ (J0 ∪ J1) ≤
      1 / Real.sqrt n * projNorm X (J0 ∪ J1) (X.mulVec δ) := by
  classical
  obtain ⟨J, K, hsh, hfirst⟩ := exists_shelling_first δ J0 J1 m hm htop
  have hpart := hsh.1
  have hA1 := eq_A1_projection_triangle X hn hM δ J0 J K hpart
  rw [hfirst] at hA1
  have hheadcard : (J0 ∪ J1).card ≤ s+m :=
    (Finset.card_union_le _ _).trans (by rw [htop.2.1]; omega)
  have hbase : euclNorm (X.mulVec (restrict δ (J0 ∪ J1))) -
      ∑ k ∈ Finset.Icc 2 K, projNorm X (J0 ∪ J1) (X.mulVec (restrict δ (J k))) ≤
      projNorm X (J0 ∪ J1) (X.mulVec δ) := by
    apply hA1.2.2.trans
    rw [← hA1.2.1]
    exact hA1.1
  have htail : ∑ k ∈ Finset.Icc 2 K,
      (1 / Real.sqrt n * projNorm X (J0 ∪ J1) (X.mulVec (restrict δ (J k)))) ≤
        b * (c0 * Real.sqrt ((s : ℝ) / m) * l2On δ (J0 ∪ J1)) := by
    have hsum : ∑ k ∈ Finset.Icc 2 K,
        (1 / Real.sqrt n * projNorm X (J0 ∪ J1) (X.mulVec (restrict δ (J k)))) ≤
        b * ∑ k ∈ Finset.Icc 2 K, l2On δ (J k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      have hk1 : k ∈ Finset.Icc 1 K := by simp; omega
      apply hupper
      · apply Finset.disjoint_left.mpr
        intro j hj hS
        rcases Finset.mem_union.mp hS with hj0 | hj1
        · exact (Finset.mem_compl.mp (block_subset hpart hk1 hj)) hj0
        · rw [← hfirst] at hj1
          exact Finset.disjoint_left.mp
            (hpart.2.1 k hk1 1 (by simp; omega) (by omega)) hj hj1
      · by_cases hkK : k = K
        · simpa [hkK] using hsh.2.2.1
        · exact (hsh.2.1 k (by simp; omega)).le
      · exact hheadcard
    have hA3 := eq_A3_shelling_bound hn hM s m hm c0 hc0 δ J0 J K hsh
    have hchain := hA3.2.2 hJ0 hcone
    rw [hfirst] at hchain
    exact hsum.trans (mul_le_mul_of_nonneg_left
      (hA3.2.1.trans (hchain.1.trans (hchain.2.1.trans hchain.2.2))) hb)
  have hhead := hlower δ (J0 ∪ J1)
    ((Finset.card_union_le _ _).trans (by rw [htop.2.1]; omega))
  have hscaled := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 1 / Real.sqrt n by positivity)
  rw [mul_sub, Finset.mul_sum] at hscaled
  calc
    _ = a * l2On δ (J0 ∪ J1) - b * (c0 * Real.sqrt ((s : ℝ) / m) * l2On δ (J0 ∪ J1)) := by ring
    _ ≤ _ := sub_le_sub hhead htail
    _ ≤ _ := hscaled

lemma projNorm_le {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (S : Finset (Fin M)) (v : Fin n → ℝ) : projNorm X S v ≤ euclNorm v := by
  unfold projNorm euclNorm
  calc _ ≤ ‖WithLp.toLp 2 v‖ := Submodule.norm_starProjection_apply_le _ _
    _ = _ := by rw [EuclideanSpace.norm_eq]; simp

lemma assemble_RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (s m : ℕ) (hsm : s+m ≤ M) (c0 κ : ℝ) (hκ : 0 ≤ κ)
    (hproj : ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ,
      ConeCond c0 J0 δ → ∀ J1, IsTopBlock δ J0 J1 m →
      κ * l2On δ (J0 ∪ J1) ≤ 1 / Real.sqrt n * projNorm X (J0 ∪ J1) (X.mulVec δ)) :
    RE X s c0 κ ∧ REm X s m c0 κ := by
  classical
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hfull : ∀ J0, J0.card ≤ s → ∀ δ, ConeCond c0 J0 δ → ∀ J1,
      IsTopBlock δ J0 J1 m → κ * Real.sqrt n * l2On δ (J0 ∪ J1) ≤ euclNorm (X.mulVec δ) := by
    intro J0 hJ0 δ hcone J1 htop
    have h := (hproj J0 hJ0 δ hcone J1 htop).trans
      (mul_le_mul_of_nonneg_left (projNorm_le X _ _) (by positivity))
    rw [one_div_mul_eq_div, le_div_iff₀ hsn] at h
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  refine ⟨?_, fun J0 hJ0 δ _ hcone J1 htop => hfull J0 hJ0 δ hcone J1 htop⟩
  intro J0 hJ0 δ _ hcone
  have hmcard : m ≤ J0ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨J1, hsub, hcard, hdom⟩ := exists_top_subset δ J0ᶜ m hmcard
  have hmono : l2On δ J0 ≤ l2On δ (J0 ∪ J1) := by
    apply Real.sqrt_le_sqrt
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (fun _ _ _ => sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left hmono (mul_nonneg hκ hsn.le)).trans
    (hfull J0 hJ0 δ hcone J1 ⟨hsub, hcard, hdom⟩)

end LassoDantzig.REConditions


set_option maxHeartbeats 1000000

namespace LassoDantzig.REConditions

lemma correlation_neg_mem {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (m1 m2 : ℕ) (t : ℝ)
    (ht : t ∈ corrSet X m1 m2) : -t ∈ corrSet X m1 m2 := by
  obtain ⟨I1, I2, hd, h1, h2, c1, c2, hs1, hs2, hc1, hc2, rfl⟩ := ht
  refine ⟨I1, I2, hd, h1, h2, -c1, c2, fun j hj => by simp [hs1 j hj], hs2,
    neg_ne_zero.mpr hc1, hc2, ?_⟩
  simp [Matrix.mulVec_neg, neg_div, Finset.sum_neg_distrib]

lemma theta_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hM : 2 ≤ M)
    (m1 m2 : ℕ) (h1 : 1 ≤ m1) (h2 : 1 ≤ m2) : 0 ≤ theta X m1 m2 := by
  classical
  have hne : (corrSet X m1 m2).Nonempty := by
    let i0 : Fin M := ⟨0, by omega⟩
    let i1 : Fin M := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    refine ⟨_, {i0}, {i1}, ?_, by simpa using h1, by simpa using h2, Pi.single i0 1,
      Pi.single i1 1, ?_, ?_, ?_, ?_, rfl⟩
    · simpa using h01
    · intro j hj
      have : j ≠ i0 := by simpa using hj
      simp [this]
    · intro j hj
      have : j ≠ i1 := by simpa using hj
      simp [this]
    · simp
    · simp
  obtain ⟨t, ht⟩ := hne
  rcases le_total 0 t with h | h
  · exact Real.sSup_nonneg' ⟨t, ht, h⟩
  · exact Real.sSup_nonneg' ⟨-t, correlation_neg_mem X m1 m2 t ht, by linarith⟩

lemma kappa1_formula_positive {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hM : 2 ≤ M) (s : ℕ) (hs : 1 ≤ s) (c0 : ℝ) (hc0 : 0 < c0)
    (hA1 : Assumption1 X s c0) :
    kappa1 X s c0 = Real.sqrt (phiMin X (2*s)) -
      theta X s (2*s) / Real.sqrt (phiMin X (2*s)) * c0 ∧
    0 < kappa1 X s c0 ∧ 0 < phiMin X (2*s) := by
  have hθ := theta_nonneg X hM s (2*s) hs (by omega)
  have hφ : 0 < phiMin X (2*s) :=
    lt_of_le_of_lt (mul_nonneg hc0.le hθ) hA1
  have hr : 0 < Real.sqrt (phiMin X (2*s)) := Real.sqrt_pos.mpr hφ
  have hr2 := Real.sq_sqrt hφ.le
  have heq : kappa1 X s c0 = Real.sqrt (phiMin X (2*s)) -
      theta X s (2*s) / Real.sqrt (phiMin X (2*s)) * c0 := by
    unfold kappa1
    rw [mul_sub, mul_one]
    congr 1
    field_simp [ne_of_gt hr, ne_of_gt hφ]
    nlinarith only [congrArg (fun z : ℝ => z * theta X s (2*s)) hr2]
  refine ⟨heq, ?_, hφ⟩
  unfold kappa1
  apply mul_pos hr
  have hquot : c0 * theta X s (2*s) / phiMin X (2*s) < 1 :=
    (div_lt_one hφ).mpr hA1
  linarith

end LassoDantzig.REConditions

open LassoDantzig.REConditions

theorem solution {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : 2 * s ≤ M) (hc0 : 0 < c0)
    (hA1 : Assumption1 X s c0) :
    0 < kappa1 X s c0 ∧
    RE X s c0 (kappa1 X s c0) ∧
    REm X s s c0 (kappa1 X s c0) ∧
    ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, ConeCond c0 J0 δ →
      ∀ J1 : Finset (Fin M), IsTopBlock δ J0 J1 s →
        kappa1 X s c0 * l2On δ (J0 ∪ J1) ≤
          1 / Real.sqrt n * projNorm X (J0 ∪ J1) (X.mulVec δ) := by
  obtain ⟨heq, hpos, hφ⟩ := kappa1_formula_positive X hM s hs c0 hc0 hA1
  have hproj : ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ,
      ConeCond c0 J0 δ → ∀ J1, IsTopBlock δ J0 J1 s →
      kappa1 X s c0 * l2On δ (J0 ∪ J1) ≤
        1 / Real.sqrt n * projNorm X (J0 ∪ J1) (X.mulVec δ) := by
    intro J0 hJ0 δ hcone J1 htop
    have hgeneric := projected_lower_bound X hn hM s s hs c0 hc0
      (Real.sqrt (phiMin X (2*s))) (theta X s (2*s) / Real.sqrt (phiMin X (2*s)))
      (div_nonneg (theta_nonneg X hM s (2*s) hs (by omega)) (Real.sqrt_nonneg _))
      (fun δ S hS => sparse_lower_bound X (2*s) δ S (by omega))
      (fun δ S T hd hT hS => candes_tao_correlation_bound X hn hM s hs δ T S hd hT
        (by omega) hφ)
      J0 hJ0 δ hcone J1 htop
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
    simpa [heq, div_self hsR] using hgeneric
  obtain ⟨hRE, hREm⟩ := assemble_RE X hn s s (by omega) c0 _ hpos.le hproj
  exact ⟨hpos, hRE, hREm, hproj⟩
