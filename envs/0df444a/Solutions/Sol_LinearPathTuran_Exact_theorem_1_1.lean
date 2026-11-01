-- Prove2me | solution 1 for LinearPathTuran.Exact.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T07:11:14.602065+00:00
-- url     : https://prove2.me/submissions/fa9b1934-ad73-4548-90c7-58086617564b

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_Setting

section

open Finset
open scoped BigOperators
namespace LinearPathTuran.Exact.Fresh

def degree {n : ℕ} (F : Finset (Finset (Fin n))) (v : Fin n) : ℕ :=
  (F.filter (fun A => v ∈ A)).card

end LinearPathTuran.Exact.Fresh
end

section

namespace LinearPathTuran.Exact.Fresh

open Finset

variable {V : Type*} [DecidableEq V]

theorem greedy_matching (F : Finset (Finset V)) (k B : ℕ)
    (hF : ∀ A ∈ F, A.card = k) (T W : Finset V)
    (hTW : Disjoint T W) (hbudget : W.card + (k + 1) * T.card ≤ B)
    (hchoose : ∀ v ∈ T, ∀ Z : Finset V, v ∉ Z → Z.card ≤ B →
      ∃ A ∈ F, v ∈ A ∧ Disjoint A Z) :
    ∃ M ⊆ F, M.card = T.card ∧ (M : Set (Finset V)).PairwiseDisjoint id ∧
      Disjoint (M.biUnion id) W ∧ T ⊆ M.biUnion id := by
  classical
  induction T using Finset.induction_on generalizing W with
  | empty => exact ⟨∅, by simp, by simp, by simp, by simp, by simp⟩
  | @insert v T hv ih =>
    have hvW : v ∉ W := by
      exact fun hvw => Finset.disjoint_left.mp hTW (by simp) hvw
    have hvZ : v ∉ W ∪ T := by simp [hvW, hv]
    have hz : (W ∪ T).card ≤ B := by
      have hu := Finset.card_union_le W T
      rw [Finset.card_insert_of_notMem hv] at hbudget
      nlinarith
    obtain ⟨A, hAF, hvA, hAZ⟩ := hchoose v (by simp) (W ∪ T) hvZ hz
    have hAW : Disjoint A W := (Finset.disjoint_union_right.mp hAZ).1
    have hAT : Disjoint A T := (Finset.disjoint_union_right.mp hAZ).2
    have hTW' : Disjoint T (W ∪ A) := by
      apply Finset.disjoint_union_right.mpr
      exact ⟨hTW.mono_left (Finset.subset_insert _ _), hAT.symm⟩
    have hb' : (W ∪ A).card + (k + 1) * T.card ≤ B := by
      have hu := Finset.card_union_le W A
      have ha := hF A hAF
      rw [Finset.card_insert_of_notMem hv] at hbudget
      nlinarith
    obtain ⟨M, hMF, hcard, hpair, hMWA, hcover⟩ :=
      ih (W ∪ A) hTW' hb' (fun u hu => hchoose u (Finset.mem_insert_of_mem hu))
    have hMW := (Finset.disjoint_union_right.mp hMWA).1
    have hMA := (Finset.disjoint_union_right.mp hMWA).2
    have hAnot : A ∉ M := by
      intro ha
      have hvM : v ∈ M.biUnion id := Finset.mem_biUnion.mpr ⟨A, ha, hvA⟩
      exact Finset.disjoint_left.mp hMA hvM hvA
    refine ⟨insert A M, Finset.insert_subset hAF hMF, ?_, ?_, ?_, ?_⟩
    · simp only [Finset.card_insert_of_notMem hAnot, Finset.card_insert_of_notMem hv, hcard]
    · rw [Finset.coe_insert]
      exact hpair.insert fun C hC _ =>
        ((Finset.disjoint_biUnion_left M id A).mp hMA C hC).symm
    · simpa only [Finset.biUnion_insert, id_eq, Finset.disjoint_union_left] using And.intro hAW hMW
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · simp only [Finset.biUnion_insert, id_eq, Finset.mem_union]
        exact Or.inl hvA
      · simp only [Finset.biUnion_insert, id_eq, Finset.mem_union]
        exact Or.inr (hcover hu)

end LinearPathTuran.Exact.Fresh
end

section

open scoped BigOperators
namespace LinearPathTuran.Exact.Fresh
open Finset
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem matching_card_le (F : Finset (Finset V)) (t : ℕ)
    (hfree : ¬ ∃ M ⊆ F, M.card = t + 1 ∧ (M : Set (Finset V)).PairwiseDisjoint id)
    {M : Finset (Finset V)} (hMF : M ⊆ F)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id) : M.card ≤ t := by
  by_contra h
  have hh : t + 1 ≤ M.card := by omega
  obtain ⟨N, hNM, hNcard⟩ := Finset.exists_subset_card_eq hh
  apply hfree
  exact ⟨N, hNM.trans hMF, hNcard, fun A hA C hC hAC => hpair (hNM hA) (hNM hC) hAC⟩

theorem matching_cover (F : Finset (Finset V)) (k t : ℕ) (hk : 1 ≤ k)
    (hF : ∀ A ∈ F, A.card = k)
    (hfree : ¬ ∃ M ⊆ F, M.card = t + 1 ∧ (M : Set (Finset V)).PairwiseDisjoint id) :
    ∃ W : Finset V, W.card ≤ k * t ∧ ∀ A ∈ F, ¬ Disjoint A W := by
  classical
  let Q : Finset (Finset (Finset V)) := F.powerset.filter (fun (M : Finset (Finset V)) => (M : Set (Finset V)).PairwiseDisjoint id)
  have hQ : Q.Nonempty := ⟨∅, by simp [Q]⟩
  obtain ⟨M, hMQ, hmax⟩ := Finset.exists_max_image Q Finset.card hQ
  have hMF : M ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hMQ).1
  have hpair : (M : Set (Finset V)).PairwiseDisjoint id := (Finset.mem_filter.mp hMQ).2
  have hMt := matching_card_le F t hfree hMF hpair
  refine ⟨M.biUnion id, ?_, ?_⟩
  · calc
      _ ≤ ∑ A ∈ M, (id A).card := Finset.card_biUnion_le
      _ = M.card * k := by
        calc
          _ = ∑ _A ∈ M, k := Finset.sum_congr rfl (fun A hA => hF A (hMF hA))
          _ = _ := by simp
      _ ≤ k * t := by nlinarith
  · intro A hAF hdis
    have hAne : A.Nonempty := Finset.card_pos.mp (by rw [hF A hAF]; omega)
    have hAnot : A ∉ M := by
      intro ha
      obtain ⟨v, hv⟩ := hAne
      exact Finset.disjoint_left.mp hdis hv (Finset.mem_biUnion.mpr ⟨A, ha, hv⟩)
    have hp' : ((insert A M : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
      rw [Finset.coe_insert]
      exact hpair.insert fun C hC _ => (Finset.disjoint_biUnion_right A M id).mp hdis C hC
    have hmem : insert A M ∈ Q := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hAF hMF), hp'⟩
    have hh := hmax (insert A M) hmem
    rw [Finset.card_insert_of_notMem hAnot] at hh
    omega

end LinearPathTuran.Exact.Fresh
end

section

namespace LinearPathTuran.Exact.Fresh
open Finset
variable {V : Type*} [DecidableEq V]

theorem high_card_le (F : Finset (Finset V)) (k t : ℕ) (H : Finset V)
    (hF : ∀ A ∈ F, A.card = k)
    (hfree : ¬ ∃ M ⊆ F, M.card = t + 1 ∧ (M : Set (Finset V)).PairwiseDisjoint id)
    (hchoose : ∀ v ∈ H, ∀ Z : Finset V, v ∉ Z → Z.card ≤ (k + 1) * (t + 1) →
      ∃ A ∈ F, v ∈ A ∧ Disjoint A Z) : H.card ≤ t := by
  by_contra hh
  obtain ⟨T, hTH, hTc⟩ := Finset.exists_subset_card_eq (show t + 1 ≤ H.card by omega)
  obtain ⟨M, hMF, hMc, hpair, _, _⟩ := greedy_matching F k ((k + 1) * (t + 1)) hF T ∅
    (by simp) (by simp [hTc]) (fun v hv => hchoose v (hTH hv))
  exact hfree ⟨M, hMF, hMc.trans hTc, hpair⟩

theorem high_cover (F : Finset (Finset V)) (k t : ℕ) (hk : 1 ≤ k) (H : Finset V)
    (hH : H.card = t) (hF : ∀ A ∈ F, A.card = k)
    (hfree : ¬ ∃ M ⊆ F, M.card = t + 1 ∧ (M : Set (Finset V)).PairwiseDisjoint id)
    (hchoose : ∀ v ∈ H, ∀ Z : Finset V, v ∉ Z → Z.card ≤ (k + 1) * (t + 1) →
      ∃ A ∈ F, v ∈ A ∧ Disjoint A Z) : ∀ A ∈ F, ¬ Disjoint A H := by
  intro A hAF hAH
  have hb : A.card + (k + 1) * H.card ≤ (k + 1) * (t + 1) := by
    rw [hF A hAF, hH]
    nlinarith
  obtain ⟨M, hMF, hMc, hpair, hMA, _⟩ :=
    greedy_matching F k ((k + 1) * (t + 1)) hF H A hAH.symm hb hchoose
  have hAnot : A ∉ M := by
    intro ha
    have hAne : A.Nonempty := Finset.card_pos.mp (by rw [hF A hAF]; omega)
    obtain ⟨v, hv⟩ := hAne
    exact Finset.disjoint_left.mp hMA (Finset.mem_biUnion.mpr ⟨A, ha, hv⟩) hv
  apply hfree
  refine ⟨insert A M, Finset.insert_subset hAF hMF, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hAnot, hMc, hH]
  · rw [Finset.coe_insert]
    exact hpair.insert fun C hC _ =>
      ((Finset.disjoint_biUnion_left M id A).mp hMA C hC).symm

end LinearPathTuran.Exact.Fresh
end

section
namespace LinearPathTuran.Exact.Fresh
open Finset

theorem prescribed_count {n k : ℕ} (R : Finset (Fin n)) (hR : R.card ≤ k) :
    (((univ : Finset (Fin n)).powersetCard k).filter (fun A => R ⊆ A)).card =
      (n-R.card).choose (k-R.card) := by
  simpa using card_filter_powersetCard_subset R univ k (subset_univ R) hR

theorem degree_le_single {n k : ℕ} (hk : 1 ≤ k) (F : Finset (Finset (Fin n)))
    (hF : F ⊆ (univ : Finset (Fin n)).powersetCard k) (v : Fin n) :
    degree F v ≤ (n-1).choose (k-1) := by
  have hc := prescribed_count ({v} : Finset (Fin n)) (by simpa using hk)
  rw [card_singleton] at hc
  rw [← hc]
  apply card_le_card
  intro A hA
  simp only [mem_filter] at hA
  exact mem_filter.mpr ⟨hF hA.1, singleton_subset_iff.mpr hA.2⟩

theorem pair_degree_le {n k : ℕ} (hk : 2 ≤ k) (F : Finset (Finset (Fin n)))
    (hF : F ⊆ (univ : Finset (Fin n)).powersetCard k) (v w : Fin n) (hvw : v ≠ w) :
    (F.filter (fun A => v ∈ A ∧ w ∈ A)).card ≤ (n-2).choose (k-2) := by
  have hcR : ({v,w} : Finset (Fin n)).card = 2 := by simp [hvw]
  have hc := prescribed_count (k := k) ({v,w} : Finset (Fin n)) (by omega)
  rw [hcR] at hc
  rw [← hc]
  apply card_le_card
  intro A hA
  simp only [mem_filter] at hA
  exact mem_filter.mpr ⟨hF hA.1, by simp only [insert_subset_iff, singleton_subset_iff]; exact hA.2⟩

theorem star_card {n k : ℕ} (S : Finset (Fin n)) :
    (starFamily n k S).card = n.choose k - (n-S.card).choose k := by
  have he : ((univ : Finset (Fin n)).powersetCard k).filter (fun A => Disjoint A S) =
      (univ \ S).powersetCard k := by
    ext A
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨hA, hd⟩
      refine ⟨?_, hA⟩
      intro a ha
      exact mem_sdiff.mpr ⟨mem_univ a, fun hs => Finset.disjoint_left.mp hd ha hs⟩
    · rintro ⟨hA,hc⟩
      exact ⟨hc, disjoint_of_subset_left hA disjoint_sdiff_self_left⟩
  have hc := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n)).powersetCard k) (p := fun A => Disjoint A S)
  rw [he, card_powersetCard, card_sdiff_of_subset (subset_univ S), card_univ,
    Fintype.card_fin, card_powersetCard, card_univ, Fintype.card_fin] at hc
  unfold starFamily
  omega

end LinearPathTuran.Exact.Fresh
end

section
namespace LinearPathTuran.Exact.Fresh
open Finset

theorem family_cover_count {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (F : Finset α) (S : Finset ι) (P : ι → α → Prop) [∀ i, DecidablePred (P i)]
    (h : ∀ A ∈ F, ∃ v ∈ S, P v A) :
    F.card ≤ ∑ v ∈ S, (F.filter (P v)).card := by
  calc
    F.card ≤ (S.biUnion (fun v => F.filter (P v))).card := by
      apply card_le_card
      intro A hA
      obtain ⟨v,hv,hP⟩ := h A hA
      exact mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨hA,hP⟩⟩
    _ ≤ _ := card_biUnion_le

theorem degree_avoid {n : ℕ} (F : Finset (Finset (Fin n))) (v : Fin n)
    (W : Finset (Fin n)) (C : ℕ) (_hv : v ∉ W)
    (hp : ∀ w ∈ W, (F.filter (fun A => v ∈ A ∧ w ∈ A)).card ≤ C)
    (hd : W.card*C < degree F v) :
    ∃ A ∈ F, v ∈ A ∧ Disjoint A W := by
  classical
  by_contra hn
  have hcover : ∀ A ∈ F.filter (fun A => v ∈ A), ∃ w ∈ W, w ∈ A := by
    intro A hA
    have ha := mem_filter.mp hA
    have hnd : ¬ Disjoint A W := fun h => hn ⟨A,ha.1,ha.2,h⟩
    obtain ⟨w,hwA,hwW⟩ := Finset.not_disjoint_iff.mp hnd
    exact ⟨w,hwW,hwA⟩
  have hc := family_cover_count (F.filter (fun A => v ∈ A)) W (fun w A => w ∈ A) hcover
  have hsum : ∑ w ∈ W, ((F.filter (fun A => v ∈ A)).filter (fun A => w ∈ A)).card ≤
      W.card*C := by
    calc
      _ ≤ ∑ w ∈ W, C := by
        apply sum_le_sum
        intro w hw
        simpa only [filter_filter] using hp w hw
      _ = _ := by simp
  have hle : degree F v ≤ W.card*C := hc.trans hsum
  omega

theorem degree_avoid_uniform {n k : ℕ} (hk : 2 ≤ k)
    (F : Finset (Finset (Fin n))) (hF : F ⊆ univ.powersetCard k)
    (v : Fin n) (W : Finset (Fin n)) (hv : v ∉ W)
    (hd : W.card*(n-2).choose (k-2) < degree F v) :
    ∃ A ∈ F, v ∈ A ∧ Disjoint A W := by
  apply degree_avoid F v W _ hv ?_ hd
  intro w hw
  exact pair_degree_le hk F hF v w (fun h => hv (h ▸ hw))

end LinearPathTuran.Exact.Fresh
end

section
namespace LinearPathTuran.Exact.Fresh
open Finset

theorem family_degree_split {n : ℕ} (F : Finset (Finset (Fin n)))
    (H W : Finset (Fin n)) (A D : ℕ)
    (hcover : ∀ E ∈ F, ¬ Disjoint E W)
    (hhigh : ∀ v ∈ H, degree F v ≤ A)
    (hlow : ∀ v, v ∉ H → degree F v ≤ D) :
    F.card ≤ H.card*A + W.card*D := by
  have hc : ∀ E ∈ F, ∃ v ∈ H ∪ (W \ H), v ∈ E := by
    intro E hE
    obtain ⟨v,hvE,hvW⟩ := Finset.not_disjoint_iff.mp (hcover E hE)
    refine ⟨v, ?_, hvE⟩
    by_cases hvH : v ∈ H
    · exact mem_union_left _ hvH
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hvW,hvH⟩)
  have h := family_cover_count F (H ∪ (W \ H)) (fun v E => v ∈ E) hc
  change F.card ≤ ∑ v ∈ H ∪ (W \ H), degree F v at h
  rw [sum_union disjoint_sdiff_self_right] at h
  have h1 : ∑ v ∈ H, degree F v ≤ H.card*A := by
    calc
      _ ≤ ∑ _v ∈ H, A := sum_le_sum hhigh
      _ = _ := by simp
  have h2 : ∑ v ∈ W \ H, degree F v ≤ W.card*D := by
    calc
      _ ≤ ∑ _v ∈ W \ H, D := sum_le_sum (fun v hv => hlow v (mem_sdiff.mp hv).2)
      _ = (W \ H).card*D := by simp
      _ ≤ W.card*D := Nat.mul_le_mul_right D (card_le_card sdiff_subset)
  omega

end LinearPathTuran.Exact.Fresh
end

section

namespace LinearPathTuran.Exact.Fresh

def degreeSlack (k t : ℕ) : ℕ := (k + 1) * (t + 1)
def thresholdCoeff (k t : ℕ) : ℕ := k * t * degreeSlack k t + t * (t - 1)
def matchingThreshold (k t : ℕ) : ℕ := k + t + 1 + thresholdCoeff k t * (k - 1)

lemma large_n_binomial_gap (k t n : ℕ) (hk : 2 ≤ k) (_ht : 1 ≤ t)
    (hn : matchingThreshold k t < n) :
    k + t ≤ n ∧ 0 < (n - 2).choose (k - 2) ∧
      thresholdCoeff k t * (n - 2).choose (k - 2) < (n - 1).choose (k - 1) := by
  have hn' := hn
  unfold matchingThreshold at hn'
  have hkn : k + t ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hpos : 0 < (n - 2).choose (k - 2) := Nat.choose_pos (by omega)
  refine ⟨hkn, hpos, ?_⟩
  have hi := Nat.add_one_mul_choose_eq (n - 2) (k - 2)
  have hne : n - 2 + 1 = n - 1 := by omega
  have hke : k - 2 + 1 = k - 1 := by omega
  rw [hne, hke] at hi
  have hsmall : thresholdCoeff k t * (k - 1) < n - 1 := by omega
  by_contra h
  have hle : (n - 1).choose (k - 1) ≤ thresholdCoeff k t * (n - 2).choose (k - 2) := by omega
  have hmul := Nat.mul_le_mul_left (k - 1) hle
  have hstrict := Nat.mul_lt_mul_of_pos_right hsmall hpos
  nlinarith

lemma strict_matching_count_gap (f A C T k t L : ℕ) (ht : 1 ≤ t)
    (hf : f ≤ (t - 1) * A + k * t * L * C)
    (hT : t * A ≤ T + t * (t - 1) * C)
    (hgap : (k * t * L + t * (t - 1)) * C < A) : f < T := by
  have hid : (t - 1) * A + A = t * A := by
    calc
      _ = ((t - 1) + 1) * A := by ring
      _ = _ := by rw [Nat.sub_add_cancel ht]
  nlinarith

end LinearPathTuran.Exact.Fresh
end

section

namespace LinearPathTuran.Exact.Fresh
open Finset

theorem near_extremal_star {n k t : ℕ} (hk : 2 ≤ k) (ht : 1 ≤ t)
    (F : Finset (Finset (Fin n))) (hF : F ⊆ univ.powersetCard k)
    (hfree : ¬ ∃ M ⊆ F, M.card = t + 1 ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id)
    (T : ℕ)
    (hT : t * (n - 1).choose (k - 1) ≤ T + t * (t - 1) * (n - 2).choose (k - 2))
    (hgap : thresholdCoeff k t * (n - 2).choose (k - 2) < (n - 1).choose (k - 1))
    (hlarge : T ≤ F.card) :
    ∃ H : Finset (Fin n), H.card = t ∧ F ⊆ starFamily n k H := by
  classical
  let C := (n - 2).choose (k - 2)
  let A := (n - 1).choose (k - 1)
  let L := degreeSlack k t
  let H := univ.filter (fun v => L * C < degree F v)
  have hcard : ∀ E ∈ F, E.card = k := fun E hE => (mem_powersetCard.mp (hF hE)).2
  have hchoose : ∀ v ∈ H, ∀ Z : Finset (Fin n), v ∉ Z → Z.card ≤ (k + 1) * (t + 1) →
      ∃ E ∈ F, v ∈ E ∧ Disjoint E Z := by
    intro v hv Z hvZ hZ
    apply degree_avoid_uniform hk F hF v Z hvZ
    have hd : L * C < degree F v := (mem_filter.mp hv).2
    have hm : Z.card * C ≤ L * C := Nat.mul_le_mul_right C hZ
    exact hm.trans_lt hd
  have hHt := high_card_le F k t H hcard hfree hchoose
  have hHeq : H.card = t := by
    by_contra hh
    have hHs : H.card ≤ t - 1 := by omega
    obtain ⟨W, hWc, hcover⟩ := matching_cover F k t (by omega) hcard hfree
    have hs := family_degree_split F H W A (L * C) hcover
      (fun v _ => degree_le_single (by omega) F hF v)
      (fun v hv => by
        have hh : ¬ L * C < degree F v := by simpa only [H, mem_filter, mem_univ, true_and] using hv
        omega)
    have hf : F.card ≤ (t - 1) * A + k * t * L * C := by
      have h1 := Nat.mul_le_mul_right A hHs
      have h2 := Nat.mul_le_mul_right (L * C) hWc
      nlinarith
    have hstrict := strict_matching_count_gap F.card A C T k t L ht hf hT hgap
    omega
  refine ⟨H, hHeq, ?_⟩
  intro E hE
  exact mem_filter.mpr ⟨hF hE, high_cover F k t (by omega) H hHeq hcard hfree hchoose E hE⟩

end LinearPathTuran.Exact.Fresh
end

section
namespace LinearPathTuran.Exact.Fresh
open Finset

theorem optimum_from_near {n k t : ℕ} (hk : 2 ≤ k) (ht : 1 ≤ t)
    (F : Finset (Finset (Fin n))) (hF : F ⊆ univ.powersetCard k)
    (hfree : ¬ ∃ M ⊆ F, M.card = t+1 ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hT : t*(n-1).choose (k-1) ≤ n.choose k-(n-t).choose k+t*(t-1)*(n-2).choose (k-2))
    (hgap : thresholdCoeff k t*(n-2).choose (k-2) < (n-1).choose (k-1)) :
    F.card ≤ n.choose k-(n-t).choose k ∧
    (F.card = n.choose k-(n-t).choose k ↔
      ∃ S : Finset (Fin n), S.card=t ∧ F=starFamily n k S) := by
  have hstar (S : Finset (Fin n)) (hS : S.card=t) :
      (starFamily n k S).card = n.choose k-(n-t).choose k := by
    rw [star_card,hS]
  have hbound : F.card ≤ n.choose k-(n-t).choose k := by
    by_cases hlarge : n.choose k-(n-t).choose k ≤ F.card
    · obtain ⟨H,hH,hFH⟩ := near_extremal_star hk ht F hF hfree _ hT hgap hlarge
      simpa only [hstar H hH] using card_le_card hFH
    · omega
  refine ⟨hbound, ?_⟩
  constructor
  · intro he
    obtain ⟨H,hH,hFH⟩ := near_extremal_star hk ht F hF hfree _ hT hgap he.ge
    refine ⟨H,hH,?_⟩
    exact eq_of_subset_of_card_le hFH (by rw [hstar H hH,he])
  · rintro ⟨S,hS,rfl⟩
    exact hstar S hS

end LinearPathTuran.Exact.Fresh
end

section
namespace LinearPathTuran.Exact.Fresh
open Finset

theorem singleton_pairwise {n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : F ⊆ univ.powersetCard 1) : (F : Set (Finset (Fin n))).PairwiseDisjoint id := by
  intro A hA B hB hne
  obtain ⟨a, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp (hF hA)).2
  obtain ⟨b, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp (hF hB)).2
  change Disjoint ({a} : Finset (Fin n)) {b}
  simpa only [disjoint_singleton] using (fun h : a = b => hne (congrArg singleton h))

theorem singleton_star_union {n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : F ⊆ univ.powersetCard 1) : F = starFamily n 1 (F.biUnion id) := by
  ext A
  constructor
  · intro hA
    refine mem_filter.mpr ⟨hF hA, ?_⟩
    obtain ⟨a, ha⟩ := card_eq_one.mp (mem_powersetCard.mp (hF hA)).2
    subst A
    exact not_disjoint_iff.mpr ⟨a, mem_singleton_self a, mem_biUnion.mpr ⟨{a},hA,mem_singleton_self a⟩⟩
  · intro hA
    have hc := (mem_powersetCard.mp (mem_filter.mp hA).1).2
    obtain ⟨a,rfl⟩ := card_eq_one.mp hc
    obtain ⟨v,hv,hvU⟩ := not_disjoint_iff.mp (mem_filter.mp hA).2
    have hva : v = a := mem_singleton.mp hv
    subst v
    obtain ⟨B,hBF,haB⟩ := mem_biUnion.mp hvU
    obtain ⟨b,rfl⟩ := card_eq_one.mp (mem_powersetCard.mp (hF hBF)).2
    have hab : a = b := mem_singleton.mp haB
    simpa only [hab] using hBF

theorem singleton_case {n t : ℕ} (htn : t ≤ n) (F : Finset (Finset (Fin n)))
    (hF : F ⊆ univ.powersetCard 1)
    (hfree : ¬ ∃ M ⊆ F, M.card = t+1 ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id) :
    F.card ≤ n.choose 1 - (n-t).choose 1 ∧
    (F.card = n.choose 1 - (n-t).choose 1 ↔
      ∃ S : Finset (Fin n), S.card=t ∧ F=starFamily n 1 S) := by
  have hp := singleton_pairwise F hF
  have hb := matching_card_le F t hfree (subset_refl F) hp
  have hnum : n.choose 1 - (n-t).choose 1 = t := by simp only [Nat.choose_one_right]; omega
  rw [hnum]
  refine ⟨hb, ?_⟩
  constructor
  · intro he
    refine ⟨F.biUnion id, ?_, singleton_star_union F hF⟩
    rw [card_biUnion hp]
    calc
      _ = ∑ _A ∈ F, 1 := sum_congr rfl (fun A hA => (mem_powersetCard.mp (hF hA)).2)
      _ = t := by simpa using he
  · rintro ⟨S,hS,rfl⟩
    rw [star_card, hS, hnum]

end LinearPathTuran.Exact.Fresh
end

section

namespace LinearPathTuran.Exact.Fresh

lemma choose_increment_lower (N t r : ℕ) :
    N.choose (r + 1) + t * N.choose r ≤ (N + t).choose (r + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have he : (N + (t + 1)).choose (r + 1) =
          (N + t).choose r + (N + t).choose (r + 1) := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using Nat.choose_succ_succ (N + t) r
      rw [he]
      have hm := Nat.choose_le_choose r (by omega : N ≤ N + t)
      nlinarith

lemma choose_increment_upper (N t r : ℕ) :
    (N + t).choose (r + 1) ≤ N.choose (r + 1) + t * (N + t - 1).choose r := by
  induction t with
  | zero => simp
  | succ t ih =>
      have he : (N + (t + 1)).choose (r + 1) =
          (N + t).choose r + (N + t).choose (r + 1) := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using Nat.choose_succ_succ (N + t) r
      have hidx : N + (t + 1) - 1 = N + t := by omega
      rw [he, hidx]
      have hm := Nat.choose_le_choose r (Nat.sub_le (N + t) 1)
      have hmul := Nat.mul_le_mul_left t hm
      nlinarith

lemma matching_star_lower_arithmetic (n k t : ℕ) (hkn : k + t ≤ n)
    (hk : 2 ≤ k) (ht : 1 ≤ t) :
    t * (n - 1).choose (k - 1) ≤
      (n.choose k - (n - t).choose k) + t * (t - 1) * (n - 2).choose (k - 2) := by
  have hnt : n - t + t = n := by omega
  have hk1 : k - 1 + 1 = k := by omega
  have hlo := choose_increment_lower (n - t) t (k - 1)
  rw [hnt, hk1] at hlo
  have hlow : t * (n - t).choose (k - 1) ≤ n.choose k - (n - t).choose k := by omega
  have hidx : n - t + (t - 1) = n - 1 := by omega
  have hidx' : n - t + (t - 1) - 1 = n - 2 := by omega
  have hk2 : k - 2 + 1 = k - 1 := by omega
  have hup := choose_increment_upper (n - t) (t - 1) (k - 2)
  rw [hidx', hidx, hk2] at hup
  have hmul := Nat.mul_le_mul_left t hup
  nlinarith

end LinearPathTuran.Exact.Fresh
end

section
namespace LinearPathTuran.Exact.Fresh
open Finset

theorem native_theorem_1_1 (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n > n₀, ∀ 𝓕 : Finset (Finset (Fin n)),
      𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k →
      (¬ ∃ 𝓜 ⊆ 𝓕, #𝓜 = t + 1 ∧ (𝓜 : Set (Finset (Fin n))).PairwiseDisjoint id) →
      #𝓕 ≤ n.choose k - (n - t).choose k ∧
      (#𝓕 = n.choose k - (n - t).choose k ↔
        ∃ S : Finset (Fin n), #S = t ∧ 𝓕 = starFamily n k S) := by
  refine ⟨matchingThreshold k t, ?_⟩
  intro n hn F hF hfree
  by_cases hk1 : k = 1
  · subst k
    apply singleton_case (F := F) ?_ hF hfree
    unfold matchingThreshold at hn
    omega
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨hkn, _, hgap⟩ := large_n_binomial_gap k t n hk2 ht hn
    exact optimum_from_near hk2 ht F hF hfree
      (matching_star_lower_arithmetic n k t hkn hk2 ht) hgap

end LinearPathTuran.Exact.Fresh
end

open LinearPathTuran.Exact Finset

theorem solution (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n > n₀, ∀ 𝓕 : Finset (Finset (Fin n)),
      𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k →
      (¬ ∃ 𝓜 ⊆ 𝓕, #𝓜 = t + 1 ∧ (𝓜 : Set (Finset (Fin n))).PairwiseDisjoint id) →
      #𝓕 ≤ n.choose k - (n - t).choose k ∧
      (#𝓕 = n.choose k - (n - t).choose k ↔
        ∃ S : Finset (Fin n), #S = t ∧ 𝓕 = starFamily n k S) := by
  exact Fresh.native_theorem_1_1 k t hk ht
