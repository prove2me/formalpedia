-- Prove2me | solution 1 for KallenbergLP.AverageLP.theorem_4_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:01:23.704114+00:00
-- url     : https://prove2.me/submissions/e41829f3-8e4b-4acd-8ac6-a390a7ac2a59

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter
open Topology

namespace KallenbergLP.AverageLP

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PCFarkas

open Matrix

set_option linter.unusedSectionVars false

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

def PFeas (M : Matrix κ ι ℝ) (r : κ → ℝ) (z : ι → ℝ) : Prop := (∀ j, 0 ≤ z j) ∧ M *ᵥ z = r

noncomputable def supp (z : ι → ℝ) : Finset ι := Finset.univ.filter (fun j => z j ≠ 0)

def ColLI (M : Matrix κ ι ℝ) (S : Finset ι) : Prop :=
  LinearIndependent ℝ (fun j : S => Mᵀ (j : ι))

lemma mem_supp {z : ι → ℝ} {j : ι} : j ∈ supp z ↔ z j ≠ 0 := by simp [supp]

lemma sum_sub_eq_mulVec (M : Matrix κ ι ℝ) (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ j, j ∉ S → w j = 0) :
    ∑ j : S, w j • Mᵀ (j : ι) = M *ᵥ w := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul, mulVec, dotProduct]
  rw [Finset.sum_coe_sort S (fun j => w j * M i j)]
  rw [Finset.sum_subset (Finset.subset_univ S)]
  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro j _ hj; simp [hw j hj]

lemma reduce (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) :
    ∀ n, ∀ z, (supp z).card = n → PFeas M r z →
      ∃ z', PFeas M r z' ∧ c ⬝ᵥ z' ≤ c ⬝ᵥ z ∧ supp z' ⊆ supp z ∧ ColLI M (supp z') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hn hz
  by_cases hli : ColLI M (supp z)
  · exact ⟨z, hz, le_rfl, subset_rfl, hli⟩
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
  let d : ι → ℝ := fun j => if h : j ∈ supp z then g ⟨j, h⟩ else 0
  have hdS : ∀ j, j ∉ supp z → d j = 0 := by intro j hj; simp [d, hj]
  have hMd : M *ᵥ d = 0 := by
    rw [← sum_sub_eq_mulVec M (supp z) d hdS]
    convert hg using 2 with j
    simp [d]
  have hdi0 : d i0 ≠ 0 := by simpa [d] using hi0
  have hzpos : ∀ j, 0 ≤ z j := hz.1
  -- unboundedness contradiction
  have unb : ∀ e : ι → ℝ, M *ᵥ e = 0 → (∀ j, 0 ≤ e j) → c ⬝ᵥ e < 0 → False := by
    intro e hMe he hce
    set s := (c ⬝ᵥ z - L + 1) / (-(c ⬝ᵥ e)) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith [hL z hz]) (by linarith)
    have hf : PFeas M r (z + s • e) := ⟨fun j => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hzpos j) (mul_nonneg hs0 (he j)), by
      rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    have := hL _ hf
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have hse : s * (c ⬝ᵥ e) = -(c ⬝ᵥ z - L + 1) := by
      have hne : -(c ⬝ᵥ e) ≠ 0 := by linarith
      have h2 : (c ⬝ᵥ z - L + 1) / -(c ⬝ᵥ e) * -(c ⬝ᵥ e) = c ⬝ᵥ z - L + 1 := div_mul_cancel₀ _ hne
      rw [hs]; linear_combination -h2
    linarith
  obtain ⟨e, hMe, heS, hce, j0, hj0⟩ : ∃ e : ι → ℝ, M *ᵥ e = 0 ∧ (∀ j, j ∉ supp z → e j = 0) ∧
      c ⬝ᵥ e ≤ 0 ∧ ∃ j, e j < 0 := by
    obtain ⟨d1, hMd1, hd1S, hcd1, hd1i0⟩ : ∃ d1 : ι → ℝ, M *ᵥ d1 = 0 ∧
        (∀ j, j ∉ supp z → d1 j = 0) ∧ c ⬝ᵥ d1 ≤ 0 ∧ d1 i0 ≠ 0 := by
      by_cases h : c ⬝ᵥ d ≤ 0
      · exact ⟨d, hMd, hdS, h, hdi0⟩
      · refine ⟨-d, by rw [mulVec_neg, hMd, neg_zero], fun j hj => by simp [hdS j hj], ?_, ?_⟩
        · rw [dotProduct_neg]; linarith
        · simpa using hdi0
    by_cases hneg : ∃ j, d1 j < 0
    · exact ⟨d1, hMd1, hd1S, hcd1, hneg⟩
    push_neg at hneg
    rcases hcd1.lt_or_eq with hlt | heq
    · exact (unb d1 hMd1 hneg hlt).elim
    · refine ⟨-d1, by rw [mulVec_neg, hMd1, neg_zero], fun j hj => by simp [hd1S j hj],
        by rw [dotProduct_neg, heq, neg_zero], i0, ?_⟩
      have := lt_of_le_of_ne (hneg i0) (Ne.symm hd1i0)
      simp only [Pi.neg_apply]; linarith
  let P := Finset.univ.filter (fun j => e j < 0)
  obtain ⟨jm, hjmP, hjm⟩ := P.exists_min_image (fun j => z j / (-e j)) ⟨j0, by simp [P, hj0]⟩
  have hejm : e jm < 0 := by simpa [P] using hjmP
  set t := z jm / (-e jm) with ht
  have ht0 : 0 ≤ t := div_nonneg (hzpos jm) (by linarith)
  let z' := z + t • e
  have hz' : PFeas M r z' := by
    refine ⟨fun j => ?_, by simp only [z']; rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hej : e j < 0
    · have h1 : t ≤ z j / (-e j) := hjm j (by simp [P, hej])
      rw [le_div_iff₀ (by linarith)] at h1
      linarith
    · push_neg at hej
      exact add_nonneg (hzpos j) (mul_nonneg ht0 hej)
  have hsub : supp z' ⊆ supp z := by
    intro j hj
    rw [mem_supp] at hj ⊢
    intro hzj
    apply hj
    have : e j = 0 := by
      by_contra hne
      exact absurd (heS j) (by
        intro h'
        have : j ∉ supp z := by rw [mem_supp]; exact fun h => h hzj
        exact hne (h' this))
    simp [z', hzj, this]
  have hjm_in : jm ∈ supp z := by
    by_contra h; exact absurd (heS jm h) (ne_of_lt hejm)
  have hjm_out : jm ∉ supp z' := by
    rw [mem_supp, not_not]
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht]
    have hne : e jm ≠ 0 := ne_of_lt hejm
    rw [div_neg, neg_mul, div_mul_cancel₀ _ hne]; ring
  have hlt : (supp z').card < n := by
    rw [← hn]
    exact Finset.card_lt_card ⟨hsub, fun h => hjm_out (h hjm_in)⟩
  obtain ⟨z'', h1, h2, h3, h4⟩ := ih _ hlt z' rfl hz'
  refine ⟨z'', h1, le_trans h2 ?_, h3.trans hsub, h4⟩
  simp only [z', dotProduct_add, dotProduct_smul, smul_eq_mul]
  nlinarith

lemma colLI_unique (M : Matrix κ ι ℝ) (z1 z2 : ι → ℝ) (h : supp z1 = supp z2)
    (hli : ColLI M (supp z1)) (hM : M *ᵥ z1 = M *ᵥ z2) : z1 = z2 := by
  have hw : ∀ j, j ∉ supp z1 → (z1 - z2) j = 0 := by
    intro j hj
    have hj2 : j ∉ supp z2 := h ▸ hj
    rw [mem_supp, not_not] at hj hj2
    simp [hj, hj2]
  have hsum := sum_sub_eq_mulVec M (supp z1) (z1 - z2) hw
  rw [mulVec_sub, hM, sub_self] at hsum
  have := Fintype.linearIndependent_iff.mp hli (fun j => (z1 - z2) j) hsum
  funext j
  by_cases hj : j ∈ supp z1
  · have := this ⟨j, hj⟩; simp only [Pi.sub_apply] at this; linarith
  · have := hw j hj; simp only [Pi.sub_apply] at this; linarith

lemma attain (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) (z0 : ι → ℝ) (hz0 : PFeas M r z0) :
    ∃ zs, PFeas M r zs ∧ ColLI M (supp zs) ∧ ∀ z, PFeas M r z → c ⬝ᵥ zs ≤ c ⬝ᵥ z := by
  let F : Set (ι → ℝ) := {z | PFeas M r z ∧ ColLI M (supp z)}
  have hinj : Set.InjOn supp F := by
    intro z1 h1 z2 h2 h
    exact colLI_unique M z1 z2 h h1.2 (by rw [h1.1.2, h2.1.2])
  have hfin : F.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  obtain ⟨z1, hz1, _, _, hz1li⟩ := reduce M r c L hL _ z0 rfl hz0
  obtain ⟨zs, hzs, hmin⟩ := Set.exists_min_image F (fun z => c ⬝ᵥ z) hfin ⟨z1, hz1, hz1li⟩
  refine ⟨zs, hzs.1, hzs.2, fun z hz => ?_⟩
  obtain ⟨z', hz', hc', _, hli'⟩ := reduce M r c L hL _ z rfl hz
  exact le_trans (hmin z' ⟨hz', hli'⟩) hc'


def cone (M : Matrix κ ι ℝ) : Set (κ → ℝ) := (M.mulVecLin) '' {z | ∀ j, 0 ≤ z j}

lemma cone_closed (M : Matrix κ ι ℝ) : IsClosed (cone M) := by
  have heq : cone M = ⋃ (S : Finset ι) (_ : ColLI M S),
      (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) '' {w | ∀ j, 0 ≤ w j} := by
    ext t
    simp only [cone, Set.mem_image, Set.mem_setOf_eq, Set.mem_iUnion, mulVecLin_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨z', hz', _, _, hli⟩ := reduce M (M *ᵥ z) 0 0 (fun _ _ => by simp) _ z rfl ⟨hz, rfl⟩
      refine ⟨supp z', hli, fun j => z' j, fun j => hz'.1 j, ?_⟩
      rw [Fintype.linearCombination_apply, sum_sub_eq_mulVec M (supp z') z'
        (fun j hj => by rw [mem_supp, not_not] at hj; exact hj), hz'.2]
    · rintro ⟨S, _, w, hw, rfl⟩
      refine ⟨fun j => if h : j ∈ S then w ⟨j, h⟩ else 0, fun j => ?_, ?_⟩
      · by_cases h : j ∈ S <;> simp [h, hw]
      · rw [Fintype.linearCombination_apply, ← sum_sub_eq_mulVec M S _ (fun j hj => by simp [hj])]
        simp
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro S
  apply isClosed_iUnion_of_finite
  intro hli
  have hinj := linearIndependent_iff_injective_fintypeLinearCombination.mp hli
  have hker : LinearMap.ker (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  apply (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap
  have : {w : S → ℝ | ∀ j, 0 ≤ w j} = ⋂ j, {w | 0 ≤ w j} := by ext; simp
  rw [this]
  exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_apply j))

lemma farkas (M : Matrix κ ι ℝ) (t : κ → ℝ) (ht : t ∉ cone M) :
    ∃ y : κ → ℝ, (∀ j, 0 ≤ (y ᵥ* M) j) ∧ y ⬝ᵥ t < 0 := by
  have hconv : Convex ℝ (cone M) := by
    apply Convex.linear_image
    have : {z : ι → ℝ | ∀ j, 0 ≤ z j} = Set.Ici 0 := by ext; simp [Pi.le_def]
    rw [this]; exact convex_Ici 0
  obtain ⟨f, u, hfu, hut⟩ := geometric_hahn_banach_closed_point hconv (cone_closed M) ht
  have h0 : 0 < u := by
    have := hfu 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hneg : ∀ a ∈ cone M, f a ≤ 0 := by
    intro a ha
    by_contra h
    push_neg at h
    obtain ⟨z, hz, rfl⟩ := ha
    have hs : 0 ≤ u / f (M.mulVecLin z) + 1 := by positivity
    have hmem : (u / f (M.mulVecLin z) + 1) • M.mulVecLin z ∈ cone M :=
      ⟨(u / f (M.mulVecLin z) + 1) • z, fun j => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hs (hz j), by simp⟩
    have := hfu _ hmem
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ (ne_of_gt h)] at this
    linarith
  have hf : ∀ v : κ → ℝ, f v = ∑ i, v i * f (fun j => if i = j then 1 else 0) := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap v
    simpa using this
  refine ⟨fun i => - f (fun j => if i = j then 1 else 0), fun j => ?_, ?_⟩
  · have hmem : Mᵀ j ∈ cone M := ⟨Pi.single j 1, fun k => by
      by_cases h : k = j
      · subst h; simp
      · simp [h], by ext i; simp [mulVec, dotProduct, Pi.single_apply]⟩
    have := hneg _ hmem
    rw [hf] at this
    simp only [vecMul, dotProduct, transpose_apply] at this ⊢
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * M x j =
        -∑ x, M x j * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith
  · have := hf t
    simp only [dotProduct]
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * t x =
        -∑ x, t x * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith

end PCFarkas

section PC
lemma farkasL {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (L : κ → (ι → ℝ) →ₗ[ℝ] ℝ) (c : (ι → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ d, (∀ k, L k d ≤ 0) → 0 ≤ c d) :
    ∃ lam : κ → ℝ, (∀ k, 0 ≤ lam k) ∧ ∀ z, c z = - ∑ k, lam k * L k z := by
  have hlin : ∀ (g : (ι → ℝ) →ₗ[ℝ] ℝ) (z : ι → ℝ),
      g z = ∑ i, z i * g (fun j => if i = j then 1 else 0) := by
    intro g z
    have := LinearMap.pi_apply_eq_sum_univ g z
    simpa using this
  let M : Matrix ι κ ℝ := fun i k => - L k (fun j => if i = j then 1 else 0)
  let t : ι → ℝ := fun i => c (fun j => if i = j then 1 else 0)
  by_cases ht : t ∈ PCFarkas.cone M
  · obtain ⟨w, hw, hMw⟩ := ht
    refine ⟨w, hw, fun z => ?_⟩
    have hti : ∀ i, t i = ∑ k, M i k * w k := fun i => by
      rw [← hMw]; simp [Matrix.mulVec, dotProduct]
    rw [hlin c z]
    simp_rw [hlin (L _) z]
    calc ∑ i, z i * c (fun j => if i = j then 1 else 0) = ∑ i, z i * t i := rfl
      _ = ∑ i, z i * ∑ k, M i k * w k := by simp_rw [hti]
      _ = _ := by
        simp only [M, Finset.mul_sum]
        rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
  · exfalso
    obtain ⟨y, hy, hyt⟩ := PCFarkas.farkas M t ht
    have h1 : ∀ k, L k y ≤ 0 := by
      intro k
      have := hy k
      simp only [Matrix.vecMul, dotProduct, M] at this
      rw [hlin (L k) y]
      have e : ∑ x, y x * -(L k) (fun j => if x = j then 1 else 0) =
          -∑ x, y x * (L k) (fun j => if x = j then 1 else 0) := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      linarith
    have h2 : c y < 0 := by
      rw [hlin c y]; simpa [dotProduct, t] using hyt
    linarith [h y h1]
end PC

section MarkovTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

instance bmk_fc : FirstCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (FirstCountableTopology (n → n → ℝ))

lemma bmk_mul {A B : Matrix n n ℝ} (hA : IsMarkovMatrix A) (hB : IsMarkovMatrix B) :
    IsMarkovMatrix (A * B) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hB.2, mul_one]
    exact hA.2 i

lemma bmk_one : IsMarkovMatrix (1 : Matrix n n ℝ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.one_apply]; split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma bmk_pow {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (k : ℕ) : IsMarkovMatrix (P ^ k) := by
  induction k with
  | zero => simpa using (bmk_one (n := n))
  | succ k ih => rw [pow_succ]; exact bmk_mul ih hP

lemma bmk_le_one {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (i j : n) : P i j ≤ 1 := by
  rw [← hP.2 i]
  exact Finset.single_le_sum (f := fun j => P i j) (fun j _ => hP.1 i j) (Finset.mem_univ j)

lemma bmk_cesaro {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) :
    IsMarkovMatrix (cesaroMean P N) := by
  unfold cesaroMean
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (bmk_pow hP k).1 i j)
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [(bmk_pow hP _).2 i]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp

lemma bmk_P_mul_sum (P : Matrix n n ℝ) (N : ℕ) :
    P * ∑ k ∈ Finset.range (N + 1), P ^ k = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, ← pow_succ']
    abel

lemma bmk_sum_mul_P (P : Matrix n n ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), P ^ k) * P = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, ← pow_succ]
    abel

lemma bmk_P_cesaro (P : Matrix n n ℝ) (N : ℕ) :
    P * cesaroMean P N - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.mul_smul, bmk_P_mul_sum, smul_add]
  abel

lemma bmk_cesaro_P (P : Matrix n n ℝ) (N : ℕ) :
    cesaroMean P N * P - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.smul_mul, bmk_sum_mul_P, smul_add]
  abel

lemma bmk_D_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hb : ∀ N : ℕ, ‖(((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) i j‖ ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Real.norm_eq_abs]
    have h1 := (bmk_pow hP (N + 1)).1 i j
    have h2 := bmk_le_one (bmk_pow hP (N + 1)) i j
    have h3 : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := bmk_one.1 i j
    have h4 : (1 : Matrix n n ℝ) i j ≤ 1 := bmk_le_one bmk_one i j
    rw [abs_mul, abs_of_pos (by positivity), one_div]
    have : |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc ((N : ℝ) + 1)⁻¹ * |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ ((N : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  exact squeeze_zero_norm hb tendsto_one_div_add_atTop_nhds_zero_nat

lemma bmk_clus {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {L : Matrix n n ℝ}
    (hL : Tendsto (fun j => cesaroMean P (ns j)) atTop (𝓝 L)) : P * L = L ∧ L * P = L := by
  have hD := (bmk_D_tendsto hP).comp hns
  constructor
  · have h1 : Tendsto (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) atTop
        (𝓝 (P * L - L)) := (hL.const_mul P).sub hL
    have h2 : (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_P_cesaro P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)
  · have h1 : Tendsto (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) atTop
        (𝓝 (L * P - L)) := (hL.mul_const P).sub hL
    have h2 : (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_cesaro_P P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)

lemma bmk_avg_const (L : Matrix n n ℝ) (N : ℕ) :
    ((N : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (N + 1), L = L := by
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]

lemma bmk_cesaro_mul_fix {P L : Matrix n n ℝ} (h : P * L = L) (N : ℕ) :
    cesaroMean P N * L = L := by
  have hk : ∀ k : ℕ, P ^ k * L = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_fix_mul_cesaro {P L : Matrix n n ℝ} (h : L * P = L) (N : ℕ) :
    L * cesaroMean P N = L := by
  have hk : ∀ k : ℕ, L * P ^ k = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.mul_smul, Finset.mul_sum]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_compact : IsCompact {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} := by
  have e : {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} =
      Set.pi Set.univ (fun (_ : n) => Set.pi Set.univ (fun (_ : n) => Set.Icc (0 : ℝ) 1)) := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [e]
  exact isCompact_univ_pi (fun (_ : n) => isCompact_univ_pi (fun (_ : n) => isCompact_Icc))

theorem bmk_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) := by
  have hmem : ∀ N, cesaroMean P N ∈ {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} :=
    fun N i j => ⟨(bmk_cesaro hP N).1 i j, bmk_le_one (bmk_cesaro hP N) i j⟩
  obtain ⟨L, -, φ, hφ, hL⟩ := bmk_compact.tendsto_subseq hmem
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨hPL, hLP⟩ := bmk_clus hP hφt hL
  have main : Tendsto (cesaroMean P) atTop (𝓝 L) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨L', -, ψ, hψ, hL'⟩ := bmk_compact.tendsto_subseq (fun j => hmem (ns j))
    refine ⟨ψ, ?_⟩
    have hnsψ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
    obtain ⟨hPL', hL'P⟩ := bmk_clus hP hnsψ hL'
    have e1 : L * L' = L' := by
      have t : Tendsto (fun j => cesaroMean P (φ j) * L') atTop (𝓝 (L * L')) := hL.mul_const L'
      simp_rw [bmk_cesaro_mul_fix hPL'] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have e2 : L * L' = L := by
      have t : Tendsto (fun j => L * cesaroMean P ((ns ∘ ψ) j)) atTop (𝓝 (L * L')) :=
        hL'.const_mul L
      simp_rw [bmk_fix_mul_cesaro hLP] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have : L' = L := e1.symm.trans e2
    rw [this] at hL'
    exact hL'
  rw [limitMatrix, main.limUnder_eq]
  exact main

variable {P : Matrix n n ℝ}

lemma bmk_PL (hP : IsMarkovMatrix P) : P * limitMatrix P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).1

lemma bmk_LP (hP : IsMarkovMatrix P) : limitMatrix P * P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).2

lemma bmk_LL (hP : IsMarkovMatrix P) : limitMatrix P * limitMatrix P = limitMatrix P := by
  have t : Tendsto (fun N => cesaroMean P N * limitMatrix P) atTop
      (𝓝 (limitMatrix P * limitMatrix P)) := (bmk_tendsto hP).mul_const _
  simp_rw [bmk_cesaro_mul_fix (bmk_PL hP)] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_fixvec (hP : IsMarkovMatrix P) {v : n → ℝ} (hv : P *ᵥ v = v) :
    limitMatrix P *ᵥ v = v := by
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ v = v := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have hA : ∀ N, cesaroMean P N *ᵥ v = v := by
    intro N
    rw [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp_rw [hk]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by positivity), one_smul]
  have t : Tendsto (fun N => cesaroMean P N *ᵥ v) atTop (𝓝 (limitMatrix P *ᵥ v)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp (bmk_tendsto hP)
  simp_rw [hA] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_L_markov (hP : IsMarkovMatrix P) : IsMarkovMatrix (limitMatrix P) := by
  have hc : IsClosed {M : Matrix n n ℝ | IsMarkovMatrix M} := by
    have : {M : Matrix n n ℝ | IsMarkovMatrix M} =
        (⋂ i, ⋂ j, {M : Matrix n n ℝ | 0 ≤ M i j}) ∩ ⋂ i, {M : Matrix n n ℝ | ∑ j, M i j = 1} := by
      ext M; simp [IsMarkovMatrix]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
    · exact isClosed_eq (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp (continuous_apply i)) continuous_const
  exact hc.mem_of_tendsto (bmk_tendsto hP) (Eventually.of_forall fun N => bmk_cesaro hP N)

end MarkovTheory

section Bounds
variable {S A : Type*} [Fintype S] [Fintype A]
lemma k_avg_le {ι : Type*} (s : Finset ι) (w X : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hs : ∑ i ∈ s, w i = 1) (Y : ℝ) (h : ∀ i ∈ s, X i ≤ Y) : ∑ i ∈ s, w i * X i ≤ Y := by
  calc ∑ i ∈ s, w i * X i ≤ ∑ i ∈ s, w i * Y :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (hw i hi)
    _ = Y := by rw [← Finset.sum_mul, hs, one_mul]

lemma k_le_avg {ι : Type*} (s : Finset ι) (w X : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hs : ∑ i ∈ s, w i = 1) (Y : ℝ) (h : ∀ i ∈ s, Y ≤ X i) : Y ≤ ∑ i ∈ s, w i * X i := by
  calc Y = ∑ i ∈ s, w i * Y := by rw [← Finset.sum_mul, hs, one_mul]
    _ ≤ ∑ i ∈ s, w i * X i :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (hw i hi)

/-- A bound on all rewards. -/
noncomputable def kRm (M : StationaryMDP S A) : ℝ := ∑ s, ∑ a, |M.reward s a|

lemma k_abs_reward_le (M : StationaryMDP S A) (s : S) (a : A) : |M.reward s a| ≤ kRm M := by
  unfold kRm
  calc |M.reward s a| ≤ ∑ a', |M.reward s a'| :=
        Finset.single_le_sum (f := fun a' => |M.reward s a'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ a)
    _ ≤ ∑ s', ∑ a', |M.reward s' a'| :=
        Finset.single_le_sum (f := fun s' => ∑ a', |M.reward s' a'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ s)

lemma k_Rm_nonneg (M : StationaryMDP S A) : 0 ≤ kRm M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma k_tr_bound {M : StationaryMDP S A} (π : AvgHRPolicy M) :
    ∀ k t hist s, |totalReward π k t hist s| ≤ k * kRm M := by
  intro k
  induction k with
  | zero => intro t hist s; simp [totalReward]
  | succ k ih =>
    intro t hist s
    simp only [totalReward]
    rw [abs_le]
    push_cast
    constructor
    · apply k_le_avg _ _ _ (fun a _ => π.nonneg _ _ _ _) (π.sum_one _ _ _)
      intro a _
      have h1 : -(k * kRm M) ≤ ∑ j, M.trans s a j * totalReward π k (t + 1) (hist ++ [(s, a)]) j :=
        k_le_avg _ _ _ (fun j _ => M.trans_nonneg _ _ _) (M.trans_sum _ _) _
          (fun j _ => (abs_le.mp (ih _ _ _)).1)
      have h2 := (abs_le.mp (k_abs_reward_le M s a)).1
      linarith
    · apply k_avg_le _ _ _ (fun a _ => π.nonneg _ _ _ _) (π.sum_one _ _ _)
      intro a _
      have h1 : ∑ j, M.trans s a j * totalReward π k (t + 1) (hist ++ [(s, a)]) j ≤ k * kRm M :=
        k_avg_le _ _ _ (fun j _ => M.trans_nonneg _ _ _) (M.trans_sum _ _) _
          (fun j _ => (abs_le.mp (ih _ _ _)).2)
      have h2 := (abs_le.mp (k_abs_reward_le M s a)).2
      linarith

noncomputable def khc (h : S → ℝ) : ℝ := ∑ s, |h s|

lemma k_abs_h_le (h : S → ℝ) (s : S) : |h s| ≤ khc h :=
  Finset.single_le_sum (f := fun s => |h s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

lemma k_limsup_le_of_bounds (u : ℕ → ℝ) (g C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hu : ∀ N, u N ≤ N * g + C) (hb : ∀ N, |u N| ≤ N * R) :
    limsup (fun N : ℕ => u N / N) atTop ≤ g := by
  have hlow : ∀ N : ℕ, -R ≤ u N / N := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp [hR]
    · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [le_div_iff₀ hN]
      linarith [(abs_le.mp (hb N)).1]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine limsup_le_of_le (isCoboundedUnder_le_of_le atTop hlow) ?_
  filter_upwards [eventually_ge_atTop (⌈C / ε⌉₊ + 1)] with N hN
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hN
    linarith
  have hCN : C / ε ≤ N := by
    have := Nat.le_ceil (C / ε)
    have h2 : (⌈C / ε⌉₊ : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_right _ 1) hN
    linarith
  rw [div_le_iff₀ hNpos]
  have : C ≤ ε * N := by rwa [div_le_iff₀ hε, mul_comm] at hCN
  nlinarith [hu N]
lemma k_gain_bounds {M : StationaryMDP S A} (π : AvgHRPolicy M) (s : S) :
    gainInf π s ≤ gainSup π s ∧ gainSup π s ≤ kRm M ∧ -kRm M ≤ gainInf π s := by
  have hR := k_Rm_nonneg M
  have hb := fun N => k_tr_bound π N 0 [] s
  have hup : ∀ N : ℕ, totalReward π N 0 [] s / N ≤ kRm M := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp [hR]
    · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [div_le_iff₀ hN]; linarith [(abs_le.mp (hb N)).2]
  have hlow : ∀ N : ℕ, -kRm M ≤ totalReward π N 0 [] s / N := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp [hR]
    · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [le_div_iff₀ hN]; linarith [(abs_le.mp (hb N)).1]
  have bU : IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => totalReward π N 0 [] s / N) :=
    isBoundedUnder_of ⟨kRm M, hup⟩
  have bL : IsBoundedUnder (· ≥ ·) atTop (fun N : ℕ => totalReward π N 0 [] s / N) :=
    isBoundedUnder_of ⟨-kRm M, hlow⟩
  refine ⟨liminf_le_limsup bU bL, ?_, ?_⟩
  · exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop hlow) (Eventually.of_forall hup)
  · exact le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hup) (Eventually.of_forall hlow)

lemma k_bdd_inf {M : StationaryMDP S A} (s : S) :
    BddAbove (Set.range fun π : AvgHRPolicy M => gainInf π s) :=
  ⟨kRm M, by rintro _ ⟨π, rfl⟩; exact (k_gain_bounds π s).1.trans (k_gain_bounds π s).2.1⟩


lemma k_tr_upper_SH {M : StationaryMDP S A} (R : AvgHRPolicy M) (φ u : S → ℝ)
    (hSH : SuperharmonicPair M φ u) :
    ∀ k t hist s, totalReward R k t hist s ≤ k * φ s + u s + khc u := by
  intro k
  induction k with
  | zero =>
    intro t hist s
    simp only [totalReward, Nat.cast_zero, zero_mul, zero_add]
    linarith [(abs_le.mp (k_abs_h_le u s)).1]
  | succ k ih =>
    intro t hist s
    simp only [totalReward]
    apply k_avg_le _ _ _ (fun a _ => R.nonneg _ _ _ _) (R.sum_one _ _ _)
    intro a ha
    have h1 : ∑ j, M.trans s a j * totalReward R k (t + 1) (hist ++ [(s, a)]) j ≤
        ∑ j, M.trans s a j * (k * φ j + u j + khc u) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih _ _ _) (M.trans_nonneg _ _ _)
    have e1 : ∑ j, M.trans s a j * (k * φ j) = k * ∑ j, M.trans s a j * φ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    have e2 : ∑ j, M.trans s a j * khc u = khc u := by
      rw [← Finset.sum_mul, M.trans_sum, one_mul]
    have h2 : ∑ j, M.trans s a j * (k * φ j + u j + khc u) =
        k * ∑ j, M.trans s a j * φ j + ∑ j, M.trans s a j * u j + khc u := by
      simp only [mul_add, Finset.sum_add_distrib, e1, e2]
    obtain ⟨h3, h4⟩ := hSH s a ha
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have h5 : (k:ℝ) * ∑ j, M.trans s a j * φ j ≤ k * φ s := mul_le_mul_of_nonneg_left h3 hk
    push_cast
    linarith

lemma k_gainInf_le_SH {M : StationaryMDP S A} (R : AvgHRPolicy M) (φ u : S → ℝ)
    (hSH : SuperharmonicPair M φ u) (i : S) : gainInf R i ≤ φ i := by
  have hC : 0 ≤ u i + khc u := by linarith [(abs_le.mp (k_abs_h_le u i)).1]
  exact (k_gain_bounds R i).1.trans (k_limsup_le_of_bounds _ (φ i) (u i + khc u) (kRm M) hC
    (k_Rm_nonneg M) (fun N => by have := k_tr_upper_SH R φ u hSH N 0 [] i; linarith)
    (fun N => k_tr_bound R N 0 [] i))

end Bounds

section Main
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma k_optGainInf_le_SH (M : StationaryMDP S A) (φ u : S → ℝ)
    (hSH : SuperharmonicPair M φ u) (i : S) : optGainInf M i ≤ φ i := by
  haveI : Nonempty (AvgHRPolicy M) := ⟨stationaryPolicy M (fun s => (M.admissible_nonempty s).choose)
    (fun s => (M.admissible_nonempty s).choose_spec)⟩
  unfold optGainInf
  exact ciSup_le fun R => k_gainInf_le_SH R φ u hSH i

lemma k_stateSum_eq (M : StationaryMDP S A) (x : Pair M → ℝ) (j : S) :
    stateSum M x j = ∑ p : Pair M, (if p.1.1 = j then (1:ℝ) else 0) * x p := by
  unfold stateSum; rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun p _ => by split_ifs <;> simp)

lemma k_pair_sum (M : StationaryMDP S A) (v : S → ℝ) (w : Pair M → ℝ) :
    ∑ j, v j * ∑ p : Pair M, ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * w p
      = ∑ p : Pair M, w p * (v p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * v j) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have : ∀ j, v j * (((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * w p) =
      (if p.1.1 = j then w p * v j else 0) - w p * (M.trans p.1.1 p.1.2 j * v j) := by
    intro j; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, mul_sub, Finset.mul_sum]

lemma k_state_sum2 (M : StationaryMDP S A) (v : S → ℝ) (x : Pair M → ℝ) :
    ∑ j, v j * stateSum M x j = ∑ p, x p * v p.1.1 := by
  simp_rw [k_stateSum_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have : ∀ j, v j * ((if p.1.1 = j then (1:ℝ) else 0) * x p) =
      if p.1.1 = j then x p * v j else 0 := by
    intro j; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_ite_eq]
  simp

lemma k_wd (M : StationaryMDP S A) (β : S → ℝ) (z : (Pair M → ℝ) × (Pair M → ℝ))
    (hz : z ∈ dualFeasible M β) (φ u : S → ℝ) :
    ∑ j, β j * φ j - dualObjective M z.1 =
      ∑ p, z.2 p * (φ p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * φ j) +
      ∑ p, z.1 p * (φ p.1.1 + u p.1.1 - M.reward p.1.1 p.1.2 -
        ∑ j, M.trans p.1.1 p.1.2 j * u j) := by
  obtain ⟨h1, h2, h3⟩ := hz
  have eβ : ∑ j, β j * φ j = ∑ j, φ j * stateSum M z.1 j + ∑ j, φ j * ∑ p : Pair M,
      ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.2 p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [← h2 j]; ring
  rw [k_state_sum2, k_pair_sum] at eβ
  have e0 : ∑ j, u j * ∑ p : Pair M,
      ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.1 p = 0 := by
    simp [h1]
  rw [k_pair_sum] at e0
  have eo : dualObjective M z.1 = ∑ p, z.1 p * M.reward p.1.1 p.1.2 :=
    Finset.sum_congr rfl (fun p _ => mul_comm _ _)
  rw [eo, eβ]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at e0 ⊢
  linarith

lemma k_cs (M : StationaryMDP S A) (β : S → ℝ) (z : (Pair M → ℝ) × (Pair M → ℝ))
    (hz : z ∈ dualFeasible M β) (φ u : S → ℝ) (hSH : SuperharmonicPair M φ u)
    (hle : ∑ j, β j * φ j ≤ dualObjective M z.1) (p : Pair M) :
    (0 < z.1 p → φ p.1.1 = ∑ j, M.trans p.1.1 p.1.2 j * φ j ∧
        φ p.1.1 + u p.1.1 = M.reward p.1.1 p.1.2 + ∑ j, M.trans p.1.1 p.1.2 j * u j) ∧
    (0 < z.2 p → φ p.1.1 = ∑ j, M.trans p.1.1 p.1.2 j * φ j) := by
  have hw := k_wd M β z hz φ u
  obtain ⟨h1, h2, h3⟩ := hz
  have hA : ∀ q ∈ (Finset.univ : Finset (Pair M)),
      0 ≤ z.2 q * (φ q.1.1 - ∑ j, M.trans q.1.1 q.1.2 j * φ j) := fun q _ =>
    mul_nonneg (h3 q).2 (by linarith [(hSH q.1.1 q.1.2 q.2).1])
  have hB : ∀ q ∈ (Finset.univ : Finset (Pair M)),
      0 ≤ z.1 q * (φ q.1.1 + u q.1.1 - M.reward q.1.1 q.1.2 -
        ∑ j, M.trans q.1.1 q.1.2 j * u j) := fun q _ =>
    mul_nonneg (h3 q).1 (by linarith [(hSH q.1.1 q.1.2 q.2).2])
  have hC : ∀ q ∈ (Finset.univ : Finset (Pair M)),
      0 ≤ z.1 q * (φ q.1.1 - ∑ j, M.trans q.1.1 q.1.2 j * φ j) := fun q _ =>
    mul_nonneg (h3 q).1 (by linarith [(hSH q.1.1 q.1.2 q.2).1])
  have sA := Finset.sum_nonneg hA
  have sB := Finset.sum_nonneg hB
  have sA0 : ∑ q, z.2 q * (φ q.1.1 - ∑ j, M.trans q.1.1 q.1.2 j * φ j) = 0 := by linarith
  have sB0 : ∑ q, z.1 q * (φ q.1.1 + u q.1.1 - M.reward q.1.1 q.1.2 -
        ∑ j, M.trans q.1.1 q.1.2 j * u j) = 0 := by linarith
  have sC0 : ∑ q, z.1 q * (φ q.1.1 - ∑ j, M.trans q.1.1 q.1.2 j * φ j) = 0 := by
    rw [← k_pair_sum]; simp [h1]
  have tA := (Finset.sum_eq_zero_iff_of_nonneg hA).1 sA0 p (Finset.mem_univ _)
  have tB := (Finset.sum_eq_zero_iff_of_nonneg hB).1 sB0 p (Finset.mem_univ _)
  have tC := (Finset.sum_eq_zero_iff_of_nonneg hC).1 sC0 p (Finset.mem_univ _)
  refine ⟨fun hx => ⟨?_, ?_⟩, fun hy => ?_⟩
  · rcases mul_eq_zero.1 tC with h | h
    · linarith
    · linarith
  · rcases mul_eq_zero.1 tB with h | h
    · linarith
    · linarith
  · rcases mul_eq_zero.1 tA with h | h
    · linarith
    · linarith

end Main
section Farkas2
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

noncomputable def kLin {ι : Type*} [Fintype ι] (F : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun d := ∑ i, F i * d i
  map_add' a b := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

lemma kLin_apply {ι : Type*} [Fintype ι] (F : ι → ℝ) (d : ι → ℝ) :
    kLin F d = ∑ i, F i * d i := rfl

lemma kLin_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℝ) (i0 : ι) :
    kLin F (fun i => if i = i0 then 1 else 0) = F i0 := by
  rw [kLin_apply]; simp

noncomputable def kCoef (M : StationaryMDP S A) (β : S → ℝ) (V : ℝ) :
    Option (Option (Pair M ⊕ Pair M)) → Option (S ⊕ S) → ℝ
  | none, none => -1
  | none, some _ => 0
  | some none, none => -V
  | some none, some (Sum.inl j) => β j
  | some none, some (Sum.inr _) => 0
  | some (some (Sum.inl _)), none => 0
  | some (some (Sum.inl p)), some (Sum.inl j) =>
      M.trans p.1.1 p.1.2 j - (if p.1.1 = j then 1 else 0)
  | some (some (Sum.inl _)), some (Sum.inr _) => 0
  | some (some (Sum.inr p)), none => M.reward p.1.1 p.1.2
  | some (some (Sum.inr p)), some (Sum.inl j) => -(if p.1.1 = j then 1 else 0)
  | some (some (Sum.inr p)), some (Sum.inr j) =>
      M.trans p.1.1 p.1.2 j - (if p.1.1 = j then 1 else 0)

lemma kLin_expand (F : Option (S ⊕ S) → ℝ) (d : Option (S ⊕ S) → ℝ) :
    kLin F d = F none * d none + ∑ j, F (some (Sum.inl j)) * d (some (Sum.inl j)) +
      ∑ j, F (some (Sum.inr j)) * d (some (Sum.inr j)) := by
  rw [kLin_apply, Fintype.sum_option, Fintype.sum_sum_type]; ring

lemma k_delta_sum (c g : S → ℝ) (i : S) :
    ∑ j, (c j - if i = j then (1:ℝ) else 0) * g j = ∑ j, c j * g j - g i := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

lemma k_delta_sum' (g : S → ℝ) (i : S) :
    ∑ j, (-(if i = j then (1:ℝ) else 0)) * g j = - g i := by
  simp only [neg_mul, Finset.sum_neg_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

lemma k_sum_div_add {ι : Type*} [Fintype ι] (c a b : ι → ℝ) (D : ℝ) :
    ∑ p, c p * ((a p + b p) / D) = (∑ p, c p * a p + ∑ p, c p * b p) / D := by
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl (fun p _ => by ring)

lemma k_stateSum_div (M : StationaryMDP S A) (a b : Pair M → ℝ) (D : ℝ) (j : S) :
    stateSum M (fun p => (a p + b p) / D) j = (stateSum M a j + stateSum M b j) / D := by
  unfold stateSum; rw [← Finset.sum_add_distrib, Finset.sum_div]

lemma k_exists_primal (M : StationaryMDP S A) (β : S → ℝ) (z : (Pair M → ℝ) × (Pair M → ℝ))
    (hopt : IsDualOptimal M β z) :
    ∃ φ u : S → ℝ, SuperharmonicPair M φ u ∧ ∑ j, β j * φ j ≤ dualObjective M z.1 := by
  classical
  by_contra hne
  push_neg at hne
  set V := dualObjective M z.1 with hV
  have hfar := farkasL (fun k => kLin (kCoef M β V k)) (kLin (kCoef M β V none)) (by
    intro d hd
    rw [kLin_expand]
    simp only [kCoef, zero_mul, Finset.sum_const_zero, add_zero]
    by_contra hneg
    push_neg at hneg
    set t := d none with ht
    have htpos : 0 < t := by linarith
    let φ : S → ℝ := fun j => d (some (Sum.inl j)) / t
    let u : S → ℝ := fun j => d (some (Sum.inr j)) / t
    have hSH : SuperharmonicPair M φ u := by
      intro i a ha
      have c1 := hd (some (some (Sum.inl ⟨(i, a), ha⟩)))
      have c2 := hd (some (some (Sum.inr ⟨(i, a), ha⟩)))
      simp only [kLin_expand, kCoef, zero_mul, Finset.sum_const_zero, add_zero,
        zero_add] at c1 c2
      rw [k_delta_sum] at c1 c2
      rw [k_delta_sum'] at c2
      have e1 : ∑ j, M.trans i a j * φ j = (∑ j, M.trans i a j * d (some (Sum.inl j))) / t := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun j _ => by simp only [φ]; ring)
      have e2 : ∑ j, M.trans i a j * u j = (∑ j, M.trans i a j * d (some (Sum.inr j))) / t := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun j _ => by simp only [u]; ring)
      constructor
      · rw [e1]
        exact div_le_div_of_nonneg_right (by linarith) htpos.le
      · rw [e2]
        have key : M.reward i a * t + ∑ j, M.trans i a j * d (some (Sum.inr j)) ≤
            d (some (Sum.inl i)) + d (some (Sum.inr i)) := by linarith
        calc M.reward i a + (∑ j, M.trans i a j * d (some (Sum.inr j))) / t
            = (M.reward i a * t + ∑ j, M.trans i a j * d (some (Sum.inr j))) / t := by
              rw [add_div, mul_div_assoc, div_self htpos.ne', mul_one]
          _ ≤ (d (some (Sum.inl i)) + d (some (Sum.inr i))) / t :=
              div_le_div_of_nonneg_right key htpos.le
          _ = φ i + u i := by simp only [φ, u]; ring
    have h4 := hne φ u hSH
    have c3 := hd (some none)
    simp only [kLin_expand, kCoef, zero_mul, Finset.sum_const_zero, add_zero] at c3
    have e3 : ∑ j, β j * φ j = (∑ j, β j * d (some (Sum.inl j))) / t := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun j _ => by simp only [φ]; ring)
    rw [e3, lt_div_iff₀ htpos] at h4
    linarith)
  obtain ⟨lam, hlam, hid⟩ := hfar
  have hu : ∀ i0 : Option (S ⊕ S), kCoef M β V none i0 =
      -∑ k, lam k * kCoef M β V k i0 := by
    intro i0
    have := hid (fun i => if i = i0 then 1 else 0)
    simpa only [kLin_unit] using this
  set x : Pair M → ℝ := fun p => lam (some (some (Sum.inr p))) with hx
  set y : Pair M → ℝ := fun p => lam (some (some (Sum.inl p))) with hy
  set μ := lam (some none) with hμ
  set ν := lam none with hν
  have hnone := hu none
  simp only [Fintype.sum_option, Fintype.sum_sum_type, kCoef, mul_zero, Finset.sum_const_zero,
    zero_add] at hnone
  have hinl : ∀ j, ∑ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) -
      M.trans p.1.1 p.1.2 j) * y p + stateSum M x j = μ * β j := by
    intro j
    have := hu (some (Sum.inl j))
    simp only [Fintype.sum_option, Fintype.sum_sum_type, kCoef, mul_zero,
      zero_add] at this
    rw [k_stateSum_eq]
    have e1 : ∑ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * y p
        = -∑ p : Pair M, lam (some (some (Sum.inl p))) *
            (M.trans p.1.1 p.1.2 j - if p.1.1 = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun p _ => by simp only [y]; ring)
    have e2 : ∑ p : Pair M, (if p.1.1 = j then (1 : ℝ) else 0) * x p
        = -∑ p : Pair M, lam (some (some (Sum.inr p))) * -(if p.1.1 = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun p _ => by simp only [x]; ring)
    rw [e1, e2]; linarith
  have hinr : ∀ j, ∑ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) -
      M.trans p.1.1 p.1.2 j) * x p = 0 := by
    intro j
    have := hu (some (Sum.inr j))
    simp only [Fintype.sum_option, Fintype.sum_sum_type, kCoef, mul_zero, Finset.sum_const_zero,
      zero_add] at this
    have e1 : ∑ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * x p
        = -∑ p : Pair M, lam (some (some (Sum.inr p))) *
            (M.trans p.1.1 p.1.2 j - if p.1.1 = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun p _ => by simp only [x]; ring)
    rw [e1]; linarith
  have hobj : ∑ p : Pair M, M.reward p.1.1 p.1.2 * x p = 1 + ν + μ * V := by
    have e1 : ∑ p : Pair M, M.reward p.1.1 p.1.2 * x p =
        ∑ p : Pair M, lam (some (some (Sum.inr p))) * M.reward p.1.1 p.1.2 :=
      Finset.sum_congr rfl (fun p _ => by simp only [x]; ring)
    rw [e1]; linarith
  have hμ0 : 0 ≤ μ := hlam _
  have hν0 : 0 ≤ ν := hlam _
  set D := 1 + μ with hD
  have hDpos : 0 < D := by linarith
  obtain ⟨h1, h2, h3⟩ := hopt.1
  let z' : (Pair M → ℝ) × (Pair M → ℝ) :=
    (fun p => (z.1 p + x p) / D, fun p => (z.2 p + y p) / D)
  have hz' : z' ∈ dualFeasible M β := by
    refine ⟨fun j => ?_, fun j => ?_, fun p => ⟨?_, ?_⟩⟩
    · show ∑ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) *
          ((z.1 p + x p) / D) = 0
      rw [k_sum_div_add, h1 j, hinr j]; simp
    · show stateSum M (fun p => (z.1 p + x p) / D) j + ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) *
          ((z.2 p + y p) / D) = β j
      rw [k_sum_div_add, k_stateSum_div, ← add_div, div_eq_iff hDpos.ne']
      have := h2 j
      have := hinl j
      rw [hD]; linarith
    · exact div_nonneg (add_nonneg (h3 p).1 (hlam _)) hDpos.le
    · exact div_nonneg (add_nonneg (h3 p).2 (hlam _)) hDpos.le
  have hle := hopt.2 z' hz'
  have eobj : dualObjective M z'.1 = (V + (1 + ν + μ * V)) / D := by
    show ∑ p : Pair M, M.reward p.1.1 p.1.2 * ((z.1 p + x p) / D) = _
    rw [k_sum_div_add, hobj] <;> rfl
  rw [eobj, div_le_iff₀ hDpos] at hle
  rw [hD] at hle
  nlinarith

end Farkas2
section Chain
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma k_Pf_markov (M : StationaryMDP S A) (f : S → A) : IsMarkovMatrix (Pf M f) :=
  ⟨fun i j => by simp only [Pf, Matrix.of_apply]; exact M.trans_nonneg _ _ _,
   fun i => by simp only [Pf, Matrix.of_apply]; exact M.trans_sum _ _⟩

lemma k_stat_total (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) :
    ∀ N t h s, totalReward (stationaryPolicy M f hf) N t h s =
      (∑ k ∈ Finset.range N, (Pf M f ^ k) *ᵥ rf M f) s := by
  intro N
  induction N with
  | zero => intro t h s; simp [totalReward]
  | succ N ih =>
    intro t h s
    have hq : ∀ t' hist' s' a, (stationaryPolicy M f hf).q t' hist' s' a =
        if a = f s' then 1 else 0 := fun _ _ _ _ => rfl
    simp only [totalReward, hq]
    rw [Finset.sum_eq_single_of_mem (f s) (hf s) (fun b _ hb => by simp [hb])]
    simp only [if_true, one_mul, ih]
    have hv : (∑ k ∈ Finset.range (N+1), (Pf M f ^ k) *ᵥ rf M f) =
        rf M f + Pf M f *ᵥ (∑ k ∈ Finset.range N, (Pf M f ^ k) *ᵥ rf M f) := by
      rw [Finset.sum_range_succ', Matrix.mulVec_sum, pow_zero, Matrix.one_mulVec,
        add_comm (rf M f)]
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ', ← Matrix.mulVec_mulVec])
    rw [hv]
    rfl

lemma k_pow_fix (P : Matrix S S ℝ) (φ : S → ℝ) (hφ : P *ᵥ φ = φ) (N : ℕ) :
    (P ^ N) *ᵥ φ = φ := by
  induction N with
  | zero => simp
  | succ N ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hφ]

lemma k_tele (P : Matrix S S ℝ) (φ u r : S → ℝ) (hφ : P *ᵥ φ = φ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (P ^ k) *ᵥ r = (N : ℝ) • φ + u - (P ^ N) *ᵥ u +
      ∑ k ∈ Finset.range N, (P ^ k) *ᵥ (r - φ - u + P *ᵥ u) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_sub, k_pow_fix P φ hφ N,
      Matrix.mulVec_mulVec, ← pow_succ]
    push_cast
    rw [add_smul, one_smul]
    abel

lemma k_avg_tendsto (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (φ u : S → ℝ) (hφ : Pf M f *ᵥ φ = φ) (i : S)
    (hLw : (limitMatrix (Pf M f) *ᵥ (rf M f - φ - u + Pf M f *ᵥ u)) i = 0) :
    gainInf (stationaryPolicy M f hf) i = φ i := by
  set P := Pf M f with hPdef
  set w := rf M f - φ - u + P *ᵥ u with hw
  have hP := k_Pf_markov M f
  have hc : Tendsto (fun N : ℕ => (cesaroMean P (N - 1) *ᵥ w) i) atTop
      (𝓝 ((limitMatrix P *ᵥ w) i)) := by
    have t1 := (bmk_tendsto hP).comp (tendsto_sub_atTop_nat 1)
    have t2 : Tendsto (fun M' : Matrix S S ℝ => (M' *ᵥ w) i) (𝓝 (limitMatrix P))
        (𝓝 ((limitMatrix P *ᵥ w) i)) :=
      ((continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)).tendsto _
    exact t2.comp t1
  have hb : ∀ N : ℕ, |((P ^ N) *ᵥ u) i| ≤ khc u := by
    intro N
    have hPN := bmk_pow hP N
    calc |((P ^ N) *ᵥ u) i| = |∑ j, (P ^ N) i j * u j| := rfl
      _ ≤ ∑ j, |(P ^ N) i j * u j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |u j| := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul, abs_of_nonneg (hPN.1 i j)]
          exact mul_le_of_le_one_left (abs_nonneg _) (bmk_le_one hPN i j))
      _ = khc u := rfl
  have hu0 : Tendsto (fun N : ℕ => (u i - ((P ^ N) *ᵥ u) i) / N) atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => (2 * khc u) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm (fun N => ?_) h2
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have := hb N
    have := k_abs_h_le u i
    calc |u i - ((P ^ N) *ᵥ u) i| ≤ |u i| + |((P ^ N) *ᵥ u) i| := abs_sub _ _
      _ ≤ 2 * khc u := by linarith
  have key : ∀ N : ℕ, 1 ≤ N → totalReward (stationaryPolicy M f hf) N 0 [] i / N =
      φ i + (u i - ((P ^ N) *ᵥ u) i) / N + (cesaroMean P (N - 1) *ᵥ w) i := by
    intro N hN
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    rw [k_stat_total, k_tele P φ u (rf M f) hφ]
    simp only [Nat.add_sub_cancel, cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    have hm : (0:ℝ) < (m:ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring
  have ht : Tendsto (fun N : ℕ => totalReward (stationaryPolicy M f hf) N 0 [] i / N) atTop
      (𝓝 (φ i)) := by
    have := ((tendsto_const_nhds (x := φ i)).add hu0).add hc
    rw [hLw, add_zero, add_zero] at this
    exact this.congr' (eventually_atTop.2 ⟨1, fun N hN => (key N hN).symm⟩)
  unfold gainInf
  exact ht.liminf_eq

lemma k_graph_sum (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (F : Pair M → ℝ) (hF : ∀ p : Pair M, p.1.2 ≠ f p.1.1 → F p = 0) :
    ∑ p, F p = ∑ s, F ⟨(s, f s), hf s⟩ := by
  let e : S ↪ Pair M := ⟨fun s => ⟨(s, f s), hf s⟩, fun a b h => by
    simpa using congrArg (fun p : Pair M => p.1.1) h⟩
  calc ∑ p, F p = ∑ p ∈ Finset.univ.map e, F p := by
        refine (Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => hF p ?_)).symm
        intro h
        apply hp
        refine Finset.mem_map.2 ⟨p.1.1, Finset.mem_univ _, ?_⟩
        apply Subtype.ext
        exact Prod.ext rfl h.symm
    _ = ∑ s, F (e s) := Finset.sum_map _ _ _
    _ = ∑ s, F ⟨(s, f s), hf s⟩ := rfl

lemma k_stateSum_nonneg (M : StationaryMDP S A) (x : Pair M → ℝ) (hx : ∀ p, 0 ≤ x p) (j : S) :
    0 ≤ stateSum M x j := Finset.sum_nonneg (fun p _ => hx p)

lemma k_Ex_closed (M : StationaryMDP S A) (β : S → ℝ) (z : (Pair M → ℝ) × (Pair M → ℝ))
    (hz : z ∈ dualFeasible M β) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (hsel : IsSelection M z.1 z.2 f hf) (s k : S) (hs : 0 < stateSum M z.1 s)
    (hk : ¬ 0 < stateSum M z.1 k) : M.trans s (f s) k = 0 := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hk0 : stateSum M z.1 k = 0 :=
    le_antisymm (not_lt.1 hk) (k_stateSum_nonneg M z.1 (fun p => (h3 p).1) k)
  have e := h1 k
  have e2 : ∑ p : Pair M, ((if p.1.1 = k then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 k) * z.1 p
      = stateSum M z.1 k - ∑ p : Pair M, M.trans p.1.1 p.1.2 k * z.1 p := by
    rw [k_stateSum_eq, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [e2, hk0] at e
  have hnn : ∀ p ∈ (Finset.univ : Finset (Pair M)), 0 ≤ M.trans p.1.1 p.1.2 k * z.1 p :=
    fun p _ => mul_nonneg (M.trans_nonneg _ _ _) (h3 p).1
  have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by linarith) ⟨(s, f s), hf s⟩
    (Finset.mem_univ _)
  have hxpos : 0 < z.1 ⟨(s, f s), hf s⟩ := (hsel s).1 hs
  rcases mul_eq_zero.1 hz0 with h | h
  · exact h
  · exact absurd h hxpos.ne'

lemma k_L_zero (M : StationaryMDP S A) (β : S → ℝ) (z : (Pair M → ℝ) × (Pair M → ℝ))
    (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (hsel : IsSelection M z.1 z.2 f hf) (i j : S) (hj : ¬ 0 < stateSum M z.1 j) :
    limitMatrix (Pf M f) i j = 0 := by
  have hz : z ∈ dualFeasible M β := hext.1
  have hP := k_Pf_markov M f
  set L := limitMatrix (Pf M f) with hLdef
  have hLm := bmk_L_markov hP
  have hLP := bmk_LP hP
  have stat : ∀ k, ∑ s, L i s * M.trans s (f s) k = L i k := by
    intro k
    show ∑ s, limitMatrix (Pf M f) i s * Pf M f s k = limitMatrix (Pf M f) i k
    rw [← Matrix.mul_apply, hLP]
  let π' : S → ℝ := fun s => if 0 < stateSum M z.1 s then 0 else L i s
  have hπnn : ∀ s, 0 ≤ π' s := by
    intro s; simp only [π']; split_ifs
    · exact le_rfl
    · exact hLm.1 i s
  have hclosed := k_Ex_closed M β z hz f hf hsel
  have hout : ∀ k, ¬ 0 < stateSum M z.1 k → ∑ s, π' s * M.trans s (f s) k = L i k := by
    intro k hk
    rw [← stat k]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hs : 0 < stateSum M z.1 s
    · simp [π', hs, hclosed s k hs hk]
    · simp [π', hs]
  have htot : ∑ k, ∑ s, π' s * M.trans s (f s) k = ∑ k, π' k := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => by rw [← Finset.mul_sum, M.trans_sum, mul_one])
  have hin : ∀ k, 0 < stateSum M z.1 k → ∑ s, π' s * M.trans s (f s) k = 0 := by
    intro k0 hk0
    have hs1 := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k => 0 < stateSum M z.1 k) (fun k => ∑ s, π' s * M.trans s (f s) k)
    have hs2 := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k => 0 < stateSum M z.1 k) π'
    have e1 : ∑ k ∈ Finset.univ.filter (fun k => ¬ 0 < stateSum M z.1 k),
        ∑ s, π' s * M.trans s (f s) k =
        ∑ k ∈ Finset.univ.filter (fun k => ¬ 0 < stateSum M z.1 k), π' k :=
      Finset.sum_congr rfl (fun k hk => by
        have hk' := (Finset.mem_filter.1 hk).2
        rw [hout k hk']; simp [π', hk'])
    have e2 : ∑ k ∈ Finset.univ.filter (fun k => 0 < stateSum M z.1 k), π' k = 0 :=
      Finset.sum_eq_zero (fun k hk => by simp [π', (Finset.mem_filter.1 hk).2])
    have hF0 : ∑ k ∈ Finset.univ.filter (fun k => 0 < stateSum M z.1 k),
        ∑ s, π' s * M.trans s (f s) k = 0 := by linarith
    have hFnn : ∀ k ∈ Finset.univ.filter (fun k => 0 < stateSum M z.1 k),
        0 ≤ ∑ s, π' s * M.trans s (f s) k :=
      fun k _ => Finset.sum_nonneg (fun s _ => mul_nonneg (hπnn s) (M.trans_nonneg _ _ _))
    exact (Finset.sum_eq_zero_iff_of_nonneg hFnn).1 hF0 k0 (by simp [hk0])
  have stat' : ∀ k, ∑ s, π' s * M.trans s (f s) k = π' k := by
    intro k
    by_cases hk : 0 < stateSum M z.1 k
    · rw [hin k hk]; simp [π', hk]
    · rw [hout k hk]; simp [π', hk]
  -- the direction
  let d : Pair M → ℝ := fun p => if p.1.2 = f p.1.1 then π' p.1.1 else 0
  have hd : ∀ k, ∑ p : Pair M, ((if p.1.1 = k then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 k) *
      d p = 0 := by
    intro k
    rw [k_graph_sum M f hf _ (fun p hp => by simp [d, hp])]
    simp only [d, if_true]
    have : ∑ s, ((if s = k then (1:ℝ) else 0) - M.trans s (f s) k) * π' s =
        π' k - ∑ s, π' s * M.trans s (f s) k := by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      congr 1
      exact Finset.sum_congr rfl (fun s _ => mul_comm _ _)
    rw [this, stat' k, sub_self]
  -- epsilon
  obtain ⟨h1, h2, h3⟩ := hz
  set T := Finset.univ.filter (fun s => ¬ 0 < stateSum M z.1 s) with hT
  have hjT : j ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
  have hTne : T.Nonempty := ⟨j, hjT⟩
  set m := T.inf' hTne (fun s => z.2 ⟨(s, f s), hf s⟩) with hm
  have hmpos : 0 < m := by
    obtain ⟨s0, hs0, hm0⟩ := Finset.exists_mem_eq_inf' hTne (fun s => z.2 ⟨(s, f s), hf s⟩)
    rw [hm, hm0]
    exact (hsel s0).2 (Finset.mem_filter.1 hs0).2
  set B := 1 + ∑ s, π' s with hB
  have hBpos : 0 < B := by
    have := Finset.sum_nonneg (fun s (_ : s ∈ (Finset.univ : Finset S)) => hπnn s)
    linarith
  set ε := m / B with hε
  have hεpos : 0 < ε := div_pos hmpos hBpos
  have hbound : ∀ p : Pair M, ε * d p ≤ z.2 p := by
    intro p
    by_cases hp : p.1.2 = f p.1.1
    · have hpe : p = ⟨(p.1.1, f p.1.1), hf p.1.1⟩ := Subtype.ext (Prod.ext rfl hp)
      simp only [d, hp, if_true]
      by_cases hs : 0 < stateSum M z.1 p.1.1
      · simp only [π', hs, if_true, mul_zero]; exact (h3 p).2
      · have hsT : p.1.1 ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩
        have hmle : m ≤ z.2 ⟨(p.1.1, f p.1.1), hf p.1.1⟩ := Finset.inf'_le _ hsT
        have hπle : π' p.1.1 ≤ B := by
          have := Finset.single_le_sum (f := π') (fun s _ => hπnn s) (Finset.mem_univ p.1.1)
          linarith
        have : ε * π' p.1.1 ≤ m := by
          rw [hε, div_mul_eq_mul_div, div_le_iff₀ hBpos]
          exact mul_le_mul_of_nonneg_left hπle hmpos.le
        rw [hpe]; simp only at this ⊢; linarith
    · simp only [d, hp, if_false, mul_zero]; exact (h3 p).2
  have hdnn : ∀ p, 0 ≤ d p := by
    intro p; simp only [d]; split_ifs
    · exact hπnn _
    · exact le_rfl
  let z1 : (Pair M → ℝ) × (Pair M → ℝ) := (z.1, fun p => z.2 p + ε * d p)
  let z2 : (Pair M → ℝ) × (Pair M → ℝ) := (z.1, fun p => z.2 p - ε * d p)
  have hfeas : ∀ c : ℝ, (∀ p, 0 ≤ z.2 p + c * d p) →
      ((z.1, fun p => z.2 p + c * d p) : (Pair M → ℝ) × (Pair M → ℝ)) ∈ dualFeasible M β := by
    intro c hc
    refine ⟨fun k => h1 k, fun k => ?_, fun p => ⟨(h3 p).1, hc p⟩⟩
    have e : ∑ p : Pair M, ((if p.1.1 = k then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 k) *
        (z.2 p + c * d p) = ∑ p : Pair M, ((if p.1.1 = k then (1:ℝ) else 0) -
          M.trans p.1.1 p.1.2 k) * z.2 p + c * ∑ p : Pair M,
          ((if p.1.1 = k then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 k) * d p := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    show stateSum M z.1 k + ∑ p : Pair M, ((if p.1.1 = k then (1:ℝ) else 0) -
      M.trans p.1.1 p.1.2 k) * (z.2 p + c * d p) = β k
    rw [e, hd k, mul_zero, add_zero]
    exact h2 k
  have hz1 : z1 ∈ dualFeasible M β :=
    hfeas ε (fun p => add_nonneg (h3 p).2 (mul_nonneg hεpos.le (hdnn p)))
  have hz2 : z2 ∈ dualFeasible M β := by
    have := hfeas (-ε) (fun p => by have := hbound p; linarith)
    convert this using 2
    funext p; ring
  have hseg : z ∈ openSegment ℝ z1 z2 := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext p
    · simp [z1, z2]; ring
    · simp [z1, z2]; ring
  have := ((mem_extremePoints.1 hext).2 z1 hz1 z2 hz2 hseg).1
  have hp0 := congrFun (congrArg Prod.snd this) ⟨(j, f j), hf j⟩
  simp only [z1] at hp0
  have hεd : ε * d ⟨(j, f j), hf j⟩ = 0 := by linarith
  rcases mul_eq_zero.1 hεd with h | h
  · exact absurd h hεpos.ne'
  · simpa [d, π', hj] using h

end Chain
section Final
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma k_exists_pos (M : StationaryMDP S A) (w : Pair M → ℝ) (i : S) (h : 0 < stateSum M w i) :
    ∃ a, ∃ ha : a ∈ M.admissible i, 0 < w ⟨(i, a), ha⟩ := by
  by_contra hcon
  push_neg at hcon
  have : stateSum M w i ≤ 0 := by
    unfold stateSum
    refine Finset.sum_nonpos (fun p hp => ?_)
    have hp' := (Finset.mem_filter.1 hp).2
    obtain ⟨⟨i', a⟩, ha⟩ := p
    simp only at hp'
    subst hp'
    exact hcon a ha
  linarith

lemma k_selection_exists (M : StationaryMDP S A) (β : S → ℝ) (hβpos : ∀ j, 0 < β j)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hz : z ∈ dualFeasible M β) :
    ∃ (f : S → A) (hf : ∀ i, f i ∈ M.admissible i), IsSelection M z.1 z.2 f hf := by
  obtain ⟨h1, h2, h3⟩ := hz
  have key : ∀ i, ∃ a, ∃ ha : a ∈ M.admissible i,
      (i ∈ Ex M z.1 → 0 < z.1 ⟨(i, a), ha⟩) ∧ (i ∉ Ex M z.1 → 0 < z.2 ⟨(i, a), ha⟩) := by
    intro i
    by_cases hi : i ∈ Ex M z.1
    · obtain ⟨a, ha, hpos⟩ := k_exists_pos M z.1 i hi
      exact ⟨a, ha, fun _ => hpos, fun h => absurd hi h⟩
    · have hi0 : stateSum M z.1 i = 0 :=
        le_antisymm (not_lt.1 hi) (k_stateSum_nonneg M z.1 (fun p => (h3 p).1) i)
      have e := h2 i
      rw [hi0, zero_add] at e
      have hle : ∑ p : Pair M, ((if p.1.1 = i then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 i) * z.2 p
          ≤ stateSum M z.2 i := by
        rw [k_stateSum_eq]
        exact Finset.sum_le_sum (fun p _ => by
          have := mul_nonneg (M.trans_nonneg p.1.1 p.1.2 i) (h3 p).2
          nlinarith)
      have hpos : 0 < stateSum M z.2 i := by linarith [hβpos i]
      obtain ⟨a, ha, hp⟩ := k_exists_pos M z.2 i hpos
      exact ⟨a, ha, fun h => absurd h hi, fun _ => hp⟩
  choose f hf hsel using key
  exact ⟨f, hf, hsel⟩

lemma k_fix_of_cs (M : StationaryMDP S A) (β : S → ℝ) (z : (Pair M → ℝ) × (Pair M → ℝ))
    (hz : z ∈ dualFeasible M β) (φ u : S → ℝ) (hSH : SuperharmonicPair M φ u)
    (hle : ∑ j, β j * φ j ≤ dualObjective M z.1)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) (i : S) :
    φ i = ∑ j, M.trans i (f i) j * φ j := by
  have hcs := k_cs M β z hz φ u hSH hle ⟨(i, f i), hf i⟩
  by_cases hi : i ∈ Ex M z.1
  · exact (hcs.1 ((hsel i).1 hi)).1
  · exact hcs.2 ((hsel i).2 hi)

theorem prop421_core (M : StationaryMDP S A)
    (β : S → ℝ) (z : (Pair M → ℝ) × (Pair M → ℝ))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf)
    (φ u : S → ℝ) (hφu : IsPrimalOptimal M β φ u) :
    (∀ i, ∑ j, ((if i = j then (1 : ℝ) else 0) - M.trans i (f i) j) * φ j = 0) ∧
    (∀ i ∈ Ex M z.1,
      φ i + ∑ j, ((if i = j then (1 : ℝ) else 0) - M.trans i (f i) j) * u j = rf M f i) := by
  obtain ⟨φ', u', hSH', hle'⟩ := k_exists_primal M β z hopt
  have hle : ∑ j, β j * φ j ≤ dualObjective M z.1 := (hφu.2 φ' u' hSH').trans hle'
  have hds : ∀ (g : S → ℝ) (i : S),
      ∑ j, ((if i = j then (1 : ℝ) else 0) - M.trans i (f i) j) * g j =
        g i - ∑ j, M.trans i (f i) j * g j := by
    intro g i
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · rw [hds, ← k_fix_of_cs M β z hopt.1 φ u hφu.1 hle f hf hsel i, sub_self]
  · rw [hds]
    have := (k_cs M β z hopt.1 φ u hφu.1 hle ⟨(i, f i), hf i⟩).1 ((hsel i).1 hi)
    simp only [rf]
    linarith [this.2]

theorem thm424_core (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z) :
    (∃ (f : S → A) (hf : ∀ i, f i ∈ M.admissible i), IsSelection M z.1 z.2 f hf) ∧
    ∀ (f : S → A) (hf : ∀ i, f i ∈ M.admissible i), IsSelection M z.1 z.2 f hf →
      IsAvgOptimal M (stationaryPolicy M f hf) := by
  refine ⟨k_selection_exists M β hβpos z hopt.1, fun f hf hsel => ?_⟩
  obtain ⟨φ, u, hSH, hle⟩ := k_exists_primal M β z hopt
  have hφ : Pf M f *ᵥ φ = φ := by
    funext i
    exact (k_fix_of_cs M β z hopt.1 φ u hSH hle f hf hsel i).symm
  have hLw : ∀ i, (limitMatrix (Pf M f) *ᵥ (rf M f - φ - u + Pf M f *ᵥ u)) i = 0 := by
    intro i
    show ∑ j, limitMatrix (Pf M f) i j * (rf M f - φ - u + Pf M f *ᵥ u) j = 0
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hj : 0 < stateSum M z.1 j
    · have := (k_cs M β z hopt.1 φ u hSH hle ⟨(j, f j), hf j⟩).1 ((hsel j).1 hj)
      have e : (rf M f - φ - u + Pf M f *ᵥ u) j = 0 := by
        show M.reward j (f j) - φ j - u j + ∑ k, M.trans j (f j) k * u k = 0
        linarith [this.2]
      rw [e, mul_zero]
    · rw [k_L_zero M β z hext f hf hsel i j hj, zero_mul]
  intro i
  have hg := k_avg_tendsto M f hf φ u hφ i (hLw i)
  apply le_antisymm
  · unfold optGainInf
    exact le_ciSup (k_bdd_inf i) (stationaryPolicy M f hf)
  · rw [hg]; exact k_optGainInf_le_SH M φ u hSH i

end Final
section Exist
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

def kMat (M : StationaryMDP S A) : Matrix (S ⊕ S) (Pair M ⊕ Pair M) ℝ
  | Sum.inl j, Sum.inl p => (if p.1.1 = j then 1 else 0) - M.trans p.1.1 p.1.2 j
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr j, Sum.inl p => if p.1.1 = j then 1 else 0
  | Sum.inr j, Sum.inr p => (if p.1.1 = j then 1 else 0) - M.trans p.1.1 p.1.2 j

def kRhs (β : S → ℝ) : S ⊕ S → ℝ
  | Sum.inl _ => 0
  | Sum.inr j => β j

def kObj (M : StationaryMDP S A) : Pair M ⊕ Pair M → ℝ
  | Sum.inl p => -M.reward p.1.1 p.1.2
  | Sum.inr _ => 0

lemma k_mulVec1 (M : StationaryMDP S A) (a b : Pair M → ℝ) (j : S) :
    (kMat M *ᵥ Sum.elim a b) (Sum.inl j) = ∑ p : Pair M,
      ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * a p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, kMat, Sum.elim_inl, Sum.elim_inr,
    zero_mul, Finset.sum_const_zero, add_zero]

lemma k_mulVec2 (M : StationaryMDP S A) (a b : Pair M → ℝ) (j : S) :
    (kMat M *ᵥ Sum.elim a b) (Sum.inr j) = stateSum M a j + ∑ p : Pair M,
      ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * b p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, kMat, Sum.elim_inl, Sum.elim_inr]
  rw [k_stateSum_eq]

lemma k_feas_iff (M : StationaryMDP S A) (β : S → ℝ) (z : (Pair M → ℝ) × (Pair M → ℝ)) :
    PCFarkas.PFeas (kMat M) (kRhs β) (Sum.elim z.1 z.2) ↔ z ∈ dualFeasible M β := by
  constructor
  · rintro ⟨hnn, heq⟩
    refine ⟨fun j => ?_, fun j => ?_, fun p => ⟨hnn (Sum.inl p), hnn (Sum.inr p)⟩⟩
    · have := congrFun heq (Sum.inl j)
      rw [k_mulVec1] at this
      exact this
    · have := congrFun heq (Sum.inr j)
      rw [k_mulVec2] at this
      exact this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun q => ?_, ?_⟩
    · cases q with
      | inl p => exact (h3 p).1
      | inr p => exact (h3 p).2
    · funext k
      cases k with
      | inl j => rw [k_mulVec1, h1 j]; rfl
      | inr j => rw [k_mulVec2, h2 j]; rfl

lemma k_obj_dot (M : StationaryMDP S A) (a b : Pair M → ℝ) :
    kObj M ⬝ᵥ Sum.elim a b = -dualObjective M a := by
  simp only [dotProduct, Fintype.sum_sum_type, kObj, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, add_zero, dualObjective, neg_mul, Finset.sum_neg_distrib]

def kM0 (M : StationaryMDP S A) : StationaryMDP S A := { M with reward := fun _ _ => 0 }

lemma k_phi_nonneg (M : StationaryMDP S A) (φ u : S → ℝ)
    (h : ∀ i, ∀ a ∈ M.admissible i, ∑ j, M.trans i a j * φ j ≤ φ i ∧
      ∑ j, M.trans i a j * u j ≤ φ i + u i) (i : S) : 0 ≤ φ i := by
  have hSH : SuperharmonicPair (kM0 M) φ u := fun i a ha =>
    ⟨(h i a ha).1, by simpa [kM0] using (h i a ha).2⟩
  let g := fun s => (M.admissible_nonempty s).choose
  have hg : ∀ s, g s ∈ (kM0 M).admissible s := fun s => (M.admissible_nonempty s).choose_spec
  have h0 : ∀ N t hh s, totalReward (stationaryPolicy (kM0 M) g hg) N t hh s = 0 := by
    intro N
    induction N with
    | zero => intro t hh s; rfl
    | succ N ih =>
      intro t hh s
      simp only [totalReward, ih, mul_zero, Finset.sum_const_zero, add_zero]
      simp [kM0]
  have h1 := k_gainInf_le_SH (stationaryPolicy (kM0 M) g hg) φ u hSH i
  have hgi : gainInf (stationaryPolicy (kM0 M) g hg) i = 0 := by
    unfold gainInf; simp [h0]
  linarith

lemma k_colLI_eq {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (Mat : Matrix κ ι ℝ) (w w1 : ι → ℝ) (hli : PCFarkas.ColLI Mat (PCFarkas.supp w))
    (hs : ∀ q, w q = 0 → w1 q = 0) (hM : Mat *ᵥ w = Mat *ᵥ w1) : w = w1 := by
  have hw : ∀ j, j ∉ PCFarkas.supp w → (w - w1) j = 0 := by
    intro j hj
    rw [PCFarkas.mem_supp, not_not] at hj
    simp [hj, hs j hj]
  have hsum := PCFarkas.sum_sub_eq_mulVec Mat (PCFarkas.supp w) (w - w1) hw
  rw [Matrix.mulVec_sub, hM, sub_self] at hsum
  have := Fintype.linearIndependent_iff.mp hli (fun j => (w - w1) j) hsum
  funext j
  by_cases hj : j ∈ PCFarkas.supp w
  · have := this ⟨j, hj⟩; simp only [Pi.sub_apply] at this; linarith
  · have := hw j hj; simp only [Pi.sub_apply] at this; linarith

lemma k_exists_extreme_opt (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ j, 0 ≤ β j) :
    ∃ z, z ∈ Set.extremePoints ℝ (dualFeasible M β) ∧ IsDualOptimal M β z := by
  classical
  have hfeas : ∃ w, PCFarkas.PFeas (kMat M) (kRhs β) w := by
    by_contra hno
    have hnc : kRhs β ∉ PCFarkas.cone (kMat M) := by
      rintro ⟨w, hw, hMw⟩
      exact hno ⟨w, hw, by simpa using hMw⟩
    obtain ⟨y, hy, hyr⟩ := PCFarkas.farkas (kMat M) (kRhs β) hnc
    have hcolx : ∀ p : Pair M, (y ᵥ* kMat M) (Sum.inl p) =
        y (Sum.inl p.1.1) - ∑ j, M.trans p.1.1 p.1.2 j * y (Sum.inl j) + y (Sum.inr p.1.1) := by
      intro p
      simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, kMat]
      simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have : ∑ j, y (Sum.inl j) * M.trans p.1.1 p.1.2 j =
          ∑ j, M.trans p.1.1 p.1.2 j * y (Sum.inl j) :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [this]
    have hcoly : ∀ p : Pair M, (y ᵥ* kMat M) (Sum.inr p) =
        y (Sum.inr p.1.1) - ∑ j, M.trans p.1.1 p.1.2 j * y (Sum.inr j) := by
      intro p
      simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, kMat]
      simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, zero_add]
      have : ∑ j, y (Sum.inr j) * M.trans p.1.1 p.1.2 j =
          ∑ j, M.trans p.1.1 p.1.2 j * y (Sum.inr j) :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [this]
    have hnn : ∀ i, 0 ≤ y (Sum.inr i) := by
      intro i
      refine k_phi_nonneg M (fun j => y (Sum.inr j)) (fun j => y (Sum.inl j)) (fun i a ha => ?_) i
      have c1 := hy (Sum.inl ⟨(i, a), ha⟩)
      have c2 := hy (Sum.inr ⟨(i, a), ha⟩)
      rw [hcolx] at c1
      rw [hcoly] at c2
      simp only at c1 c2 ⊢
      constructor <;> linarith
    have : 0 ≤ y ⬝ᵥ kRhs β := by
      simp only [dotProduct, Fintype.sum_sum_type, kRhs, mul_zero, Finset.sum_const_zero,
        zero_add]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hnn j) (hβ j))
    linarith
  have hbound : ∀ w, PCFarkas.PFeas (kMat M) (kRhs β) w →
      -(∑ j, β j * kRm M) ≤ kObj M ⬝ᵥ w := by
    intro w hw
    have hwdec : Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := Sum.elim_comp_inl_inr w
    have hw' : ((w ∘ Sum.inl, w ∘ Sum.inr) : (Pair M → ℝ) × (Pair M → ℝ)) ∈ dualFeasible M β := by
      rw [← k_feas_iff]; simpa only [hwdec] using hw
    have hSH : SuperharmonicPair M (fun _ => kRm M) (fun _ => 0) := by
      intro i a ha
      constructor
      · simp only
        rw [← Finset.sum_mul, M.trans_sum, one_mul]
      · simp only [mul_zero, Finset.sum_const_zero, add_zero]
        exact le_trans (le_abs_self _) (k_abs_reward_le M i a)
    have hwd := k_wd M β _ hw' (fun _ => kRm M) (fun _ => 0)
    obtain ⟨h1, h2, h3⟩ := hw'
    have sA : 0 ≤ ∑ p : Pair M, (w ∘ Sum.inr) p * ((fun _ => kRm M) p.1.1 -
        ∑ j, M.trans p.1.1 p.1.2 j * (fun _ => kRm M) j) :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (h3 p).2 (by linarith [(hSH p.1.1 p.1.2 p.2).1]))
    have sB : 0 ≤ ∑ p : Pair M, (w ∘ Sum.inl) p * ((fun _ => kRm M) p.1.1 +
        (fun _ => (0:ℝ)) p.1.1 - M.reward p.1.1 p.1.2 -
        ∑ j, M.trans p.1.1 p.1.2 j * (fun _ => (0:ℝ)) j) :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (h3 p).1 (by linarith [(hSH p.1.1 p.1.2 p.2).2]))
    rw [← hwdec, k_obj_dot]
    simp only at hwd sA sB
    have : ∑ j, β j * kRm M - dualObjective M (w ∘ Sum.inl) ≥ 0 := by linarith
    linarith
  obtain ⟨w0, hw0⟩ := hfeas
  obtain ⟨zs, hzs, hli, hmin⟩ :=
    PCFarkas.attain (kMat M) (kRhs β) (kObj M) _ hbound w0 hw0
  let z : (Pair M → ℝ) × (Pair M → ℝ) := (zs ∘ Sum.inl, zs ∘ Sum.inr)
  have hzdec : Sum.elim z.1 z.2 = zs := Sum.elim_comp_inl_inr zs
  have hz : z ∈ dualFeasible M β := (k_feas_iff M β z).1 (by rw [hzdec]; exact hzs)
  have huniq : ∀ z1 ∈ dualFeasible M β, (∀ q, zs q = 0 → Sum.elim z1.1 z1.2 q = 0) → z1 = z := by
    intro z1 hz1 hs
    have h1 := (k_feas_iff M β z1).2 hz1
    have e := k_colLI_eq (kMat M) zs (Sum.elim z1.1 z1.2) hli hs (by rw [hzs.2, h1.2])
    ext p
    · have := congrFun e (Sum.inl p); simp only [Sum.elim_inl] at this; exact this.symm
    · have := congrFun e (Sum.inr p); simp only [Sum.elim_inr] at this; exact this.symm
  refine ⟨z, mem_extremePoints.2 ⟨hz, fun z1 hz1 z2 hz2 hseg => ?_⟩, hz, fun z' hz' => ?_⟩
  · obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hseg
    have c1 : ∀ p, a * z1.1 p + b * z2.1 p = zs (Sum.inl p) := fun p => by
      have := congrArg (fun w : (Pair M → ℝ) × (Pair M → ℝ) => w.1 p) hcomb
      simpa [z] using this
    have c2 : ∀ p, a * z1.2 p + b * z2.2 p = zs (Sum.inr p) := fun p => by
      have := congrArg (fun w : (Pair M → ℝ) × (Pair M → ℝ) => w.2 p) hcomb
      simpa [z] using this
    have n1 := hz1.2.2
    have n2 := hz2.2.2
    refine ⟨huniq z1 hz1 ?_, huniq z2 hz2 ?_⟩
    · intro q hq
      cases q with
      | inl p =>
        have := c1 p; rw [hq] at this
        have e : a * z1.1 p = 0 := by nlinarith [mul_nonneg ha.le (n1 p).1, mul_nonneg hb.le (n2 p).1]
        exact (mul_eq_zero.1 e).resolve_left ha.ne'
      | inr p =>
        have := c2 p; rw [hq] at this
        have e : a * z1.2 p = 0 := by nlinarith [mul_nonneg ha.le (n1 p).2, mul_nonneg hb.le (n2 p).2]
        exact (mul_eq_zero.1 e).resolve_left ha.ne'
    · intro q hq
      cases q with
      | inl p =>
        have := c1 p; rw [hq] at this
        have e : b * z2.1 p = 0 := by nlinarith [mul_nonneg ha.le (n1 p).1, mul_nonneg hb.le (n2 p).1]
        exact (mul_eq_zero.1 e).resolve_left hb.ne'
      | inr p =>
        have := c2 p; rw [hq] at this
        have e : b * z2.2 p = 0 := by nlinarith [mul_nonneg ha.le (n1 p).2, mul_nonneg hb.le (n2 p).2]
        exact (mul_eq_zero.1 e).resolve_left hb.ne'
  · have := hmin _ ((k_feas_iff M β z').2 hz')
    rw [← hzdec, k_obj_dot, k_obj_dot] at this
    linarith

lemma k_gainSup_le_SH (M : StationaryMDP S A) (R : AvgHRPolicy M) (φ u : S → ℝ)
    (hSH : SuperharmonicPair M φ u) (i : S) : gainSup R i ≤ φ i := by
  have hC : 0 ≤ u i + khc u := by linarith [(abs_le.mp (k_abs_h_le u i)).1]
  exact k_limsup_le_of_bounds _ (φ i) (u i + khc u) (kRm M) hC
    (k_Rm_nonneg M) (fun N => by have := k_tr_upper_SH R φ u hSH N 0 [] i; linarith)
    (fun N => k_tr_bound R N 0 [] i)

lemma k_value_SH (M : StationaryMDP S A) :
    ∃ φ u : S → ℝ, SuperharmonicPair M φ u ∧ ∀ i, optGainInf M i = φ i := by
  obtain ⟨z, hext, hopt⟩ := k_exists_extreme_opt M (fun _ => 1) (fun _ => zero_le_one)
  obtain ⟨f, hf, hsel⟩ := k_selection_exists M _ (fun _ => one_pos) z hopt.1
  have hA := (thm424_core M (fun _ => 1) (fun _ => one_pos) z hext hopt).2 f hf hsel
  obtain ⟨φ, u, hSH, hle⟩ := k_exists_primal M _ z hopt
  have hφ : Pf M f *ᵥ φ = φ := by
    funext i
    exact (k_fix_of_cs M _ z hopt.1 φ u hSH hle f hf hsel i).symm
  have hLw : ∀ i, (limitMatrix (Pf M f) *ᵥ (rf M f - φ - u + Pf M f *ᵥ u)) i = 0 := by
    intro i
    show ∑ j, limitMatrix (Pf M f) i j * (rf M f - φ - u + Pf M f *ᵥ u) j = 0
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hj : 0 < stateSum M z.1 j
    · have := (k_cs M _ z hopt.1 φ u hSH hle ⟨(j, f j), hf j⟩).1 ((hsel j).1 hj)
      have e : (rf M f - φ - u + Pf M f *ᵥ u) j = 0 := by
        show M.reward j (f j) - φ j - u j + ∑ k, M.trans j (f j) k * u k = 0
        linarith [this.2]
      rw [e, mul_zero]
    · rw [k_L_zero M _ z hext f hf hsel i j hj, zero_mul]
  refine ⟨φ, u, hSH, fun i => ?_⟩
  rw [← hA i]
  exact k_avg_tendsto M f hf φ u hφ i (hLw i)

theorem thm422_core (M : StationaryMDP S A) :
    IsAMDSuperharmonic M (optGainInf M) ∧
      ∀ φ' : S → ℝ, IsAMDSuperharmonic M φ' → ∀ i, optGainInf M i ≤ φ' i := by
  refine ⟨?_, fun φ' hφ' i => ?_⟩
  · obtain ⟨φ, u, hSH, heq⟩ := k_value_SH M
    have : optGainInf M = φ := funext heq
    exact ⟨u, this ▸ hSH⟩
  · obtain ⟨u', hu'⟩ := hφ'
    exact k_optGainInf_le_SH M φ' u' hu' i

theorem thm423_core (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (hopt : IsAvgOptimal M (stationaryPolicy M f hf)) :
    ∀ (R : AvgHRPolicy M) (i : S), gainSup R i ≤ gainSup (stationaryPolicy M f hf) i := by
  obtain ⟨φ, u, hSH, heq⟩ := k_value_SH M
  intro R i
  have h1 := k_gainSup_le_SH M R φ u hSH i
  have h2 := (k_gain_bounds (stationaryPolicy M f hf) i).1
  rw [hopt i, heq i] at h2
  linarith

end Exist

end KallenbergLP.AverageLP

open KallenbergLP.AverageLP


theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (hopt : IsAvgOptimal M (stationaryPolicy M f hf)) :
    ∀ (R : AvgHRPolicy M) (i : S), gainSup R i ≤ gainSup (stationaryPolicy M f hf) i := by
  exact thm423_core M f hf hopt
