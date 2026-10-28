-- Prove2me | solution 1 for KelsoCrawford.ContinuousCore.continuous_market_has_strict_core
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T06:11:13.14756+00:00
-- url     : https://prove2.me/submissions/c26f20b9-c5cc-4dab-a80c-35c5e89f042f

import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model

-- BEGIN DemandBounds
open Finset
open KelsoCrawford.ContinuousCore
open KelsoCrawford.Process (profit IsDemanded GrossSubstitutesOn)

namespace KCProof
variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

noncomputable def outputMass (M : Market W F) : ℝ := ∑ j, ∑ C : Finset W, |M.y j C|
noncomputable def reserveMass (M : Market W F) : ℝ := ∑ i, ∑ j, |M.σ i j|
noncomputable def bound (M : Market W F) : ℝ := 1 + 2 * outputMass M + reserveMass M

omit [DecidableEq W] [DecidableEq F] in
lemma outputMass_nonneg (M : Market W F) : 0 ≤ outputMass M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
omit [DecidableEq W] [DecidableEq F] in
lemma reserveMass_nonneg (M : Market W F) : 0 ≤ reserveMass M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
omit [DecidableEq W] [DecidableEq F] in
lemma output_abs_le (M : Market W F) (j : F) (C : Finset W) : |M.y j C| ≤ outputMass M := by
  exact (Finset.single_le_sum (fun x _ => abs_nonneg (M.y j x)) (Finset.mem_univ C)).trans
    (Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun C _ => abs_nonneg (M.y x C)) (Finset.mem_univ j))
omit [DecidableEq W] [DecidableEq F] in
lemma reserve_abs_le (M : Market W F) (i : W) (j : F) : |M.σ i j| ≤ reserveMass M := by
  exact (Finset.single_le_sum (fun x _ => abs_nonneg (M.σ i x)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun j _ => abs_nonneg (M.σ x j)) (Finset.mem_univ i))
omit [DecidableEq W] [DecidableEq F] in
lemma reserve_sum_le (M : Market W F) (j : F) (C : Finset W) :
    ∑ i ∈ C, |M.σ i j| ≤ reserveMass M := by
  calc
    _ ≤ ∑ i ∈ C, ∑ j, |M.σ i j| := Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (fun x _ => abs_nonneg (M.σ i x)) (Finset.mem_univ j)
    _ ≤ reserveMass M := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
      (fun i _ _ => Finset.sum_nonneg fun j _ => abs_nonneg (M.σ i j))
omit [DecidableEq W] [DecidableEq F] in
lemma bound_pos (M : Market W F) : 0 < bound M := by
  have := outputMass_nonneg M; have := reserveMass_nonneg M
  unfold bound; linarith
omit [DecidableEq W] [DecidableEq F] in
omit [DecidableEq W] [DecidableEq F] in
lemma reserve_abs_le_bound (M : Market W F) (i : W) (j : F) : |M.σ i j| ≤ bound M := by
  have := reserve_abs_le M i j; have := outputMass_nonneg M
  unfold bound; linarith
omit [DecidableEq F] in
lemma demanded_salary_le (M : Market W F) (j : F) (s : W → ℝ) (C : Finset W)
    (hd : IsDemanded (M.y j) s C) {i : W} (hi : i ∈ C) : s i ≤ bound M := by
  have h := hd (C.erase i)
  have hs := Finset.sum_erase_add C s hi
  have h1 := (le_abs_self (M.y j C)).trans (output_abs_le M j C)
  have h2 := (neg_le_abs (M.y j (C.erase i))).trans (output_abs_le M j (C.erase i))
  have h3 := reserveMass_nonneg M
  unfold profit at h
  unfold bound
  linarith
lemma ir_salary_abs_le (M : Market W F) (A : Allocation W F) (hA : M.IsIR A) (i : W) :
    |A.sal i| ≤ bound M := by
  let j := A.assign i
  have hi : i ∈ A.hired j := by simp [Allocation.hired, j]
  have hs := Finset.sum_erase_add (A.hired j) A.sal hi
  have hl : -(reserveMass M) ≤ ∑ k ∈ (A.hired j).erase i, A.sal k := by
    have hsum : ∑ k ∈ (A.hired j).erase i, -( |M.σ k j| ) ≤
        ∑ k ∈ (A.hired j).erase i, A.sal k := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hk)).2
      have h := hA.1 k
      rw [hk'] at h
      exact (neg_abs_le _).trans h
    have hb := reserve_sum_le M j ((A.hired j).erase i)
    rw [Finset.sum_neg_distrib] at hsum
    linarith
  have hp := hA.2 j
  have hy := (le_abs_self (M.y j (A.hired j))).trans (output_abs_le M j (A.hired j))
  have hlo := (neg_abs_le (M.σ i j)).trans (hA.1 i)
  have hr := reserve_abs_le_bound M i j
  have hY := outputMass_nonneg M
  apply abs_le.mpr
  constructor
  · linarith
  · unfold profit at hp
    unfold bound
    linarith
lemma exists_ir_box (M : Market W F) :
    ∃ L U : W → ℝ, ∀ A, M.IsIR A → ∀ i, L i ≤ A.sal i ∧ A.sal i ≤ U i := by
  refine ⟨fun _ => -bound M, fun _ => bound M, ?_⟩
  intro A hA i
  exact abs_le.mp (ir_salary_abs_le M A hA i)

omit [Fintype W] [Fintype F] [DecidableEq F] in
lemma reserve_profit_mono (M : Market W F) (hMP : M.MP) (j : F) {C D : Finset W}
    (hCD : C ⊆ D) : profit (M.y j) C (fun i => M.σ i j) ≤ profit (M.y j) D (fun i => M.σ i j) := by
  have hm : Monotone (fun C : Finset W => profit (M.y j) C (fun i => M.σ i j)) := by
    apply Finset.monotone_iff_forall_le_insert.mpr
    intro S i hi
    have h := hMP i j S hi
    simp only [profit, Finset.sum_insert hi]
    linarith
  exact hm hCD

omit [Fintype F] [DecidableEq F] in
lemma reserve_univ_demanded (M : Market W F) (hMP : M.MP) (j : F) :
    IsDemanded (M.y j) (fun i => M.σ i j) Finset.univ := by
  intro C
  exact reserve_profit_mono M hMP j (Finset.subset_univ C)

end KCProof
-- END DemandBounds

-- BEGIN DiscreteState
open Finset
open KelsoCrawford.ContinuousCore
open KelsoCrawford.Process (profit IsDemanded GrossSubstitutesOn)

namespace KCProof
variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

structure OfferState (W F : Type) (N : ℕ) where
  level : W → F → Fin (N + 1)
  offers : F → Finset W
  chosen : W → F

noncomputable instance {N : ℕ} : Fintype (OfferState W F N) := by
  classical
  exact Fintype.ofEquiv ((W → F → Fin (N+1)) × (F → Finset W) × (W → F))
    { toFun := fun x => ⟨x.1,x.2.1,x.2.2⟩
      invFun := fun s => ⟨s.level,s.offers,s.chosen⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable def OfferState.salary {N : ℕ} (M : Market W F) (δ : ℝ) (s : OfferState W F N)
    (i : W) (j : F) : ℝ := M.σ i j + (s.level i j).val * δ

def OfferState.Good {N : ℕ} (M : Market W F) (δ : ℝ) (s : OfferState W F N) : Prop :=
  (∀ j, IsDemanded (M.y j) (fun i => s.salary M δ i j) (s.offers j)) ∧
  (∀ i, i ∈ s.offers (s.chosen i)) ∧
  (∀ i j, i ∈ s.offers j → M.u i j (s.salary M δ i j) ≤ M.u i (s.chosen i) (s.salary M δ i (s.chosen i))) ∧
  (∀ i j, 0 < (s.level i j).val → M.u i j (s.salary M δ i j - δ) ≤ M.u i (s.chosen i) (s.salary M δ i (s.chosen i)))

def OfferState.mass {N : ℕ} (s : OfferState W F N) : ℕ := ∑ i, ∑ j, (s.level i j).val

def OfferState.Rejected {N : ℕ} (s : OfferState W F N) (i : W) (j : F) : Prop :=
  i ∈ s.offers j ∧ s.chosen i ≠ j

omit [Fintype W] [DecidableEq F] in
lemma favorite_exists (M : Market W F) (s : W → F → ℝ) (O : F → Finset W)
    (hc : ∀ i, ∃ j, i ∈ O j) :
    ∃ a : W → F, (∀ i, i ∈ O (a i)) ∧
      ∀ i j, i ∈ O j → M.u i j (s i j) ≤ M.u i (a i) (s i (a i)) := by
  classical
  have h : ∀ i, ∃ j, i ∈ O j ∧ ∀ j', i ∈ O j' → M.u i j' (s i j') ≤ M.u i j (s i j) := by
    intro i
    obtain ⟨j,hj⟩ := hc i
    obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun j => i ∈ O j)
      (fun j => M.u i j (s i j)) ⟨j,by simp [hj]⟩
    exact ⟨a,(Finset.mem_filter.mp ha).2,fun j' hj' => hmax j' (by simp [hj'])⟩
  choose a ha hm using h
  exact ⟨a,ha,hm⟩

omit [DecidableEq F] in
lemma initial_state [Nonempty F] (M : Market W F) (hMP : M.MP) (δ : ℝ) (N : ℕ) :
    ∃ s : OfferState W F N, s.Good M δ := by
  classical
  obtain ⟨a,ha,hm⟩ := favorite_exists M M.σ (fun _ => Finset.univ)
    (fun _ => ⟨Classical.choice inferInstance,Finset.mem_univ _⟩)
  refine ⟨⟨fun _ _ => 0,fun _ => Finset.univ,a⟩,?_,?_,?_,?_⟩
  · intro j; simpa [OfferState.salary] using reserve_univ_demanded M hMP j
  · exact ha
  · simpa [OfferState.salary] using hm
  · simp

omit [DecidableEq F] in
lemma state_step (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
    (hN : 2 * bound M + δ < (N : ℝ) * δ)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) Set.univ)
    (s : OfferState W F N) (hs : s.Good M δ) (hr : ∃ i j, s.Rejected i j) :
    ∃ t : OfferState W F N, t.Good M δ ∧ s.mass < t.mass := by
  classical
  have hcap : ∀ i j, s.Rejected i j → (s.level i j).val + 1 < N + 1 := by
    intro i j hij
    have hu := demanded_salary_le M j (fun i => s.salary M δ i j) (s.offers j) (hs.1 j) hij.1
    have hl := (neg_abs_le (M.σ i j)).trans' (neg_le_neg (reserve_abs_le_bound M i j))
    have hmul : (((s.level i j).val + 1 : ℕ) : ℝ) * δ < (N : ℝ) * δ := by
      simp only [Nat.cast_add,Nat.cast_one]
      unfold OfferState.salary at hu
      nlinarith
    have hlt : (s.level i j).val + 1 < N := by exact_mod_cast (lt_of_mul_lt_mul_right hmul hδ.le)
    omega
  let k : W → F → Fin (N+1) := fun i j => if h : s.Rejected i j then
    ⟨(s.level i j).val+1,hcap i j h⟩ else s.level i j
  let p : W → F → ℝ := fun i j => M.σ i j + (k i j).val * δ
  have hk : ∀ i j, (s.level i j).val ≤ (k i j).val := by
    intro i j; by_cases h : s.Rejected i j <;> simp [k,h]
  have hp : ∀ i j, s.salary M δ i j ≤ p i j := by
    intro i j
    dsimp [OfferState.salary,p]
    gcongr
    exact_mod_cast hk i j
  have heq : ∀ i j, ¬s.Rejected i j → p i j = s.salary M δ i j := by
    intro i j hij; simp [p,k,hij,OfferState.salary]
  have hnew : ∀ j, ∃ O, IsDemanded (M.y j) (fun i => p i j) O ∧
      ∀ i, i ∈ s.offers j → ¬s.Rejected i j → i ∈ O := by
    intro j
    obtain ⟨O,hO,hkeep⟩ := hGS j (fun i=>s.salary M δ i j) (Set.mem_univ _) (fun i=>p i j)
      (Set.mem_univ _) (fun i=>hp i j) (s.offers j) (hs.1 j)
    exact ⟨O,hO,fun i hi hn => hkeep (Finset.mem_filter.mpr ⟨hi,heq i j hn⟩)⟩
  choose O hO hkeep using hnew
  have hheld : ∀ i, i ∈ O (s.chosen i) := by
    intro i; exact hkeep (s.chosen i) i (hs.2.1 i) (by simp [OfferState.Rejected])
  obtain ⟨a,ha,hm⟩ := favorite_exists M p O (fun i => ⟨s.chosen i,hheld i⟩)
  let t : OfferState W F N := ⟨k,O,a⟩
  have htpay : ∀ i j, t.salary M δ i j = p i j := by intros; rfl
  have hinc : ∀ i, M.u i (s.chosen i) (s.salary M δ i (s.chosen i)) ≤ M.u i (a i) (p i (a i)) := by
    intro i
    have h := hm i (s.chosen i) (hheld i)
    rwa [heq i (s.chosen i) (by simp [OfferState.Rejected])] at h
  refine ⟨t,⟨?_,?_,?_,?_⟩,?_⟩
  · exact hO
  · exact ha
  · exact hm
  · intro i j hkpos
    change M.u i j (p i j-δ) ≤ M.u i (a i) (p i (a i))
    by_cases hij : s.Rejected i j
    · have hp' : p i j - δ = s.salary M δ i j := by
        simp [p,k,hij,OfferState.salary]; ring
      rw [hp']
      exact (hs.2.2.1 i j hij.1).trans (hinc i)
    · have hk' : 0 < (s.level i j).val := by simpa [t,k,hij] using hkpos
      rw [heq i j hij]
      exact (hs.2.2.2 i j hk').trans (hinc i)
  · obtain ⟨i,j,hij⟩ := hr
    apply Finset.sum_lt_sum
    · intro i' _; exact Finset.sum_le_sum fun j' _ => hk i' j'
    · refine ⟨i,Finset.mem_univ _,?_⟩
      apply Finset.sum_lt_sum
      · intro j' _; exact hk i j'
      · exact ⟨j,Finset.mem_univ _,by simp [t,k,hij]⟩

lemma stopped_state [Nonempty F] (M : Market W F) (hMP : M.MP) (δ : ℝ) (hδ : 0 < δ)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) Set.univ) :
    ∃ (N : ℕ) (s : OfferState W F N), s.Good M δ ∧ ∀ i j, i ∈ s.offers j → s.chosen i = j := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt ((2 * bound M + δ) / δ)
  have hN' : 2 * bound M + δ < (N:ℝ)*δ := (div_lt_iff₀ hδ).mp hN
  obtain ⟨s,hs⟩ := initial_state M hMP δ N
  obtain ⟨t,ht,hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun t : OfferState W F N => t.Good M δ)
    OfferState.mass ⟨s,by simp [hs]⟩
  have ht' := (Finset.mem_filter.mp ht).2
  refine ⟨N,t,ht',?_⟩
  intro i j hij
  by_contra hne
  obtain ⟨t',ht',hgt⟩ := state_step M δ hδ N hN' hGS t ht' ⟨i,j,hij,hne⟩
  have hle := hmax t' (by simp [ht'])
  omega

end KCProof
-- END DiscreteState

-- BEGIN DiscreteCore
open Finset
open KelsoCrawford.ContinuousCore
open KelsoCrawford.Process (profit IsDemanded GrossSubstitutesOn)

namespace KCProof
variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

lemma discrete_core_exists [Nonempty F] (M : Market W F) (hu : M.UtilityRegular)
    (hMP : M.MP) (hNFL : M.NFL) (hGS : ∀ j, GrossSubstitutesOn (M.y j) Set.univ)
    (δ : ℝ) (hδ : 0 < δ) : ∃ A, M.IsCore (M.grid δ) A := by
  classical
  obtain ⟨N,s,hs,hn⟩ := stopped_state M hMP δ hδ hGS
  let A : Allocation W F := ⟨s.chosen,fun i => s.salary M δ i (s.chosen i)⟩
  have hsets : ∀ j, A.hired j = s.offers j := by
    intro j
    ext i
    simp only [Allocation.hired,Finset.mem_filter,Finset.mem_univ,true_and]
    change s.chosen i = j ↔ i ∈ s.offers j
    exact ⟨fun h => h ▸ hs.2.1 i,hn i j⟩
  have hprofit : ∀ j, profit (M.y j) (A.hired j) A.sal =
      profit (M.y j) (s.offers j) (fun i => s.salary M δ i j) := by
    intro j
    rw [hsets]
    unfold profit
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    change s.salary M δ i (s.chosen i) = _
    rw [hn i j hi]
  refine ⟨A,⟨?_,?_,?_⟩⟩
  · constructor
    · intro i
      change M.σ i (s.chosen i) ≤ M.σ i (s.chosen i) + _
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ.le)
    · intro j
      rw [hprofit]
      have h := hs.1 j ∅
      simpa [profit,hNFL j] using h
  · intro i
    exact ⟨(s.level i (s.chosen i)).val,rfl⟩
  · rintro ⟨j,C,r,hr,hw,hp⟩
    have hrge : ∀ i ∈ C, s.salary M δ i j ≤ r i := by
      intro i hi
      obtain ⟨m,hm⟩ := hr i hi
      by_contra h
      have hlt : r i < s.salary M δ i j := lt_of_not_ge h
      have hmk : m < (s.level i j).val := by
        rw [hm] at hlt
        unfold OfferState.salary at hlt
        have hmul : (m:ℝ)*δ < ((s.level i j).val:ℝ)*δ := by linarith
        exact_mod_cast (lt_of_mul_lt_mul_right hmul hδ.le)
      have hkpos : 0 < (s.level i j).val := by omega
      have hprev : r i ≤ s.salary M δ i j - δ := by
        have hnat : m+1 ≤ (s.level i j).val := by omega
        have hreal : (m:ℝ)+1 ≤ ((s.level i j).val:ℝ) := by exact_mod_cast hnat
        rw [hm]
        unfold OfferState.salary
        nlinarith
      have hh := (hu i j).1.monotone hprev
      have hn' := hs.2.2.2 i j hkpos
      have hw' := hw i hi
      change M.u i (s.chosen i) (s.salary M δ i (s.chosen i)) < M.u i j (r i) at hw'
      linarith
    have hsum := Finset.sum_le_sum hrge
    have hd := hs.1 j C
    rw [hprofit] at hp
    unfold profit at hd hp
    linarith

end KCProof
-- END DiscreteCore

-- BEGIN StrictBlocking
open Filter Topology
open KelsoCrawford.ContinuousCore
open KelsoCrawford.Process (profit)

namespace KCProof
variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

noncomputable def step (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem step_pos (n : ℕ) : 0 < step n := by
  unfold step
  positivity

theorem step_tendsto : Tendsto step atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

omit [DecidableEq W] [Fintype F] in
theorem raise_to_strict (M : Market W F) (hu : M.UtilityRegular)
    (A : Allocation W F) (j : F) (C : Finset W) (r : W → ℝ)
    (hw : ∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i))
    (hp : profit (M.y j) (A.hired j) A.sal < profit (M.y j) C r) :
    M.CanStrictlyImprove anySalary A := by
  have hc : Tendsto (fun n => profit (M.y j) C (fun i => r i + step n)) atTop
      (𝓝 (profit (M.y j) C r)) := by
    unfold profit
    exact tendsto_const_nhds.sub (tendsto_finsetSum C fun i _ => by
      simpa using (tendsto_const_nhds (x := r i)).add step_tendsto)
  obtain ⟨n, hn⟩ := ((tendsto_const_nhds (x := profit (M.y j) (A.hired j) A.sal)).eventually_lt hc hp).exists
  refine ⟨j, C, (fun i => r i + step n), ?_, ?_, hn⟩
  · intro i _
    trivial
  · intro i hi
    exact (hw i hi).trans_lt ((hu i j).1 (lt_add_of_pos_right _ (step_pos n)))

omit [Fintype F] in
theorem strict_block_of_block (M : Market W F) (hu : M.UtilityRegular)
    (A : Allocation W F) : M.CanImprove anySalary A → M.CanStrictlyImprove anySalary A := by
  classical
  rintro ⟨j, C, r, _, hw, hp, hgain⟩
  rcases hgain with ⟨i₀, hi₀, hg⟩ | hg
  · have hc : Tendsto (fun n => M.u i₀ j (r i₀ - step n)) atTop (𝓝 (M.u i₀ j (r i₀))) :=
      (hu i₀ j).2.continuousAt.tendsto.comp (by simpa using (tendsto_const_nhds (x := r i₀)).sub step_tendsto)
    obtain ⟨n, hn⟩ := ((tendsto_const_nhds (x := M.u i₀ (A.assign i₀) (A.sal i₀))).eventually_lt hc hg).exists
    let r' : W → ℝ := fun i => r i - if i = i₀ then step n else 0
    have hs : ∑ i ∈ C, r' i = (∑ i ∈ C, r i) - step n := by
      simp [r', Finset.sum_sub_distrib, hi₀]
    apply raise_to_strict M hu A j C r'
    · intro i hi
      by_cases he : i = i₀
      · subst i
        simpa [r'] using hn.le
      · simpa [r', he] using hw i hi
    · unfold profit at hp ⊢
      rw [hs]
      have := step_pos n
      linarith
  · exact raise_to_strict M hu A j C r hw hg
end KCProof
-- END StrictBlocking

-- BEGIN GridCompactness
open Filter Topology
open KelsoCrawford.ContinuousCore
open KelsoCrawford.Process (profit)

namespace KCProof
variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

omit [DecidableEq W] [Fintype F] in
theorem ir_of_limit (M : Market W F) (A : ℕ → Allocation W F)
    (B : Allocation W F) (hA : ∀ n, M.IsIR (A n))
    (ha : ∀ n, (A n).assign = B.assign)
    (hs : Tendsto (fun n => (A n).sal) atTop (𝓝 B.sal)) : M.IsIR B := by
  have hc (i : W) : Tendsto (fun n => (A n).sal i) atTop (𝓝 (B.sal i)) :=
    (continuous_apply i).tendsto _ |>.comp hs
  constructor
  · intro i
    apply ge_of_tendsto' (hc i)
    intro n
    simpa [ha n] using (hA n).1 i
  · intro j
    have ht : Tendsto (fun n => profit (M.y j) (B.hired j) (A n).sal) atTop
        (𝓝 (profit (M.y j) (B.hired j) B.sal)) :=
      tendsto_const_nhds.sub (tendsto_finsetSum _ fun i _ => hc i)
    apply ge_of_tendsto' ht
    intro n
    have he : (A n).hired j = B.hired j := by simp [Allocation.hired, ha n]
    simpa [he] using (hA n).2 j

omit [DecidableEq W] in
theorem extract_ir_limit (M : Market W F) (A : ℕ → Allocation W F)
    (hA : ∀ n, M.IsIR (A n)) (L U : W → ℝ)
    (hb : ∀ n i, L i ≤ (A n).sal i ∧ (A n).sal i ≤ U i) :
    ∃ (B : Allocation W F) (ν : ℕ → ℕ), Tendsto ν atTop atTop ∧
      (∀ n, (A (ν n)).assign = B.assign) ∧
      Tendsto (fun n => (A (ν n)).sal) atTop (𝓝 B.sal) ∧ M.IsIR B := by
  classical
  have hf : ∃ᶠ n in atTop, ∃ a : W → F, (A n).assign = a :=
    Frequently.of_forall fun n => ⟨(A n).assign, rfl⟩
  obtain ⟨a, ha⟩ := frequently_exists.mp hf
  obtain ⟨μ, hμ, haμ⟩ := subseq_forall_of_frequently (p := fun n => (A n).assign = a) tendsto_id ha
  have hi (n : ℕ) : (A (μ n)).sal ∈ Set.Icc L U := by
    exact ⟨fun i => (hb _ i).1, fun i => (hb _ i).2⟩
  obtain ⟨s, _, ν, hν, hs⟩ := isCompact_Icc.tendsto_subseq hi
  let B : Allocation W F := ⟨a, s⟩
  have hass (n : ℕ) : (A (μ (ν n))).assign = B.assign := haμ (ν n)
  have hsal : Tendsto (fun n => (A (μ (ν n))).sal) atTop (𝓝 B.sal) := hs
  refine ⟨B, μ ∘ ν, hμ.comp hν.tendsto_atTop, hass, hsal, ?_⟩
  exact ir_of_limit M (fun n => A (μ (ν n))) B (fun n => hA _) hass hsal

noncomputable def gridRound (M : Market W F) (δ : ℝ) (j : F) (r : W → ℝ) : W → ℝ :=
  fun i => M.σ i j + (⌈(r i - M.σ i j) / δ⌉₊ : ℝ) * δ

omit [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] in
theorem gridRound_mem (M : Market W F) (δ : ℝ) (j : F) (r : W → ℝ) (i : W) :
    gridRound M δ j r i ∈ M.grid δ i j := by
  exact ⟨_, rfl⟩

omit [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] in
theorem gridRound_bounds (M : Market W F) (δ : ℝ) (hd : 0 < δ)
    (j : F) (r : W → ℝ) (i : W) (hr : M.σ i j ≤ r i) :
    r i ≤ gridRound M δ j r i ∧ gridRound M δ j r i < r i + δ := by
  have hq : 0 ≤ (r i - M.σ i j) / δ := div_nonneg (sub_nonneg.mpr hr) hd.le
  have h1 := Nat.le_ceil ((r i - M.σ i j) / δ)
  have h2 := Nat.ceil_lt_add_one hq
  have h3 := (div_le_iff₀ hd).mp h1
  have h4 := mul_lt_mul_of_pos_right h2 hd
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hd), one_mul] at h4
  unfold gridRound
  constructor <;> linarith

omit [Fintype F] in
theorem rounded_block_eventually (M : Market W F) (hu : M.UtilityRegular)
    (hres : M.ReservationSalaries) (B : Allocation W F) (hB : M.IsIR B)
    (A : ℕ → Allocation W F) (ha : ∀ n, (A n).assign = B.assign)
    (hs : Tendsto (fun n => (A n).sal) atTop (𝓝 B.sal))
    (δ : ℕ → ℝ) (hd : ∀ n, 0 < δ n) (ht : Tendsto δ atTop (𝓝 0))
    (hblock : M.CanStrictlyImprove anySalary B) :
    ∀ᶠ n in atTop, M.CanStrictlyImprove (M.grid (δ n)) (A n) := by
  classical
  obtain ⟨j, C, r, _, hw, hp⟩ := hblock
  have hr (i : W) (hi : i ∈ C) : M.σ i j ≤ r i := by
    have hl := (hu i (B.assign i)).1.monotone (hB.1 i)
    have he := hres i j (B.assign i)
    have hlt : M.u i j (M.σ i j) < M.u i j (r i) := by rw [he]; exact hl.trans_lt (hw i hi)
    exact ((hu i j).1.lt_iff_lt.mp hlt).le
  have hc (i : W) : Tendsto (fun n => (A n).sal i) atTop (𝓝 (B.sal i)) :=
    (continuous_apply i).tendsto _ |>.comp hs
  have hround (i : W) (hi : i ∈ C) :
      Tendsto (fun n => gridRound M (δ n) j r i) atTop (𝓝 (r i)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => r i + δ n) atTop (𝓝 (r i)) by simpa using (tendsto_const_nhds (x := r i)).add ht)
    · intro n
      exact (gridRound_bounds M _ (hd n) j r i (hr i hi)).1
    · intro n
      exact (gridRound_bounds M _ (hd n) j r i (hr i hi)).2.le
  have hpold : Tendsto (fun n => profit (M.y j) (B.hired j) (A n).sal) atTop
      (𝓝 (profit (M.y j) (B.hired j) B.sal)) :=
    tendsto_const_nhds.sub (tendsto_finsetSum _ fun i _ => hc i)
  have hpnew : Tendsto (fun n => profit (M.y j) C (gridRound M (δ n) j r)) atTop
      (𝓝 (profit (M.y j) C r)) :=
    tendsto_const_nhds.sub (tendsto_finsetSum _ fun i hi => hround i hi)
  have hwold : ∀ᶠ n in atTop, ∀ i ∈ C,
      M.u i (B.assign i) ((A n).sal i) < M.u i j (r i) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ C
    · exact ((hu i (B.assign i)).2.continuousAt.tendsto.comp (hc i)).eventually_lt
        tendsto_const_nhds (hw i hi) |>.mono (fun n hn _ => hn)
    · exact Eventually.of_forall (fun _ h => (hi h).elim)
  filter_upwards [hpold.eventually_lt hpnew hp, hwold] with n hpn hwn
  refine ⟨j, C, gridRound M (δ n) j r, (fun i _ => gridRound_mem M _ j r i), ?_, ?_⟩
  · intro i hi
    rw [ha n]
    exact (hwn i hi).trans_le ((hu i j).1.monotone (gridRound_bounds M _ (hd n) j r i (hr i hi)).1)
  · simpa [Allocation.hired, ha n] using hpn

theorem continuous_core_from_discrete [Nonempty F] (M : Market W F)
    (hu : M.UtilityRegular) (hres : M.ReservationSalaries)
    (hbox : ∃ L U : W → ℝ, ∀ A, M.IsIR A → ∀ i, L i ≤ A.sal i ∧ A.sal i ≤ U i)
    (hdiscrete : ∀ δ : ℝ, 0 < δ → ∃ A, M.IsCore (M.grid δ) A) :
    ∃ A, M.IsStrictCore anySalary A := by
  classical
  choose A hA using fun n => hdiscrete (step n) (step_pos n)
  obtain ⟨L, U, hb⟩ := hbox
  obtain ⟨B, ν, hν, ha, hs, hB⟩ := extract_ir_limit M A (fun n => (hA n).1) L U
    (fun n => hb (A n) (hA n).1)
  refine ⟨B, hB, (fun _ => Set.mem_univ _), ?_⟩
  intro hblock
  have he := rounded_block_eventually M hu hres B hB (fun n => A (ν n)) ha hs
    (fun n => step (ν n)) (fun n => step_pos _) (step_tendsto.comp hν)
    (strict_block_of_block M hu B hblock)
  obtain ⟨n, hn⟩ := he.exists
  exact (hA (ν n)).2.2 hn
end KCProof
-- END GridCompactness

-- BEGIN NativeRoot
namespace KelsoCrawford.ContinuousCore

theorem continuous_market_has_strict_core {W F : Type}
    [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hres : M.ReservationSalaries)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) Set.univ) :
    ∃ A : Allocation W F, M.IsStrictCore anySalary A := by
  exact KCProof.continuous_core_from_discrete M hu hres (KCProof.exists_ir_box M)
    (fun δ hδ => KCProof.discrete_core_exists M hu hMP hNFL hGS δ hδ)

end KelsoCrawford.ContinuousCore

theorem solution {W F : Type}
    [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : KelsoCrawford.ContinuousCore.Market W F) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hres : M.ReservationSalaries)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) Set.univ) :
    ∃ A : KelsoCrawford.ContinuousCore.Allocation W F, M.IsStrictCore KelsoCrawford.ContinuousCore.anySalary A := by
  exact KelsoCrawford.ContinuousCore.continuous_market_has_strict_core M hu hMP hNFL hres hGS
-- END NativeRoot

