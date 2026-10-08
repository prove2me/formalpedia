-- Prove2me | solution 1 for IgnallSchrage.Invariance.threeMachine_shift
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:55:33.776567+00:00
-- url     : https://prove2.me/submissions/e958e20d-d88b-48ac-b35b-b3d9e811bd50

import Mathlib
import Definitions.Def_IgnallSchrage_Invariance_ThreeMachine
open IgnallSchrage.Invariance
open IgnallSchrage.Makespan
set_option autoImplicit false

private lemma append_shift {n : ℕ} (a b c : Fin n → ℝ) (G l : ℝ)
    (t : ℝ × ℝ × ℝ) (i : Fin n) :
    appendJob3 (fun i => a i+G) (fun i => b i+G) (fun i => c i+G)
      (t.1+G*l,t.2.1+G*(l+1),t.2.2+G*(l+2)) i =
    ((appendJob3 a b c t i).1+G*(l+1),
      (appendJob3 a b c t i).2.1+G*(l+2),
      (appendJob3 a b c t i).2.2+G*(l+3)) := by
  have hA : t.1+G*l+(a i+G) = (t.1+a i)+G*(l+1) := by ring
  have hB : max (t.2.1+G*(l+1)) (t.1+G*l+(a i+G))+(b i+G) =
      (max t.2.1 (t.1+a i)+b i)+G*(l+2) := by
    rw [hA, max_add_add_right]; ring
  simp only [appendJob3]
  rw [hB, hA, max_add_add_right]
  congr 2 <;> ring

private lemma times_shift {n : ℕ} (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (J : List (Fin n)) (hJ : J ≠ []) :
    times3 (fun i => a i+G) (fun i => b i+G) (fun i => c i+G) J =
      ((times3 a b c J).1+G*J.length,
       (times3 a b c J).2.1+G*(J.length+1),
       (times3 a b c J).2.2+G*(J.length+2)) := by
  induction J using List.reverseRecOn with
  | nil => contradiction
  | append_singleton J i ih =>
    by_cases he : J = []
    · subst J
      simp [times3, appendJob3, max_eq_right (ha i),
        max_eq_right (by linarith [ha i] : 0 ≤ a i+G),
        max_eq_right (by linarith [ha i,hb i] : 0 ≤ a i+b i),
        max_eq_right (by linarith [ha i,hb i] : 0 ≤ a i+G+(b i+G))]
      <;> constructor <;> ring
    · simp only [times3, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
      rw [ih he]
      rw [append_shift]
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      congr 2 <;> simp only [appendJob3] <;> ring

private lemma done_shift {n : ℕ} (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    JohnsonFlowShop.ThreeStage.asapDone (fun i => a i+G) (fun i => b i+G)
      (fun i => c i+G) σ r =
    ((JohnsonFlowShop.ThreeStage.asapDone a b c σ r).1+G*r,
     (JohnsonFlowShop.ThreeStage.asapDone a b c σ r).2.1+G*(r+1),
     (JohnsonFlowShop.ThreeStage.asapDone a b c σ r).2.2+G*(r+2)) := by
  induction r with
  | zero => omega
  | succ r ih =>
    have hrn' : r < n := by omega
    rw [JohnsonFlowShop.ThreeStage.asapDone, JohnsonFlowShop.ThreeStage.asapDone,
      dif_pos hrn', dif_pos hrn']
    change appendJob3 (fun i => a i+G) (fun i => b i+G) (fun i => c i+G)
      (JohnsonFlowShop.ThreeStage.asapDone (fun i => a i+G) (fun i => b i+G)
        (fun i => c i+G) σ r) (σ ⟨r,hrn'⟩) = _
    by_cases he : r = 0
    · subst r
      simp [JohnsonFlowShop.ThreeStage.asapDone, appendJob3,
        max_eq_right (ha (σ ⟨0,hrn'⟩)),
        max_eq_right (by linarith [ha (σ ⟨0,hrn'⟩)] : 0 ≤ a (σ ⟨0,hrn'⟩)+G),
        max_eq_right (by linarith [ha (σ ⟨0,hrn'⟩),hb (σ ⟨0,hrn'⟩)] :
          0 ≤ a (σ ⟨0,hrn'⟩)+b (σ ⟨0,hrn'⟩)),
        max_eq_right (by linarith [ha (σ ⟨0,hrn'⟩),hb (σ ⟨0,hrn'⟩)] :
          0 ≤ a (σ ⟨0,hrn'⟩)+G+(b (σ ⟨0,hrn'⟩)+G))]
      <;> constructor <;> ring
    · rw [ih (by omega) (by omega), append_shift]
      push_cast
      congr 2 <;> simp only [appendJob3] <;> ring

private lemma min_shift {n : ℕ} (U : Finset (Fin n)) (hU : U.Nonempty)
    (f : Fin n → ℝ) (d : ℝ) :
    minOver U (fun i => f i+d) = minOver U f+d := by
  simp only [minOver, dif_pos hU]
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hU f
  apply le_antisymm
  · rw [he]; exact Finset.inf'_le _ hi
  · apply Finset.le_inf'
    intro j hj
    linarith [Finset.inf'_le f hj]

theorem solution {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (G : ℝ) (hG : 0 < G) :
    (∀ σ : Equiv.Perm (Fin n),
      IgnallSchrage.Makespan.makespan (fun i => a i + G) (fun i => b i + G) (fun i => c i + G) σ =
        IgnallSchrage.Makespan.makespan a b c σ + G * (n + 2)) ∧
    (∀ J : List (Fin n), J.Nodup → 1 ≤ J.length → J.length + 1 ≤ n →
      lowerBound3 (fun i => a i + G) (fun i => b i + G) (fun i => c i + G) J =
        lowerBound3 a b c J + G * (n + 2))  := by
  classical
  constructor
  · intro σ
    exact congrArg Prod.snd (congrArg Prod.snd (done_shift a b c ha hb G hG σ n hn le_rfl))
  · intro J hnd hlo hhi
    have hcard : (unscheduled J).card + J.length = n := by
      have hp : J.toFinset.card = J.length := List.toFinset_card_of_nodup hnd
      have he : unscheduled J = Finset.univ \ J.toFinset := by ext; simp [unscheduled]
      rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hp]
      have : J.length ≤ n := by simpa [hp] using (J.toFinset.card_le_univ)
      omega
    have hU : (unscheduled J).Nonempty := Finset.card_pos.mp (by omega)
    have ht := times_shift a b c ha hb G hG J (by intro he; simp [he] at hlo)
    simp only [lowerBound3, ht, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [show (fun i => b i+G+(c i+G)) = (fun i => (b i+c i)+2*G) by funext; ring,
      min_shift _ hU, min_shift _ hU]
    have he : (J.length : ℝ)+(unscheduled J).card = n := by exact_mod_cast (by omega : J.length+(unscheduled J).card=n)
    have h1 : (times3 a b c J).1+G*J.length+(∑ i ∈ unscheduled J, a i+(0:ℝ)) +
        (unscheduled J).card*G+(minOver (unscheduled J) (fun i => b i+c i)+2*G) =
      (times3 a b c J).1+(∑ i ∈ unscheduled J, a i)+minOver (unscheduled J) (fun i => b i+c i)+G*(n+2) := by
      simp only [add_zero]; nlinarith [congrArg (fun x : ℝ => G*x) he]
    have h2 : (times3 a b c J).2.1+G*(J.length+1)+(∑ i ∈ unscheduled J, b i)+
        (unscheduled J).card*G+(minOver (unscheduled J) c+G) =
      (times3 a b c J).2.1+(∑ i ∈ unscheduled J, b i)+minOver (unscheduled J) c+G*(n+2) := by
      nlinarith [congrArg (fun x : ℝ => G*x) he]
    have h3 : (times3 a b c J).2.2+G*(J.length+2)+((∑ i ∈ unscheduled J, c i)+(unscheduled J).card*G) =
      (times3 a b c J).2.2+(∑ i ∈ unscheduled J, c i)+G*(n+2) := by
      nlinarith [congrArg (fun x : ℝ => G*x) he]
    rw [show (times3 a b c J).1+G*J.length+((∑ i ∈ unscheduled J,a i)+(unscheduled J).card*G)+
       (minOver (unscheduled J) (fun i => b i+c i)+2*G) =
       (times3 a b c J).1+(∑ i ∈ unscheduled J,a i)+minOver (unscheduled J) (fun i => b i+c i)+G*(n+2) by
       simp only [add_zero] at h1; linarith [h1],
      show (times3 a b c J).2.1+G*(J.length+1)+((∑ i ∈ unscheduled J,b i)+(unscheduled J).card*G)+
       (minOver (unscheduled J) c+G) =
       (times3 a b c J).2.1+(∑ i ∈ unscheduled J,b i)+minOver (unscheduled J) c+G*(n+2) by linarith [h2],
      h3, max_add_add_right, max_add_add_right]
#print axioms solution
