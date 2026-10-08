-- Prove2me | solution 1 for KellyReversibility.MarkovFields.markov_field_iff_simplex_product
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:10:34.586405+00:00
-- url     : https://prove2.me/submissions/12067fad-d539-42c7-900b-a3bd29baf283

import Mathlib
import Definitions.Def_KellyReversibility_MarkovFields_RandomField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HC44d9

open Finset KellyReversibility.MarkovFields

section
variable {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*} [∀ j, Fintype (N j)]

/-- take `n` on `B` and the reference state `n0` off `B` -/
def rst (n0 n : (k : V) → N k) (B : Finset V) : (k : V) → N k :=
  fun k => if k ∈ B then n k else n0 k

/-- extend a configuration on `C` by `n0` -/
def ext (n0 : (k : V) → N k) (C : Finset V) (y : (k : C) → N k) : (k : V) → N k :=
  fun k => if h : k ∈ C then y ⟨k, h⟩ else n0 k

lemma rst_univ (n0 n : (k : V) → N k) : rst n0 n univ = n := by
  funext k; simp [rst]

lemma rst_empty (n0 n : (k : V) → N k) : rst n0 n ∅ = n0 := by
  funext k; simp [rst]

lemma rst_insert (n0 n : (k : V) → N k) (i : V) (B : Finset V) :
    rst n0 n (insert i B) = Function.update (rst n0 n B) i (n i) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [rst]
  · simp [rst, Function.update_of_ne hk, hk]

lemma rst_notin (n0 n : (k : V) → N k) {i : V} {B : Finset V} (hi : i ∉ B) :
    rst n0 n B = Function.update (rst n0 n B) i (n0 i) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [rst, hi]
  · simp [rst, Function.update_of_ne hk]

lemma rst_ext (n0 n : (k : V) → N k) {B C : Finset V} (hBC : B ⊆ C) :
    rst n0 (ext n0 C (fun k : C => n k)) B = rst n0 n B := by
  funext k
  by_cases hk : k ∈ B
  · simp [rst, ext, hk, hBC hk]
  · simp [rst, hk]

end

section
variable {V : Type*} [DecidableEq V]

/-- Moebius transform on subsets -/
def Vf (f : Finset V → ℝ) (A : Finset V) : ℝ :=
  ∑ B ∈ A.powerset, (-1 : ℝ) ^ (A.card + B.card) * f B

lemma Vf_insert (f : Finset V → ℝ) {a : V} {A : Finset V} (ha : a ∉ A) :
    Vf f (insert a A) = Vf (fun B => f (insert a B)) A - Vf f A := by
  unfold Vf
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha, sub_eq_neg_add,
    ← Finset.sum_neg_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro B _; ring
  · apply Finset.sum_congr rfl; intro B hB
    have : a ∉ B := fun h => ha (Finset.mem_powerset.1 hB h)
    rw [Finset.card_insert_of_notMem this]; ring

lemma sum_Vf (S : Finset V) : ∀ f : Finset V → ℝ, ∑ A ∈ S.powerset, Vf f A = f S := by
  induction S using Finset.induction_on with
  | empty => intro f; simp [Vf]
  | @insert a S ha ih =>
    intro f
    rw [Finset.sum_powerset_insert ha]
    have : ∑ A ∈ S.powerset, Vf f (insert a A)
        = ∑ A ∈ S.powerset, (Vf (fun B => f (insert a B)) A - Vf f A) := by
      apply Finset.sum_congr rfl; intro A hA
      exact Vf_insert f (fun h => ha (Finset.mem_powerset.1 hA h))
    rw [this, Finset.sum_sub_distrib, ih, ih]; ring

lemma Vf_eq_zero_of_square (f : Finset V → ℝ) {i j : V} {A : Finset V} (hij : i ≠ j)
    (hi : i ∈ A) (hj : j ∈ A)
    (h : ∀ B ⊆ (A.erase i).erase j,
      f (insert i (insert j B)) - f (insert j B) - f (insert i B) + f B = 0) :
    Vf f A = 0 := by
  have hjA' : j ∉ (A.erase i).erase j := Finset.notMem_erase j _
  have hiA' : i ∉ insert j ((A.erase i).erase j) := by simp [hij]
  have hA : A = insert i (insert j ((A.erase i).erase j)) := by
    rw [Finset.insert_erase (Finset.mem_erase.2 ⟨hij.symm, hj⟩), Finset.insert_erase hi]
  have e1 : Vf f (insert i (insert j ((A.erase i).erase j)))
      = Vf (fun B => f (insert i B)) (insert j ((A.erase i).erase j))
        - Vf f (insert j ((A.erase i).erase j)) := Vf_insert f hiA'
  have e2 : Vf (fun B => f (insert i B)) (insert j ((A.erase i).erase j))
      = Vf (fun B => f (insert i (insert j B))) ((A.erase i).erase j)
        - Vf (fun B => f (insert i B)) ((A.erase i).erase j) := Vf_insert _ hjA'
  have e3 : Vf f (insert j ((A.erase i).erase j))
      = Vf (fun B => f (insert j B)) ((A.erase i).erase j) - Vf f ((A.erase i).erase j) :=
    Vf_insert f hjA'
  have key : Vf (fun B => f (insert i (insert j B))) ((A.erase i).erase j)
      - Vf (fun B => f (insert i B)) ((A.erase i).erase j)
      - (Vf (fun B => f (insert j B)) ((A.erase i).erase j) - Vf f ((A.erase i).erase j)) = 0 := by
    unfold Vf
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro B hB
    have := h B (Finset.mem_powerset.1 hB)
    linear_combination (-1 : ℝ) ^ (((A.erase i).erase j).card + B.card) * this
  rw [hA]; linarith

end

section
variable {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*} [∀ j, Fintype (N j)]

open Classical in
lemma markov_local {G : SimpleGraph V} {π : ((k : V) → N k) → ℝ} (hM : IsMarkovField G π)
    (j : V) (n n' : (k : V) → N k) (hj : n j = n' j) (hH : ∀ k, G.Adj j k → n k = n' k) :
    condProb π j n = condProb π j n' := by
  rw [hM j n, hM j n']
  unfold condProbGiven
  have h1 : ∀ z : (k : V) → N k, (∀ k ∈ G.neighborSet j, z k = n k) ↔
      (∀ k ∈ G.neighborSet j, z k = n' k) := by
    intro z; constructor
    · intro h k hk; rw [h k hk]; exact hH k hk
    · intro h k hk; rw [h k hk]; exact (hH k hk).symm
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hj, h1 z]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h1 z

lemma pi_eq_cp_mul {π : ((k : V) → N k) → ℝ} (hpos : ∀ n, 0 < π n) (i : V)
    (z : (k : V) → N k) (a : N i) :
    π (Function.update z i a)
      = condProb π i (Function.update z i a) * ∑ m, π (Function.update z i m) := by
  unfold condProb
  simp only [Function.update_idem]
  have : 0 < ∑ m, π (Function.update z i m) :=
    Finset.sum_pos (fun m _ => hpos _) ⟨a, Finset.mem_univ _⟩
  rw [div_mul_cancel₀ _ this.ne']

lemma cross_ratio {G : SimpleGraph V} {π : ((k : V) → N k) → ℝ} (hpos : ∀ n, 0 < π n)
    (hM : IsMarkovField G π) {i j : V} (hij : i ≠ j) (hadj : ¬ G.Adj i j)
    (x : (k : V) → N k) (a b : N i) (c : N j) :
    π (Function.update (Function.update x j c) i a) * π (Function.update x i b) =
      π (Function.update x i a) * π (Function.update (Function.update x j c) i b) := by
  have hloc : ∀ v : N i, condProb π i (Function.update (Function.update x j c) i v)
      = condProb π i (Function.update x i v) := by
    intro v
    apply markov_local hM
    · simp
    · intro k hk
      have hki : k ≠ i := fun h => by subst h; exact G.irrefl hk
      have hkj : k ≠ j := fun h => by subst h; exact hadj hk
      simp [Function.update_of_ne hki, Function.update_of_ne hkj]
  rw [pi_eq_cp_mul hpos i _ a, pi_eq_cp_mul hpos i x b, pi_eq_cp_mul hpos i x a,
    pi_eq_cp_mul hpos i _ b, hloc a, hloc b]
  ring

lemma square_log {G : SimpleGraph V} {π : ((k : V) → N k) → ℝ} (hpos : ∀ n, 0 < π n)
    (hM : IsMarkovField G π) (n0 n : (k : V) → N k) {i j : V} (hij : i ≠ j)
    (hadj : ¬ G.Adj i j) {B : Finset V} (hiB : i ∉ B) :
    Real.log (π (rst n0 n (insert i (insert j B)))) - Real.log (π (rst n0 n (insert j B)))
      - Real.log (π (rst n0 n (insert i B))) + Real.log (π (rst n0 n B)) = 0 := by
  have key := cross_ratio hpos hM hij hadj (rst n0 n B) (n i) (n0 i) (n j)
  have e1 : Function.update (Function.update (rst n0 n B) j (n j)) i (n i)
      = rst n0 n (insert i (insert j B)) := by rw [rst_insert, rst_insert]
  have e2 : Function.update (rst n0 n B) i (n0 i) = rst n0 n B := (rst_notin n0 n hiB).symm
  have e3 : Function.update (rst n0 n B) i (n i) = rst n0 n (insert i B) :=
    (rst_insert n0 n i B).symm
  have hiJB : i ∉ insert j B := by simp [hij, hiB]
  have e4 : Function.update (Function.update (rst n0 n B) j (n j)) i (n0 i)
      = rst n0 n (insert j B) := by
    rw [← rst_insert]; exact (rst_notin n0 n hiJB).symm
  rw [e1, e2, e3, e4] at key
  have := congrArg Real.log key
  rw [Real.log_mul (hpos _).ne' (hpos _).ne', Real.log_mul (hpos _).ne' (hpos _).ne'] at this
  linarith

open Classical in
lemma forward {G : SimpleGraph V} {π : ((k : V) → N k) → ℝ} (hπ : IsRandomField π)
    (hM : IsMarkovField G π) : HasSimplexProductForm G π := by
  obtain ⟨n0, -, -⟩ : ∃ n0 ∈ (univ : Finset ((k : V) → N k)), π n0 ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hπ.2]; norm_num)
  refine ⟨π n0, fun C y => Real.exp (Vf (fun A => Real.log (π (rst n0 (ext n0 C y) A))) C),
    fun n => ?_⟩
  have h1 := sum_Vf (univ : Finset V) (fun A => Real.log (π (rst n0 n A)))
  simp only [Finset.powerset_univ, rst_univ] at h1
  have h2 : ∑ A ∈ (univ : Finset (Finset V)), Vf (fun A => Real.log (π (rst n0 n A))) A
      = ∑ A ∈ insert ∅ (simplices G), Vf (fun A => Real.log (π (rst n0 n A))) A := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro A _ hA
    have hA' : A ≠ ∅ ∧ ¬ (A.Nonempty ∧ G.IsClique (A : Set V)) := by
      rw [Finset.mem_insert, not_or] at hA
      refine ⟨hA.1, fun h => hA.2 ?_⟩
      simp only [simplices, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
    have hnc : ¬ G.IsClique (A : Set V) :=
      fun h => hA'.2 ⟨Finset.nonempty_iff_ne_empty.2 hA'.1, h⟩
    rw [SimpleGraph.isClique_iff, Set.Pairwise] at hnc
    push_neg at hnc
    obtain ⟨i, hi, j, hj, hij, hadj⟩ := hnc
    apply Vf_eq_zero_of_square _ hij (Finset.mem_coe.1 hi) (Finset.mem_coe.1 hj)
    intro B hB
    have hiB : i ∉ B := fun h => by have := hB h; simp at this
    exact square_log hπ.1 hM n0 n hij hadj hiB
  have h3 : ∑ A ∈ insert ∅ (simplices G), Vf (fun A => Real.log (π (rst n0 n A))) A
      = Real.log (π n0) + ∑ C ∈ simplices G,
          Vf (fun A => Real.log (π (rst n0 (ext n0 C (fun k : C => n k)) A))) C := by
    rw [Finset.sum_insert (by simp [simplices])]
    congr 1
    · simp [Vf, rst_empty]
    · apply Finset.sum_congr rfl; intro C _
      unfold Vf; apply Finset.sum_congr rfl; intro B hB
      dsimp only
      rw [rst_ext n0 n (Finset.mem_powerset.1 hB)]
  calc π n = Real.exp (Real.log (π n)) := (Real.exp_log (hπ.1 n)).symm
    _ = Real.exp (Real.log (π n0) + ∑ C ∈ simplices G,
          Vf (fun A => Real.log (π (rst n0 (ext n0 C (fun k : C => n k)) A))) C) := by
        rw [← h1, h2, h3]
    _ = _ := by rw [Real.exp_add, Real.exp_log (hπ.1 n0), Real.exp_sum]

/-- product over simplices containing `j` -/
noncomputable def Pj (G : SimpleGraph V) (φ : (C : Finset V) → ((k : C) → N k) → ℝ) (j : V)
    (z : (k : V) → N k) : ℝ :=
  ∏ C ∈ (simplices G).filter (fun C => j ∈ C), φ C (fun k => z k)

/-- product over simplices not containing `j` -/
noncomputable def Qj (G : SimpleGraph V) (φ : (C : Finset V) → ((k : C) → N k) → ℝ) (j : V)
    (z : (k : V) → N k) : ℝ :=
  ∏ C ∈ (simplices G).filter (fun C => ¬ j ∈ C), φ C (fun k => z k)

lemma prod_local {G : SimpleGraph V} {π : ((k : V) → N k) → ℝ} (hpos : ∀ n, 0 < π n)
    (h : HasSimplexProductForm G π) (j : V) :
    ∀ n n' : (k : V) → N k, n j = n' j → (∀ k, G.Adj j k → n k = n' k) →
      condProb π j n = condProb π j n' := by
  obtain ⟨B, φ, hφ⟩ := h
  have hsplit : ∀ z, π z = B * (Pj G φ j z * Qj G φ j z) := by
    intro z; rw [hφ z]; unfold Pj Qj; rw [Finset.prod_filter_mul_prod_filter_not]
  have hQ : ∀ z (m : N j), Qj G φ j (Function.update z j m) = Qj G φ j z := by
    intro z m; unfold Qj
    apply Finset.prod_congr rfl; intro C hC
    have hjC : ¬ j ∈ C := (Finset.mem_filter.1 hC).2
    congr 1; funext k
    exact Function.update_of_ne (fun (h : (k : V) = j) => hjC (by rw [← h]; exact k.2)) _ _
  have hP : ∀ z z' : (k : V) → N k, z j = z' j → (∀ k, G.Adj j k → z k = z' k) →
      Pj G φ j z = Pj G φ j z' := by
    intro z z' hzj hzk; unfold Pj
    apply Finset.prod_congr rfl; intro C hC
    have hC' := Finset.mem_filter.1 hC
    have hjC : j ∈ C := hC'.2
    have hcl : G.IsClique (C : Set V) := by
      have := hC'.1
      simp only [simplices, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.2
    congr 1; funext k
    obtain ⟨k, hk⟩ := k
    by_cases hkj : k = j
    · subst hkj; exact hzj
    · exact hzk k (hcl (Finset.mem_coe.2 hjC) (Finset.mem_coe.2 hk) (Ne.symm hkj))
  have hcp : ∀ z, condProb π j z
      = Pj G φ j z / ∑ m, Pj G φ j (Function.update z j m) := by
    intro z
    have hne : B * Qj G φ j z ≠ 0 := by
      have h0 : B * (Pj G φ j z * Qj G φ j z) ≠ 0 := by rw [← hsplit z]; exact (hpos z).ne'
      intro h; apply h0; linear_combination Pj G φ j z * h
    have hsum : ∑ m, π (Function.update z j m)
        = (B * Qj G φ j z) * ∑ m, Pj G φ j (Function.update z j m) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
      rw [hsplit, hQ]; ring
    unfold condProb
    rw [hsum, hsplit z, show B * (Pj G φ j z * Qj G φ j z) = (B * Qj G φ j z) * Pj G φ j z by ring,
      mul_div_mul_left _ _ hne]
  intro n n' hj hk
  rw [hcp n, hcp n', hP n n' hj hk]
  congr 1
  apply Finset.sum_congr rfl; intro m _
  apply hP
  · simp
  · intro k hk'
    have hkj : k ≠ j := fun h => by subst h; exact G.irrefl hk'
    simp [Function.update_of_ne hkj, hk k hk']

lemma local_markov_aux {G : SimpleGraph V} {π : ((k : V) → N k) → ℝ} (hpos : ∀ n, 0 < π n)
    (j : V)
    (hloc : ∀ n n' : (k : V) → N k, n j = n' j → (∀ k, G.Adj j k → n k = n' k) →
      condProb π j n = condProb π j n')
    (n : (k : V) → N k) (S Sj : Finset ((k : V) → N k))
    (hS : ∀ z, z ∈ S ↔ ∀ k, G.Adj j k → z k = n k)
    (hSj : ∀ z, z ∈ Sj ↔ (z j = n j ∧ ∀ k, G.Adj j k → z k = n k)) :
    condProb π j n = (∑ z ∈ Sj, π z) / ∑ z ∈ S, π z := by
  have hD : ∀ z : (k : V) → N k, 0 < ∑ m, π (Function.update z j m) :=
    fun z => Finset.sum_pos (fun m _ => hpos _) ⟨z j, Finset.mem_univ _⟩
  have hnum : ∑ z ∈ Sj, π z = condProb π j n * ∑ z ∈ Sj, ∑ m, π (Function.update z j m) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z hz
    rw [hSj] at hz
    have hcz : condProb π j z = condProb π j n := hloc z n hz.1 hz.2
    rw [← hcz]; unfold condProb; rw [div_mul_cancel₀ _ (hD z).ne']
  have hden : ∑ z ∈ S, π z = ∑ z ∈ Sj, ∑ m, π (Function.update z j m) := by
    have hp : ∑ z ∈ Sj, ∑ m, π (Function.update z j m)
        = ∑ p ∈ Sj ×ˢ (univ : Finset (N j)), π (Function.update p.1 j p.2) := by
      rw [Finset.sum_product]
    rw [hp]; symm
    apply Finset.sum_nbij' (fun p => Function.update p.1 j p.2)
      (fun z => (Function.update z j (n j), z j))
    · intro p hp
      rw [Finset.mem_product, hSj] at hp
      rw [hS]; intro k hk
      have hkj : k ≠ j := fun h => by subst h; exact G.irrefl hk
      simp [Function.update_of_ne hkj, hp.1.2 k hk]
    · intro z hz
      rw [hS] at hz
      rw [Finset.mem_product, hSj]
      refine ⟨⟨by simp, fun k hk => ?_⟩, Finset.mem_univ _⟩
      have hkj : k ≠ j := fun h => by subst h; exact G.irrefl hk
      simp [Function.update_of_ne hkj, hz k hk]
    · intro p hp
      rw [Finset.mem_product, hSj] at hp
      ext
      · simp only [Function.update_idem]
        rw [← hp.1.1, Function.update_eq_self]
      · simp
    · intro z _
      simp
    · intro p _; rfl
  have hpd : 0 < ∑ z ∈ S, π z :=
    Finset.sum_pos (fun z _ => hpos z) ⟨n, (hS n).2 (fun _ _ => rfl)⟩
  rw [hnum, ← hden, mul_div_assoc, div_self hpd.ne', mul_one]

lemma local_markov {G : SimpleGraph V} {π : ((k : V) → N k) → ℝ} (hpos : ∀ n, 0 < π n)
    (j : V)
    (hloc : ∀ n n' : (k : V) → N k, n j = n' j → (∀ k, G.Adj j k → n k = n' k) →
      condProb π j n = condProb π j n')
    (n : (k : V) → N k) : condProb π j n = condProbGiven π j (G.neighborSet j) n := by
  unfold condProbGiven
  apply local_markov_aux hpos j hloc n
  · intro z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborSet]
  · intro z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborSet]

end

end HC44d9

open KellyReversibility.MarkovFields in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {N : V → Type*} [∀ j, Fintype (N j)] (G : SimpleGraph V)
    (π : ((j : V) → N j) → ℝ) (hπ : IsRandomField π) :
    IsMarkovField G π ↔ HasSimplexProductForm G π := by
  constructor
  · exact HC44d9.forward hπ
  · intro h j n
    exact HC44d9.local_markov hπ.1 j (HC44d9.prod_local hπ.1 h j) n
