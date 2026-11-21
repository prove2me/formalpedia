-- Prove2me | solution 1 for InputSparsity.Embed.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:43:36.871094+00:00
-- url     : https://prove2.me/submissions/98689f20-ee8c-42f2-917b-291a0374de04

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

open Matrix

namespace Aux_InputSparsity_Embed_lemma_5

open InputSparsity.Embed

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem collide_card {n t : ℕ} (i i' : Fin n) (hii : i ≠ i') :
    (Finset.univ.filter (fun h : Fin n → Fin t => h i = h i')).card * t ≤ t ^ n := by
  let Ψ : {h : Fin n → Fin t // h i = h i'} × Fin t → (Fin n → Fin t) :=
    fun p => Function.update p.1.1 i' p.2
  have hinj : Function.Injective Ψ := by
    rintro ⟨⟨h1, hh1⟩, c1⟩ ⟨⟨h2, hh2⟩, c2⟩ heq
    have hc : c1 = c2 := by
      have := congrFun heq i'
      simpa [Ψ] using this
    have hh : h1 = h2 := by
      funext m
      by_cases hm : m = i'
      · rw [hm, ← hh1, ← hh2]
        have := congrFun heq i
        simpa [Ψ, Function.update_of_ne hii] using this
      · have := congrFun heq m
        simpa [Ψ, Function.update_of_ne hm] using this
    subst hc
    subst hh
    rfl
  have := Fintype.card_le_of_injective Ψ hinj
  rw [Fintype.card_prod, Fintype.card_subtype, Fintype.card_fun] at this
  simpa only [Fintype.card_fin] using this

theorem sketch_entry {n t : ℕ} (h : Fin n → Fin t) (σ : Fin n → Bool) (a : Fin t) (i : Fin n) :
    sketch h σ a i = if h i = a then sgn (σ i) else 0 := by
  unfold sketch Dmat
  rw [Matrix.mul_diagonal]
  simp only [Phi]
  split_ifs <;> simp

theorem sketch_coord {n t : ℕ} (h : Fin n → Fin t) (σ : Fin n → Bool) (x : Fin n → ℝ)
    (a : Fin t) :
    (sketch h σ *ᵥ x) a = ∑ i, (if h i = a then sgn (σ i) * x i else 0) := by
  simp only [Matrix.mulVec, dotProduct, sketch_entry]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

end Aux_InputSparsity_Embed_lemma_5

open InputSparsity.Embed Aux_InputSparsity_Embed_lemma_5 in
theorem solution {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (T : ℝ) (ht : 0 < t) :
    1 - unifProb (Fin n → Fin t) {h | PerfectOnHeavy U T h} ≤
        (((Finset.univ.filter (fun i : Fin n => T < lev U i)).card + 1 : ℕ) : ℝ) ^ 2 / t ∧
      ∀ (h : Fin n → Fin t), PerfectOnHeavy U T h →
        ∀ (σ : Fin n → Bool) (y : Fin n → ℝ),
          sqNorm (heavy U T y) = sqNorm (sketch h σ *ᵥ heavy U T y) := by
  classical
  refine ⟨?_, ?_⟩
  · have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    have htn : (0 : ℝ) < (t : ℝ) ^ n := by positivity
    obtain ⟨H, hH⟩ : ∃ H : Finset (Fin n), H = Finset.univ.filter (fun i : Fin n => T < lev U i) :=
      ⟨_, rfl⟩
    rw [← hH]
    obtain ⟨P, hP⟩ : ∃ P : Finset (Fin n × Fin n), P = (H ×ˢ H).filter (fun p => p.1 ≠ p.2) :=
      ⟨_, rfl⟩
    have hsub : Finset.univ.filter (fun h : Fin n → Fin t => ¬ PerfectOnHeavy U T h) ⊆
        P.biUnion (fun p => Finset.univ.filter (fun h : Fin n → Fin t => h p.1 = h p.2)) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      have hh2 := hh.2
      unfold PerfectOnHeavy at hh2
      push_neg at hh2
      obtain ⟨i, i', hi, hi', hne, heq⟩ := hh2
      rw [Finset.mem_biUnion]
      refine ⟨(i, i'), ?_, ?_⟩
      · rw [hP, Finset.mem_filter, Finset.mem_product, hH]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hi, hi'⟩, hne⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
    have h1 := le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le (s := P)
      (t := fun p => Finset.univ.filter (fun h : Fin n → Fin t => h p.1 = h p.2)))
    have h2 : (∑ p ∈ P, (Finset.univ.filter (fun h : Fin n → Fin t => h p.1 = h p.2)).card) * t
        ≤ P.card * t ^ n := by
      rw [Finset.sum_mul]
      calc ∑ p ∈ P, (Finset.univ.filter (fun h : Fin n → Fin t => h p.1 = h p.2)).card * t
          ≤ ∑ _p ∈ P, t ^ n := by
            apply Finset.sum_le_sum
            intro p hp
            rw [hP, Finset.mem_filter] at hp
            exact collide_card p.1 p.2 hp.2
        _ = P.card * t ^ n := by rw [Finset.sum_const, smul_eq_mul]
    have h3 : P.card ≤ H.card * H.card := by
      rw [hP, ← Finset.card_product]
      exact Finset.card_filter_le _ _
    have hbadN : (Finset.univ.filter (fun h : Fin n → Fin t => ¬ PerfectOnHeavy U T h)).card * t
        ≤ H.card * H.card * t ^ n := by
      calc (Finset.univ.filter (fun h : Fin n → Fin t => ¬ PerfectOnHeavy U T h)).card * t
          ≤ (∑ p ∈ P, (Finset.univ.filter (fun h : Fin n → Fin t => h p.1 = h p.2)).card) * t :=
            Nat.mul_le_mul_right _ h1
        _ ≤ P.card * t ^ n := h2
        _ ≤ H.card * H.card * t ^ n := Nat.mul_le_mul_right _ h3
    have hbad : ((Finset.univ.filter (fun h : Fin n → Fin t => ¬ PerfectOnHeavy U T h)).card : ℝ)
        * t ≤ (H.card : ℝ) * H.card * (t : ℝ) ^ n := by
      exact_mod_cast hbadN
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n → Fin t))) (fun h => PerfectOnHeavy U T h)
    have hcardU : (Finset.univ : Finset (Fin n → Fin t)).card = t ^ n := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [hcardU] at hsplit
    have hs : ((Finset.univ.filter (fun h : Fin n → Fin t => PerfectOnHeavy U T h)).card : ℝ) +
        ((Finset.univ.filter (fun h : Fin n → Fin t => ¬ PerfectOnHeavy U T h)).card : ℝ)
        = (t : ℝ) ^ n := by
      rw [← Nat.cast_add, hsplit, Nat.cast_pow]
    unfold unifProb
    rw [Nat.card_eq_card_toFinset, Set.toFinset_setOf, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
    push_cast
    obtain ⟨g, hg⟩ : ∃ g : ℝ, g = ((Finset.univ.filter
        (fun h : Fin n → Fin t => PerfectOnHeavy U T h)).card : ℝ) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ((Finset.univ.filter
        (fun h : Fin n → Fin t => ¬ PerfectOnHeavy U T h)).card : ℝ) := ⟨_, rfl⟩
    rw [← hg]
    rw [← hg, ← hb] at hs
    rw [← hb] at hbad
    have hk : (H.card : ℝ) * H.card ≤ ((H.card : ℝ) + 1) ^ 2 := by nlinarith
    have e1 : 1 - g / (t : ℝ) ^ n = b / (t : ℝ) ^ n := by
      have hg' : g = (t : ℝ) ^ n - b := by linarith
      rw [hg', sub_div, div_self htn.ne']
      ring
    rw [e1, div_le_div_iff₀ htn htpos]
    have hb0 : 0 ≤ b := by rw [hb]; positivity
    have htn0 : (0 : ℝ) ≤ (t : ℝ) ^ n := htn.le
    nlinarith
  · intro h hperf σ y
    have hcoord : ∀ a : Fin t, ((sketch h σ *ᵥ heavy U T y) a) ^ 2 =
        ∑ i, (if h i = a then (heavy U T y i) ^ 2 else 0) := by
      intro a
      rw [sketch_coord]
      obtain ⟨A, hA⟩ : ∃ A : Finset (Fin n),
          A = Finset.univ.filter (fun i => h i = a ∧ T < lev U i) := ⟨_, rfl⟩
      have e1 : ∑ i, (if h i = a then sgn (σ i) * heavy U T y i else 0)
          = ∑ i ∈ A, sgn (σ i) * y i := by
        rw [hA, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h1 : h i = a <;> by_cases h2 : T < lev U i <;> simp [heavy, h1, h2]
      have e2 : ∑ i, (if h i = a then (heavy U T y i) ^ 2 else 0) = ∑ i ∈ A, y i ^ 2 := by
        rw [hA, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h1 : h i = a <;> by_cases h2 : T < lev U i <;> simp [heavy, h1, h2]
      rw [e1, e2]
      have hcard : A.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro i hi i' hi'
        rw [hA, Finset.mem_filter] at hi hi'
        by_contra hne
        exact hperf i i' hi.2.2 hi'.2.2 hne (by rw [hi.2.1, hi'.2.1])
      rcases Finset.eq_empty_or_nonempty A with hAe | ⟨i0, hi0⟩
      · rw [hAe]
        simp
      · have hA1 : A = {i0} :=
          Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hi0, fun i hi => Finset.card_le_one.mp hcard i hi i0 hi0⟩
        rw [hA1, Finset.sum_singleton, Finset.sum_singleton, mul_pow, sgn_sq, one_mul]
    unfold sqNorm
    rw [Finset.sum_congr rfl (fun a _ => hcoord a), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq]
    simp
