-- Prove2me | solution 1 for MPECRelax.KDBConv.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:22:35.467711+00:00
-- url     : https://prove2.me/submissions/c5dd21f9-0b0d-462b-85c2-af9ad0a31e7b

import Mathlib
import Definitions.Def_MPECRelax_KDBConv_Basic

open Filter Topology

namespace KDB35Aux

/-- Sign-preserving Carathéodory reduction. -/
theorem carath {J V : Type*} [Fintype J] [DecidableEq J] [AddCommGroup V] [Module ℝ V]
    (v : J → V) : ∀ (N : ℕ) (c : J → ℝ), (Finset.univ.filter (fun j => c j ≠ 0)).card ≤ N →
    ∃ c' : J → ℝ, ∑ j, c' j • v j = ∑ j, c j • v j ∧ (∀ j, c' j = 0 ∨ 0 < c' j * c j) ∧
      ∀ d : J → ℝ, (∀ j, c' j = 0 → d j = 0) → ∑ j, d j • v j = 0 → d = 0 := by
  intro N
  induction N with
  | zero =>
    intro c hc
    have hz : ∀ j, c j = 0 := by
      intro j; by_contra h
      have hm : j ∈ Finset.univ.filter (fun j => c j ≠ 0) := by simp [h]
      have := Finset.card_pos.2 ⟨j, hm⟩; omega
    refine ⟨c, rfl, fun j => Or.inl (hz j), ?_⟩
    intro d hd _; funext j; exact hd j (hz j)
  | succ N ih =>
    intro c hc
    by_cases hLI : ∀ d : J → ℝ, (∀ j, c j = 0 → d j = 0) → ∑ j, d j • v j = 0 → d = 0
    · refine ⟨c, rfl, fun j => ?_, hLI⟩
      by_cases h : c j = 0
      · exact Or.inl h
      · exact Or.inr (mul_self_pos.2 h)
    push Not at hLI
    obtain ⟨d0, hd0supp, hd0sum, hd0ne⟩ := hLI
    obtain ⟨j0, hj0⟩ : ∃ j, d0 j ≠ 0 := by
      by_contra h; push Not at h; exact hd0ne (funext h)
    have hcj0 : c j0 ≠ 0 := fun h => hj0 (hd0supp j0 h)
    obtain ⟨d, hdsupp, hdsum, hdpos⟩ : ∃ d : J → ℝ, (∀ j, c j = 0 → d j = 0) ∧
        ∑ j, d j • v j = 0 ∧ 0 < d j0 * c j0 := by
      rcases lt_or_gt_of_ne (mul_ne_zero hj0 hcj0) with h | h
      · refine ⟨-d0, fun j hj => by simp [hd0supp j hj], ?_, ?_⟩
        · simp [neg_smul, Finset.sum_neg_distrib, hd0sum]
        · simp; linarith
      · exact ⟨d0, hd0supp, hd0sum, h⟩
    set S := Finset.univ.filter (fun j => 0 < d j * c j) with hSdef
    have hS : S.Nonempty := ⟨j0, by simp [S, hdpos]⟩
    obtain ⟨j1, hj1S, hj1min⟩ := S.exists_min_image (fun j => c j / d j) hS
    have hj1pos : 0 < d j1 * c j1 := by simpa [S] using hj1S
    have hdj1 : d j1 ≠ 0 := by intro h; rw [h] at hj1pos; simp at hj1pos
    set τ := c j1 / d j1 with hτ
    have hτpos : 0 < τ := by
      have : τ = (d j1 * c j1) / (d j1 * d j1) := by
        rw [hτ]; field_simp
      rw [this]; exact div_pos hj1pos (mul_self_pos.2 hdj1)
    set c'' : J → ℝ := fun j => c j - τ * d j with hc''
    have hsum : ∑ j, c'' j • v j = ∑ j, c j • v j := by
      simp only [c'', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdsum,
        smul_zero, sub_zero]
    have hsign : ∀ j, c'' j = 0 ∨ 0 < c'' j * c j := by
      intro j
      by_cases hcj : c j = 0
      · left; simp [c'', hcj, hdsupp j hcj]
      have hcc : 0 < c j * c j := mul_self_pos.2 hcj
      have hge : 0 ≤ c'' j * c j := by
        by_cases hdc : 0 < d j * c j
        · have hjS : j ∈ S := by simp [S, hdc]
          have hle : τ ≤ c j / d j := hj1min j hjS
          have hdj : d j ≠ 0 := by intro h; rw [h] at hdc; simp at hdc
          have : (c j / d j) * (d j * c j) = c j * c j := by field_simp
          have h2 : τ * (d j * c j) ≤ c j * c j := by
            rw [← this]; exact mul_le_mul_of_nonneg_right hle hdc.le
          simp only [c'']; nlinarith
        · push Not at hdc
          simp only [c'']; nlinarith
      rcases hge.lt_or_eq with h | h
      · exact Or.inr h
      · left; rcases mul_eq_zero.1 h.symm with h' | h'
        · exact h'
        · exact absurd h' hcj
    have hj1zero : c'' j1 = 0 := by
      simp only [c'', hτ]; field_simp; ring
    have hcard : (Finset.univ.filter (fun j => c'' j ≠ 0)).card ≤ N := by
      have hsub : Finset.univ.filter (fun j => c'' j ≠ 0) ⊂
          Finset.univ.filter (fun j => c j ≠ 0) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨j1, ?_, ?_⟩
          · have : c j1 ≠ 0 := by intro h; rw [h] at hj1pos; simp at hj1pos
            simp [this]
          · simp [hj1zero]
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          intro hcj; apply hj; rcases hsign j with h | h
          · exact h
          · rw [hcj] at h; simp at h
      have := Finset.card_lt_card hsub; omega
    obtain ⟨c', h1, h2, h3⟩ := ih c'' hcard
    refine ⟨c', h1.trans hsum, fun j => ?_, h3⟩
    rcases h2 j with h | h
    · exact Or.inl h
    rcases hsign j with h' | h'
    · rw [h'] at h; simp at h
    right
    have hm := mul_pos h h'
    have hc''ne : c'' j ≠ 0 := by intro hz; rw [hz] at h; simp at h
    have hsq : 0 < c'' j * c'' j := mul_self_pos.2 hc''ne
    have : c' j * c'' j * (c'' j * c j) = (c' j * c j) * (c'' j * c'' j) := by ring
    rw [this] at hm
    exact pos_of_mul_pos_left hm hsq.le

theorem arith (a b γ G H t : ℝ) (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (h1 : a * (-(G + t)) = 0) (h2 : b * (-(H + t)) = 0) (h3 : γ * ((G - t) * (H - t)) = 0) :
    (a - γ * (H - t) ≠ 0 → |G| ≤ t) ∧ (b - γ * (G - t) ≠ 0 → |H| ≤ t) ∧
      (a - γ * (H - t) ≠ 0 → b - γ * (G - t) ≠ 0 → 0 < a - γ * (H - t) ∧ 0 < b - γ * (G - t)) := by
  have hG' : a = 0 ∨ G = -t := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact Or.inl h
    · right; linarith
  have hH' : b = 0 ∨ H = -t := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl h
    · right; linarith
  have hγ' : γ = 0 ∨ G = t ∨ H = t := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inl h
    · rcases mul_eq_zero.1 h with h | h
      · right; left; linarith
      · right; right; linarith
  rcases hG' with hA | hA <;> rcases hH' with hB | hB <;> rcases hγ' with hC | hC | hC <;>
    (try subst a) <;> (try subst b) <;> (try subst γ) <;> (try subst G) <;> (try subst H) <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h h' => ?_⟩ <;>
    first
    | (exfalso; simp at h; done)
    | (exfalso; simp at h'; done)
    | (rw [abs_le]; constructor <;> linarith)
    | exact ⟨lt_of_le_of_ne (by nlinarith) (Ne.symm h), lt_of_le_of_ne (by nlinarith) (Ne.symm h')⟩

open MPECRelax.KDBConv MPECRelax.ScholtesConv

variable {n m p l : ℕ}

abbrev Jx (m p l : ℕ) := Fin m ⊕ Fin p ⊕ Fin l ⊕ Fin l

noncomputable def vv (P : MPEC n m p l) (y : E n) : Jx m p l → E n :=
  Sum.elim (fun i => gradient (P.g i) y) (Sum.elim (fun j => gradient (P.h j) y)
    (Sum.elim (fun i => -gradient (P.G i) y) (fun i => -gradient (P.H i) y)))

theorem sum_vv (P : MPEC n m p l) (y : E n) (c : Jx m p l → ℝ) :
    ∑ j, c j • vv P y j = ∑ i, c (Sum.inl i) • gradient (P.g i) y
      + ∑ j, c (Sum.inr (Sum.inl j)) • gradient (P.h j) y
      - ∑ i, c (Sum.inr (Sum.inr (Sum.inl i))) • gradient (P.G i) y
      - ∑ i, c (Sum.inr (Sum.inr (Sum.inr i))) • gradient (P.H i) y := by
  simp only [Fintype.sum_sum_type, vv, Sum.elim_inl, Sum.elim_inr, smul_neg,
    Finset.sum_neg_distrib]
  abel

def SignOK (c : Jx m p l → ℝ) : Prop :=
  (∀ i, 0 ≤ c (Sum.inl i)) ∧ ∀ i, c (Sum.inr (Sum.inr (Sum.inl i))) ≠ 0 →
    c (Sum.inr (Sum.inr (Sum.inr i))) ≠ 0 →
    0 < c (Sum.inr (Sum.inr (Sum.inl i))) ∧ 0 < c (Sum.inr (Sum.inr (Sum.inr i)))

def LocOK (P : MPEC n m p l) (y : E n) (t : ℝ) (c : Jx m p l → ℝ) : Prop :=
  (∀ i, c (Sum.inl i) ≠ 0 → P.g i y = 0) ∧
    (∀ i, c (Sum.inr (Sum.inr (Sum.inl i))) ≠ 0 → |P.G i y| ≤ t) ∧
    (∀ i, c (Sum.inr (Sum.inr (Sum.inr i))) ≠ 0 → |P.H i y| ≤ t)

def LIat (P : MPEC n m p l) (y : E n) (c : Jx m p l → ℝ) : Prop :=
  ∀ d : Jx m p l → ℝ, (∀ j, c j = 0 → d j = 0) → ∑ j, d j • vv P y j = 0 → d = 0

theorem grad_neg_add (F : E n → ℝ) (t : ℝ) (x : E n) :
    gradient (fun y => -(F y + t)) x = -gradient F x := by
  simp only [gradient, fderiv_fun_neg, fderiv_add_const, map_neg]

theorem grad_prod {x : E n} (F K : E n → ℝ) (hF : DifferentiableAt ℝ F x) (hK : DifferentiableAt ℝ K x)
    (t : ℝ) : gradient (fun y => (F y - t) * (K y - t)) x =
      (F x - t) • gradient K x + (K x - t) • gradient F x := by
  have h1 : DifferentiableAt ℝ (fun y => F y - t) x := hF.sub_const t
  have h2 : DifferentiableAt ℝ (fun y => K y - t) x := hK.sub_const t
  simp only [gradient]
  rw [fderiv_fun_mul h1 h2, fderiv_sub_const, fderiv_sub_const, map_add, map_smul, map_smul]

theorem stepA (P : MPEC n m p l) (hP : P.IsC1) (t : ℝ) (ht : 0 < t) (x : E n)
    (hx : (P.RKDB t).IsKKTPoint x) : ∃ c : Jx m p l → ℝ,
      gradient P.f x + ∑ j, c j • vv P x j = 0 ∧ SignOK c ∧ LocOK P x t c := by
  obtain ⟨_, Λ, mu, hΛ0, hcomp, heq⟩ := hx
  have hdG : ∀ i, DifferentiableAt ℝ (P.G i) x := fun i =>
    ((hP.2.2.2.1 i).differentiable (by norm_num)) x
  have hdH : ∀ i, DifferentiableAt ℝ (P.H i) x := fun i =>
    ((hP.2.2.2.2 i).differentiable (by norm_num)) x
  set a : Fin l → ℝ := fun i => Λ (Sum.inr (Sum.inl i))
  set b : Fin l → ℝ := fun i => Λ (Sum.inr (Sum.inr (Sum.inl i)))
  set γ : Fin l → ℝ := fun i => Λ (Sum.inr (Sum.inr (Sum.inr i)))
  refine ⟨Sum.elim (fun i => Λ (Sum.inl i)) (Sum.elim mu (Sum.elim
    (fun i => a i - γ i * (P.H i x - t)) (fun i => b i - γ i * (P.G i x - t)))), ?_, ?_, ?_⟩
  · rw [sum_vv]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hsum : ∑ j, Λ j • gradient ((P.RKDB t).g j) x = ∑ i, Λ (Sum.inl i) • gradient (P.g i) x
        + ∑ i, (a i • (-gradient (P.G i) x) + b i • (-gradient (P.H i) x)
          + γ i • ((P.G i x - t) • gradient (P.H i) x + (P.H i x - t) • gradient (P.G i) x)) := by
      simp only [Fintype.sum_sum_type, MPEC.RKDB, Sum.elim_inl, Sum.elim_inr, grad_neg_add,
        grad_prod _ _ (hdG _) (hdH _), Finset.sum_add_distrib, a, b, γ]
      abel
    have hs2 : ∑ i, (a i • (-gradient (P.G i) x) + b i • (-gradient (P.H i) x)
          + γ i • ((P.G i x - t) • gradient (P.H i) x + (P.H i x - t) • gradient (P.G i) x)) =
        - ∑ i, (a i - γ i * (P.H i x - t)) • gradient (P.G i) x
          - ∑ i, (b i - γ i * (P.G i x - t)) • gradient (P.H i) x := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      module
    rw [hsum, hs2] at heq
    simp only [MPEC.RKDB] at heq
    rw [← heq]
    abel
  · refine ⟨fun i => hΛ0 _, fun i h1 h2 => ?_⟩
    have := (arith (a i) (b i) (γ i) (P.G i x) (P.H i x) t ht (hΛ0 _) (hΛ0 _) (hΛ0 _)
      (by simpa [MPEC.RKDB] using hcomp (Sum.inr (Sum.inl i)))
      (by simpa [MPEC.RKDB] using hcomp (Sum.inr (Sum.inr (Sum.inl i))))
      (by simpa [MPEC.RKDB] using hcomp (Sum.inr (Sum.inr (Sum.inr i))))).2.2
    simpa using this h1 h2
  · have key := fun i => arith (a i) (b i) (γ i) (P.G i x) (P.H i x) t ht (hΛ0 _) (hΛ0 _) (hΛ0 _)
      (by simpa [MPEC.RKDB] using hcomp (Sum.inr (Sum.inl i)))
      (by simpa [MPEC.RKDB] using hcomp (Sum.inr (Sum.inr (Sum.inl i))))
      (by simpa [MPEC.RKDB] using hcomp (Sum.inr (Sum.inr (Sum.inr i))))
    refine ⟨fun i h => ?_, fun i h => (key i).1 (by simpa using h),
      fun i h => (key i).2.1 (by simpa using h)⟩
    have := hcomp (Sum.inl i)
    simp only [MPEC.RKDB, Sum.elim_inl] at this
    simp only [Sum.elim_inl] at h
    exact (mul_eq_zero.1 this).resolve_left h

theorem stepB (P : MPEC n m p l) (hP : P.IsC1) (t : ℝ) (ht : 0 < t) (x : E n)
    (hx : (P.RKDB t).IsKKTPoint x) : ∃ c : Jx m p l → ℝ,
      gradient P.f x + ∑ j, c j • vv P x j = 0 ∧ SignOK c ∧ LocOK P x t c ∧ LIat P x c := by
  classical
  obtain ⟨c0, h0, hs0, hl0⟩ := stepA P hP t ht x hx
  obtain ⟨c, hsum, hrel, hLI⟩ := carath (vv P x) _ c0 le_rfl
  have hne : ∀ j, c j ≠ 0 → c0 j ≠ 0 := by
    intro j hj h; rcases hrel j with h' | h'
    · exact hj h'
    · rw [h] at h'; simp at h'
  have hpos : ∀ j, 0 < c0 j → c j ≠ 0 → 0 < c j := by
    intro j hj hcj; rcases hrel j with h' | h'
    · exact absurd h' hcj
    · exact pos_of_mul_pos_left h' hj.le
  refine ⟨c, by rw [hsum]; exact h0, ⟨fun i => ?_, fun i h1 h2 => ?_⟩, ⟨fun i h => hl0.1 i (hne _ h),
    fun i h => hl0.2.1 i (hne _ h), fun i h => hl0.2.2 i (hne _ h)⟩, hLI⟩
  · by_cases hci : c (Sum.inl i) = 0
    · exact hci.ge
    rcases (hs0.1 i).lt_or_eq with h | h
    · exact (hpos _ h hci).le
    · exact absurd h.symm (hne _ hci)
  · have := hs0.2 i (hne _ h1) (hne _ h2)
    exact ⟨hpos _ this.1 h1, hpos _ this.2 h2⟩

theorem sum_subtype_ext {α M : Type*} [Fintype α] [AddCommMonoid M] (S : Set α) [Fintype S]
    (f : α → M) (hf : ∀ a ∉ S, f a = 0) : ∑ s : S, f s = ∑ a, f a := by
  classical
  rw [Finset.sum_set_coe]
  exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hf a (by simpa using ha))

theorem sum_subtype_dite {α M : Type*} [Fintype α] [AddCommMonoid M] (S : Set α) [Fintype S]
    [DecidablePred (· ∈ S)] (f : S → M) :
    ∑ s : S, f s = ∑ a, if h : a ∈ S then f ⟨a, h⟩ else 0 := by
  rw [← sum_subtype_ext S (fun a => if h : a ∈ S then f ⟨a, h⟩ else 0)
    (by intro a ha; simp [ha])]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [s.2]

theorem bridge (P : MPEC n m p l) (xs : E n) (hfeas : P.Feasible xs) (hCQ : P.MPEC_CPLD xs)
    (u : Jx m p l → ℝ) (hu0 : u ≠ 0) (hsum : ∑ j, u j • vv P xs j = 0)
    (hsign : ∀ i, 0 ≤ u (Sum.inl i))
    (hag : ∀ i, u (Sum.inl i) ≠ 0 → P.g i xs = 0)
    (haG : ∀ i, u (Sum.inr (Sum.inr (Sum.inl i))) ≠ 0 → P.G i xs = 0)
    (haH : ∀ i, u (Sum.inr (Sum.inr (Sum.inr i))) ≠ 0 → P.H i xs = 0) :
    ∀ᶠ y in 𝓝 xs, ∃ d : Jx m p l → ℝ, d ≠ 0 ∧ (∀ j, u j = 0 → d j = 0) ∧
      ∑ j, d j • vv P y j = 0 := by
  classical
  have hmemG : ∀ i, u (Sum.inr (Sum.inr (Sum.inl i))) ≠ 0 → i ∈ P.I0p xs ∪ P.I00 xs := by
    intro i h
    have hG := haG i h
    rcases (hfeas.2.2 i).2.1.lt_or_eq with hH | hH
    · exact Or.inl ⟨hG, hH⟩
    · exact Or.inr ⟨hG, hH.symm⟩
  have hmemH : ∀ i, u (Sum.inr (Sum.inr (Sum.inr i))) ≠ 0 → i ∈ P.Ip0 xs ∪ P.I00 xs := by
    intro i h
    have hH := haH i h
    rcases (hfeas.2.2 i).1.lt_or_eq with hG | hG
    · exact Or.inl ⟨hG, hH⟩
    · exact Or.inr ⟨hG.symm, hH⟩
  set α' : (Fin m ⊕ ↥(P.I0p xs) ⊕ ↥(P.Ip0 xs)) → ℝ := Sum.elim (fun i => u (Sum.inl i)) 0
    with hα'
  set β' : (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs)) → ℝ :=
    Sum.elim (fun j => u (Sum.inr (Sum.inl j)))
      (Sum.elim (fun s => -u (Sum.inr (Sum.inr (Sum.inl s.1))))
        (fun s => -u (Sum.inr (Sum.inr (Sum.inr s.1))))) with hβ'
  have hact : Function.support α' ⊆ (P.TNLP xs).activeSet xs := by
    intro a ha
    rcases a with i | r
    · simp only [Function.mem_support, α', Sum.elim_inl] at ha
      exact hag i ha
    · simp [α'] at ha
  have hpld : (P.TNLP xs).PosLinDep xs (Function.support α') (Function.support β') := by
    refine ⟨α', β', ?_, fun a ha => Function.notMem_support.1 ha,
      fun b hb => Function.notMem_support.1 hb, ?_, ?_⟩
    · intro a _; rcases a with i | r
      · exact hsign i
      · simp [α']
    · obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
        by_contra h; push Not at h; exact hu0 (funext h)
      rcases j with i | j | i | i
      · left; exact ⟨Sum.inl i, hj⟩
      · right; exact ⟨Sum.inl j, hj⟩
      · right; exact ⟨Sum.inr (Sum.inl ⟨i, hmemG i hj⟩), by simpa [β'] using hj⟩
      · right; exact ⟨Sum.inr (Sum.inr ⟨i, hmemH i hj⟩), by simpa [β'] using hj⟩
    · rw [sum_vv] at hsum
      simp only [Fintype.sum_sum_type, MPEC.TNLP, α', β', Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
      rw [sum_subtype_ext (P.I0p xs ∪ P.I00 xs)
          (fun i => (-u (Sum.inr (Sum.inr (Sum.inl i)))) • gradient (P.G i) xs) ?_,
        sum_subtype_ext (P.Ip0 xs ∪ P.I00 xs)
          (fun i => (-u (Sum.inr (Sum.inr (Sum.inr i)))) • gradient (P.H i) xs) ?_]
      · simp only [neg_smul, Finset.sum_neg_distrib]; rw [← hsum]; abel
      all_goals
        intro i hi; by_contra h
        first
        | exact hi (hmemG i (fun h' => h (by simp [h'])))
        | exact hi (hmemH i (fun h' => h (by simp [h'])))
  filter_upwards [hCQ _ _ hact hpld] with y hy
  rw [Fintype.not_linearIndependent_iff] at hy
  obtain ⟨g, hg, z, hz⟩ := hy
  set G1 : (Fin m ⊕ ↥(P.I0p xs) ⊕ ↥(P.Ip0 xs)) → ℝ :=
    fun a => if h : a ∈ Function.support α' then g (Sum.inl ⟨a, h⟩) else 0 with hG1
  set G2 : (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs)) → ℝ :=
    fun b => if h : b ∈ Function.support β' then g (Sum.inr ⟨b, h⟩) else 0 with hG2
  have hg' : ∑ a, G1 a • gradient ((P.TNLP xs).g a) y
      + ∑ b, G2 b • gradient ((P.TNLP xs).h b) y = 0 := by
    rw [← hg]
    conv_rhs => rw [Fintype.sum_sum_type]
    congr 1
    · rw [← sum_subtype_ext (Function.support α')
        (fun a => G1 a • gradient ((P.TNLP xs).g a) y)
        (by intro a ha; simp only [G1, dif_neg ha, zero_smul])]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [G1, dif_pos s.2, Sum.elim_inl]
    · rw [← sum_subtype_ext (Function.support β')
        (fun b => G2 b • gradient ((P.TNLP xs).h b) y)
        (by intro b hb; simp only [G2, dif_neg hb, zero_smul])]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [G2, dif_pos s.2, Sum.elim_inr]
  refine ⟨Sum.elim (fun i => G1 (Sum.inl i)) (Sum.elim (fun j => G2 (Sum.inl j)) (Sum.elim
      (fun i => if h : i ∈ P.I0p xs ∪ P.I00 xs then -G2 (Sum.inr (Sum.inl ⟨i, h⟩)) else 0)
      (fun i => if h : i ∈ P.Ip0 xs ∪ P.I00 xs then -G2 (Sum.inr (Sum.inr ⟨i, h⟩)) else 0))),
    ?_, ?_, ?_⟩
  · intro hd
    apply hz
    rcases z with ⟨a, ha⟩ | ⟨b, hb⟩
    · rcases a with i | r
      · have := congrFun hd (Sum.inl i)
        simp only [Sum.elim_inl, Pi.zero_apply, G1, dif_pos ha] at this
        exact this
      · exfalso; simp [α'] at ha
    · rcases b with j | ⟨i, hi⟩ | ⟨i, hi⟩
      · have := congrFun hd (Sum.inr (Sum.inl j))
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, G2, dif_pos hb] at this
        exact this
      · have := congrFun hd (Sum.inr (Sum.inr (Sum.inl i)))
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, G2, dif_pos hi, dif_pos hb,
          neg_eq_zero] at this
        exact this
      · have := congrFun hd (Sum.inr (Sum.inr (Sum.inr i)))
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, G2, dif_pos hi, dif_pos hb,
          neg_eq_zero] at this
        exact this
  · intro j hj
    rcases j with i | j | i | i
    · simp [G1, α', hj]
    · simp [G2, β', hj]
    · simp [G2, β', hj]
    · simp [G2, β', hj]
  · rw [sum_vv]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have e1 : ∑ a, G1 a • gradient ((P.TNLP xs).g a) y
        = ∑ i, G1 (Sum.inl i) • gradient (P.g i) y := by
      have : ∀ r, G1 (Sum.inr r) = 0 := by intro r; simp [G1, α']
      simp [Fintype.sum_sum_type, MPEC.TNLP, this]
    have e2 : ∑ b, G2 b • gradient ((P.TNLP xs).h b) y
        = ∑ j, G2 (Sum.inl j) • gradient (P.h j) y
          + ∑ s : ↥(P.I0p xs ∪ P.I00 xs), G2 (Sum.inr (Sum.inl s)) • gradient (P.G s) y
          + ∑ s : ↥(P.Ip0 xs ∪ P.I00 xs), G2 (Sum.inr (Sum.inr s)) • gradient (P.H s) y := by
      simp only [Fintype.sum_sum_type, MPEC.TNLP, Sum.elim_inl, Sum.elim_inr]
      abel
    have e3 : ∑ i, (if h : i ∈ P.I0p xs ∪ P.I00 xs then -G2 (Sum.inr (Sum.inl ⟨i, h⟩)) else 0)
          • gradient (P.G i) y
        = -∑ s : ↥(P.I0p xs ∪ P.I00 xs), G2 (Sum.inr (Sum.inl s)) • gradient (P.G s) y := by
      rw [sum_subtype_dite, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    have e4 : ∑ i, (if h : i ∈ P.Ip0 xs ∪ P.I00 xs then -G2 (Sum.inr (Sum.inr ⟨i, h⟩)) else 0)
          • gradient (P.H i) y
        = -∑ s : ↥(P.Ip0 xs ∪ P.I00 xs), G2 (Sum.inr (Sum.inr s)) • gradient (P.H s) y := by
      rw [sum_subtype_dite, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    rw [e3, e4]
    rw [e1, e2] at hg'
    rw [← hg']
    abel

theorem grad_cont {F : E n → ℝ} (hF : ContDiff ℝ 1 F) : Continuous (gradient F) := by
  have : gradient F = fun y => (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ F y) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp (hF.continuous_fderiv (by norm_num))

theorem vv_cont (P : MPEC n m p l) (hP : P.IsC1) (j : Jx m p l) :
    Continuous (fun y => vv P y j) := by
  rcases j with i | j | i | i
  · exact grad_cont (hP.2.1 i)
  · exact grad_cont (hP.2.2.1 j)
  · exact (grad_cont (hP.2.2.2.1 i)).neg
  · exact (grad_cont (hP.2.2.2.2 i)).neg

theorem limit_feasible (P : MPEC n m p l) (hP : P.IsC1) (t : ℕ → ℝ)
    (ht_lim : Tendsto t atTop (𝓝 0)) (x : ℕ → E n)
    (hfeas : ∀ k, (P.RKDB (t k)).Feasible (x k)) (xs : E n) (hxs : Tendsto x atTop (𝓝 xs)) :
    P.Feasible xs := by
  refine ⟨fun i => ?_, fun j => ?_, fun i => ?_⟩
  · have h1 : Tendsto (fun k => P.g i (x k)) atTop (𝓝 (P.g i xs)) :=
      ((hP.2.1 i).continuous.tendsto xs).comp hxs
    exact le_of_tendsto' h1 (fun k => (hfeas k).1 (Sum.inl i))
  · have h1 : Tendsto (fun k => P.h j (x k)) atTop (𝓝 (P.h j xs)) :=
      ((hP.2.2.1 j).continuous.tendsto xs).comp hxs
    have h2 : (fun k => P.h j (x k)) = fun _ => 0 := funext fun k => (hfeas k).2 j
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · have hG : Tendsto (fun k => P.G i (x k)) atTop (𝓝 (P.G i xs)) :=
      ((hP.2.2.2.1 i).continuous.tendsto xs).comp hxs
    have hH : Tendsto (fun k => P.H i (x k)) atTop (𝓝 (P.H i xs)) :=
      ((hP.2.2.2.2 i).continuous.tendsto xs).comp hxs
    have hG0 : 0 ≤ P.G i xs := by
      have := ge_of_tendsto' (hG.add ht_lim) (fun k => by
        have := (hfeas k).1 (Sum.inr (Sum.inl i))
        simp only [MPEC.RKDB, Sum.elim_inr, Sum.elim_inl] at this
        show (0:ℝ) ≤ P.G i (x k) + t k
        linarith)
      simpa using this
    have hH0 : 0 ≤ P.H i xs := by
      have := ge_of_tendsto' (hH.add ht_lim) (fun k => by
        have := (hfeas k).1 (Sum.inr (Sum.inr (Sum.inl i)))
        simp only [MPEC.RKDB, Sum.elim_inr, Sum.elim_inl] at this
        show (0:ℝ) ≤ P.H i (x k) + t k
        linarith)
      simpa using this
    have hGH : P.G i xs * P.H i xs ≤ 0 := by
      have := le_of_tendsto' ((hG.sub ht_lim).mul (hH.sub ht_lim)) (fun k => by
        have := (hfeas k).1 (Sum.inr (Sum.inr (Sum.inr i)))
        simp only [MPEC.RKDB, Sum.elim_inr] at this
        exact this)
      simpa using this
    exact ⟨hG0, hH0, le_antisymm hGH (mul_nonneg hG0 hH0)⟩

theorem eventually_adm (P : MPEC n m p l) (hP : P.IsC1) (t : ℕ → ℝ)
    (ht_lim : Tendsto t atTop (𝓝 0)) (x : ℕ → E n) (xs : E n) (hxs : Tendsto x atTop (𝓝 xs))
    (c : ℕ → Jx m p l → ℝ) (hloc : ∀ k, LocOK P (x k) (t k) (c k)) :
    ∀ᶠ k in atTop, (∀ i, c k (Sum.inl i) ≠ 0 → P.g i xs = 0) ∧
      (∀ i, c k (Sum.inr (Sum.inr (Sum.inl i))) ≠ 0 → P.G i xs = 0) ∧
      (∀ i, c k (Sum.inr (Sum.inr (Sum.inr i))) ≠ 0 → P.H i xs = 0) := by
  refine Eventually.and (eventually_all.2 fun i => ?_)
    (Eventually.and (eventually_all.2 fun i => ?_) (eventually_all.2 fun i => ?_))
  · by_cases hg : P.g i xs = 0
    · exact Eventually.of_forall fun k _ => hg
    · have h1 : Tendsto (fun k => P.g i (x k)) atTop (𝓝 (P.g i xs)) :=
        ((hP.2.1 i).continuous.tendsto xs).comp hxs
      filter_upwards [h1.eventually_ne hg] with k hk hc
      exact absurd ((hloc k).1 i hc) hk
  · by_cases hG : P.G i xs = 0
    · exact Eventually.of_forall fun k _ => hG
    · have h1 : Tendsto (fun k => |P.G i (x k)| - t k) atTop (𝓝 (|P.G i xs| - 0)) :=
        (((hP.2.2.2.1 i).continuous.tendsto xs).comp hxs).abs.sub ht_lim
      have hpos : (0:ℝ) < |P.G i xs| - 0 := by simpa using hG
      filter_upwards [h1.eventually_const_lt hpos] with k hk hc
      have := (hloc k).2.1 i hc
      linarith
  · by_cases hH : P.H i xs = 0
    · exact Eventually.of_forall fun k _ => hH
    · have h1 : Tendsto (fun k => |P.H i (x k)| - t k) atTop (𝓝 (|P.H i xs| - 0)) :=
        (((hP.2.2.2.2 i).continuous.tendsto xs).comp hxs).abs.sub ht_lim
      have hpos : (0:ℝ) < |P.H i xs| - 0 := by simpa using hH
      filter_upwards [h1.eventually_const_lt hpos] with k hk hc
      have := (hloc k).2.2 i hc
      linarith

theorem bounded (P : MPEC n m p l) (hP : P.IsC1) (xs : E n) (hfeas : P.Feasible xs)
    (hCQ : P.MPEC_CPLD xs) (x : ℕ → E n) (hxs : Tendsto x atTop (𝓝 xs))
    (c : ℕ → Jx m p l → ℝ)
    (heq : ∀ k, gradient P.f (x k) + ∑ j, c k j • vv P (x k) j = 0)
    (hsign : ∀ k, SignOK (c k)) (hLI : ∀ k, LIat P (x k) (c k))
    (hadm : ∀ᶠ k in atTop, (∀ i, c k (Sum.inl i) ≠ 0 → P.g i xs = 0) ∧
      (∀ i, c k (Sum.inr (Sum.inr (Sum.inl i))) ≠ 0 → P.G i xs = 0) ∧
      (∀ i, c k (Sum.inr (Sum.inr (Sum.inr i))) ≠ 0 → P.H i xs = 0)) :
    ∃ C, ∀ᶠ k in atTop, ‖c k‖ ≤ C := by
  by_contra hcon
  push Not at hcon
  obtain ⟨φ, hφ, hφC⟩ := Filter.extraction_forall_of_frequently (fun N : ℕ => hcon (N : ℝ))
  set w : ℕ → Jx m p l → ℝ := fun k => ‖c (φ k)‖⁻¹ • c (φ k) with hwdef
  have hnpos : ∀ k, 0 < ‖c (φ k)‖ := fun k => lt_of_le_of_lt (Nat.cast_nonneg k) (hφC k)
  have hw : ∀ k, w k ∈ Metric.sphere (0 : Jx m p l → ℝ) 1 := by
    intro k
    simp only [mem_sphere_iff_norm, sub_zero, w, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hnpos k).ne'
  obtain ⟨ū, hū, ψ, hψ, hlim⟩ := (isCompact_sphere (0 : Jx m p l → ℝ) 1).tendsto_subseq hw
  have hū0 : ū ≠ 0 := by intro h; rw [h] at hū; simp at hū
  have hθt : Tendsto (fun k => φ (ψ k)) atTop atTop := (hφ.comp hψ).tendsto_atTop
  have hxθ : Tendsto (fun k => x (φ (ψ k))) atTop (𝓝 xs) := hxs.comp hθt
  have hlimj : ∀ j, Tendsto (fun k => w (ψ k) j) atTop (𝓝 (ū j)) := fun j =>
    ((continuous_apply j).tendsto ū).comp hlim
  have hinv : Tendsto (fun k => ‖c (φ (ψ k))‖⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun k => ‖c (φ (ψ k))‖) atTop atTop := by
      refine tendsto_atTop_mono (fun k => (hφC (ψ k)).le) ?_
      exact tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop
    exact tendsto_inv_atTop_zero.comp this
  have hsumū : ∑ j, ū j • vv P xs j = 0 := by
    have h1 : Tendsto (fun k => ‖c (φ (ψ k))‖⁻¹ • gradient P.f (x (φ (ψ k)))
        + ∑ j, w (ψ k) j • vv P (x (φ (ψ k))) j) atTop
        (𝓝 ((0:ℝ) • gradient P.f xs + ∑ j, ū j • vv P xs j)) :=
      (hinv.smul (((grad_cont hP.1).tendsto xs).comp hxθ)).add
        (tendsto_finsetSum _ fun j _ =>
          (hlimj j).smul (((vv_cont P hP j).tendsto xs).comp hxθ))
    have h2 : (fun k => ‖c (φ (ψ k))‖⁻¹ • gradient P.f (x (φ (ψ k)))
        + ∑ j, w (ψ k) j • vv P (x (φ (ψ k))) j) = fun _ => 0 := by
      funext k
      have := congrArg (fun v => ‖c (φ (ψ k))‖⁻¹ • v) (heq (φ (ψ k)))
      simp only [smul_add, Finset.smul_sum, smul_smul, smul_zero] at this
      simpa only [w, Pi.smul_apply, smul_eq_mul] using this
    rw [h2] at h1
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    simpa using this
  have hev : ∀ j, ū j ≠ 0 → ∀ᶠ k in atTop, c (φ (ψ k)) j ≠ 0 := by
    intro j h
    filter_upwards [(hlimj j).eventually_ne h] with k hk hc
    apply hk; simp [w, hc]
  have hadmθ := hθt.eventually hadm
  have hsg : ∀ i, 0 ≤ ū (Sum.inl i) := fun i => ge_of_tendsto' (hlimj _) fun k => by
    simp only [w, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) ((hsign _).1 i)
  have hbr := bridge P xs hfeas hCQ ū hū0 hsumū hsg
    (fun i h => by obtain ⟨k, hk1, hk2⟩ := ((hev _ h).and hadmθ).exists; exact hk2.1 i hk1)
    (fun i h => by obtain ⟨k, hk1, hk2⟩ := ((hev _ h).and hadmθ).exists; exact hk2.2.1 i hk1)
    (fun i h => by obtain ⟨k, hk1, hk2⟩ := ((hev _ h).and hadmθ).exists; exact hk2.2.2 i hk1)
  have hbrθ := hxθ.eventually hbr
  have hsupp : ∀ᶠ k in atTop, ∀ j, ū j ≠ 0 → c (φ (ψ k)) j ≠ 0 := by
    refine eventually_all.2 fun j => ?_
    by_cases h : ū j = 0
    · exact Eventually.of_forall fun k h' => absurd h h'
    · exact (hev j h).mono fun k hk _ => hk
  obtain ⟨k, hk1, hk2⟩ := (hbrθ.and hsupp).exists
  obtain ⟨d, hd0, hdsupp, hdsum⟩ := hk1
  exact hd0 (hLI (φ (ψ k)) d (fun j hj => hdsupp j (by
    by_contra h; exact (hk2 j h) hj)) hdsum)

theorem main {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → MPECRelax.ScholtesConv.E n) (hx : ∀ k, (P.RKDB (t k)).IsKKTPoint (x k))
    (xs : MPECRelax.ScholtesConv.E n) (hxs : Tendsto x atTop (𝓝 xs)) (hCQ : P.MPEC_CPLD xs) :
    P.IsMStationary xs := by
  classical
  have hfeas := limit_feasible P hP t ht_lim x (fun k => (hx k).1) xs hxs
  choose c hc using fun k => stepB P hP (t k) (ht_pos k) (x k) (hx k)
  have hadm := eventually_adm P hP t ht_lim x xs hxs c (fun k => (hc k).2.2.1)
  obtain ⟨C, hC⟩ := bounded P hP xs hfeas hCQ x hxs c (fun k => (hc k).1) (fun k => (hc k).2.1)
    (fun k => (hc k).2.2.2) hadm
  obtain ⟨cs, -, φ, hφ, hlim⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_closedBall (x := (0 : Jx m p l → ℝ)) (r := C))
    (hC.frequently.mono fun k hk => by simpa using hk)
  have hφt := hφ.tendsto_atTop
  have hxφ : Tendsto (fun k => x (φ k)) atTop (𝓝 xs) := hxs.comp hφt
  have hlimj : ∀ j, Tendsto (fun k => c (φ k) j) atTop (𝓝 (cs j)) := fun j =>
    ((continuous_apply j).tendsto cs).comp hlim
  have hsum : gradient P.f xs + ∑ j, cs j • vv P xs j = 0 := by
    have h1 : Tendsto (fun k => gradient P.f (x (φ k)) + ∑ j, c (φ k) j • vv P (x (φ k)) j)
        atTop (𝓝 (gradient P.f xs + ∑ j, cs j • vv P xs j)) :=
      (((grad_cont hP.1).tendsto xs).comp hxφ).add (tendsto_finsetSum _ fun j _ =>
        (hlimj j).smul (((vv_cont P hP j).tendsto xs).comp hxφ))
    have h2 : (fun k => gradient P.f (x (φ k)) + ∑ j, c (φ k) j • vv P (x (φ k)) j) =
        fun _ => 0 := funext fun k => (hc (φ k)).1
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hev : ∀ j, cs j ≠ 0 → ∀ᶠ k in atTop, c (φ k) j ≠ 0 := fun j h =>
    (hlimj j).eventually_ne h
  have hadmφ := hφt.eventually hadm
  have hag : ∀ i, cs (Sum.inl i) ≠ 0 → P.g i xs = 0 := fun i h => by
    obtain ⟨k, hk1, hk2⟩ := ((hev _ h).and hadmφ).exists; exact hk2.1 i hk1
  have haG : ∀ i, cs (Sum.inr (Sum.inr (Sum.inl i))) ≠ 0 → P.G i xs = 0 := fun i h => by
    obtain ⟨k, hk1, hk2⟩ := ((hev _ h).and hadmφ).exists; exact hk2.2.1 i hk1
  have haH : ∀ i, cs (Sum.inr (Sum.inr (Sum.inr i))) ≠ 0 → P.H i xs = 0 := fun i h => by
    obtain ⟨k, hk1, hk2⟩ := ((hev _ h).and hadmφ).exists; exact hk2.2.2 i hk1
  refine ⟨hfeas, fun i => cs (Sum.inl i), fun j => cs (Sum.inr (Sum.inl j)),
    fun i => cs (Sum.inr (Sum.inr (Sum.inl i))), fun i => cs (Sum.inr (Sum.inr (Sum.inr i))),
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [sum_vv] at hsum
    rw [← hsum]
    abel
  · intro i; exact ge_of_tendsto' (hlimj _) fun k => (hc (φ k)).2.1.1 i
  · intro i
    by_cases h : cs (Sum.inl i) = 0
    · simp [h]
    · simp [hag i h]
  · intro i hi
    by_contra h
    exact absurd (haG i h) hi.1.ne'
  · intro i hi
    by_contra h
    exact absurd (haH i h) hi.2.ne'
  · intro i _
    by_cases h : cs (Sum.inr (Sum.inr (Sum.inl i))) * cs (Sum.inr (Sum.inr (Sum.inr i))) = 0
    · exact Or.inr h
    left
    have hG := left_ne_zero_of_mul h
    have hH := right_ne_zero_of_mul h
    have hpos : ∀ᶠ k in atTop, 0 < c (φ k) (Sum.inr (Sum.inr (Sum.inl i))) ∧
        0 < c (φ k) (Sum.inr (Sum.inr (Sum.inr i))) :=
      ((hev _ hG).and (hev _ hH)).mono fun k hk => (hc (φ k)).2.1.2 i hk.1 hk.2
    have h1 := ge_of_tendsto (hlimj _) (hpos.mono fun k hk => hk.1.le)
    have h2 := ge_of_tendsto (hlimj _) (hpos.mono fun k hk => hk.2.le)
    exact ⟨lt_of_le_of_ne h1 (Ne.symm hG), lt_of_le_of_ne h2 (Ne.symm hH)⟩

end KDB35Aux

theorem solution {n m p l : ℕ} (P : MPECRelax.KDBConv.MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (_ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → MPECRelax.ScholtesConv.E n) (hx : ∀ k, (P.RKDB (t k)).IsKKTPoint (x k))
    (xs : MPECRelax.ScholtesConv.E n) (hxs : Tendsto x atTop (𝓝 xs)) (hCQ : P.MPEC_CPLD xs) :
    P.IsMStationary xs :=
  KDB35Aux.main P hP t ht_pos ht_lim x hx xs hxs hCQ
