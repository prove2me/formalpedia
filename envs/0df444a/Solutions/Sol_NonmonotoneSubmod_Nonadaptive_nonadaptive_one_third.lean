-- Prove2me | solution 1 for NonmonotoneSubmod.Nonadaptive.nonadaptive_one_third
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T14:59:36.562325+00:00
-- url     : https://prove2.me/submissions/78a5f206-0fcb-44e2-9f29-07d3ade188c9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Nonadaptive_omega



namespace NonmonotoneSubmod.Nonadaptive

open NonmonotoneSubmod.Shared
open scoped symmDiff

variable {X : Type} [Fintype X] [DecidableEq X]

lemma F_half' (f : Finset X → ℝ) :
    F f (fun _ => 1 / 2) = (∑ S : Finset X, f S) * (1 / 2) ^ Fintype.card X := by
  unfold F
  rw [Finset.sum_mul]
  congr 1; funext S
  congr 1
  have : ∀ i : X, (if i ∈ S then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := fun i => by
    split_ifs <;> norm_num
  simp only [this, Finset.prod_const, Finset.card_univ]

lemma quad' (f : Finset X → ℝ) (hf : Submodular f) (O S : Finset X) :
    f Finset.univ + f O + f Oᶜ + f ∅ ≤ f S + f (S ∆ O) + f (S ∆ Oᶜ) + f Sᶜ := by
  have e1 : S ∪ S ∆ O = O ∪ S := by ext x; simp [Finset.mem_symmDiff]; tauto
  have e2 : S ∩ S ∆ O = S \ O := by ext x; simp [Finset.mem_symmDiff]; tauto
  have e3 : S ∆ Oᶜ ∪ Sᶜ = O ∪ Sᶜ := by ext x; simp [Finset.mem_symmDiff]; tauto
  have e4 : S ∆ Oᶜ ∩ Sᶜ = Sᶜ \ O := by ext x; simp [Finset.mem_symmDiff]; tauto
  have e5 : (O ∪ S) ∪ (O ∪ Sᶜ) = Finset.univ := by ext x; simp; tauto
  have e6 : (O ∪ S) ∩ (O ∪ Sᶜ) = O := by ext x; simp; tauto
  have e7 : (S \ O) ∪ (Sᶜ \ O) = Oᶜ := by ext x; simp; tauto
  have e8 : (S \ O) ∩ (Sᶜ \ O) = ∅ := by ext x; simp; tauto
  have h1 := hf S (S ∆ O)
  have h2 := hf (S ∆ Oᶜ) Sᶜ
  have h3 := hf (O ∪ S) (O ∪ Sᶜ)
  have h4 := hf (S \ O) (Sᶜ \ O)
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  rw [e5, e6] at h3
  rw [e7, e8] at h4
  linarith

/-- averaged Lemma 2.3 in unnormalised form -/
lemma sum_quad (f : Finset X → ℝ) (hf : Submodular f) (O : Finset X) :
    (2 : ℝ) ^ Fintype.card X * (f Finset.univ + f O + f Oᶜ + f ∅) ≤
      4 * ∑ S : Finset X, f S := by
  have s1 : ∑ S : Finset X, f (S ∆ O) = ∑ S : Finset X, f S :=
    Fintype.sum_bijective (fun S => S ∆ O)
      (Function.Involutive.bijective (fun S => by simp [symmDiff_symmDiff_cancel_right]))
      _ _ (fun _ => rfl)
  have s2 : ∑ S : Finset X, f (S ∆ Oᶜ) = ∑ S : Finset X, f S :=
    Fintype.sum_bijective (fun S => S ∆ Oᶜ)
      (Function.Involutive.bijective (fun S => by simp [symmDiff_symmDiff_cancel_right]))
      _ _ (fun _ => rfl)
  have s3 : ∑ S : Finset X, f Sᶜ = ∑ S : Finset X, f S :=
    Fintype.sum_bijective (fun S => Sᶜ) (Function.Involutive.bijective compl_compl)
      _ _ (fun _ => rfl)
  have := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset X)))
    (fun S _ => quad' f hf O S)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul] at this
  simp only [Finset.sum_add_distrib] at this
  rw [s1, s2, s3] at this
  push_cast at this
  linarith

lemma sum_pair (f : Finset X → ℝ) (x : X) :
    2 * ∑ S : Finset X, f S = ∑ S : Finset X, f (insert x S) + ∑ S : Finset X, f (S.erase x) := by
  have hT : ∑ S : Finset X, f (S ∆ {x}) = ∑ S : Finset X, f S :=
    Fintype.sum_bijective (fun S => S ∆ {x})
      (Function.Involutive.bijective (fun S => by simp [symmDiff_symmDiff_cancel_right]))
      _ _ (fun _ => rfl)
  have hpt : ∀ S : Finset X, f S + f (S ∆ {x}) = f (insert x S) + f (S.erase x) := by
    intro S
    by_cases hx : x ∈ S
    · have e1 : S ∆ {x} = S.erase x := by
        ext y; simp [Finset.mem_symmDiff]; constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [exact ⟨h2, h1⟩; exact absurd (h1 ▸ hx) h2]
        · rintro ⟨h1, h2⟩; left; exact ⟨h2, h1⟩
      rw [e1, Finset.insert_eq_of_mem hx]
    · have e1 : S ∆ {x} = insert x S := by
        ext y; simp [Finset.mem_symmDiff]; constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [exact Or.inr h1; exact Or.inl h1]
        · rintro (h | h)
          · right; exact ⟨h, h ▸ hx⟩
          · left; exact ⟨h, fun h' => hx (h' ▸ h)⟩
      rw [e1, Finset.erase_eq_of_notMem hx]; ring
  calc 2 * ∑ S : Finset X, f S = ∑ S : Finset X, f S + ∑ S : Finset X, f (S ∆ {x}) := by
        rw [hT]; ring
    _ = ∑ S : Finset X, (f S + f (S ∆ {x})) := by rw [Finset.sum_add_distrib]
    _ = _ := by rw [Finset.sum_congr rfl fun S _ => hpt S, Finset.sum_add_distrib]

lemma chain_up (f : Finset X → ℝ) (hf : Submodular f) (R D : Finset X) :
    f (R ∪ D) ≤ f R + ∑ x ∈ D, (f (insert x R) - f R) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert a D ha ih =>
    have h := hf (R ∪ D) (insert a R)
    have e1 : R ∪ D ∪ insert a R = R ∪ insert a D := by ext y; simp; tauto
    have e2 : (R ∪ D) ∩ insert a R = R := by
      ext y; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · exact h1
        · exact h1
        · exact absurd (h2 ▸ h1) ha
        · exact h2
      · intro h; exact ⟨Or.inl h, Or.inr h⟩
    rw [e1, e2] at h
    rw [Finset.sum_insert ha]
    linarith

lemma chain_down (f : Finset X → ℝ) (hf : Submodular f) (R D : Finset X) :
    f (R \ D) + ∑ x ∈ D, (f R - f (R.erase x)) ≤ f R := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert a D ha ih =>
    have h := hf (R \ D) (R.erase a)
    have e1 : R \ D ∪ R.erase a = R := by
      ext y; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro (⟨h1, _⟩ | ⟨_, h1⟩) <;> exact h1
      · intro h; by_cases hy : y ∈ D
        · right; exact ⟨fun h' => ha (h' ▸ hy), h⟩
        · left; exact ⟨h, hy⟩
    have e2 : R \ D ∩ R.erase a = R \ insert a D := by ext y; simp; tauto
    rw [e1, e2] at h
    rw [Finset.sum_insert ha]
    linarith

lemma submod_union (f : Finset X → ℝ) (hf : Submodular f) (D : Finset X) :
    Submodular (fun S => f (S ∪ D)) := by
  intro S T
  have e1 : S ∪ T ∪ D = (S ∪ D) ∪ (T ∪ D) := by ext y; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  have e2 : S ∩ T ∪ D = (S ∪ D) ∩ (T ∪ D) := by ext y; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  simp only; rw [e1, e2]; exact hf _ _

lemma submod_inter (f : Finset X → ℝ) (hf : Submodular f) (E : Finset X) :
    Submodular (fun S => f (S ∩ E)) := by
  intro S T
  have e1 : (S ∪ T) ∩ E = (S ∩ E) ∪ (T ∩ E) := by ext y; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  have e2 : (S ∩ T) ∩ E = (S ∩ E) ∩ (T ∩ E) := by ext y; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  simp only; rw [e1, e2]; exact hf _ _

theorem nonadaptive_main [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (ωt : X → ℝ)
    (hωt : ∀ x, |ωt x - omega f x| < OPT f / (Fintype.card X : ℝ) ^ 2) :
    (1 / 3 - 4 / (9 * (Fintype.card X : ℝ))) * OPT f ≤
      (8 / 9) * F f (fun _ => 1 / 2) + (1 / 9) * f (Finset.univ.filter (fun x => 0 < ωt x)) := by
  set n := Fintype.card X with hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨C, -, hC⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  have hOPT : OPT f = f C := hC
  have hO0 : 0 ≤ OPT f := by rw [hOPT]; exact hf0 C
  set A := Finset.univ.filter (fun x => 0 < ωt x) with hA
  set B := Aᶜ with hB
  set N : ℝ := (2 : ℝ) ^ n with hN
  set k : ℝ := (1 / 2 : ℝ) ^ n with hk
  have hkN : k * N = 1 := by rw [hk, hN, ← mul_pow]; norm_num
  have hkpos : 0 < k := by positivity
  have hNpos : 0 < N := by positivity
  set Sf := ∑ S : Finset X, f S with hSf
  -- ω in terms of sums
  have hom : ∀ x, omega f x = k * ∑ S : Finset X, (f (insert x S) - f (S.erase x)) := by
    intro x; unfold omega; rw [F_half']; ring
  -- marginal sums
  have hup : ∀ x, ∑ S : Finset X, (f (insert x S) - f S) = N * (omega f x / 2) := by
    intro x
    rw [hom, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have := sum_pair f x
    have e : N * (k * 1) = 1 := by rw [mul_one, mul_comm]; exact hkN
    linear_combination (-(1:ℝ)/2) * this + (-1/2 * ((∑ S : Finset X, f (insert x S)) -
      ∑ S : Finset X, f (S.erase x))) * e
  have hdown : ∀ x, ∑ S : Finset X, (f S - f (S.erase x)) = N * (omega f x / 2) := by
    intro x
    rw [hom, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have := sum_pair f x
    have e : N * (k * 1) = 1 := by rw [mul_one, mul_comm]; exact hkN
    linear_combination (1:ℝ)/2 * this + (-1/2 * ((∑ S : Finset X, f (insert x S)) -
      ∑ S : Finset X, f (S.erase x))) * e
  -- ω bounds
  set ε := OPT f / (n : ℝ) ^ 2 with hε
  have hB_om : ∀ x ∈ B, omega f x ≤ ε := by
    intro x hx
    have hx' : ¬ 0 < ωt x := by simpa [hB, hA] using hx
    have := (abs_lt.1 (hωt x)).1
    linarith
  have hA_om : ∀ x ∈ A, -ε ≤ omega f x := by
    intro x hx
    have hx' : 0 < ωt x := by simpa [hA] using hx
    have := (abs_lt.1 (hωt x)).2
    linarith
  have hεn : (n : ℝ) * ε = OPT f / n := by rw [hε]; field_simp
  -- the upper chain, summed
  set D := B ∩ C
  have hg : ∑ S : Finset X, f (S ∪ D) ≤ Sf + N * (OPT f / (2 * n)) := by
    have h1 : ∑ S : Finset X, f (S ∪ D) ≤
        ∑ S : Finset X, (f S + ∑ x ∈ D, (f (insert x S) - f S)) :=
      Finset.sum_le_sum fun S _ => chain_up f hf S D
    rw [Finset.sum_add_distrib, Finset.sum_comm] at h1
    have h2 : ∑ x ∈ D, ∑ S : Finset X, (f (insert x S) - f S) ≤ ∑ _x ∈ D, N * (ε / 2) := by
      refine Finset.sum_le_sum fun x hx => ?_
      rw [hup]
      have := hB_om x (Finset.mem_inter.1 hx).1
      nlinarith
    have hcard : (D.card : ℝ) ≤ n := by exact_mod_cast Finset.card_le_univ D
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have hε0 : 0 ≤ ε := by positivity
    have h3 : (D.card : ℝ) * (N * (ε / 2)) ≤ N * (OPT f / (2 * n)) := by
      have : (D.card : ℝ) * ε ≤ n * ε := mul_le_mul_of_nonneg_right hcard hε0
      rw [hεn] at this
      have e : N * (OPT f / (2 * n)) = N / 2 * (OPT f / n) := by ring
      rw [e]; nlinarith
    linarith
  -- the lower chain, summed
  set E := B ∪ C
  have hh : ∑ S : Finset X, f (S ∩ E) ≤ Sf + N * (OPT f / (2 * n)) := by
    have hdiff : ∀ S : Finset X, S \ (A \ C) = S ∩ E := by
      intro S; ext y; simp [hB, E]; tauto
    have h1 : ∑ S : Finset X, (f (S ∩ E) + ∑ x ∈ A \ C, (f S - f (S.erase x))) ≤ Sf :=
      Finset.sum_le_sum fun S _ => by rw [← hdiff S]; exact chain_down f hf S (A \ C)
    rw [Finset.sum_add_distrib, Finset.sum_comm] at h1
    have h2 : ∑ _x ∈ A \ C, N * (-ε / 2) ≤ ∑ x ∈ A \ C, ∑ S : Finset X, (f S - f (S.erase x)) := by
      refine Finset.sum_le_sum fun x hx => ?_
      rw [hdown]
      have := hA_om x (Finset.mem_sdiff.1 hx).1
      nlinarith
    have hcard : ((A \ C).card : ℝ) ≤ n := by exact_mod_cast Finset.card_le_univ _
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have hε0 : 0 ≤ ε := by positivity
    have h3 : ((A \ C).card : ℝ) * (N * (ε / 2)) ≤ N * (OPT f / (2 * n)) := by
      have : ((A \ C).card : ℝ) * ε ≤ n * ε := mul_le_mul_of_nonneg_right hcard hε0
      rw [hεn] at this
      have e : N * (OPT f / (2 * n)) = N / 2 * (OPT f / n) := by ring
      rw [e]; nlinarith
    have : ((A \ C).card : ℝ) * (N * (-ε / 2)) = -(((A \ C).card : ℝ) * (N * (ε / 2))) := by ring
    linarith
  -- Lemma 2.3 for g and h
  have hgq := sum_quad (fun S => f (S ∪ D)) (submod_union f hf D) C
  have hhq := sum_quad (fun S => f (S ∩ E)) (submod_inter f hf E) C
  have eg1 : C ∪ D = C := Finset.union_eq_left.2 Finset.inter_subset_right
  have eh1 : Finset.univ ∩ E = E := Finset.univ_inter E
  have eh2 : C ∩ E = C := Finset.inter_eq_left.2 Finset.subset_union_right
  rw [eg1, Finset.empty_union] at hgq
  rw [eh1, eh2, Finset.empty_inter] at hhq
  rw [← hn, ← hN] at hgq hhq
  -- α + β + γ ≥ OPT
  have hαβγ : f C ≤ f A + f D + f E := by
    have h1 := hf A D
    have e1 : A ∪ D = A ∪ C := by ext y; simp [D, hB]; tauto
    have e2 : A ∩ D = ∅ := by ext y; simp [D, hB]; tauto
    rw [e1, e2] at h1
    have h2 := hf (A ∪ C) E
    have e3 : A ∪ C ∪ E = Finset.univ := by ext y; simp [E, hB]; tauto
    have e4 : (A ∪ C) ∩ E = C := by ext y; simp [E, hB]; tauto
    rw [e3, e4] at h2
    have := hf0 Finset.univ
    have := hf0 ∅
    linarith
  -- combine
  have key : N * (f C / 4 + (f D + f E) / 8) ≤ Sf + N * (OPT f / (2 * n)) := by
    have p1 := mul_nonneg hNpos.le (hf0 (Finset.univ ∪ D))
    have p2 := mul_nonneg hNpos.le (hf0 (Cᶜ ∪ D))
    have p3 := mul_nonneg hNpos.le (hf0 (Cᶜ ∩ E))
    have p4 := mul_nonneg hNpos.le (hf0 ∅)
    have d1 : N * (f (Finset.univ ∪ D) + f C + f (Cᶜ ∪ D) + f D) =
        N * f (Finset.univ ∪ D) + N * f C + N * f (Cᶜ ∪ D) + N * f D := by ring
    have d2 : N * (f E + f C + f (Cᶜ ∩ E) + f ∅) =
        N * f E + N * f C + N * f (Cᶜ ∩ E) + N * f ∅ := by ring
    have d3 : N * (f C / 4 + (f D + f E) / 8) = N * f C / 4 + N * f D / 8 + N * f E / 8 := by
      ring
    rw [d1] at hgq; rw [d2] at hhq; rw [d3]
    linarith
  have hF : F f (fun _ => 1 / 2) = Sf * k := by rw [F_half']
  rw [hF]
  have key' : f C / 4 + (f D + f E) / 8 - OPT f / (2 * n) ≤ Sf * k := by
    have := mul_le_mul_of_nonneg_left key hkpos.le
    have e1 : k * (N * (f C / 4 + (f D + f E) / 8)) = f C / 4 + (f D + f E) / 8 := by
      rw [← mul_assoc, hkN, one_mul]
    have e2 : k * (Sf + N * (OPT f / (2 * n))) = Sf * k + OPT f / (2 * n) := by
      rw [mul_add, ← mul_assoc, hkN, one_mul, mul_comm]
    linarith
  have e : (1 / 3 - 4 / (9 * (n : ℝ))) * OPT f =
      8 / 9 * (OPT f / 4 - OPT f / (2 * n)) + OPT f / 9 := by field_simp; ring
  rw [e]
  have h9 : OPT f / 9 = f C / 9 := by rw [hOPT]
  have h4 : OPT f / 4 = f C / 4 := by rw [hOPT]
  linarith

end NonmonotoneSubmod.Nonadaptive

open NonmonotoneSubmod.Nonadaptive

theorem solution {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (ωt : X → ℝ)
    (hωt : ∀ x, |ωt x - omega f x| < NonmonotoneSubmod.Shared.OPT f / (Fintype.card X : ℝ) ^ 2) :
    (1 / 3 - 4 / (9 * (Fintype.card X : ℝ))) * NonmonotoneSubmod.Shared.OPT f ≤
      (8 / 9) * NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2) + (1 / 9) * f (Finset.univ.filter (fun x => 0 < ωt x)) := by
  exact nonadaptive_main f hf0 hf ωt hωt
