-- Prove2me | solution 1 for GeomRescale.claim_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:51:54.353991+00:00
-- url     : https://prove2.me/submissions/2239ae31-fb6d-4409-a339-62aabf2e34f6

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_norm1
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_Lone
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Ff
import Definitions.Def_GeomRescale_alpha

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace Aux_GeomRescale_claim_2_2
open GeomRescale

theorem mem_before {n : ℕ} (σ : Equiv.Perm (Fin n)) (u v : Fin n) :
    u ∈ before σ v ↔ σ u < σ v := by
  simp [before]

theorem univ_lower {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsLowerIdeal σ Finset.univ :=
  fun _ _ w _ => Finset.mem_univ w

theorem dimret {n : ℕ} {f : Finset (Fin n) → ℝ} (hsub : Submodular f) {A B : Finset (Fin n)}
    (hAB : A ⊆ B) {v : Fin n} (hv : v ∉ B) :
    f (insert v B) - f B ≤ f (insert v A) - f A := by
  have h := hsub (insert v A) B
  have h1 : insert v A ∪ B = insert v B := by
    ext x
    have := @hAB x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have h2 : insert v A ∩ B = A := by
    ext x
    have := @hAB x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h | h, h'⟩
      · subst h
        exact absurd h' hv
      · exact h
    · intro h
      exact ⟨Or.inr h, this h⟩
  rw [h1, h2] at h
  linarith

theorem xsum_insert {n : ℕ} (x : Fin n → ℝ) {a : Fin n} {s : Finset (Fin n)} (ha : a ∉ s) :
    xsum x (insert a s) = x a + xsum x s := by
  unfold xsum
  rw [Finset.sum_insert ha]

theorem greedy_le {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (σ : Equiv.Perm (Fin n)) (U : Finset (Fin n)) :
    xsum (greedy f σ) U ≤ f U - f ∅ := by
  induction U using Finset.induction_on_max_value (fun v => σ v) with
  | empty => simp [xsum]
  | insert a s ha hmax ih =>
    have hs : s ⊆ before σ a := by
      intro x hx
      rw [mem_before]
      rcases lt_or_eq_of_le (hmax x hx) with h | h
      · exact h
      · exact absurd (by rw [← σ.injective h]; exact hx) ha
    have hnot : a ∉ before σ a := by
      rw [mem_before]
      exact lt_irrefl _
    have h1 := dimret hsub hs hnot
    rw [xsum_insert _ ha]
    have h3 : greedy f σ a = f (insert a (before σ a)) - f (before σ a) := rfl
    linarith

theorem greedy_eq {n : ℕ} (f : Finset (Fin n) → ℝ) (σ : Equiv.Perm (Fin n))
    (U : Finset (Fin n)) (hU : IsLowerIdeal σ U) : xsum (greedy f σ) U = f U - f ∅ := by
  induction U using Finset.induction_on_max_value (fun v => σ v) with
  | empty => simp [xsum]
  | insert a s ha hmax ih =>
    have hb : before σ a = s := by
      ext x
      rw [mem_before]
      constructor
      · intro h
        have hx := hU a (Finset.mem_insert_self a s) x h
        rcases Finset.mem_insert.mp hx with hx | hx
        · subst hx
          exact absurd h (lt_irrefl _)
        · exact hx
      · intro hx
        rcases lt_or_eq_of_le (hmax x hx) with h | h
        · exact h
        · exact absurd (by rw [← σ.injective h]; exact hx) ha
    have hs : IsLowerIdeal σ s := by
      intro u hu w hw
      have := hU u (Finset.mem_insert_of_mem hu) w hw
      rcases Finset.mem_insert.mp this with h | h
      · subst h
        exact absurd (lt_of_lt_of_le hw (hmax u hu)) (lt_irrefl _)
      · exact h
    rw [xsum_insert _ ha, ih hs]
    show f (insert a (before σ a)) - f (before σ a) + (f s - f ∅) = f (insert a s) - f ∅
    rw [hb]
    ring

theorem greedy_mem {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (σ : Equiv.Perm (Fin n)) : greedy f σ ∈ baseB f := by
  simp only [baseB, Set.mem_setOf_eq]
  refine ⟨fun U => ?_, ?_⟩
  · have := greedy_le f hsub σ U
    linarith
  · have := greedy_eq f σ Finset.univ (univ_lower σ)
    linarith

theorem exists_lower {n : ℕ} (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), IsLowerIdeal σ S := by
  let w : Fin n → ℝ := fun v => if v ∈ S then (0 : ℝ) else 1
  refine ⟨(Tuple.sort w).symm, fun u hu x hx => ?_⟩
  have hm := Tuple.monotone_sort w (le_of_lt hx)
  have h : w x ≤ w u := by simpa using hm
  simp only [w, hu, if_true] at h
  by_contra hx'
  simp only [hx', if_false] at h
  linarith

theorem xsum_single {n : ℕ} (x : Fin n → ℝ) (v : Fin n) : xsum x {v} = x v := by
  simp [xsum]

theorem xsum_erase {n : ℕ} (x : Fin n → ℝ) (v : Fin n) :
    xsum x (Finset.univ.erase v) = xsum x Finset.univ - x v := by
  unfold xsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  ring

theorem alpha_nonneg {n : ℕ} (f : Finset (Fin n) → ℝ) (v : Fin n) : 0 ≤ GeomRescale.alpha f v :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem abs_le_alpha {n : ℕ} (f : Finset (Fin n) → ℝ) {z : Fin n → ℝ} (hz : z ∈ baseB f)
    (v : Fin n) : |z v| ≤ GeomRescale.alpha f v := by
  simp only [baseB, Set.mem_setOf_eq] at hz
  have h1 := hz.1 {v}
  have h2 := hz.1 (Finset.univ.erase v)
  rw [xsum_single] at h1
  rw [xsum_erase, hz.2] at h2
  unfold GeomRescale.alpha
  rw [abs_le]
  constructor
  · have := neg_abs_le (f Finset.univ - f (Finset.univ.erase v))
    have := le_max_right |f {v}| |f Finset.univ - f (Finset.univ.erase v)|
    linarith
  · have := le_abs_self (f {v})
    have := le_max_left |f {v}| |f Finset.univ - f (Finset.univ.erase v)|
    linarith

theorem baseB_closed {n : ℕ} (f : Finset (Fin n) → ℝ) : IsClosed (baseB f) := by
  have hc : ∀ U : Finset (Fin n), Continuous (fun x : Fin n → ℝ => xsum x U) := by
    intro U
    unfold xsum
    exact continuous_finset_sum _ (fun v _ => continuous_apply v)
  have : baseB f = (⋂ U : Finset (Fin n), {x | xsum x U ≤ f U}) ∩
      {x | xsum x Finset.univ = f Finset.univ} := by
    ext x
    simp [baseB]
  rw [this]
  refine IsClosed.inter (isClosed_iInter (fun U => ?_)) ?_
  · exact isClosed_le (hc U) continuous_const
  · exact isClosed_eq (hc _) continuous_const

theorem baseB_sub_Icc {n : ℕ} (f : Finset (Fin n) → ℝ) :
    baseB f ⊆ Set.Icc (-GeomRescale.alpha f) (GeomRescale.alpha f) := by
  intro z hz
  constructor
  · intro v
    have := abs_le_alpha f hz v
    have := neg_abs_le (z v)
    simp only [Pi.neg_apply]
    linarith
  · intro v
    have := abs_le_alpha f hz v
    have := le_abs_self (z v)
    linarith

theorem baseB_compact {n : ℕ} (f : Finset (Fin n) → ℝ) : IsCompact (baseB f) :=
  IsCompact.of_isClosed_subset isCompact_Icc (baseB_closed f) (baseB_sub_Icc f)

theorem baseB_nonempty {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0) :
    (baseB f).Nonempty :=
  ⟨greedy f (Equiv.refl _), greedy_mem f hsub hf0 _⟩

theorem norm1_cont {n : ℕ} : Continuous (fun z : Fin n → ℝ => norm1 z) := by
  unfold norm1
  exact continuous_finset_sum _ (fun v _ => continuous_abs.comp (continuous_apply v))

theorem norm2_cont {n : ℕ} : Continuous (fun z : Fin n → ℝ => norm2 z) := by
  unfold norm2
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ (fun v _ => (continuous_apply v).pow 2))

theorem greatest_of_cont {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) :
    IsGreatest (g '' baseB f) (sSup (g '' baseB f)) :=
  IsCompact.isGreatest_sSup ((baseB_compact f).image hg) ((baseB_nonempty f hsub hf0).image g)

theorem le_sSup_img {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) {z : Fin n → ℝ} (hz : z ∈ baseB f) :
    g z ≤ sSup (g '' baseB f) :=
  (greatest_of_cont f hsub hf0 g hg).2 ⟨z, hz, rfl⟩

theorem sSup_img_le {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) {c : ℝ} (hc : ∀ z ∈ baseB f, g z ≤ c) :
    sSup (g '' baseB f) ≤ c := by
  obtain ⟨⟨z, hz, hz'⟩, _⟩ := greatest_of_cont f hsub hf0 g hg
  rw [← hz']
  exact hc z hz

theorem norm1_nonneg {n : ℕ} (z : Fin n → ℝ) : 0 ≤ norm1 z :=
  Finset.sum_nonneg (fun v _ => abs_nonneg (z v))

theorem norm2_nonneg {n : ℕ} (z : Fin n → ℝ) : 0 ≤ norm2 z := Real.sqrt_nonneg _

theorem norm2_le_norm1 {n : ℕ} (z : Fin n → ℝ) : norm2 z ≤ norm1 z := by
  unfold norm2
  rw [Real.sqrt_le_left (norm1_nonneg z)]
  have : ∀ v, z v ^ 2 ≤ |z v| * norm1 z := by
    intro v
    have h1 : |z v| ≤ norm1 z :=
      Finset.single_le_sum (f := fun v => |z v|) (fun v _ => abs_nonneg (z v)) (Finset.mem_univ v)
    rw [← sq_abs, sq]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  calc ∑ v, z v ^ 2 ≤ ∑ v, |z v| * norm1 z := Finset.sum_le_sum (fun v _ => this v)
    _ = norm1 z ^ 2 := by rw [← Finset.sum_mul]; unfold norm1; ring

theorem norm1_le_sqrt_norm2 {n : ℕ} (z : Fin n → ℝ) : norm1 z ≤ √(n : ℝ) * norm2 z := by
  unfold norm2
  rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun v => |z v|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at h
  unfold norm1
  exact h

theorem abs_le_Ff {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : |f S| ≤ Ff f :=
  Finset.le_sup' (fun S => |f S|) (Finset.mem_univ S)

theorem Ff_nonneg {n : ℕ} (f : Finset (Fin n) → ℝ) : 0 ≤ Ff f :=
  le_trans (abs_nonneg _) (abs_le_Ff f ∅)

theorem norm1_eq_two {n : ℕ} (z : Fin n → ℝ) :
    norm1 z = 2 * xsum z (Finset.univ.filter (fun v => 0 < z v)) - xsum z Finset.univ := by
  unfold norm1 xsum
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => 0 < z v) (fun v => |z v|),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => 0 < z v) z]
  have h1 : ∑ v ∈ Finset.univ.filter (fun v => 0 < z v), |z v| =
      ∑ v ∈ Finset.univ.filter (fun v => 0 < z v), z v :=
    Finset.sum_congr rfl (fun v hv => abs_of_pos (Finset.mem_filter.mp hv).2)
  have h2 : ∑ v ∈ Finset.univ.filter (fun v => ¬ 0 < z v), |z v| =
      ∑ v ∈ Finset.univ.filter (fun v => ¬ 0 < z v), -z v :=
    Finset.sum_congr rfl (fun v hv => abs_of_nonpos (not_lt.mp (Finset.mem_filter.mp hv).2))
  rw [h1, h2, Finset.sum_neg_distrib]
  ring

theorem abs_f_le_Lone {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (S : Finset (Fin n)) : |f S| ≤ Lone f := by
  obtain ⟨σ, hσ⟩ := exists_lower S
  have hx := greedy_eq f σ S hσ
  rw [hf0, sub_zero] at hx
  rw [← hx]
  calc |xsum (greedy f σ) S| ≤ ∑ v ∈ S, |greedy f σ v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ norm1 (greedy f σ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun v _ _ => abs_nonneg _)
    _ ≤ Lone f := le_sSup_img f hsub hf0 norm1 norm1_cont (greedy_mem f hsub hf0 σ)

end Aux_GeomRescale_claim_2_2

open GeomRescale Aux_GeomRescale_claim_2_2 in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0) :
    (IsGreatest (norm1 '' baseB f) (Lone f) ∧ IsGreatest (norm2 '' baseB f) (Ltwo f)) ∧
      (Ltwo f ≤ Lone f ∧ Lone f ≤ √(n : ℝ) * Ltwo f) ∧
      (Ff f ≤ Lone f ∧ Lone f ≤ 3 * Ff f) ∧
      ((∀ z ∈ baseB f, ∀ v, |z v| ≤ alpha f v) ∧
        Lone f ≤ norm1 (alpha f) ∧ norm1 (alpha f) = ∑ v, alpha f v ∧
        Ltwo f ≤ norm2 (alpha f)) ∧
      ∀ v, alpha f v ≤ 2 * Ff f := by
  have hG1 : IsGreatest (norm1 '' baseB f) (Lone f) :=
    greatest_of_cont f hsub hf0 norm1 norm1_cont
  have hG2 : IsGreatest (norm2 '' baseB f) (Ltwo f) :=
    greatest_of_cont f hsub hf0 norm2 norm2_cont
  have hL1 : ∀ z ∈ baseB f, norm1 z ≤ Lone f := fun z hz => hG1.2 ⟨z, hz, rfl⟩
  have hL2 : ∀ z ∈ baseB f, norm2 z ≤ Ltwo f := fun z hz => hG2.2 ⟨z, hz, rfl⟩
  obtain ⟨z1, hz1, hz1e⟩ := hG1.1
  obtain ⟨z2, hz2, hz2e⟩ := hG2.1
  refine ⟨⟨hG1, hG2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨fun z hz v => abs_le_alpha f hz v, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hz2e]
    exact le_trans (norm2_le_norm1 z2) (hL1 z2 hz2)
  · rw [← hz1e]
    exact le_trans (norm1_le_sqrt_norm2 z1)
      (mul_le_mul_of_nonneg_left (hL2 z1 hz1) (Real.sqrt_nonneg _))
  · unfold Ff
    exact Finset.sup'_le _ _ (fun S _ => abs_f_le_Lone f hsub hf0 S)
  · rw [← hz1e]
    simp only [baseB, Set.mem_setOf_eq] at hz1
    rw [norm1_eq_two, hz1.2]
    have h1 := hz1.1 (Finset.univ.filter (fun v => 0 < z1 v))
    have h2 := abs_le_Ff f (Finset.univ.filter (fun v => 0 < z1 v))
    have h3 := abs_le_Ff f Finset.univ
    have h4 := le_abs_self (f (Finset.univ.filter (fun v => 0 < z1 v)))
    have h5 := neg_abs_le (f Finset.univ)
    linarith
  · rw [← hz1e]
    unfold norm1
    exact Finset.sum_le_sum (fun v _ => le_trans (abs_le_alpha f hz1 v) (le_abs_self _))
  · unfold norm1
    exact Finset.sum_congr rfl (fun v _ => abs_of_nonneg (alpha_nonneg f v))
  · rw [← hz2e]
    unfold norm2
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum (fun v _ => ?_)
    rw [← sq_abs (z2 v)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_alpha f hz2 v) 2
  · intro v
    unfold GeomRescale.alpha
    refine max_le ?_ ?_
    · have := abs_le_Ff f {v}
      have := Ff_nonneg f
      linarith
    · have h1 := abs_le_Ff f Finset.univ
      have h2 := abs_le_Ff f (Finset.univ.erase v)
      rw [abs_le]
      constructor
      · have := neg_abs_le (f Finset.univ)
        have := le_abs_self (f (Finset.univ.erase v))
        linarith
      · have := le_abs_self (f Finset.univ)
        have := neg_abs_le (f (Finset.univ.erase v))
        linarith

