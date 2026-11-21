-- Prove2me | solution 1 for GeomRescale.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:55:50.872187+00:00
-- url     : https://prove2.me/submissions/5bcb2a64-845a-4c10-9428-fc85a326167d

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_Lone

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace Aux_GeomRescale_lemma_3_4
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

noncomputable def abnd {n : ℕ} (f : Finset (Fin n) → ℝ) (v : Fin n) : ℝ :=
  max |f {v}| |f Finset.univ - f (Finset.univ.erase v)|

theorem abs_le_abnd {n : ℕ} (f : Finset (Fin n) → ℝ) {z : Fin n → ℝ} (hz : z ∈ baseB f)
    (v : Fin n) : |z v| ≤ abnd f v := by
  simp only [baseB, Set.mem_setOf_eq] at hz
  have h1 := hz.1 {v}
  have h2 := hz.1 (Finset.univ.erase v)
  rw [xsum_single] at h1
  rw [xsum_erase, hz.2] at h2
  unfold abnd
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
    baseB f ⊆ Set.Icc (-abnd f) (abnd f) := by
  intro z hz
  constructor
  · intro v
    have := abs_le_abnd f hz v
    have := neg_abs_le (z v)
    simp only [Pi.neg_apply]
    linarith
  · intro v
    have := abs_le_abnd f hz v
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

theorem enl_empty {n : ℕ} (f : Finset (Fin n) → ℝ) (m : ℝ) : enlarge f m ∅ = 0 :=
  if_pos (Or.inl rfl)

theorem enl_univ {n : ℕ} (f : Finset (Fin n) → ℝ) (m : ℝ) : enlarge f m Finset.univ = 0 :=
  if_pos (Or.inr rfl)

theorem enl_mid {n : ℕ} (f : Finset (Fin n) → ℝ) (m : ℝ) (U : Finset (Fin n)) (h1 : U ≠ ∅)
    (h2 : U ≠ Finset.univ) : enlarge f m U = f U + m :=
  if_neg (not_or.mpr ⟨h1, h2⟩)

theorem enlarge_sub {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) : Submodular (enlarge f μ) := by
  have hμ0 : 0 ≤ μ := le_trans (le_max_left _ _) hμ
  have hμ1 : -f Finset.univ ≤ μ := le_trans (le_max_right _ _) hμ
  have hg0 : ∀ m, enlarge f m ∅ = 0 := fun m => if_pos (Or.inl rfl)
  have hgu : ∀ m, enlarge f m Finset.univ = 0 := fun m => if_pos (Or.inr rfl)
  have hgp : ∀ m U, U ≠ ∅ → U ≠ Finset.univ → enlarge f m U = f U + m :=
    fun m U h1 h2 => if_neg (not_or.mpr ⟨h1, h2⟩)
  intro S T
  by_cases hS0 : S = ∅
  · rw [hS0, Finset.empty_union, Finset.empty_inter, hg0] <;> linarith
  by_cases hT0 : T = ∅
  · rw [hT0, Finset.union_empty, Finset.inter_empty, hg0] <;> linarith
  by_cases hSu : S = Finset.univ
  · rw [hSu, Finset.union_eq_left.2 (Finset.subset_univ T),
      Finset.inter_eq_right.2 (Finset.subset_univ T), hgu] <;> linarith
  by_cases hTu : T = Finset.univ
  · rw [hTu, Finset.union_eq_right.2 (Finset.subset_univ S),
      Finset.inter_eq_left.2 (Finset.subset_univ S), hgu] <;> linarith
  rw [hgp μ S hS0 hSu, hgp μ T hT0 hTu]
  have hST := hsub S T
  have hU0 : S ∪ T ≠ ∅ := fun h => hS0 (Finset.union_eq_empty.mp h).1
  have hIu : S ∩ T ≠ Finset.univ := by
    intro h
    apply hSu
    refine Finset.eq_univ_of_forall (fun x => ?_)
    have hx := Finset.mem_univ x
    rw [← h] at hx
    exact (Finset.mem_inter.mp hx).1
  by_cases hUu : S ∪ T = Finset.univ
  · rw [hUu, hgu]
    rw [hUu] at hST
    by_cases hI0 : S ∩ T = ∅
    · rw [hI0, hg0]; rw [hI0, hf0] at hST; linarith
    · rw [hgp μ _ hI0 hIu]; linarith
  · rw [hgp μ _ hU0 hUu]
    by_cases hI0 : S ∩ T = ∅
    · rw [hI0, hg0]; rw [hI0, hf0] at hST; linarith
    · rw [hgp μ _ hI0 hIu]; linarith

end Aux_GeomRescale_lemma_3_4

open GeomRescale Aux_GeomRescale_lemma_3_4 in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) (W : Finset (Fin n)) (hW : μ = -f W) :
    Lone (enlarge f μ) ≤ 4 * Lone f := by
  have hgs := enlarge_sub f hsub hf0 μ hμ
  have hg0 := enl_empty f μ
  have hμ0 : 0 ≤ μ := le_trans (le_max_left _ _) hμ
  have hL0 : 0 ≤ Lone f := le_trans (abs_nonneg _) (abs_f_le_Lone f hsub hf0 ∅)
  have hW1 : μ ≤ Lone f := by
    rw [hW]
    exact le_trans (neg_le_abs _) (abs_f_le_Lone f hsub hf0 W)
  show sSup (norm1 '' baseB (enlarge f μ)) ≤ 4 * Lone f
  apply sSup_img_le (enlarge f μ) hgs hg0 norm1 norm1_cont
  intro x hx
  rw [norm1_eq_two]
  simp only [baseB, Set.mem_setOf_eq] at hx
  rw [hx.2, enl_univ]
  set P := Finset.univ.filter (fun v => 0 < x v) with hP
  have h1 := hx.1 P
  have hgP : enlarge f μ P ≤ 2 * Lone f := by
    by_cases hP0 : P = ∅
    · rw [hP0, enl_empty]
      linarith
    by_cases hPu : P = Finset.univ
    · rw [hPu, enl_univ]
      linarith
    rw [enl_mid f μ P hP0 hPu]
    have := le_trans (le_abs_self _) (abs_f_le_Lone f hsub hf0 P)
    linarith
  linarith

