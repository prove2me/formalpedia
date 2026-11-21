-- Prove2me | solution 1 for GeomRescale.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:15:06.578475+00:00
-- url     : https://prove2.me/submissions/72672842-a7a1-41b5-a9cf-8f88e4d7b29b

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Fmu
import Definitions.Def_GeomRescale_width
import Definitions.Def_GeomRescale_omega

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace Aux_GeomRescale_lemma_3_8
open GeomRescale

def norm1 {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  ∑ v, |z v|

noncomputable def Lone {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  sSup (norm1 '' SchrijverSFM.Alg.baseB f)

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

theorem norm1_cont {n : ℕ} : Continuous (fun z : Fin n → ℝ => norm1 z) := by
  unfold norm1
  exact continuous_finset_sum _ (fun v _ => continuous_abs.comp (continuous_apply v))

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

theorem norm2_cont {n : ℕ} : Continuous (fun z : Fin n → ℝ => norm2 z) := by
  unfold norm2
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ (fun v _ => (continuous_apply v).pow 2))

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

theorem cs_dot {n : ℕ} (x z : Fin n → ℝ) : x ⬝ᵥ z ≤ norm2 x * norm2 z := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x z
  have h1 : x ⬝ᵥ z ≤ |x ⬝ᵥ z| := le_abs_self _
  have h2 : |x ⬝ᵥ z| ≤ √((∑ v, x v ^ 2) * ∑ v, z v ^ 2) := Real.abs_le_sqrt h
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun v _ => sq_nonneg (x v)))] at h2
  unfold norm2
  linarith

theorem width_ge {n : ℕ} (X : Set (Fin n → ℝ)) (a w : Fin n → ℝ) (hw : w ∈ X)
    (hX : ∀ z ∈ X, norm2 z ≤ 1) : a ⬝ᵥ w ≤ width X a := by
  unfold width
  apply le_csSup
  · refine ⟨norm2 a, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h1 := cs_dot a z
    have h2 := hX z hz
    have h3 := norm2_nonneg a
    nlinarith
  · exact ⟨w, hw, rfl⟩

theorem norm2_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < norm2 x := by
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hx
  unfold norm2
  apply Real.sqrt_pos.mpr
  have h1 : x v ^ 2 ≤ ∑ u, x u ^ 2 :=
    Finset.single_le_sum (f := fun u => x u ^ 2) (fun u _ => sq_nonneg (x u)) (Finset.mem_univ v)
  have h2 : 0 < x v ^ 2 := by
    have : x v ≠ 0 := hv
    positivity
  linarith

theorem norm1_enl_le {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) (hμL : μ ≤ Lone f) {x : Fin n → ℝ}
    (hx : x ∈ baseB (enlarge f μ)) : norm1 x ≤ 4 * Lone f := by
  have hμ0 : 0 ≤ μ := le_trans (le_max_left _ _) hμ
  have hL0 : 0 ≤ Lone f := le_trans (abs_nonneg _) (abs_f_le_Lone f hsub hf0 ∅)
  rw [norm1_eq_two]
  simp only [baseB, Set.mem_setOf_eq] at hx
  rw [hx.2, enl_univ]
  have h1 := hx.1 (Finset.univ.filter (fun v => 0 < x v))
  have hgP : enlarge f μ (Finset.univ.filter (fun v => 0 < x v)) ≤ 2 * Lone f := by
    by_cases hP0 : Finset.univ.filter (fun v => 0 < x v) = ∅
    · rw [hP0, enl_empty]
      linarith
    by_cases hPu : Finset.univ.filter (fun v => 0 < x v) = Finset.univ
    · rw [hPu, enl_univ]
      linarith
    rw [enl_mid f μ _ hP0 hPu]
    have := le_trans (le_abs_self _) (abs_f_le_Lone f hsub hf0 (Finset.univ.filter (fun v => 0 < x v)))
    linarith
  linarith

theorem Lone_le_sqrt_Ltwo {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0) :
    Lone f ≤ √(n : ℝ) * Ltwo f := by
  obtain ⟨⟨z1, hz1, hz1e⟩, _⟩ := greatest_of_cont f hsub hf0 norm1 norm1_cont
  have h1 : norm2 z1 ≤ Ltwo f := le_sSup_img f hsub hf0 norm2 norm2_cont hz1
  show sSup (norm1 '' baseB f) ≤ √(n : ℝ) * Ltwo f
  rw [← hz1e]
  exact le_trans (norm1_le_sqrt_norm2 z1) (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _))

theorem Ltwo_nonneg {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0) :
    0 ≤ Ltwo f := by
  obtain ⟨z, hz⟩ := baseB_nonempty f hsub hf0
  exact le_trans (norm2_nonneg z) (le_sSup_img f hsub hf0 norm2 norm2_cont hz)

theorem part1 {n : ℕ} (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f)) (hf0 : f ∅ = 0)
    (μ : ℤ) (hmin : ∃ S, f S < -μ) (hμ : -μ ≤ min 0 (f Finset.univ)) :
    ∀ x ∈ baseB (enlarge (fR f) (μ : ℝ)), 1 / √(n : ℝ) ≤ width (Fmu (fR f) (μ : ℝ)) x := by
  obtain ⟨S, hS⟩ := hmin
  have hμ' := le_min_iff.mp hμ
  have hS1 : (f S : ℝ) + μ ≤ -1 := by
    have : f S + μ ≤ -1 := by omega
    exact_mod_cast this
  have hS0 : S ≠ ∅ := by
    rintro rfl
    rw [hf0] at hS
    omega
  have hSu : S ≠ Finset.univ := by
    rintro rfl
    omega
  have hcard : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
  have hcardn : (S.card : ℝ) ≤ n := by
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hcpos : (0 : ℝ) < S.card := by exact_mod_cast hcard
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / √(S.card : ℝ) := ⟨_, rfl⟩
  have hsq : 0 < √(S.card : ℝ) := Real.sqrt_pos.mpr hcpos
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcn : 1 / √(n : ℝ) ≤ c := by
    rw [hc]
    exact one_div_le_one_div_of_le hsq (Real.sqrt_le_sqrt hcardn)
  have hc2 : c ^ 2 * S.card = 1 := by
    rw [hc, div_pow, Real.sq_sqrt hcpos.le, one_pow, div_mul_cancel₀ _ hcpos.ne']
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℝ, w = fun v => if v ∈ S then -c else 0 := ⟨_, rfl⟩
  have hdot : ∀ y : Fin n → ℝ, y ⬝ᵥ w = -c * xsum y S := by
    intro y
    have h1 : ∀ v, y v * w v = if v ∈ S then -c * y v else 0 := by
      intro v
      simp only [hw]
      split_ifs <;> ring
    unfold dotProduct xsum
    rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.mul_sum]
  have hmemS : ∀ y ∈ baseB (enlarge (fR f) (μ : ℝ)), xsum y S ≤ -1 := by
    intro y hy
    have h0 := hy.1 S
    rw [enl_mid _ _ S hS0 hSu] at h0
    have h' : xsum y S ≤ (f S : ℝ) + μ := h0
    linarith
  have hwF : w ∈ Fmu (fR f) (μ : ℝ) := by
    refine ⟨fun y hy => ?_, ?_⟩
    · rw [dotProduct_comm, hdot]
      have := hmemS y hy
      nlinarith
    · show norm2 w ≤ 1
      unfold norm2
      rw [Real.sqrt_le_left zero_le_one]
      have h1 : ∀ v, w v ^ 2 = if v ∈ S then c ^ 2 else 0 := by
        intro v
        simp only [hw]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
      nlinarith [hc2]
  intro x hx
  have h1 := width_ge (Fmu (fR f) (μ : ℝ)) x w hwF (fun z hz => hz.2)
  rw [hdot] at h1
  have := hmemS x hx
  nlinarith

end Aux_GeomRescale_lemma_3_8

open GeomRescale Aux_GeomRescale_lemma_3_8 in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f)) (hf0 : f ∅ = 0)
    (μ : ℤ) (hmin : ∃ S, f S < -μ) (hμ : -μ ≤ min 0 (f Finset.univ)) :
    (∀ x ∈ baseB (enlarge (fR f) (μ : ℝ)), 1 / √(n : ℝ) ≤ width (Fmu (fR f) (μ : ℝ)) x) ∧
      1 / (4 * (n : ℝ) * Ltwo (fR f)) ≤ omega (fR f) (μ : ℝ) := by
  have hP1 := part1 f hsub hf0 μ hmin hμ
  refine ⟨hP1, ?_⟩
  have hf0' : fR f ∅ = 0 := by
    simp [fR, hf0]
  have hμ' := le_min_iff.mp hμ
  have hμR : max 0 (-fR f Finset.univ) ≤ (μ : ℝ) := by
    show max 0 (-((f Finset.univ : ℤ) : ℝ)) ≤ (μ : ℝ)
    have h1 : (0 : ℝ) ≤ μ := by exact_mod_cast (show (0 : ℤ) ≤ μ by omega)
    have h2 : -(f Finset.univ : ℝ) ≤ μ := by
      exact_mod_cast (show -f Finset.univ ≤ μ by omega)
    exact max_le h1 h2
  have hgs := enlarge_sub (fR f) hsub hf0' (μ : ℝ) hμR
  have hg0 := enl_empty (fR f) (μ : ℝ)
  obtain ⟨S, hS⟩ := hmin
  have hμL : (μ : ℝ) ≤ Lone (fR f) := by
    have h1 : |(f S : ℝ)| ≤ Lone (fR f) := abs_f_le_Lone (fR f) hsub hf0' S
    have h2 : (μ : ℝ) ≤ -(f S : ℝ) := by exact_mod_cast (show μ ≤ -f S by omega)
    have h3 := neg_le_abs (f S : ℝ)
    linarith
  have hS1 : (f S : ℝ) + μ ≤ -1 := by
    have : f S + μ ≤ -1 := by omega
    exact_mod_cast this
  have hS0 : S ≠ ∅ := by
    rintro rfl
    rw [hf0] at hS
    omega
  have hSu : S ≠ Finset.univ := by
    rintro rfl
    omega
  have hne0 : ∀ x ∈ baseB (enlarge (fR f) (μ : ℝ)), x ≠ 0 := by
    intro x hx hx0
    have h1 : xsum x S = 0 := by
      rw [hx0]
      simp [xsum]
    have h2 := hx.1 S
    rw [enl_mid _ _ S hS0 hSu, h1] at h2
    have h3 : (0 : ℝ) ≤ (f S : ℝ) + μ := h2
    linarith
  have hL12 := Lone_le_sqrt_Ltwo (fR f) hsub hf0'
  have hL2 := Ltwo_nonneg (fR f) hsub hf0'
  unfold GeomRescale.omega
  apply le_csInf
  · obtain ⟨x, hx⟩ := baseB_nonempty _ hgs hg0
    exact ⟨_, x, ⟨hx, hne0 x hx⟩, rfl⟩
  · rintro _ ⟨x, ⟨hx, hx0⟩, rfl⟩
    have hW := hP1 x hx
    have hNpos := norm2_pos (hne0 x hx)
    have hN1 := norm1_enl_le (fR f) hsub hf0' (μ : ℝ) hμR hμL hx
    have hN : norm2 x ≤ 4 * √(n : ℝ) * Ltwo (fR f) := by
      have := norm2_le_norm1 x
      nlinarith
    have hprod : 0 < √(n : ℝ) * Ltwo (fR f) := by nlinarith
    have hsn : 0 < √(n : ℝ) := by
      rcases lt_or_eq_of_le (Real.sqrt_nonneg (n : ℝ)) with h | h
      · exact h
      · rw [← h, zero_mul] at hprod
        exact absurd hprod (lt_irrefl _)
    have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hkey : √(n : ℝ) * norm2 x ≤ 4 * (n : ℝ) * Ltwo (fR f) := by
      have h1 := mul_le_mul_of_nonneg_left hN hsn.le
      have h2 : √(n : ℝ) * (4 * √(n : ℝ) * Ltwo (fR f)) = 4 * (n : ℝ) * Ltwo (fR f) := by
        calc √(n : ℝ) * (4 * √(n : ℝ) * Ltwo (fR f))
            = 4 * (√(n : ℝ) * √(n : ℝ)) * Ltwo (fR f) := by ring
          _ = 4 * (n : ℝ) * Ltwo (fR f) := by rw [hsq]
      linarith
    calc 1 / (4 * (n : ℝ) * Ltwo (fR f)) ≤ 1 / (√(n : ℝ) * norm2 x) :=
          one_div_le_one_div_of_le (mul_pos hsn hNpos) hkey
      _ = 1 / √(n : ℝ) / norm2 x := (div_div _ _ _).symm
      _ ≤ width (Fmu (fR f) (μ : ℝ)) x / norm2 x := div_le_div_of_nonneg_right hW hNpos.le

