-- Prove2me | solution 1 for MultiwayCut.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:28:03.886555+00:00
-- url     : https://prove2.me/submissions/c68caaca-3eb4-4481-82c0-96a3174d7204

import Mathlib
import Definitions.Def_MultiwayCut_Transformation

open Matrix

namespace Aux_MultiwayCut_lemma_5_1

open MultiwayCut

/-- Abel summation: an antitone nonnegative weight against a sequence with nonnegative prefix
sums gives a nonnegative sum. -/
theorem abel_nonneg (g : ℕ → ℝ) : ∀ (n : ℕ) (f : ℕ → ℝ),
    (∀ i j, i ≤ j → j < n → f j ≤ f i) → (0 < n → 0 ≤ f (n - 1)) →
    (∀ r, 1 ≤ r → r ≤ n → 0 ≤ ∑ i ∈ Finset.range r, g i) →
    0 ≤ ∑ i ∈ Finset.range n, f i * g i := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro f hmono hlast hpre
    have hfn : 0 ≤ f n := by simpa using hlast (Nat.succ_pos n)
    have key : ∑ i ∈ Finset.range (n + 1), f i * g i =
        ∑ i ∈ Finset.range n, (f i - f n) * g i + f n * ∑ i ∈ Finset.range (n + 1), g i := by
      rw [Finset.mul_sum, Finset.sum_range_succ, Finset.sum_range_succ (fun i => f n * g i)]
      have : ∑ i ∈ Finset.range n, f i * g i =
          ∑ i ∈ Finset.range n, ((f i - f n) * g i + f n * g i) := by
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [this, Finset.sum_add_distrib]
      ring
    rw [key]
    have h1 : 0 ≤ ∑ i ∈ Finset.range n, (f i - f n) * g i := by
      apply ih (fun i => f i - f n)
      · intro i j hij hjn
        have := hmono i j hij (by omega)
        show f j - f n ≤ f i - f n
        linarith
      · intro hn
        have := hmono (n - 1) n (by omega) (by omega)
        show 0 ≤ f (n - 1) - f n
        linarith
      · intro r h1 h2
        exact hpre r h1 (by omega)
    have h2 : 0 ≤ ∑ i ∈ Finset.range (n + 1), g i := hpre (n + 1) (by omega) le_rfl
    have h3 := mul_nonneg hfn h2
    linarith

/-- Extension of a `Fin k`-indexed vector by zero. -/
noncomputable def ext {k : ℕ} (a : Fin k → ℝ) (n : ℕ) : ℝ := if h : n < k then a ⟨n, h⟩ else 0

theorem ext_val {k : ℕ} (a : Fin k → ℝ) (i : Fin k) : ext a i.val = a i := by
  simp [ext, i.isLt]

theorem univ_conv {k : ℕ} (a : Fin k → ℝ) :
    ∑ i : Fin k, a i = ∑ n ∈ Finset.range k, ext a n := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => (ext_val a i).symm)

theorem Iic_conv {k : ℕ} (a : Fin k → ℝ) (ℓ : Fin k) :
    ∑ i ∈ Finset.Iic ℓ, a i = ∑ n ∈ Finset.range (ℓ.val + 1), ext a n := by
  refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Iic] at hi
    show i.val ∈ Finset.range (ℓ.val + 1)
    rw [Finset.mem_range]
    have := Fin.le_def.mp hi
    omega
  · intro a₁ _ a₂ _ h
    exact Fin.ext h
  · intro n hn
    rw [Finset.mem_range] at hn
    refine ⟨⟨n, by have := ℓ.isLt; omega⟩, ?_, rfl⟩
    rw [Finset.mem_Iic, Fin.le_def]
    show n ≤ ℓ.val
    omega
  · intro i _
    exact (ext_val a i).symm

theorem P_lt {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hcond : Lemma51Conditions A)
    (ℓ r : Fin k) (h : ℓ ≤ r) : 0 ≤ ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic r, A i j := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact hcond.2.1 _
  · have hsplit : ∀ i, ∑ j ∈ Finset.Iic r, A i j =
        ∑ j ∈ Finset.Iic ℓ, A i j + ∑ j ∈ Finset.Ioc ℓ r, A i j := by
      intro i
      rw [← Finset.sum_union, Finset.Iic_union_Ioc_eq_Iic (le_of_lt h)]
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_Iic] at hx
      rw [Finset.mem_Ioc] at hx'
      exact absurd hx'.1 (not_lt.mpr hx)
    simp_rw [hsplit, Finset.sum_add_distrib]
    exact add_nonneg (hcond.2.1 ℓ) (hcond.2.2 ℓ r h)

theorem P_nonneg {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hcond : Lemma51Conditions A) (ℓ r : Fin k) :
    0 ≤ ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic r, A i j := by
  rcases le_total ℓ r with h | h
  · exact P_lt A hcond ℓ r h
  · rw [show (∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic r, A i j) =
        ∑ j ∈ Finset.Iic r, ∑ i ∈ Finset.Iic ℓ, A i j from Finset.sum_comm]
    have : ∑ y ∈ Finset.Iic r, ∑ x ∈ Finset.Iic ℓ, A x y =
        ∑ y ∈ Finset.Iic r, ∑ x ∈ Finset.Iic ℓ, A y x := by
      refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
      exact hA.apply y x
    rw [this]
    exact P_lt A hcond r ℓ h

/-- The bilinear form is nonnegative on antitone nonnegative vectors. -/
theorem B_nonneg {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hcond : Lemma51Conditions A) (t t' : Fin k → ℝ) (ht : Antitone t) (ht0 : ∀ m, 0 ≤ t m)
    (ht' : Antitone t') (ht'0 : ∀ m, 0 ≤ t' m) : 0 ≤ t ⬝ᵥ (A *ᵥ t') := by
  have hmono : ∀ (a : Fin k → ℝ), Antitone a →
      ∀ i j, i ≤ j → j < k → ext a j ≤ ext a i := by
    intro a ha i j hij hjk
    have hik : i < k := by omega
    simp only [ext, dif_pos hjk, dif_pos hik]
    exact ha (Fin.le_def.mpr hij)
  have hlast : ∀ (a : Fin k → ℝ), (∀ m, 0 ≤ a m) → 0 < k → 0 ≤ ext a (k - 1) := by
    intro a ha hk
    simp only [ext, dif_pos (show k - 1 < k by omega)]
    exact ha _
  have hdot : t ⬝ᵥ (A *ᵥ t') = ∑ n ∈ Finset.range k, ext t n * ext (A *ᵥ t') n := by
    rw [dotProduct, univ_conv]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hn : n < k
    · simp only [ext, dif_pos hn]
    · simp only [ext, dif_neg hn, mul_zero]
  rw [hdot]
  apply abel_nonneg _ k _ (hmono t ht) (hlast t ht0)
  intro r hr1 hrk
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin k, ℓ.val + 1 = r :=
    ⟨⟨r - 1, by omega⟩, by show r - 1 + 1 = r; omega⟩
  rw [← hℓ, ← Iic_conv]
  have hsw : ∑ i ∈ Finset.Iic ℓ, (A *ᵥ t') i =
      ∑ j : Fin k, t' j * ∑ i ∈ Finset.Iic ℓ, A i j := by
    simp only [mulVec, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsw, univ_conv]
  have hprod : ∀ n, ext (fun j => t' j * ∑ i ∈ Finset.Iic ℓ, A i j) n =
      ext t' n * ext (fun j => ∑ i ∈ Finset.Iic ℓ, A i j) n := by
    intro n
    by_cases hn : n < k
    · simp only [ext, dif_pos hn]
    · simp only [ext, dif_neg hn, mul_zero]
  simp_rw [hprod]
  apply abel_nonneg _ k _ (hmono t' ht') (hlast t' ht'0)
  intro s hs1 hsk
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin k, ℓ'.val + 1 = s :=
    ⟨⟨s - 1, by omega⟩, by show s - 1 + 1 = s; omega⟩
  rw [← hℓ', ← Iic_conv, Finset.sum_comm]
  exact P_nonneg A hA hcond ℓ ℓ'

theorem sym_form {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm) (v w : Fin k → ℝ) :
    v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ v) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [hA.apply j i]
  ring

theorem sorted_anti {k : ℕ} (u : Fin k → ℝ) : Antitone (u ∘ sortPerm u) := by
  intro a b hab
  have := Tuple.monotone_sort (-u) hab
  simp only [Function.comp_apply, Pi.neg_apply] at this
  show u (sortPerm u b) ≤ u (sortPerm u a)
  unfold sortPerm
  linarith

theorem flat_anti {k : ℕ} (s : Fin k → ℝ) (hs : Antitone s) (ℓ : Fin k) :
    Antitone (flat s ℓ) := by
  intro a b hab
  simp only [flat]
  by_cases ha : a < ℓ
  · by_cases hb : b < ℓ
    · simp only [if_pos ha, if_pos hb, le_refl]
    · simp only [if_pos ha, if_neg hb]
      exact hs (not_lt.mp hb)
  · have hb : ¬ b < ℓ := fun hb => ha (lt_of_le_of_lt hab hb)
    simp only [if_neg ha, if_neg hb]
    exact hs hab

theorem flat_nonneg {k : ℕ} (s : Fin k → ℝ) (hs : ∀ m, 0 ≤ s m) (ℓ : Fin k) :
    ∀ m, 0 ≤ flat s ℓ m := by
  intro m
  simp only [flat]
  split_ifs
  · exact hs ℓ
  · exact hs m

theorem flat_le {k : ℕ} (s : Fin k → ℝ) (hs : Antitone s) (ℓ : Fin k) :
    ∀ m, flat s ℓ m ≤ s m := by
  intro m
  simp only [flat]
  split_ifs with h
  · exact hs (le_of_lt h)
  · exact le_refl _

theorem flat_flat {k : ℕ} (s : Fin k → ℝ) (ℓ ℓ' : Fin k) (h : ℓ ≤ ℓ') :
    flat (flat s ℓ) ℓ' = flat s ℓ' := by
  funext m
  simp only [flat]
  by_cases hm : m < ℓ'
  · simp only [if_pos hm, if_neg (not_lt.mpr h)]
  · have : ¬ m < ℓ := fun h' => hm (lt_of_lt_of_le h' h)
    simp only [if_neg hm, if_neg this]

theorem diff_anti {k : ℕ} (t : Fin k → ℝ) (ht : Antitone t) (ℓ : Fin k) :
    Antitone (t - flat t ℓ) := by
  intro a b hab
  simp only [Pi.sub_apply, flat]
  by_cases ha : a < ℓ
  · by_cases hb : b < ℓ
    · simp only [if_pos ha, if_pos hb]
      linarith [ht hab]
    · simp only [if_pos ha, if_neg hb]
      linarith [ht (le_of_lt ha)]
  · have hb : ¬ b < ℓ := fun hb => ha (lt_of_le_of_lt hab hb)
    simp only [if_neg ha, if_neg hb, sub_self, le_refl]

theorem diff_nonneg {k : ℕ} (t : Fin k → ℝ) (ht : Antitone t) (ℓ : Fin k) :
    ∀ m, 0 ≤ (t - flat t ℓ) m := by
  intro m
  simp only [Pi.sub_apply, flat]
  split_ifs with h
  · linarith [ht (le_of_lt h)]
  · simp

theorem quad_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) (m : Fin k) :
    quadTransform A u m = flat (u ∘ sortPerm u) ((sortPerm u).symm m) ⬝ᵥ
      (A *ᵥ flat (u ∘ sortPerm u) ((sortPerm u).symm m)) := rfl

end Aux_MultiwayCut_lemma_5_1

open MultiwayCut Aux_MultiwayCut_lemma_5_1 in
theorem solution {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hcond : Lemma51Conditions A) :
    IsFeasibleTransform (quadTransform A) := by
  refine ⟨?_, ?_, ?_⟩
  · -- range
    intro u hu ℓ
    obtain ⟨hu0, hu1⟩ := hu
    have hsa := sorted_anti u
    have hs0 : ∀ m, 0 ≤ (u ∘ sortPerm u) m := fun m => hu0 _
    have hsum_s : ∑ m, (u ∘ sortPerm u) m = 1 := by
      simp only [Function.comp_apply]
      rw [Equiv.sum_comp (sortPerm u) u]
      exact hu1
    obtain ⟨π, hπ⟩ : ∃ π, π = sortPerm u := ⟨_, rfl⟩
    rw [← hπ] at hsa hs0 hsum_s
    rw [quad_eq, ← hπ]
    obtain ⟨t, ht⟩ : ∃ t, t = flat (u ∘ π) (π.symm ℓ) := ⟨_, rfl⟩
    rw [← ht]
    have hta : Antitone t := by rw [ht]; exact flat_anti _ hsa _
    have ht0 : ∀ m, 0 ≤ t m := by rw [ht]; exact flat_nonneg _ hs0 _
    have hts : ∀ m, t m ≤ (u ∘ π) m := by rw [ht]; exact flat_le _ hsa _
    have hsum_t : ∑ m, t m ≤ 1 := by
      rw [← hsum_s]
      exact Finset.sum_le_sum (fun m _ => hts m)
    have hsum_t0 : 0 ≤ ∑ m, t m := Finset.sum_nonneg (fun m _ => ht0 m)
    refine ⟨B_nonneg A hA hcond t t hta ht0 hta ht0, ?_⟩
    have hle : t ⬝ᵥ (A *ᵥ t) ≤ (∑ m, t m) * (∑ m, t m) := by
      simp only [dotProduct, mulVec]
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun i _ => ?_)
      apply mul_le_mul_of_nonneg_left _ (ht0 i)
      refine Finset.sum_le_sum (fun j _ => ?_)
      have := hcond.1.2 i j
      nlinarith [ht0 j]
    nlinarith [mul_nonneg hsum_t0 (sub_nonneg.mpr hsum_t)]
  · -- vertices
    intro i
    have hsa := sorted_anti ((Pi.single i 1 : Fin k → ℝ))
    obtain ⟨π, hπ⟩ : ∃ π, π = sortPerm ((Pi.single i 1 : Fin k → ℝ)) := ⟨_, rfl⟩
    rw [← hπ] at hsa
    have hπ0 : π 0 = i := by
      by_contra hne
      have h1 : ((Pi.single i 1 : Fin k → ℝ) ∘ π) (π.symm i) = 1 := by
        simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.single_eq_same]
      have h2 : ((Pi.single i 1 : Fin k → ℝ) ∘ π) 0 = 0 := by
        simp only [Function.comp_apply]
        exact Pi.single_eq_of_ne hne 1
      have := hsa (Fin.zero_le (π.symm i))
      linarith
    have hsval : ∀ a, (Pi.single i 1 : Fin k → ℝ) (π a) = if a = 0 then 1 else 0 := by
      intro a
      by_cases ha : a = 0
      · rw [if_pos ha, ha, hπ0, Pi.single_eq_same]
      · rw [if_neg ha]
        apply Pi.single_eq_of_ne
        intro h
        apply ha
        have : π a = π 0 := by rw [h, hπ0]
        exact π.injective this
    funext m
    rw [quad_eq, ← hπ]
    by_cases hm : m = i
    · rw [hm]
      have hl : π.symm i = 0 := by rw [Equiv.symm_apply_eq, hπ0]
      rw [hl]
      have hfl : flat ((Pi.single i 1 : Fin k → ℝ) ∘ π) 0 = Pi.single 0 1 := by
        funext a
        have ha : ¬ a < 0 := not_lt.mpr (Fin.zero_le a)
        simp only [flat, if_neg ha, Function.comp_apply, hsval, Pi.single_apply]
      rw [hfl, Pi.single_eq_same, Matrix.mulVec_single_one, single_dotProduct, one_mul]
      exact hcond.1.1
    · have hl : π.symm m ≠ 0 := by
        intro h
        apply hm
        rw [← hπ0, ← h, Equiv.apply_symm_apply]
      have hfl : flat ((Pi.single i 1 : Fin k → ℝ) ∘ π) (π.symm m) = 0 := by
        funext a
        simp only [flat, Pi.zero_apply, Function.comp_apply]
        by_cases ha : a < π.symm m
        · rw [if_pos ha, Equiv.apply_symm_apply]
          exact Pi.single_eq_of_ne hm 1
        · rw [if_neg ha, hsval]
          have : a ≠ 0 := by
            intro h
            apply ha
            rw [h]
            exact lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hl)
          rw [if_neg this]
      rw [hfl, Pi.single_eq_of_ne hm]
      simp
  · -- order preservation
    intro u hu π' hanti
    obtain ⟨hu0, _⟩ := hu
    have hsa := sorted_anti u
    have hs0 : ∀ m, 0 ≤ (u ∘ sortPerm u) m := fun m => hu0 _
    have hsv : ∀ x, (u ∘ sortPerm u) ((sortPerm u).symm x) = u x := by
      intro x
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    obtain ⟨π, hπ⟩ : ∃ π, π = sortPerm u := ⟨_, rfl⟩
    rw [← hπ] at hsa hs0 hsv
    intro p q hpq
    show quadTransform A u (π' q) ≤ quadTransform A u (π' p)
    rw [quad_eq, quad_eq, ← hπ]
    obtain ⟨a, ha⟩ : ∃ a, a = π' p := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = π' q := ⟨_, rfl⟩
    rw [← ha, ← hb]
    have hab : u b ≤ u a := by
      rw [ha, hb]
      exact hanti hpq
    by_cases heq : u a = u b
    · have e1 : (u ∘ π) (π.symm a) = (u ∘ π) (π.symm b) := by rw [hsv, hsv, heq]
      have hflat : flat (u ∘ π) (π.symm b) = flat (u ∘ π) (π.symm a) := by
        funext m
        simp only [flat]
        by_cases h1 : m < π.symm b
        · by_cases h2 : m < π.symm a
          · rw [if_pos h1, if_pos h2]
            exact e1.symm
          · rw [if_pos h1, if_neg h2]
            exact le_antisymm (hsa (le_of_lt h1)) (e1 ▸ hsa (not_lt.mp h2))
        · by_cases h2 : m < π.symm a
          · rw [if_neg h1, if_pos h2]
            exact le_antisymm (e1.symm ▸ hsa (not_lt.mp h1)) (hsa (le_of_lt h2))
          · rw [if_neg h1, if_neg h2]
      exact le_of_eq (by rw [hflat])
    · have hlt : u b < u a := lt_of_le_of_ne hab (Ne.symm heq)
      have hord : π.symm a ≤ π.symm b := by
        by_contra hc
        have := hsa (le_of_lt (not_le.mp hc))
        rw [hsv, hsv] at this
        linarith
      obtain ⟨t, ht⟩ : ∃ t, t = flat (u ∘ π) (π.symm a) := ⟨_, rfl⟩
      have hta : Antitone t := by rw [ht]; exact flat_anti _ hsa _
      have ht0 : ∀ m, 0 ≤ t m := by rw [ht]; exact flat_nonneg _ hs0 _
      have htb : flat (u ∘ π) (π.symm b) = flat t (π.symm b) := by
        rw [ht, flat_flat _ _ _ hord]
      rw [htb, ← ht]
      obtain ⟨t2, ht2⟩ : ∃ t2, t2 = flat t (π.symm b) := ⟨_, rfl⟩
      rw [← ht2]
      have ht2a : Antitone t2 := by rw [ht2]; exact flat_anti t hta _
      have ht20 : ∀ m, 0 ≤ t2 m := by rw [ht2]; exact flat_nonneg t ht0 _
      have hDa : Antitone (t - t2) := by rw [ht2]; exact diff_anti t hta _
      have hD0 : ∀ m, 0 ≤ (t - t2) m := by rw [ht2]; exact diff_nonneg t hta _
      have hD := B_nonneg A hA hcond (t - t2) (t + t2) hDa hD0 (hta.add ht2a)
        (fun m => add_nonneg (ht0 m) (ht20 m))
      have hexp : (t - t2) ⬝ᵥ (A *ᵥ (t + t2)) = t ⬝ᵥ (A *ᵥ t) - t2 ⬝ᵥ (A *ᵥ t2) := by
        rw [Matrix.mulVec_add, sub_dotProduct, dotProduct_add, dotProduct_add,
          sym_form A hA t t2]
        ring
      linarith
