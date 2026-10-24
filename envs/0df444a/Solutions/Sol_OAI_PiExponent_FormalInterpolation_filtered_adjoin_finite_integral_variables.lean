-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.filtered_adjoin_finite_integral_variables
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:34:04.273678+00:00
-- url     : https://prove2.me/submissions/e1de199d-65cd-49e9-b493-aafca7f8f253

import Mathlib

section

open MvPolynomial

namespace PiL32

variable {σ : Type} [Fintype σ] [DecidableEq σ]

def LowW (W : σ → ℕ) (f : MvPolynomial σ ℂ) (k : ℕ) : Prop :=
  ∀ c ∈ f.support, Finsupp.weight W c < k

def LeW (W : σ → ℕ) (f : MvPolynomial σ ℂ) (k : ℕ) : Prop :=
  ∀ c ∈ f.support, Finsupp.weight W c ≤ k

variable (W : σ → ℕ)

lemma le_mul {f g : MvPolynomial σ ℂ} {k l : ℕ} (hf : LeW W f k) (hg : LeW W g l) : LeW W (f * g) (k + l) := by
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f g hc)
  rw [map_add]; exact add_le_add (hf a ha) (hg b hb)

lemma low_mul_le {f g : MvPolynomial σ ℂ} {k l : ℕ} (hf : LowW W f k) (hg : LeW W g l) :
    LowW W (f * g) (k + l) := by
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f g hc)
  rw [map_add]; exact add_lt_add_of_lt_of_le (hf a ha) (hg b hb)

lemma le_mul_low {f g : MvPolynomial σ ℂ} {k l : ℕ} (hf : LeW W f k) (hg : LowW W g l) :
    LowW W (f * g) (k + l) := by
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f g hc)
  rw [map_add]; exact add_lt_add_of_le_of_lt (hf a ha) (hg b hb)

lemma low_add {f g : MvPolynomial σ ℂ} {k : ℕ} (hf : LowW W f k) (hg : LowW W g k) : LowW W (f + g) k := by
  intro c hc
  rcases Finset.mem_union.1 (support_add hc) with h | h
  · exact hf c h
  · exact hg c h

lemma low_neg {f : MvPolynomial σ ℂ} {k : ℕ} (hf : LowW W f k) : LowW W (-f) k := by
  intro c hc; rw [support_neg] at hc; exact hf c hc

lemma low_sub {f g : MvPolynomial σ ℂ} {k : ℕ} (hf : LowW W f k) (hg : LowW W g k) : LowW W (f - g) k := by
  rw [sub_eq_add_neg]; exact low_add W hf (low_neg W hg)

lemma low_zero (k : ℕ) : LowW W (0 : MvPolynomial σ ℂ) k := by intro c hc; simp at hc

lemma low_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ) (k : ℕ)
    (hf : ∀ i ∈ s, LowW W (f i) k) : LowW W (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using low_zero W k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact low_add W (hf a (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma low_C_mul {f : MvPolynomial σ ℂ} {k : ℕ} (hf : LowW W f k) (a : ℂ) : LowW W (C a * f) k := by
  intro c hc
  rw [C_mul'] at hc
  exact hf c (support_smul hc)

lemma le_of_hom {f : MvPolynomial σ ℂ} {k : ℕ} (hf : IsWeightedHomogeneous W f k) : LeW W f k := by
  intro c hc
  exact le_of_eq (hf (mem_support_iff.1 hc))

lemma le_one : LeW W (1 : MvPolynomial σ ℂ) 0 := by
  intro c hc
  rw [show (1 : MvPolynomial σ ℂ) = monomial 0 1 from rfl] at hc
  have := support_monomial_subset hc
  rw [Finset.mem_singleton] at this
  simp [this]

lemma le_pow {f : MvPolynomial σ ℂ} {k : ℕ} (hf : LeW W f k) (n : ℕ) : LeW W (f ^ n) (n * k) := by
  induction n with
  | zero => simpa using le_one W
  | succ n ih =>
    rw [pow_succ, show (n + 1) * k = n * k + k by ring]
    exact le_mul W ih hf

variable {m : ℕ}

/-- difference of powers -/
lemma pow_diff (g h : Fin m → MvPolynomial σ ℂ) (D : ℕ)
    (hg : ∀ j, LeW W (g j) D) (hh : ∀ j, LeW W (h j) D) (hgh : ∀ j, LowW W (g j - h j) D)
    (j : Fin m) (n : ℕ) : LowW W (g j ^ n - h j ^ n) (n * D) ∧ LeW W (g j ^ n) (n * D) ∧
      LeW W (h j ^ n) (n * D) := by
  induction n with
  | zero =>
    simp only [pow_zero, sub_self, zero_mul]
    exact ⟨low_zero W 0, le_one W, le_one W⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · have e : g j ^ (n + 1) - h j ^ (n + 1) = g j ^ n * (g j - h j) + (g j ^ n - h j ^ n) * h j := by ring
      rw [e, show (n + 1) * D = n * D + D by ring]
      exact low_add W (le_mul_low W h2 (hgh j)) (low_mul_le W h1 (hh j))
    · rw [pow_succ, show (n + 1) * D = n * D + D by ring]; exact le_mul W h2 (hg j)
    · rw [pow_succ, show (n + 1) * D = n * D + D by ring]; exact le_mul W h3 (hh j)

lemma prod_diff (g h : Fin m → MvPolynomial σ ℂ) (D : ℕ)
    (hg : ∀ j, LeW W (g j) D) (hh : ∀ j, LeW W (h j) D) (hgh : ∀ j, LowW W (g j - h j) D)
    (α : Fin m → ℕ) (s : Finset (Fin m)) :
    LowW W (∏ j ∈ s, g j ^ α j - ∏ j ∈ s, h j ^ α j) (∑ j ∈ s, α j * D) ∧
      LeW W (∏ j ∈ s, g j ^ α j) (∑ j ∈ s, α j * D) ∧ LeW W (∏ j ∈ s, h j ^ α j) (∑ j ∈ s, α j * D) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, sub_self]
    exact ⟨low_zero W 0, le_one W, le_one W⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨p1, p2, p3⟩ := pow_diff W g h D hg hh hgh a (α a)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨?_, le_mul W p2 h2, le_mul W p3 h3⟩
    have e : g a ^ α a * ∏ j ∈ s, g j ^ α j - h a ^ α a * ∏ j ∈ s, h j ^ α j =
        g a ^ α a * (∏ j ∈ s, g j ^ α j - ∏ j ∈ s, h j ^ α j) +
          (g a ^ α a - h a ^ α a) * ∏ j ∈ s, h j ^ α j := by ring
    rw [e]
    exact low_add W (le_mul_low W p2 h1) (low_mul_le W p1 h3)

lemma weight_const (D : ℕ) (α : Fin m →₀ ℕ) :
    Finsupp.weight (fun _ : Fin m => D) α = ∑ j, α j * D := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [smul_eq_mul]

lemma aeval_monomial_eq (f : Fin m → MvPolynomial σ ℂ) (α : Fin m →₀ ℕ) (c : ℂ) :
    aeval f (monomial α c) = C c * ∏ j, f j ^ α j := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  rfl

lemma diff_low (g h : Fin m → MvPolynomial σ ℂ) (D : ℕ)
    (hg : ∀ j, LeW W (g j) D) (hh : ∀ j, LeW W (h j) D) (hgh : ∀ j, LowW W (g j - h j) D)
    (q : MvPolynomial (Fin m) ℂ) (k : ℕ) (hq : IsWeightedHomogeneous (fun _ => D) q k) :
    LowW W (aeval g q - aeval h q) k := by
  conv => arg 2; rw [q.as_sum]
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply low_sum
  intro α hα
  rw [aeval_monomial_eq, aeval_monomial_eq, ← mul_sub]
  apply low_C_mul
  have hk : ∑ j, α j * D = k := by
    rw [← weight_const]; exact hq (mem_support_iff.1 hα)
  rw [← hk]
  exact (prod_diff W g h D hg hh hgh α Finset.univ).1

lemma hom_aeval (h : Fin m → MvPolynomial σ ℂ) (D : ℕ) (hh : ∀ j, IsWeightedHomogeneous W (h j) D)
    (α : Fin m →₀ ℕ) (c : ℂ) :
    IsWeightedHomogeneous W (aeval h (monomial α c)) (Finsupp.weight (fun _ : Fin m => D) α) := by
  rw [aeval_monomial_eq, weight_const]
  apply IsWeightedHomogeneous.C_mul
  exact IsWeightedHomogeneous.prod _ _ _ fun j _ => by
    simpa [mul_comm] using (hh j).pow (α j)

/-- extraction of the degree-`n` component -/
lemma comp_extract (h : Fin m → MvPolynomial σ ℂ) (D : ℕ) (hh : ∀ j, IsWeightedHomogeneous W (h j) D)
    (b : σ →₀ ℕ) (n : ℕ) (p : MvPolynomial (Fin m) ℂ) :
    weightedHomogeneousComponent W n (aeval h p * monomial b 1) =
      aeval h (if Finsupp.weight W b ≤ n then
        weightedHomogeneousComponent (fun _ => D) (n - Finsupp.weight W b) p else 0) * monomial b 1 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    have hom := (hom_aeval W h D hh α c).mul (isWeightedHomogeneous_monomial W b (1 : ℂ) rfl)
    have hmon := isWeightedHomogeneous_monomial (fun _ : Fin m => D) α c
      (rfl : Finsupp.weight (fun _ : Fin m => D) α = Finsupp.weight (fun _ : Fin m => D) α)
    by_cases hn : Finsupp.weight (fun _ : Fin m => D) α + Finsupp.weight W b = n
    · rw [← hn, hom.weightedHomogeneousComponent_same, if_pos (by omega),
        show Finsupp.weight (fun _ : Fin m => D) α + Finsupp.weight W b - Finsupp.weight W b =
          Finsupp.weight (fun _ : Fin m => D) α by omega,
        hmon.weightedHomogeneousComponent_same]
    · rw [hom.weightedHomogeneousComponent_ne n (fun e => hn e.symm)]
      split_ifs with hb
      · rw [hmon.weightedHomogeneousComponent_ne _ (by omega)]; simp
      · simp
  | add p q hp hq =>
    rw [map_add, add_mul, map_add, hp, hq]
    split_ifs <;> simp [map_add, add_mul]

theorem core (W : σ → ℕ) (D : ℕ) (g : Fin m → MvPolynomial σ ℂ)
    (hbound : ∀ j, LeW W (g j) D)
    (h' : Fin m → MvPolynomial σ ℂ) (hh' : ∀ j, h' j = weightedHomogeneousComponent W D (g j))
    (hfinite : Module.Finite (Algebra.adjoin ℂ (Set.range h')) (MvPolynomial σ ℂ)) :
    Module.Finite (Algebra.adjoin ℂ (Set.range g)) (MvPolynomial σ ℂ) := by
  classical
  obtain rfl : h' = fun j => weightedHomogeneousComponent W D (g j) := funext hh'
  set h : Fin m → MvPolynomial σ ℂ := fun j => weightedHomogeneousComponent W D (g j) with h_def
  set Ah := Algebra.adjoin ℂ (Set.range h)
  set Ag := Algebra.adjoin ℂ (Set.range g)
  have hh : ∀ j, IsWeightedHomogeneous W (h j) D := fun j => weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hhle : ∀ j, LeW W (h j) D := fun j => le_of_hom W (hh j)
  have hgh : ∀ j, LowW W (g j - h j) D := by
    intro j c hc
    rw [mem_support_iff, coeff_sub, h_def] at hc
    simp only [coeff_weightedHomogeneousComponent] at hc
    split_ifs at hc with hcD
    · simp at hc
    · have hc' : c ∈ (g j).support := by rw [mem_support_iff]; simpa using hc
      exact lt_of_le_of_ne (hbound j c hc') hcD
  -- finite generating set of monomials over Ah
  obtain ⟨S, hS⟩ := (Module.finite_def.1 hfinite)
  set B := S.biUnion (fun s => s.support)
  let mon : B → MvPolynomial σ ℂ := fun b => monomial (b : σ →₀ ℕ) 1
  have hB : ∀ x : MvPolynomial σ ℂ, x ∈ Submodule.span Ah (Set.range mon) := by
    intro x
    have hx : x ∈ Submodule.span Ah (S : Set (MvPolynomial σ ℂ)) := hS ▸ Submodule.mem_top
    refine (Submodule.span_le.2 ?_) hx
    intro s hs
    rw [SetLike.mem_coe, s.as_sum]
    refine Submodule.sum_mem _ fun c hc => ?_
    have hcB : c ∈ B := Finset.mem_biUnion.2 ⟨s, hs, hc⟩
    rw [show monomial c (coeff c s) = coeff c s • mon ⟨c, hcB⟩ by simp [mon, smul_monomial]]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨⟨c, hcB⟩, rfl⟩)
  set N := Submodule.span Ag (Set.range mon)
  have hmain : ∀ n : ℕ, ∀ a : σ →₀ ℕ, Finsupp.weight W a = n → monomial a (1 : ℂ) ∈ N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro a ha
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun Ah).1 (hB (monomial a 1))
    have hp : ∀ b, ∃ p : MvPolynomial (Fin m) ℂ, aeval h p = (cf b : MvPolynomial σ ℂ) := by
      intro b
      have h2 : ((cf b : Ah) : MvPolynomial σ ℂ) ∈ Algebra.adjoin ℂ (Set.range h) := (cf b).2
      rw [Algebra.adjoin_range_eq_range_aeval] at h2
      exact h2
    choose p hp using hp
    set q : B → MvPolynomial (Fin m) ℂ := fun b => if Finsupp.weight W (b : σ →₀ ℕ) ≤ n then
        weightedHomogeneousComponent (fun _ => D) (n - Finsupp.weight W (b : σ →₀ ℕ)) (p b) else 0
    have hsum : monomial a (1 : ℂ) = ∑ b, aeval h (p b) * mon b := by
      rw [← hcf]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, hp, smul_eq_mul]
    have hsum2 : monomial a (1 : ℂ) = ∑ b, aeval h (q b) * mon b := by
      have := congrArg (weightedHomogeneousComponent W n) hsum
      rw [(isWeightedHomogeneous_monomial W a (1 : ℂ) ha).weightedHomogeneousComponent_same, map_sum] at this
      rw [this]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact comp_extract W h D hh b n (p b)
    have hsplit : monomial a (1 : ℂ) = ∑ b, aeval g (q b) * mon b - ∑ b, (aeval g (q b) - aeval h (q b)) * mon b := by
      rw [hsum2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [hsplit]
    refine Submodule.sub_mem _ ?_ ?_
    · refine Submodule.sum_mem _ fun b _ => ?_
      have hmem : aeval g (q b) ∈ Ag := by
        rw [show Ag = (aeval g).range from Algebra.adjoin_range_eq_range_aeval ℂ g]; exact ⟨q b, rfl⟩
      rw [show aeval g (q b) * mon b = (⟨aeval g (q b), hmem⟩ : Ag) • mon b from rfl]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    · set E := ∑ b, (aeval g (q b) - aeval h (q b)) * mon b
      have hlow : LowW W E n := by
        apply low_sum
        intro b _
        by_cases hb : Finsupp.weight W (b : σ →₀ ℕ) ≤ n
        · have hq : IsWeightedHomogeneous (fun _ => D) (q b) (n - Finsupp.weight W (b : σ →₀ ℕ)) := by
            simp only [q, if_pos hb]
            exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
          have := low_mul_le W (diff_low W g h D hbound hhle hgh _ _ hq)
            (le_of_hom W (isWeightedHomogeneous_monomial W (b : σ →₀ ℕ) (1 : ℂ) rfl))
          rwa [Nat.sub_add_cancel hb] at this
        · simp only [q, if_neg hb, map_zero, sub_zero, zero_mul]
          exact low_zero W n
      rw [E.as_sum]
      refine Submodule.sum_mem _ fun c hc => ?_
      have hc' := ih _ (hlow c hc) c rfl
      rw [show monomial c (coeff c E) = coeff c E • monomial c (1 : ℂ) by simp [smul_monomial]]
      exact Submodule.smul_of_tower_mem _ _ hc'
  have hN : N = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [x.as_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [show monomial c (coeff c x) = coeff c x • monomial c (1 : ℂ) by simp [smul_monomial]]
    exact Submodule.smul_of_tower_mem _ _ (hmain _ c rfl)
  refine Module.finite_def.2 ⟨Finset.univ.image mon, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact hN

end PiL32

end

section

open MvPolynomial

namespace PiL33

lemma int_weights {d : ℕ} (w : Fin d → ℚ) (hw : ∀ i, 0 < w i) :
    ∃ L : ℕ, 0 < L ∧ ∃ W : Fin d → ℕ, ∀ k, (W k : ℚ) = L * w k := by
  refine ⟨∏ k, (w k).den, Finset.prod_pos fun k _ => (w k).den_pos, ?_⟩
  have : ∀ k, ∃ n : ℕ, (n : ℚ) = (∏ k, (w k).den : ℕ) * w k := by
    intro k
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem (fun k => (w k).den) (Finset.mem_univ k)
    have hnum : 0 < (w k).num := Rat.num_pos.2 (hw k)
    refine ⟨(w k).num.toNat * t, ?_⟩
    rw [ht]
    push_cast
    rw [show ((w k).num.toNat : ℚ) = ((w k).num : ℚ) by exact_mod_cast Int.toNat_of_nonneg hnum.le]
    rw [← Rat.mul_den_eq_num]
    ring
  choose W hW using this
  exact ⟨W, hW⟩

theorem filtered {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hbound : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (hfinite : Module.Finite
      (Algebra.adjoin Complex
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j))))
      (MvPolynomial (Fin d) Complex)) :
    Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex) := by
  classical
  have hwq : ∀ i, 0 < w i := fun i => by exact_mod_cast hw i
  obtain ⟨L, hL, W, hW⟩ := int_weights w hwq
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have hwt : ∀ c : Fin d →₀ ℕ, (Finsupp.weight W c : ℚ) = L * Finsupp.weight (fun k => (w k : ℚ)) c := by
    intro c
    rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.sum_fintype _ _ (by simp)]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [nsmul_eq_mul]
    rw [Nat.cast_mul, hW k]
    push_cast
    ring
  have hcomp : ∀ f : MvPolynomial (Fin d) ℂ,
      weightedHomogeneousComponent (fun k => (w k : ℚ)) (D : ℚ) f = weightedHomogeneousComponent W (L * D) f := by
    intro f
    ext c
    rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
    have : Finsupp.weight (fun k => (w k : ℚ)) c = (D : ℚ) ↔ Finsupp.weight W c = L * D := by
      rw [← Nat.cast_inj (R := ℚ), hwt]
      push_cast
      constructor
      · intro h; rw [h]
      · intro h; exact mul_left_cancel₀ hLq h
    by_cases h1 : Finsupp.weight (fun k => (w k : ℚ)) c = (D : ℚ)
    · rw [if_pos h1, if_pos (this.1 h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (this.2 h))]
  refine PiL32.core W (L * D) g (fun j c hc => ?_) _ (fun j => hcomp (g j)) hfinite
  have h1 := hbound j c hc
  have h2 : (Finsupp.weight W c : ℝ) = L * ∑ k, (w k : ℝ) * (c k : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (hwt c)
    rw [show ((Finsupp.weight W c : ℕ) : ℝ) = (((Finsupp.weight W c : ℕ) : ℚ) : ℝ) by push_cast; rfl, this]
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    push_cast
    simp only [nsmul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by push_cast; ring
  have h3 : (Finsupp.weight W c : ℝ) ≤ ((L * D : ℕ) : ℝ) := by
    rw [h2]; push_cast
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  exact_mod_cast h3

end PiL33

namespace PiL33b

theorem integral_vars {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hbound : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (hfinite : Module.Finite
      (Algebra.adjoin Complex
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k : Fin d => (w k : ℚ)) (D : ℚ) (g j))))
      (MvPolynomial (Fin d) Complex)) :
    ∀ i : Fin d, IsIntegral (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial.X (R := Complex) i) := by
  intro i
  haveI := PiL33.filtered w hw D hD m g hbound hfinite
  exact Algebra.IsIntegral.isIntegral _

end PiL33b

end


open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hbound : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (hfinite : Module.Finite
      (Algebra.adjoin Complex
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k : Fin d => (w k : ℚ)) (D : ℚ) (g j))))
      (MvPolynomial (Fin d) Complex)) :
    ∀ i : Fin d, IsIntegral (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial.X (R := Complex) i) := by
  apply PiL33b.integral_vars <;> assumption
