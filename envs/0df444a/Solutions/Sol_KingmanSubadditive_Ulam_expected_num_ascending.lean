-- Prove2me | solution 1 for KingmanSubadditive.Ulam.expected_num_ascending
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:04:43.266234+00:00
-- url     : https://prove2.me/submissions/7e85e301-ceac-440b-ad60-f962235abf2c

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

open scoped BigOperators


namespace KingmanSubadditive.Ulam

open Finset Classical

variable {n : ℕ}

/-- permutations fixing the complement of `s` pointwise -/
def fixSet (s : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun ρ => ∀ a, a ∉ s → ρ a = a)

/-- permutations ascending on `s` -/
def ascSet (s : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun σ => IsAscendingOn σ s)

lemma card_fixSet (s : Finset (Fin n)) : (fixSet s).card = (s.card).factorial := by
  classical
  have h1 : (fixSet s).card = Fintype.card {f : Equiv.Perm (Fin n) // ∀ a, ¬ a ∈ s → f a = a} := by
    rw [Fintype.card_subtype]
    unfold fixSet
    congr 1
  rw [h1, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∈ s)),
    Fintype.card_perm, Fintype.card_coe]

/-- a permutation fixing `sᶜ` maps `s` into `s` -/
lemma fix_maps (s : Finset (Fin n)) (g : Equiv.Perm (Fin n)) (hg : ∀ a, a ∉ s → g a = a)
    {a : Fin n} (ha : a ∈ s) : g a ∈ s := by
  by_contra h
  have := hg _ h
  have h2 : g (g a) = g a := this
  have := g.injective h2
  rw [this] at h
  exact h ha

/-- a permutation fixing `sᶜ` and increasing on `s` is the identity -/
lemma fix_of_mono (s : Finset (Fin n)) (g : Equiv.Perm (Fin n)) (hg : ∀ a, a ∉ s → g a = a)
    (hmono : ∀ i ∈ s, ∀ j ∈ s, i < j → g i < g j) : g = 1 := by
  have hc : s.card = s.card := rfl
  have hu := Finset.orderEmbOfFin_unique hc (f := fun x => g (s.orderEmbOfFin hc x))
    (fun x => fix_maps s g hg (Finset.orderEmbOfFin_mem s hc x))
    (fun x y hxy => hmono _ (Finset.orderEmbOfFin_mem s hc x) _ (Finset.orderEmbOfFin_mem s hc y)
      ((s.orderEmbOfFin hc).strictMono hxy))
  refine Equiv.ext fun a => ?_
  simp only [Equiv.Perm.coe_one, id_eq]
  by_cases ha : a ∈ s
  · have : a ∈ Set.range (s.orderEmbOfFin hc) := by rw [Finset.range_orderEmbOfFin]; exact ha
    obtain ⟨x, rfl⟩ := this
    exact congrFun hu x
  · exact hg a ha

lemma asc_iff (s : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) (hτ : IsAscendingOn τ s)
    {i j : Fin n} (hi : i ∈ s) (hj : j ∈ s) (h : τ i < τ j) : i < j := by
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact h1
  · subst h1; exact absurd h (lt_irrefl _)
  · exact absurd (hτ j hj i hi h1) (not_lt.2 h.le)

lemma card_ascSet_mul (s : Finset (Fin n)) :
    (ascSet s).card * (s.card).factorial = n.factorial := by
  classical
  have hn : n.factorial = (univ : Finset (Equiv.Perm (Fin n))).card := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← card_fixSet, ← Finset.card_product, hn]
  refine Finset.card_bij (fun p _ => p.1 * p.2) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · rintro ⟨τ, ρ⟩ hp ⟨τ', ρ'⟩ hp' heq
    simp only [Finset.mem_product, ascSet, fixSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hp'
    simp only at heq
    -- g = τ'⁻¹ * τ = ρ' * ρ⁻¹
    have hg1 : τ'⁻¹ * τ = ρ' * ρ⁻¹ := by
      calc τ'⁻¹ * τ = τ'⁻¹ * (τ * ρ) * ρ⁻¹ := by group
        _ = τ'⁻¹ * (τ' * ρ') * ρ⁻¹ := by rw [heq]
        _ = ρ' * ρ⁻¹ := by group
    have hfix : ∀ a, a ∉ s → (τ'⁻¹ * τ) a = a := by
      intro a ha
      rw [hg1, Equiv.Perm.mul_apply]
      have h1 : ρ⁻¹ a = a := by
        have := hp.2 a ha
        exact (Equiv.Perm.inv_eq_iff_eq.2 this.symm)
      rw [h1]; exact hp'.2 a ha
    have hmono : ∀ i ∈ s, ∀ j ∈ s, i < j → (τ'⁻¹ * τ) i < (τ'⁻¹ * τ) j := by
      intro i hi j hj hij
      have h1 := hp.1 i hi j hj hij
      apply asc_iff s τ' hp'.1 (fix_maps s _ hfix hi) (fix_maps s _ hfix hj)
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      exact h1
    have hid := fix_of_mono s _ hfix hmono
    have hττ : τ = τ' := by
      have := congrArg (fun g => τ' * g) hid
      simpa using this
    subst hττ
    have hρ : ρ = ρ' := by
      have := congrArg (fun g => τ⁻¹ * g) heq
      simpa using this
    subst hρ; rfl
  · intro σ _
    -- sorting: build τ
    set V := s.image σ with hV
    have hVc : V.card = s.card := Finset.card_image_of_injective _ σ.injective
    have hsc : s.card = s.card := rfl
    let e := s.orderIsoOfFin hsc
    let f := V.orderEmbOfFin hVc
    let τf : Fin n → Fin n := fun i => if hi : i ∈ s then f (e.symm ⟨i, hi⟩) else σ i
    have hτf_mem : ∀ i (hi : i ∈ s), τf i ∈ V := by
      intro i hi; simp only [τf, dif_pos hi]; exact Finset.orderEmbOfFin_mem _ _ _
    have hτf_not : ∀ i, i ∉ s → τf i ∉ V := by
      intro i hi hmem
      simp only [τf, dif_neg hi] at hmem
      rw [hV, Finset.mem_image] at hmem
      obtain ⟨a, ha, hai⟩ := hmem
      have := σ.injective hai
      rw [this] at ha; exact hi ha
    have hinj : Function.Injective τf := by
      intro i j hij
      by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
      · simp only [τf, dif_pos hi, dif_pos hj] at hij
        have := e.symm.injective (f.injective hij)
        exact congrArg Subtype.val this
      · exact absurd (hij ▸ hτf_mem i hi) (hτf_not j hj)
      · exact absurd (hij ▸ hτf_mem j hj) (hτf_not i hi)
      · simp only [τf, dif_neg hi, dif_neg hj] at hij
        exact σ.injective hij
    let τ : Equiv.Perm (Fin n) := Equiv.ofBijective τf (Finite.injective_iff_bijective.1 hinj)
    have hτ : ∀ i, τ i = τf i := fun i => rfl
    refine ⟨⟨τ, τ⁻¹ * σ⟩, ?_, ?_⟩
    · simp only [Finset.mem_product, ascSet, fixSet, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · intro i hi j hj hij
        rw [hτ, hτ]
        simp only [τf, dif_pos hi, dif_pos hj]
        apply f.strictMono
        apply e.symm.strictMono
        exact hij
      · intro a ha
        rw [Equiv.Perm.mul_apply]
        apply Equiv.Perm.inv_eq_iff_eq.2
        rw [hτ]; simp only [τf, dif_neg ha]
    · simp only; group

lemma card_ascSet_real (s : Finset (Fin n)) :
    ((ascSet s).card : ℝ) = (n.factorial : ℝ) / ((s.card).factorial : ℝ) := by
  rw [eq_div_iff (by positivity)]
  exact_mod_cast card_ascSet_mul s

theorem expected_num_ascending_core (n k : ℕ) (_hk : 0 < k) :
    (∑ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ)) / (Nat.factorial n : ℝ) =
      (n.choose k : ℝ) / (Nat.factorial k : ℝ) := by
  classical
  have h1 : ∀ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ) =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard k, (if IsAscendingOn σ s then (1 : ℝ) else 0) := by
    intro σ
    unfold numAscending
    rw [Finset.card_filter]; push_cast; rfl
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ s ∈ (univ : Finset (Fin n)).powersetCard k,
      (∑ σ : Equiv.Perm (Fin n), (if IsAscendingOn σ s then (1 : ℝ) else 0)) =
        (n.factorial : ℝ) / (k.factorial : ℝ) := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    rw [← hs.2, ← card_ascSet_real]
    unfold ascSet
    rw [Finset.card_filter]; push_cast; rfl
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

end KingmanSubadditive.Ulam

open KingmanSubadditive.Ulam


theorem solution (n k : ℕ) (hk : 0 < k) :
    (∑ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ)) / (Nat.factorial n : ℝ) =
      (n.choose k : ℝ) / (Nat.factorial k : ℝ) := by
  exact expected_num_ascending_core n k hk
