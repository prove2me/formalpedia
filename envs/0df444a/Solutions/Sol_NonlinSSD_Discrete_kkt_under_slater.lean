-- Prove2me | solution 1 for NonlinSSD.Discrete.kkt_under_slater
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:23:57.188263+00:00
-- url     : https://prove2.me/submissions/74959203-40c1-4495-94eb-ffe9b7526839

import Mathlib
import Definitions.Def_NonlinSSD_Discrete_Problem

-- carved verbatim out of submission 3861eee3-2361-4b05-a58e-2703be548708, lines 185-518

section
open Finset
set_option autoImplicit false

theorem slater_kkt_aux {E L : Type*} [AddCommGroup E] [Module ℝ E] [Fintype L]
    (S : Set E) (hS : Convex ℝ S) (F0 : E → ℝ) (hF0 : ConcaveOn ℝ S F0)
    (F : L → E → ℝ) (hF : ∀ l, ConcaveOn ℝ S (F l))
    (st : E) (hst : st ∈ S) (hslater : ∀ l, 0 < F l st)
    (sh : E) (hsh : sh ∈ S) (hfeas : ∀ l, 0 ≤ F l sh)
    (hopt : ∀ s ∈ S, (∀ l, 0 ≤ F l s) → F0 s ≤ F0 sh) :
    ∃ lam : L → ℝ, (∀ l, 0 ≤ lam l) ∧
      (∀ s ∈ S, F0 s + ∑ l, lam l * F l s ≤ F0 sh) ∧ (∀ l, lam l * F l sh = 0) := by
  classical
  let v : E → Option L → ℝ := fun s o => Option.elim o (F0 s - F0 sh) (fun l => F l s)
  have hvn : ∀ s, v s none = F0 s - F0 sh := fun s => rfl
  have hvs : ∀ s l, v s (some l) = F l s := fun s l => rfl
  let C : Set (Option L → ℝ) := ⋃ s ∈ S, Set.univ.pi (fun o => Set.Iio (v s o))
  let T : Set (Option L → ℝ) := Set.univ.pi (fun _ => Set.Ici 0)
  have hCmem : ∀ w, w ∈ C ↔ ∃ s ∈ S, ∀ o, w o < v s o := by
    intro w
    simp only [C, Set.mem_iUnion, Set.mem_univ_pi, Set.mem_Iio, exists_prop]
  have hTmem : ∀ w, w ∈ T ↔ ∀ o, 0 ≤ w o := by
    intro w
    simp only [T, Set.mem_univ_pi, Set.mem_Ici]
  have hCopen : IsOpen C := isOpen_biUnion fun s _ =>
    isOpen_set_pi Set.finite_univ fun o _ => isOpen_Iio
  have hTconv : Convex ℝ T := convex_pi fun _ _ => convex_Ici 0
  have hvconc : ∀ s1 ∈ S, ∀ s2 ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → ∀ o,
      a * v s1 o + b * v s2 o ≤ v (a • s1 + b • s2) o := by
    intro s1 h1 s2 h2 a b ha hb hab o
    cases o with
    | none =>
      have := (hF0.2 h1 h2 ha hb hab)
      simp only [hvn, smul_eq_mul] at this ⊢
      have e : F0 sh = (a + b) * F0 sh := by rw [hab, one_mul]
      linear_combination this + e
    | some l =>
      have := ((hF l).2 h1 h2 ha hb hab)
      simpa only [hvs, smul_eq_mul] using this
  have hCconv : Convex ℝ C := by
    intro w1 hw1 w2 hw2 a b ha hb hab
    rw [hCmem] at hw1 hw2 ⊢
    obtain ⟨s1, h1, hw1⟩ := hw1
    obtain ⟨s2, h2, hw2⟩ := hw2
    refine ⟨a • s1 + b • s2, hS h1 h2 ha hb hab, fun o => ?_⟩
    have hv := hvconc s1 h1 s2 h2 a b ha hb hab o
    have k1 := hw1 o
    have k2 := hw2 o
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_lt_mul_of_pos_left k1 ha'
      have := mul_le_mul_of_nonneg_left k2.le hb
      linarith
    · have hb' : 0 < b := by linarith
      have := mul_lt_mul_of_pos_left k2 hb'
      have := mul_le_mul_of_nonneg_left k1.le ha
      linarith
  have hdisj : Disjoint C T := by
    rw [Set.disjoint_left]
    intro w hwC hwT
    rw [hCmem] at hwC
    rw [hTmem] at hwT
    obtain ⟨s, hs, hw⟩ := hwC
    have h0 := hw none
    have hl : ∀ l, 0 ≤ F l s := fun l => by
      have := hw (some l); rw [hvs] at this; linarith [hwT (some l)]
    have := hopt s hs hl
    have := hwT none
    rw [hvn] at h0
    linarith
  obtain ⟨f, u, hfC, hfT⟩ := geometric_hahn_banach_open hCconv hCopen hTconv hdisj
  let a : Option L → ℝ := fun o => f (fun o' => if o = o' then 1 else 0)
  have hf : ∀ w, f w = ∑ o, w o * a o := by
    intro w
    have := LinearMap.pi_apply_eq_sum_univ (f : (Option L → ℝ) →ₗ[ℝ] ℝ) w
    simpa [a, smul_eq_mul] using this
  have hu0 : u ≤ 0 := by
    have := hfT 0 ((hTmem 0).2 fun o => le_rfl)
    simpa using this
  have ha0 : ∀ o, 0 ≤ a o := by
    intro o
    by_contra hneg
    rw [not_le] at hneg
    set t : ℝ := (u - 1) / a o with ht_def
    have ht : 0 ≤ t := div_nonneg_of_nonpos (by linarith) hneg.le
    have hmem : (fun o' => if o = o' then t else 0) ∈ T := by
      rw [hTmem]
      intro o'; split_ifs <;> simp [ht]
    have h1 := hfT _ hmem
    rw [hf] at h1
    rw [Finset.sum_eq_single o (fun o' _ h => by simp [Ne.symm h]) (by simp)] at h1
    simp only [if_true] at h1
    have h2 : t * a o = u - 1 := by rw [ht_def, div_mul_cancel₀ _ hneg.ne]
    linarith
  have hmain : ∀ s ∈ S, ∑ o, v s o * a o ≤ 0 := by
    intro s hs
    by_contra hpos
    rw [not_le] at hpos
    set A := ∑ o, v s o * a o with hA
    set B := ∑ o, a o with hB_def
    have hB : 0 ≤ B := Finset.sum_nonneg fun o _ => ha0 o
    set ε := A / (B + 1) with hε_def
    have hε : 0 < ε := div_pos hpos (by linarith)
    have hmem : (fun o => v s o - ε) ∈ C := (hCmem _).2 ⟨s, hs, fun o => by linarith⟩
    have h1 := hfC _ hmem
    rw [hf] at h1
    have e : ∑ o, (v s o - ε) * a o = A - ε * B := by
      rw [hA, hB_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun o _ => by ring
    rw [e] at h1
    have h2 : ε * B + ε = A := by
      rw [hε_def]; field_simp
    linarith
  have hpos0 : 0 < a none := by
    rcases (ha0 none).lt_or_eq with h | h
    · exact h
    exfalso
    have hm := hmain st hst
    rw [Fintype.sum_option, ← h, mul_zero, zero_add] at hm
    have hnn : ∀ l ∈ (Finset.univ : Finset L), 0 ≤ v st (some l) * a (some l) :=
      fun l _ => mul_nonneg (by rw [hvs]; exact (hslater l).le) (ha0 _)
    have hsum0 := le_antisymm hm (Finset.sum_nonneg hnn)
    have hall : ∀ l, a (some l) = 0 := by
      intro l
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 l (Finset.mem_univ _)
      rw [hvs] at this
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 (hslater l).ne'
      · exact h1
    have hfz : ∀ w, f w = 0 := by
      intro w; rw [hf, Fintype.sum_option, ← h]; simp [hall]
    have hmem : (fun o => v st o - 1) ∈ C := (hCmem _).2 ⟨st, hst, fun o => by linarith⟩
    have := hfC _ hmem
    rw [hfz] at this
    linarith
  have hbound : ∀ s ∈ S, F0 s + ∑ l, a (some l) / a none * F l s ≤ F0 sh := by
    intro s hs
    have hm := hmain s hs
    rw [Fintype.sum_option, hvn] at hm
    simp only [hvs] at hm
    have e : ∑ l, a (some l) / a none * F l s = (∑ l, F l s * a (some l)) / a none := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [e]
    have h1 : (∑ l, F l s * a (some l)) ≤ (F0 sh - F0 s) * a none := by linarith
    have h2 := div_le_div_of_nonneg_right h1 hpos0.le
    rw [mul_div_assoc, div_self hpos0.ne', mul_one] at h2
    linarith
  have hnn : ∀ l ∈ (Finset.univ : Finset L), 0 ≤ a (some l) / a none * F l sh :=
    fun l _ => mul_nonneg (div_nonneg (ha0 _) hpos0.le) (hfeas l)
  refine ⟨fun l => a (some l) / a none, fun l => div_nonneg (ha0 _) hpos0.le, hbound, ?_⟩
  have hb := hbound sh hsh
  have hsum0 : ∑ l, a (some l) / a none * F l sh = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg hnn)
  intro l
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 l (Finset.mem_univ _)

theorem max_conv_6ef (t x1 x2 a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    max (t - (a * x1 + b * x2)) 0 ≤ a * max (t - x1) 0 + b * max (t - x2) 0 := by
  apply max_le
  · have e : t - (a * x1 + b * x2) = a * (t - x1) + b * (t - x2) := by
      linear_combination (-t) * hab
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))

theorem std_split_6ef {m n N : ℕ} (p : Fin n → ℝ) (h : Fin n → (Fin N → ℝ) → ℝ)
    (g : Fin m → Fin n → (Fin N → ℝ) → ℝ) (y : Fin m → Fin n → ℝ)
    (z : Fin N → ℝ) (X μ θ : Fin m → Fin n → ℝ) :
    NonlinSSD.Discrete.stdLagrangian p h g y z X μ θ =
      NonlinSSD.Discrete.objective p h z + ∑ i, ∑ j, p j * (θ i j * (g i j z - X i j)) +
      ∑ i, ∑ k, μ i k * ((∑ j, p j * max (y i k - y i j) 0) -
        ∑ j, p j * max (y i k - X i j) 0) := by
  unfold NonlinSSD.Discrete.stdLagrangian NonlinSSD.Discrete.objective
  have e : ∀ j, p j * (h j z + ∑ i, θ i j * (g i j z - X i j)) =
      p j * h j z + ∑ i, p j * (θ i j * (g i j z - X i j)) := fun j => by
    rw [mul_add, Finset.mul_sum]
  simp only [e, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j i => p j * (θ i j * (g i j z - X i j)))]

open NonlinSSD.Discrete in
theorem solution {m n N : ℕ} (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (Z : Set (Fin N → ℝ)) (hZ : Convex ℝ Z)
    (h : Fin n → (Fin N → ℝ) → ℝ) (hh : ∀ j, ConcaveOn ℝ Set.univ (h j))
    (g : Fin m → Fin n → (Fin N → ℝ) → ℝ) (hg : ∀ i j, ConcaveOn ℝ Set.univ (g i j))
    (y : Fin m → Fin n → ℝ) (hS : SlaterCondition p Z g y)
    (zh : Fin N → ℝ) (Xh : Fin m → Fin n → ℝ) (hopt : IsOptimal p Z h g y zh Xh) :
    ∃ μ θ : Fin m → Fin n → ℝ, (∀ i k, 0 ≤ μ i k) ∧ (∀ i j, 0 ≤ θ i j) ∧
      (∀ z ∈ Z, ∀ X : Fin m → Fin n → ℝ,
        stdLagrangian p h g y z X μ θ ≤ stdLagrangian p h g y zh Xh μ θ) ∧
      (∀ i k, μ i k * ((∑ j, p j * max (y i k - y i j) 0) -
        ∑ j, p j * max (y i k - Xh i j) 0) = 0) ∧
      (∀ i j, θ i j * (g i j zh - Xh i j) = 0) := by
  classical
  obtain ⟨⟨hdomh, hgh, hzhZ⟩, hoptv⟩ := hopt
  obtain ⟨zt, hztI, Xt, hXtg, hdomt⟩ := hS
  have hztZ : zt ∈ Z := intrinsicInterior_subset hztI
  obtain ⟨c, hc⟩ : ∃ c : Fin m → Fin n → ℝ, ∀ i k, c i k = ∑ j, p j * max (y i k - y i j) 0 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Fin m → Fin n → (Fin m → Fin n → ℝ) → ℝ,
      ∀ i k X, D i k X = ∑ j, p j * max (y i k - X i j) 0 := ⟨_, fun _ _ _ => rfl⟩
  have hc0 : ∀ i k, 0 ≤ c i k := fun i k => by
    rw [hc]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hp0 j) (le_max_right _ _)
  have hD0 : ∀ i k X, 0 ≤ D i k X := fun i k X => by
    rw [hD]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hp0 j) (le_max_right _ _)
  have hsupp : ∃ j, 0 < p j := by
    by_contra hne
    simp only [not_exists, not_lt] at hne
    have : ∑ j, p j ≤ 0 := Finset.sum_nonpos fun j _ => hne j
    linarith
  have hk0 : ∀ i, ∃ k, 0 < p k ∧ ∀ j, 0 < p j → y i k ≤ y i j := by
    intro i
    obtain ⟨j0, hj0⟩ := hsupp
    obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun j => 0 < p j) (y i)
      ⟨j0, by simp [hj0]⟩
    exact ⟨k, (Finset.mem_filter.1 hk).2, fun j hj => hmin j (by simp [hj])⟩
  choose k0 hk0p hk0min using hk0
  have hck0 : ∀ i, c i (k0 i) = 0 := by
    intro i; rw [hc]
    apply Finset.sum_eq_zero; intro j _
    rcases (hp0 j).lt_or_eq with hj | hj
    · rw [max_eq_right (by linarith [hk0min i j hj]), mul_zero]
    · rw [← hj, zero_mul]
  have hc0le : ∀ i k, c i k = 0 → y i k ≤ y i (k0 i) := by
    intro i k hck
    rw [hc] at hck
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ p j * max (y i k - y i j) 0 :=
      fun j _ => mul_nonneg (hp0 j) (le_max_right _ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hck (k0 i) (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (hk0p i).ne'
    · have := le_max_left (y i k - y i (k0 i)) 0; linarith
  have hbox : ∀ X, DominanceConstraints p y X → ∀ i j, 0 < p j → y i (k0 i) ≤ X i j := by
    intro X hX i j hj
    have h1 : ∑ j, p j * max (y i (k0 i) - X i j) 0 ≤ 0 := by
      have := hX i (k0 i); rw [← hc, hck0] at this; exact this
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ p j * max (y i (k0 i) - X i j) 0 :=
      fun j _ => mul_nonneg (hp0 j) (le_max_right _ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm h1 (Finset.sum_nonneg hnn)) j
      (Finset.mem_univ _)
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hj.ne'
    · have := le_max_left (y i (k0 i) - X i j) 0; linarith
  have hDbox : ∀ X, (∀ i j, 0 < p j → y i (k0 i) ≤ X i j) → ∀ i k, c i k = 0 → D i k X = 0 := by
    intro X hX i k hck
    rw [hD]; apply Finset.sum_eq_zero; intro j _
    rcases (hp0 j).lt_or_eq with hj | hj
    · rw [max_eq_right (by linarith [hc0le i k hck, hX i j hj]), mul_zero]
    · rw [← hj, zero_mul]
  obtain ⟨ε, hεg, hεpos⟩ : ∃ ε : ℝ, (∀ i k, ε < g i k zt - Xt i k) ∧ 0 < ε := by
    have hev : ∀ᶠ ε in nhds (0:ℝ), ∀ i k, ε < g i k zt - Xt i k :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
        eventually_lt_nhds (sub_pos.2 (hXtg i k))
    exact ((hev.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).and (self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)) (a := 0))).exists
  let S : Set ((Fin N → ℝ) × (Fin m → Fin n → ℝ)) :=
    {s | s.1 ∈ Z ∧ ∀ i j, 0 < p j → y i (k0 i) ≤ s.2 i j}
  have hSconv : Convex ℝ S := by
    intro s1 hs1 s2 hs2 a b ha hb hab
    refine ⟨hZ hs1.1 hs2.1 ha hb hab, fun i j hj => ?_⟩
    have h1 := mul_le_mul_of_nonneg_left (hs1.2 i j hj) ha
    have h2 := mul_le_mul_of_nonneg_left (hs2.2 i j hj) hb
    have e : a * y i (k0 i) + b * y i (k0 i) = y i (k0 i) := by rw [← add_mul, hab, one_mul]
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hF0 : ConcaveOn ℝ S (fun s => objective p h s.1) := by
    refine ⟨hSconv, fun s1 _ s2 _ a b ha hb hab => ?_⟩
    simp only [objective, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro j _
    have h1 := (hh j).2 (Set.mem_univ s1.1) (Set.mem_univ s2.1) ha hb hab
    simp only [smul_eq_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hp0 j)
    simp only [Prod.fst_add, Prod.smul_fst]
    linarith
  let F : (Fin m × Fin n) ⊕ (Fin m × Fin n) → (Fin N → ℝ) × (Fin m → Fin n → ℝ) → ℝ :=
    fun l s => Sum.elim
      (fun ij : Fin m × Fin n => p ij.2 * (g ij.1 ij.2 s.1 - s.2 ij.1 ij.2) +
        (if p ij.2 = 0 then 1 else 0))
      (fun ik : Fin m × Fin n => if c ik.1 ik.2 = 0 then 1 else c ik.1 ik.2 - D ik.1 ik.2 s.2) l
  have hFl : ∀ i j s, F (Sum.inl (i, j)) s =
      p j * (g i j s.1 - s.2 i j) + (if p j = 0 then 1 else 0) := fun _ _ _ => rfl
  have hFr : ∀ i k s, F (Sum.inr (i, k)) s =
      if c i k = 0 then 1 else c i k - D i k s.2 := fun _ _ _ => rfl
  have hF : ∀ l, ConcaveOn ℝ S (F l) := by
    rintro (⟨i, j⟩ | ⟨i, k⟩)
    · refine ⟨hSconv, fun s1 _ s2 _ a b ha hb hab => ?_⟩
      simp only [smul_eq_mul, hFl]
      have h1 := (hg i j).2 (Set.mem_univ s1.1) (Set.mem_univ s2.1) ha hb hab
      simp only [smul_eq_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (hp0 j)
      have e : ∀ d : ℝ, a * d + b * d = d := fun d => by rw [← add_mul, hab, one_mul]
      have e1 := e (if p j = 0 then 1 else 0)
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      linarith
    · refine ⟨hSconv, fun s1 _ s2 _ a b ha hb hab => ?_⟩
      simp only [smul_eq_mul, hFr]
      split_ifs with hck
      · linarith
      · have hconv : D i k (a • s1 + b • s2).2 ≤ a * D i k s1.2 + b * D i k s2.2 := by
          rw [hD, hD, hD, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum; intro j _
          have := mul_le_mul_of_nonneg_left
            (max_conv_6ef (y i k) (s1.2 i j) (s2.2 i j) a b ha hb hab) (hp0 j)
          simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linarith
        have e : a * c i k + b * c i k = c i k := by rw [← add_mul, hab, one_mul]
        linarith
  have hXtbox := hbox Xt hdomt
  have hst : ((zt, fun i k => Xt i k + ε) : (Fin N → ℝ) × (Fin m → Fin n → ℝ)) ∈ S :=
    ⟨hztZ, fun i j hj => by have := hXtbox i j hj; dsimp only; linarith⟩
  have hDmono : ∀ i k (X X' : Fin m → Fin n → ℝ), (∀ i j, X i j ≤ X' i j) → D i k X' ≤ D i k X := by
    intro i k X X' hXX
    rw [hD, hD]; apply Finset.sum_le_sum; intro j _
    exact mul_le_mul_of_nonneg_left (max_le_max (by linarith [hXX i j]) le_rfl) (hp0 j)
  have hslater : ∀ l, 0 < F l (zt, fun i k => Xt i k + ε) := by
    rintro (⟨i, j⟩ | ⟨i, k⟩)
    · rw [hFl]
      dsimp only
      by_cases hj : p j = 0
      · rw [if_pos hj, hj]; simp
      · rw [if_neg hj, add_zero]
        exact mul_pos (lt_of_le_of_ne (hp0 j) (Ne.symm hj)) (by linarith [hεg i j])
    · rw [hFr]
      split_ifs with hck
      · exact one_pos
      · have hcpos : 0 < c i k := lt_of_le_of_ne (hc0 i k) (Ne.symm hck)
        dsimp only
        have hdc : D i k Xt ≤ c i k := by
          have := hdomt i k; rw [← hc, ← hD] at this; exact this
        have hle := hDmono i k Xt (fun i k => Xt i k + ε) (fun i j => by linarith)
        by_cases hDt : D i k Xt ≤ 0
        · linarith
        · have hDt' : 0 < D i k Xt := lt_of_not_ge hDt
          have hlt : D i k (fun i k => Xt i k + ε) < D i k Xt := by
            obtain ⟨j, hjpos⟩ : ∃ j, 0 < p j * max (y i k - Xt i j) 0 := by
              by_contra hne
              simp only [not_exists, not_lt] at hne
              rw [hD] at hDt'
              have := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => hne j)
              linarith
            rw [hD, hD]
            apply Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left
              (max_le_max (by linarith) le_rfl) (hp0 j))
            refine ⟨j, Finset.mem_univ _, ?_⟩
            have hpj : 0 < p j := lt_of_le_of_ne (hp0 j)
              (fun h => by rw [← h, zero_mul] at hjpos; exact lt_irrefl _ hjpos)
            have hmx : 0 < max (y i k - Xt i j) 0 := lt_of_le_of_ne (le_max_right _ _)
              (fun h => by rw [← h, mul_zero] at hjpos; exact lt_irrefl _ hjpos)
            have hu : 0 < y i k - Xt i j := by
              rcases lt_max_iff.1 hmx with h | h
              · exact h
              · exact absurd h (lt_irrefl _)
            apply mul_lt_mul_of_pos_left _ hpj
            rw [max_eq_left hu.le]
            exact max_lt (by linarith) hu
          linarith
  have hshS : ((zh, Xh) : (Fin N → ℝ) × (Fin m → Fin n → ℝ)) ∈ S := ⟨hzhZ, hbox Xh hdomh⟩
  have hfeas : ∀ l, 0 ≤ F l (zh, Xh) := by
    rintro (⟨i, j⟩ | ⟨i, k⟩)
    · rw [hFl]; dsimp only
      have := mul_nonneg (hp0 j) (sub_nonneg.2 (hgh i j))
      split_ifs <;> linarith
    · rw [hFr]; dsimp only
      split_ifs
      · exact zero_le_one
      · have := hdomh i k; rw [← hc, ← hD] at this; linarith
  have hoptK : ∀ s ∈ S, (∀ l, 0 ≤ F l s) → objective p h s.1 ≤ objective p h zh := by
    intro s hs hFs
    apply hoptv s.1 (fun i j => if p j = 0 then g i j s.1 else s.2 i j)
    refine ⟨fun i k => ?_, fun i k => ?_, hs.1⟩
    · show ∑ j, p j * max (y i k - (if p j = 0 then g i j s.1 else s.2 i j)) 0 ≤
        ∑ j, p j * max (y i k - y i j) 0
      have hDeq : ∑ j, p j * max (y i k - (if p j = 0 then g i j s.1 else s.2 i j)) 0 =
          D i k s.2 := by
        rw [hD]; apply Finset.sum_congr rfl; intro j _
        split_ifs with hj
        · rw [hj, zero_mul, zero_mul]
        · rfl
      rw [hDeq, ← hc]
      have := hFs (Sum.inr (i, k))
      rw [hFr] at this
      split_ifs at this with hck
      · rw [hDbox s.2 hs.2 i k hck]; exact hc0 i k
      · linarith
    · show (if p k = 0 then g i k s.1 else s.2 i k) ≤ g i k s.1
      split_ifs with hk
      · exact le_rfl
      · have hpk : 0 < p k := lt_of_le_of_ne (hp0 k) (Ne.symm hk)
        have := hFs (Sum.inl (i, k))
        rw [hFl, if_neg hk, add_zero] at this
        by_contra hlt
        have : p k * (g i k s.1 - s.2 i k) < 0 := mul_neg_of_pos_of_neg hpk (by linarith)
        linarith
  obtain ⟨lam, hlam0, hbound, hcs⟩ := slater_kkt_aux S hSconv (fun s => objective p h s.1) hF0 F hF
    (zt, fun i k => Xt i k + ε) hst hslater (zh, Xh) hshS hfeas hoptK
  have hlaml0 : ∀ i j, p j = 0 → lam (Sum.inl (i, j)) = 0 := by
    intro i j hj
    have := hcs (Sum.inl (i, j)); rw [hFl, if_pos hj, hj] at this
    simpa using this
  have hlamr0 : ∀ i k, c i k = 0 → lam (Sum.inr (i, k)) = 0 := by
    intro i k hck
    have := hcs (Sum.inr (i, k)); rw [hFr, if_pos hck, mul_one] at this; exact this
  have hlamrcs : ∀ i k, lam (Sum.inr (i, k)) * (c i k - D i k Xh) = 0 := by
    intro i k
    by_cases hck : c i k = 0
    · rw [hlamr0 i k hck, zero_mul]
    · have := hcs (Sum.inr (i, k)); rw [hFr, if_neg hck] at this; exact this
  obtain ⟨θ, hθ⟩ : ∃ θ : Fin m → Fin n → ℝ, ∀ i j, θ i j = lam (Sum.inl (i, j)) :=
    ⟨_, fun _ _ => rfl⟩
  have hθ0 : ∀ i j, 0 ≤ θ i j := fun i j => by rw [hθ]; exact hlam0 _
  have hθcs : ∀ i j, θ i j * (g i j zh - Xh i j) = 0 := by
    intro i j
    rw [hθ]
    by_cases hj : p j = 0
    · rw [hlaml0 i j hj, zero_mul]
    · have := hcs (Sum.inl (i, j)); rw [hFl, if_neg hj, add_zero] at this; dsimp only at this
      have h2 : p j * (lam (Sum.inl (i, j)) * (g i j zh - Xh i j)) = 0 := by
        linear_combination this
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd h3 hj
      · exact h3
  obtain ⟨Mi, hMi⟩ : ∃ Mi : Fin m → ℝ, ∀ i, Mi i = ∑ j, θ i j := ⟨_, fun _ => rfl⟩
  have hMi0 : ∀ i, 0 ≤ Mi i := fun i => by rw [hMi]; exact Finset.sum_nonneg fun j _ => hθ0 i j
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin m → Fin n → ℝ, ∀ i k,
      μ i k = lam (Sum.inr (i, k)) + if k = k0 i then Mi i else 0 := ⟨_, fun _ _ => rfl⟩
  have hμ0 : ∀ i k, 0 ≤ μ i k := fun i k => by
    rw [hμ]; have := hlam0 (Sum.inr (i, k)); split_ifs <;> linarith [hMi0 i]
  have hDXh0 : ∀ i, D i (k0 i) Xh = 0 := fun i => hDbox Xh (hbox Xh hdomh) i (k0 i) (hck0 i)
  have hμcs : ∀ i k, μ i k * (c i k - D i k Xh) = 0 := by
    intro i k
    rw [hμ, add_mul, hlamrcs i k]
    split_ifs with hk
    · subst hk; rw [hck0, hDXh0]; ring
    · ring
  have hSL : ∀ z X, stdLagrangian p h g y z X μ θ = objective p h z +
      ∑ i, ∑ j, p j * (θ i j * (g i j z - X i j)) + ∑ i, ∑ k, μ i k * (c i k - D i k X) := by
    intro z X; rw [std_split_6ef]; simp only [hc, hD]
  have hSLh : stdLagrangian p h g y zh Xh μ θ = objective p h zh := by
    rw [hSL]
    simp only [hθcs, hμcs, mul_zero, Finset.sum_const_zero, add_zero]
  have hB : ∀ z ∈ Z, ∀ Xb : Fin m → Fin n → ℝ, (∀ i j, 0 < p j → y i (k0 i) ≤ Xb i j) →
      stdLagrangian p h g y z Xb μ θ ≤ objective p h zh := by
    intro z hz Xb hXb
    have hb := hbound (z, Xb) ⟨hz, hXb⟩
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hb
    have e1 : ∑ i, ∑ j, lam (Sum.inl (i, j)) * F (Sum.inl (i, j)) (z, Xb) =
        ∑ i, ∑ j, p j * (θ i j * (g i j z - Xb i j)) := by
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
      rw [hFl, hθ]; dsimp only
      by_cases hj : p j = 0
      · rw [hlaml0 i j hj, hj]; ring
      · rw [if_neg hj]; ring
    have e2 : ∑ i, ∑ k, lam (Sum.inr (i, k)) * F (Sum.inr (i, k)) (z, Xb) =
        ∑ i, ∑ k, μ i k * (c i k - D i k Xb) := by
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _
      rw [hFr, hμ]; dsimp only
      by_cases hck : c i k = 0
      · rw [if_pos hck, hlamr0 i k hck, hck, hDbox Xb hXb i k hck]; ring
      · rw [if_neg hck]
        have hk : k ≠ k0 i := fun hh => hck (hh ▸ hck0 i)
        rw [if_neg hk]; ring
    rw [e1, e2] at hb
    rw [hSL]
    dsimp only at hb
    linarith
  have hA : ∀ z (X Xb : Fin m → Fin n → ℝ), (∀ i j, Xb i j = max (X i j) (y i (k0 i))) →
      stdLagrangian p h g y z X μ θ ≤ stdLagrangian p h g y z Xb μ θ := by
    intro z X Xb hXb
    have hXbX : ∀ i j, X i j ≤ Xb i j := fun i j => by rw [hXb]; exact le_max_left _ _
    have hDk0X : ∀ i, D i (k0 i) X = ∑ j, p j * (Xb i j - X i j) := by
      intro i; rw [hD]; apply Finset.sum_congr rfl; intro j _; rw [hXb]; congr 1
      rcases le_total (X i j) (y i (k0 i)) with h1 | h1
      · rw [max_eq_left (by linarith), max_eq_right h1]
      · rw [max_eq_right (by linarith), max_eq_left h1]; ring
    have hDk0b : ∀ i, D i (k0 i) Xb = 0 := fun i =>
      hDbox Xb (fun i j _ => by rw [hXb]; exact le_max_right _ _) i (k0 i) (hck0 i)
    rw [hSL, hSL]
    have key : ∀ i, ∑ j, p j * (θ i j * (g i j z - X i j)) + ∑ k, μ i k * (c i k - D i k X) ≤
        ∑ j, p j * (θ i j * (g i j z - Xb i j)) + ∑ k, μ i k * (c i k - D i k Xb) := by
      intro i
      have hT1 : ∑ j, p j * (θ i j * (g i j z - X i j)) -
          ∑ j, p j * (θ i j * (g i j z - Xb i j)) ≤ Mi i * D i (k0 i) X := by
        rw [← Finset.sum_sub_distrib, hDk0X, Finset.mul_sum]
        apply Finset.sum_le_sum; intro j _
        have h1 : 0 ≤ p j * (Xb i j - X i j) := mul_nonneg (hp0 j) (sub_nonneg.2 (hXbX i j))
        have h2 : θ i j ≤ Mi i := by
          rw [hMi]; exact Finset.single_le_sum (fun j _ => hθ0 i j) (Finset.mem_univ j)
        have := mul_le_mul_of_nonneg_right h2 h1
        linarith
      have hT2 : Mi i * D i (k0 i) X ≤ ∑ k, μ i k * (D i k X - D i k Xb) := by
        have hnn : ∀ k ∈ Finset.univ, 0 ≤ μ i k * (D i k X - D i k Xb) :=
          fun k _ => mul_nonneg (hμ0 i k) (sub_nonneg.2 (hDmono i k X Xb hXbX))
        refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ (k0 i)))
        rw [hDk0b, sub_zero]
        apply mul_le_mul_of_nonneg_right _ (hD0 i (k0 i) X)
        rw [hμ, if_pos rfl]; linarith [hlam0 (Sum.inr (i, k0 i))]
      have e : ∑ k, μ i k * (c i k - D i k X) = ∑ k, μ i k * (c i k - D i k Xb) -
          ∑ k, μ i k * (D i k X - D i k Xb) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
      linarith
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
    linarith
  refine ⟨μ, θ, hμ0, hθ0, ?_, ?_, hθcs⟩
  · intro z hz X
    obtain ⟨Xb, hXb⟩ : ∃ Xb : Fin m → Fin n → ℝ, ∀ i j, Xb i j = max (X i j) (y i (k0 i)) :=
      ⟨_, fun _ _ => rfl⟩
    calc stdLagrangian p h g y z X μ θ ≤ stdLagrangian p h g y z Xb μ θ := hA z X Xb hXb
      _ ≤ objective p h zh := hB z hz Xb (fun i j _ => by rw [hXb]; exact le_max_right _ _)
      _ = stdLagrangian p h g y zh Xh μ θ := hSLh.symm
  · intro i k
    rw [← hc i k, ← hD i k Xh]
    exact hμcs i k

end
