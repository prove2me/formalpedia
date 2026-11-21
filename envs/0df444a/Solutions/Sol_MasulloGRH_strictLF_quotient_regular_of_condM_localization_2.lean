-- Prove2me | solution 2 for MasulloGRH.strictLF_quotient_regular_of_condM_localization
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:15:39.91818+00:00
-- url     : https://prove2.me/submissions/1f6c8c0e-d8d6-478a-98f4-240118d53d06

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages

/-!
# Retakh's lemma: condition (M) localizes to the inductive limit

Abstract part.  We work in a complex vector space `Y` with an increasing sequence of "levels"
`L k ⊆ Y` and, for each level, a predicate `N k S` ("`S` is a `0`-neighbourhood of level `k`").
The proof follows J. Wengenroth, *Acyclic inductive spectra of Fréchet spaces*,
Studia Math. 120 (1996), Lemma 2.4 and Proposition 2.5 (nesting), and the Palamodov–Valdivia
localization argument (increasing disks and a downward induction on tails).
-/

set_option autoImplicit false

open Set Filter Topology Pointwise

namespace RetakhLoc

/-- Abstract inductive-spectrum data. -/
structure Spec (Y : Type*) [AddCommGroup Y] [Module ℂ Y] where
  L : ℕ → Set Y
  N : ℕ → Set Y → Prop
  L_mono : ∀ i j, i ≤ j → L i ⊆ L j
  L_zero : ∀ i, (0 : Y) ∈ L i
  L_add : ∀ i, ∀ x ∈ L i, ∀ y ∈ L i, x + y ∈ L i
  L_smul : ∀ i (c : ℝ), ∀ x ∈ L i, c • x ∈ L i
  N_mono : ∀ i (S T : Set Y), N i S → S ⊆ T → N i T
  N_inter : ∀ i (S T : Set Y), N i S → N i T → N i (S ∩ T)
  N_smul : ∀ i (S : Set Y) (c : ℝ), c ≠ 0 → N i S → N i (c • S)
  N_absconv : ∀ i (S : Set Y), N i S → ∃ T ⊆ S, N i T ∧ Balanced ℂ T ∧ Convex ℝ T
  N_absorb : ∀ i (S : Set Y), N i S → ∀ y ∈ L i, ∃ p : ℕ, ((2 : ℝ) ^ p)⁻¹ • y ∈ S
  N_le : ∀ i j (S : Set Y), i ≤ j → N j S → N i S

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

/-- `A` is `(i,k)`-good: on `A` the level-`k` neighbourhood filter is finer than level `i`. -/
def Good (S : Spec Y) (i k : ℕ) (A : Set Y) : Prop :=
  ∀ W, S.N i W → ∃ W', S.N k W' ∧ A ∩ W' ⊆ W

lemma Spec.zero_mem (S : Spec Y) {i : ℕ} {W : Set Y} (h : S.N i W) : (0 : Y) ∈ W := by
  obtain ⟨p, hp⟩ := S.N_absorb i W h 0 (S.L_zero i)
  simpa using hp

lemma good_mono (S : Spec Y) {i k : ℕ} {A B : Set Y} (h : Good S i k A) (hBA : B ⊆ A) :
    Good S i k B := by
  intro W hW
  obtain ⟨W', hW', hs⟩ := h W hW
  exact ⟨W', hW', fun x hx => hs ⟨hBA hx.1, hx.2⟩⟩

lemma good_raise (S : Spec Y) {i i' k : ℕ} {A : Set Y} (h : Good S i k A) (hii : i ≤ i') :
    Good S i' k A := fun W hW => h W (S.N_le i i' W hii hW)

lemma balanced_real_smul_mem {A : Set Y} (hA : Balanced ℂ A) {r : ℝ} (hr : |r| ≤ 1) {x : Y}
    (hx : x ∈ A) : r • x ∈ A := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact hA.smul_mem (by simpa using hr) hx

/-- For an absolutely convex `P` and `0 ≤ a ≤ b`, `a • P ⊆ b • P`. -/
lemma smul_subset_smul_of_le {P : Set Y} (hP : Balanced ℂ P) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : a • P ⊆ b • P := by
  rintro _ ⟨p, hp, rfl⟩
  rcases eq_or_lt_of_le (ha.trans hab) with hb | hb
  · have : a = 0 := le_antisymm (hb ▸ hab) ha
    subst this
    refine ⟨0, ?_, by simp⟩
    have := balanced_real_smul_mem hP (r := 0) (by simp) hp
    simpa using this
  · refine ⟨(a / b) • p, balanced_real_smul_mem hP ?_ hp, ?_⟩
    · rw [abs_of_nonneg (div_nonneg ha hb.le)]
      exact (div_le_one hb).mpr hab
    · show b • ((a / b) • p) = a • p
      rw [smul_smul, mul_div_cancel₀ _ hb.ne']

/-- Sums of two members of an absolutely convex set. -/
lemma add_mem_two_smul {P : Set Y} (hP : Convex ℝ P) {x y : Y} (hx : x ∈ P) (hy : y ∈ P) :
    x + y ∈ (2 : ℝ) • P := by
  have h := (hP.add_smul (p := (1 : ℝ)) (q := 1) zero_le_one zero_le_one)
  have : x + y ∈ (1 : ℝ) • P + (1 : ℝ) • P := by
    rw [one_smul]; exact Set.add_mem_add hx hy
  rw [← h] at this
  norm_num at this
  exact this

/-- **Lemma R** (Wengenroth 1996, Lemma 2.4). -/
lemma good_of_good_inter (S : Spec Y) {j k : ℕ} {A Vn : Set Y} (hAL : A ⊆ S.L j)
    (hAb : Balanced ℂ A) (hVn : S.N j Vn) (h : Good S j k (A ∩ Vn)) : Good S j k A := by
  intro W hW
  obtain ⟨W', hW', hsub⟩ :=
    h (W ∩ ((1 / 2 : ℝ) • Vn)) (S.N_inter _ _ _ hW (S.N_smul _ _ _ (by norm_num) hVn))
  obtain ⟨T, hTW', hT, hTb, -⟩ := S.N_absconv _ _ hW'
  refine ⟨T, hT, ?_⟩
  rintro x ⟨hxA, hxT⟩
  have key : ∀ p : ℕ, ((2 : ℝ) ^ p)⁻¹ • x ∈ Vn → x ∈ Vn := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      intro hp
      apply ih
      have hle : |((2 : ℝ) ^ (p + 1))⁻¹| ≤ 1 := by
        rw [abs_of_pos (by positivity)]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      have hyA := balanced_real_smul_mem hAb hle hxA
      have hyT := balanced_real_smul_mem hTb hle hxT
      have hm := (hsub ⟨⟨hyA, hp⟩, hTW' hyT⟩).2
      obtain ⟨v, hv, hveq⟩ := Set.mem_smul_set.mp hm
      have h2 : ((2 : ℝ) ^ p)⁻¹ • x = (2 : ℝ) • (((2 : ℝ) ^ (p + 1))⁻¹ • x) := by
        rw [smul_smul]; congr 1; rw [pow_succ]; field_simp
      rw [h2, ← hveq, smul_smul]
      norm_num
      exact hv
  obtain ⟨p, hp⟩ := S.N_absorb _ _ hVn x (hAL hxA)
  exact (hsub ⟨⟨hxA, key p hp⟩, hTW' hxT⟩).1

/-- **Nesting** (Wengenroth 1996, Proposition 2.5): the neighbourhoods of condition (M) can be
replaced by an increasing sequence of absolutely convex ones with the same goodness. -/
lemma nest (S : Spec Y) (ℓ : ℕ → ℕ) (hℓ : Monotone ℓ) (Q : ℕ → Set Y)
    (hQL : ∀ j, Q j ⊆ S.L (ℓ j)) (hQb : ∀ j, Balanced ℂ (Q j)) (hQc : ∀ j, Convex ℝ (Q j))
    (hQN : ∀ j, S.N (ℓ j) (Q j)) (hQg : ∀ j, Good S (ℓ (j + 1)) (ℓ (j + 2)) (Q j)) :
    ∃ P : ℕ → Set Y, P 0 = Q 0 ∧ (∀ j, P j ⊆ P (j + 1)) ∧ (∀ j, P j ⊆ S.L (ℓ j)) ∧
      (∀ j, Balanced ℂ (P j)) ∧ (∀ j, Convex ℝ (P j)) ∧ (∀ j, S.N (ℓ j) (P j)) ∧
      (∀ j, Good S (ℓ (j + 1)) (ℓ (j + 2)) (P j)) := by
  have hex : ∀ (j : ℕ) (P : Set Y), ∃ Vv : Set Y, Good S (ℓ (j + 1)) (ℓ (j + 2)) P →
      S.N (ℓ (j + 2)) Vv ∧ Balanced ℂ Vv ∧ Convex ℝ Vv ∧
        P ∩ ((2 : ℝ) • Vv) ⊆ (1 / 2 : ℝ) • Q (j + 1) := by
    intro j P
    by_cases hg : Good S (ℓ (j + 1)) (ℓ (j + 2)) P
    · obtain ⟨W', hW', hsub⟩ :=
        hg ((1 / 2 : ℝ) • Q (j + 1)) (S.N_smul _ _ _ (by norm_num) (hQN (j + 1)))
      obtain ⟨T, hTW, hT, hTb, hTc⟩ := S.N_absconv _ _ hW'
      refine ⟨(1 / 2 : ℝ) • T, fun _ =>
        ⟨S.N_smul _ _ _ (by norm_num) hT, hTb.smul _, hTc.smul _, ?_⟩⟩
      rw [smul_smul]
      norm_num
      exact fun x hx => hsub ⟨hx.1, hTW hx.2⟩
    · exact ⟨univ, fun h => absurd h hg⟩
  choose Vv hVv using hex
  let P : ℕ → Set Y := fun j =>
    Nat.rec (Q 0) (fun j Pj => Pj + ((1 / 2 : ℝ) • Q (j + 1) ∩ Vv j Pj)) j
  have hP0 : P 0 = Q 0 := rfl
  have hPs : ∀ j, P (j + 1) = P j + ((1 / 2 : ℝ) • Q (j + 1) ∩ Vv j (P j)) := fun j => rfl
  have inv : ∀ j, P j ⊆ S.L (ℓ j) ∧ Balanced ℂ (P j) ∧ Convex ℝ (P j) ∧ S.N (ℓ j) (P j) ∧
      Good S (ℓ (j + 1)) (ℓ (j + 2)) (P j) := by
    intro j
    induction j with
    | zero => exact ⟨hQL 0, hQb 0, hQc 0, hQN 0, hQg 0⟩
    | succ j ih =>
      obtain ⟨hL, hb, hc, hN, hg⟩ := ih
      obtain ⟨hVN, hVb, hVc, hVsub⟩ := hVv j (P j) hg
      have h0P : (0 : Y) ∈ P j := S.zero_mem hN
      have hQhalfL : (1 / 2 : ℝ) • Q (j + 1) ⊆ S.L (ℓ (j + 1)) := by
        rintro _ ⟨q, hq, rfl⟩
        exact S.L_smul _ _ _ (hQL (j + 1) hq)
      have hPL1 : P (j + 1) ⊆ S.L (ℓ (j + 1)) := by
        rw [hPs]
        rintro _ ⟨a, ha, b, hb', rfl⟩
        exact S.L_add _ _ (S.L_mono _ _ (hℓ (Nat.le_succ j)) (hL ha)) _ (hQhalfL hb'.1)
      have hPb1 : Balanced ℂ (P (j + 1)) := by
        rw [hPs]; exact hb.add (((hQb (j + 1)).smul _).inter hVb)
      refine ⟨hPL1, hPb1, ?_, ?_, ?_⟩
      · rw [hPs]; exact hc.add (((hQc (j + 1)).smul _).inter hVc)
      · rw [hPs]
        refine S.N_mono _ _ _ (S.N_inter _ _ _ (S.N_smul _ _ (1 / 2 : ℝ) (by norm_num) (hQN (j + 1)))
          (S.N_le _ _ _ (hℓ (by omega)) hVN)) ?_
        intro x hx
        exact ⟨0, h0P, x, hx, zero_add x⟩
      · -- goodness via Lemma R with `Vn := Vv j (P j)`
        have hPL2 : P (j + 1) ⊆ S.L (ℓ (j + 2)) :=
          hPL1.trans (S.L_mono _ _ (hℓ (by omega)))
        refine good_of_good_inter S hPL2 hPb1 hVN (good_mono S (hQg (j + 1)) ?_)
        rw [hPs]
        rintro z ⟨⟨a, ha, b, ⟨hbQ, hbV⟩, rfl⟩, hzV⟩
        -- `a = (a + b) + (-b) ∈ V + V = 2 • V`
        have hnb : -b ∈ Vv j (P j) := hVb.neg_mem_iff.mpr hbV
        have ha2 : a ∈ (2 : ℝ) • Vv j (P j) := by
          have := add_mem_two_smul hVc hzV hnb
          simpa using this
        have haQ : a ∈ (1 / 2 : ℝ) • Q (j + 1) := hVsub ⟨ha, ha2⟩
        obtain ⟨a', ha', rfl⟩ := Set.mem_smul_set.mp haQ
        obtain ⟨b', hb'', rfl⟩ := Set.mem_smul_set.mp hbQ
        have hconv := (hQc (j + 1)) ha' hb'' (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        simpa using hconv
  refine ⟨P, hP0, fun j => ?_, fun j => (inv j).1, fun j => (inv j).2.1, fun j => (inv j).2.2.1,
    fun j => (inv j).2.2.2.1, fun j => (inv j).2.2.2.2⟩
  rw [hPs]
  intro x hx
  exact ⟨x, hx, 0, ⟨⟨0, S.zero_mem (hQN (j + 1)), by simp⟩,
    S.zero_mem (hVv j (P j) (inv j).2.2.2.2).1⟩, add_zero x⟩

lemma smul_set_mono' {A B : Set Y} (h : A ⊆ B) (c : ℝ) : c • A ⊆ c • B := by
  rintro _ ⟨a, ha, rfl⟩; exact ⟨a, h ha, rfl⟩

/-- **Localization** (Palamodov–Valdivia): with nested good neighbourhoods `P j`, every
level-`ℓ 1` neighbourhood `W` contains `P 0 ∩ G` for an absolutely convex `G` that is a
neighbourhood at every level. -/
lemma localize (S : Spec Y) (ℓ : ℕ → ℕ) (hℓ : Monotone ℓ) (P : ℕ → Set Y)
    (hPmono : ∀ j, P j ⊆ P (j + 1)) (hPb : ∀ j, Balanced ℂ (P j)) (hPc : ∀ j, Convex ℝ (P j))
    (hPN : ∀ j, S.N (ℓ j) (P j)) (hPg : ∀ j, Good S (ℓ (j + 1)) (ℓ (j + 2)) (P j))
    (W : Set Y) (hWN : S.N (ℓ 1) W) (hWb : Balanced ℂ W) (hWc : Convex ℝ W) :
    ∃ G : Set Y, Balanced ℂ G ∧ Convex ℝ G ∧ (∀ j, S.N (ℓ (j + 1)) G) ∧ P 0 ∩ G ⊆ W := by
  have hex : ∀ (i : ℕ) (Zi : Set Y), ∃ Z' : Set Y, S.N (ℓ (i + 1)) Zi →
      S.N (ℓ (i + 2)) Z' ∧ Balanced ℂ Z' ∧ Convex ℝ Z' ∧ P i ∩ Z' ⊆ (1 / 2 : ℝ) • Zi := by
    intro i Zi
    by_cases hZ : S.N (ℓ (i + 1)) Zi
    · obtain ⟨W', hW', hsub⟩ := hPg i ((1 / 2 : ℝ) • Zi) (S.N_smul _ _ _ (by norm_num) hZ)
      obtain ⟨T, hTW, hT, hTb, hTc⟩ := S.N_absconv _ _ hW'
      exact ⟨T, fun _ => ⟨hT, hTb, hTc, fun x hx => hsub ⟨hx.1, hTW hx.2⟩⟩⟩
    · exact ⟨univ, fun h => absurd h hZ⟩
  choose Zn hZn using hex
  let Z : ℕ → Set Y := fun i => Nat.rec W (fun i Zi => Zn i Zi) i
  have hZ0 : Z 0 = W := rfl
  have hZs : ∀ i, Z (i + 1) = Zn i (Z i) := fun i => rfl
  have hZinv : ∀ i, S.N (ℓ (i + 1)) (Z i) ∧ Balanced ℂ (Z i) ∧ Convex ℝ (Z i) := by
    intro i
    induction i with
    | zero => exact ⟨hWN, hWb, hWc⟩
    | succ i ih =>
      rw [hZs]
      obtain ⟨h1, h2, h3, -⟩ := hZn i (Z i) ih.1
      exact ⟨h1, h2, h3⟩
  have hZrel : ∀ i, P i ∩ Z (i + 1) ⊆ (1 / 2 : ℝ) • Z i := fun i => by
    rw [hZs]; exact (hZn i (Z i) (hZinv i).1).2.2.2
  -- the disks
  let W' : ℕ → Set Y := fun i => Z i ∩ Z (i + 1) ∩ (((2 : ℝ) ^ (i + 1))⁻¹ • P (i + 1))
  have hW'b : ∀ i, Balanced ℂ (W' i) := fun i =>
    ((hZinv i).2.1.inter (hZinv (i + 1)).2.1).inter ((hPb (i + 1)).smul _)
  have hW'c : ∀ i, Convex ℝ (W' i) := fun i =>
    ((hZinv i).2.2.inter (hZinv (i + 1)).2.2).inter ((hPc (i + 1)).smul _)
  have hW'N : ∀ i, S.N (ℓ (i + 1)) (W' i) := fun i =>
    S.N_inter _ _ _ (S.N_inter _ _ _ (hZinv i).1
      (S.N_le _ _ _ (hℓ (by omega)) (hZinv (i + 1)).1))
      (S.N_smul _ _ _ (by positivity) (hPN (i + 1)))
  have h0W' : ∀ i, (0 : Y) ∈ W' i := fun i => S.zero_mem (hW'N i)
  -- `G`: finite sums of elements of the disks
  let G : Set Y := {x | ∃ (n : ℕ) (w : ℕ → Y), (∀ i < n, w i ∈ W' i) ∧
    x = ∑ i ∈ Finset.range n, w i}
  -- padding lemma
  have pad : ∀ (n M : ℕ) (w : ℕ → Y), n ≤ M →
      ∑ i ∈ Finset.range M, (if i < n then w i else 0) = ∑ i ∈ Finset.range n, w i := by
    intro n M w hnM
    rw [← Finset.sum_range_add_sum_Ico _ hnM]
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi)),
      Finset.sum_eq_zero (fun i hi => if_neg (by simp at hi; omega)), add_zero]
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · -- balanced
    intro a ha
    rintro _ ⟨x, ⟨n, w, hw, rfl⟩, rfl⟩
    exact ⟨n, fun i => a • w i, fun i hi => (hW'b i).smul_mem ha (hw i hi),
      by simp [Finset.smul_sum]⟩
  · -- convex
    rintro x ⟨n, w, hw, rfl⟩ y ⟨m, u, hu, rfl⟩ a b ha hb hab
    refine ⟨max n m, fun i => a • (if i < n then w i else 0) + b • (if i < m then u i else 0),
      fun i _ => ?_, ?_⟩
    · apply hW'c i
      · split_ifs with h
        · exact hw i h
        · exact h0W' i
      · split_ifs with h
        · exact hu i h
        · exact h0W' i
      · exact ha
      · exact hb
      · exact hab
    · rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
        pad n _ w (le_max_left _ _), pad m _ u (le_max_right _ _)]
  · -- neighbourhood at each level
    intro j
    refine S.N_mono _ _ _ (hW'N j) ?_
    intro y hy
    refine ⟨j + 1, fun i => if i = j then y else 0, fun i _ => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hy
      · simp only [h, if_false]; exact h0W' i
    · rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp
  · -- the key inclusion
    rintro x ⟨hxP, n, w, hw, hxsum⟩
    -- running remainders lie in `(2 - 2^{-i}) • P i`
    have hs : ∀ i, i ≤ n → x - ∑ j ∈ Finset.range i, w j ∈ (2 - ((2 : ℝ) ^ i)⁻¹) • P i := by
      intro i
      induction i with
      | zero =>
        intro _
        norm_num
        exact hxP
      | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        have hwi : w i ∈ W' i := hw i (by omega)
        have hwP : -w i ∈ ((2 : ℝ) ^ (i + 1))⁻¹ • P (i + 1) := by
          obtain ⟨p, hp, hpe⟩ := Set.mem_smul_set.mp hwi.2
          refine ⟨-p, (hPb (i + 1)).neg_mem_iff.mpr hp, ?_⟩
          show ((2 : ℝ) ^ (i + 1))⁻¹ • (-p) = -w i
          rw [smul_neg, hpe]
        have hsP := smul_set_mono' (hPmono i) _ h1
        have hsum := Set.add_mem_add hsP hwP
        rw [← (hPc (i + 1)).add_smul (by
            have : ((2 : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
            linarith) (by positivity)] at hsum
        have hscal : (2 - ((2 : ℝ) ^ i)⁻¹) + ((2 : ℝ) ^ (i + 1))⁻¹ =
            2 - ((2 : ℝ) ^ (i + 1))⁻¹ := by
          rw [pow_succ]; field_simp; ring
        rw [hscal] at hsum
        rw [Finset.sum_range_succ, ← sub_sub]
        simpa [sub_eq_add_neg] using hsum
    have hs2 : ∀ i, i ≤ n → x - ∑ j ∈ Finset.range i, w j ∈ (2 : ℝ) • P i := fun i hi =>
      smul_subset_smul_of_le (hPb i) (by
          have : ((2 : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
          linarith) (by have : (0 : ℝ) ≤ ((2 : ℝ) ^ i)⁻¹ := by positivity
                        linarith) (hs i hi)
    -- downward induction on the tails
    have htail : ∀ d i, i + d + 1 = n → x - ∑ j ∈ Finset.range i, w j ∈ Z i := by
      intro d
      induction d with
      | zero =>
        intro i hi
        have : x - ∑ j ∈ Finset.range i, w j = w i := by
          rw [hxsum, ← hi, show i + 0 + 1 = i + 1 by omega, Finset.sum_range_succ]; abel
        rw [this]
        exact (hw i (by omega)).1.1
      | succ d ih =>
        intro i hi
        have hnext := ih (i + 1) (by omega)
        have hwi : w i ∈ W' i := hw i (by omega)
        have hdecomp : x - ∑ j ∈ Finset.range i, w j =
            w i + (x - ∑ j ∈ Finset.range (i + 1), w j) := by
          rw [Finset.sum_range_succ]; abel
        have hZ2 : x - ∑ j ∈ Finset.range i, w j ∈ (2 : ℝ) • Z (i + 1) := by
          rw [hdecomp]; exact add_mem_two_smul (hZinv (i + 1)).2.2 hwi.1.2 hnext
        have hP2 := hs2 i (by omega)
        obtain ⟨a, ha, hae⟩ := Set.mem_smul_set.mp hP2
        obtain ⟨b, hb, hbe⟩ := Set.mem_smul_set.mp hZ2
        have hab : a = b := by
          have := hae.trans hbe.symm
          exact smul_right_injective Y (by norm_num : (2 : ℝ) ≠ 0) this
        subst hab
        obtain ⟨z, hz, hze⟩ := Set.mem_smul_set.mp (hZrel i ⟨ha, hb⟩)
        rw [← hae, ← hze, smul_smul]
        norm_num
        exact hz
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp at hxsum
      rw [hxsum]
      exact S.zero_mem hWN
    · have := htail (n - 1) 0 (by omega)
      simpa [hZ0] using this

end RetakhLoc

/-! ## Concrete part: the quotient spectrum of a strict LF-space

The four lemmas `continuous_into_seminorms`, `exists_withSeminorms`,
`unitBall_mem_nhds_of_withSeminorms`, `mem_nhds_zero_of_inductive` are copied from the accepted
proof of `MasulloGRH.open_mapping_LF` (namespace `OpenMappingLF`). -/

namespace RetakhConcrete

open MasulloGRH RetakhLoc

theorem continuous_into_seminorms {A F I : Type*} [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [AddCommGroup F] [Module ℂ F]
    {τ : TopologicalSpace F} {q : SeminormFamily ℂ F I}
    (hq : WithSeminorms (topology := τ) q) (f : A →ₗ[ℂ] F)
    (h : ∀ i, Continuous ((q i).comp f)) : @Continuous A F _ τ f := by
  let := τ
  exact hq.continuous_of_continuous_comp f h

theorem exists_withSeminorms {F I : Type*} [AddCommGroup F] [Module ℂ F] [Nonempty I]
    (q : SeminormFamily ℂ F I) : ∃ τ : TopologicalSpace F, WithSeminorms (topology := τ) q := by
  let τ : TopologicalSpace F := q.moduleFilterBasis.topology
  exact ⟨τ, ⟨rfl⟩⟩

theorem unitBall_mem_nhds_of_withSeminorms {F I : Type*} [AddCommGroup F] [Module ℂ F]
    [Nonempty I] {τ : TopologicalSpace F} {q : SeminormFamily ℂ F I}
    (hq : WithSeminorms (topology := τ) q) (i : I) : {x : F | q i x < 1} ∈ @nhds F τ 0 := by
  let := τ
  have hc : Continuous (q i) := hq.continuous_seminorm i
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

/-- **Neighbourhoods of `0` in a locally convex inductive limit.**  If `E` carries the finest
locally convex topology making the linear maps `i m : A m → E` continuous, then a balanced, convex,
absorbent set whose preimage under every `i m` is a `0`-neighbourhood is a `0`-neighbourhood. -/
theorem mem_nhds_zero_of_inductive {E : Type*} [AddCommGroup E] [Module ℂ E]
    [tE : TopologicalSpace E] (hlc : IsLocallyConvexTopology E tE)
    {A : ℕ → Type*} [∀ m, AddCommGroup (A m)] [∀ m, Module ℂ (A m)]
    [∀ m, TopologicalSpace (A m)] [∀ m, IsTopologicalAddGroup (A m)]
    [∀ m, ContinuousSMul ℂ (A m)] (i : ∀ m, A m →ₗ[ℂ] E)
    (htop : tE = sInf {t | IsLocallyConvexTopology E t ∧ ∀ m, @Continuous (A m) E _ t (i m)})
    (W : Set E) (hWb : Balanced ℂ W) (hWc : Convex ℝ W) (hWa : Absorbent ℝ W)
    (hW : ∀ m, (i m) ⁻¹' W ∈ 𝓝 (0 : A m)) : W ∈ 𝓝 (0 : E) := by
  obtain ⟨ι, _, p, hp⟩ := hlc
  have hi : ∀ m, Continuous (i m) := by
    intro m
    have h : @Continuous (A m) E _
        (sInf {t | IsLocallyConvexTopology E t ∧ ∀ m, @Continuous (A m) E _ t (i m)}) (i m) :=
      continuous_sInf_rng.2 fun t ht => ht.2 m
    rw [htop]
    exact h
  have h0W : (0 : E) ∈ W := by simpa using mem_of_mem_nhds (hW 0)
  let g : Seminorm ℂ E := gaugeSeminorm hWb hWc hWa
  have hg : ∀ x, g x = gauge W x := fun _ => rfl
  have hgW : {x : E | g x < 1} ⊆ W := fun x hx =>
    setOfPred_gauge_lt_one_subset_self hWc h0W hWa (by simpa [hg] using hx)
  let p' : SeminormFamily ℂ E (Option ι) := fun o => o.elim g p
  have hcomp : ∀ m (o : Option ι), Continuous ((p' o).comp (i m)) := by
    intro m o
    cases o with
    | none =>
      refine Seminorm.continuous' (r := 1) (mem_of_superset (hW m) fun x hx => ?_)
      rw [Seminorm.mem_closedBall_zero]
      exact gauge_le_one_of_mem hx
    | some k =>
      exact (hp.continuous_seminorm k).comp (hi m)
  have hunit : {x : E | p' none x < 1} ⊆ W := hgW
  obtain ⟨τ', hτ'⟩ := exists_withSeminorms p'
  have hin : ∀ m, @Continuous (A m) E _ τ' (i m) := fun m =>
    continuous_into_seminorms hτ' (i m) (hcomp m)
  have hle : tE ≤ τ' := htop.le.trans (sInf_le ⟨⟨Option ι, inferInstance, p', hτ'⟩, hin⟩)
  exact mem_of_superset (nhds_mono hle (unitBall_mem_nhds_of_withSeminorms hτ' none)) hunit

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]

instance instContinuousSMulRealSub (X' : Submodule ℂ E) : ContinuousSMul ℝ X' :=
  IsScalarTower.continuousSMul (M := ℝ) (α := X') ℂ

/-- The trace of a subset of the quotient on the `k`-th step. -/
def lev (X : ℕ → Submodule ℂ E) (V : Submodule ℂ E) (k : ℕ) (S : Set (E ⧸ V)) : Set (X k) :=
  {z | V.mkQ (z : E) ∈ S}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
lemma mkQ_real_smul (V : Submodule ℂ E) (c : ℝ) (x : E) : V.mkQ (c • x) = c • V.mkQ x :=
  LinearMap.map_smul_of_tower V.mkQ c x

/-- The quotient spectrum as abstract data. -/
noncomputable def quotSpec {ι : Type*} [Nonempty ι] (p : SeminormFamily ℂ E ι)
    (hp : WithSeminorms p) (X : ℕ → Submodule ℂ E) (hmono : Monotone X) (V : Submodule ℂ E) :
    Spec (E ⧸ V) where
  L k := V.mkQ '' (X k : Set E)
  N k S := lev X V k S ∈ 𝓝 (0 : X k)
  L_mono i j hij := Set.image_mono (fun x hx => hmono hij hx)
  L_zero i := ⟨0, (X i).zero_mem, map_zero _⟩
  L_add i := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a + b, (X i).add_mem ha hb, map_add _ _ _⟩
  L_smul i c := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨c • a, (X i).smul_of_tower_mem c ha, mkQ_real_smul V c a⟩
  N_mono i S T hS hST := mem_of_superset hS (fun z hz => hST hz)
  N_inter i S T hS hT := inter_mem hS hT
  N_smul i S c hc hS := by
    refine mem_of_superset ((set_smul_mem_nhds_zero_iff hc).mpr hS) ?_
    rintro _ ⟨z, hz, rfl⟩
    show V.mkQ ((c • z : X i) : E) ∈ c • S
    rw [Submodule.coe_smul_of_tower, mkQ_real_smul]
    exact Set.smul_mem_smul_set hz
  N_absconv i S hS := by
    have hp' := LinearMap.withSeminorms_induced hp (X i).subtype
    obtain ⟨⟨s, r⟩, hr, hsub⟩ := hp'.hasBasis_zero_ball.mem_iff.1 hS
    set B := ((s.sup (p.comp (X i).subtype)).ball 0 r) with hB
    have hBb : Balanced ℂ B := Seminorm.balanced_ball_zero _ r
    have hBc : Convex ℝ B := Seminorm.convex_ball _ _ _
    have hBn : B ∈ 𝓝 (0 : X i) := hp'.hasBasis_zero_ball.mem_of_mem (i := (s, r)) hr
    let f : X i →ₗ[ℂ] E ⧸ V := V.mkQ ∘ₗ (X i).subtype
    refine ⟨f '' B, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩; exact hsub hz
    · exact mem_of_superset hBn (fun z hz => ⟨z, hz, rfl⟩)
    · intro a ha
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨a • z, hBb.smul_mem ha hz, map_smul f a z⟩
    · exact hBc.linear_image (f.restrictScalars ℝ)
  N_absorb i S hS := by
    rintro _ ⟨x, hx, rfl⟩
    have ht : Tendsto (fun q : ℕ => ((2 : ℝ) ^ q)⁻¹ • (⟨x, hx⟩ : X i)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun q : ℕ => ((2 : ℝ) ^ q)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
      simpa using h1.smul_const (⟨x, hx⟩ : X i)
    obtain ⟨q, hq⟩ := (ht.eventually hS).exists
    refine ⟨q, ?_⟩
    have : V.mkQ ((((2 : ℝ) ^ q)⁻¹ • (⟨x, hx⟩ : X i) : X i) : E) ∈ S := hq
    rwa [Submodule.coe_smul_of_tower, mkQ_real_smul] at this
  N_le i j S hij hS := by
    have hc : Continuous (Submodule.inclusion (hmono hij)) :=
      continuous_induced_rng.2 continuous_subtype_val
    have := hc.continuousAt (x := 0) |>.preimage_mem_nhds (by simpa using hS)
    exact this

/-- **Neighbourhoods of `0` in the quotient of a strict LF-space**: an absolutely convex set whose
trace on every step is a `0`-neighbourhood is a `0`-neighbourhood of `E ⧸ V`. -/
lemma quot_mem_nhds (hlc : IsLocallyConvexTopology E ‹_›)
    (X : ℕ → Submodule ℂ E) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (G : Set (E ⧸ V)) (hGb : Balanced ℂ G) (hGc : Convex ℝ G)
    (hGN : ∀ k, lev X V k G ∈ 𝓝 (0 : X k)) : G ∈ 𝓝 (0 : E ⧸ V) := by
  set D : Set E := V.mkQ ⁻¹' G with hD
  have hDb : Balanced ℂ D := by
    intro a ha
    rintro _ ⟨x, hx, rfl⟩
    show V.mkQ (a • x) ∈ G
    rw [map_smul]; exact hGb.smul_mem ha hx
  have hDc : Convex ℝ D := hGc.linear_preimage (V.mkQ.restrictScalars ℝ)
  have hDa : Absorbent ℝ D := by
    intro x
    obtain ⟨k, hk⟩ := hexh x
    have hab : Absorbent ℝ (lev X V k G) := absorbent_nhds_zero (hGN k)
    obtain ⟨r, hr⟩ := absorbs_iff_norm.mp (hab ⟨x, hk⟩)
    refine absorbs_iff_norm.mpr ⟨r, fun c hc => ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨z, hz, hze⟩ := Set.mem_smul_set.mp (hr c hc (Set.mem_singleton _))
    refine ⟨(z : E), hz, ?_⟩
    have := congrArg Subtype.val hze
    simpa using this
  have hDn : ∀ m, (X m).subtype ⁻¹' D ∈ 𝓝 (0 : X m) := fun m => hGN m
  have hDnhds : D ∈ 𝓝 (0 : E) :=
    mem_nhds_zero_of_inductive hlc (A := fun m => X m) (fun m => (X m).subtype) htop D hDb hDc
      hDa hDn
  have himg : V.mkQ '' D = G := Set.image_preimage_eq G (Submodule.mkQ_surjective V)
  have := (Submodule.isOpenMap_mkQ V).image_mem_nhds hDnhds
  rw [himg, map_zero] at this
  exact this

end RetakhConcrete

open MasulloGRH RetakhLoc RetakhConcrete in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hM : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ W ∈ nhds (0 : X m),
      ∃ G ∈ nhds (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by
  obtain ⟨hHLCS, -⟩ :=
    MasulloGRH.bounded_in_strict_frechet_stages E X hmono hexh (fun n => (hX n).1) htop
  obtain ⟨hlc, -⟩ := hHLCS
  have hlc' := hlc
  obtain ⟨ι, hne, p, hp⟩ := hlc
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  set S := quotSpec p hp X hmono V with hS
  choose m hnm U hU hMU using hM
  -- absolutely convex shrinking of the neighbourhoods `U a`
  have hshrink : ∀ a, ∃ U0 ⊆ U a, U0 ∈ 𝓝 (0 : X a) ∧ Balanced ℂ U0 ∧ Convex ℝ U0 := by
    intro a
    have hp' := LinearMap.withSeminorms_induced hp (X a).subtype
    obtain ⟨⟨s, r⟩, hr, hsub⟩ := hp'.hasBasis_zero_ball.mem_iff.1 (hU a)
    exact ⟨_, hsub, hp'.hasBasis_zero_ball.mem_of_mem (i := (s, r)) hr,
      Seminorm.balanced_ball_zero _ r, Seminorm.convex_ball _ _ _⟩
  choose U0 hU0U hU0N hU0b hU0c using hshrink
  let f : ∀ a, X a →ₗ[ℂ] E ⧸ V := fun a => V.mkQ ∘ₗ (X a).subtype
  have hf : ∀ a (z : X a), f a z = V.mkQ (z : E) := fun a z => rfl
  let Qs : ℕ → Set (E ⧸ V) := fun a => f a '' U0 a
  have hQsL : ∀ a, Qs a ⊆ S.L a := by
    rintro a _ ⟨z, -, rfl⟩; exact ⟨z, z.2, rfl⟩
  have hQsb : ∀ a, Balanced ℂ (Qs a) := by
    intro a c hc
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨c • z, (hU0b a).smul_mem hc hz, map_smul (f a) c z⟩
  have hQsc : ∀ a, Convex ℝ (Qs a) := fun a => (hU0c a).linear_image ((f a).restrictScalars ℝ)
  have hQsN : ∀ a, S.N a (Qs a) := fun a =>
    mem_of_superset (hU0N a) (fun z hz => ⟨z, hz, rfl⟩)
  -- condition (M) as goodness
  have hgood : ∀ a k, m a ≤ k → Good S (m a) k (Qs a) := by
    intro a k hk W hW
    obtain ⟨W', hW'N, hW'⟩ := hMU a k hk (lev X V (m a) W) hW
    refine ⟨f k '' W', mem_of_superset hW'N (fun z hz => ⟨z, hz, rfl⟩), ?_⟩
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have hsub : ((x : E) - (y : E)) ∈ V := by
      rw [hf, hf] at hxy
      exact (Submodule.Quotient.eq V).mp hxy.symm
    obtain ⟨w, hw, hxw⟩ := hW' x (hU0U a hx) y hy hsub
    have hxwq : V.mkQ (x : E) = V.mkQ (w : E) := (Submodule.Quotient.eq V).mpr hxw
    show f a x ∈ W
    rw [hf, hxwq]
    exact hw
  intro n0
  -- a cofinal subsequence of levels
  let ℓ : ℕ → ℕ := fun j => Nat.rec n0 (fun _ lj => max (m lj) (lj + 1)) j
  have hℓ0 : ℓ 0 = n0 := rfl
  have hℓs : ∀ j, ℓ (j + 1) = max (m (ℓ j)) (ℓ j + 1) := fun j => rfl
  have hℓmono : Monotone ℓ := monotone_nat_of_le_succ (fun j => by rw [hℓs]; omega)
  have hℓge : ∀ j, j ≤ ℓ j := by
    intro j
    induction j with
    | zero => omega
    | succ j ih => rw [hℓs]; omega
  have hmℓ : ∀ j, m (ℓ j) ≤ ℓ (j + 1) := fun j => by rw [hℓs]; exact le_max_left _ _
  let Q : ℕ → Set (E ⧸ V) := fun j => Qs (ℓ j)
  have hQg : ∀ j, Good S (ℓ (j + 1)) (ℓ (j + 2)) (Q j) := fun j =>
    good_raise S (hgood (ℓ j) (ℓ (j + 2)) ((hmℓ j).trans (hℓmono (show j + 1 ≤ j + 2 by omega)))) (hmℓ j)
  obtain ⟨P, hP0, hPmono, -, hPb, hPc, hPN, hPg⟩ :=
    nest S ℓ hℓmono Q (fun j => hQsL _) (fun j => hQsb _) (fun j => hQsc _) (fun j => hQsN _) hQg
  refine ⟨m n0, hnm n0, U0 n0, hU0N n0, ?_⟩
  intro W hW
  have hSW : S.N (m n0) (f (m n0) '' W) := mem_of_superset hW (fun z hz => ⟨z, hz, rfl⟩)
  obtain ⟨W1, hW1N, hW1⟩ :=
    hgood n0 (ℓ 1) (hmℓ 0) _ hSW
  obtain ⟨W1', hW1'W1, hW1'N, hW1'b, hW1'c⟩ := S.N_absconv _ _ hW1N
  obtain ⟨G, hGb, hGc, hGN, hPG⟩ :=
    localize S ℓ hℓmono P hPmono hPb hPc hPN hPg W1' hW1'N hW1'b hW1'c
  have hGall : ∀ k, lev X V k G ∈ 𝓝 (0 : X k) := fun k =>
    S.N_le k (ℓ (k + 1)) G ((hℓge (k + 1)).trans' (by omega)) (hGN k)
  refine ⟨G, quot_mem_nhds hlc' X hexh htop V G hGb hGc hGall, ?_⟩
  intro x hx hxG
  have hxQ : V.mkQ (x : E) ∈ P 0 := by
    rw [hP0]; exact ⟨x, hx, rfl⟩
  have h1 : V.mkQ (x : E) ∈ W1 := hW1'W1 (hPG ⟨hxQ, hxG⟩)
  obtain ⟨w, hw, hwe⟩ := hW1 ⟨(⟨x, hx, rfl⟩ : V.mkQ (x : E) ∈ Qs n0), h1⟩
  refine ⟨w, hw, ?_⟩
  rw [hf] at hwe
  exact (Submodule.Quotient.eq V).mp hwe.symm
