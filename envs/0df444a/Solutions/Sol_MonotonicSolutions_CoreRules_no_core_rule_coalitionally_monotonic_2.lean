-- Prove2me | solution 2 for MonotonicSolutions.CoreRules.no_core_rule_coalitionally_monotonic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:48:15.442589+00:00
-- url     : https://prove2.me/submissions/c55356e2-4f13-4114-a348-5b9156728da9

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoreRule
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoalitionallyMonotonic
import Definitions.Def_MonotonicSolutions_CoreRules_YoungGames
import Theorems.Thm_MonotonicSolutions_CoreRules_coalitionallyMonotonic_iff_player

-- carved verbatim out of submission 1cdbb021-57b3-4244-971a-89967e80d959, lines 246-250

section
open MonotonicSolutions
open MonotonicSolutions.CoreRules

def NF (val : Fin 5 → ℕ) (top : ℕ) (S : Finset (Fin 5)) : ℕ :=
  if S = Finset.univ then top
  else (Finset.univ.filter (fun k => youngCoalition k ⊆ S)).sup val

lemma youngMaxFun_eq (val : Fin 5 → ℕ) (top : ℕ) (S : Finset (Fin 5)) :
    youngMaxFun val top S = (NF val top S : ℝ) := by
  unfold youngMaxFun NF; split_ifs <;> rfl

def xN : Fin 5 → ℕ := ![0, 1, 2, 7, 1]

def yN : Fin 5 → ℕ := ![3, 0, 0, 6, 3]

lemma chk_x : ∀ T : Finset (Fin 5), NF ![3, 3, 9, 9, 9] 11 T ≤ ∑ k ∈ T, xN k := by decide

lemma chk_y : ∀ T : Finset (Fin 5), NF ![3, 3, 9, 9, 12] 12 T ≤ ∑ k ∈ T, yN k := by decide

lemma chk_cmp : ∀ T : Finset (Fin 5), (1 ∈ T → NF ![3, 3, 9, 9, 9] 11 T ≤ NF ![3, 3, 9, 9, 12] 12 T) ∧
    (1 ∉ T → NF ![3, 3, 9, 9, 12] 12 T = NF ![3, 3, 9, 9, 9] 11 T) := by decide

end

section
open MonotonicSolutions
open MonotonicSolutions.CoreRules
variable {n : ℕ} (hn : 5 ≤ n)

def eE : Fin 5 ↪ Fin n := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩

def pre (S : Finset (Fin n)) : Finset (Fin 5) :=
  Finset.univ.filter (fun k => Fin.castLE hn k ∈ S)

def GG (val : Fin 5 → ℕ) (top : ℕ) : Game n :=
  ⟨fun S => youngMaxFun val top (pre hn S), by
    have : pre hn (∅ : Finset (Fin n)) = ∅ := by simp [pre]
    show youngMaxFun val top (pre hn ∅) = 0
    rw [this]; exact youngMaxFun_empty val top⟩

lemma pre_map (T : Finset (Fin 5)) : pre hn (T.map (eE hn)) = T := by
  ext k; simp [pre, eE]

lemma pre_univ : pre hn (Finset.univ : Finset (Fin n)) = Finset.univ := by
  ext k; simp [pre]

lemma NF_univ (val : Fin 5 → ℕ) (top : ℕ) : NF val top Finset.univ = top := by
  simp [NF]

lemma core_restrict (val : Fin 5 → ℕ) (top : ℕ) (z : Fin n → ℝ)
    (hz : z ∈ Supermodularity.Cooperative.Core Finset.univ (GG hn val top).1) :
    (∀ T : Finset (Fin 5), (NF val top T : ℝ) ≤ ∑ k ∈ T, z (Fin.castLE hn k)) ∧
      ∑ k, z (Fin.castLE hn k) ≤ top := by
  classical
  obtain ⟨hsum, hS⟩ := hz
  constructor
  · intro T
    have h := hS (T.map (eE hn)) (Finset.subset_univ _)
    simp only [GG, pre_map] at h
    rw [youngMaxFun_eq, Finset.sum_map] at h
    simpa [eE] using h
  · simp only [GG, pre_univ] at hsum
    rw [youngMaxFun_eq, NF_univ] at hsum
    have hsplit := Finset.sum_sdiff (s₁ := Finset.univ.map (eE hn)) (s₂ := Finset.univ)
      (f := z) (Finset.subset_univ _)
    have hnn : 0 ≤ ∑ j ∈ Finset.univ \ Finset.univ.map (eE hn), z j := by
      apply Finset.sum_nonneg
      intro j hj
      have hj' : ∀ k : Fin 5, Fin.castLE hn k ≠ j := by
        intro k hk
        apply (Finset.mem_sdiff.mp hj).2
        rw [Finset.mem_map]; exact ⟨k, Finset.mem_univ _, hk⟩
      have h := hS {j} (Finset.subset_univ _)
      have hp : pre hn {j} = ∅ := by
        ext k; simp [pre, hj' k]
      simp only [GG, hp] at h
      rw [youngMaxFun_empty] at h
      simpa using h
    rw [Finset.sum_map] at hsplit
    have : ∑ k, z (Fin.castLE hn k) = ∑ x : Fin 5, z ((eE hn) x) := rfl
    linarith

lemma core_ext (val : Fin 5 → ℕ) (top : ℕ) (x5 : Fin 5 → ℕ)
    (hx : ∀ T, NF val top T ≤ ∑ k ∈ T, x5 k) (htop : ∑ k, x5 k = top) :
    (Supermodularity.Cooperative.Core Finset.univ (GG hn val top).1).Nonempty := by
  classical
  let x' : Fin n → ℝ := fun j => if h : j.val < 5 then (x5 ⟨j.val, h⟩ : ℝ) else 0
  have key : ∀ S : Finset (Fin n), ∑ j ∈ S, x' j = ((∑ k ∈ pre hn S, x5 k : ℕ) : ℝ) := by
    intro S
    push_cast
    have h1 : ∑ k ∈ pre hn S, (x5 k : ℝ) = ∑ j ∈ (pre hn S).map (eE hn), x' j := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro k _
      simp [x', eE, k.isLt]
    rw [h1]
    symm
    apply Finset.sum_subset
    · intro j hj
      rw [Finset.mem_map] at hj
      obtain ⟨k, hk, rfl⟩ := hj
      simpa [pre, eE] using hk
    · intro j hjS hj
      simp only [x']
      split_ifs with h
      · exfalso; apply hj
        rw [Finset.mem_map]
        refine ⟨⟨j.val, h⟩, ?_, ?_⟩
        · simp [pre]; convert hjS
        · ext; simp [eE]
      · rfl
  refine ⟨x', ?_, ?_⟩
  · rw [key]; simp only [GG, pre_univ]; rw [youngMaxFun_eq, NF_univ, htop]
  · intro S _
    rw [key]; simp only [GG]; rw [youngMaxFun_eq]
    exact_mod_cast hx (pre hn S)

end

section
open MonotonicSolutions
open MonotonicSolutions.CoreRules

theorem noCM_core {n : ℕ} (hn : 5 ≤ n) (φ : Game n → Fin n → ℝ) (_hA : IsAllocationProcedure φ)
    (hC : IsCoreRule φ) (hM : IsCoalitionallyMonotonic φ) : False := by
  have hW := hC (GG hn ![3, 3, 9, 9, 9] 11)
    (core_ext hn _ _ xN chk_x (by decide))
  have hV := hC (GG hn ![3, 3, 9, 9, 12] 12)
    (core_ext hn _ _ yN chk_y (by decide))
  obtain ⟨hW1, hW2⟩ := core_restrict hn _ _ _ hW
  obtain ⟨hV1, hV2⟩ := core_restrict hn _ _ _ hV
  have hmono := (MonotonicSolutions.CoreRules.coalitionallyMonotonic_iff_player φ).mp hM (Fin.castLE hn 1)
    (GG hn ![3, 3, 9, 9, 12] 12) (GG hn ![3, 3, 9, 9, 9] 11)
    (by
      intro S hS
      simp only [GG]; rw [youngMaxFun_eq, youngMaxFun_eq]
      have : (1 : Fin 5) ∈ pre hn S := by simpa [pre] using hS
      exact_mod_cast (chk_cmp (pre hn S)).1 this)
    (by
      intro S hS
      simp only [GG]; rw [youngMaxFun_eq, youngMaxFun_eq]
      have : (1 : Fin 5) ∉ pre hn S := by simpa [pre] using hS
      exact_mod_cast (chk_cmp (pre hn S)).2 this)
  set a := φ (GG hn ![3, 3, 9, 9, 9] 11) with ha
  set b := φ (GG hn ![3, 3, 9, 9, 12] 12) with hb
  clear_value a b
  have w1 := hW1 {1, 3, 4}
  have w2 := hW1 {0, 1, 2}
  have v1 := hV1 {0, 2, 3}
  have v2 := hV1 {2, 4}
  have v3 := hV1 {0, 1, 3, 4}
  rw [show NF ![3, 3, 9, 9, 9] 11 {1, 3, 4} = 9 by decide] at w1
  rw [show NF ![3, 3, 9, 9, 9] 11 {0, 1, 2} = 3 by decide] at w2
  rw [show NF ![3, 3, 9, 9, 12] 12 {0, 2, 3} = 9 by decide] at v1
  rw [show NF ![3, 3, 9, 9, 12] 12 {2, 4} = 3 by decide] at v2
  rw [show NF ![3, 3, 9, 9, 12] 12 {0, 1, 3, 4} = 12 by decide] at v3
  simp [Finset.sum_insert, Fin.sum_univ_five] at w1 w2 v1 v2 v3 hW2 hV2
  have e1 : (Fin.castLE hn (1 : Fin 5)) = Fin.castLE hn 1 := rfl
  linarith

theorem noCM_general (n : ℕ) (hn : 5 ≤ n) :
    ¬ ∃ φ : Game n → Fin n → ℝ,
      IsAllocationProcedure φ ∧ IsCoreRule φ ∧ IsCoalitionallyMonotonic φ := by
  rintro ⟨φ, hA, hC, hM⟩
  exact noCM_core hn φ hA hC hM

end

section
open MonotonicSolutions.CoreRules

theorem solution (n : ℕ) (hn : 5 ≤ n) :
    ¬ ∃ φ : Game n → Fin n → ℝ,
      IsAllocationProcedure φ ∧ IsCoreRule φ ∧ IsCoalitionallyMonotonic φ := by
  exact noCM_general n hn

end
