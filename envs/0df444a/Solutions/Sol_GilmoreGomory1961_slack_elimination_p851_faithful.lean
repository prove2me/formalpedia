-- Prove2me | solution 1 for GilmoreGomory1961.slack_elimination_p851_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:10:47.470295+00:00
-- url     : https://prove2.me/submissions/2449810d-6094-4f5a-93e9-e890f2d4d829

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Model

open GilmoreGomory61.CuttingStock

namespace GG84

open Classical


variable {m k : ℕ} (I : Instance m k)

/-- surplus column -/
def cr (r : Fin m) : Col I := Sum.inr r

theorem sum_eq_lc (g : Col I → ℝ) (z : Col I →₀ ℝ) :
    (z.sum fun j v => g j * v) = Finsupp.linearCombination ℝ g z := by
  rw [Finsupp.linearCombination_apply]
  simp [smul_eq_mul, mul_comm]

theorem patLen_update_le {i : Fin m} (hℓ : 0 ≤ I.ℓ i) (a : Fin m → ℕ) :
    patLen I (Function.update a i 0) ≤ patLen I a := by
  unfold patLen
  apply Finset.sum_le_sum
  intro r _
  by_cases h : r = i
  · subst h; simp; exact mul_nonneg hℓ (Nat.cast_nonneg _)
  · simp [Function.update_of_ne h]

def zAct (i : Fin m) (hℓ : 0 ≤ I.ℓ i) (p : Activity I) : Activity I :=
  ⟨(p.1.1, Function.update p.1.2 i 0), le_trans (patLen_update_le I hℓ _) p.2⟩

/-- activity column -/
def cl (p : Activity I) : Col I := Sum.inl p

theorem cr_inj {a b : Fin m} : cr I a = cr I b ↔ a = b := Sum.inr_injective.eq_iff
theorem cl_ne_cr (p : Activity I) (r : Fin m) : cl I p ≠ cr I r := Sum.inl_ne_inr

@[simp] theorem colVec_cl (p : Activity I) (r : Fin m) : colVec I (cl I p) r = (p.1.2 r : ℝ) := rfl
@[simp] theorem colVec_cr (r' r : Fin m) : colVec I (cr I r') r = if r = r' then -1 else 0 := rfl
@[simp] theorem colCost_cl (p : Activity I) : colCost I (cl I p) = I.c p.1.1 := rfl
@[simp] theorem colCost_cr (r : Fin m) : colCost I (cr I r) = 0 := rfl

def Zc (i : Fin m) (hℓ : 0 ≤ I.ℓ i) : Col I → Col I
  | Sum.inl p => cl I (zAct I i hℓ p)
  | Sum.inr r => cr I r

theorem colVec_Zc_ne (i : Fin m) (hℓ : 0 ≤ I.ℓ i) (j : Col I) (r : Fin m) (hr : r ≠ i) :
    colVec I (Zc I i hℓ j) r = colVec I j r := by
  cases j with
  | inl p =>
    show colVec I (cl I (zAct I i hℓ p)) r = colVec I (cl I p) r
    rw [colVec_cl, colVec_cl]; simp [zAct, Function.update_of_ne hr]
  | inr r' => rfl

theorem colCost_Zc (i : Fin m) (hℓ : 0 ≤ I.ℓ i) (j : Col I) :
    colCost I (Zc I i hℓ j) = colCost I j := by
  cases j <;> rfl

theorem mapDomain_apply_inr (i : Fin m) (hℓ : 0 ≤ I.ℓ i) (w : Col I →₀ ℝ) (r : Fin m) :
    Finsupp.mapDomain (Zc I i hℓ) w (cr I r) = w (cr I r) := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  by_cases hs : cr I r ∈ w.support
  · rw [Finsupp.sum, Finset.sum_eq_single (cr I r)]
    · show (Finsupp.single (cr I r) (w (cr I r))) (cr I r) = w (cr I r)
      exact Finsupp.single_eq_same
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      cases b with
      | inl p => exact cl_ne_cr I _ r
      | inr r' => intro h; exact hb ((cr_inj I).mp h ▸ rfl)
    · intro h; exact absurd hs h
  · have h0 : w (cr I r) = 0 := by simpa using hs
    rw [h0, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    cases b with
    | inl p => exact cl_ne_cr I _ r h
    | inr r' => have := (cr_inj I).mp h; subst this; exact hs hb

theorem mapDomain_nonneg (f : Col I → Col I) (w : Col I →₀ ℝ) (hw : ∀ j, 0 ≤ w j) (x : Col I) :
    0 ≤ Finsupp.mapDomain f w x := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro b _
  rw [Finsupp.single_apply]; split_ifs
  · exact hw b
  · exact le_refl 0

/-- One elimination step. -/
theorem step (hℓ : ∀ i, 0 < I.ℓ i) (i : Fin m) (S : Finset (Fin m)) (z : Col I →₀ ℝ)
    (hz : Feasible I z) (hS : ∀ r ∈ S, z (cr I r) = 0) :
    ∃ z' : Col I →₀ ℝ, Feasible I z' ∧ cost I z' = cost I z ∧
      ∀ r ∈ insert i S, z' (cr I r) = 0 := by
  have hl : 0 ≤ I.ℓ i := (hℓ i).le
  set s := z (cr I i) with hs_def
  set w : Col I →₀ ℝ := z.erase (cr I i) with hw_def
  have hzw : z = w + (Finsupp.single (cr I i) s : Col I →₀ ℝ) := (Finsupp.erase_add_single _ _).symm
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j; rw [hw_def, Finsupp.erase_apply]; split_ifs
    · exact le_refl 0
    · exact hz.1 j
  -- rows and cost as linear combinations
  let row : Fin m → (Col I →₀ ℝ) → ℝ := fun r v => Finsupp.linearCombination ℝ (fun j => colVec I j r) v
  have hrow : ∀ r v, (v.sum fun j x => colVec I j r * x) = row r v := fun r v => sum_eq_lc I _ v
  have hcost : ∀ v, cost I v = Finsupp.linearCombination ℝ (colCost I) v := fun v => sum_eq_lc I _ v
  have hrowz : ∀ r, row r z = row r w + (if r = i then -1 else 0) * s := by
    intro r
    simp only [row]
    rw [hzw, map_add, Finsupp.linearCombination_single, smul_eq_mul, mul_comm]
    simp [colVec, cr]
  have hcz : cost I z = cost I w := by
    rw [hcost, hcost, hzw, map_add, Finsupp.linearCombination_single]; simp [colCost, cr]
  have hNi : row i w = I.N i + s := by
    have := hz.2 i; rw [hrow, hrowz] at this; simp at this; linarith
  have hs0 : 0 ≤ s := hz.1 _
  set T := row i w
  -- the map
  let D : Col I →₀ ℝ := Finsupp.mapDomain (Zc I i hl) w
  have hrowD : ∀ r, row r D = Finsupp.linearCombination ℝ (fun j => colVec I (Zc I i hl j) r) w := by
    intro r; simp only [row, D]; exact Finsupp.linearCombination_mapDomain _ _ _
  have hrowD_ne : ∀ r, r ≠ i → row r D = row r w := by
    intro r hr; rw [hrowD]; simp only [row]
    have : (fun j => colVec I (Zc I i hl j) r) = (fun j => colVec I j r) := by
      funext j; exact colVec_Zc_ne I i hl j r hr
    rw [this]
  have hrowD_i : row i D = 0 := by
    rw [hrowD, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ cr I i := by
      intro h; rw [h, hw_def, Finsupp.mem_support_iff, Finsupp.erase_same] at hj; exact hj rfl
    cases j with
    | inl p =>
      rw [show Zc I i hl (Sum.inl p) = cl I (zAct I i hl p) from rfl, colVec_cl]
      simp [zAct]
    | inr r' =>
      have : r' ≠ i := fun h => hji (by rw [h]; rfl)
      rw [show Zc I i hl (Sum.inr r') = cr I r' from rfl, colVec_cr]
      simp [Ne.symm this]
  have hcD : Finsupp.linearCombination ℝ (colCost I) D = Finsupp.linearCombination ℝ (colCost I) w := by
    simp only [D]; rw [Finsupp.linearCombination_mapDomain]
    have : (colCost I ∘ Zc I i hl) = colCost I := by funext j; exact colCost_Zc I i hl j
    rw [this]
  by_cases hT : T = 0
  · -- nothing to do: the surplus is already zero
    have : s = 0 := by have := I.N i; have hN : (0:ℝ) ≤ I.N i := Nat.cast_nonneg _; linarith
    refine ⟨z, hz, rfl, ?_⟩
    intro r hr; rcases Finset.mem_insert.mp hr with rfl | hr
    · exact this
    · exact hS r hr
  have hTpos : 0 < T := by
    have hN : (0:ℝ) ≤ I.N i := Nat.cast_nonneg _
    rcases lt_or_eq_of_le (show 0 ≤ T by linarith) with h | h
    · exact h
    · exact absurd h.symm hT
  set θ := (I.N i : ℝ) / T
  have hθ0 : 0 ≤ θ := div_nonneg (Nat.cast_nonneg _) hTpos.le
  have hθ1 : θ ≤ 1 := (div_le_one hTpos).mpr (by linarith)
  refine ⟨θ • w + (1 - θ) • D, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro j
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hθ0 (hw0 j)) (mul_nonneg (by linarith) (mapDomain_nonneg I _ w hw0 j))
  · intro r
    rw [hrow]; simp only [row, map_add, map_smul, smul_eq_mul]
    by_cases hr : r = i
    · subst hr
      show θ * row r w + (1 - θ) * row r D = _
      rw [hrowD_i, mul_zero, add_zero]
      show (I.N r : ℝ) / T * T = _
      field_simp
    · show θ * row r w + (1 - θ) * row r D = _
      rw [hrowD_ne r hr]
      have := hz.2 r; rw [hrow, hrowz] at this; simp [hr] at this
      rw [← this]; ring
  · rw [hcost, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hcD, ← hcost, ← hcz]; ring
  · intro r hr
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [show D (cr I r) = _ from mapDomain_apply_inr I i hl w r]
    rcases Finset.mem_insert.mp hr with rfl | hr
    · simp [hw_def]
    · have : w (cr I r) = 0 := by
        rw [hw_def, Finsupp.erase_apply]; split_ifs
        · rfl
        · exact hS r hr
      rw [this]; ring

end GG84

theorem solution {m k : ℕ} (I : Instance m k)
    (hℓ : ∀ i, 0 < I.ℓ i) (z : Col I →₀ ℝ) (hz : Feasible I z) :
    ∃ z' : Col I →₀ ℝ, Feasible I z' ∧ cost I z' = cost I z ∧
      ∀ i : Fin m, z' (Sum.inr i) = 0 := by
  have key : ∀ S : Finset (Fin m), ∃ z' : Col I →₀ ℝ, Feasible I z' ∧ cost I z' = cost I z ∧
      ∀ r ∈ S, z' (Sum.inr r) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨z, hz, rfl, by simp⟩
    | insert i S _ ih =>
      obtain ⟨z1, h1, c1, s1⟩ := ih
      obtain ⟨z2, h2, c2, s2⟩ := GG84.step I hℓ i S z1 h1 s1
      exact ⟨z2, h2, c2.trans c1, s2⟩
  obtain ⟨z', h1, h2, h3⟩ := key Finset.univ
  exact ⟨z', h1, h2, fun i => h3 i (Finset.mem_univ i)⟩
