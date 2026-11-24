-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:27.421958+00:00
-- url     : https://prove2.me/submissions/b48876d8-827c-40cc-9d0b-b8e98d3d3763

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_val_mul_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_val_entry_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_val_diag
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_exists_mem_iwahori
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_val_pw_le
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.IwContract
theorem _root_.solution {ϖ : Fˣ} (hϖ : IsUniformiser (ϖ : F)) {a : Fin n → ℤ} (ha : StrictlyDominant a)
    {r : ValueGroupWithZero F} {c : GL (Fin n) F} (hc : Near r c) :
    ∃ m ∈ GlobalTheory.SmGL.iwahori F (Fin n), ∃ c' : GL (Fin n) F, Near (r * valuation F (ϖ : F)) c' ∧
      (diagPow ϖ a * c) * m = m * (diagPow ϖ a * c') := by
  classical
  have hq : valuation F (ϖ : F) < 1 := hϖ.1
  set q := valuation F (ϖ : F) with hqdef
  set D : Fin n → F := fun i => c.val i i with hDdef
  have hD : ∀ i, valuation F (D i) = 1 := val_diag hc.1
  have hD0 : ∀ i, D i ≠ 0 := fun i h => by
    have := hD i
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hc1 : ∀ i j, valuation F (c.val i j) ≤ 1 := val_entry_le_one hc.1
  have hlow : ∀ i j, j < i → valuation F (c.val i j) ≤ q := fun i j hij =>
    hϖ.2.2 _ ((GlobalTheory.SmGL.mem_iwahori.1 hc.1).2 i j hij)
  let p : Fin n → Fin n → F := fun i j => ((ϖ ^ (a i - a j) : Fˣ) : F)
  have hp : ∀ i j, i < j → valuation F (p i j) ≤ q := fun i j hij => val_pw_le hq ha hij
  let E : Matrix (Fin n) (Fin n) F := fun i j =>
    if i < j then p i j * c.val i j / D j else if j < i then -c.val i j / D i else 0
  let E' : Matrix (Fin n) (Fin n) F := fun i j =>
    if i < j then c.val i j / D j else if j < i then -(p j i * c.val i j) / D i else 0
  have hEu : ∀ i j, i < j → E i j = p i j * c.val i j / D j := fun i j h => if_pos h
  have hEl : ∀ i j, j < i → E i j = -c.val i j / D i := fun i j h => by
    show (if i < j then _ else _) = _
    rw [if_neg h.not_gt, if_pos h]
  have hEd : ∀ i, E i i = 0 := fun i => by
    show (if i < i then _ else _) = _
    rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  have hE'u : ∀ i j, i < j → E' i j = c.val i j / D j := fun i j h => if_pos h
  have hE'l : ∀ i j, j < i → E' i j = -(p j i * c.val i j) / D i := fun i j h => by
    show (if i < j then _ else _) = _
    rw [if_neg h.not_gt, if_pos h]
  have hE'd : ∀ i, E' i i = 0 := fun i => by
    show (if i < i then _ else _) = _
    rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  have hq1 : q ≤ 1 := hq.le
  have hE : ∀ i j, valuation F (E i j) ≤ q := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hEu i j h, map_div₀, hD, div_one, map_mul]
      exact (mul_le_mul' (hp i j h) (hc1 i j)).trans_eq (mul_one _)
    · rw [hEd, map_zero]; exact zero_le'
    · rw [hEl i j h, map_div₀, hD, div_one, Valuation.map_neg]
      exact hlow i j h
  have hE'1 : ∀ i j, valuation F (E' i j) ≤ 1 := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hE'u i j h, map_div₀, hD, div_one]
      exact hc1 i j
    · rw [hE'd, map_zero]; exact zero_le'
    · rw [hE'l i j h, map_div₀, hD, div_one, Valuation.map_neg, map_mul]
      exact (mul_le_mul' ((hp j i h).trans hq1) (hc1 i j)).trans_eq (mul_one _)
  have hE'low : ∀ i j, j < i → valuation F (E' i j) < 1 := by
    intro i j h
    rw [hE'l i j h, map_div₀, hD, div_one, Valuation.map_neg, map_mul]
    exact lt_of_le_of_lt ((mul_le_mul' (hp j i h) (hc1 i j)).trans_eq (mul_one _)) hq
  have one_add : ∀ (G : Matrix (Fin n) (Fin n) F), (∀ i, G i i = 0) → (∀ i j, valuation F (G i j) ≤ 1) →
      (∀ i j, j < i → valuation F (G i j) < 1) →
      ∃ g ∈ GlobalTheory.SmGL.iwahori F (Fin n), g.val = 1 + G := by
    intro G h0 h1 h2
    refine exists_mem_iwahori _ (fun i j => ?_) (fun i j hij => ?_) fun i => ?_
    · rw [Matrix.add_apply]
      refine Valuation.map_add_le _ ?_ (h1 i j)
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    · rw [Matrix.add_apply, Matrix.one_apply_ne hij.ne', zero_add]
      exact h2 i j hij
    · rw [Matrix.add_apply, h0, add_zero, Matrix.one_apply_eq, map_one]
  obtain ⟨m, hm, hmv⟩ := one_add E hEd (fun i j => (hE i j).trans hq1)
    (fun i j h => lt_of_le_of_lt (hE i j) hq)
  obtain ⟨m', hm', hm'v⟩ := one_add E' hE'd hE'1 hE'low
  have hx : diagPow ϖ a * m' = m * diagPow ϖ a := by
    apply Units.ext
    have hxv : (diagPow ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : Fˣ) : F) := rfl
    rw [Units.val_mul, Units.val_mul, hmv, hm'v, hxv]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.add_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · have e : ((ϖ ^ a i : Fˣ) : F) = p i j * ((ϖ ^ a j : Fˣ) : F) := by
        show _ = ((ϖ ^ (a i - a j) : Fˣ) : F) * _
        rw [← Units.val_mul, ← _root_.zpow_add]
        simp
      rw [Matrix.one_apply_ne h.ne, zero_add, zero_add, hE'u i j h, hEu i j h, e]
      ring
    · rw [hE'd, hEd]
      ring
    · have e : ((ϖ ^ a j : Fˣ) : F) = p j i * ((ϖ ^ a i : Fˣ) : F) := by
        show _ = ((ϖ ^ (a j - a i) : Fˣ) : F) * _
        rw [← Units.val_mul, ← _root_.zpow_add]
        simp
      rw [Matrix.one_apply_ne h.ne', zero_add, zero_add, hE'l i j h, hEl i j h, e]
      ring
  refine ⟨m, hm, m'⁻¹ * c * m, ⟨mul_mem (mul_mem (inv_mem hm') hc.1) hm, ?_⟩, ?_⟩
  · intro i j hij
    obtain ⟨Dg, hDg⟩ : ∃ Dg : Matrix (Fin n) (Fin n) F, Dg = Matrix.diagonal D := ⟨_, rfl⟩
    obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin n) (Fin n) F, W = c.val * (1 + E) - (1 + E') * Dg := ⟨_, rfl⟩
    have hval : (m'⁻¹ * c * m).val = Dg + (m'⁻¹).val * W := by
      have h1 : (m'⁻¹).val * (1 + E') = 1 := by
        rw [← hm'v, ← Units.val_mul]
        simp
      have h2 : (m'⁻¹ * c * m).val = (m'⁻¹).val * (c.val * (1 + E)) := by
        rw [Units.val_mul, Units.val_mul, hmv, mul_assoc]
      rw [h2, hW, mul_sub, ← mul_assoc (m'⁻¹).val (1 + E') Dg, h1, one_mul]
      abel
    have hinv : ∀ i j, valuation F ((m'⁻¹).val i j) ≤ 1 := val_entry_le_one (inv_mem hm')
    have hC : ∀ i j, valuation F ((c.val - Dg) i j) ≤ r := by
      intro i j
      by_cases h : i = j
      · subst h
        rw [hDg, Matrix.sub_apply, Matrix.diagonal_apply_eq, sub_self, map_zero]
        exact zero_le'
      · rw [hDg, Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, sub_zero]
        exact hc.2 i j h
    have hWeq : W = (c.val - Dg) * E + ((c.val - Dg) + Dg * E - E' * Dg) := by
      rw [hW]
      simp only [mul_add, add_mul, mul_one, one_mul, sub_mul]
      abel
    have hWb : ∀ i j, valuation F (W i j) ≤ r * q := by
      intro i j
      rw [hWeq, Matrix.add_apply]
      refine Valuation.map_add_le _ (val_mul_entry hC hE i j) ?_
      rw [Matrix.sub_apply, Matrix.add_apply, hDg, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rcases lt_trichotomy i j with h | rfl | h
      · have e : (c.val - Matrix.diagonal D) i j + D i * E i j - E' i j * D j =
            D i * (p i j * c.val i j / D j) := by
          rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h.ne, sub_zero, hEu i j h, hE'u i j h,
            div_mul_cancel₀ _ (hD0 j)]
          ring
        rw [e, map_mul, hD, one_mul, map_div₀, hD, div_one, map_mul, mul_comm r]
        exact mul_le_mul' (hp i j h) (hc.2 i j h.ne)
      · rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, hEd, hE'd]
        simp [hDdef]
      · have e : (c.val - Matrix.diagonal D) i j + D i * E i j - E' i j * D j =
            p j i * c.val i j * D j / D i := by
          rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h.ne', sub_zero, hEl i j h, hE'l i j h,
            mul_div_cancel₀ _ (hD0 i)]
          ring
        rw [e, map_div₀, hD, div_one, map_mul, map_mul, hD, mul_one, mul_comm r]
        exact mul_le_mul' (hp j i h) (hc.2 i j h.ne')
    have hfin := val_mul_entry hinv hWb i j
    rw [hval, Matrix.add_apply, hDg, Matrix.diagonal_apply_ne _ hij, zero_add]
    simpa using hfin
  · rw [← mul_assoc m, ← hx]
    group
end GlobalTheory.CompanionTheory.IwContract
