-- Prove2me | solution 1 for GroundTheory.Automorphic.rowsReduced_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:17.295801+00:00
-- url     : https://prove2.me/submissions/bbe84898-73d5-4750-a305-9aa128b307c9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_exists_borel_of_isUpperTriangular
import Theorems.Thm_GroundTheory_Automorphic_mul_one_add_vecMulVec_apply
import Theorems.Thm_GroundTheory_Automorphic_one_add_vecMulVec_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
namespace GroundTheory.Automorphic
theorem _root_.solution (h : GL (Fin n) k) (t : ℕ) (ht : t < n)
    (hred : RowsReduced (h : Matrix (Fin n) (Fin n) k) (t + 1)) :
    ∃ b₁ ∈ borel n k, ∃ b₂ ∈ borel n k,
      RowsReduced ((b₁ * h * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) t := by
  classical
  obtain ⟨p, hp⟩ := hred
  set H : Matrix (Fin n) (Fin n) k := (h : Matrix (Fin n) (Fin n) k) with hH
  set i₀ : Fin n := ⟨t, ht⟩ with hi₀
  have hne : ∀ i : Fin n, t + 1 ≤ i.val → i₀ ≠ i := by
    intro i hi e
    have := congrArg Fin.val e
    simp [i₀] at this
    omega

  have hrow : ∃ c, H i₀ c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
      (Matrix.det_eq_zero_of_row_eq_zero i₀ hcon)

  set s := Finset.univ.filter (fun c => H i₀ c ≠ 0) with hs_def
  have hs : s.Nonempty := let ⟨c, hc⟩ := hrow; ⟨c, by simp [s, hc]⟩
  set j := s.min' hs with hj_def
  have hj : H i₀ j ≠ 0 := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hjmin : ∀ c, c < j → H i₀ c = 0 := fun c hc => by
    by_contra hc0
    exact absurd (s.min'_le c (by simp [s, hc0])) (not_le.mpr hc)
  have hpS : ∀ i : Fin n, t + 1 ≤ i.val → H i₀ (p i) = 0 :=
    fun i hi => (hp i hi).2.2 i₀ (hne i hi)
  have hjp : ∀ i : Fin n, t + 1 ≤ i.val → p i ≠ j := fun i hi e => hj (e ▸ hpS i hi)
  have hHj : ∀ r : Fin n, t + 1 ≤ r.val → H r j = 0 :=
    fun r hr => (hp r hr).2.1 j (hjp r hr).symm

  set v : Fin n → k := fun c => if j < c then -(H i₀ c / H i₀ j) else 0 with hv
  set E₂ : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (Pi.single j 1) v with hE₂
  have hE₂up : E₂.IsUpperTriangular := by
    intro a c hca
    replace hca : c < a := hca
    simp only [E₂, Matrix.add_apply, one_apply, vecMulVec_apply, Pi.single_apply]
    rw [if_neg (ne_of_lt hca).symm]
    by_cases haj : a = j
    · subst haj
      simp [v, not_lt.mpr hca.le]
    · simp [haj]
  have hE₂d : ∀ a, E₂ a a ≠ 0 := by
    intro a
    simp only [E₂, Matrix.add_apply, one_apply_eq, vecMulVec_apply, Pi.single_apply]
    by_cases haj : a = j
    · subst haj; simp [v]
    · simp [haj]
  obtain ⟨b₂, hb₂, hb₂E⟩ := exists_borel_of_isUpperTriangular E₂ hE₂up hE₂d
  set M₁ : Matrix (Fin n) (Fin n) k := H * E₂ with hM₁_def
  have hM₁ : ∀ r c, M₁ r c = H r c + H r j * v c := fun r c =>
    mul_one_add_vecMulVec_apply H j v r c
  have hM₁i₀ : ∀ c, M₁ i₀ c = if c = j then H i₀ j else 0 := by
    intro c
    rw [hM₁]
    rcases lt_trichotomy c j with hc | rfl | hc
    · simp [v, hjmin c hc, not_lt.mpr hc.le, (ne_of_lt hc)]
    · simp [v]
    · simp only [v, if_pos hc, if_neg (ne_of_lt hc).symm]
      field_simp
      ring
  have hM₁S : ∀ r : Fin n, t + 1 ≤ r.val → ∀ c, M₁ r c = H r c := by
    intro r hr c
    rw [hM₁, hHj r hr, zero_mul, add_zero]
  have hvp : ∀ i : Fin n, t + 1 ≤ i.val → v (p i) = 0 := by
    intro i hi
    simp [v, hpS i hi]

  set u : Fin n → k := fun r => if r < i₀ then -(M₁ r j / H i₀ j) else 0 with hu_def
  set E₁ : Matrix (Fin n) (Fin n) k := 1 + vecMulVec u (Pi.single i₀ 1) with hE₁
  have hE₁up : E₁.IsUpperTriangular := by
    intro a c hca
    replace hca : c < a := hca
    simp only [E₁, Matrix.add_apply, one_apply, vecMulVec_apply, Pi.single_apply]
    rw [if_neg (ne_of_lt hca).symm]
    by_cases hci : c = i₀
    · subst hci
      simp [u, not_lt.mpr hca.le]
    · simp [hci]
  have hE₁d : ∀ a, E₁ a a ≠ 0 := by
    intro a
    simp only [E₁, Matrix.add_apply, one_apply_eq, vecMulVec_apply, Pi.single_apply]
    by_cases hai : a = i₀
    · subst hai; simp [u]
    · simp [hai]
  obtain ⟨b₁, hb₁, hb₁E⟩ := exists_borel_of_isUpperTriangular E₁ hE₁up hE₁d
  set M₂ : Matrix (Fin n) (Fin n) k := E₁ * M₁ with hM₂_def
  have hM₂ : ∀ r c, M₂ r c = M₁ r c + u r * M₁ i₀ c := fun r c =>
    one_add_vecMulVec_mul_apply M₁ i₀ u r c
  have hu0 : ∀ r : Fin n, t ≤ r.val → u r = 0 := by
    intro r hr
    have : ¬ r < i₀ := by
      rw [Fin.lt_def]
      simp [i₀]
      omega
    simp [u, this]
  have hM₂j : ∀ r : Fin n, r.val < t → M₂ r j = 0 := by
    intro r hr
    have hlt : r < i₀ := by
      rw [Fin.lt_def]
      simpa [i₀] using hr
    rw [hM₂, hM₁i₀ j, if_pos rfl]
    simp only [u, if_pos hlt]
    field_simp
    ring
  have hval : ((b₁ * h * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M₂ := by
    rw [Units.val_mul, Units.val_mul, hb₁E, hb₂E, mul_assoc]
  refine ⟨b₁, hb₁, b₂, hb₂, ?_⟩
  rw [hval]
  refine ⟨Function.update p i₀ j, fun i hi => ?_⟩
  rcases Nat.eq_or_lt_of_le hi with hti | hti
  ·
    have hii : i = i₀ := Fin.ext (by simp [i₀, hti])
    subst hii
    rw [Function.update_self]
    refine ⟨?_, ?_, ?_⟩
    · rw [hM₂, hu0 _ le_rfl, zero_mul, add_zero, hM₁i₀, if_pos rfl]
      exact hj
    · intro c hc
      rw [hM₂, hu0 _ le_rfl, zero_mul, add_zero, hM₁i₀, if_neg hc]
    · intro r hr
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hr) with hlt | hgt
      · exact hM₂j r (by simpa [i₀] using hlt)
      · have hr' : t + 1 ≤ r.val := by simp [i₀] at hgt; omega
        rw [hM₂, hu0 r (by omega), zero_mul, add_zero, hM₁S r hr', hHj r hr']
  ·
    have hi' : t + 1 ≤ i.val := hti
    rw [Function.update_of_ne (hne i hi').symm]
    obtain ⟨h1, h2, h3⟩ := hp i hi'
    refine ⟨?_, ?_, ?_⟩
    · rw [hM₂, hu0 i hi, zero_mul, add_zero, hM₁S i hi']
      exact h1
    · intro c hc
      rw [hM₂, hu0 i hi, zero_mul, add_zero, hM₁S i hi']
      exact h2 c hc
    · intro r hr
      rw [hM₂, hM₁i₀, if_neg (hjp i hi'), mul_zero, add_zero, hM₁, hvp i hi', mul_zero,
        add_zero]
      exact h3 r hr
end GroundTheory.Automorphic
