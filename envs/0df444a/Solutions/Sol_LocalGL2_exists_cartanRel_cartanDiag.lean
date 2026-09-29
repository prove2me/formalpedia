-- Prove2me | solution 1 for LocalGL2.exists_cartanRel_cartanDiag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6ce02c16-84e2-55c4-9472-072b37d77dd9

import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_exists_cartanRel_cartanDiag

open Matrix LocalGL2

namespace LocalGL2Exists

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

private theorem dvd_total' (x y : R) : x ∣ y ∨ y ∣ x := by
  rcases le_total (IsDiscreteValuationRing.addVal R x) (IsDiscreteValuationRing.addVal R y)
    with h | h
  · exact Or.inl (IsDiscreteValuationRing.addVal_le_iff_dvd.mp h)
  · exact Or.inr (IsDiscreteValuationRing.addVal_le_iff_dvd.mp h)

private theorem exists_mem_dvd_all :
    ∀ l : List R, l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, x ∣ y := by
  intro l
  induction l with
  | nil => exact fun h => absurd rfl h
  | cons a l ih =>
    intro _
    by_cases hl : l = []
    · subst hl
      refine ⟨a, by simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact dvd_rfl
      · exact absurd hy (List.not_mem_nil)
    · obtain ⟨x, hxl, hx⟩ := ih hl
      rcases dvd_total' a x with hax | hxa
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact dvd_rfl
        · exact hax.trans (hx y hy)
      · refine ⟨x, List.mem_cons_of_mem _ hxl, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hxa
        · exact hx y hy

private theorem cartanRel_of_corner_dvd {ϖ : R} (hϖ : Irreducible ϖ)
    (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det ≠ 0) (hdvd : ∀ i j, g 0 0 ∣ g i j) :
    ∃ a b : ℕ, a ≤ b ∧ CartanRel g (cartanDiag ϖ a b) := by
  obtain ⟨β, hβ⟩ := hdvd 0 1
  obtain ⟨γ, hγ⟩ := hdvd 1 0
  have hp : g 0 0 ≠ 0 := by
    intro h0; apply hg
    rw [Matrix.det_fin_two, hβ, hγ, h0]; ring
  have hL : IsUnit (!![1, 0; -γ, 1] : Matrix (Fin 2) (Fin 2) R) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by simp [Matrix.det_fin_two_of])
  have hU : IsUnit (!![1, -β; 0, 1] : Matrix (Fin 2) (Fin 2) R) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by simp [Matrix.det_fin_two_of])
  set d : R := g 1 1 - γ * (g 0 0 * β) with hd_def
  have hred : hL.unit.val * g * hU.unit.val = !![g 0 0, 0; 0, d] := by
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    have hgeta : g = !![g 0 0, g 0 0 * β; g 0 0 * γ, g 1 1] := by
      rw [← hβ, ← hγ]; exact Matrix.eta_fin_two g
    rw [hgeta]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_two, hd_def]; try ring)
  have hrel : CartanRel g (!![g 0 0, 0; 0, d]) := by
    rw [← hred]; exact (cartanRel_unit_mul_mul hL.unit hU.unit g).symm
  have hpd : g 0 0 ∣ d := by
    rw [hd_def]; exact dvd_sub (hdvd 1 1) ⟨γ * β, by ring⟩
  have hd0 : d ≠ 0 := by
    intro h0; apply hg
    have hD : Associated g.det (!![g 0 0, 0; 0, d] : Matrix (Fin 2) (Fin 2) R).det :=
      hrel.det_associated
    rw [Matrix.det_fin_two_of, h0, mul_zero, zero_sub, mul_zero, neg_zero] at hD
    exact (associated_zero_iff_eq_zero _).mp hD
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp hϖ
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  have ham : a ≤ m := by
    rw [← pow_irreducible_dvd_pow_iff hϖ]
    have h1 : Associated (g 0 0) (ϖ ^ a) := by
      rw [hu]; exact associated_unit_mul_left _ _ u.isUnit
    have h2 : Associated d (ϖ ^ m) := by
      rw [hv]; exact associated_unit_mul_left _ _ v.isUnit
    exact h1.dvd_iff_dvd_left.mp (h2.dvd_iff_dvd_right.mp hpd)
  have hW : IsUnit (!![(u : R), 0; 0, (v : R)] : Matrix (Fin 2) (Fin 2) R) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by simp [Matrix.det_fin_two_of])
  have hsplit : (!![g 0 0, 0; 0, d] : Matrix (Fin 2) (Fin 2) R) =
      hW.unit.val * cartanDiag ϖ a m := by
    rw [IsUnit.unit_spec]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [cartanDiag, Matrix.mul_apply, Fin.sum_univ_two, hu, hv]; try ring)
  refine ⟨a, m, ham, hrel.trans ?_⟩
  rw [hsplit]
  have : hW.unit.val * cartanDiag ϖ a m =
      hW.unit.val * cartanDiag ϖ a m * (1 : (Matrix (Fin 2) (Fin 2) R)ˣ).val := by simp
  rw [this]
  exact cartanRel_unit_mul_mul hW.unit 1 (cartanDiag ϖ a m)

end LocalGL2Exists

open LocalGL2Exists in
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det ≠ 0) :
    ∃ a b : ℕ, a ≤ b ∧ CartanRel g (cartanDiag ϖ a b) := by
  obtain ⟨x, hxmem, hx⟩ := exists_mem_dvd_all [g 0 0, g 0 1, g 1 0, g 1 1] (by simp)
  have hx' : ∀ i j : Fin 2, x ∣ g i j := by
    simp only [Fin.forall_fin_two]
    exact ⟨⟨hx _ (by simp), hx _ (by simp)⟩, hx _ (by simp), hx _ (by simp)⟩
  have hxdvd : ∀ (k₁ k₂ : (Matrix (Fin 2) (Fin 2) R)ˣ) (i j : Fin 2),
      x ∣ (k₁.val * g * k₂.val) i j := by
    intro k₁ k₂ i j
    rw [← Ideal.mem_span_singleton]
    have hle : entryIdeal (k₁.val * g * k₂.val) ≤ Ideal.span {x} := by
      refine ((entryIdeal_mul_le_left _ _).trans (entryIdeal_mul_le_right _ _)).trans ?_
      rw [entryIdeal_le_iff]
      intro i' j'
      exact Ideal.mem_span_singleton.mpr (hx' i' j')
    exact hle (entry_mem_entryIdeal _ i j)
  have key : ∀ k₁ k₂ : (Matrix (Fin 2) (Fin 2) R)ˣ,
      (k₁.val * g * k₂.val) 0 0 = x →
      ∃ a b : ℕ, a ≤ b ∧ CartanRel g (cartanDiag ϖ a b) := by
    intro k₁ k₂ hcorner
    have hdet : (k₁.val * g * k₂.val).det ≠ 0 := by
      intro h0
      exact hg (((cartanRel_unit_mul_mul k₁ k₂ g).det_associated).eq_zero_iff.mp h0)
    obtain ⟨a, b, hab, hrel⟩ := cartanRel_of_corner_dvd hϖ (k₁.val * g * k₂.val) hdet
      (fun i j => hcorner ▸ hxdvd k₁ k₂ i j)
    exact ⟨a, b, hab, ((cartanRel_unit_mul_mul k₁ k₂ g).symm).trans hrel⟩
  have hxcases : x = g 0 0 ∨ x = g 0 1 ∨ x = g 1 0 ∨ x = g 1 1 := by
    simpa using hxmem
  rcases hxcases with h | h | h | h
  · refine key 1 1 ?_
    simp [h]
  · refine key 1 swapUnit ?_
    rw [Units.val_one, one_mul, swapUnit_val, h]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · refine key swapUnit 1 ?_
    rw [Units.val_one, mul_one, swapUnit_val, h]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · refine key swapUnit swapUnit ?_
    rw [swapUnit_val, h]
    simp [Matrix.mul_apply, Matrix.vecMul_eq_sum, Fin.sum_univ_two]

end S_LocalGL2_exists_cartanRel_cartanDiag
end P2MW
export P2MW.S_LocalGL2_exists_cartanRel_cartanDiag (solution)
