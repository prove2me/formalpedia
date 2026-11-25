-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.rowsReducedOn_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:07.467091+00:00
-- url     : https://prove2.me/submissions/b6d58926-90bc-4e7e-9dba-b74f2f655562

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_mem_iwahori
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_mul_one_add_vecMulVec_apply
import Theorems.Thm_GroundTheory_Automorphic_one_add_vecMulVec_mul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (h : GL (Fin n) F) (R : Finset (Fin n)) (hR : R ≠ Finset.univ)
    (hred : RowsReducedOn (h : Matrix (Fin n) (Fin n) F) R) :
    ∃ x ∈ iwahori F n, ∃ y ∈ iwahori F n, ∃ r ∉ R,
      RowsReducedOn ((x * h * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (insert r R) := by
  classical
  obtain ⟨p, hp⟩ := hred
  obtain ⟨i₀, hi₀⟩ : ∃ i, i ∉ R := by
    by_contra hcon
    push Not at hcon
    exact hR (Finset.eq_univ_of_forall hcon)
  have hrow : ∀ i, ∃ j, (h : Matrix (Fin n) (Fin n) F) i j ≠ 0 := by
    intro i
    by_contra hcon
    push Not at hcon
    exact ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
      (det_eq_zero_of_row_eq_zero i hcon)
  let M : Matrix (Fin n) (Fin n) F := h
  let S : Finset (Fin n × Fin n) := Finset.univ.filter fun e => e.1 ∉ R
  have hS : S.Nonempty := ⟨(i₀, i₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
  obtain ⟨e₀, he₀S, he₀⟩ := S.exists_max_image (fun e => valuation F (M e.1 e.2)) hS
  let S₀ := S.filter fun e => valuation F (M e.1 e.2) = valuation F (M e₀.1 e₀.2)
  have hS₀ : S₀.Nonempty := ⟨e₀, Finset.mem_filter.mpr ⟨he₀S, rfl⟩⟩
  obtain ⟨⟨r₁, c⟩, he₁S₀, he₁⟩ := S₀.exists_min_image (fun e => e.2) hS₀
  let S₁ := S₀.filter fun e => e.2 = c
  have hS₁ : S₁.Nonempty := ⟨(r₁, c), Finset.mem_filter.mpr ⟨he₁S₀, rfl⟩⟩
  obtain ⟨⟨r, c₂⟩, he₂S₁, he₂⟩ := S₁.exists_max_image (fun e => e.1) hS₁
  obtain ⟨he₂S₀, hc₂⟩ := Finset.mem_filter.mp he₂S₁
  obtain ⟨he₂S, hv⟩ := Finset.mem_filter.mp he₂S₀
  have hr : r ∉ R := (Finset.mem_filter.mp he₂S).2
  simp only at hc₂ hv
  subst hc₂

  have F1 : ∀ i, i ∉ R → ∀ j, valuation F (M i j) ≤ valuation F (M r c₂) := fun i hi j => by
    rw [hv]
    exact he₀ (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have F2 : ∀ i, i ∉ R → ∀ j, valuation F (M i j) = valuation F (M r c₂) → c₂ ≤ j :=
    fun i hi j hij => he₁ (i, j) (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hij.trans hv⟩)
  have F3 : ∀ i, i ∉ R → valuation F (M i c₂) = valuation F (M r c₂) → i ≤ r :=
    fun i hi hij => he₂ (i, c₂) (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hij.trans hv⟩, rfl⟩)
  have hP : M r c₂ ≠ 0 := by
    obtain ⟨j, hj⟩ := hrow i₀
    intro h0
    have := F1 i₀ hi₀ j
    rw [h0, map_zero] at this
    exact hj ((Valuation.zero_iff _).mp (le_antisymm this zero_le))
  have hvP : 0 < valuation F (M r c₂) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hP)
  have hpc : ∀ i ∈ R, p i ≠ c₂ := by
    intro i hi e
    exact hP (e ▸ (hp i hi).2.2 r (fun e' => hr (e' ▸ hi)))
  have hRc : ∀ i ∈ R, M i c₂ = 0 := fun i hi => (hp i hi).2.1 c₂ (Ne.symm (hpc i hi))
  have hrp : ∀ i ∈ R, M r (p i) = 0 := fun i hi => (hp i hi).2.2 r (fun e => hr (e ▸ hi))

  let u : Fin n → F := fun i => if i = r then 0 else -(M i c₂ / M r c₂)
  have hu_val : ∀ i, i ≠ r → valuation F (u i) = valuation F (M i c₂) / valuation F (M r c₂) := by
    intro i hi
    simp only [u, if_neg hi, Valuation.map_neg, map_div₀]
  have hu_le : ∀ i, valuation F (u i) ≤ 1 := by
    intro i
    by_cases hi : i = r
    · simp [u, hi]
    rw [hu_val i hi, div_le_one₀ hvP]
    by_cases hiR : i ∈ R
    · rw [hRc i hiR, map_zero]
      exact hvP.le
    · exact F1 i hiR c₂
  have hu_lt : ∀ i, r < i → valuation F (u i) < 1 := by
    intro i hri
    have hi : i ≠ r := hri.ne'
    rw [hu_val i hi, div_lt_one₀ hvP]
    by_cases hiR : i ∈ R
    · rw [hRc i hiR, map_zero]
      exact hvP
    · exact lt_of_le_of_ne (F1 i hiR c₂) fun e => absurd (F3 i hiR e) (not_le.mpr hri)
  have hur : u r = 0 := by simp [u]
  have huR : ∀ i ∈ R, u i = 0 := by
    intro i hi
    have hir : i ≠ r := fun e => hr (e ▸ hi)
    simp [u, hir, hRc i hi]
  let X : Matrix (Fin n) (Fin n) F := 1 + vecMulVec u (Pi.single r 1)
  have hX : ∀ i j, X i j = (1 : Matrix (Fin n) (Fin n) F) i j + if j = r then u i else 0 := by
    intro i j
    simp only [X, Matrix.add_apply, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨x, hx, hxX⟩ := exists_mem_iwahori F n X
    (fun i j => by
      rw [hX]
      by_cases hij : i = j
      · subst hij
        rw [one_apply_eq]
        by_cases hir : i = r
        · rw [if_pos hir, hir, hur, add_zero, map_one]
        · rw [if_neg hir, add_zero, map_one]
      · rw [one_apply_ne hij, zero_add]
        split_ifs
        · exact hu_le i
        · rw [map_zero]
          exact zero_le)
    (fun i j hji => by
      rw [hX, one_apply_ne hji.ne', zero_add]
      split_ifs with hjr
      · exact hu_lt i (hjr ▸ hji)
      · rw [map_zero]
        exact zero_lt_one)
    (fun i => by
      rw [hX, one_apply_eq]
      by_cases hir : i = r
      · rw [if_pos hir, hir, hur, add_zero, map_one]
      · rw [if_neg hir, add_zero, map_one])

  let t : Fin n → F := fun j => if j = c₂ then 0 else -(M r j / M r c₂)
  have ht_val : ∀ j, j ≠ c₂ → valuation F (t j) = valuation F (M r j) / valuation F (M r c₂) := by
    intro j hj
    simp only [t, if_neg hj, Valuation.map_neg, map_div₀]
  have htc : t c₂ = 0 := by simp [t]
  have ht_le : ∀ j, valuation F (t j) ≤ 1 := by
    intro j
    by_cases hj : j = c₂
    · simp [t, hj]
    rw [ht_val j hj, div_le_one₀ hvP]
    exact F1 r hr j
  have ht_lt : ∀ j, j < c₂ → valuation F (t j) < 1 := by
    intro j hj
    rw [ht_val j hj.ne, div_lt_one₀ hvP]
    exact lt_of_le_of_ne (F1 r hr j) fun e => absurd (F2 r hr j e) (not_le.mpr hj)
  let Y : Matrix (Fin n) (Fin n) F := 1 + vecMulVec (Pi.single c₂ 1) t
  have hY : ∀ i j, Y i j = (1 : Matrix (Fin n) (Fin n) F) i j + if i = c₂ then t j else 0 := by
    intro i j
    simp only [Y, Matrix.add_apply, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨y, hy, hyY⟩ := exists_mem_iwahori F n Y
    (fun i j => by
      rw [hY]
      by_cases hij : i = j
      · subst hij
        rw [one_apply_eq]
        by_cases hic : i = c₂
        · rw [if_pos hic, hic, htc, add_zero, map_one]
        · rw [if_neg hic, add_zero, map_one]
      · rw [one_apply_ne hij, zero_add]
        split_ifs
        · exact ht_le j
        · rw [map_zero]
          exact zero_le)
    (fun i j hji => by
      rw [hY, one_apply_ne hji.ne', zero_add]
      split_ifs with hic
      · exact ht_lt j (hic ▸ hji)
      · rw [map_zero]
        exact zero_lt_one)
    (fun i => by
      rw [hY, one_apply_eq]
      by_cases hic : i = c₂
      · rw [if_pos hic, hic, htc, add_zero, map_one]
      · rw [if_neg hic, add_zero, map_one])

  let M₁ : Matrix (Fin n) (Fin n) F := X * M
  have hM₁ : ∀ a b, M₁ a b = M a b + u a * M r b := fun a b =>
    one_add_vecMulVec_mul_apply M r u a b
  have hM₁c : ∀ a, a ≠ r → M₁ a c₂ = 0 := by
    intro a ha
    rw [hM₁]
    simp only [u, if_neg ha]
    rw [neg_mul, div_mul_cancel₀ _ hP, add_neg_cancel]
  have hN : ∀ a b, ((x * h * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b =
      M₁ a b + M₁ a c₂ * t b := by
    intro a b
    rw [Units.val_mul, Units.val_mul, hxX, hyY]
    exact mul_one_add_vecMulVec_apply M₁ c₂ t a b
  refine ⟨x, hx, y, hy, r, hr, Function.update p r c₂, fun i hi => ?_⟩
  rcases Finset.mem_insert.mp hi with rfl | hiR
  · rw [Function.update_self]
    refine ⟨?_, fun b hb => ?_, fun a ha => ?_⟩
    · rw [hN, htc, mul_zero, add_zero, hM₁, hur, zero_mul, add_zero]
      exact hP
    · rw [hN, hM₁, hM₁, hur, zero_mul, zero_mul, add_zero, add_zero]
      simp only [t, if_neg hb]
      rw [mul_neg, mul_div_cancel₀ _ hP, add_neg_cancel]
    · rw [hN, hM₁c a ha, zero_mul, add_zero]
  · have hir : i ≠ r := fun e => hr (e ▸ hiR)
    rw [Function.update_of_ne hir]
    obtain ⟨h1, h2, h3⟩ := hp i hiR
    have hrow_i : ∀ b, ((x * h * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i b = M i b := by
      intro b
      rw [hN, hM₁c i hir, zero_mul, add_zero, hM₁, huR i hiR, zero_mul, add_zero]
    refine ⟨by rw [hrow_i]; exact h1, fun b hb => by rw [hrow_i]; exact h2 b hb, fun a ha => ?_⟩
    rw [hN]
    by_cases har : a = r
    · subst har
      have htp : t (p i) = 0 := by
        simp only [t, if_neg (hpc i hiR), hrp i hiR, zero_div, neg_zero]
      rw [htp, mul_zero, add_zero, hM₁, hrp i hiR, mul_zero, add_zero]
    · have h3' : M a (p i) = 0 := h3 a ha
      rw [hM₁c a har, zero_mul, add_zero, hM₁, h3', hrp i hiR, mul_zero, add_zero]
end GroundTheory.Automorphic.GLnLocal
