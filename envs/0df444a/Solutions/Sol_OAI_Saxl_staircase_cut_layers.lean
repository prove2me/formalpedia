-- Prove2me | solution 1 for OAI.Saxl.staircase_cut_layers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:33:56.935383+00:00
-- url     : https://prove2.me/submissions/8463bd51-8db1-4d8e-8100-2c731ef1d8fb

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector

open OAI OAI.Saxl
open scoped TensorProduct
theorem h42_finset_eq {X : Type*} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 < w x) (hn : ∀ x ∉ B, w x < 0)
    (he : ∑ x ∈ A, w x = ∑ x ∈ B, w x) : A = B := by
  have h1 := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := A) (f := w) Finset.inter_subset_left
  have h2 := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := B) (f := w) Finset.inter_subset_right
  have e1 : A \ (A ∩ B) = A \ B := by ext x; simp
  have e2 : B \ (A ∩ B) = B \ A := by ext x; simp [and_comm]
  rw [e1] at h1; rw [e2] at h2
  have hAB : ∑ x ∈ A \ B, w x = ∑ x ∈ B \ A, w x := by omega
  have hle : ∑ x ∈ A \ B, w x ≤ 0 := Finset.sum_nonpos (fun x hx => by
    have := hn x (Finset.mem_sdiff.1 hx).2; omega)
  have hge : 0 ≤ ∑ x ∈ B \ A, w x := Finset.sum_nonneg (fun x hx => by
    have := hp x (Finset.mem_sdiff.1 hx).1; omega)
  have d1 : A \ B = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have : ∑ x ∈ A \ B, w x < 0 := Finset.sum_neg (fun x hx => hn x (Finset.mem_sdiff.1 hx).2) ⟨y, hy⟩
    omega
  have d2 : B \ A = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have : 0 < ∑ x ∈ B \ A, w x := Finset.sum_pos (fun x hx => hp x (Finset.mem_sdiff.1 hx).1) ⟨y, hy⟩
    omega
  rw [Finset.sdiff_eq_empty_iff_subset] at d1 d2
  exact Finset.Subset.antisymm d1 d2

theorem h42_shiftA (h s : ℕ) (f : ℕ → ℤ) :
    ∑ y ∈ (staircase (h+s)).cells, (if s ≤ y.2 then f y.1 else 0) =
      ∑ y ∈ (staircase (h+s)).cells, (if y.1 + y.2 < h then f y.1 else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun y => (y.1, y.2 - s)) (fun y => (y.1, y.2 + s))
  · rintro ⟨a, b⟩ hy
    dsimp only; simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy ⊢; omega
  · rintro ⟨a, b⟩ hy
    dsimp only; simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy ⊢; omega
  · rintro ⟨a, b⟩ hy
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy
    refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  · rintro ⟨a, b⟩ hy
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy
    refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  · intro y _; rfl

theorem h42_shiftB (h s : ℕ) (f : ℕ → ℤ) :
    ∑ y ∈ (staircase (h+s)).cells, (if s ≤ y.1 then f y.2 else 0) =
      ∑ y ∈ (staircase (h+s)).cells, (if y.1 + y.2 < h then f y.2 else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun y => (y.1 - s, y.2)) (fun y => (y.1 + s, y.2))
  · rintro ⟨a, b⟩ hy
    dsimp only; simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy ⊢; omega
  · rintro ⟨a, b⟩ hy
    dsimp only; simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy ⊢; omega
  · rintro ⟨a, b⟩ hy
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy
    refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  · rintro ⟨a, b⟩ hy
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy
    refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  · intro y _; rfl

theorem h42_rigid (h s : ℕ)
    (g k : Equiv.Perm (staircase (h+s)).cells)
    (hg : ∀ x, (g x).val.1 = x.val.1)
    (hk : ∀ x, (k x).val.2 = x.val.2)
    (hc : ∀ x, s ≤ (g x).val.2 ↔ s ≤ (k x).val.1) :
    ∀ x, s ≤ (g x).val.2 ↔ x.val.1 + x.val.2 < h := by
  classical
  let C := (staircase (h+s)).cells
  let α : ℕ → ℤ := fun r => 2 * (h : ℤ) - 1 - 2 * r
  let β : ℕ → ℤ := fun c => -2 * (c : ℤ)
  let w : C → ℤ := fun x => α x.val.1 + β x.val.2
  let H : Finset C := Finset.univ.filter (fun x => s ≤ (g x).val.2)
  let T : Finset C := Finset.univ.filter (fun x => x.val.1 + x.val.2 < h)
  have hA : ∑ x : C, (if s ≤ x.val.2 then α x.val.1 else 0) =
      ∑ x : C, (if x.val.1 + x.val.2 < h then α x.val.1 else 0) := by
    rw [Finset.sum_coe_sort C (fun y => if s ≤ y.2 then α y.1 else 0),
      Finset.sum_coe_sort C (fun y => if y.1 + y.2 < h then α y.1 else 0)]
    exact h42_shiftA h s α
  have hB : ∑ x : C, (if s ≤ x.val.1 then β x.val.2 else 0) =
      ∑ x : C, (if x.val.1 + x.val.2 < h then β x.val.2 else 0) := by
    rw [Finset.sum_coe_sort C (fun y => if s ≤ y.1 then β y.2 else 0),
      Finset.sum_coe_sort C (fun y => if y.1 + y.2 < h then β y.2 else 0)]
    exact h42_shiftB h s β
  have hgA : ∑ x : C, (if s ≤ (g x).val.2 then α x.val.1 else 0) =
      ∑ x : C, (if s ≤ x.val.2 then α x.val.1 else 0) := by
    rw [← Equiv.sum_comp g (fun x : C => if s ≤ x.val.2 then α x.val.1 else 0)]
    apply Finset.sum_congr rfl; intro x _; simp only [hg]
  have hkB : ∑ x : C, (if s ≤ (g x).val.2 then β x.val.2 else 0) =
      ∑ x : C, (if s ≤ x.val.1 then β x.val.2 else 0) := by
    rw [← Equiv.sum_comp k (fun x : C => if s ≤ x.val.1 then β x.val.2 else 0)]
    apply Finset.sum_congr rfl; intro x _; simp only [hk, hc]
  have hsplit : ∀ (p : C → Prop) [DecidablePred p], ∑ x ∈ Finset.univ.filter p, w x =
      ∑ x : C, (if p x then α x.val.1 else 0) + ∑ x : C, (if p x then β x.val.2 else 0) := by
    intro p _
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    split_ifs <;> simp [w]
  have heq : H = T := by
    apply h42_finset_eq H T w
    · intro x hx
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [w, α, β]; omega
    · intro x hx
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [w, α, β]; omega
    · rw [hsplit, hsplit, hgA, hkB, hA, hB]
  intro x
  have := congrArg (fun S : Finset C => x ∈ S) heq
  simpa [H, T] using this

theorem h42_poly_ne {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (a : Fin n → Fin (μ.colLen 0))
    (ha : polytabloid t a ≠ 0) :
    ∃ g : Equiv.Perm (Fin n), g ∈ columnGroup t ∧ a = rowWord t ∘ g := by
  classical
  unfold polytabloid at ha
  simp only [Finset.sum_apply] at ha
  obtain ⟨g, _, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  refine ⟨(g : Equiv.Perm (Fin n))⁻¹, inv_mem g.2, ?_⟩
  rw [Pi.smul_apply, wordRep_single] at hg
  by_contra hne
  apply hg
  rw [Pi.single_apply, if_neg hne, smul_zero]

theorem h42_uniq {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (x y : Equiv.Perm (Fin n))
    (hx : x ∈ columnGroup t) (hy : y ∈ columnGroup t) (h : rowWord t ∘ x = rowWord t ∘ y) :
    x = y := by
  ext i : 1
  have h1 := congrFun h i
  simp only [rowWord, Function.comp_apply, Fin.mk.injEq] at h1
  have h2 : (t (x i)).val.2 = (t (y i)).val.2 := (hx i).trans (hy i).symm
  exact t.injective (Subtype.ext (Prod.ext h1 h2))

open Classical in
theorem h42_alt_val {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (S : Subgroup (Equiv.Perm (Fin n)))
    (ρ g : Equiv.Perm (Fin n)) (hρ : ρ ∈ columnGroup t) (hg : g ∈ columnGroup t) :
    altWord (columnGroup t ⊓ S) (rowWord t ∘ ρ) (rowWord t ∘ g) =
      if g⁻¹ * ρ ∈ S then signC (g⁻¹ * ρ) else 0 := by
  classical
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ k : (columnGroup t ⊓ S : Subgroup _),
      (wordRep n (μ.colLen 0) (k : Equiv.Perm (Fin n)) (Pi.single (rowWord t ∘ ρ) (1:ℂ)))
        (rowWord t ∘ g) = if (k : Equiv.Perm (Fin n)) = g⁻¹ * ρ then 1 else 0 := by
    intro k
    change (Pi.single (rowWord t ∘ ρ) (1:ℂ) : WordSpace n _) ((rowWord t ∘ g) ∘ (k : Equiv.Perm (Fin n))) = _
    rw [Pi.single_apply]
    have : (rowWord t ∘ g) ∘ (k : Equiv.Perm (Fin n)) = rowWord t ∘ ρ ↔
        (k : Equiv.Perm (Fin n)) = g⁻¹ * ρ := by
      constructor
      · intro h
        have := h42_uniq t (g * k) ρ (mul_mem hg (Subgroup.mem_inf.1 k.2).1) hρ (by
          funext i; exact congrFun h i)
        rw [← this, ← mul_assoc, inv_mul_cancel, one_mul]
      · intro h; rw [h]; funext i; simp
    simp only [this]
  simp only [hterm, mul_ite, mul_one, mul_zero]
  split_ifs with hS
  · rw [Finset.sum_eq_single (⟨g⁻¹ * ρ, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hg) hρ, hS⟩⟩ :
      (columnGroup t ⊓ S : Subgroup _))]
    · simp
    · intro k _ hk
      rw [if_neg]; intro h; exact hk (Subtype.ext h)
    · intro h; exact absurd (by simp) h
  · apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    intro h
    exact hS (h ▸ (Subgroup.mem_inf.1 k.2).2)

theorem h42_alt_ne {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (S : Subgroup (Equiv.Perm (Fin n)))
    (ρ : Equiv.Perm (Fin n)) (hρ : ρ ∈ columnGroup t) (a : Fin n → Fin (μ.colLen 0))
    (ha : altWord (columnGroup t ⊓ S) (rowWord t ∘ ρ) a ≠ 0) :
    ∃ g : Equiv.Perm (Fin n), g ∈ columnGroup t ∧ a = rowWord t ∘ g := by
  classical
  unfold altWord at ha
  simp only [Finset.sum_apply] at ha
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  refine ⟨ρ * (k : Equiv.Perm (Fin n))⁻¹, mul_mem hρ (inv_mem (Subgroup.mem_inf.1 k.2).1), ?_⟩
  rw [Pi.smul_apply, wordRep_single] at hk
  by_contra hne
  apply hk
  rw [Pi.single_apply, if_neg, smul_zero]
  intro h; apply hne; rw [h]; rfl

theorem h42_poly_val {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (g : Equiv.Perm (Fin n))
    (hg : g ∈ columnGroup t) : polytabloid t (rowWord t ∘ g) = signC g := by
  classical
  unfold polytabloid
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨g⁻¹, inv_mem hg⟩ : columnGroup t)]
  · change _ * (Pi.single (rowWord t) (1:ℂ) : WordSpace n _)
      ((rowWord t ∘ g) ∘ (g⁻¹ : Equiv.Perm (Fin n))) = _
    rw [show (rowWord t ∘ g) ∘ (g⁻¹ : Equiv.Perm (Fin n)) = rowWord t by funext i; simp,
      Pi.single_eq_same, mul_one]
    simp [signC_def, Equiv.Perm.sign_inv]
  · intro k _ hk
    have key : (rowWord t ∘ g) ∘ (k : Equiv.Perm (Fin n)) ≠ rowWord t := by
      intro h
      apply hk
      have := h42_uniq t (g * k) 1 (mul_mem hg k.2) (one_mem _) (by funext i; exact congrFun h i)
      apply Subtype.ext
      exact eq_inv_of_mul_eq_one_right this
    change _ * (Pi.single (rowWord t) (1:ℂ) : WordSpace n _)
      ((rowWord t ∘ g) ∘ (k : Equiv.Perm (Fin n))) = 0
    rw [Pi.single_apply, if_neg key, mul_zero]
  · intro h; exact absurd (by simp) h

theorem h42_high (h s : ℕ) (g1 g2 : Equiv.Perm (Fin (staircase (h+s)).card))
    (hg1 : g1 ∈ columnGroup (stairRowTableau (h+s))) (hg2 : g2 ∈ columnGroup (stairTableau (h+s)))
    (hcond : ∀ i, s ≤ (rowWord (stairRowTableau (h+s)) (g1 i)).val ↔
      s ≤ (rowWord (stairTableau (h+s)) (g2 i)).val) :
    ∀ i, s ≤ (rowWord (stairRowTableau (h+s)) (g1 i)).val ↔ stairHigh h s i := by
  classical
  let T := stairTableau (h+s)
  let G : Equiv.Perm (staircase (h+s)).cells := (T.symm.trans g1).trans T
  let K : Equiv.Perm (staircase (h+s)).cells := (T.symm.trans g2).trans T
  have hG : ∀ x, (G x).val.1 = x.val.1 := by
    intro x
    have := hg1 (T.symm x)
    simpa [G, T, stairRowTableau, staircaseSwap] using this
  have hK : ∀ x, (K x).val.2 = x.val.2 := by
    intro x
    have := hg2 (T.symm x)
    simpa [K, T] using this
  have hL : ∀ i, (rowWord (stairRowTableau (h+s)) (g1 i)).val = (G (T i)).val.2 := by
    intro i; simp [G, T, rowWord, stairRowTableau, staircaseSwap]
  have hR : ∀ i, (rowWord (stairTableau (h+s)) (g2 i)).val = (K (T i)).val.1 := by
    intro i; simp [K, T, rowWord]
  have hc : ∀ x, s ≤ (G x).val.2 ↔ s ≤ (K x).val.1 := by
    intro x
    have := hcond (T.symm x)
    rw [hL, hR] at this
    simpa using this
  have hr := h42_rigid h s G K hG hK hc
  intro i; rw [hL]; exact hr (T i)

theorem h42_sec {n s : ℕ} (H : Fin n → Prop) (f : Fin n → ℕ) (g ρ : Equiv.Perm (Fin n))
    (hr : ∀ i, s ≤ f (ρ i) ↔ H i) :
    (∀ i, H ((g⁻¹ * ρ) i) ↔ H i) ↔ ∀ j, (s ≤ f (g j) ↔ H j) := by
  constructor
  · intro hk j
    have h1 := hk (ρ⁻¹ (g j))
    have h2 := hr (ρ⁻¹ (g j))
    have e1 : ρ (ρ⁻¹ (g j)) = g j := by simp
    have e2 : (g⁻¹ * ρ) (ρ⁻¹ (g j)) = j := by simp
    rw [e1] at h2; rw [e2] at h1
    rw [h2, h1]
  · intro hj i
    have h1 := hj ((g⁻¹ * ρ) i)
    have e1 : g ((g⁻¹ * ρ) i) = ρ i := by simp
    rw [e1] at h1
    rw [← h1, hr]

theorem solution (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
      wordTensor _ _ _ (cutRowWord h s ⊗ₜ[ℂ] cutColumnWord h s) := by
  classical
  let T := stairTableau (h+s)
  let ρ1 := (rotateRowPositions h s).1
  let ρ2 := (rotateColumnPositions h s).1
  have hρ1 : ρ1 ∈ columnGroup (stairRowTableau (h+s)) := (rotateRowPositions h s).2
  have hρ2 : ρ2 ∈ columnGroup (stairTableau (h+s)) := (rotateColumnPositions h s).2
  have hrot : ∀ x : (staircase (h+s)).cells,
      s ≤ (rotateRow h s x).val.2 ↔ x.val.1 + x.val.2 < h := by
    intro x
    have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
    change s ≤ (rotateRowCell h s x).val.2 ↔ _
    simp only [rotateRowCell]
    split_ifs <;> constructor <;> intro <;> omega
  have hr1 : ∀ i, s ≤ (rowWord (stairRowTableau (h+s)) (ρ1 i)).val ↔ stairHigh h s i := by
    intro i
    have : (rowWord (stairRowTableau (h+s)) (ρ1 i)).val = (rotateRow h s (T i)).val.2 := by
      simp [ρ1, T, rowWord, stairRowTableau, staircaseSwap, rotateRowPositions]
    rw [this, hrot]; rfl
  have hr2 : ∀ i, s ≤ (rowWord (stairTableau (h+s)) (ρ2 i)).val ↔ stairHigh h s i := by
    intro i
    have : (rowWord (stairTableau (h+s)) (ρ2 i)).val =
        (rotateRow h s (staircaseSwap _ (T i))).val.2 := by
      simp [ρ2, T, rowWord, rotateColumnPositions, rotateColumn, staircaseSwap]
    rw [this, hrot]
    simp only [stairHigh, staircaseSwap, Equiv.coe_fn_mk, T]
    constructor <;> intro <;> omega
  have hsg : signC ρ1 = signC ρ2 := by
    have e1 : ρ1 = T.symm.permCongr (rotateRow h s) := by ext i; rfl
    have e2 : ρ2 = T.symm.permCongr ((staircaseSwap (h+s)).symm.permCongr (rotateRow h s)) := by
      ext i; rfl
    rw [e1, e2, signC_def, signC_def, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_permCongr,
      Equiv.Perm.sign_permCongr]
  funext w
  rw [wordTensor_tmul]
  change (if (∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val)
    then staircaseWord (h+s) w else 0) = _
  rw [staircaseWord, wordTensor_tmul]
  unfold cutRowWord cutColumnWord
  by_cases ha : ∃ g, g ∈ columnGroup (stairRowTableau (h+s)) ∧
      splitLeft w = rowWord (stairRowTableau (h+s)) ∘ g
  swap
  · have h1 : polytabloid (stairRowTableau (h+s)) (splitLeft w) = 0 := by
      by_contra hne; exact ha (h42_poly_ne _ _ hne)
    have h2 : altWord (columnGroup (stairRowTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
        (rowWord (stairRowTableau (h+s)) ∘ ρ1) (splitLeft w) = 0 := by
      by_contra hne; exact ha (h42_alt_ne _ _ _ hρ1 _ hne)
    rw [h1, h2]; simp
  by_cases hb : ∃ g, g ∈ columnGroup (stairTableau (h+s)) ∧
      splitRight w = rowWord (stairTableau (h+s)) ∘ g
  swap
  · have h1 : polytabloid (stairTableau (h+s)) (splitRight w) = 0 := by
      by_contra hne; exact hb (h42_poly_ne _ _ hne)
    have h2 : altWord (columnGroup (stairTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
        (rowWord (stairTableau (h+s)) ∘ ρ2) (splitRight w) = 0 := by
      by_contra hne; exact hb (h42_alt_ne _ _ _ hρ2 _ hne)
    rw [h1, h2]; simp
  obtain ⟨g1, hg1, e1⟩ := ha
  obtain ⟨g2, hg2, e2⟩ := hb
  rw [e1, e2, h42_poly_val _ _ hg1, h42_poly_val _ _ hg2, h42_alt_val _ _ _ _ hρ1 hg1,
    h42_alt_val _ _ _ _ hρ2 hg2]
  have hs1 := h42_sec (stairHigh h s) (fun i => (rowWord (stairRowTableau (h+s)) i).val) g1 ρ1 hr1
  have hs2 := h42_sec (stairHigh h s) (fun i => (rowWord (stairTableau (h+s)) i).val) g2 ρ2 hr2
  have hm1 : g1⁻¹ * ρ1 ∈ sectorGroup (stairHigh h s) ↔ ∀ i, stairHigh h s ((g1⁻¹ * ρ1) i) ↔ stairHigh h s i :=
    Iff.rfl
  have hm2 : g2⁻¹ * ρ2 ∈ sectorGroup (stairHigh h s) ↔ ∀ i, stairHigh h s ((g2⁻¹ * ρ2) i) ↔ stairHigh h s i :=
    Iff.rfl
  have hsign : signC (g1⁻¹ * ρ1) * signC (g2⁻¹ * ρ2) = signC g1 * signC g2 := by
    rw [map_mul, map_mul, signC_inv, signC_inv, hsg]
    have := signC_mul_self ρ2
    linear_combination (signC g1 * signC g2) * this
  by_cases hc : ∀ i, s ≤ ((rowWord (stairRowTableau (h+s)) ∘ g1) i).val ↔
      s ≤ ((rowWord (stairTableau (h+s)) ∘ g2) i).val
  · have hh := h42_high h s g1 g2 hg1 hg2 hc
    have hA : g1⁻¹ * ρ1 ∈ sectorGroup (stairHigh h s) := hm1.2 (hs1.2 hh)
    have hB : g2⁻¹ * ρ2 ∈ sectorGroup (stairHigh h s) := hm2.2 (hs2.2 (fun j => by
      rw [← hh j]; exact (hc j).symm))
    rw [if_pos hc, if_pos hA, if_pos hB, hsign]
  · rw [if_neg hc]
    by_cases hA : g1⁻¹ * ρ1 ∈ sectorGroup (stairHigh h s)
    · by_cases hB : g2⁻¹ * ρ2 ∈ sectorGroup (stairHigh h s)
      · exfalso; apply hc; intro i
        have a1 := hs1.1 (hm1.1 hA) i
        have a2 := hs2.1 (hm2.1 hB) i
        simp only [Function.comp_apply] at a1 a2 ⊢
        rw [a1, a2]
      · rw [if_neg hB, mul_zero]
    · rw [if_neg hA, zero_mul]

