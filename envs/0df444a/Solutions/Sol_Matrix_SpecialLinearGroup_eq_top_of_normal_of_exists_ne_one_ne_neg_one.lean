-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.eq_top_of_normal_of_exists_ne_one_ne_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/53349a31-7816-55df-9b70-a5e4e5331a95

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_eq_top_of_normal_of_exists_ne_one_ne_neg_one

set_option autoImplicit false

open Matrix
open scoped MatrixGroups

namespace SL2NormalCC

variable {K : Type*} [Field K]

def U (x : K) : SL(2, K) := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩

def L (x : K) : SL(2, K) := ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two_of]⟩

def D (t : K) (ht : t ≠ 0) : SL(2, K) := ⟨!![t, 0; 0, t⁻¹], by simp [Matrix.det_fin_two_of, ht]⟩

@[scoped simp] theorem U_apply (x : K) : ((U x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, x; 0, 1] := rfl
@[scoped simp] theorem L_apply (x : K) : ((L x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; x, 1] := rfl
@[scoped simp] theorem D_apply (t : K) (ht : t ≠ 0) :
    ((D t ht : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹] := rfl

theorem sl2_ext {A B : SL(2, K)}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1) (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) :
    A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem coe_mul_fin_two (A B : SL(2, K)) :
    ((A * B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![A 0 0 * B 0 0 + A 0 1 * B 1 0, A 0 0 * B 0 1 + A 0 1 * B 1 1;
         A 1 0 * B 0 0 + A 1 1 * B 1 0, A 1 0 * B 0 1 + A 1 1 * B 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_apply00 (A B : SL(2, K)) : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 := by
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) (coe_mul_fin_two A B)
  simpa using this
theorem mul_apply01 (A B : SL(2, K)) : (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 := by
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) (coe_mul_fin_two A B)
  simpa using this
theorem mul_apply10 (A B : SL(2, K)) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := by
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) (coe_mul_fin_two A B)
  simpa using this
theorem mul_apply11 (A B : SL(2, K)) : (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) (coe_mul_fin_two A B)
  simpa using this

theorem det_expl (A : SL(2, K)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.2
  rw [Matrix.det_fin_two] at h
  exact h

theorem inv_apply00 (A : SL(2, K)) : (A⁻¹) 0 0 = A 1 1 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
theorem inv_apply01 (A : SL(2, K)) : (A⁻¹) 0 1 = - A 0 1 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
theorem inv_apply10 (A : SL(2, K)) : (A⁻¹) 1 0 = - A 1 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
theorem inv_apply11 (A : SL(2, K)) : (A⁻¹) 1 1 = A 0 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl

@[scoped simp] theorem U00 (x : K) : (U x : SL(2, K)) 0 0 = 1 := rfl
@[scoped simp] theorem U01 (x : K) : (U x : SL(2, K)) 0 1 = x := rfl
@[scoped simp] theorem U10 (x : K) : (U x : SL(2, K)) 1 0 = 0 := rfl
@[scoped simp] theorem U11 (x : K) : (U x : SL(2, K)) 1 1 = 1 := rfl
@[scoped simp] theorem L00 (x : K) : (L x : SL(2, K)) 0 0 = 1 := rfl
@[scoped simp] theorem L01 (x : K) : (L x : SL(2, K)) 0 1 = 0 := rfl
@[scoped simp] theorem L10 (x : K) : (L x : SL(2, K)) 1 0 = x := rfl
@[scoped simp] theorem L11 (x : K) : (L x : SL(2, K)) 1 1 = 1 := rfl
@[scoped simp] theorem D00 (t : K) (ht : t ≠ 0) : (D t ht : SL(2, K)) 0 0 = t := rfl
@[scoped simp] theorem D01 (t : K) (ht : t ≠ 0) : (D t ht : SL(2, K)) 0 1 = 0 := rfl
@[scoped simp] theorem D10 (t : K) (ht : t ≠ 0) : (D t ht : SL(2, K)) 1 0 = 0 := rfl
@[scoped simp] theorem D11 (t : K) (ht : t ≠ 0) : (D t ht : SL(2, K)) 1 1 = t⁻¹ := rfl
@[scoped simp] theorem one00 : (1 : SL(2, K)) 0 0 = 1 := rfl
@[scoped simp] theorem one01 : (1 : SL(2, K)) 0 1 = 0 := rfl
@[scoped simp] theorem one10 : (1 : SL(2, K)) 1 0 = 0 := rfl
@[scoped simp] theorem one11 : (1 : SL(2, K)) 1 1 = 1 := rfl

scoped macro "sl2_simp" : tactic =>
  `(tactic| simp only [mul_apply00, mul_apply01, mul_apply10, mul_apply11,
      inv_apply00, inv_apply01, inv_apply10, inv_apply11,
      U00, U01, U10, U11, L00, L01, L10, L11, D00, D01, D10, D11, one00, one01, one10, one11])

theorem U_mul_U (x y : K) : (U x * U y : SL(2, K)) = U (x + y) := by
  apply sl2_ext <;> sl2_simp <;> ring

theorem L_mul_L (x y : K) : (L x * L y : SL(2, K)) = L (x + y) := by
  apply sl2_ext <;> sl2_simp <;> ring

@[scoped simp] theorem U_zero : (U 0 : SL(2, K)) = 1 := by
  apply sl2_ext <;> sl2_simp

@[scoped simp] theorem L_zero : (L 0 : SL(2, K)) = 1 := by
  apply sl2_ext <;> sl2_simp

theorem U_inv (x : K) : (U x : SL(2, K))⁻¹ = U (-x) := by
  rw [inv_eq_iff_mul_eq_one, U_mul_U, add_neg_cancel, U_zero]

theorem L_inv (x : K) : (L x : SL(2, K))⁻¹ = L (-x) := by
  rw [inv_eq_iff_mul_eq_one, L_mul_L, add_neg_cancel, L_zero]

theorem D_U_comm (t : K) (ht : t ≠ 0) (y : K) :
    (D t ht * U y * (D t ht)⁻¹ * (U y)⁻¹ : SL(2, K)) = U ((t ^ 2 - 1) * y) := by
  apply sl2_ext <;> sl2_simp <;> field_simp <;> ring

theorem D_L_comm (t : K) (ht : t ≠ 0) (y : K) :
    (D t ht * L y * (D t ht)⁻¹ * (L y)⁻¹ : SL(2, K)) = L ((t⁻¹ ^ 2 - 1) * y) := by
  apply sl2_ext <;> sl2_simp <;> field_simp <;> ring

theorem eq_U_L_U (g : SL(2, K)) (hc : g 1 0 ≠ 0) :
    g = U ((g 0 0 - 1) / g 1 0) * L (g 1 0) * U ((g 1 1 - 1) / g 1 0) := by
  have hdet := det_expl g
  apply sl2_ext <;> sl2_simp
  · field_simp; ring
  · field_simp; linear_combination -hdet
  · ring
  · field_simp; ring

theorem U_inv_mul_mul_U_inv (g : SL(2, K)) (hc : g 1 0 ≠ 0) :
    (U ((g 0 0 - 1) / g 1 0))⁻¹ * g * (U ((g 1 1 - 1) / g 1 0))⁻¹ = L (g 1 0) := by
  have h := eq_U_L_U g hc
  generalize (g 0 0 - 1) / g 1 0 = α at h ⊢
  generalize (g 1 1 - 1) / g 1 0 = β at h ⊢
  generalize g 1 0 = c at h ⊢
  rw [h]
  group

theorem closure_U_L_eq_top :
    Subgroup.closure (Set.range (U (K := K)) ∪ Set.range (L (K := K))) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  set H := Subgroup.closure (Set.range (U (K := K)) ∪ Set.range (L (K := K))) with hH
  have hU : ∀ x, U x ∈ H := fun x => Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
  have hL : ∀ x, L x ∈ H := fun x => Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)
  have key : ∀ g : SL(2, K), g 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    rw [eq_U_L_U g hc]
    exact H.mul_mem (H.mul_mem (hU _) (hL _)) (hU _)
  by_cases hc : g 1 0 = 0
  · have h1 : (L 1 * g : SL(2, K)) 1 0 ≠ 0 := by
      sl2_simp
      rw [hc, mul_zero, add_zero, one_mul]
      intro h0
      have := det_expl g
      rw [h0, hc, zero_mul, mul_zero, sub_zero] at this
      exact zero_ne_one this
    have := key _ h1
    have h2 : g = (L 1)⁻¹ * (L 1 * g) := by group
    rw [h2]
    exact H.mul_mem (H.inv_mem (hL 1)) this
  · exact key g hc

theorem commutator_eq_top (t : K) (ht : t ≠ 0) (ht2 : t ^ 2 ≠ 1) :
    commutator SL(2, K) = ⊤ := by
  have hsub : t ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr ht2
  have hsub' : (1 : K) - t ^ 2 ≠ 0 := by
    intro h; apply hsub; linear_combination -h
  have ht2' : t⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [inv_pow, sub_ne_zero]
    intro h
    apply ht2
    have := congrArg (fun z => z⁻¹) h
    simpa using this
  apply top_le_iff.mp
  rw [← closure_U_L_eq_top, Subgroup.closure_le]
  rintro g (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · have h : U x = D t ht * U (x / (t ^ 2 - 1)) * (D t ht)⁻¹ * (U (x / (t ^ 2 - 1)))⁻¹ := by
      rw [D_U_comm]; congr 1; field_simp
    show U x ∈ commutator SL(2, K)
    rw [h, ← commutatorElement_def, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · have h : L x = D t ht * L (x / (t⁻¹ ^ 2 - 1)) * (D t ht)⁻¹ * (L (x / (t⁻¹ ^ 2 - 1)))⁻¹ := by
      rw [D_L_comm]; congr 1; field_simp
    show L x ∈ commutator SL(2, K)
    rw [h, ← commutatorElement_def, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

def borel : Subgroup SL(2, K) where
  carrier := {g | g 1 0 = 0}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    sl2_simp; rw [ha, hb]; ring
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    sl2_simp; rw [ha, neg_zero]

theorem mem_borel_iff (g : SL(2, K)) : g ∈ (borel : Subgroup SL(2, K)) ↔ g 1 0 = 0 := Iff.rfl

theorem U_mem_borel (x : K) : U x ∈ (borel : Subgroup SL(2, K)) := rfl

theorem borel00_ne_zero {g : SL(2, K)} (hg : g ∈ (borel : Subgroup SL(2, K))) : g 0 0 ≠ 0 := by
  intro h0
  have := det_expl g
  rw [(mem_borel_iff g).1 hg, h0, zero_mul, mul_zero, sub_zero] at this
  exact zero_ne_one this

theorem borel00_mul_borel11 {g : SL(2, K)} (hg : g ∈ (borel : Subgroup SL(2, K))) :
    g 0 0 * g 1 1 = 1 := by
  have := det_expl g
  rwa [(mem_borel_iff g).1 hg, mul_zero, sub_zero] at this

noncomputable def borelChar : (borel : Subgroup SL(2, K)) →* Kˣ where
  toFun g := Units.mk0 ((g : SL(2, K)) 0 0) (borel00_ne_zero g.2)
  map_one' := by ext; rfl
  map_mul' := by
    intro a b
    ext
    simp only [Units.val_mk0, Subgroup.coe_mul, Units.val_mul]
    sl2_simp
    rw [(mem_borel_iff _).1 b.2, mul_zero, add_zero]

def uHom : Multiplicative K →* (borel : Subgroup SL(2, K)) where
  toFun x := ⟨U x.toAdd, U_mem_borel _⟩
  map_one' := by ext1; simp
  map_mul' := by intro a b; ext1; simp [U_mul_U]

theorem isSolvable_borel : Group.IsSolvable (borel : Subgroup SL(2, K)) := by
  refine solvable_of_ker_le_range (uHom (K := K)) (borelChar (K := K)) ?_
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have h00 : (g : SL(2, K)) 0 0 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hg
    simpa [borelChar] using this
  have h10 : (g : SL(2, K)) 1 0 = 0 := (mem_borel_iff _).1 g.2
  have h11 : (g : SL(2, K)) 1 1 = 1 := by
    have := borel00_mul_borel11 g.2
    rwa [h00, one_mul] at this
  refine ⟨Multiplicative.ofAdd ((g : SL(2, K)) 0 1), ?_⟩
  ext1
  simp only [uHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  apply sl2_ext <;> sl2_simp
  · exact h00.symm
  · exact h10.symm
  · exact h11.symm

theorem eq_top_of_borel_le {H : Subgroup SL(2, K)} (hB : (borel : Subgroup SL(2, K)) ≤ H)
    {n : SL(2, K)} (hn : n ∈ H) (hc : n 1 0 ≠ 0) : H = ⊤ := by
  have hLc' : L (n 1 0) ∈ H := by
    rw [← U_inv_mul_mul_U_inv n hc]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hB (U_mem_borel _))) hn) (H.inv_mem (hB (U_mem_borel _)))
  set c := n 1 0 with hcdef
  have hLc : L c ∈ H := hLc'

  obtain ⟨w, hwH, hw00, hw01, hw10, hw11⟩ :
      ∃ w ∈ H, w 0 0 = 0 ∧ w 0 1 = -c⁻¹ ∧ w 1 0 = c ∧ w 1 1 = 0 := by
    refine ⟨U (-c⁻¹) * L c * U (-c⁻¹),
      H.mul_mem (H.mul_mem (hB (U_mem_borel _)) hLc) (hB (U_mem_borel _)), ?_, ?_, ?_, ?_⟩
    · sl2_simp; field_simp; ring
    · sl2_simp; field_simp; ring
    · sl2_simp; ring
    · sl2_simp; field_simp; ring
  have hLall : ∀ x : K, L x ∈ H := by
    intro x
    have h : L x = w * U (-x / c ^ 2) * w⁻¹ := by
      apply sl2_ext <;> sl2_simp <;> simp only [hw00, hw01, hw10, hw11] <;> field_simp <;> ring
    rw [h]
    exact H.mul_mem (H.mul_mem hwH (hB (U_mem_borel _))) (H.inv_mem hwH)
  rw [eq_top_iff, ← closure_U_L_eq_top, Subgroup.closure_le]
  rintro g (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · exact hB (U_mem_borel x)
  · exact hLall x

def W : SL(2, K) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

@[scoped simp] theorem W00 : (W : SL(2, K)) 0 0 = 0 := rfl
@[scoped simp] theorem W01 : (W : SL(2, K)) 0 1 = -1 := rfl
@[scoped simp] theorem W10 : (W : SL(2, K)) 1 0 = 1 := rfl
@[scoped simp] theorem W11 : (W : SL(2, K)) 1 1 = 0 := rfl

theorem exists_apply_ne_zero_of_normal (N : Subgroup SL(2, K)) [N.Normal]
    {g : SL(2, K)} (hg : g ∈ N) (h1 : g ≠ 1) (h2 : g ≠ -1) :
    ∃ n ∈ N, n 1 0 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hg10 : g 1 0 = 0 := hcon g hg

  have hWg : W * g * W⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance g hg W
  have hg01 : g 0 1 = 0 := by
    have h := hcon _ hWg
    have e : (W * g * W⁻¹ : SL(2, K)) 1 0 = -(g 0 1) := by
      sl2_simp; simp only [W10, W11]; rw [hg10]; ring
    rw [e] at h
    exact neg_eq_zero.mp h

  have hLg : L 1 * g * (L 1)⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance g hg (L 1)
  have hdiag : g 0 0 = g 1 1 := by
    have h := hcon _ hLg
    have e : (L 1 * g * (L 1)⁻¹ : SL(2, K)) 1 0 = g 0 0 - g 1 1 := by
      sl2_simp; rw [hg10, hg01]; ring
    rw [e] at h
    exact sub_eq_zero.mp h
  have hdet := det_expl g
  rw [hg01, hg10, ← hdiag, mul_zero, sub_zero] at hdet

  have hsq : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.mp hsq with h | h
  · apply h1
    have h' : g 0 0 = 1 := by linear_combination h
    apply sl2_ext <;> sl2_simp
    · exact h'
    · exact hg01
    · exact hg10
    · rw [← hdiag, h']
  · apply h2
    have h' : g 0 0 = -1 := by linear_combination h
    apply sl2_ext
    · rw [Matrix.SpecialLinearGroup.coe_neg]; simp [h']
    · rw [Matrix.SpecialLinearGroup.coe_neg]; simp [hg01]
    · rw [Matrix.SpecialLinearGroup.coe_neg]; simp [hg10]
    · rw [Matrix.SpecialLinearGroup.coe_neg]; simp [← hdiag, h']

theorem main (hK : 4 ≤ Cardinal.mk K) (N : Subgroup SL(2, K)) [N.Normal]
    (hN : ∃ g ∈ N, g ≠ 1 ∧ g ≠ -1) : N = ⊤ := by
  classical

  obtain ⟨t, ht⟩ := Cardinal.exists_notMem_of_length_lt [(0 : K), 1, -1]
    (lt_of_lt_of_le (by norm_num) hK)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ht
  obtain ⟨ht0, ht1, htm1⟩ := ht
  have ht2 : t ^ 2 ≠ 1 := by
    intro h
    have : (t - 1) * (t + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact ht1 (by linear_combination h')
    · exact htm1 (by linear_combination h')
  obtain ⟨g, hg, h1, h2⟩ := hN
  obtain ⟨n, hn, hc⟩ := exists_apply_ne_zero_of_normal N hg h1 h2

  have hsup : N ⊔ (borel : Subgroup SL(2, K)) = ⊤ :=
    eq_top_of_borel_le le_sup_right (Subgroup.mem_sup_left hn) hc

  haveI : Group.IsSolvable (borel : Subgroup SL(2, K)) := isSolvable_borel
  set π : SL(2, K) →* SL(2, K) ⧸ N := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective (π.comp (borel : Subgroup SL(2, K)).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ ((N ⊔ (borel : Subgroup SL(2, K)) : Subgroup SL(2, K)) : Set SL(2, K)) := by
      rw [hsup]; exact Subgroup.mem_top x
    rw [Subgroup.normal_mul] at hx
    obtain ⟨y, hy, b, hb, rfl⟩ := hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, hπ,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_iff_div_mem]

    have : b / (y * b) = y⁻¹ := by
      rw [div_eq_mul_inv, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [this]
    exact N.inv_mem hy
  haveI hsolv : Group.IsSolvable (SL(2, K) ⧸ N) := Group.isSolvable_of_surjective hsurj

  have hperf : commutator (SL(2, K) ⧸ N) = ⊤ := by
    have h := commutator_eq_top t ht0 ht2
    have : Subgroup.map π (commutator SL(2, K)) = commutator (SL(2, K) ⧸ N) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    rw [← this, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

  by_contra hne
  have hnt : Nontrivial (SL(2, K) ⧸ N) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    exact hne ((QuotientGroup.subsingleton_iff).1 hs)
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial (SL(2, K) ⧸ N)
  rw [hperf] at this
  exact lt_irrefl _ this

end SL2NormalCC
p2m_reactivate "P2MW.S_Matrix_SpecialLinearGroup_eq_top_of_normal_of_exists_ne_one_ne_neg_one.SL2NormalCC"

theorem solution
    {K : Type*} [Field K] (hK : 4 ≤ Cardinal.mk K)
    (N : Subgroup SL(2, K)) [N.Normal]
    (hN : ∃ g ∈ N, g ≠ 1 ∧ g ≠ -1) :
    N = ⊤ :=
  SL2NormalCC.main hK N hN

end S_Matrix_SpecialLinearGroup_eq_top_of_normal_of_exists_ne_one_ne_neg_one
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_eq_top_of_normal_of_exists_ne_one_ne_neg_one (solution)
