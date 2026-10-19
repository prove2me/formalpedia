-- Prove2me | solution 1 for OAI.CPTSeparation.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T21:18:55.679933+00:00
-- url     : https://prove2.me/submissions/5ca437f8-abd2-49f7-93ab-cd7efb73b557

import Mathlib
import Definitions.Def_ChoicelessPolynomialTime
import Definitions.Def_OAIQWCPT000
import Theorems.Thm_OAI_CPTSeparation_Grid_grid_hf_transfer

section
-- module Solutions.OAIQW_CPTSeparation.Compat
namespace OAI.CPTSeparation
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434


end OAI.CPTSeparation
end

section
-- module Solutions.OAIQW_CPTSeparation.Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation

namespace Support

theorem omega_swap (u v : Plane) : omega v u = -omega u v := by
  simp [omega]; ring

variable {F K : Type} [finiteF : Fintype F] [AddCommGroup K] [scalarModuleK : Module Scalar K]

theorem correction_swap (cycle : F → K) (a b : F → Plane) :
    correction cycle b a = -correction cycle a b := by
  unfold correction
  rw [← smul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  rw [omega_swap, neg_smul]

namespace H

variable (cycle : F → K)

theorem commutator (x y : H cycle) :
    x * y * x⁻¹ * y⁻¹ = central cycle (∑ f, omega (x.face f) (y.face f) • cycle f) := by
  apply H.ext
  · simp only [mul_face, inv_face, central]
    abel
  · simp only [mul_flow, mul_face, inv_flow, inv_face,
      correction_add_left, correction_neg_left,
      correction_neg_right, correction_self,
      zero_add, add_zero, central]
    have hc : correction cycle x.face y.face + correction cycle x.face y.face =
        ∑ f, omega (x.face f) (y.face f) • cycle f := by
      rw [correction, ← add_smul]
      have h : (2 : Scalar) + 2 = 1 := by decide
      rw [h, one_smul]
    have hs := correction_swap cycle x.face y.face
    rw [hs]
    abel_nf at hc ⊢
    exact hc

theorem commutator_mem_centralPart (S : Subgroup (H cycle))
    {a b : F → Plane} (ha : a ∈ projected cycle S) (hb : b ∈ projected cycle S) :
    (∑ f, omega (a f) (b f) • cycle f) ∈ centralPart cycle S := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  rw [mem_centralPart, ← commutator]
  exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)

theorem stabilizer_isotropic (S : Subgroup (H cycle)) (lambda : K →ₗ[Scalar] Scalar)
    (hlambda : ∀ k ∈ centralPart cycle S, lambda k = 0)
    {a b : F → Plane} (ha : a ∈ projected cycle S) (hb : b ∈ projected cycle S) :
    (∑ f, lambda (cycle f) * omega (a f) (b f)) = 0 := by
  have h := hlambda _ (commutator_mem_centralPart cycle S ha hb)
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h

theorem subgroup_card [FiniteDimensional Scalar K] (S : Subgroup (H cycle)) :
    Nat.card S = 3 ^ (Module.finrank Scalar (projected cycle S) +
      Module.finrank Scalar (centralPart cycle S)) := by
  rw [Nat.card_congr (subgroupEquiv cycle S), Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := Scalar) (V := projected cycle S),
    Module.natCard_eq_pow_finrank (K := Scalar) (V := centralPart cycle S)]
  have h : Nat.card Scalar = 3 := by simp [Scalar, Nat.card_eq_fintype_card]
  rw [h, ← pow_add]

theorem ambient_card [FiniteDimensional Scalar K] :
    Nat.card (H cycle) = 3 ^ (Module.finrank Scalar (F → Plane) + Module.finrank Scalar K) := by
  rw [Nat.card_congr (productEquiv cycle), Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := Scalar) (V := F → Plane),
    Module.natCard_eq_pow_finrank (K := Scalar) (V := K)]
  have h : Nat.card Scalar = 3 := by simp [Scalar, Nat.card_eq_fintype_card]
  rw [h, ← pow_add]

theorem subgroup_index [FiniteDimensional Scalar K] (S : Subgroup (H cycle)) :
    S.index = 3 ^ ((Module.finrank Scalar (F → Plane) - Module.finrank Scalar (projected cycle S)) +
      (Module.finrank Scalar K - Module.finrank Scalar (centralPart cycle S))) := by
  have hu := Submodule.finrank_le (projected cycle S)
  have hk := Submodule.finrank_le (centralPart cycle S)
  have hc := S.index_mul_card
  rw [subgroup_card cycle S, ambient_card cycle] at hc
  apply Nat.mul_right_cancel (m := 3 ^ (Module.finrank Scalar (projected cycle S) +
    Module.finrank Scalar (centralPart cycle S))) (by positivity)
  rw [hc, ← pow_add]
  congr 1
  omega

end H

theorem diagonalForm_finrank_ker (weight : F → Scalar) :
    Module.finrank Scalar (diagonalForm weight).ker =
      2 * Fintype.card {f : F // weight f = 0} := by
  classical
  rw [(diagonalKerEquiv weight).finrank_eq, Module.finrank_pi_fintype]
  simp [Plane, Module.finrank_prod, Nat.mul_comm]

theorem nonzero_blocks_le_codim (weight : F → Scalar)
    (U : Submodule Scalar (F → Plane))
    (hisotropic : ∀ a ∈ U, ∀ b ∈ U, diagonalForm weight a b = 0) :
    Fintype.card {f : F // weight f ≠ 0} ≤
      Module.finrank Scalar (F → Plane) - Module.finrank Scalar U := by
  classical
  have hle : U ≤ (diagonalForm weight).orthogonal U := by
    intro a ha
    exact fun b hb => hisotropic b hb a ha
  have hd := Submodule.finrank_mono hle
  have heq := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := diagonalForm weight) U
  have hker := Submodule.finrank_mono
    (show U ⊓ (diagonalForm weight).ker ≤ (diagonalForm weight).ker from inf_le_right)
  have hcard : Fintype.card {f : F // weight f ≠ 0} =
      Fintype.card F - Fintype.card {f : F // weight f = 0} :=
    Fintype.card_subtype_compl (fun f : F => weight f = 0)
  have hcardle := Fintype.card_subtype_le (fun f : F => weight f = 0)
  have hdimu : Module.finrank Scalar U ≤ Module.finrank Scalar (F → Plane) :=
    Submodule.finrank_le U
  have hdim : Module.finrank Scalar (F → Plane) = 2 * Fintype.card F := by
    rw [Module.finrank_pi_fintype]
    simp [Plane, Module.finrank_prod, Nat.mul_comm]
  rw [diagonalForm_finrank_ker] at hker
  rw [hdim] at heq hdimu ⊢
  omega

end Support

end CPTSeparation

namespace CPTSeparation.Grid

variable {n : ℕ}

theorem single_mul_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (z : Scalar) (l : ι → Scalar) :
    (∑ j, (Pi.single i z : ι → Scalar) j * l j) = z * l i := by
  classical
  simp only [Pi.single_apply, ite_mul, zero_mul]
  simp

@[simp] theorem curl_xy (l : Edge n → Scalar) (i j : Fin n) (k : Fin (n+1)) :
    curl l (.inl (i,j,k)) = l (ex i j.castSucc k) + l (ey i.succ j k) -
      l (ex i j.succ k) - l (ey i.castSucc j k) := by
  classical
  simp only [curl, cycle, Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, single_mul_sum, one_mul]

@[simp] theorem curl_xz (l : Edge n → Scalar) (i k : Fin n) (j : Fin (n+1)) :
    curl l (.inr (.inl (i,j,k))) = l (ex i j k.castSucc) + l (ez i.succ j k) -
      l (ex i j k.succ) - l (ez i.castSucc j k) := by
  classical
  simp only [curl, cycle, Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, single_mul_sum, one_mul]

@[simp] theorem curl_yz (l : Edge n → Scalar) (j k : Fin n) (i : Fin (n+1)) :
    curl l (.inr (.inr (i,j,k))) = l (ey i j k.castSucc) + l (ez i j.succ k) -
      l (ey i j k.succ) - l (ez i j.castSucc k) := by
  classical
  simp only [curl, cycle, Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, single_mul_sum, one_mul]

@[simp] theorem curl_gradient (φ : Vertex n → Scalar) (f : Face n) :
    curl (gradient φ) f = 0 := by
  rcases f with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals simp [gradient, head, tail, ex, ey, ez]

theorem prefix_step (l : Fin n → Scalar) (i : Fin n) :
    prefixSum l i.succ - prefixSum l i.castSucc = l i := by
  classical
  have h : prefixSum l i.succ = prefixSum l i.castSucc + l i := by
    unfold prefixSum
    have hs : (∑ a : Fin n, if a = i then l a else 0) = l i := by simp
    rw [← hs, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Fin.val_succ, Fin.val_castSucc]
    by_cases hai : a.val < i.val
    · have hne : a ≠ i := by intro h; subst a; omega
      simp [hai, hne, show a.val < i.val+1 by omega]
    · by_cases heq : a = i
      · subst a; simp
      · have hge : i.val + 1 ≤ a.val := by
          have : a.val ≠ i.val := by intro h; exact heq (Fin.ext h)
          omega
        simp [hai, heq, show ¬a.val < i.val+1 by omega]
  rw [h]
  abel

@[simp] theorem residual1_x (l : Edge n → Scalar) (i : Fin n) (j k : Fin (n+1)) :
    residual1 l (ex i j k) = 0 := by
  simp only [residual1, Pi.sub_apply, gradient, head, tail, ex, phi1, prefix_step, sub_self]

@[simp] theorem residual2_x (l : Edge n → Scalar) (i0 : Fin (n+1))
    (i : Fin n) (j k : Fin (n+1)) : residual2 l i0 (ex i j k) = 0 := by
  rw [residual2, Pi.sub_apply, residual1_x]
  simp only [gradient, phi2, head, tail, ex, sub_self]

@[simp] theorem residual2_y (l : Edge n → Scalar) (i0 : Fin (n+1))
    (j : Fin n) (k : Fin (n+1)) : residual2 l i0 (ey i0 j k) = 0 := by
  simp only [residual2, Pi.sub_apply, gradient, phi2, head, tail, ey,
    prefix_step, sub_self]

@[simp] theorem residual_x (l : Edge n → Scalar) (i0 : Fin (n+1))
    (i : Fin n) (j k : Fin (n+1)) : residual l i0 (ex i j k) = 0 := by
  rw [residual, Pi.sub_apply, residual2_x]
  simp only [gradient, phi3, head, tail, ex, sub_self]

@[simp] theorem residual_y (l : Edge n → Scalar) (i0 : Fin (n+1))
    (j : Fin n) (k : Fin (n+1)) : residual l i0 (ey i0 j k) = 0 := by
  rw [residual, Pi.sub_apply, residual2_y]
  simp only [gradient, phi3, head, tail, ey, sub_self]

@[simp] theorem residual_z (l : Edge n → Scalar) (i0 : Fin (n+1))
    (k : Fin n) : residual l i0 (ez i0 0 k) = 0 := by
  simp only [residual, Pi.sub_apply, gradient, phi3, head, tail, ez,
    prefix_step, sub_self]

@[simp] theorem curl_residual (l : Edge n → Scalar) (i0 : Fin (n+1)) (f : Face n) :
    curl (residual l i0) f = curl l f := by
  simp [residual, residual2, residual1]

theorem residual_as_gradient (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    residual l i0 = l - gradient (phi1 l + phi2 l i0 + phi3 l i0) := by
  funext e
  simp only [residual, residual2, residual1, Pi.sub_apply, gradient, Pi.add_apply]
  ring

theorem line_constant {g : Fin (n+1) → Scalar}
    (h : ∀ a : Fin n, g a.succ = g a.castSucc) (i j : Fin (n+1)) : g i = g j := by
  have hz : ∀ a, g a = g 0 := by
    intro a
    induction a using Fin.induction with
    | zero => rfl
    | succ a ha => exact (h a).trans ha
  exact (hz i).trans (hz j).symm

theorem residual_y_witness (l : Edge n → Scalar) (i0 i : Fin (n+1))
    (j : Fin n) (k : Fin (n+1)) (h : residual l i0 (ey i j k) ≠ 0) :
    ∃ a : Fin n, curl l (.inl (a,j,k)) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hd : ∀ a : Fin n, residual l i0 (ey a.succ j k) =
      residual l i0 (ey a.castSucc j k) := by
    intro a
    have hc := curl_residual l i0 (.inl (a,j,k))
    rw [curl_xy, residual_x, residual_x, hn a] at hc
    simpa using sub_eq_zero.mp hc
  have hc := line_constant (g := fun a => residual l i0 (ey a j k)) hd i i0
  exact h (hc.trans (residual_y l i0 j k))

theorem residual_z_witness (l : Edge n → Scalar) (i0 i j : Fin (n+1))
    (k : Fin n) (h : residual l i0 (ez i j k) ≠ 0) :
    (∃ a : Fin n, curl l (.inr (.inl (a,j,k))) ≠ 0) ∨
    (∃ b : Fin n, curl l (.inr (.inr (i0,b,k))) ≠ 0) := by
  by_contra hn
  push Not at hn
  have hx : ∀ a : Fin n, residual l i0 (ez a.succ j k) =
      residual l i0 (ez a.castSucc j k) := by
    intro a
    have hc := curl_residual l i0 (.inr (.inl (a,j,k)))
    rw [curl_xz, residual_x, residual_x, hn.1 a] at hc
    simpa using sub_eq_zero.mp hc
  have hy : ∀ b : Fin n, residual l i0 (ez i0 b.succ k) =
      residual l i0 (ez i0 b.castSucc k) := by
    intro b
    have hc := curl_residual l i0 (.inr (.inr (i0,b,k)))
    rw [curl_yz, residual_y, residual_y, hn.2 b] at hc
    simpa using sub_eq_zero.mp hc
  exact h ((line_constant (g := fun a => residual l i0 (ez a j k)) hx i i0).trans ((line_constant (g := fun b => residual l i0 (ez i0 b k)) hy j 0).trans
    (residual_z l i0 k)))

theorem card_le_product_of_witness {α β γ : Type*} [DecidableEq α] [Fintype β]
    (s : Finset α) (t : Finset γ) (f : β → γ → α)
    (h : ∀ x ∈ s, ∃ b c, c ∈ t ∧ f b c = x) :
    s.card ≤ Fintype.card β * t.card := by
  classical
  have hs : s ⊆ (Finset.univ ×ˢ t).image (fun p => f p.1 p.2) := by
    intro x hx
    obtain ⟨b,c,hc,hbc⟩ := h x hx
    exact Finset.mem_image.mpr ⟨(b,c), by simp [hc], hbc⟩
  calc
    s.card ≤ ((Finset.univ ×ˢ t).image (fun p => f p.1 p.2)).card := Finset.card_le_card hs
    _ ≤ (Finset.univ ×ˢ t).card := Finset.card_image_le
    _ = Fintype.card β * t.card := by simp

theorem card_le_two_products_of_witness {α β γ δ ε : Type*} [DecidableEq α]
    [Fintype β] [Fintype δ] (s : Finset α) (t : Finset γ) (u : Finset ε)
    (f : β → γ → α) (g : δ → ε → α)
    (h : ∀ x ∈ s, (∃ b c, c ∈ t ∧ f b c = x) ∨ (∃ d e, e ∈ u ∧ g d e = x)) :
    s.card ≤ Fintype.card β * t.card + Fintype.card δ * u.card := by
  classical
  let sf := (Finset.univ ×ˢ t).image (fun p => f p.1 p.2)
  let sg := (Finset.univ ×ˢ u).image (fun p => g p.1 p.2)
  have hs : s ⊆ sf ∪ sg := by
    intro x hx
    rcases h x hx with ⟨b,c,hc,hbc⟩ | ⟨d,e,he,hde⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(b,c), by simp [hc], hbc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(d,e), by simp [he], hde⟩)
  calc
    s.card ≤ (sf ∪ sg).card := Finset.card_le_card hs
    _ ≤ sf.card + sg.card := Finset.card_union_le _ _
    _ ≤ (Finset.univ ×ˢ t).card + (Finset.univ ×ˢ u).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by simp

theorem sum_badSlice (l : Edge n → Scalar) :
    (∑ i : Fin (n+1), (badSlice l i).card) = (badYZ l).card := by
  simp only [badSlice, badYZ, nonzeroSet, Finset.card_filter, Fintype.sum_prod_type]

theorem exists_sparse_slice (l : Edge n → Scalar) :
    ∃ i0 : Fin (n+1), (n+1) * (badSlice l i0).card ≤ (badYZ l).card := by
  obtain ⟨i0, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin (n+1) => (badSlice l i).card) (by simp)
  refine ⟨i0, ?_⟩
  calc
    (n+1) * (badSlice l i0).card = ∑ _ : Fin (n+1), (badSlice l i0).card := by simp
    _ ≤ ∑ i : Fin (n+1), (badSlice l i).card := Finset.sum_le_sum hi
    _ = _ := sum_badSlice l

theorem count_residual_y (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    (nonzeroSet (fun p : EdgeY n => residual l i0 (ey p.1 p.2.1 p.2.2))).card ≤
      (n+1) * (badXY l).card := by
  have h := card_le_product_of_witness (β := Fin (n+1))
    (nonzeroSet (fun p : EdgeY n => residual l i0 (ey p.1 p.2.1 p.2.2)))
    (badXY l) (fun i f => (i,f.2.1,f.2.2)) (by
      rintro ⟨i,j,k⟩ hx
      obtain ⟨a,ha⟩ := residual_y_witness l i0 i j k (by simpa only [mem_nonzeroSet] using hx)
      exact ⟨i,(a,j,k), by simpa [badXY] using ha, rfl⟩)
  simpa only [Fintype.card_fin] using h

theorem count_residual_z (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    (nonzeroSet (fun p : EdgeZ n => residual l i0 (ez p.1 p.2.1 p.2.2))).card ≤
      (n+1) * (badXZ l).card + (n+1)^2 * (badSlice l i0).card := by
  have h := card_le_two_products_of_witness (β := Fin (n+1))
    (δ := Fin (n+1) × Fin (n+1))
    (nonzeroSet (fun p : EdgeZ n => residual l i0 (ez p.1 p.2.1 p.2.2)))
    (badXZ l) (badSlice l i0) (fun i f => (i,f.2.1,f.2.2))
    (fun p f => (p.1,p.2,f.2)) (by
      rintro ⟨i,j,k⟩ hx
      rcases residual_z_witness l i0 i j k (by simpa only [mem_nonzeroSet] using hx) with ⟨a,ha⟩ | ⟨b,hb⟩
      · exact Or.inl ⟨i,(a,j,k), by simpa [badXZ] using ha, rfl⟩
      · exact Or.inr ⟨(i,j),(b,k), by simpa [badSlice] using hb, rfl⟩)
  simpa only [Fintype.card_fin, Fintype.card_prod, pow_two] using h

theorem count_curl (l : Edge n → Scalar) :
    (nonzeroSet (curl l)).card = (badXY l).card + (badXZ l).card + (badYZ l).card := by
  simp only [nonzeroSet, badXY, badXZ, badYZ, Finset.card_filter, Fintype.sum_sum_type]
  omega

theorem count_residual (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    (nonzeroSet (residual l i0)).card ≤
      (n+1) * ((badXY l).card + (badXZ l).card) + (n+1)^2 * (badSlice l i0).card := by
  have heq : (nonzeroSet (residual l i0)).card =
      (nonzeroSet (fun p : EdgeY n => residual l i0 (ey p.1 p.2.1 p.2.2))).card +
      (nonzeroSet (fun p : EdgeZ n => residual l i0 (ez p.1 p.2.1 p.2.2))).card := by
    simp only [nonzeroSet, Finset.card_filter, Fintype.sum_sum_type]
    have hx : (∑ p : EdgeX n, if residual l i0 (.inl p) ≠ 0 then 1 else 0) = (0 : ℕ) := by
      apply Finset.sum_eq_zero
      rintro ⟨i,j,k⟩ _
      change (if residual l i0 (ex i j k) ≠ 0 then 1 else 0) = 0
      simp only [residual_x, ne_eq, not_true_eq_false, ite_false]
    rw [hx, zero_add]
    rfl
  rw [heq, Nat.mul_add]
  have hy := count_residual_y l i0
  have hz := count_residual_z l i0
  omega

theorem sparse_cochain (l : Edge n → Scalar) :
    ∃ φ : Vertex n → Scalar,
      (nonzeroSet (l - gradient φ)).card ≤ (n+1) * (nonzeroSet (curl l)).card := by
  obtain ⟨i0,hi⟩ := exists_sparse_slice l
  refine ⟨phi1 l + phi2 l i0 + phi3 l i0, ?_⟩
  rw [← residual_as_gradient, count_curl]
  calc
    (nonzeroSet (residual l i0)).card ≤
      (n+1) * ((badXY l).card + (badXZ l).card) + (n+1)^2 * (badSlice l i0).card :=
        count_residual l i0
    _ ≤ (n+1) * ((badXY l).card + (badXZ l).card) + (n+1) * (badYZ l).card := by
      apply Nat.add_le_add_left
      simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul_left (n+1) hi
    _ = _ := by ring

end CPTSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Grid

section

open Support

variable {n : ℕ}

theorem pairing_boundary (φ : Vertex n → Scalar) (z : Edge n → Scalar) :
    pairing φ (boundary z) = pairing (gradient φ) z := by
  have hb : boundary z = ∑ e : Edge n, z e •
      ((Pi.single (head e) (1 : Scalar) : Vertex n → Scalar) - Pi.single (tail e) 1) := rfl
  rw [hb]
  simp only [map_sum, map_smul, map_sub, pairing_single, mul_one, smul_eq_mul]
  change (∑ e, z e * (φ (head e) - φ (tail e))) =
    ∑ e, (φ (head e) - φ (tail e)) * z e
  apply Finset.sum_congr rfl
  intro e _
  ring

@[simp] theorem pairing_gradient_flow (φ : Vertex n → Scalar) (k : FlowSpace n) :
    pairing (gradient φ) k.val = 0 := by
  rw [← pairing_boundary, LinearMap.mem_ker.mp k.property, map_zero]

theorem pairing_sub {ι : Type*} [Fintype ι] (l r z : ι → Scalar) :
    pairing (l-r) z = pairing l z - pairing r z := by
  simp only [pairing, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
    sub_mul, Finset.sum_sub_distrib]

theorem exists_representative (lambda : FlowSpace n →ₗ[Scalar] Scalar) :
    ∃ l : Edge n → Scalar, ∀ k : FlowSpace n, pairing l k.val = lambda k := by
  obtain ⟨g,hg⟩ := LinearMap.exists_extend lambda
  let l : Edge n → Scalar := fun e => g (Pi.single e 1)
  have hrep (z : Edge n → Scalar) : g z = pairing l z := by
    have hz : (∑ e : Edge n, z e • Pi.single e (1 : Scalar)) = z := by
      classical
      ext e
      simp [Finset.sum_apply, Pi.single_apply]
    calc
      g z = g (∑ e : Edge n, z e • Pi.single e (1 : Scalar)) := congrArg g hz.symm
      _ = ∑ e, z e * l e := by simp only [map_sum, map_smul, smul_eq_mul]; rfl
      _ = pairing l z := by
        change (∑ e, z e * l e) = ∑ e, l e * z e
        apply Finset.sum_congr rfl
        intro e _
        ring
  refine ⟨l, fun k => ?_⟩
  rw [← hrep]
  exact LinearMap.congr_fun hg k

theorem curl_representative (lambda : FlowSpace n →ₗ[Scalar] Scalar) (l : Edge n → Scalar)
    (hl : ∀ k : FlowSpace n, pairing l k.val = lambda k) (f : Face n) :
    curl l f = lambda (flowCycle f) := by
  rw [← hl]
  simp only [curl, pairing, LinearMap.coe_mk, AddHom.coe_mk, flowCycle, mul_comm]

theorem curl_count_le_codim (S : Subgroup (BoxGroup n))
    (lambda : FlowSpace n →ₗ[Scalar] Scalar)
    (hlambda : lambda ∈ (Support.H.centralPart flowCycle S).dualAnnihilator)
    (l : Edge n → Scalar) (hl : ∀ k : FlowSpace n, pairing l k.val = lambda k) :
    (nonzeroSet (curl l)).card ≤ faceCodim S := by
  classical
  have hiso : ∀ a ∈ Support.H.projected flowCycle S,
      ∀ b ∈ Support.H.projected flowCycle S, Support.diagonalForm (curl l) a b = 0 := by
    intro a ha b hb
    simp only [Support.diagonalForm_apply, curl_representative lambda l hl]
    exact Support.H.stabilizer_isotropic flowCycle S lambda
      ((Submodule.mem_dualAnnihilator lambda).mp hlambda) ha hb
  have h := Support.nonzero_blocks_le_codim (curl l)
    (Support.H.projected flowCycle S) hiso
  simpa only [nonzeroSet, faceCodim, Fintype.card_subtype] using h

theorem sparse_annihilator (S : Subgroup (BoxGroup n))
    (lambda : FlowSpace n →ₗ[Scalar] Scalar)
    (hlambda : lambda ∈ (Support.H.centralPart flowCycle S).dualAnnihilator) :
    ∃ r : Edge n → Scalar,
      (∀ k : FlowSpace n, pairing r k.val = lambda k) ∧
      (nonzeroSet r).card ≤ (n+1) * faceCodim S := by
  obtain ⟨l,hl⟩ := exists_representative lambda
  obtain ⟨φ,hφ⟩ := sparse_cochain l
  refine ⟨l - gradient φ, ?_, hφ.trans (Nat.mul_le_mul_left _ (curl_count_le_codim S lambda hlambda l hl))⟩
  intro k
  rw [pairing_sub, pairing_gradient_flow, sub_zero, hl]

theorem subgroup_support_edges (S : Subgroup (BoxGroup n)) :
    ∃ T : Finset (Edge n),
      T.card ≤ (n+1) * faceCodim S * flowCodim S ∧
      ∀ k : FlowSpace n, (∀ e ∈ T, k.val e = 0) →
        Support.H.central flowCycle k ∈ S := by
  classical
  let W := (Support.H.centralPart flowCycle S).dualAnnihilator
  have : Module.Free Scalar W := Module.Free.of_divisionRing Scalar W
  let b := Module.finBasis Scalar W
  have hd : Module.finrank Scalar W = flowCodim S := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq
      (Support.H.centralPart flowCycle S)
    change Module.finrank Scalar (Support.H.centralPart flowCycle S) +
      Module.finrank Scalar W = Module.finrank Scalar (FlowSpace n) at h
    unfold flowCodim
    omega
  have hr : ∀ i : Fin (Module.finrank Scalar W), ∃ r : Edge n → Scalar,
      (∀ k : FlowSpace n, pairing r k.val = (b i).val k) ∧
      (nonzeroSet r).card ≤ (n+1) * faceCodim S := by
    intro i
    exact sparse_annihilator S (b i).val (b i).property
  choose r hr hbnd using hr
  let T := Finset.univ.biUnion (fun i => nonzeroSet (r i))
  refine ⟨T, ?_, ?_⟩
  · calc
      T.card ≤ ∑ i : Fin (Module.finrank Scalar W), (nonzeroSet (r i)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _ : Fin (Module.finrank Scalar W), (n+1) * faceCodim S :=
        Finset.sum_le_sum (fun i _ => hbnd i)
      _ = (n+1) * faceCodim S * flowCodim S := by simp [hd, Nat.mul_comm]
  · intro k hk
    apply (Support.H.mem_centralPart flowCycle S k).mp
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
      (Support.H.centralPart flowCycle S) k).mp
    have hbi (i : Fin (Module.finrank Scalar W)) : (b i).val k = 0 := by
      rw [← hr i k]
      change (∑ e, r i e * k.val e) = 0
      apply Finset.sum_eq_zero
      intro e _
      by_cases he : r i e = 0
      · simp [he]
      · have hmem : e ∈ T := Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ _, (mem_nonzeroSet _ _).mpr he⟩
        simp [hk e hmem]
    intro lambda hlambda
    let w : W := ⟨lambda, hlambda⟩
    have heq := congrArg (fun w : W => w.val k) (b.sum_repr w)
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hbi, mul_zero, Finset.sum_const_zero] at heq
    exact heq.symm

theorem box_subgroup_index (S : Subgroup (BoxGroup n)) :
    S.index = 3 ^ (faceCodim S + flowCodim S) :=
  Support.H.subgroup_index flowCycle S

theorem orbit_card_eq_power {X : Type*} [MulAction (BoxGroup n) X] (x : X) :
    Nat.card (MulAction.orbit (BoxGroup n) x) =
      3 ^ (faceCodim (MulAction.stabilizer (BoxGroup n) x) +
        flowCodim (MulAction.stabilizer (BoxGroup n) x)) := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (BoxGroup n) x)]
  exact box_subgroup_index (MulAction.stabilizer (BoxGroup n) x)

theorem small_orbit_support_edges {X : Type*} [MulAction (BoxGroup n) X]
    (x : X) (N : ℕ) (hN : 0 < N) (q : ℝ) (_hq : 0 ≤ q)
    (horbit : (Nat.card (MulAction.orbit (BoxGroup n) x) : ℝ) ≤ (N : ℝ) ^ q) :
    ∃ T : Finset (Edge n),
      (T.card : ℝ) ≤ 2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2 ∧
      ∀ k : FlowSpace n, (∀ e ∈ T, k.val e = 0) →
        Support.H.central flowCycle k • x = x := by
  let S := MulAction.stabilizer (BoxGroup n) x
  obtain ⟨T,hcard,hfix⟩ := subgroup_support_edges S
  have heq := orbit_card_eq_power (n := n) x
  have horbit' : (3 : ℝ) ^ (faceCodim S + flowCodim S) ≤ (N : ℝ) ^ q := by
    rw [heq, Nat.cast_pow, Nat.cast_ofNat] at horbit
    exact horbit
  have hlog := Real.logb_le_logb_of_le (b := 3) (by norm_num : (1 : ℝ) < 3)
    (by positivity : (0 : ℝ) < 3 ^ (faceCodim S + flowCodim S)) horbit'
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
    Real.logb_rpow_eq_mul_logb_of_pos (by exact_mod_cast hN), Nat.cast_add] at hlog
  have ha : 0 ≤ (faceCodim S : ℝ) := Nat.cast_nonneg _
  have hd : 0 ≤ (flowCodim S : ℝ) := Nat.cast_nonneg _
  have hab : (faceCodim S : ℝ) * flowCodim S ≤ (q * Real.logb 3 N)^2 := by
    nlinarith [sq_nonneg ((faceCodim S : ℝ) - flowCodim S)]
  have hc : (T.card : ℝ) ≤ (n+1 : ℝ) * faceCodim S * flowCodim S := by
    exact_mod_cast hcard
  refine ⟨T, ?_, fun k hk => hfix k hk⟩
  calc
    (T.card : ℝ) ≤ (n+1 : ℝ) * faceCodim S * flowCodim S := hc
    _ ≤ (n+1 : ℝ) * (q * Real.logb 3 N)^2 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hab (by positivity)
    _ ≤ 2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2 := by
      have hpos : 0 ≤ (n+1 : ℝ) * (q * Real.logb 3 N)^2 := by positivity
      nlinarith

end

open Support

end CPTSeparation.Grid

namespace CPTSeparation

namespace Input

variable {A B : Type} [finiteA : Fintype A] [finiteB : Fintype B]

namespace Iso

variable {S : Input A} {T : Input B} (e : S.Iso T)

include e in
theorem query_map : S.query → T.query := by
  rintro ⟨lambda, mu, hn, hc⟩
  refine ⟨lambda ∘ e.configEquiv.symm, mu ∘ e.edgeEquiv.symm, ?_, ?_⟩
  · intro t
    obtain ⟨t, rfl⟩ := e.configEquiv.surjective t
    calc
      (∑ a : T.Config, if T.rel .VB (e.configEquiv t) a then
        (lambda ∘ e.configEquiv.symm) a else 0) =
          ∑ a : S.Config, if S.rel .VB t a then lambda a else 0 := by
            symm
            apply Fintype.sum_equiv e.configEquiv
            intro a
            simp [configEquiv, e.rel_eq]
      _ = 1 := hn t
  · intro t y ht
    obtain ⟨t, rfl⟩ := e.configEquiv.surjective t
    obtain ⟨y, rfl⟩ := e.edgeEquiv.surjective y
    have hi : S.incident t y := (e.incident_eq t y).mp ht
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    calc
      mu y = ∑ a : S.Config, if S.rel .VB t a then lambda a * S.coefficient y a
        else 0 := hc t y hi
      _ = ∑ a : T.Config, if T.rel .VB (e.configEquiv t) a then
          (lambda ∘ e.configEquiv.symm) a * T.coefficient (e.edgeEquiv y) a else 0 := by
        apply Fintype.sum_equiv e.configEquiv
        intro a
        simp [configEquiv_val, e.rel_eq]

end Iso

theorem query_invariant {S : Input A} {T : Input B} (e : S.Iso T) :
    S.query ↔ T.query := ⟨e.query_map, e.symm.query_map⟩

end Input

end CPTSeparation

namespace CPTSeparation.Grid

section

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

theorem edge_support_tuple {X : Type*} [MulAction (BoxGroup n) X]
    (T : Finset (Edge n)) (x : X)
    (hx : ∀ k : FlowSpace n, (∀ e ∈ T, k.val e = 0) →
      Support.H.central flowCycle k • x = x) :
    ∃ alpha : Fin T.card → Atom b, ∀ k : CentralGroup n,
      (∀ i, k • alpha i = alpha i) → centralHom k • x = x := by
  classical
  let alpha (i : Fin T.card) : Atom b := zeroEdgeAtom b ((T.equivFin).symm i).val
  refine ⟨alpha,?_⟩
  intro k hk
  apply hx k.toAdd
  intro e he
  let i : Fin T.card := T.equivFin ⟨e,he⟩
  have hi : ((T.equivFin).symm i).val = e := by simp [i]
  have hfix := hk i
  change Support.H.central flowCycle k.toAdd •
      zeroEdgeAtom b ((T.equivFin).symm i).val = _ at hfix
  rw [central_fix_zeroEdgeAtom_iff] at hfix
  simpa only [hi] using hfix

end

section

variable {n : ℕ}

theorem sum_boundary (z : Edge n → Scalar) : ∑ v, boundary z v = 0 := by
  classical
  simp only [boundary, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  simp [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum]

theorem head_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : head e = head e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,head]

theorem tail_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : tail e = tail e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,tail]

theorem degree_le_six (v : Vertex n) :
    Fintype.card {e : Edge n // head e = v ∨ tail e = v} ≤ 6 := by
  classical
  let f : {e : Edge n // head e = v ∨ tail e = v} → Fin 3 × Bool :=
    fun e => (edgeAxis e.val, decide (head e.val = v))
  have hf : Function.Injective f := by
    intro e e' heq
    have ha : edgeAxis e.val = edgeAxis e'.val := congrArg Prod.fst heq
    have hb : decide (head e.val = v) = decide (head e'.val = v) := congrArg Prod.snd heq
    apply Subtype.ext
    by_cases he : head e.val = v
    · have he' : head e'.val = v := by simpa only [he,decide_true,true_eq_decide_iff] using hb
      exact head_injective_on_axis ha (he.trans he'.symm)
    · have he' : head e'.val ≠ v := by simpa only [he,decide_false,false_eq_decide_iff] using hb
      exact tail_injective_on_axis ha
        ((e.property.resolve_left he).trans (e'.property.resolve_left he').symm)
  have h := Fintype.card_le_of_injective f hf
  simpa using h

end

section

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

theorem rel_z_edge (e f : Edge n) (g : LocalGroup e) (h : LocalGroup f) (d : Scalar)
    (hz : (atomInput b).rel (.Z d) (queryEdge (b := b) e g) (queryEdge (b := b) f h) = true) : e = f := by
  rw [atomInput_rel_true] at hz
  cases hz
  rfl

theorem sum_queryEdges {M : Type*} [AddCommMonoid M] (f : (atomInput b).Edge → M) :
    (∑ y, f y) = ∑ e, ∑ g, f (queryEdge e g) := by
  rw [← (queryEdgeEquiv (b := b)).sum_comp f,Fintype.sum_sigma]
  rfl

theorem sum_queryConfigs {M : Type*} [AddCommMonoid M] (f : (atomInput b).Config → M) :
    (∑ a, f a) = ∑ v, ∑ t, f (queryConfig v t) := by
  rw [← (queryConfigEquiv (b := b)).sum_comp f,Fintype.sum_sigma]
  rfl

theorem zsum_same (e : Edge n) (g h : LocalGroup e) :
    (∑ d : Scalar, if (atomInput b).rel (.Z d)
      (queryEdge (b := b) e g) (queryEdge (b := b) e h) then d else 0) = (g⁻¹*h).flow := by
  simp only [rel_z_same]
  simp

theorem zsum_ne (e f : Edge n) (g : LocalGroup e) (h : LocalGroup f) (hne : e ≠ f) :
    (∑ d : Scalar, if (atomInput b).rel (.Z d)
      (queryEdge (b := b) e g) (queryEdge (b := b) f h) then d else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro d _
  have hh : ¬(atomInput b).rel (.Z d)
      (queryEdge (b := b) e g) (queryEdge (b := b) f h) = true := fun hd =>
    hne (rel_z_edge e f g h d hd)
  simp [hh]

theorem coefficient_incident (v : Vertex n) (s : Configuration b v)
    (e : Edge n) (g : LocalGroup e) (he : incident v e) :
    (atomInput b).coefficient (queryEdge e g) (queryConfig v s) =
      (g⁻¹ * s.state ⟨e,he⟩).flow := by
  classical
  unfold Input.coefficient
  rw [sum_queryEdges,Finset.sum_eq_single e]
  · simp only [zsum_same,rel_inc]
    have hiff : ∀ h : LocalGroup e,
        (∃ he : incident v e, s.state ⟨e,he⟩ = h) ↔ s.state ⟨e,he⟩ = h := by
      intro h
      exact ⟨fun ⟨_,hh⟩ => hh,fun hh => ⟨he,hh⟩⟩
    simp only [hiff]
    simp
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro h _
    simp only [zsum_ne e f g h hfe.symm,ite_self]
  · simp

theorem query_incident_iff (v : Vertex n) (s : Configuration b v)
    (e : Edge n) (g : LocalGroup e) :
    (atomInput b).incident (queryConfig v s) (queryEdge e g) ↔ incident v e := by
  constructor
  · rintro ⟨a,hvb,x,hI,hEB⟩
    obtain ⟨w,t,rfl⟩ := exists_queryConfig a
    obtain ⟨f,h,rfl⟩ := exists_queryEdge x
    have hw : v = w := (rel_vb v w s t).mp hvb
    have hf : e = f := (rel_eb e f g h).mp hEB
    subst w; subst f
    exact ((rel_inc v t e h).mp hI).choose
  · intro he
    refine ⟨queryConfig v s,?_,queryEdge e (s.state ⟨e,he⟩),?_,?_⟩
    · exact (rel_vb _ _ _ _).mpr rfl
    · exact (rel_inc _ _ _ _).mpr ⟨he,rfl⟩
    · exact (rel_eb _ _ _ _).mpr rfl

theorem sum_block (v : Vertex n) (s : Configuration b v) (f : (atomInput b).Config → Scalar) :
    (∑ a : (atomInput b).Config, if (atomInput b).rel .VB (queryConfig v s) a then f a else 0) =
      ∑ t : Configuration b v, f (queryConfig v t) := by
  classical
  rw [sum_queryConfigs]
  simp only [rel_vb]
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    simp [Ne.symm hw]
  · simp

theorem block_normalized (hn : 1 ≤ n) (lambda : (atomInput b).Config → Scalar)
    (hl : (atomInput b).normalized lambda) (v : Vertex n) :
    (∑ t : Configuration b v, lambda (queryConfig v t)) = 1 := by
  have h := hl (queryConfig v (someConfiguration hn b v))
  rw [sum_block] at h
  exact h

theorem flow_query_eq (hn : 1 ≤ n) (lambda : (atomInput b).Config → Scalar)
    (mu : (atomInput b).Edge → Scalar) (h : (atomInput b).consistent lambda mu)
    (v : Vertex n) (e : IncidentEdges v) :
    mu (queryEdge e.val 1) = ∑ t : Configuration b v, lambda (queryConfig v t) * (t.state e).flow := by
  have hh := h (queryConfig v (someConfiguration hn b v)) (queryEdge e.val 1)
    ((query_incident_iff _ _ _ _).mpr e.property)
  rw [sum_block] at hh
  simpa only [coefficient_incident v _ e.val 1 e.property,inv_one,one_mul] using hh

theorem query_implies_total_charge_zero (hn : 1 ≤ n) (hq : (atomInput b).query) :
    (∑ v, b v) = 0 := by
  classical
  obtain ⟨lambda,mu,hl,hm⟩ := hq
  let z : Edge n → Scalar := fun e => mu (queryEdge e 1)
  have hz : boundary z = b := by
    funext v
    rw [← sum_incident]
    change (∑ e : IncidentEdges v, epsilon v e.val * mu (queryEdge e.val 1)) = b v
    simp_rw [flow_query_eq hn lambda mu hm,Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ t : Configuration b v, ∑ e : IncidentEdges v,
        epsilon v e.val * (lambda (queryConfig v t) * (t.state e).flow)) =
        ∑ t : Configuration b v, lambda (queryConfig v t) * divergence t.state := by
          apply Finset.sum_congr rfl
          intro t _
          simp only [divergence,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
      _ = ∑ t : Configuration b v, lambda (queryConfig v t) * b v := by
          simp only [Configuration.charge]
      _ = b v := by rw [← Finset.sum_mul,block_normalized hn lambda hl,one_mul]
  rw [← hz]
  exact sum_boundary z

theorem query_zero_charge : (atomInput (0 : Vertex n → Scalar)).query := by
  classical
  refine ⟨zeroWeight,zeroMu,?_,?_⟩
  · intro a
    obtain ⟨v,t,rfl⟩ := exists_queryConfig a
    rw [sum_block]
    simp [zeroWeight,queryConfig]
  · intro a y hi
    obtain ⟨v,t,rfl⟩ := exists_queryConfig a
    obtain ⟨e,g,rfl⟩ := exists_queryEdge y
    have he : incident v e := (query_incident_iff v t e g).mp hi
    rw [sum_block]
    change -g.flow = ∑ t' : Configuration (0 : Vertex n → Scalar) v,
      (if t' = zeroConfiguration v then 1 else 0) *
        (atomInput (0 : Vertex n → Scalar)).coefficient (queryEdge e g) (queryConfig v t')
    simp only [ite_mul,one_mul,zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (zeroConfiguration v)]
    simp only [Finset.mem_univ,ite_true,coefficient_incident v _ e g he,
      zeroConfiguration, mul_one,Support.H.inv_flow]

theorem opposite_answers (hn : 1 ≤ n) (vstar : Vertex n) :
    (atomInput (0 : Vertex n → Scalar)).query ∧
      ¬ (atomInput (Pi.single vstar (1 : Scalar))).query := by
  refine ⟨query_zero_charge,?_⟩
  intro h
  have hh := query_implies_total_charge_zero hn h
  simp at hh

end

open Classical Support

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Flows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Grid

theorem boxConstant_pos : 0 < boxConstant := by
  unfold boxConstant
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
    (by norm_num : -(1:ℝ)/3 < 0)
  simpa using h

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Hereditary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Hereditary

variable {A B : Type*}

attribute [local instance] CPTSeparation.Hereditary.instDecidableEqHF

theorem ofFinset_elements {x : HF A} (hx : isSet x = true) : ofFinset (elements x) = x := by
  apply ext_sets (isSet_ofFinset _) hx
  intro z
  rw [mem_ofFinset]
  rfl

theorem atom_or_set (x : HF A) : (∃ a, x = atom a) ∨ x = ofFinset (elements x) := by
  induction x using Quotient.inductionOn with
  | _ l =>
    rcases l with ⟨(_ | _), l⟩
    · cases l with
      | atom a => exact Or.inl ⟨a,rfl⟩
    · exact Or.inr (ofFinset_elements rfl).symm

end CPTSeparation.Hereditary

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Forms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Hereditary

variable {A G : Type*} [Group G] [MulAction G A]

theorem supports_pad {k s : ℕ} (hks : k ≤ s) (a₀ : A) (alpha : Fin k → A)
    {x : HF A} (h : Supports (G := G) alpha x) : Supported (G := G) s x := by
  classical
  let beta (i : Fin s) : A := if hi : i.val < k then alpha ⟨i.val,hi⟩ else a₀
  refine ⟨beta,?_⟩
  intro g hg
  apply h g
  intro i
  have hi := hg (i.castLE hks)
  simpa only [beta, Fin.val_castLE, dite_eq_left i.isLt] using hi

end CPTSeparation.Hereditary

namespace CPTSeparation.Grid

section

open Support Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

theorem small_orbit_supported (hn : 1 ≤ n) (x : HF (Atom b))
    (N : ℕ) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q)
    (horbit : (Nat.card (MulAction.orbit (BoxGroup n) x) : ℝ) ≤ (N : ℝ)^q) :
    Supported (G := CentralGroup n) ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ x := by
  classical
  obtain ⟨T,hT,hfix⟩ := small_orbit_support_edges x N hN q hq horbit
  obtain ⟨alpha,ha⟩ := edge_support_tuple (b := b) T x hfix
  have hsupport : Supports (G := CentralGroup n) alpha x := by
    intro k hk
    exact ha k hk
  have hlen : T.card ≤ ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ := by
    exact_mod_cast le_trans hT (Nat.le_ceil _)
  let a₀ : Atom b := zeroEdgeAtom b (ex ⟨0,by omega⟩ 0 0)
  exact supports_pad hlen a₀ alpha hsupport

theorem orbit_card_le_invariant_family (F : Finset (HF (Atom b)))
    (hF : ∀ g : BoxGroup n, ∀ x ∈ F, g • x ∈ F) {x : HF (Atom b)} (hx : x ∈ F) :
    Nat.card (MulAction.orbit (BoxGroup n) x) ≤ F.card := by
  classical
  let f : MulAction.orbit (BoxGroup n) x → {y // y ∈ F} := fun y =>
    ⟨y.val,by obtain ⟨g,hg⟩ := y.property; rw [← hg]; exact hF g x hx⟩
  have hf : Function.Injective f := by
    intro a c h
    exact Subtype.ext (congrArg (fun z : {y // y ∈ F} => z.val) h)
  have hn := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hn

theorem invariant_family_hereditarily_supported (hn : 1 ≤ n)
    (F : Finset (HF (Atom b)))
    (hF : ∀ g : BoxGroup n, ∀ x ∈ F, g • x ∈ F)
    (htrans : ∀ x ∈ F, ∀ y, y ∈ x → y ∈ F)
    (N : ℕ) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q)
    (hsize : (F.card : ℝ) ≤ (N : ℝ)^q) :
    ∀ x ∈ F, HereditarilySupported (G := CentralGroup n)
      ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ x := by
  intro x hx y hy
  have hymem : y ∈ F := by
    induction hy with
    | refl => exact hx
    | @tail z w hpath hmem ih => exact ih (htrans w hx z hmem)
  apply small_orbit_supported hn y N hN q hq
  exact le_trans (by exact_mod_cast orbit_card_le_invariant_family F hF hymem) hsize

end

open Classical Finset

variable {n M m s : ℕ} {b : Vertex n → Scalar}

theorem atom_nonempty (hn : 1 ≤ n) (b : Vertex n → Scalar) : Nonempty (Atom b) :=
  ⟨.inr ⟨(0,0,0),someConfiguration hn b (0,0,0)⟩⟩

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Interpretations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Interpretations

attribute [instance] Structure.finite

end CPTSeparation.Interpretations

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A B : Type*}

theorem mem_ordinal (x : HF A) (i : ℕ) : x ∈ ordinal i ↔ ∃ k < i, x = ordinal k := by
  induction i with
  | zero => simp [ordinal]
  | succ i ih =>
    change x ∈ ofFinset (insert (ordinal i) (elements (ordinal i))) ↔ _
    simp only [mem_ofFinset,mem_insert]
    change x = ordinal i ∨ x ∈ ordinal i ↔ _
    rw [ih]
    constructor
    · rintro (rfl|⟨k,hk,rfl⟩)
      · exact ⟨i,by omega,rfl⟩
      · exact ⟨k,by omega,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      by_cases hki : k = i
      · exact Or.inl (congrArg ordinal hki)
      · exact Or.inr ⟨k,by omega,rfl⟩

theorem ordinal_injective : Function.Injective (ordinal (A := A)) := by
  intro i j hij
  by_contra hn
  rcases lt_or_gt_of_ne hn with h|h
  · have hm := (mem_ordinal (ordinal (A := A) i) j).mpr ⟨i,h,rfl⟩
    rw [hij] at hm
    exact (Nat.lt_irrefl _) (rank_lt_of_mem hm)
  · have hm := (mem_ordinal (ordinal (A := A) j) i).mpr ⟨j,h,rfl⟩
    rw [hij] at hm
    exact (Nat.lt_irrefl _) (rank_lt_of_mem hm)

end CPTSeparation.Hereditary

namespace CPTSeparation.Counting

open Classical Finset

variable {R D : Type*} (S : Structure R D) {m n k : ℕ}

namespace Definable

variable {S} {P Q : (Fin n → D) → Prop}

theorem reindex (h : Definable S m n P) (f : Fin n → Fin k) :
    Definable S m k (fun v => P (v ∘ f)) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h (args ∘ f)
  refine ⟨φ,?_,fun v => he v⟩
  intro i hi
  obtain ⟨j,_,rfl⟩ := mem_image.mp (hφ hi)
  exact mem_image.mpr ⟨f j,mem_univ _,rfl⟩

theorem and (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v ∧ Q v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  obtain ⟨ψ,hψ,he'⟩ := h' args
  exact ⟨.and φ ψ,union_subset hφ hψ,fun v => and_congr (he v) (he' v)⟩

theorem or (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v ∨ Q v) :=
  (h.neg.and h'.neg).neg.congr (fun _ => by tauto)

theorem imp (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v → Q v) :=
  (h.neg.or h').congr (fun _ => by tauto)

theorem iff (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v ↔ Q v) :=
  ((h.imp h').and (h'.imp h)).congr (fun _ => by tauto)

end Definable

end CPTSeparation.Counting

namespace CPTSeparation.HFCoding

open Classical Finset Hereditary Counting

variable {A R : Type} {d : Set (HF A)}

variable (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d)

variable (S : Counting.Structure R (Domain d)) {m : ℕ}

include hd

theorem singletonTest_iff (u a : Domain d) : SingletonTest u a ↔ u.val = Hereditary.singleton a.val := by
  constructor
  · rintro ⟨hu,h⟩
    apply ext_sets hu (isSet_ofFinset _)
    intro w
    change w ∈ u.val ↔ w ∈ Hereditary.singleton a.val
    rw [Hereditary.mem_singleton]
    constructor
    · intro hw
      exact congrArg Subtype.val ((h ⟨w,hd _ u.property _ hw⟩).mp hw)
    · rintro rfl
      exact (h a).mpr rfl
  · intro h
    constructor
    · rw [h]; exact isSet_ofFinset _
    · intro w
      rw [h,Hereditary.mem_singleton]
      exact Subtype.val_injective.eq_iff

theorem doubleTest_iff (u a b : Domain d) : DoubleTest u a b ↔ u.val = double a.val b.val := by
  constructor
  · rintro ⟨hu,h⟩
    apply ext_sets hu (isSet_ofFinset _)
    intro w
    change w ∈ u.val ↔ w ∈ double a.val b.val
    rw [mem_double]
    constructor
    · intro hw
      rcases (h ⟨w,hd _ u.property _ hw⟩).mp hw with h|h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rintro (rfl|rfl)
      · exact (h a).mpr (Or.inl rfl)
      · exact (h b).mpr (Or.inr rfl)
  · intro h
    constructor
    · rw [h]; exact isSet_ofFinset _
    · intro w
      rw [h,mem_double]
      exact or_congr Subtype.val_injective.eq_iff Subtype.val_injective.eq_iff

end CPTSeparation.HFCoding

namespace CPTSeparation.Counting

open Classical Finset

variable {R ι : Type*} {D : ι → Type*} (S : ∀ i, Structure R (D i)) {m n k : ℕ}

namespace UniformDefinable

variable {S} {P Q : ∀ i, (Fin n → D i) → Prop}

theorem reindex (h : UniformDefinable S m n P) (f : Fin n → Fin k) :
    UniformDefinable S m k (fun i v => P i (v ∘ f)) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h (args ∘ f)
  refine ⟨φ,?_,fun i v => he i v⟩
  intro j hj
  obtain ⟨l,_,rfl⟩ := mem_image.mp (hφ hj)
  exact mem_image.mpr ⟨f l,mem_univ _,rfl⟩

theorem falsum : UniformDefinable S m n (fun _ _ => False) :=
  fun _ => ⟨.falsum,by simp [Formula.free],fun _ _ => Iff.rfl⟩

theorem and (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v ∧ Q i v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  obtain ⟨ψ,hψ,he'⟩ := h' args
  exact ⟨.and φ ψ,union_subset hφ hψ,fun i v => and_congr (he i v) (he' i v)⟩

theorem or (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v ∨ Q i v) :=
  (h.neg.and h'.neg).neg.congr (fun _ _ => by tauto)

theorem imp (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v → Q i v) :=
  (h.neg.or h').congr (fun _ _ => by tauto)

theorem iff (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v ↔ Q i v) :=
  ((h.imp h').and (h'.imp h)).congr (fun _ _ => by tauto)

theorem equal (a b : Fin n) : UniformDefinable S m n (fun _ v => v a = v b) := by
  intro args
  refine ⟨.equal (args a) (args b),?_,fun _ _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨a,mem_univ _,rfl⟩,mem_image.mpr ⟨b,mem_univ _,rfl⟩⟩

theorem relation (r : R) (a b : Fin n) :
    UniformDefinable S m n (fun i v => (S i).rel r (v a) (v b)) := by
  intro args
  refine ⟨.relation r (args a) (args b),?_,fun _ _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨a,mem_univ _,rfl⟩,mem_image.mpr ⟨b,mem_univ _,rfl⟩⟩

theorem exact {P : ∀ i, (Fin (n+1) → D i) → Prop} (h : UniformDefinable S m (n+1) P) (hn : n < m) (k : ℕ) :
    UniformDefinable S m n (fun i v => Nonempty ({x : D i // P i (Fin.cons x v)} ≃ Fin k)) := by
  intro args
  obtain ⟨a,ha⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons a args)
  refine ⟨.exact a k φ,free_binder hφ,?_⟩
  intro i v
  let e : {x : D i // φ.eval (S i) (Function.update v a x)} ≃ {x : D i // P i (Fin.cons x (v ∘ args))} :=
    Equiv.subtypeEquivRight (fun x => by simpa only [updated_args args a ha] using he i (Function.update v a x))
  exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩,fun ⟨f⟩ => ⟨e.trans f⟩⟩

theorem exists_finset {κ : Type*} {P : κ → ∀ i, (Fin n → D i) → Prop} (t : Finset κ)
    (h : ∀ a ∈ t, UniformDefinable S m n (P a)) : UniformDefinable S m n (fun i v => ∃ a ∈ t, P a i v) := by
  induction t using Finset.induction_on with
  | empty => exact (falsum (S := S)).congr (fun _ _ => by simp)
  | @insert a t ha ih =>
    exact ((h a (mem_insert_self _ _)).or (ih (fun b hb => h b (mem_insert_of_mem hb)))).congr
      (fun _ _ => by simp only [mem_insert,exists_eq_or_imp])

end UniformDefinable

end CPTSeparation.Counting

namespace CPTSeparation.HFCoding

open Classical Finset Hereditary Counting

variable {ι R : Type} {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (S : ∀ i, Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

include hmem hset hm

theorem uniform_singleton : UniformDefinable S m 2 (fun _ v => SingletonTest (v 0) (v 1)) := by
  have hs : UniformDefinable S m 2 (fun _ v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 2)
  have hbody : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2) := by
    have hmem' : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 3)
    exact hmem'.iff (UniformDefinable.equal 0 2)
  exact hs.and (hbody.all (by omega))

theorem uniform_double : UniformDefinable S m 3 (fun _ v => DoubleTest (v 0) (v 1) (v 2)) := by
  have hs : UniformDefinable S m 3 (fun _ v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 3)
  have hbody : UniformDefinable S m 4 (fun _ v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2 ∨ v 0 = v 3) := by
    have hmem' : UniformDefinable S m 4 (fun _ v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 4)
    exact hmem'.iff ((UniformDefinable.equal 0 2).or (UniformDefinable.equal 0 3))
  exact hs.and (hbody.all (by omega))

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

include hd

theorem uniform_ordinal (hpure : ∀ i k, ordinal (A := A i) k ∈ d i) (k : ℕ) :
    UniformDefinable S m 1 (fun _ v => (v 0).val = ordinal k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hor : UniformDefinable S m 2 (fun _ v => ∃ j ∈ range k, (v 0).val = ordinal j) := by
      apply UniformDefinable.exists_finset
      intro j hj
      simpa using (ih j (mem_range.mp hj)).reindex (![0] : Fin 1 → Fin 2)
    have hbody := (hmem.iff hor).all (by omega : 1 < m)
    apply (hset.and hbody).congr
    intro i v
    change (isSet (v 0).val = true ∧ ∀ w : Domain (d i),
      w.val ∈ (v 0).val ↔ ∃ j ∈ range k, w.val = ordinal j) ↔ _
    constructor
    · rintro ⟨hv,h⟩
      apply ext_sets hv (ordinal_isSet k)
      intro w
      rw [mem_ordinal]
      constructor
      · intro hw
        obtain ⟨j,hj,hjw⟩ := (h ⟨w,hd i _ (v 0).property _ hw⟩).mp hw
        exact ⟨j,mem_range.mp hj,hjw⟩
      · rintro ⟨j,hj,rfl⟩
        exact (h ⟨ordinal j,hpure i j⟩).mpr ⟨j,mem_range.mpr hj,rfl⟩
    · intro hv
      refine ⟨by rw [hv]; exact ordinal_isSet k,?_⟩
      intro w
      rw [hv,mem_ordinal]
      simp only [mem_range]

end CPTSeparation.HFCoding

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Grid

open Classical Finset Support

variable {n : ℕ}

private theorem four_fibers {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ f₁ f₂ f₃ : α → β) (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (h₂ : Function.Injective f₂) (h₃ : Function.Injective f₃) (e : β)
    (p : α → Prop) [DecidablePred p] (hp : ∀ a, p a → f₀ a = e ∨ f₁ a = e ∨ f₂ a = e ∨ f₃ a = e) :
    Fintype.card {a // p a} ≤ 4 := by
  have hcard (f : α → β) (hf : Function.Injective f) :
      (univ.filter (fun a => f a = e)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hf ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  rw [Fintype.card_subtype]
  have hs : univ.filter p ⊆
      ((univ.filter (fun a => f₀ a = e) ∪ univ.filter (fun a => f₁ a = e)) ∪
      univ.filter (fun a => f₂ a = e)) ∪ univ.filter (fun a => f₃ a = e) := by
    intro a ha
    have h := hp a (mem_filter.mp ha).2
    simpa only [mem_union,mem_filter,mem_univ,true_and,or_assoc] using h
  exact (card_le_card hs).trans (le_trans (card_union_le _ _) (by
    have h01 := card_union_le (univ.filter (fun a => f₀ a = e)) (univ.filter (fun a => f₁ a = e))
    have h012 := card_union_le
      (univ.filter (fun a => f₀ a = e) ∪ univ.filter (fun a => f₁ a = e))
      (univ.filter (fun a => f₂ a = e))
    have := hcard f₀ h₀; have := hcard f₁ h₁; have := hcard f₂ h₂; have := hcard f₃ h₃
    omega))

theorem edgeFaces_card_le (e : Edge n) : Fintype.card (EdgeFaces e) ≤ 12 := by
  have hxy : Fintype.card {f : FaceXY n // cycle (.inl f) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceXY n) (β := Edge n) (fun ⟨i,j,k⟩ => ex i j.castSucc k)
      (fun ⟨i,j,k⟩ => ey i.succ j k) (fun ⟨i,j,k⟩ => ex i j.succ k)
      (fun ⟨i,j,k⟩ => ey i.castSucc j k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  have hxz : Fintype.card {f : FaceXZ n // cycle (.inr (.inl f)) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceXZ n) (β := Edge n) (fun ⟨i,j,k⟩ => ex i j k.castSucc)
      (fun ⟨i,j,k⟩ => ez i.succ j k) (fun ⟨i,j,k⟩ => ex i j k.succ)
      (fun ⟨i,j,k⟩ => ez i.castSucc j k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  have hyz : Fintype.card {f : FaceYZ n // cycle (.inr (.inr f)) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceYZ n) (β := Edge n) (fun ⟨i,j,k⟩ => ey i j k.castSucc)
      (fun ⟨i,j,k⟩ => ez i j.succ k) (fun ⟨i,j,k⟩ => ey i j k.succ)
      (fun ⟨i,j,k⟩ => ez i j.castSucc k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  unfold EdgeFaces Face
  rw [Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum,
    Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum]
  omega

theorem localGroup_card_le (e : Edge n) : Fintype.card (LocalGroup e) ≤ localSizeBound := by
  rw [Fintype.card_congr (Support.H.productEquiv (localCycle e)),Fintype.card_prod,
    Fintype.card_fun,Fintype.card_prod]
  have hf := edgeFaces_card_le e
  simp only [Scalar,ZMod.card] at *
  change (3*3)^Fintype.card (EdgeFaces e)*3 ≤ 3^25
  calc
    (3*3)^Fintype.card (EdgeFaces e)*3 ≤ (3*3)^12*3 :=
      Nat.mul_le_mul_right 3 (Nat.pow_le_pow_right (by norm_num) hf)
    _ = 3^25 := by norm_num

theorem configuration_card_le (b : Vertex n → Scalar) (v : Vertex n) :
    Fintype.card (Configuration b v) ≤ localSizeBound^6 := by
  have hi : Function.Injective (fun s : Configuration b v => s.state) :=
    fun s t h => Configuration.ext (congrFun h)
  have hdegree : Fintype.card (IncidentEdges v) ≤ 6 := degree_le_six v
  calc
    Fintype.card (Configuration b v) ≤ Fintype.card (LocalStates v) := Fintype.card_le_of_injective _ hi
    _ = ∏ e : IncidentEdges v, Fintype.card (LocalGroup e.val) := Fintype.card_pi
    _ ≤ ∏ _e : IncidentEdges v, localSizeBound := Finset.prod_le_prod' (fun e _ => localGroup_card_le e.val)
    _ = localSizeBound^Fintype.card (IncidentEdges v) := by simp
    _ ≤ localSizeBound^6 := Nat.pow_le_pow_right (by norm_num [localSizeBound]) hdegree

theorem atom_card_bounds (hn : 1 ≤ n) (b : Vertex n → Scalar) :
    (n+1)^3 ≤ Fintype.card (Atom b) ∧
    Fintype.card (Atom b) ≤ atomSizeConstant*(n+1)^3 := by
  have hv : Fintype.card (Vertex n) = (n+1)^3 := by simp [Vertex]; ring
  have he : Fintype.card (Edge n) ≤ 3*(n+1)^3 := by
    simp only [Edge,EdgeX,EdgeY,EdgeZ,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    nlinarith
  constructor
  · rw [← hv]
    apply Fintype.card_le_of_injective (fun v : Vertex n => (.inr ⟨v,someConfiguration hn b v⟩ : Atom b))
    intro v w h
    exact congrArg Sigma.fst (Sum.inr.inj h)
  · change Fintype.card ((Σ e : Edge n, LocalGroup e) ⊕ (Σ v : Vertex n, Configuration b v)) ≤ _
    rw [← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_sigma, Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card]
    calc
      (∑ e : Edge n, Fintype.card (LocalGroup e))+
          ∑ v : Vertex n, Fintype.card (Configuration b v) ≤
          (∑ _e : Edge n, localSizeBound)+∑ _v : Vertex n, localSizeBound^6 :=
        add_le_add (sum_le_sum (fun e _ => localGroup_card_le e))
          (sum_le_sum (fun v _ => configuration_card_le b v))
      _ = Fintype.card (Edge n)*localSizeBound+Fintype.card (Vertex n)*localSizeBound^6 := by simp
      _ ≤ (3*(n+1)^3)*localSizeBound+(n+1)^3*localSizeBound^6 := by
        rw [hv]
        exact add_le_add (Nat.mul_le_mul_right _ he) (le_refl _)
      _ = atomSizeConstant*(n+1)^3 := by unfold atomSizeConstant; ring

end CPTSeparation.Grid

namespace CPTSeparation.Hereditary

open Classical

variable {A G : Type*} [Group G] [MulAction G A] {s : ℕ}

theorem hereditary_iff {x : HF A} : HereditarilySupported (G := G) s x ↔
    Supported (G := G) s x ∧ ∀ y, y ∈ x → HereditarilySupported (G := G) s y := by
  constructor
  · intro h
    exact ⟨h x .refl,fun y hy z hz => h z (hz.tail hy)⟩
  · rintro ⟨h,hm⟩ y hy
    cases hy with
    | refl => exact h
    | tail hz hzx => exact hm _ hzx _ hz

theorem hereditary_transitive {x y : HF A} (hx : HereditarilySupported (G := G) s x) (hy : y ∈ x) :
    HereditarilySupported (G := G) s y := (hereditary_iff.mp hx).2 y hy

theorem ordinal_hereditary [Nonempty A] (s j : ℕ) :
    HereditarilySupported (G := G) s (ordinal (A := A) j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    apply hereditary_iff.mpr
    constructor
    · refine ⟨fun _ => Classical.choice (inferInstance : Nonempty A),?_⟩
      intro g _
      exact map_ordinal (fun a => g • a) j
    · intro y hy
      obtain ⟨k,hk,rfl⟩ := (mem_ordinal y j).mp hy
      exact ih k hk

end CPTSeparation.Hereditary

namespace CPTSeparation.Grid

section

open Classical Hereditary Counting HFCoding Interpretations

variable {n : ℕ} (b : Vertex n → Scalar)

variable (P : Interpretations.Program Symbol)

variable {ι : Type} (bs : ι → Vertex n → Scalar) {s m : ℕ}

theorem program_domain_transitive (i : ι) :
    ∀ x ∈ programDomain bs (s := s) i, ∀ y, y ∈ x → y ∈ programDomain bs (s := s) i :=
  fun _ hx _ hy => hereditary_transitive hx hy

theorem program_mem_uniform : UniformDefinable (programHF bs (s := s)) m 2
    (fun _ v => (v 0).val ∈ (v 1).val) :=
  UniformDefinable.relation (S := programHF bs (s := s)) .mem 0 1

theorem program_set_uniform : UniformDefinable (programHF bs (s := s)) m 1
    (fun _ v => isSet (v 0).val = true) := by
  apply (UniformDefinable.relation (S := programHF bs (s := s)) .atom 0 0).neg.congr
  intro i v
  change (¬ isSet (v 0).val = false) ↔ _
  cases isSet (v 0).val <;> simp

theorem program_pure (hn : 1 ≤ n) (i : ι) (k : ℕ) : ordinal k ∈ programDomain bs (s := s) i := by
  let := atom_nonempty hn (bs i)
  exact ordinal_hereditary s k

end

open Classical Hereditary Counting HFCoding Interpretations

end CPTSeparation.Grid

namespace CPTSeparation.Quantitative

section

open Filter Asymptotics Topology

lemma const_little_rpow (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (fun _ : ℝ => c) =o[atTop] (fun L => L^r) :=
  (isLittleO_const_id_atTop c).comp_tendsto (tendsto_rpow_atTop hr)

lemma power_little_power {a b : ℝ} (hab : a < b) :
    (fun L : ℝ => L^a) =o[atTop] (fun L => L^b) := by
  have h := (isBigO_refl (fun L : ℝ => L^a) atTop).mul_isLittleO (const_little_rpow 1 (sub_pos.mpr hab))
  apply h.congr' (by filter_upwards [] with L; simp)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [← Real.rpow_add hL]
  congr 1
  ring

lemma ceil_little {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (h : f =o[l] g) (h1 : (fun _ => (1:ℝ)) =o[l] g) :
    (fun x => (⌈f x⌉₊ : ℝ)) =o[l] g := by
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [hf,h.bound (show 0 < c/2 by linarith),h1.bound (show 0 < c/2 by linarith)] with x hx hh hconst
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [Real.norm_of_nonneg hx] at hh
  norm_num at hconst
  have hb := Nat.ceil_lt_add_one hx
  simp only [Real.norm_eq_abs] at hh ⊢
  linarith

lemma log_volume_little (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => q*Real.logb 3 (C*L^3)) =o[atTop] (fun L => L^((1:ℝ)/12)) := by
  have hc := const_little_rpow (Real.log C) (show 0 < (1:ℝ)/12 by norm_num)
  have hl := (isLittleO_log_rpow_atTop (show 0 < (1:ℝ)/12 by norm_num)).const_mul_left 3
  have h := ((hc.add hl).const_mul_left ((q:ℝ)/Real.log 3))
  apply h.congr' _ (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  simp only [Real.logb,Real.log_mul (ne_of_gt hC) (ne_of_gt (pow_pos hL 3)),Real.log_pow]
  ring

lemma radius_little (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => (radius C q L : ℝ)) =o[atTop] (fun L => L^((7:ℝ)/6)) := by
  have hlog := log_volume_little C q hC
  have hsquare := hlog.pow (show 0 < 2 by omega)
  have hlin := (isBigO_refl (fun L : ℝ => L) atTop).mul_isLittleO hsquare
  have hraw : (fun L : ℝ => 2*L*(q*Real.logb 3 (C*L^3))^2) =o[atTop] (fun L => L^((7:ℝ)/6)) := by
    apply (hlin.const_mul_left 2).congr' (by filter_upwards [] with L; ring)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    calc
      L * (L ^ ((1:ℝ)/12)) ^ 2 = L^((1:ℝ)) * L^(((1:ℝ)/12)*2) := by
        rw [Real.rpow_one, Real.rpow_mul hL.le]; norm_num
      _ = L^((7:ℝ)/6) := by rw [← Real.rpow_add hL]; norm_num
  apply ceil_little _ hraw (const_little_rpow 1 (by norm_num))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  positivity

lemma radius_little_palette (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => (radius C q L : ℝ)) =o[atTop] (fun L => L^((7:ℝ)/4)) :=
  (radius_little C q hC).trans (power_little_power (by norm_num))

lemma homogeneity_little (C q m c : ℝ) (hC : 0 < C) :
    (fun L : ℝ => 7*(m*(radius C q L:ℝ))+7*((6*(m*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1)
      =o[atTop] (fun L => L^((7:ℝ)/4)) := by
  have hlin := (radius_little_palette C q hC).const_mul_left (7*m)
  have hsr := (radius_little C q hC).const_mul_left (6*m/c)
  have hp := hsr.rpow (show 0 < (3:ℝ)/2 by norm_num)
    ((eventually_ge_atTop (0:ℝ)).mono (fun L hL => Real.rpow_nonneg hL _))
  have hp' : (fun L : ℝ => ((6*(m*(radius C q L:ℝ)))/c)^((3:ℝ)/2))
      =o[atTop] (fun L => L^((7:ℝ)/4)) := by
    apply hp.congr' (by filter_upwards [] with L; congr 1; ring)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_mul hL]
    congr 1
    norm_num
  have h := (hlin.add (hp'.const_mul_left 7)).add (const_little_rpow 1 (by norm_num))
  apply h.congr_left
  intro L
  ring

lemma floor_big (a : ℝ) : (fun L : ℝ => (⌊L^a⌋₊:ℝ)) =O[atTop] (fun L => L^a) := by
  apply IsBigO.of_norm_eventuallyLE
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact Nat.floor_le (Real.rpow_nonneg hL _)

lemma giant_little (c : ℝ) :
    (fun L : ℝ => ((12*(palette L:ℝ))/c)^((3:ℝ)/2)) =o[atTop] (fun L => L^3) := by
  have hb := (floor_big ((7:ℝ)/4)).const_mul_left (12/c)
  have hp := hb.rpow (show 0 ≤ (3:ℝ)/2 by norm_num)
    ((eventually_ge_atTop (0:ℝ)).mono (fun L hL => Real.rpow_nonneg hL _))
  have hp' : (fun L : ℝ => ((12*(palette L:ℝ))/c)^((3:ℝ)/2)) =O[atTop]
      (fun L => L^((21:ℝ)/8)) := by
    apply hp.congr' (by filter_upwards [] with L; simp only [palette]; congr 1; ring)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_mul hL]
    congr 1
    norm_num
  have h := hp'.trans_isLittleO (power_little_power (a := (21:ℝ)/8) (b := 3) (by norm_num))
  exact h.congr_right (fun L => Real.rpow_natCast L 3)

theorem eventual_bounds (C q c : ℝ) (hC : 0 < C) (hc : 0 < c) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (max 4 (m+1):ℝ)*(radius C q L:ℝ) ≤ (palette L:ℝ) ∧
      7*((max 2 m:ℝ)*(radius C q L:ℝ))+
        7*((6*((max 2 m:ℝ)*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1 ≤ (palette L:ℝ) ∧
      ((12*(palette L:ℝ))/c)^((3:ℝ)/2) < L^3 := by
  have hw := ((radius_little_palette C q hC).const_mul_left (max 4 (m+1):ℝ)).bound
    (show 0 < (1:ℝ)/2 by norm_num)
  have hh := (homogeneity_little C q (max 2 m:ℝ) c hC).bound (show 0 < (1:ℝ)/2 by norm_num)
  have hg := (giant_little c).bound (show 0 < (1:ℝ)/2 by norm_num)
  filter_upwards [hw,hh,hg,eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (show 0 < (7:ℝ)/4 by norm_num)).eventually_ge_atTop 2] with L hw hh hg hL hpow
  have hp : 0 ≤ L^((7:ℝ)/4) := Real.rpow_nonneg hL.le _
  have hs : 0 ≤ (radius C q L:ℝ) := Nat.cast_nonneg _
  have hfl := Nat.lt_floor_add_one (L^((7:ℝ)/4))
  have hn : 0 ≤ 7*((max 2 m:ℝ)*(radius C q L:ℝ))+
      7*((6*((max 2 m:ℝ)*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1 := by positivity
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg hp] at hw
  rw [Real.norm_of_nonneg hn,Real.norm_of_nonneg hp] at hh
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (pow_nonneg hL.le 3)] at hg
  change _ ≤ (⌊L^((7:ℝ)/4)⌋₊:ℝ) ∧ _ ≤ (⌊L^((7:ℝ)/4)⌋₊:ℝ) ∧ _
  refine ⟨by linarith,by linarith,?_⟩
  have hcube := pow_pos hL 3
  linarith

end

lemma timeExponent_ge_two (c d : ℕ) : 2 ≤ timeExponent c d := by unfold timeExponent; omega

lemma nat_le_power (N c : ℕ) (hN : 2 ≤ N) : c ≤ N^c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ]
    have hp : 1 ≤ N^c := Nat.one_le_pow _ _ (by omega)
    nlinarith

lemma polynomial_bounds (c d N : ℕ) (hN : 2 ≤ N) :
    2 ≤ N^timeExponent c d ∧ N ≤ N^timeExponent c d ∧
    c*(N+1)^d ≤ N^timeExponent c d ∧
    9*(N^timeExponent c d)^3 ≤ N^traceExponent c d := by
  have hpos : 1 ≤ N := by omega
  have hD := timeExponent_ge_two c d
  have hNB : N ≤ N^timeExponent c d := by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (show 1 ≤ timeExponent c d by omega)
  refine ⟨le_trans hN hNB,hNB,?_,?_⟩
  · calc
      c*(N+1)^d ≤ N^c*(N^2)^d := Nat.mul_le_mul (nat_le_power N c hN)
        (Nat.pow_le_pow_left (by nlinarith : N+1 ≤ N^2) d)
      _ = N^(c+2*d) := by rw [← pow_mul,← pow_add]
      _ ≤ N^timeExponent c d := Nat.pow_le_pow_right hpos (by unfold timeExponent; omega)
  · calc
      9*(N^timeExponent c d)^3 ≤ N^4*(N^timeExponent c d)^3 := by
        apply Nat.mul_le_mul_right
        have hh := Nat.pow_le_pow_left hN 4
        norm_num at hh
        omega
      _ = N^traceExponent c d := by
        rw [← pow_mul,← pow_add]
        unfold traceExponent
        congr 1
        omega

end CPTSeparation.Quantitative

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Interpretations Quantitative Filter

lemma atomSizeConstant_pos : 0 < atomSizeConstant := by
  unfold atomSizeConstant localSizeBound
  positivity

theorem exists_numeric_box (q : ℕ) (hq : 0 < q) (m : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧
      let N : ℕ := atomSizeConstant*(n+1)^3
      let s : ℕ := ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊
      let M : ℕ := palette (n+1:ℝ)
      2 ≤ N ∧ 0 < s ∧ max 4 (m+1)*s ≤ M ∧
      (7:ℝ)*((max 2 m*s:ℕ):ℝ)+7*((6*((max 2 m*s:ℕ):ℝ))/boxConstant)^((3:ℝ)/2)+1 ≤ M ∧
      GiantBound n M := by
  have hC : 0 < (atomSizeConstant:ℝ) := by exact_mod_cast atomSizeConstant_pos
  have hev := eventual_bounds (atomSizeConstant:ℝ) (q:ℝ) boxConstant hC boxConstant_pos m
  have ht : Filter.Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have he := ht.eventually hev
  obtain ⟨n,hn,hnum⟩ := ((eventually_ge_atTop (1:ℕ)).and he).exists
  refine ⟨n,hn,?_⟩
  dsimp only
  let N : ℕ := atomSizeConstant*(n+1)^3
  have hN : 2 ≤ N := by
    have hC' : 1 ≤ atomSizeConstant := atomSizeConstant_pos
    have hp : 2 ≤ (n+1)^3 := by
      have h := Nat.pow_le_pow_left (show 2 ≤ n+1 by omega) 3
      norm_num at h
      omega
    exact hp.trans (by simpa only [one_mul] using Nat.mul_le_mul_right ((n+1)^3) hC')
  have hlog : 0 < Real.logb 3 (N:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast hN)
  have hs : 0 < ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ := by
    apply Nat.ceil_pos.mpr
    have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
    positivity
  have hrad : radius (atomSizeConstant:ℝ) (q:ℝ) (n+1:ℝ) =
      ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ := by
    simp only [radius,N,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  rw [hrad] at hnum
  refine ⟨hN,hs,?_,?_,?_⟩
  · exact_mod_cast hnum.1
  · simpa only [N,Nat.cast_mul, Nat.cast_max, Nat.cast_ofNat] using hnum.2.1
  · simpa only [GiantBound,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hnum.2.2

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Operational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Operational

open Classical Hereditary Finset

variable {A B R F : Type*} {arity : F → ℕ}

attribute [local instance] CPTSeparation.Operational.instDecidableEqHF

@[simp] theorem truth_ne_empty : (truth : HF A) ≠ empty :=
  fun h => by have := ordinal_injective h; omega

@[simp] theorem boolean_truth (p : Prop) : boolean (A := A) p = truth ↔ p := by
  by_cases h : p <;> simp [boolean,h,Ne.symm truth_ne_empty]

lemma uniqueHF_spec (x : HF A) :
    (∃ a, elements x = {a} ∧ uniqueHF x = a) ∨
      (¬ ∃ a, elements x = {a}) ∧ uniqueHF x = empty := by
  by_cases h : ∃ a, elements x = {a}
  · exact Or.inl ⟨h.choose,h.choose_spec,by simp only [uniqueHF,dite_eq_left h]⟩
  · exact Or.inr ⟨h,by simp only [uniqueHF,dite_eq_right h]⟩

namespace State

lemma updatedValue_eq (s : State F arity A) (u : Finset (Update F arity A))
    (hu : Consistent u) {l : Location F arity A} {x : HF A} (hx : (l,x) ∈ u) :
    s.updatedValue u l = x := by
  have h : ∃ y, (l,y) ∈ u := ⟨x,hx⟩
  simp only [updatedValue,dite_eq_left h]
  exact hu l _ _ h.choose_spec hx

lemma updatedValue_default (s : State F arity A) (u : Finset (Update F arity A))
    {l : Location F arity A} (hl : ¬ ∃ x, (l,x) ∈ u) : s.updatedValue u l = s.value l := by
  simp only [updatedValue,dite_eq_right hl]

end State

end CPTSeparation.Operational

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A B : Type*}

attribute [local instance] CPTSeparation.Hereditary.instDecidableEqHF_1

lemma closure_member_subset {x y : HF A} (h : y ∈ x) : closure y ⊆ closure x := by
  nth_rw 2 [closure]
  intro z hz
  simp only [mem_insert,mem_biUnion,mem_attach,true_and,Subtype.exists]
  exact Or.inr ⟨y,h,hz⟩

lemma mem_closure_iff (x y : HF A) : x ∈ closure y ↔
    Relation.ReflTransGen (fun a b : HF A => a ∈ b) x y := by
  constructor
  · intro h
    induction y using (measure rank).wf.induction with
    | h y ih =>
      rw [closure] at h
      rcases mem_insert.mp h with rfl | hm
      · exact .refl
      · obtain ⟨z,hz,hxz⟩ := mem_biUnion.mp hm
        exact (ih z.val (rank_lt_of_mem z.property) hxz).tail z.property
  · intro h
    induction h with
    | refl => exact mem_closure_self _
    | tail hab hbc ih => exact closure_member_subset hbc ih

lemma closure_transitive {x y z : HF A} (hxy : y ∈ closure x) (hyz : z ∈ y) :
    z ∈ closure x := by
  apply (mem_closure_iff z x).mpr
  exact (Relation.ReflTransGen.single (r := fun a b : HF A => a ∈ b) hyz).trans ((mem_closure_iff y x).mp hxy)

lemma mem_mapEquiv (e : A ≃ B) (x y : HF A) : map e x ∈ map e y ↔ x ∈ y := by
  change map e x ∈ elements (map e y) ↔ x ∈ elements y
  rw [elements_map]
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
    exact (mapEquiv e).injective he ▸ hz
  · intro h
    exact Finset.mem_image.mpr ⟨x,h,rfl⟩

lemma rtc_map (e : A ≃ B) {x y : HF A}
    (h : Relation.ReflTransGen (fun a b : HF A => a ∈ b) x y) :
    Relation.ReflTransGen (fun a b : HF B => a ∈ b) (map e x) (map e y) := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih => exact ih.tail ((mem_mapEquiv e _ _).mpr hbc)

lemma closure_map (e : A ≃ B) (x : HF A) : closure (map e x) = (closure x).image (map e) := by
  ext y
  obtain ⟨z,rfl⟩ := (mapEquiv e).surjective y
  rw [mem_closure_iff,mem_image]
  constructor
  · intro h
    have h' : Relation.ReflTransGen (fun a b : HF A => a ∈ b) z x := by
      have hm := rtc_map e.symm h
      change Relation.ReflTransGen (fun a b : HF A => a ∈ b)
        ((mapEquiv e).symm ((mapEquiv e) z)) ((mapEquiv e).symm ((mapEquiv e) x)) at hm
      simpa only [Equiv.symm_apply_apply] using hm
    exact ⟨z,(mem_closure_iff z x).mpr h',rfl⟩
  · rintro ⟨w,hw,he⟩
    have h := (mem_closure_iff w x).mp hw
    have hm := rtc_map e h
    exact he ▸ hm

lemma mem_familyClosure {f : Finset (HF A)} {x : HF A} :
    x ∈ familyClosure f ↔ ∃ y ∈ f, x ∈ closure y := by simp [familyClosure]

lemma familyClosure_contains {f : Finset (HF A)} {x : HF A} (hx : x ∈ f) :
    x ∈ familyClosure f := mem_familyClosure.mpr ⟨x,hx,mem_closure_self x⟩

lemma familyClosure_transitive {f : Finset (HF A)} {x y : HF A}
    (hx : x ∈ familyClosure f) (hy : y ∈ x) : y ∈ familyClosure f := by
  obtain ⟨z,hz,hxz⟩ := mem_familyClosure.mp hx
  exact mem_familyClosure.mpr ⟨z,hz,closure_transitive hxz hy⟩

end CPTSeparation.Hereditary

namespace CPTSeparation.Operational

section

open Classical Hereditary Finset

variable {A R F : Type*} {arity : F → ℕ}

attribute [local instance] CPTSeparation.Operational.instDecidableEqHF_1

namespace State

lemma value_mem_critical (s : State F arity A) {l : Location F arity A}
    (h : s.value l ≠ empty) : s.value l ∈ s.critical := by
  exact mem_biUnion.mpr ⟨l,(mem_support s l).mpr h,mem_insert_self _ _⟩

lemma argument_mem_critical (s : State F arity A) {l : Location F arity A}
    (h : s.value l ≠ empty) (i : Fin (arity l.1)) : l.2 i ∈ s.critical := by
  exact mem_biUnion.mpr ⟨l,(mem_support s l).mpr h,mem_insert_of_mem (mem_image.mpr ⟨i,mem_univ _,rfl⟩)⟩

lemma active_transitive [Fintype A] (s : State F arity A) {x y : HF A}
    (hx : x ∈ s.active) (hy : y ∈ x) : y ∈ s.active :=
  familyClosure_transitive hx hy

end State

namespace Machine

variable (P : Machine R) [Fintype A]

lemma state_active_subset (rel : R → A → A → Bool) {h j : ℕ} {s : P.Store (A := A)}
    (hj : j ≤ h) (hs : P.run rel j = some s) : s.active ⊆ P.runActive rel h := by
  intro x hx
  exact mem_biUnion.mpr ⟨j,by simpa using hj,by simpa only [hs] using hx⟩

lemma runActive_transitive (rel : R → A → A → Bool) (h : ℕ) {x y : HF A}
    (hx : x ∈ P.runActive rel h) (hy : y ∈ x) : y ∈ P.runActive rel h := by
  obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
  cases hs : P.run rel j with
  | none => simp only [hs,Finset.notMem_empty] at hx
  | some s =>
    simp only [hs] at hx
    exact mem_biUnion.mpr ⟨j,hj,by simpa only [hs] using s.active_transitive hx hy⟩

lemma runActive_card_le (rel : R → A → A → Bool) (h K : ℕ)
    (hb : ∀ j ≤ h, ∀ s, P.run rel j = some s → s.active.card ≤ K) :
    (P.runActive rel h).card ≤ (h+1)*K := by
  unfold runActive
  apply (card_biUnion_le).trans
  calc
    (∑ j ∈ range (h+1), (match P.run rel j with | none => ∅ | some s => s.active).card) ≤
        ∑ _j ∈ range (h+1), K := by
      apply sum_le_sum
      intro j hj
      cases hs : P.run rel j with
      | none => simp
      | some s => exact hb j (by simpa using hj) s hs
    _ = (h+1)*K := by simp

end Machine

end

open Classical Hereditary Finset

variable {A B R F : Type*} {arity : F → ℕ}

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_2
@[simp] lemma lift_mem_iff (e : A ≃ B) (x y : HF A) : lift e x ∈ lift e y ↔ x ∈ y := mem_mapEquiv e x y

lemma lift_elements (e : A ≃ B) (x : HF A) : elements (lift e x) = (elements x).image (lift e) := elements_map e x

lemma lift_ofFinset (e : A ≃ B) (s : Finset (HF A)) : lift e (ofFinset s) = ofFinset (s.image (lift e)) := map_ofFinset e s

lemma lift_allAtoms [Fintype A] [Fintype B] (e : A ≃ B) : lift e allAtoms = allAtoms := by
  rw [allAtoms,lift_ofFinset,allAtoms]
  congr 1
  ext x
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨y,⟨a,rfl⟩,rfl⟩
    exact ⟨e a,rfl⟩
  · rintro ⟨b,rfl⟩
    exact ⟨atom (e.symm b),⟨e.symm b,rfl⟩,by simp [lift,mapEquiv]⟩

lemma lift_union (e : A ≃ B) (x : HF A) : lift e (unionHF x) = unionHF (lift e x) := by
  rw [unionHF,lift_ofFinset,unionHF,lift_elements]
  congr 1
  ext z
  simp only [mem_image,mem_biUnion]
  constructor
  · rintro ⟨z,⟨y,hy,hz⟩,rfl⟩
    exact ⟨lift e y,⟨y,hy,rfl⟩,(lift_mem_iff e z y).mpr hz⟩
  · rintro ⟨y,⟨w,hw,rfl⟩,hz⟩
    refine ⟨(lift e).symm z,⟨w,hw,?_⟩,Equiv.apply_symm_apply _ _⟩
    have := (lift_mem_iff e ((lift e).symm z) w).mp
    apply this
    simpa only [Equiv.apply_symm_apply] using (show z ∈ lift e w from hz)

lemma lift_unique (e : A ≃ B) (x : HF A) : lift e (uniqueHF x) = uniqueHF (lift e x) := by
  rcases uniqueHF_spec x with ⟨a,ha,hu⟩ | ⟨ha,hu⟩
  · have h : elements (lift e x) = {lift e a} := by rw [lift_elements,ha,image_singleton]
    rcases uniqueHF_spec (lift e x) with ⟨b,hb,hv⟩ | ⟨hb,hv⟩
    · rw [hu,hv]
      exact singleton_injective (h.symm.trans hb)
    · exact (hb ⟨_,h⟩).elim
  · rcases uniqueHF_spec (lift e x) with ⟨b,hb,hv⟩ | ⟨hb,hv⟩
    · exfalso
      apply ha
      refine ⟨(lift e).symm b,?_⟩
      apply (image_injective (lift e).injective)
      rw [← lift_elements,hb,image_singleton,Equiv.apply_symm_apply]
    · rw [hu,hv,lift_empty]

lemma lift_card (e : A ≃ B) (x : HF A) : lift e (cardinalityHF x) = cardinalityHF (lift e x) := by
  simp only [cardinalityHF,lift_ordinal,lift_elements,card_image_of_injective _ (lift e).injective]

lemma lift_input (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (r : R) (x y : HF A) :
    inputRelation rel' r (lift e x) (lift e y) ↔ inputRelation rel r x y := by
  constructor
  · rintro ⟨a,b,ha,hb,hr⟩
    refine ⟨e.symm a,e.symm b,?_,?_,?_⟩
    · apply (lift e).injective
      simpa [lift,mapEquiv] using ha
    · apply (lift e).injective
      simpa [lift,mapEquiv] using hb
    · simpa only [← hrel,Equiv.apply_symm_apply] using hr
  · rintro ⟨a,b,rfl,rfl,hr⟩
    exact ⟨e a,e b,rfl,rfl,by rw [hrel]; exact hr⟩

namespace Term

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_2
variable [Fintype A] [Fintype B]

lemma eval_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) :
    t.eval rel' (s.transport e) (fun j => lift e (v j)) = lift e (t.eval rel s v) := by
  induction t with
  | var i => rfl
  | constant n => simp [eval]
  | atoms => simp [eval,lift_allAtoms]
  | app f args ih =>
    simp only [eval,ih]
    exact s.transport_value e ⟨f,fun j => (args j).eval rel s v⟩
  | pair a b ia ib => simp only [eval,ia,ib,lift_double]
  | union a ia => simp only [eval,ia,lift_union]
  | unique a ia => simp only [eval,ia,lift_unique]
  | card a ia => simp only [eval,ia,lift_card]
  | equal a b ia ib => simp only [eval,ia,ib,Equiv.apply_eq_iff_eq,lift_boolean]
  | member a b ia ib => simp only [eval,ia,ib,lift_mem_iff,lift_boolean]
  | isAtom a ia => simp only [eval,ia,lift_isSet,lift_boolean]
  | input r a b ia ib => simp only [eval,ia,ib,lift_input e rel rel' hrel,lift_boolean]
  | not a ia => simp only [eval,ia,ne_eq,lift_truth_iff,lift_boolean]
  | and a b ia ib => simp only [eval,ia,ib,lift_truth_iff,lift_boolean]
  | conditional c a b ic ia ib =>
    simp only [eval,ic,lift_truth_iff]
    split <;> simp_all
  | comprehension bound guard body ihb ihg iht =>
    simp only [eval,ihb,lift_elements,lift_ofFinset]
    congr 1
    ext z
    simp only [mem_image,mem_filter]
    constructor
    · rintro ⟨z,⟨⟨x,hx,rfl⟩,hg⟩,hz⟩
      have hh : (lift e) ∘ (Fin.cons x v) = Fin.cons (lift e x) (fun j => lift e (v j)) := by
        funext j; refine Fin.cases rfl (fun _ => rfl) j
      dsimp only [Function.comp_def] at hh
      rw [← hh,ihg,lift_truth_iff] at hg
      rw [← hh,iht] at hz
      exact ⟨body.eval rel s (Fin.cons x v),⟨x,⟨hx,hg⟩,rfl⟩,hz⟩
    · rintro ⟨z,⟨x,⟨hx,hg⟩,rfl⟩,hz⟩
      have hh : (lift e) ∘ (Fin.cons x v) = Fin.cons (lift e x) (fun j => lift e (v j)) := by
        funext j; refine Fin.cases rfl (fun _ => rfl) j
      dsimp only [Function.comp_def] at hh
      exact ⟨lift e x,⟨⟨x,hx,rfl⟩,by rw [← hh,ihg,lift_truth_iff]; exact hg⟩,
        by rw [← hh,iht]; exact hz⟩

end Term

lemma mem_update_image (e : A ≃ B) (u : Finset (Update F arity A))
    (l : Location F arity A) (x : HF A) :
    (locationEquiv e l,lift e x) ∈ u.image (updateEquiv e) ↔ (l,x) ∈ u := by
  change updateEquiv e (l,x) ∈ _ ↔ _
  simp only [mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]

namespace Rule

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_2
variable [Fintype A] [Fintype B]

lemma updates_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A) :
    r.updates rel' (s.transport e) (fun j => lift e (v j)) =
      (r.updates rel s v).image (updateEquiv e) := by
  induction r with
  | skip => simp [updates]
  | update f args value =>
    simp only [updates,Term.eval_transport e rel rel' hrel,image_singleton]
    rfl
  | parallel a b ia ib =>
    simp only [updates,ia,ib,image_union]
  | conditional c a b ia ib =>
    simp only [updates,Term.eval_transport e rel rel' hrel,lift_truth_iff]
    split <;> simp_all
  | «forall» bound body ih =>
    simp only [updates,Term.eval_transport e rel rel' hrel,lift_elements]
    rw [biUnion_image,image_biUnion]
    apply biUnion_congr rfl
    intro x hx
    have hcons : (lift e) ∘ Fin.cons x v = Fin.cons (lift e x) (fun j => lift e (v j)) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    dsimp only [Function.comp_def] at hcons
    rw [← hcons,ih]
  | letValue value body ih =>
    simp only [updates,Term.eval_transport e rel rel' hrel]
    have hcons : (lift e) ∘ Fin.cons (value.eval rel s v) v =
        Fin.cons (lift e (value.eval rel s v)) (fun j => lift e (v j)) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    dsimp only [Function.comp_def] at hcons
    rw [← hcons,ih]

end Rule

namespace State

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_2
lemma consistent_transport (e : A ≃ B) (u : Finset (Update F arity A)) :
    Consistent (u.image (updateEquiv e)) ↔ Consistent u := by
  constructor
  · intro h l x y hx hy
    apply (lift e).injective
    exact h _ _ _ ((mem_update_image e u l x).mpr hx) ((mem_update_image e u l y).mpr hy)
  · intro h l x y hx hy
    obtain ⟨l,rfl⟩ := (locationEquiv e).surjective l
    obtain ⟨x,rfl⟩ := (lift e).surjective x
    obtain ⟨y,rfl⟩ := (lift e).surjective y
    exact congrArg (lift e) (h _ _ _ ((mem_update_image e u l x).mp hx)
      ((mem_update_image e u l y).mp hy))

lemma applyUpdates_transport (e : A ≃ B) (s : State F arity A)
    (u : Finset (Update F arity A)) (hu : Consistent u) :
    (s.transport e).applyUpdates (u.image (updateEquiv e)) = (s.applyUpdates u).transport e := by
  apply ext_value
  intro l
  obtain ⟨l,rfl⟩ := (locationEquiv e).surjective l
  rw [transport_value]
  change (s.transport e).updatedValue (u.image (updateEquiv e)) (locationEquiv e l) =
    lift e (s.updatedValue u l)
  by_cases h : ∃ x, (l,x) ∈ u
  · obtain ⟨x,hx⟩ := h
    rw [s.updatedValue_eq u hu hx,
      updatedValue_eq _ _ ((consistent_transport e u).mpr hu) ((mem_update_image e u l x).mpr hx)]
  · rw [s.updatedValue_default u h,updatedValue_default]
    · exact s.transport_value e l
    · rintro ⟨x,hx⟩
      obtain ⟨x,rfl⟩ := (lift e).surjective x
      exact h ⟨x,(mem_update_image e u l x).mp hx⟩

lemma support_transport (e : A ≃ B) (s : State F arity A) :
    (s.transport e).support = s.support.image (locationEquiv e) := by
  ext l
  obtain ⟨l,rfl⟩ := (locationEquiv e).surjective l
  simp only [mem_image,Equiv.apply_eq_iff_eq,exists_eq_right,mem_support,transport_value,ne_eq,lift_empty_iff]

lemma critical_transport (e : A ≃ B) (s : State F arity A) :
    (s.transport e).critical = s.critical.image (lift e) := by
  simp only [critical,support_transport,biUnion_image,image_biUnion]
  apply biUnion_congr rfl
  intro l hl
  rw [transport_value,image_insert,image_image]
  cases l
  rfl

lemma active_transport [Fintype A] [Fintype B] (e : A ≃ B) (s : State F arity A) :
    (s.transport e).active = s.active.image (lift e) := by
  have hf : ∀ f : Finset (HF A), familyClosure (f.image (lift e)) = (familyClosure f).image (lift e) := by
    intro f
    simp only [familyClosure,biUnion_image,image_biUnion]
    apply biUnion_congr rfl
    intro x hx
    exact closure_map e x
  have ha : (univ.image (@atom B)).image ((lift e).symm) = univ.image (@atom A) := by
    ext x
    simp only [mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨b,rfl⟩,rfl⟩
      exact ⟨e.symm b,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨atom (e a),⟨e a,rfl⟩,by simp [lift,mapEquiv]⟩
  have ha' : univ.image (@atom B) = (univ.image (@atom A)).image (lift e) := by
    rw [← ha,image_image]
    simp only [Function.comp_def,Equiv.apply_symm_apply,image_id']
  unfold active
  rw [critical_transport,ha',← hf]
  congr 1
  simp only [image_union,image_insert,image_singleton,lift_allAtoms,lift_empty,lift_truth]

end State

namespace Machine

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_2
variable (P : Machine R) [finiteA : Fintype A] [finiteB : Fintype B]

omit A B R P in
lemma flag_transport.{uDecl1, uDecl2, uDecl3}
    {A : Type uDecl1}
    {B : Type uDecl2}
    {R : Type uDecl3}
    (P : Operational.Machine R)
    [Fintype A]
    [Fintype B] (e : A ≃ B) (s : P.Store (A := A)) (c : Control) :
    P.flag (s.transport e) c ↔ P.flag s c := by
  have h : locationEquiv e (⟨Sum.inl c,Fin.elim0⟩ : Location _ P.functionArity A) =
      ⟨Sum.inl c,Fin.elim0⟩ := by
    change (⟨Sum.inl c,fun j : Fin 0 => lift e (Fin.elim0 j : HF A)⟩ : Location _ P.functionArity B) = ⟨Sum.inl c,Fin.elim0⟩
    congr 1
    funext i
    exact Fin.elim0 i
  unfold flag
  rw [← h,State.transport_value,lift_truth_iff]

lemma step_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : P.Store (A := A)) :
    P.step rel' (s.transport e) = (P.step rel s).map (State.transport e) := by
  have hv : (fun j : Fin 0 => lift e (Fin.elim0 j : HF A)) = Fin.elim0 := by
    funext j; exact Fin.elim0 j
  have hu := P.rule.updates_transport e rel rel' hrel s Fin.elim0
  rw [hv] at hu
  simp only [step,flag_transport,hu,State.consistent_transport]
  split
  · rfl
  · split
    · rename_i hc
      simp only [Option.map_some]
      congr 1
      exact State.applyUpdates_transport e s _ hc
    · rfl

lemma run_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (j : ℕ) :
    P.run rel' j = (P.run rel j).map (State.transport e) := by
  induction j with
  | zero => simp [run]
  | succ j ih =>
    simp only [run,ih]
    cases hs : P.run rel j with
    | none => rfl
    | some s => exact P.step_transport e rel rel' hrel s

lemma runActive_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (h : ℕ) :
    P.runActive rel' h = (P.runActive rel h).image (lift e) := by
  unfold runActive
  rw [biUnion_image]
  apply biUnion_congr rfl
  intro j hj
  rw [P.run_transport e rel rel' hrel]
  cases hs : P.run rel j with
  | none => simp
  | some s => exact s.active_transport e

end Machine

end CPTSeparation.Operational

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A : Type*}

attribute [local instance] OAI.CPTSeparation.Hereditary.instDecidableEqHF_2
lemma closure_ofFinset (s : Finset (HF A)) :
    closure (ofFinset s) = insert (ofFinset s) (familyClosure s) := by
  rw [closure,elements_ofFinset]
  congr 1
  ext x
  simp [familyClosure]

lemma closure_subset_of_transitive {s : Finset (HF A)}
    (hs : ∀ x ∈ s, ∀ y, y ∈ x → y ∈ s) {x : HF A} (hx : x ∈ s) : closure x ⊆ s := by
  intro y hy
  have h := (mem_closure_iff y x).mp hy
  clear hy
  induction h with
  | refl => exact hx
  | @tail b c h hbc ih => exact ih (hs c hx b hbc)

lemma elements_subset_closure (x : HF A) : elements x ⊆ closure x := by
  intro y hy
  exact closure_member_subset hy (mem_closure_self y)

lemma closure_double_subset (x y : HF A) :
    closure (double x y) ⊆ insert (double x y) (closure x ∪ closure y) := by
  rw [double,closure_ofFinset]
  intro z hz
  simp only [mem_insert,mem_union] at hz ⊢
  rcases hz with h | h
  · exact Or.inl h
  · obtain ⟨w,hw,hz⟩ := mem_familyClosure.mp h
    have he : w = x ∨ w = y := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hw
    rcases he with he | he
    · rw [he] at hz; exact Or.inr (Or.inl hz)
    · rw [he] at hz; exact Or.inr (Or.inr hz)

lemma closure_ordinal (n : ℕ) : closure (ordinal (A := A) n) = (range (n+1)).image ordinal := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [closure]
    ext x
    simp only [mem_insert,mem_biUnion,mem_attach,true_and,Subtype.exists,mem_image,mem_range]
    constructor
    · rintro (rfl | ⟨y,hy,hx⟩)
      · exact ⟨n,by omega,rfl⟩
      · obtain ⟨j,hj,rfl⟩ := (mem_ordinal y n).mp hy
        rw [ih j hj] at hx
        obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
        exact ⟨k,by simp only [mem_range] at hk; omega,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      by_cases he : j = n
      · exact Or.inl (by rw [he])
      · exact Or.inr ⟨ordinal j,(mem_ordinal _ _).mpr ⟨j,by omega,rfl⟩,mem_closure_self _⟩

lemma card_closure_ordinal (n : ℕ) : (closure (ordinal (A := A) n)).card = n+1 := by
  rw [closure_ordinal,card_image_of_injective _ (fun _ _ h => ordinal_injective h),card_range]

end CPTSeparation.Hereditary

namespace CPTSeparation.Operational

open Classical Hereditary Finset

variable {A R F : Type*} {arity : F → ℕ}

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_3
lemma closure_union_subset (x : HF A) : closure (unionHF x) ⊆ insert (unionHF x) (closure x) := by
  rw [unionHF,closure_ofFinset]
  apply insert_subset_insert
  intro z hz
  obtain ⟨y,hy,hzy⟩ := mem_familyClosure.mp hz
  obtain ⟨w,hw,hyw⟩ := mem_biUnion.mp hy
  exact (closure_member_subset hw) ((closure_member_subset hyw) hzy)

lemma closure_unique_subset (x : HF A) : closure (uniqueHF x) ⊆ insert empty (closure x) := by
  rcases uniqueHF_spec x with ⟨a,ha,hu⟩ | ⟨ha,hu⟩
  · rw [hu]
    exact (closure_member_subset (by change a ∈ elements x; rw [ha]; simp)).trans (subset_insert _ _)
  · rw [hu,closure_ordinal]
    simp

lemma card_closure_card (x : HF A) : (closure (cardinalityHF x)).card ≤ (closure x).card+1 := by
  rw [cardinalityHF,card_closure_ordinal]
  exact Nat.add_le_add_right (card_le_card (elements_subset_closure x)) 1

lemma card_closure_boolean (p : Prop) : (closure (boolean (A := A) p)).card ≤ 2 := by
  by_cases h : p <;> simp [boolean,h,truth,empty,card_closure_ordinal]

namespace State

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_3
variable [Fintype A]

lemma empty_mem_active (s : State F arity A) : empty ∈ s.active := by
  apply familyClosure_contains
  simp []

lemma atoms_mem_active (s : State F arity A) : allAtoms ∈ s.active := by
  apply familyClosure_contains
  simp []

lemma closure_value_subset_active (s : State F arity A) (l : Location F arity A) :
    closure (s.value l) ⊆ s.active := by
  apply closure_subset_of_transitive (fun x hx y hy => s.active_transitive hx hy)
  by_cases h : s.value l = empty
  · rw [h]; exact s.empty_mem_active
  · apply familyClosure_contains
    exact mem_union_left _ (mem_union_left _ (s.value_mem_critical h))

lemma closure_atoms_subset_active (s : State F arity A) : Hereditary.closure allAtoms ⊆ s.active :=
  closure_subset_of_transitive (fun _ hx _ hy => s.active_transitive hx hy) s.atoms_mem_active

end State

namespace Term

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_3
variable [Fintype A]

lemma closure_eval_subset_trace (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) :
    closure (t.eval rel s v) ⊆ t.trace rel s v := by
  induction t with
  | var i => exact Subset.rfl
  | constant n => exact Subset.rfl
  | atoms => exact Subset.rfl
  | app f args ih => exact subset_union_left
  | pair a b _ _ => exact subset_union_left.trans subset_union_left
  | union a _ => exact subset_union_left
  | unique a _ => exact subset_union_left
  | card a _ => exact subset_union_left
  | equal a b _ _ => exact subset_union_left.trans subset_union_left
  | member a b _ _ => exact subset_union_left.trans subset_union_left
  | isAtom a _ => exact subset_union_left
  | input r a b _ _ => exact subset_union_left.trans subset_union_left
  | not a _ => exact subset_union_left
  | and a b _ _ => exact subset_union_left.trans subset_union_left
  | conditional c a b _ ia ib =>
    simp only [eval]
    split
    · exact (ia v).trans (subset_union_right.trans subset_union_left)
    · exact (ib v).trans subset_union_right
  | comprehension bound guard body ihb ihg iht =>
    simp only [eval,trace,closure_ofFinset]
    apply insert_subset_insert
    intro z hz
    obtain ⟨y,hy,hzy⟩ := mem_familyClosure.mp hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact mem_union_right _ (mem_biUnion.mpr ⟨x,(mem_filter.mp hx).1,
      mem_union_right _ (iht _ hzy)⟩)

lemma potential_var {k : ℕ} (s : State F arity A) (v : Fin k → HF A) (j : Fin k) :
    (closure (v j)).card ≤ potential s v := by
  unfold potential
  exact (single_le_sum (s := (univ : Finset (Fin k))) (f := fun j => (closure (v j)).card)
    (fun _ _ => Nat.zero_le _) (mem_univ j)).trans (Nat.le_add_left _ _)

lemma potential_active {k : ℕ} (s : State F arity A) (v : Fin k → HF A) :
    s.active.card ≤ potential s v := Nat.le_add_right _ _

lemma potential_cons {k : ℕ} (s : State F arity A) (v : Fin k → HF A) (x : HF A) :
    potential s (Fin.cons x v) = potential s v + (closure x).card := by
  simp only [potential,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  omega

lemma card_trace_le (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) (K : ℕ) (hK : potential s v ≤ K) :
    (t.trace rel s v).card ≤ t.bound.eval K := by
  induction t generalizing K with
  | var j => simpa only [trace,bound,Polynomial.eval_X] using (potential_var s v j).trans hK
  | constant n => simpa only [trace,bound,Polynomial.eval_C] using (card_closure_ordinal (A := A) n).le
  | atoms => simpa only [trace,bound,Polynomial.eval_X] using
      (card_le_card s.closure_atoms_subset_active).trans ((potential_active s v).trans hK)
  | app f args ih =>
    unfold trace bound
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_finsetSum]
    calc
      _ ≤ (closure (s.value ⟨f,fun j => (args j).eval rel s v⟩)).card +
          ∑ j, ((args j).trace rel s v).card :=
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)
      _ ≤ K + ∑ j, (args j).bound.eval K := add_le_add
        ((card_le_card (s.closure_value_subset_active _)).trans ((potential_active s v).trans hK))
        (sum_le_sum (fun j _ => ih j v K hK))
  | pair a b ia ib =>
    have ha := ia v K hK; have hb := ib v K hK
    have ha' := card_le_card (closure_eval_subset_trace rel s a v)
    have hb' := card_le_card (closure_eval_subset_trace rel s b v)
    have hp := card_le_card (closure_double_subset (a.eval rel s v) (b.eval rel s v))
    have hp' := card_insert_le (double (a.eval rel s v) (b.eval rel s v))
      (closure (a.eval rel s v) ∪ closure (b.eval rel s v))
    have hcu := card_union_le (closure (a.eval rel s v)) (closure (b.eval rel s v))
    have ht := card_union_le (closure (double (a.eval rel s v) (b.eval rel s v)) ∪ a.trace rel s v) (b.trace rel s v)
    have ht' := (card_union_le (closure (double (a.eval rel s v) (b.eval rel s v))) (a.trace rel s v))
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega
  | union a ia =>
    have ha := ia v K hK
    have hc := card_le_card (closure_eval_subset_trace rel s a v)
    have hp := card_le_card (closure_union_subset (a.eval rel s v))
    have hi := card_insert_le (unionHF (a.eval rel s v)) (closure (a.eval rel s v))
    have hu := card_union_le (closure (unionHF (a.eval rel s v))) (a.trace rel s v)
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega
  | unique a ia =>
    have ha := ia v K hK
    have hc := card_le_card (closure_eval_subset_trace rel s a v)
    have hp := card_le_card (closure_unique_subset (a.eval rel s v))
    have hi := card_insert_le (empty (A := A)) (closure (a.eval rel s v))
    have hu := card_union_le (closure (uniqueHF (a.eval rel s v))) (a.trace rel s v)
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega
  | card a ia =>
    have ha := ia v K hK
    have hc := card_le_card (closure_eval_subset_trace rel s a v)
    have hp := card_closure_card (a.eval rel s v)
    have hu := card_union_le (closure (cardinalityHF (a.eval rel s v))) (a.trace rel s v)
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega
  | equal a b ia ib | member a b ia ib | input r a b ia ib | and a b ia ib =>
    have ha := ia v K hK; have hb := ib v K hK
    unfold trace
    apply (card_union_le _ _).trans
    apply (add_le_add (card_union_le _ _) (le_refl _)).trans
    apply (add_le_add (add_le_add (card_closure_boolean _) ha) hb).trans
    simp only [bound,Polynomial.eval_add,Polynomial.eval_ofNat,le_refl]
  | isAtom a ia | not a ia =>
    have ha := ia v K hK
    unfold trace
    apply (card_union_le _ _).trans
    apply (add_le_add (card_closure_boolean _) ha).trans
    simp only [bound,Polynomial.eval_add,Polynomial.eval_ofNat,le_refl]
  | conditional c a b ic ia ib =>
    have hc := ic v K hK; have ha := ia v K hK; have hb := ib v K hK
    unfold trace
    apply (card_union_le _ _).trans
    apply (add_le_add (card_union_le _ _) (le_refl _)).trans
    simp only [bound,Polynomial.eval_add]
    omega
  | comprehension b g t ib ig it =>
    have hb := ib v K hK
    have hc := (card_le_card (elements_subset_closure (b.eval rel s v))).trans
      ((card_le_card (closure_eval_subset_trace rel s b v)).trans hb)
    have hsub (x) (hx : x ∈ elements (b.eval rel s v)) :
        potential s (Fin.cons x v) ≤ K + b.bound.eval K := by
      rw [potential_cons]
      apply add_le_add hK
      exact (card_le_card ((closure_member_subset hx).trans
        (closure_eval_subset_trace rel s b v))).trans hb
    have hi := card_insert_le (s := (trace rel s b v ∪ (elements (b.eval rel s v)).biUnion
        (fun x => trace rel s g (Fin.cons x v) ∪ trace rel s t (Fin.cons x v))))
      (ofFinset (((elements (b.eval rel s v)).filter
        (fun x => g.eval rel s (Fin.cons x v) = truth)).image
        (fun x => t.eval rel s (Fin.cons x v))))
    have hu := card_union_le (trace rel s b v) ((elements (b.eval rel s v)).biUnion
        (fun x => trace rel s g (Fin.cons x v) ∪ trace rel s t (Fin.cons x v)))
    have hbi := @card_biUnion_le (HF A) (HF A) _ (elements (b.eval rel s v))
      (fun x => trace rel s g (Fin.cons x v) ∪ trace rel s t (Fin.cons x v))
    have hsum := sum_le_card_nsmul (elements (b.eval rel s v))
      (fun x => (trace rel s g (Fin.cons x v) ∪ trace rel s t (Fin.cons x v)).card)
      (g.bound.eval (K+b.bound.eval K) + t.bound.eval (K+b.bound.eval K)) (by
        intro x hx
        exact (card_union_le _ _).trans (add_le_add (ig _ _ (hsub x hx)) (it _ _ (hsub x hx))))
    simp only [nsmul_eq_mul, Nat.cast_id] at hsum
    have hm := Nat.mul_le_mul_right (g.bound.eval (K+b.bound.eval K) + t.bound.eval (K+b.bound.eval K)) hc
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,
      Polynomial.eval_comp,Polynomial.eval_X]
    omega

end Term

end CPTSeparation.Operational

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Definability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

local instance instDecidableEqHF_4_redf58b_1 {A : Type*} : DecidableEq (HF A) := Classical.decEq _
variable {ι R : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

omit ι A d hd in
lemma member_count_iff
    {ι : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i) (i : ι) (x : Domain (d i)) (n : ℕ) :
    Nonempty ({y : Domain (d i) // y.val ∈ x.val} ≃ Fin n) ↔ (elements x.val).card = n := by
  let e : {y : Domain (d i) // y.val ∈ x.val} ≃ {y // y ∈ elements x.val} :=
    { toFun := fun y => ⟨y.val.val,y.property⟩
      invFun := fun y => ⟨⟨y.val,hd i _ x.property _ y.property⟩,y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨f⟩
    have h := Fintype.card_congr (e.symm.trans f)
    simpa using h
  · intro h
    let f := (Fintype.equivFin {y // y ∈ elements x.val}).trans (finCongr (by simpa using h))
    exact ⟨e.trans f⟩

include hd hmem hset hm

omit ι R A d S m hd hmem hset hm in
lemma uniform_double_value
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) : UniformDefinable S m 3
    (fun _ v => (v 0).val = double (v 1).val (v 2).val) :=
  (HFCoding.uniform_double S hmem hset hm).congr
    (fun i v => HFCoding.doubleTest_iff (hd i) (v 0) (v 1) (v 2))

omit ι R A d S m hd hmem hset hm in
lemma uniform_singleton_value
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) : UniformDefinable S m 2
    (fun _ v => (v 0).val = Hereditary.singleton (v 1).val) :=
  (HFCoding.uniform_singleton S hmem hset hm).congr
    (fun i v => HFCoding.singletonTest_iff (hd i) (v 0) (v 1))

include ha in
lemma uniform_atoms : UniformDefinable S m 1 (fun i v => (v 0).val = (allAtoms : HF (A i))) := by
  have hs : UniformDefinable S m 2 (fun _ v => isSet (v 0).val = false) := by
    apply (hset.reindex (![0] : Fin 1 → Fin 2)).neg.congr
    intro i v; dsimp; cases isSet (v 0).val <;> simp
  have hbody := (hmem.iff hs).all (by omega : 1 < m)
  apply (hset.and hbody).congr
  intro i v
  change (isSet (v 0).val = true ∧ ∀ y : Domain (d i),
    y.val ∈ (v 0).val ↔ isSet y.val = false) ↔ _
  constructor
  · rintro ⟨h0,h⟩
    apply ext_sets h0 (isSet_ofFinset _)
    intro y
    simp only [mem_ofFinset,mem_image,mem_univ,true_and]
    constructor
    · intro hy
      have ht := (h ⟨y,hd i _ (v 0).property _ hy⟩).mp hy
      change isSet y = false at ht
      rcases atom_or_set y with ⟨a,rfl⟩ | he
      · exact ⟨a,rfl⟩
      · rw [he,isSet_ofFinset] at ht; contradiction
    · rintro ⟨a,rfl⟩
      exact (h ⟨atom a,ha i a⟩).mpr rfl
  · intro he
    constructor
    · rw [he]; exact isSet_ofFinset _
    · intro y
      rw [he]
      simp only [allAtoms,mem_ofFinset,mem_image,mem_univ,true_and]
      constructor
      · rintro ⟨a,he⟩; rw [← he]; rfl
      · intro ht
        rcases atom_or_set y.val with ⟨a,he⟩ | he
        · exact ⟨a,he.symm⟩
        · rw [he,isSet_ofFinset] at ht; contradiction

omit ι R A d S m hd hmem hset hm in
lemma uniform_union
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) : UniformDefinable S m 2
    (fun _ v => (v 0).val = unionHF (v 1).val) := by
  have hz : UniformDefinable S m 4
      (fun _ v => (v 0).val ∈ (v 3).val ∧ (v 1).val ∈ (v 0).val) :=
    (hmem.reindex (![0,3] : Fin 2 → Fin 4)).and (hmem.reindex (![1,0] : Fin 2 → Fin 4))
  have hleft : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 1).val) :=
    hmem.reindex (![0,1] : Fin 2 → Fin 3)
  have hbody := (hleft.iff (hz.ex (by omega))).all (by omega : 2 < m)
  have hset' := hset.reindex (![0] : Fin 1 → Fin 2)
  apply (hset'.and hbody).congr
  intro i v
  change (isSet (v 0).val = true ∧ ∀ y : Domain (d i),
    y.val ∈ (v 0).val ↔ ∃ z : Domain (d i), z.val ∈ (v 1).val ∧ y.val ∈ z.val) ↔ _
  have hmemu (y : HF (A i)) : y ∈ unionHF (v 1).val ↔
      ∃ z : Domain (d i), z.val ∈ (v 1).val ∧ y ∈ z.val := by
    simp only [unionHF,mem_ofFinset,mem_biUnion]
    constructor
    · rintro ⟨z,hz,hy⟩
      exact ⟨⟨z,hd i _ (v 1).property _ hz⟩,hz,hy⟩
    · rintro ⟨z,hz,hy⟩; exact ⟨z.val,hz,hy⟩
  constructor
  · rintro ⟨h0,h⟩
    apply ext_sets h0 (isSet_ofFinset _)
    intro y
    change y ∈ (v 0).val ↔ y ∈ unionHF (v 1).val
    rw [hmemu]
    constructor
    · intro hy; exact (h ⟨y,hd i _ (v 0).property _ hy⟩).mp hy
    · rintro ⟨z,hz,hy⟩
      exact (h ⟨y,hd i _ z.property _ hy⟩).mpr ⟨z,hz,hy⟩
  · intro he
    constructor
    · rw [he]; exact isSet_ofFinset _
    · intro y; rw [he,hmemu]

omit ι R A d S m hd hp hmem hset hm in
lemma uniform_unique
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) : UniformDefinable S m 2
    (fun _ v => (v 0).val = uniqueHF (v 1).val) := by
  have hsing := uniform_singleton_value d S hd hmem hset hm
  have hyes := hsing.reindex (![1,0] : Fin 2 → Fin 2)
  have hex : UniformDefinable S m 2 (fun i v => ∃ z : Domain (d i),
      (v 1).val = Hereditary.singleton z.val) := by
    apply ((hsing.reindex (![2,0] : Fin 2 → Fin 3)).ex (by omega)).congr
    intro i v
    apply exists_congr
    intro z
    rfl
  have hempt := (HFCoding.uniform_ordinal S hmem hset hm hd hp 0).reindex (![0] : Fin 1 → Fin 2)
  apply (hyes.or (hempt.and hex.neg)).congr
  intro i v
  change ((v 1).val = Hereditary.singleton (v 0).val ∨
    ((v 0).val = empty ∧ ¬ ∃ z : Domain (d i), (v 1).val = Hereditary.singleton z.val)) ↔ _
  have hs (z : HF (A i)) : (v 1).val = Hereditary.singleton z ↔ elements (v 1).val = {z} := by
    constructor
    · intro h; rw [h]; exact elements_ofFinset _
    · intro h
      rcases atom_or_set (v 1).val with ⟨a,he⟩ | he
      · rw [he,elements_atom] at h
        exact False.elim (by simpa using congrArg Finset.card h)
      · rw [he,h]; rfl
  have hexi : (∃ z : Domain (d i), (v 1).val = Hereditary.singleton z.val) ↔
      ∃ z, elements (v 1).val = {z} := by
    constructor
    · rintro ⟨z,hz⟩; exact ⟨z.val,(hs _).mp hz⟩
    · rintro ⟨z,hz⟩
      exact ⟨⟨z,hd i _ (v 1).property _ (by change z ∈ elements (v 1).val; rw [hz]; simp)⟩,(hs z).mpr hz⟩
  rw [hs,hexi]
  rcases uniqueHF_spec (v 1).val with ⟨z,hz,he⟩ | ⟨hne,he⟩
  · rw [he,hz]
    simp only [Finset.singleton_inj,exists_eq',not_true_eq_false,and_false,or_false]
    exact eq_comm
  · rw [he]
    constructor
    · rintro (h | ⟨h,_⟩)
      · exact False.elim (hne ⟨_,h⟩)
      · exact h
    · intro h; exact Or.inr ⟨h,hne⟩

omit ι R A d S m hd hp hmem hset hm in
lemma uniform_card
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) (K : ℕ) : UniformDefinable S m 2
    (fun _ v => BoundedCard d K (v 0) (v 1)) := by
  have hmemb : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 2).val) :=
    hmem.reindex (![0,2] : Fin 2 → Fin 3)
  have hdis : UniformDefinable S m 2 (fun i v => ∃ n ∈ range (K+1),
      Nonempty ({y : Domain (d i) // y.val ∈ (v 1).val} ≃ Fin n) ∧ (v 0).val = ordinal n) := by
    apply UniformDefinable.exists_finset
    intro n hn
    have hc := hmemb.exact (by omega) n
    have ho := (HFCoding.uniform_ordinal S hmem hset hm hd hp n).reindex (![0] : Fin 1 → Fin 2)
    exact hc.and ho
  apply hdis.congr
  intro i v
  simp only [member_count_iff d hd,mem_range,BoundedCard,cardinalityHF]
  constructor
  · rintro ⟨n,hn,hc,he⟩; exact ⟨by omega,by rwa [hc]⟩
  · rintro ⟨hc,he⟩; exact ⟨_,by omega,rfl,he⟩

omit ι R A d S m hd hp hmem hset hm in
lemma uniform_boolean
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) {n : ℕ} {P : ∀ i, (Fin (n+1) → Domain (d i)) → Prop}
    (hP : UniformDefinable S m (n+1) P) :
    UniformDefinable S m (n+1) (fun i v => (v 0).val = boolean (P i v)) := by
  have ht := (HFCoding.uniform_ordinal S hmem hset hm hd hp 1).reindex (![0] : Fin 1 → Fin (n+1))
  have hf := (HFCoding.uniform_ordinal S hmem hset hm hd hp 0).reindex (![0] : Fin 1 → Fin (n+1))
  apply ((ht.and hP).or (hf.and hP.neg)).congr
  intro i v
  change ((v 0).val = truth ∧ P i v ∨ (v 0).val = empty ∧ ¬ P i v) ↔ _
  by_cases hh : P i v <;> simp [boolean,hh]

end CPTSeparation.Operational

namespace CPTSeparation.Counting.UniformDefinable

open Classical Finset

variable {ι R : Type} {D : ι → Type} {S : ∀ i, Structure R (D i)} {m n r : ℕ}

lemma forall_finset {X : Type} {P : X → ∀ i, (Fin n → D i) → Prop} (t : Finset X)
    (h : ∀ a ∈ t, UniformDefinable S m n (P a)) :
    UniformDefinable S m n (fun i v => ∀ a ∈ t, P a i v) := by
  apply (exists_finset t (fun a ha => (h a ha).neg)).neg.congr
  intro i v; simp

lemma forall_finite {X : Type} [Fintype X] {P : X → ∀ i, (Fin n → D i) → Prop}
    (h : ∀ a, UniformDefinable S m n (P a)) :
    UniformDefinable S m n (fun i v => ∀ a, P a i v) := by
  simpa only [Finset.mem_univ,true_implies] using forall_finset univ (fun a _ => h a)

lemma append_cons {X : Type} (x : X) (u : Fin r → X) (v : Fin n → X) :
    Fin.append (Fin.cons x u) v = Fin.cons x (Fin.append u v) ∘
      (finCongr (by omega : (r+1)+n = r+n+1)) := by
  rw [Fin.append_cons]
  congr 1

lemma exists_vec {P : ∀ i, (Fin (r+n) → D i) → Prop}
    (h : UniformDefinable S m (r+n) P) (hroom : r+n ≤ m) :
    UniformDefinable S m n (fun i v => ∃ u : Fin r → D i, P i (Fin.append u v)) := by
  induction r with
  | zero =>
    have h' := h.reindex (finCongr (Nat.zero_add n))
    apply h'.congr
    intro i v
    have he (u : Fin 0 → D i) : Fin.append u v = v ∘ finCongr (Nat.zero_add n) := by
      rw [Fin.append_left_nil u v rfl]
      congr 1
    constructor
    · intro hp; exact ⟨Fin.elim0,by rw [he]; exact hp⟩
    · rintro ⟨u,hp⟩; rwa [he] at hp
  | succ r ih =>
    have h' := h.reindex (finCongr (by omega : (r+1)+n = (r+n)+1))
    have he := h'.ex (by omega)
    have hi := ih he (by omega)
    apply hi.congr
    intro i v
    constructor
    · rintro ⟨u,x,hp⟩
      exact ⟨Fin.cons x u,by simpa only [append_cons] using hp⟩
    · rintro ⟨u,hp⟩
      refine ⟨Fin.tail u,u 0,?_⟩
      simpa only [← append_cons,Fin.cons_self_tail] using hp

lemma compose_unary {P : ∀ i, (Fin (n+1) → D i) → Prop}
    {Q : ∀ i, (Fin 2 → D i) → Prop}
    (hP : UniformDefinable S m (n+1) P) (hQ : UniformDefinable S m 2 Q)
    (hr : n+1 < m) : UniformDefinable S m (n+1)
      (fun i v => ∃ x, P i (Fin.cons x (Fin.tail v)) ∧ Q i ![v 0,x]) := by
  have h1 := hP.reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2))
  have h2 := hQ.reindex (![1,0] : Fin 2 → Fin (n+2))
  apply ((h1.and h2).ex hr).congr
  intro i v
  apply exists_congr; intro x
  have he : Fin.cons x v ∘ (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2)) =
      Fin.cons x (Fin.tail v) := by funext j; refine Fin.cases rfl (fun _ => rfl) j
  have he2 : Fin.cons x v ∘ (![1,0] : Fin 2 → Fin (n+2)) = ![v 0,x] := by
    funext j; fin_cases j <;> rfl
  simp only [he,he2]

lemma compose_binary {P Q : ∀ i, (Fin (n+1) → D i) → Prop}
    {T : ∀ i, (Fin 3 → D i) → Prop}
    (hP : UniformDefinable S m (n+1) P) (hQ : UniformDefinable S m (n+1) Q)
    (hT : UniformDefinable S m 3 T) (hr : n+2 < m) :
    UniformDefinable S m (n+1) (fun i v => ∃ x y,
      P i (Fin.cons x (Fin.tail v)) ∧ Q i (Fin.cons y (Fin.tail v)) ∧ T i ![v 0,x,y]) := by
  have h1 := hP.reindex (Fin.cons 1 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3))
  have h2 := hQ.reindex (Fin.cons 0 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3))
  have h3 := hT.reindex (![2,1,0] : Fin 3 → Fin (n+3))
  apply (((h1.and (h2.and h3)).ex hr).ex (by omega)).congr
  intro i v
  apply exists_congr; intro x
  apply exists_congr; intro y
  have he1 : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 1 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3)) =
        Fin.cons x (Fin.tail v) := by funext j; refine Fin.cases rfl (fun _ => rfl) j
  have he2 : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 0 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3)) =
        Fin.cons y (Fin.tail v) := by funext j; refine Fin.cases rfl (fun _ => rfl) j
  have he3 : Fin.cons y (Fin.cons x v) ∘ (![2,1,0] : Fin 3 → Fin (n+3)) = ![v 0,x,y] := by
    funext j; fin_cases j <;> rfl
  simp only [he1,he2,he3]

lemma compose_vec {P : Fin r → ∀ i, (Fin (n+1) → D i) → Prop}
    {Q : ∀ i, (Fin (r+1) → D i) → Prop}
    (hP : ∀ j, UniformDefinable S m (n+1) (P j)) (hQ : UniformDefinable S m (r+1) Q)
    (hr : r+(n+1) ≤ m) : UniformDefinable S m (n+1)
      (fun i v => ∃ w : Fin r → D i,
        (∀ j, P j i (Fin.cons (w j) (Fin.tail v))) ∧ Q i (Fin.cons (v 0) w)) := by
  let ix (j : Fin r) : Fin (n+1) → Fin (r+(n+1)) :=
    Fin.cons (j.castAdd (n+1)) (fun l => l.succ.natAdd r)
  let iq : Fin (r+1) → Fin (r+(n+1)) :=
    Fin.cons ((0 : Fin (n+1)).natAdd r) (fun j => j.castAdd (n+1))
  have h1 := forall_finite (fun j => (hP j).reindex (ix j))
  have h2 := hQ.reindex iq
  apply ((h1.and h2).exists_vec hr).congr
  intro i v
  apply exists_congr
  intro w
  have he1 (j : Fin r) : Fin.append w v ∘ ix j = Fin.cons (w j) (Fin.tail v) := by
    funext l
    refine Fin.cases ?_ (fun l => ?_) l
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  have he2 : Fin.append w v ∘ iq = Fin.cons (v 0) w := by
    funext l
    refine Fin.cases ?_ (fun l => ?_) l
    · exact Fin.append_right _ _ _
    · exact Fin.append_left _ _ _
  simp only [he1,he2]

end CPTSeparation.Counting.UniformDefinable

namespace CPTSeparation.Operational.Term

open Classical Hereditary Counting HFCoding Finset

attribute [local instance] OAI.CPTSeparation.Operational.Term.instDecidableEqHF
variable {A R F : Type} {arity : F → ℕ} [Fintype A]

variable (d : Set (HF A)) (K : ℕ) (rel : R → A → A → Bool) (s : State F arity A)

variable (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d)

include hd in
lemma graph_sound {k : ℕ} (t : Term R F arity k) (z : Domain d) (v : Fin k → Domain d)
    (h : Graph d K rel s t z v) : z.val = t.eval rel s (fun j => (v j).val) := by
  induction t generalizing z with
  | var j => exact congrArg Subtype.val h
  | constant n => exact h
  | atoms => exact h
  | app f args ih =>
    obtain ⟨w,hw,hz⟩ := h
    have he : (fun j => (w j).val) = fun j => (args j).eval rel s (fun j => (v j).val) := funext (fun j => ih j _ _ (hw j))
    simpa only [eval,he] using hz
  | pair a b iha ihb | equal a b iha ihb | member a b iha ihb | input r a b iha ihb | and a b iha ihb =>
    obtain ⟨x,y,hx,hy,hz⟩ := h
    simpa only [eval,iha _ _ hx,ihb _ _ hy] using hz
  | union a ih | unique a ih | isAtom a ih | not a ih =>
    obtain ⟨x,hx,hz⟩ := h
    simpa only [eval,ih _ _ hx] using hz
  | card a ih =>
    obtain ⟨x,hx,_,hz⟩ := h
    simpa only [eval,ih _ _ hx] using hz
  | conditional c a b ihc iha ihb =>
    obtain ⟨x,hx,h⟩ := h
    have he := ihc _ _ hx
    rcases h with ⟨ht,h⟩ | ⟨ht,h⟩
    · simpa only [eval,← he,ite_eq_left ht] using iha _ _ h
    · simpa only [eval,← he,ite_eq_right ht] using ihb _ _ h
  | @comprehension k bound guard body ihb ihg ihy =>
    obtain ⟨b,hb,hall,hz,hmem⟩ := h
    have heb := ihb _ _ hb
    apply ext_sets hz (isSet_ofFinset _)
    intro y

    simp only [mem_ofFinset,mem_image,mem_filter]
    have hc (x : Domain d) : (fun j : Fin (k+1) => ((Fin.cons x v : Fin (k+1) → Domain d) j).val) = Fin.cons x.val (fun j => (v j).val) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    constructor
    · intro hy
      obtain ⟨x,hxb,⟨g,hg,hgt⟩,hyb⟩ := (hmem ⟨y,hd _ z.property _ hy⟩).mp hy
      refine ⟨x.val,⟨by rwa [← heb],?_⟩,?_⟩
      · rw [← hc x,← ihg _ _ hg]; exact hgt
      · have he : y = body.eval rel s (Fin.cons x.val (fun j => (v j).val)) := by
          simpa only [hc] using ihy _ _ hyb
        exact he.symm
    · rintro ⟨x,⟨hxb,hgt⟩,heq⟩
      have hxd : x ∈ d := hd _ b.property _ (by rwa [heb])
      let xx : Domain d := ⟨x,hxd⟩
      obtain ⟨g,w,hg,hw⟩ := hall xx (by change x ∈ b.val; rwa [heb])
      have hgw := ihg _ _ hg
      have hyw := ihy _ _ hw
      simp only [hc] at hgw hyw
      have hyw' : w.val = y := hyw.trans heq
      have hyd : y ∈ d := hyw' ▸ w.property
      apply (hmem ⟨y,hyd⟩).mpr
      refine ⟨xx,by change x ∈ b.val; rwa [heb],⟨g,hg,?_⟩,?_⟩
      · exact hgw.trans hgt
      · have he : w = (⟨y,hyd⟩ : Domain d) := Subtype.ext hyw'
        rwa [← he]

lemma eval_mem_trace {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) :
    t.eval rel s v ∈ t.trace rel s v :=
  closure_eval_subset_trace rel s t v (mem_closure_self _)

include hd in
lemma graph_complete {k : ℕ} (t : Term R F arity k) (v : Fin k → Domain d)
    (ht : ∀ x ∈ t.trace rel s (fun j => (v j).val), x ∈ d ∧ (elements x).card ≤ K) :
    ∃ z : Domain d, Graph d K rel s t z v ∧ z.val = t.eval rel s (fun j => (v j).val) := by
  have result {k : ℕ} (t : Term R F arity k) (v : Fin k → Domain d)
      (ht : ∀ x ∈ t.trace rel s (fun j => (v j).val), x ∈ d ∧ (elements x).card ≤ K) :
      t.eval rel s (fun j => (v j).val) ∈ d := (ht _ (eval_mem_trace rel s t _)).1
  induction t with
  | var j => exact ⟨v j,rfl,rfl⟩
  | constant n => exact ⟨⟨ordinal n,result _ _ ht⟩,rfl,rfl⟩
  | atoms => exact ⟨⟨allAtoms,result _ _ ht⟩,rfl,rfl⟩
  | app f args ih =>
    have hall : ∀ j, ∃ x : Domain d, Graph d K rel s (args j) x v ∧
        x.val = (args j).eval rel s (fun j => (v j).val) := by
      intro j
      apply ih j
      intro x hx
      apply ht x
      exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,hx⟩)
    choose w hw using hall
    refine ⟨⟨_,result _ _ ht⟩,⟨w,fun j => (hw j).1,?_⟩,rfl⟩
    change s.value _ = s.value _
    congr 1
    exact Sigma.ext rfl (heq_of_eq (funext (fun j => (hw j).2.symm)))
  | pair a b iha ihb | equal a b iha ihb | member a b iha ihb | input r a b iha ihb | and a b iha ihb =>
    obtain ⟨x,hx,hex⟩ := iha v (by
      intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
    obtain ⟨y,hy,hey⟩ := ihb v (by
      intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
    refine ⟨⟨_,result _ _ ht⟩,⟨x,y,hx,hy,?_⟩,rfl⟩
    simp only [eval,hex,hey]
  | union a ih | unique a ih | isAtom a ih | not a ih =>
    obtain ⟨x,hx,hex⟩ := ih v (by
      intro x hx; apply ht x; exact mem_union_right _ hx)
    refine ⟨⟨_,result _ _ ht⟩,⟨x,hx,?_⟩,rfl⟩
    simp only [eval,hex]
  | card a ih =>
    obtain ⟨x,hx,hex⟩ := ih v (by
      intro x hx; apply ht x; exact mem_union_right _ hx)
    refine ⟨⟨_,result _ _ ht⟩,⟨x,hx,?_,?_⟩,rfl⟩
    · rw [hex]; exact (ht _ (mem_union_right _ (eval_mem_trace rel s a _))).2
    · simp only [eval,hex]
  | conditional c a b ihc iha ihb =>
    obtain ⟨x,hx,hex⟩ := ihc v (by
      intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
    by_cases hc : x.val = truth
    · obtain ⟨z,hz,hez⟩ := iha v (by
        intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
      refine ⟨z,⟨x,hx,Or.inl ⟨hc,hz⟩⟩,?_⟩
      simpa only [eval,← hex,ite_eq_left hc] using hez
    · obtain ⟨z,hz,hez⟩ := ihb v (by
        intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
      refine ⟨z,⟨x,hx,Or.inr ⟨hc,hz⟩⟩,?_⟩
      simpa only [eval,← hex,ite_eq_right hc] using hez
  | @comprehension k bound guard body ihb ihg ihy =>
    obtain ⟨b,hb,heb⟩ := ihb v (by
      intro x hx; apply ht x; exact mem_insert_of_mem (mem_union_left _ hx))
    have hc (x : Domain d) : (fun j : Fin (k+1) => ((Fin.cons x v : Fin (k+1) → Domain d) j).val) =
        Fin.cons x.val (fun j => (v j).val) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    have hall (x : Domain d) (hxb : x.val ∈ b.val) :
        (∃ g, Graph d K rel s guard g (Fin.cons x v) ∧ g.val = guard.eval rel s (Fin.cons x.val (fun j => (v j).val))) ∧
        (∃ y, Graph d K rel s body y (Fin.cons x v) ∧ y.val = body.eval rel s (Fin.cons x.val (fun j => (v j).val))) := by
      constructor
      · have hh := ihg (Fin.cons x v) (by
          intro y hy; apply ht y
          apply mem_insert_of_mem
          apply mem_union_right
          apply mem_biUnion.mpr
          refine ⟨x.val,by rwa [← heb],?_⟩
          apply mem_union_left
          simpa only [hc] using hy)
        simpa only [hc] using hh
      · have hh := ihy (Fin.cons x v) (by
          intro y hy; apply ht y
          apply mem_insert_of_mem
          apply mem_union_right
          apply mem_biUnion.mpr
          refine ⟨x.val,by rwa [← heb],?_⟩
          apply mem_union_right
          simpa only [hc] using hy)
        simpa only [hc] using hh
    let z : Domain d := ⟨_,result _ _ ht⟩
    refine ⟨z,⟨b,hb,?_,isSet_ofFinset _,?_⟩,rfl⟩
    · intro x hx
      obtain ⟨⟨g,hg,_⟩,⟨y,hy,_⟩⟩ := hall x hx
      exact ⟨g,y,hg,hy⟩
    · intro y
      change y.val ∈ ofFinset _ ↔ _
      simp only [mem_ofFinset,mem_image,mem_filter]
      constructor
      · rintro ⟨x,⟨hx,htrue⟩,hy⟩
        have hxd : x ∈ d := (ht _ (mem_insert_of_mem (mem_union_left _
          (closure_eval_subset_trace rel s bound _ (elements_subset_closure _ hx))))).1
        let xx : Domain d := ⟨x,hxd⟩
        have hxb : xx.val ∈ b.val := by change x ∈ b.val; rwa [heb]
        obtain ⟨⟨g,hg,heg⟩,⟨w,hw,hew⟩⟩ := hall xx hxb
        refine ⟨xx,hxb,⟨g,hg,heg.trans htrue⟩,?_⟩
        have he : w = y := Subtype.ext (hew.trans hy)
        rwa [← he]
      · rintro ⟨x,hxb,⟨g,hg,hgt⟩,hy⟩
        have heg := graph_sound d K rel s hd guard g (Fin.cons x v) hg
        have hey := graph_sound d K rel s hd body y (Fin.cons x v) hy
        simp only [hc] at heg hey
        exact ⟨x.val,⟨by rwa [← heb],heg.symm.trans hgt⟩,hey.symm⟩

end CPTSeparation.Operational.Term

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

variable {ι R : Type} {A : ι → Type} (d : ∀ i, Set (HF (A i)))

variable (S : ∀ i, Counting.Structure R (Domain (d i))) {m k : ℕ}

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (htruth : UniformDefinable S m 1 (fun _ v => (v 0).val = truth))

include hmem hset htruth in
lemma uniform_comprehension
    {P : ∀ i, Domain (d i) → (Fin k → Domain (d i)) → Prop}
    {Q T : ∀ i, Domain (d i) → (Fin (k+1) → Domain (d i)) → Prop}
    (hP : UniformDefinable S m (k+1) (fun i v => P i (v 0) (Fin.tail v)))
    (hQ : UniformDefinable S m (k+2) (fun i v => Q i (v 0) (Fin.tail v)))
    (hT : UniformDefinable S m (k+2) (fun i v => T i (v 0) (Fin.tail v)))
    (hm : k+5 ≤ m) : UniformDefinable S m (k+1) (fun i v => ∃ b,
      P i b (Fin.tail v) ∧
      (∀ x : Domain (d i), x.val ∈ b.val → ∃ g y,
        Q i g (Fin.cons x (Fin.tail v)) ∧ T i y (Fin.cons x (Fin.tail v))) ∧
      isSet (v 0).val = true ∧ ∀ y : Domain (d i), y.val ∈ (v 0).val ↔ ∃ x : Domain (d i),
        x.val ∈ b.val ∧ (∃ g, Q i g (Fin.cons x (Fin.tail v)) ∧ g.val = truth) ∧
        T i y (Fin.cons x (Fin.tail v))) := by
  have hQtotal := hQ.reindex (Fin.cons 1 (Fin.cons 2 (fun j => j.succ.succ.succ.succ.succ)) : Fin (k+2) → Fin (k+5))
  have hTtotal := hT.reindex (Fin.cons 0 (Fin.cons 2 (fun j => j.succ.succ.succ.succ.succ)) : Fin (k+2) → Fin (k+5))
  have htotal := ((hmem.reindex (![0,1] : Fin 2 → Fin (k+3))).imp
    (((hQtotal.and hTtotal).ex (by omega)).ex (by omega))).all (by omega)
  have hQmember := hQ.reindex (Fin.cons 0 (Fin.cons 1 (fun j => j.succ.succ.succ.succ.succ)) : Fin (k+2) → Fin (k+5))
  have hgtruth := htruth.reindex (![0] : Fin 1 → Fin (k+5))
  have hguard := (hQmember.and hgtruth).ex (by omega)
  have hTmember := hT.reindex (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ.succ.succ)) : Fin (k+2) → Fin (k+4))
  have hrhs := ((hmem.reindex (![0,2] : Fin 2 → Fin (k+4))).and (hguard.and hTmember)).ex (by omega)
  have hext := ((hmem.reindex (![0,2] : Fin 2 → Fin (k+3))).iff hrhs).all (by omega)
  have hbound := hP.reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (k+1) → Fin (k+2))
  have hset' := hset.reindex (![1] : Fin 1 → Fin (k+2))
  apply ((hbound.and (htotal.and (hset'.and hext))).ex (by omega)).congr
  intro i v
  simp only [Fin.comp_cons,Fin.cons_zero,Fin.tail_cons,Function.comp_apply]
  rfl

end CPTSeparation.Operational

namespace CPTSeparation.Operational.Term

open Classical Hereditary Counting HFCoding Finset

local instance instDecidableEqHF_1_redf58b_1 {A : Type*} : DecidableEq (HF A) := Classical.decEq _
variable {R F : Type} {arity : F → ℕ}

variable {ι L : Type} {A : ι → Type} [∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool) (s : ∀ i, State F arity (A i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

include hd hp ha hmem hset hinput hstate in
lemma uniform_graph (K : ℕ) {k : ℕ} (t : Term R F arity k) (hm : t.width ≤ m) :
    UniformDefinable S m (k+1) (fun i v => Graph (d i) K (rel i) (s i) t (v 0) (Fin.tail v)) := by
  induction t with
  | var j => exact UniformDefinable.equal 0 j.succ
  | constant n =>
    simp only [width] at hm
    exact (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp n).reindex ![0]
  | atoms =>
    simp only [width] at hm
    exact (uniform_atoms d S hd ha hmem hset (by omega)).reindex ![0]
  | @app k f args ih =>
    simp only [width] at hm
    have hh (j) := (single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin (arity f)))) => Nat.zero_le (width (args j))) (mem_univ j))
    have hh' := UniformDefinable.compose_vec (fun j => ih j (by have := hh j; omega)) (hstate f) (by omega)
    simpa only [Graph,Fin.cons_zero,Fin.tail_cons,Fin.cons_succ] using hh'
  | pair a b iha ihb =>
    simp only [width] at hm
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega))
      (uniform_double_value d S hd hmem hset (by omega)) (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | union a ih =>
    simp only [width] at hm
    have hh := UniformDefinable.compose_unary (ih (by omega)) (uniform_union d S hd hmem hset (by omega)) (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | unique a ih =>
    simp only [width] at hm
    have hh := UniformDefinable.compose_unary (ih (by omega)) (uniform_unique d S hd hp hmem hset (by omega)) (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | card a ih =>
    simp only [width] at hm
    have hh := UniformDefinable.compose_unary (ih (by omega)) (uniform_card d S hd hp hmem hset (by omega) K) (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,BoundedCard,Fin.cons_zero,Fin.tail_cons]
    rfl
  | equal a b iha ihb =>
    simp only [width] at hm
    have htest : UniformDefinable S m 3 (fun _ v => (v 1).val = (v 2).val) :=
      (UniformDefinable.equal 1 2).congr (fun _ _ => Subtype.ext_iff)
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) htest
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | member a b iha ihb =>
    simp only [width] at hm
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) (hmem.reindex (![1,2] : Fin 2 → Fin 3))
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | isAtom a ih =>
    simp only [width] at hm
    have htest : UniformDefinable S m 2 (fun _ v => isSet (v 1).val = false) := by
      apply (hset.reindex (![1] : Fin 1 → Fin 2)).neg.congr
      intro i v; dsimp; cases isSet (v 1).val <;> simp
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) htest
    have hh := UniformDefinable.compose_unary (ih (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | input r a b iha ihb =>
    simp only [width] at hm
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) ((hinput r).reindex (![1,2] : Fin 2 → Fin 3))
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | not a ih =>
    simp only [width] at hm
    have ht := (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1).reindex (![1] : Fin 1 → Fin 2)
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) ht.neg
    have hh := UniformDefinable.compose_unary (ih (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | and a b iha ihb =>
    simp only [width] at hm
    have ht := HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1
    have hpred := (ht.reindex (![1] : Fin 1 → Fin 3)).and (ht.reindex (![2] : Fin 1 → Fin 3))
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) hpred
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | @conditional k c a b ihc iha ihb =>
    simp only [width] at hm
    have h0 := (ihc (by omega)).reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (k+1) → Fin (k+2))
    have h1 := (iha (by omega)).reindex (Fin.succ : Fin (k+1) → Fin (k+2))
    have h2 := (ihb (by omega)).reindex (Fin.succ : Fin (k+1) → Fin (k+2))
    have ht := (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1).reindex (![0] : Fin 1 → Fin (k+2))
    apply ((h0.and ((ht.and h1).or (ht.neg.and h2))).ex (by omega)).congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.cons_succ,Function.comp_def]
    rfl
  | comprehension bound guard body ihb ihg ihy =>
    simp only [width] at hm
    exact uniform_comprehension d S hmem hset (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1)
      (ihb (by omega)) (ihg (by omega)) (ihy (by omega)) (by omega)

end CPTSeparation.Operational.Term

namespace CPTSeparation.Operational.Rule

section

open Classical Hereditary Finset

variable {A R F : Type} {arity : F → ℕ} [Fintype A]

attribute [local instance] OAI.CPTSeparation.Operational.Rule.instDecidableEqHF
lemma closure_update_subset_trace (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A)
    {l : Location F arity A} {z : HF A} (hu : (l,z) ∈ r.updates rel s v) :
    closure z ⊆ r.trace rel s v ∧ ∀ j, closure (l.2 j) ⊆ r.trace rel s v := by
  induction r generalizing l z with
  | skip => simp [updates] at hu
  | update f args value =>
    have he := mem_singleton.mp hu
    cases he
    refine ⟨(Term.closure_eval_subset_trace rel s value v).trans subset_union_left,?_⟩
    intro j x hx
    exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,Term.closure_eval_subset_trace rel s (args j) v hx⟩)
  | parallel a b ia ib =>
    rcases mem_union.mp hu with ha | hb
    · obtain ⟨hz,hl⟩ := ia v ha
      exact ⟨hz.trans subset_union_left, fun j => (hl j).trans subset_union_left⟩
    · obtain ⟨hz,hl⟩ := ib v hb
      exact ⟨hz.trans subset_union_right, fun j => (hl j).trans subset_union_right⟩
  | conditional c a b ia ib =>
    unfold updates at hu
    split at hu
    · obtain ⟨hz,hl⟩ := ia v hu
      have hs : a.trace rel s v ⊆ (conditional c a b).trace rel s v :=
        subset_union_right.trans subset_union_left
      exact ⟨hz.trans hs,fun j => (hl j).trans hs⟩
    · obtain ⟨hz,hl⟩ := ib v hu
      exact ⟨hz.trans subset_union_right,fun j => (hl j).trans subset_union_right⟩
  | «forall» b r ih =>
    obtain ⟨x,hx,hu⟩ := mem_biUnion.mp hu
    obtain ⟨hz,hl⟩ := ih _ hu
    have hs : r.trace rel s (Fin.cons x v) ⊆ (Rule.forall b r).trace rel s v := by
      intro y hy; exact mem_union_right _ (mem_biUnion.mpr ⟨x,hx,hy⟩)
    exact ⟨hz.trans hs,fun j => (hl j).trans hs⟩
  | letValue b r ih =>
    obtain ⟨hz,hl⟩ := ih _ hu
    exact ⟨hz.trans subset_union_right,fun j => (hl j).trans subset_union_right⟩

lemma card_trace_le (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A) (K : ℕ) (hK : Term.potential s v ≤ K) :
    (r.trace rel s v).card ≤ r.bound.eval K := by
  induction r generalizing K with
  | skip => simp [trace,bound]
  | update f args value =>
    have hu := (card_union_le (value.trace rel s v) (univ.biUnion (fun j => (args j).trace rel s v))).trans
      (add_le_add (Term.card_trace_le rel s value v K hK)
        (card_biUnion_le.trans (sum_le_sum (fun j hj => Term.card_trace_le rel s (args j) v K hK))))
    simpa only [trace,bound,Polynomial.eval_add,Polynomial.eval_finsetSum] using hu
  | parallel a b ia ib =>
    exact (card_union_le _ _).trans (by simpa only [bound,Polynomial.eval_add] using add_le_add (ia v K hK) (ib v K hK))
  | conditional c a b ia ib =>
    exact (card_union_le _ _).trans ((add_le_add (card_union_le _ _) (le_refl _)).trans (by
      simpa only [bound,Polynomial.eval_add] using add_le_add (add_le_add (Term.card_trace_le rel s c v K hK) (ia v K hK)) (ib v K hK)))
  | «forall» b r ih =>
    have hb := Term.card_trace_le rel s b v K hK
    have hc := (card_le_card ((elements_subset_closure (b.eval rel s v)).trans (Term.closure_eval_subset_trace rel s b v))).trans hb
    have he (x) (hx : x ∈ elements (b.eval rel s v)) : Term.potential s (Fin.cons x v) ≤ K+b.bound.eval K := by
      rw [Term.potential_cons]
      exact add_le_add hK ((card_le_card ((closure_member_subset hx).trans (Term.closure_eval_subset_trace rel s b v))).trans hb)
    have hs : ((elements (b.eval rel s v)).biUnion (fun x => r.trace rel s (Fin.cons x v))).card ≤
        b.bound.eval K * r.bound.eval (K+b.bound.eval K) := by
      apply card_biUnion_le.trans
      calc
        _ ≤ ∑ _x ∈ elements (b.eval rel s v), r.bound.eval (K+b.bound.eval K) := sum_le_sum (fun x hx => ih _ _ (he x hx))
        _ = (elements (b.eval rel s v)).card * r.bound.eval (K+b.bound.eval K) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hc
    exact (card_union_le _ _).trans (by simpa only [bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X] using add_le_add hb hs)
  | letValue b r ih =>
    have hb := Term.card_trace_le rel s b v K hK
    have he : Term.potential s (Fin.cons (b.eval rel s v) v) ≤ K+b.bound.eval K := by
      rw [Term.potential_cons]
      exact add_le_add hK ((card_le_card (Term.closure_eval_subset_trace rel s b v)).trans hb)
    exact (card_union_le _ _).trans (by simpa only [bound,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X] using add_le_add hb (ih _ _ he))

end

section

open Classical Hereditary Counting HFCoding Finset

variable {A R F : Type} {arity : F → ℕ} [Fintype A]

attribute [local instance] OAI.CPTSeparation.Operational.Rule.instDecidableEqHF_1
variable (d : Set (HF A)) (K : ℕ) (rel : R → A → A → Bool) (s : State F arity A)

variable (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d)

include hd in
lemma graph_sound {k : ℕ} (r : Rule R F arity k) (f : F) (z : Domain d)
    (a : Fin (arity f) → Domain d) (v : Fin k → Domain d)
    (h : Graph d K rel s r f z a v) :
    (⟨f,fun j => (a j).val⟩,z.val) ∈ r.updates rel s (fun j => (v j).val) := by
  induction r generalizing f z a with
  | skip => exact h.elim
  | update g args value =>
    unfold Graph at h
    split at h
    next he =>
      subst g
      obtain ⟨hz,ha⟩ := h
      have hv := Term.graph_sound d K rel s hd value z v hz
      have ha' : (fun j => (a j).val) = fun j => (args j).eval rel s (fun j => (v j).val) :=
        funext (fun j => Term.graph_sound d K rel s hd (args j) (a j) v (ha j))
      simp only [updates,Finset.mem_singleton,hv,ha']
    next he => exact h.elim
  | parallel r t ir it => exact h.elim (fun h => mem_union_left _ (ir _ _ _ _ h)) (fun h => mem_union_right _ (it _ _ _ _ h))
  | conditional c r t ir it =>
    obtain ⟨b,hb,h⟩ := h
    have he := Term.graph_sound d K rel s hd c b v hb
    rcases h with ⟨hc,hr⟩ | ⟨hc,ht⟩
    · simpa only [updates,← he,ite_eq_left hc] using ir _ _ _ _ hr
    · simpa only [updates,← he,ite_eq_right hc] using it _ _ _ _ ht
  | @«forall» k b r ih =>
    obtain ⟨w,x,hw,hx,hr⟩ := h
    have he := Term.graph_sound d K rel s hd b w v hw
    refine mem_biUnion.mpr ⟨x.val,by rwa [← he],?_⟩
    have hv : (fun j => ((Fin.cons x v : Fin (k+1) → Domain d) j).val) = Fin.cons x.val (fun j => (v j).val) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    simpa only [hv] using ih f z a (Fin.cons x v) hr
  | @letValue k b r ih =>
    obtain ⟨w,hw,hr⟩ := h
    have he := Term.graph_sound d K rel s hd b w v hw
    have hv : (fun j => ((Fin.cons w v : Fin (k+1) → Domain d) j).val) = Fin.cons w.val (fun j => (v j).val) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    simpa only [updates,hv,he] using ih f z a (Fin.cons w v) hr

include hd in
lemma graph_complete {k : ℕ} (r : Rule R F arity k) (f : F) (z : Domain d)
    (a : Fin (arity f) → Domain d) (v : Fin k → Domain d)
    (ht : ∀ x ∈ r.trace rel s (fun j => (v j).val), x ∈ d ∧ (elements x).card ≤ K)
    (hu : (⟨f,fun j => (a j).val⟩,z.val) ∈ r.updates rel s (fun j => (v j).val)) :
    Graph d K rel s r f z a v := by
  have witness {k} (t : Term R F arity k) (v : Fin k → Domain d)
      (ht : ∀ x ∈ t.trace rel s (fun j => (v j).val), x ∈ d ∧ (elements x).card ≤ K) :=
    Term.graph_complete d K rel s hd t v ht
  have hv {k} (x : Domain d) (v : Fin k → Domain d) :
      (fun j => ((Fin.cons x v : Fin (k+1) → Domain d) j).val) = Fin.cons x.val (fun j => (v j).val) := by
    funext j; refine Fin.cases rfl (fun _ => rfl) j
  induction r generalizing f z a with
  | skip => simp [updates] at hu
  | update g args value =>
    have he := Finset.mem_singleton.mp hu
    have hfg : f = g := congrArg (fun p => p.1.1) he
    subst g
    have haz := (Prod.mk.inj he)
    have ha : (fun j => (a j).val) = fun j => (args j).eval rel s (fun j => (v j).val) := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp haz.1).2
    simp only [Graph,Fin.cast_refl,id_eq]
    constructor
    · obtain ⟨w,hw,hew⟩ := witness value v (fun x hx => ht x (mem_union_left _ hx))
      have hew' : w = z := Subtype.ext (hew.trans haz.2.symm)
      rwa [← hew']
    · intro j
      obtain ⟨w,hw,hew⟩ := witness (args j) v (fun x hx => ht x (mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,hx⟩)))
      have hew' : w = a j := Subtype.ext (hew.trans (congrFun ha j).symm)
      rwa [← hew']
  | parallel r t ir it =>
    rcases mem_union.mp hu with h | h
    · exact Or.inl (ir _ _ _ _ (fun x hx => ht x (mem_union_left _ hx)) h)
    · exact Or.inr (it _ _ _ _ (fun x hx => ht x (mem_union_right _ hx)) h)
  | conditional c r t ir it =>
    obtain ⟨b,hb,he⟩ := witness c v (fun x hx => ht x (mem_union_left _ (mem_union_left _ hx)))
    refine ⟨b,hb,?_⟩
    by_cases hc : b.val = truth
    · left; refine ⟨hc,ir _ _ _ _ (fun x hx => ht x (mem_union_left _ (mem_union_right _ hx))) ?_⟩
      simpa only [updates,← he,ite_eq_left hc] using hu
    · right; refine ⟨hc,it _ _ _ _ (fun x hx => ht x (mem_union_right _ hx)) ?_⟩
      simpa only [updates,← he,ite_eq_right hc] using hu
  | @«forall» k b r ih =>
    obtain ⟨w,hw,he⟩ := witness b v (fun x hx => ht x (mem_union_left _ hx))
    obtain ⟨x,hx,hu⟩ := mem_biUnion.mp hu
    have hxd : x ∈ d := hd _ w.property _ (by rwa [he])
    let xx : Domain d := ⟨x,hxd⟩
    refine ⟨w,xx,hw,by change x ∈ w.val; rwa [he],ih _ _ _ (Fin.cons xx v) ?_ ?_⟩
    · intro y hy
      rw [hv] at hy
      exact ht y (mem_union_right _ (mem_biUnion.mpr ⟨x,hx,hy⟩))
    · simpa only [hv] using hu
  | @letValue k b r ih =>
    obtain ⟨w,hw,he⟩ := witness b v (fun x hx => ht x (mem_union_left _ hx))
    refine ⟨w,hw,ih _ _ _ (Fin.cons w v) ?_ ?_⟩
    · intro x hx
      rw [hv,he] at hx; exact ht x (mem_union_right _ hx)
    · simpa only [updates,hv,he] using hu

end

open Classical Hereditary Counting HFCoding Finset

variable {R F : Type} {arity : F → ℕ}

variable {ι L : Type} {A : ι → Type} [∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool) (s : ∀ i, State F arity (A i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

include hd hp ha hmem hset hinput hstate in
lemma uniform_graph (K : ℕ) {k n : ℕ} (r : Rule R F arity k) (f : F)
    (z : Fin n) (a : Fin (arity f) → Fin n) (v : Fin k → Fin n) (hm : n+r.width ≤ m) :
    UniformDefinable S m n (fun i w => Graph (d i) K (rel i) (s i) r f (w z) (w ∘ a) (w ∘ v)) := by
  have term {k n : ℕ} (t : Term R F arity k) (z : Fin n) (v : Fin k → Fin n) (ht : t.width ≤ m) :
      UniformDefinable S m n (fun i w => Term.Graph (d i) K (rel i) (s i) t (w z) (w ∘ v)) := by
    apply (Term.uniform_graph d S hd hp ha hmem hset rel s hinput hstate K t ht |>.reindex (Fin.cons z v)).congr
    intro i w
    simp only [Fin.comp_cons,Fin.cons_zero,Fin.tail_cons]
  induction r generalizing n with
  | skip => exact UniformDefinable.falsum
  | update g args value =>
    simp only [width] at hm
    by_cases h : g = f
    · subst g
      have hv := term value z v (by omega)
      have hag (j) := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin (arity f)))) => Nat.zero_le (Term.width (args j))) (mem_univ j)
      have has := UniformDefinable.forall_finite (fun j => term (args j) (a j) v (by have := hag j; omega))
      apply (hv.and has).congr
      intro i w
      simp [Graph]
    · apply UniformDefinable.falsum.congr
      intro i w; simp only [Graph,dite_eq_right h]
  | parallel r t ir it =>
    simp only [width] at hm
    exact (ir z a v (by omega)).or (it z a v (by omega))
  | @conditional k c r t ir it =>
    simp only [width] at hm
    let vv : Fin k → Fin (n+1) := Fin.succ ∘ v
    have hc := term c (0 : Fin (n+1)) vv (by omega)
    have hr := ir z.succ (Fin.succ ∘ a) vv (by omega)
    have ht := it z.succ (Fin.succ ∘ a) vv (by omega)
    have hb := (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1).reindex (![0] : Fin 1 → Fin (n+1))
    apply ((hc.and ((hb.and hr).or (hb.neg.and ht))).ex (by omega)).congr
    intro i w
    simp only [Graph,vv,Fin.cons_zero,Fin.cons_succ,Function.comp_apply]
    rfl
  | @«forall» k b r ih =>
    simp only [width] at hm
    let vv : Fin k → Fin (n+2) := fun j => (v j).succ.succ
    have hb := term b (1 : Fin (n+2)) vv (by omega)
    have hx := hmem.reindex (![0,1] : Fin 2 → Fin (n+2))
    have hr := ih z.succ.succ (fun j => (a j).succ.succ) (Fin.cons 0 vv) (by omega)
    apply (((hb.and (hx.and hr)).ex (by omega)).ex (by omega)).congr
    intro i w
    change (∃ b' x, _ ∧ _ ∧ _) ↔ _
    simp only [Graph,vv,Fin.comp_cons,Fin.cons_zero,Fin.cons_succ,Function.comp_apply]
    rfl
  | @letValue k b r ih =>
    simp only [width] at hm
    let vv : Fin k → Fin (n+1) := Fin.succ ∘ v
    have hb := term b (0 : Fin (n+1)) vv (by omega)
    have hr := ih z.succ (Fin.succ ∘ a) (Fin.cons 0 vv) (by omega)
    apply ((hb.and hr).ex (by omega)).congr
    intro i w
    simp only [Graph,vv,Fin.comp_cons,Fin.cons_zero,Fin.cons_succ]
    rfl

end CPTSeparation.Operational.Rule

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Operational

section

open Classical Hereditary Finset

variable {A R F : Type} {arity : F → ℕ} [finiteA : Fintype A]

namespace Closed

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_5
omit A in
lemma closure
    {A : Type}
    [Fintype A] (x : HF A) : Closed (Hereditary.closure x) := fun _ hx _ hy => closure_transitive hx hy

omit A in
lemma union
    {A : Type}
    [Fintype A] {s t : Finset (HF A)} (hs : Closed s) (ht : Closed t) : Closed (s ∪ t) := by
  intro x hx y hy
  rcases mem_union.mp hx with hx | hx
  · exact mem_union_left _ (hs x hx y hy)
  · exact mem_union_right _ (ht x hx y hy)

omit A in
lemma biUnion
    {A : Type}
    [Fintype A] {I : Type} (s : Finset I) (t : I → Finset (HF A)) (h : ∀ i ∈ s, Closed (t i)) : Closed (s.biUnion t) := by
  intro x hx y hy
  obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
  exact mem_biUnion.mpr ⟨i,hi,h i hi x hx y hy⟩

omit A in
lemma insert
    {A : Type}
    [Fintype A] {s : Finset (HF A)} {x : HF A} (hs : Closed s) (hx : ∀ y, y ∈ x → y ∈ s) : Closed (insert x s) := by
  intro y hy z hz
  rcases mem_insert.mp hy with rfl | hy
  · exact mem_insert_of_mem (hx z hz)
  · exact mem_insert_of_mem (hs y hy z hz)

end Closed

namespace Term

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_5
lemma trace_closed (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) : Closed (t.trace rel s v) := by
  induction t with
  | var i | constant n | atoms => exact Closed.closure _
  | app f args ih => exact (Closed.closure _).union (Closed.biUnion univ _ (fun j _ => ih j v))
  | pair a b ia ib | equal a b ia ib | member a b ia ib | input r a b ia ib | and a b ia ib =>
    exact ((Closed.closure _).union (ia v)).union (ib v)
  | union a ia | unique a ia | card a ia | isAtom a ia | not a ia => exact (Closed.closure _).union (ia v)
  | conditional c a b ic ia ib => exact ((ic v).union (ia v)).union (ib v)
  | comprehension b g t ib ig it =>
    apply Closed.insert ((ib v).union (Closed.biUnion _ _ (fun x hx => (ig _).union (it _))))
    intro y hy
    rw [mem_ofFinset] at hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact mem_union_right _ (mem_biUnion.mpr ⟨x,(mem_filter.mp hx).1,mem_union_right _ (closure_eval_subset_trace rel s t _ (mem_closure_self _))⟩)

end Term

namespace Rule

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_5
lemma trace_closed (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A) : Closed (r.trace rel s v) := by
  induction r with
  | skip => intro x hx; exact (Finset.notMem_empty x hx).elim
  | update f args value => exact (value.trace_closed rel s v).union (Closed.biUnion univ _ (fun j _ => (args j).trace_closed rel s v))
  | parallel r t ir it => exact (ir v).union (it v)
  | conditional c r t ir it => exact ((c.trace_closed rel s v).union (ir v)).union (it v)
  | «forall» b r ih => exact (b.trace_closed rel s v).union (Closed.biUnion _ _ (fun x hx => ih _))
  | letValue b r ih => exact (b.trace_closed rel s v).union (ih _)

end Rule

end

section

open Classical Hereditary Counting HFCoding Finset

variable {A R F : Type} {arity : F → ℕ}

namespace State

local instance instDecidableEqHF_6_redf58b_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _
lemma value_apply_iff (d : Set (HF A)) (s : State F arity A) (u : Finset (Update F arity A))
    (hc : Consistent u) (hv : ∀ l z, (l,z) ∈ u → z ∈ d)
    (l : Location F arity A) (z : Domain d) :
    z.val = (s.applyUpdates u).value l ↔
      (l,z.val) ∈ u ∨ (z.val = s.value l ∧ ¬∃ x : Domain d, (l,x.val) ∈ u) := by
  change z.val = s.updatedValue u l ↔ _
  by_cases hu : ∃ x, (l,x) ∈ u
  · obtain ⟨x,hx⟩ := hu
    rw [s.updatedValue_eq u hc hx]
    constructor
    · intro he; exact Or.inl (he ▸ hx)
    · rintro (h | ⟨_,h⟩)
      · exact hc l _ _ h hx
      · exact (h ⟨⟨x,hv l x hx⟩,hx⟩).elim
  · rw [s.updatedValue_default u hu]
    constructor
    · intro h; exact Or.inr ⟨h,fun ⟨x,hx⟩ => hu ⟨x.val,hx⟩⟩
    · rintro (h | ⟨h,_⟩)
      · exact (hu ⟨z.val,h⟩).elim
      · exact h

end State

local instance instDecidableEqHF_6_redf58b_2 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable {ι L : Type} {B : ι → Type} [finiteFamilyB : ∀ i, Fintype (B i)]

variable (d : ∀ i, Set (HF (B i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := B i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → B i → B i → Bool) (s : ∀ i, State F arity (B i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

include hd hp ha hmem hset hinput hstate in
lemma uniform_updates (K : ℕ) (r : Rule R F arity 0) (f : F)
    (hm : arity f+1+r.width ≤ m)
    (ht : ∀ i x, x ∈ r.trace (rel i) (s i) Fin.elim0 → x ∈ d i ∧ (elements x).card ≤ K) :
    UniformDefinable S m (arity f+1) (fun i v =>
      (⟨f,fun j => (v j.succ).val⟩,(v 0).val) ∈ r.updates (rel i) (s i) Fin.elim0) := by
  have h := Rule.uniform_graph d S hd hp ha hmem hset rel s hinput hstate K r f
    (0 : Fin (arity f+1)) Fin.succ Fin.elim0 hm
  apply h.congr
  intro i v
  have he : (fun j : Fin 0 => (v (Fin.elim0 j)).val) = Fin.elim0 := by funext j; exact Fin.elim0 j
  constructor
  · intro h
    have hh := Rule.graph_sound (d i) K (rel i) (s i) (hd i) r f (v 0) (v ∘ Fin.succ) (v ∘ Fin.elim0) h
    simpa only [Function.comp_apply,he] using hh
  · intro h
    apply Rule.graph_complete (d i) K (rel i) (s i) (hd i) r f (v 0) (v ∘ Fin.succ) (v ∘ Fin.elim0)
    · simpa only [Function.comp_apply,he] using ht i
    · simpa only [Function.comp_apply,he] using h

end

open Classical Hereditary Finset

variable {A B R F : Type} {arity : F → ℕ} [finiteA : Fintype A] [finiteB : Fintype B]

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_7
omit A B in
lemma lift_closure
    {A : Type}
    {B : Type}
    [Fintype A]
    [Fintype B] (e : A ≃ B) (x : HF A) : closure (lift e x) = (closure x).image (lift e) := closure_map e x

omit A B in
lemma lift_cons
    {A : Type}
    {B : Type}
    [Fintype A]
    [Fintype B] (e : A ≃ B) {k : ℕ} (x : HF A) (v : Fin k → HF A) :
    (fun j => lift e ((Fin.cons x v : Fin (k+1) → HF A) j)) = Fin.cons (lift e x) (fun j => lift e (v j)) := by
  funext j; refine Fin.cases rfl (fun _ => rfl) j

namespace Term

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_7
lemma trace_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) :
    t.trace rel' (s.transport e) (fun j => lift e (v j)) = (t.trace rel s v).image (lift e) := by
  have hev {k} (t : Term R F arity k) (v : Fin k → HF A) := eval_transport e rel rel' hrel s t v
  induction t with
  | var j => exact lift_closure e _
  | constant n => simp only [trace,← lift_ordinal e n,lift_closure]
  | atoms => rw [trace,trace,← lift_allAtoms e,lift_closure]
  | app f args ih =>
    simp only [trace,hev,ih,image_union,biUnion_image]
    rw [show (s.transport e).value ⟨f,fun j => lift e ((args j).eval rel s v)⟩ = lift e (s.value ⟨f,fun j => (args j).eval rel s v⟩) from s.transport_value e ⟨f,fun j => (args j).eval rel s v⟩,lift_closure]
  | pair a b ia ib => simp only [trace,hev,ia,ib,image_union,← lift_double,lift_closure]
  | union a ia => simp only [trace,hev,ia,image_union,← lift_union,lift_closure]
  | unique a ia => simp only [trace,hev,ia,image_union,← lift_unique,lift_closure]
  | card a ia => simp only [trace,hev,ia,image_union,← lift_card,lift_closure]
  | equal a b ia ib => simp only [trace,hev,ia,ib,image_union,Equiv.apply_eq_iff_eq,← lift_boolean e,lift_closure]
  | member a b ia ib => simp only [trace,hev,ia,ib,image_union,lift_mem_iff,← lift_boolean e,lift_closure]
  | isAtom a ia => simp only [trace,hev,ia,image_union,lift_isSet,← lift_boolean e,lift_closure]
  | input r a b ia ib => simp only [trace,hev,ia,ib,image_union,lift_input e rel rel' hrel,← lift_boolean e,lift_closure]
  | not a ia => simp only [trace,hev,ia,image_union,ne_eq,lift_truth_iff,← lift_boolean e,lift_closure]
  | and a b ia ib => simp only [trace,hev,ia,ib,image_union,lift_truth_iff,← lift_boolean e,lift_closure]
  | conditional c a b ic ia ib => simp only [trace,ic,ia,ib,image_union]
  | comprehension b g t ib ig it =>
    have hz := hev (comprehension b g t) v
    change insert ((comprehension b g t).eval rel' (s.transport e) _) _ = Finset.image (lift e) (insert ((comprehension b g t).eval rel s v) _)
    rw [hz,image_insert]
    congr 1
    simp only [ib,hev,lift_elements,biUnion_image,image_union,image_biUnion,biUnion_image]
    congr 1
    apply biUnion_congr rfl
    intro x hx
    rw [← lift_cons e x v,ig,it]

end Term

namespace Rule

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_7
lemma trace_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A) :
    r.trace rel' (s.transport e) (fun j => lift e (v j)) = (r.trace rel s v).image (lift e) := by
  have ht {k} (t : Term R F arity k) (v : Fin k → HF A) := t.trace_transport e rel rel' hrel s v
  have he {k} (t : Term R F arity k) (v : Fin k → HF A) := t.eval_transport e rel rel' hrel s v
  induction r with
  | skip => simp only [trace,image_empty]
  | update f args value => simp only [trace,ht,image_union,biUnion_image]
  | parallel r t ir it => simp only [trace,ir,it,image_union]
  | conditional c r t ir it => simp only [trace,ht,ir,it,image_union]
  | «forall» b r ih =>
    simp only [trace,ht,he,image_union,lift_elements,biUnion_image,image_biUnion]
    congr 1
    apply biUnion_congr rfl
    intro x hx
    rw [← lift_cons e x v,ih]
  | letValue b r ih =>
    simp only [trace,ht,he,image_union]
    rw [← lift_cons e (b.eval rel s v) v,ih]

end Rule

end CPTSeparation.Operational

namespace CPTSeparation.Operational.Machine

section

open Classical Hereditary Counting HFCoding Finset

variable {R ι L : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)]

variable (P : Machine R)

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool) (s : ∀ i, P.Store (A := A i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (P.functionArity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

omit R ι L A P d S m hd hp hmem hset s hstate in
lemma uniform_flag
    {R : Type}
    {ι : Type}
    {L : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (P : Operational.Machine R)
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (s : (i : ι) → P.Store (A := A i))
    (hstate : ∀ (f : Operational.Control ⊕ P.Functions),
  Counting.UniformDefinable S m (P.functionArity f + 1) fun i v =>
    ↑(v 0) = (s i).value ⟨f, fun j => ↑(v j.succ)⟩) (hm : 6 ≤ m) (c : Control) :
    UniformDefinable S m 0 (fun i _ => P.flag (s i) c) := by
  have ht := HFCoding.uniform_ordinal S hmem hset hm hd hp 1
  have hs := hstate (Sum.inl c)
  simp only [functionArity,Sum.elim_inl] at hs
  have hs' : UniformDefinable S m 1 (fun i v => (v 0).val = (s i).value ⟨Sum.inl c,Fin.elim0⟩) := by
    apply hs.congr
    intro i v
    have hh : (fun j : Fin 0 => (v j.succ).val) = Fin.elim0 := by funext j; exact Fin.elim0 j
    rw [hh]
    rfl
  apply (hs'.and ht).ex (by omega) |>.congr
  intro i v
  change (∃ x : Domain (d i), x.val = (s i).value ⟨Sum.inl c,_⟩ ∧ x.val = truth) ↔ _
  constructor
  · rintro ⟨x,hx,hxt⟩
    exact hx.symm.trans hxt
  · intro h
    exact ⟨⟨truth,hp i 1⟩,h.symm,rfl⟩

include hd hp ha hmem hset hinput hstate in
lemma uniform_step (K : ℕ) (s' : ∀ i, P.Store (A := A i))
    (hh : ∀ i, P.step (rel i) (s i) = some (s' i))
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m)
    (hroom : 6 ≤ m)
    (ht : ∀ i x, x ∈ P.rule.trace (rel i) (s i) Fin.elim0 → x ∈ d i ∧ (elements x).card ≤ K)
    (f : Control ⊕ P.Functions) :
    UniformDefinable S m (P.functionArity f+1) (fun i v =>
      (v 0).val = (s' i).value ⟨f,fun j => (v j.succ).val⟩) := by
  have hu (f) := uniform_updates d S hd hp ha hmem hset rel s hinput hstate K P.rule f (by have := hm f; omega) ht
  have hx := ((hu f).reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (P.functionArity f+1) → Fin (P.functionArity f+2))).ex (by have := hm f; omega)
  have hadd := (hu f).or ((hstate f).and hx.neg)
  have hhalt := (uniform_flag P d S hd hp hmem hset s hstate hroom .halt).reindex (Fin.elim0 : Fin 0 → Fin (P.functionArity f+1))
  apply ((hhalt.and (hstate f)).or (hhalt.neg.and hadd)).congr
  intro i v
  have hh' := hh i
  by_cases hf : P.flag (s i) .halt
  · have he : s i = s' i := Option.some.inj (by simpa only [step,ite_eq_left hf] using hh')
    simp only [hf,true_and,not_true_eq_false,false_and,or_false]
    rw [he]
  · have hc : State.Consistent (P.rule.updates (rel i) (s i) Fin.elim0) := by
      by_contra hc
      simp only [step,ite_eq_right hf,ite_eq_right hc] at hh'
      contradiction
    have he : (s i).applyUpdates (P.rule.updates (rel i) (s i) Fin.elim0) = s' i := Option.some.inj (by simpa only [step,ite_eq_right hf,ite_eq_left hc] using hh')
    have hv : ∀ l z, (l,z) ∈ P.rule.updates (rel i) (s i) Fin.elim0 → z ∈ d i := by
      intro l z hz
      exact (ht i z ((P.rule.closure_update_subset_trace (rel i) (s i) Fin.elim0 hz).1 (mem_closure_self z))).1
    have hvv := State.value_apply_iff (d i) (s i) _ hc hv ⟨f,fun j => (v j.succ).val⟩ (v 0)
    rw [he] at hvv
    simp only [hf,false_and,not_false_eq_true,true_and,false_or,Fin.cons_zero,Fin.cons_succ,Function.comp_apply]
    exact hvv.symm

end

section

open Classical Hereditary Finset

variable {A B R : Type} [Fintype A] [Fintype B]

attribute [local instance] OAI.CPTSeparation.Operational.Machine.instDecidableEqHF
variable (P : Machine R)

lemma rule_trace_subset (rel : R → A → A → Bool) {h j : ℕ} {s : P.Store (A := A)}
    (hj : j ≤ h) (hs : P.run rel j = some s) :
    P.rule.trace rel s Fin.elim0 ⊆ P.runTrace rel h := by
  intro x hx
  exact mem_union_right _ (mem_biUnion.mpr ⟨j,by simpa using hj,by simpa only [hs] using hx⟩)

lemma active_subset_trace (rel : R → A → A → Bool) {h j : ℕ} {s : P.Store (A := A)}
    (hj : j ≤ h) (hs : P.run rel j = some s) : s.active ⊆ P.runTrace rel h :=
  (P.state_active_subset rel hj hs).trans subset_union_left

lemma runTrace_closed (rel : R → A → A → Bool) (h : ℕ) : Closed (P.runTrace rel h) := by
  apply Closed.union (fun _ hx _ hy => P.runActive_transitive rel h hx hy)
  apply Closed.biUnion
  intro j hj
  cases hs : P.run rel j with
  | none => intro x hx; exact (notMem_empty _ hx).elim
  | some s => exact P.rule.trace_closed rel s Fin.elim0

lemma card_runTrace_le (rel : R → A → A → Bool) (h K : ℕ)
    (hb : ∀ j ≤ h, ∀ s, P.run rel j = some s → s.active.card ≤ K) :
    (P.runTrace rel h).card ≤ (h+1)*(K+P.rule.bound.eval K) := by
  have hc : ((range (h+1)).biUnion (fun j => match P.run rel j with
    | none => ∅ | some s => P.rule.trace rel s Fin.elim0)).card ≤ (h+1)*P.rule.bound.eval K := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _j ∈ range (h+1), P.rule.bound.eval K := by
        apply sum_le_sum
        intro j hj
        cases hs : P.run rel j with
        | none => simp
        | some s =>
          apply P.rule.card_trace_le rel s Fin.elim0 K
          simpa only [Term.potential,Finset.univ_eq_empty,Finset.sum_empty,Nat.add_zero] using hb j (by simpa using hj) s hs
      _ = _ := by simp
  exact (card_union_le _ _).trans ((add_le_add (P.runActive_card_le rel h K hb) hc).trans_eq
    (Nat.mul_add (h+1) K (P.rule.bound.eval K)).symm)

lemma runTrace_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (h : ℕ) :
    P.runTrace rel' h = (P.runTrace rel h).image (lift e) := by
  unfold runTrace
  rw [P.runActive_transport e rel rel' hrel,image_union,biUnion_image]
  congr 1
  apply biUnion_congr rfl
  intro j hj
  rw [P.run_transport e rel rel' hrel]
  cases hs : P.run rel j with
  | none => simp
  | some s =>
    have hv : (fun j : Fin 0 => lift e (Fin.elim0 j : HF A)) = Fin.elim0 := by funext j; exact Fin.elim0 j
    simpa only [Option.map_some,hv] using P.rule.trace_transport e rel rel' hrel s Fin.elim0

end

open Classical Hereditary Counting HFCoding Finset

variable {R ι L : Type} {A : ι → Type} [∀ i, Fintype (A i)]

variable (P : Machine R)

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool)

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

include hd hp ha hmem hset hinput in
lemma uniform_run (ss : ∀ i, ℕ → P.Store (A := A i)) (h K : ℕ)
    (hr : ∀ i j, j ≤ h → P.run (rel i) j = some (ss i j))
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (ht : ∀ i j, j < h → ∀ x ∈ P.rule.trace (rel i) (ss i j) Fin.elim0,
      x ∈ d i ∧ (elements x).card ≤ K) :
    ∀ f, UniformDefinable S m (P.functionArity f+1)
      (fun i v => (v 0).val = (ss i h).value ⟨f,fun j => (v j.succ).val⟩) := by
  induction h with
  | zero =>
    intro f
    have hz := (HFCoding.uniform_ordinal S hmem hset hroom hd hp 0).reindex
      (fun _ : Fin 1 => (0 : Fin (P.functionArity f+1)))
    apply hz.congr
    intro i v
    have he : State.initial = ss i 0 := Option.some.inj (hr i 0 (by omega))
    rw [← he]
    rfl
  | succ h ih =>
    have hs := ih (fun i j hj => hr i j (by omega)) (fun i j hj => ht i j (by omega))
    apply P.uniform_step d S hd hp ha hmem hset rel (fun i => ss i h) hinput hs K (fun i => ss i (h+1))
    · intro i
      have hh := hr i (h+1) (by omega)
      simpa only [run,hr i h (by omega),Option.bind_some] using hh
    · exact hm
    · exact hroom
    · intro i x hx
      exact ht i h (by omega) x hx

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

section

open Classical Hereditary Counting HFCoding Operational Finset

attribute [local instance] OAI.CPTSeparation.Grid.instDecidableEqHF
variable {n : ℕ} (b : Vertex n → Scalar) (P : Operational.Machine Symbol)

lemma opTrace_supported (hn : 1 ≤ n) (h K N : ℕ) (hN : 0 < N)
    (ha : ∀ j ≤ h, ∀ st, P.run (atomInput b).rel j = some st → st.active.card ≤ K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+P.rule.bound.eval K):ℝ) ≤ (N:ℝ)^q) :
    ∀ x ∈ P.runTrace (atomInput b).rel h,
      HereditarilySupported (G := CentralGroup n) ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ x := by
  have hi : ∀ g : BoxGroup n, ∀ x ∈ P.runTrace (atomInput b).rel h,
      g • x ∈ P.runTrace (atomInput b).rel h := by
    intro g x hx
    have ht := P.runTrace_transport (actionIso (b := b) g).toEquiv
      (atomInput b).rel (atomInput b).rel (fun r a b => (actionIso g).rel_eq r a b) h
    have hm : g • x ∈ (P.runTrace (atomInput b).rel h).image (lift (actionIso (b := b) g).toEquiv) :=
      mem_image.mpr ⟨x,hx,rfl⟩
    exact (congrArg (fun t : Finset (HF (Atom b)) => g • x ∈ t) ht).mpr hm

  apply invariant_family_hereditarily_supported hn _ hi (P.runTrace_closed _ h) N hN q hq
  have hc : ((P.runTrace (atomInput b).rel h).card : ℝ) ≤ ((h+1)*(K+P.rule.bound.eval K):ℝ) := by
    exact_mod_cast P.card_runTrace_le (atomInput b).rel h K ha
  exact hc.trans hb

variable {ι : Type} (bs : ι → Vertex n → Scalar) {s m : ℕ}

lemma program_atom_mem (hs : 0 < s) (i : ι) (a : Atom (bs i)) :
    atom a ∈ programDomain bs (s := s) i := by
  apply hereditary_iff.mpr
  constructor
  · refine ⟨fun _ => a,?_⟩
    intro g hg
    rw [smul_atom,hg ⟨0,hs⟩]
  · intro y hy
    have hh : y ∈ (∅ : Finset (HF (Atom (bs i)))) := hy
    exact (notMem_empty _ hh).elim

lemma op_input_uniform (r : Symbol) :
    UniformDefinable (programHF bs (s := s)) m 2
      (fun i v => inputRelation (atomInput (bs i)).rel r (v 0).val (v 1).val) := by
  apply (UniformDefinable.relation (S := programHF bs) (.base (.input r)) 0 1).congr
  intro i v
  change (∃ a b, (v 0).val = atom a ∧ (v 1).val = atom b ∧ AtomRelation (bs i) r a b) ↔ _
  simp only [inputRelation,atomInput,decide_eq_true_eq]

end

open Classical Hereditary Counting HFCoding Operational Finset

end CPTSeparation.Grid

namespace CPTSeparation.PolynomialCost

open Finset

lemma eval_bound (p : Polynomial ℕ) : ∃ c d : ℕ, ∀ K, p.eval K ≤ c*(K+1)^d := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨c,d,hp⟩ := hp
    obtain ⟨e,f,hr⟩ := hr
    refine ⟨c+e,d+f,fun K => ?_⟩
    rw [Polynomial.eval_add]
    have h1 : (K+1)^d ≤ (K+1)^(d+f) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (K+1)^f ≤ (K+1)^(d+f) := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      p.eval K + r.eval K ≤ c*(K+1)^d + e*(K+1)^f := add_le_add (hp K) (hr K)
      _ ≤ c*(K+1)^(d+f)+e*(K+1)^(d+f) := add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
      _ = _ := by ring
  | monomial n a =>
    refine ⟨a,n,fun K => ?_⟩
    rw [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) n)

end CPTSeparation.PolynomialCost

namespace CPTSeparation.Operational.Machine

section

open Classical Hereditary Finset

variable {A R : Type} [Fintype A]

local instance instDecidableEqHF_1_redf58b_2 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable (P : Machine R)

lemma run_none (rel : R → A → A → Bool) {j : ℕ} (hj : P.run rel j = none) :
    ∀ k, j ≤ k → P.run rel k = none := by
  intro k hk
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction l with
  | zero => simpa using hj
  | succ l ih =>
    change (P.run rel (j+l)).bind (P.step rel) = none
    rw [ih]
    rfl

lemma run_prefix_exists (rel : R → A → A → Bool) {h : ℕ} {s : P.Store (A := A)}
    (hh : P.run rel h = some s) {j : ℕ} (hj : j ≤ h) : ∃ t, P.run rel j = some t := by
  cases hs : P.run rel j with
  | some t => exact ⟨t,rfl⟩
  | none => have he := P.run_none rel hs h hj; rw [hh] at he; contradiction

lemma halted_persists (rel : R → A → A → Bool) {h : ℕ} {s : P.Store (A := A)}
    (hh : P.run rel h = some s) (hf : P.flag s .halt) :
    ∀ k, h ≤ k → P.run rel k = some s := by
  intro k hk
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction l with
  | zero => simpa using hh
  | succ l ih =>
    change (P.run rel (h+l)).bind (P.step rel) = some s
    rw [ih]
    simp only [Option.bind_some,step,ite_eq_left hf]

end

open Classical Finset

variable {R : Type} (P : Machine R)

lemma exists_palette : ∃ m : ℕ, 6 ≤ m ∧ ∀ f, P.functionArity f+2+P.rule.width ≤ m := by
  let := P.finiteFunctions
  let total := ∑ f : Control ⊕ P.Functions, P.functionArity f
  refine ⟨total+P.rule.width+8,by omega,?_⟩
  intro f
  have hf : P.functionArity f ≤ total := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ f)
  omega

end CPTSeparation.Operational.Machine

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Traces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A : Type}

attribute [local instance] OAI.CPTSeparation.Hereditary.instDecidableEqHF_3
lemma descendants_mono (t : Finset (HF A)) (k : ℕ) : descendants t k ⊆ descendants t (k+1) := subset_union_left

lemma roots_subset_descendants (t : Finset (HF A)) (k : ℕ) : t ⊆ descendants t k := by
  induction k with
  | zero => exact subset_rfl
  | succ k ih => exact ih.trans (descendants_mono t k)

lemma descendants_subset (t : Finset (HF A)) (k : ℕ) : descendants t k ⊆ familyClosure t := by
  induction k with
  | zero => exact fun _ hx => familyClosure_contains hx
  | succ k ih =>
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact ih hx
    · obtain ⟨y,hy,hxy⟩ := mem_biUnion.mp hx
      exact familyClosure_transitive (ih hy) hxy

lemma descendants_stable (t : Finset (HF A)) (k : ℕ)
    (hs : descendants t (k+1) ⊆ descendants t k) : descendants t k = familyClosure t := by
  apply subset_antisymm (descendants_subset t k)
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
  have h := (mem_closure_iff x y).mp hxy
  have hc : ∀ {a b : HF A}, a ∈ b → b ∈ descendants t k → a ∈ descendants t k := by
    intro a b hab hb
    exact hs (mem_union_right _ (mem_biUnion.mpr ⟨b,hb,hab⟩))
  have aux : ∀ {a b : HF A}, Relation.ReflTransGen (fun x y : HF A => x ∈ y) a b →
      b ∈ descendants t k → a ∈ descendants t k := by
    intro a b hr
    induction hr with
    | refl => exact fun ha => ha
    | tail hab hbc ih => exact fun hb => ih (hc hbc hb)
  exact aux h (roots_subset_descendants t k hy)

lemma descendants_card_lower (t : Finset (HF A)) (k : ℕ)
    (hne : descendants t k ≠ familyClosure t) : k ≤ (descendants t k).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hproper : descendants t k ⊂ descendants t (k+1) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨descendants_mono t k,?_⟩
      intro he
      exact hne (he.symm.trans (descendants_stable t k (he ▸ subset_rfl)))
    have hprev : descendants t k ≠ familyClosure t := by
      intro he
      exact hne (subset_antisymm (descendants_subset t (k+1)) (he ▸ descendants_mono t k))
    have hh := card_lt_card hproper
    have hi := ih hprev
    omega

lemma descendants_eq (t : Finset (HF A)) (K : ℕ) (hb : (familyClosure t).card ≤ K) :
    descendants t K = familyClosure t := by
  by_contra h
  have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨descendants_subset t K,h⟩)
  have hlow := descendants_card_lower t K h
  omega

end CPTSeparation.Hereditary

namespace CPTSeparation.Operational.State

open Classical Hereditary Counting HFCoding Finset

variable {ι L F : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)] [finiteF : Fintype F] {arity : F → ℕ}

attribute [local instance] OAI.CPTSeparation.Operational.State.instDecidableEqHF
variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (s : ∀ i, State F arity (A i))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

omit ι F A arity s in
lemma mem_critical_iff
    {ι : Type}
    {F : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    [Fintype F]
    {arity : F → ℕ}
    (s : (i : ι) → Operational.State F arity (A i)) (i : ι) (x : HF (A i)) : x ∈ (s i).critical ↔
    ∃ f u, (s i).value ⟨f,u⟩ ≠ empty ∧ (x = (s i).value ⟨f,u⟩ ∨ ∃ j, x = u j) := by
  simp only [critical,mem_biUnion,mem_support,mem_insert,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨⟨f,u⟩,h,he | ⟨j,he⟩⟩
    · exact ⟨f,u,h,Or.inl he⟩
    · exact ⟨f,u,h,Or.inr ⟨j,he.symm⟩⟩
  · rintro ⟨f,u,h,he | ⟨j,he⟩⟩
    · exact ⟨⟨f,u⟩,h,Or.inl he⟩
    · exact ⟨⟨f,u⟩,h,Or.inr ⟨j,he.symm⟩⟩

omit ι L F A arity d S m hd hp hmem hset s hstate in
lemma uniform_critical
    {ι : Type}
    {L : Type}
    {F : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    [Fintype F]
    {arity : F → ℕ}
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (s : (i : ι) → Operational.State F arity (A i))
    (hstate : ∀ (f : F),
  Counting.UniformDefinable S m (arity f + 1) fun i v => ↑(v 0) = (s i).value ⟨f, fun j => ↑(v j.succ)⟩) (hm : 6 ≤ m) (har : ∀ f, arity f+2 ≤ m)
    (hs : ∀ i x, x ∈ (s i).critical → x ∈ d i) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ (s i).critical) := by
  have hf (f : F) : UniformDefinable S m 1 (fun i v =>
      ∃ u : Fin (arity f) → Domain (d i), ∃ z : Domain (d i),
        z.val = (s i).value ⟨f,fun j => (u j).val⟩ ∧ z.val ≠ empty ∧
          ((v 0).val = z.val ∨ ∃ j, (v 0).val = (u j).val)) := by
    let a := arity f
    let ix : Fin 1 → Fin ((a+1)+1) := fun _ => Fin.natAdd (a+1) 0
    let iz : Fin ((arity f)+1) → Fin ((a+1)+1) := Fin.castAdd 1
    have hz := (hstate f).reindex iz
    have he := (HFCoding.uniform_ordinal S hmem hset hm hd hp 0).reindex (fun _ : Fin 1 => iz 0)
    have hv := (UniformDefinable.equal (S := S) (m := m) (ix 0) (iz 0))
    have hu := UniformDefinable.exists_finset univ (fun j (_ : j ∈ (univ : Finset (Fin a))) =>
      UniformDefinable.equal (S := S) (m := m) (ix 0) (iz j.succ))
    have hh := (hz.and (he.neg.and (hv.or hu))).exists_vec (by have := har f; change (arity f+1)+1 ≤ m; omega)
    apply hh.congr
    intro i v
    simp only [Finset.mem_univ,true_and] at hh
    constructor
    · rintro ⟨w,hw,hne,hout⟩
      refine ⟨fun j => w j.succ,w 0,?_,?_,?_⟩
      · simpa only [iz,Fin.append_left,Function.comp_apply] using hw
      · simpa only [iz,Fin.append_left,Function.comp_apply] using hne
      · rcases hout with he | ⟨j,_,he⟩
        · exact Or.inl (congrArg Subtype.val (by simpa [ix,iz,Fin.append_left,Fin.append_right] using he))
        · exact Or.inr ⟨j,congrArg Subtype.val (by simpa [ix,iz,Fin.append_left,Fin.append_right] using he)⟩
    · rintro ⟨u,z,hz,hne,hout⟩
      refine ⟨Fin.cons z u,?_,?_,?_⟩
      · simpa only [iz,Fin.append_left,Function.comp_apply,Fin.cons_zero,Fin.cons_succ] using hz
      · simpa only [iz,Fin.append_left,Function.comp_apply,Fin.cons_zero] using hne
      · rcases hout with he | ⟨j,he⟩
        · left; apply Subtype.ext; simpa [ix,iz,Fin.append_left,Fin.append_right] using he
        · right; refine ⟨j,mem_univ _,?_⟩; apply Subtype.ext; simpa [ix,iz,Fin.append_left,Fin.append_right] using he
  apply (UniformDefinable.exists_finset univ (fun f _ => hf f)).congr
  intro i v
  simp only [mem_univ,true_and]
  rw [mem_critical_iff s]
  constructor
  · rintro ⟨f,u,z,hz,hne,hout⟩
    exact ⟨f,fun j => (u j).val,hz ▸ hne,by simpa only [hz] using hout⟩
  · rintro ⟨f,u,hne,hout⟩
    let uu : Fin (arity f) → Domain (d i) := fun j => ⟨u j,hs i _ ((s i).argument_mem_critical hne j)⟩
    refine ⟨f,uu,⟨(s i).value ⟨f,u⟩,hs i _ ((s i).value_mem_critical hne)⟩,rfl,hne,?_⟩
    exact hout

include hd hp ha hmem hset hstate in
lemma uniform_roots (hm : 6 ≤ m) (har : ∀ f, arity f+2 ≤ m)
    (hs : ∀ i x, x ∈ (s i).active → x ∈ d i) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ rootFamily (s i)) := by
  have hc := uniform_critical d S hd hp hmem hset s hstate hm har (fun i x hx =>
    hs i x (familyClosure_contains (mem_union_left _ (mem_union_left _ hx))))
  have hat := Operational.uniform_atoms d S hd ha hmem hset hm
  have he := HFCoding.uniform_ordinal S hmem hset hm hd hp 0
  have ht := HFCoding.uniform_ordinal S hmem hset hm hd hp 1
  apply (((hc.or (hat.or (he.or ht))).or hset.neg)).congr
  intro i v
  simp only [rootFamily,mem_union,mem_insert,Finset.mem_singleton,mem_image,mem_univ,true_and]
  have hh : (¬isSet (v 0).val = true) ↔ ∃ a, atom a = (v 0).val := by
    rcases atom_or_set (v 0).val with ⟨a,he⟩ | he
    · rw [he]; simp only [isSet_atom,Bool.false_eq_true,not_false_eq_true,true_iff]; exact ⟨a,rfl⟩
    · rw [he,isSet_ofFinset]; simp only [not_true_eq_false,false_iff,not_exists]
      intro a ha
      have h := congrArg isSet ha
      simp only [isSet_atom,isSet_ofFinset] at h
      cases h
  exact or_congr Iff.rfl hh

omit ι L A d S m hmem in
lemma uniform_descendants
    {ι : Type}
    {L : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ}
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (t : ∀ i, Finset (HF (A i)))
    (ht : UniformDefinable S m 1 (fun i v => (v 0).val ∈ t i))
    (hs : ∀ i x, x ∈ familyClosure (t i) → x ∈ d i) (hm : 2 ≤ m) (k : ℕ) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ descendants (t i) k) := by
  induction k with
  | zero => exact ht
  | succ k ih =>
    have hh := ((ih.reindex (![0] : Fin 1 → Fin 2)).and
      (hmem.reindex (![1,0] : Fin 2 → Fin 2))).ex (by omega)
    apply (ih.or hh).congr
    intro i v
    change ((v 0).val ∈ descendants (t i) k ∨
      ∃ y : Domain (d i), y.val ∈ descendants (t i) k ∧ (v 0).val ∈ y.val) ↔ _
    simp only [descendants,mem_union,mem_biUnion]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨y,hy,hxy⟩; exact ⟨y.val,hy,hxy⟩
    · rintro ⟨y,hy,hxy⟩; exact ⟨⟨y,hs i y (descendants_subset _ _ hy)⟩,hy,hxy⟩

include hd hp ha hmem hset hstate in
lemma uniform_active (hm : 6 ≤ m) (har : ∀ f, arity f+2 ≤ m)
    (hs : ∀ i x, x ∈ (s i).active → x ∈ d i) (K : ℕ)
    (hK : ∀ i, (s i).active.card ≤ K) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ (s i).active) := by
  have hroots := uniform_roots d S hd hp ha hmem hset s hstate hm har hs
  have hh := uniform_descendants d S hmem (fun i => rootFamily (s i)) hroots hs (by omega) K
  apply hh.congr
  intro i v
  have hi : (familyClosure (rootFamily (s i))).card ≤ K := hK i
  rw [descendants_eq (rootFamily (s i)) K hi]
  rfl

include hd hp ha hmem hset hstate in
lemma uniform_active_card (hm : 6 ≤ m) (har : ∀ f, arity f+2 ≤ m)
    (hs : ∀ i x, x ∈ (s i).active → x ∈ d i) (K : ℕ)
    (hK : ∀ i, (s i).active.card ≤ K) (k : ℕ) :
    UniformDefinable S m 0 (fun i _ => (s i).active.card = k) := by
  have hh := (uniform_active d S hd hp ha hmem hset s hstate hm har hs K hK).exact (by omega) k
  apply hh.congr
  intro i v
  change Nonempty ({x : Domain (d i) // x.val ∈ (s i).active} ≃ Fin k) ↔ _
  let e : {x : Domain (d i) // x.val ∈ (s i).active} ≃ {x // x ∈ (s i).active} :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      invFun := fun x => ⟨⟨x.val,hs i x.val x.property⟩,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨f⟩
    have h := Fintype.card_congr (e.symm.trans f)
    simpa using h
  · intro h
    exact ⟨e.trans ((Fintype.equivFin _).trans (finCongr (by simpa using h)))⟩

end CPTSeparation.Operational.State

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

variable {ι R L F : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)] [Fintype F] {arity : F → ℕ}

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_8
variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

omit ι L F A arity d S m in
lemma uniform_consistency
    {ι : Type}
    {L : Type}
    {F : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    [Fintype F]
    {arity : F → ℕ}
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ} (u : ∀ i, Finset (Update F arity (A i)))
    (hu : ∀ f, UniformDefinable S m (arity f+1) (fun i v =>
      (⟨f,fun j => (v j.succ).val⟩,(v 0).val) ∈ u i))
    (hd : ∀ i l z, (l,z) ∈ u i → z ∈ d i ∧ ∀ j, l.2 j ∈ d i)
    (hm : ∀ f, arity f+2 ≤ m) :
    UniformDefinable S m 0 (fun i _ => State.Consistent (u i)) := by
  have hf (f : F) : UniformDefinable S m 0 (fun i _ =>
      ∃ w : Fin (arity f+2) → Domain (d i),
        (⟨f,fun j => (w j.succ.succ).val⟩,(w 0).val) ∈ u i ∧
        (⟨f,fun j => (w j.succ.succ).val⟩,(w 1).val) ∈ u i ∧ (w 0).val ≠ (w 1).val) := by
    have h0 := (hu f).reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (arity f+1) → Fin (arity f+2))
    have h1 := (hu f).reindex (Fin.cons 1 (fun j => j.succ.succ) : Fin (arity f+1) → Fin (arity f+2))
    have he := (UniformDefinable.equal (S := S) (m := m) (0 : Fin (arity f+2)) 1).neg
    have hh := (h0.and (h1.and he)).exists_vec (n := 0) (hm f)
    apply hh.congr
    intro i v
    apply exists_congr
    intro w
    have happ : Fin.append w v = w := Fin.append_right_nil w v rfl
    simp only [happ,Function.comp_apply,Fin.cons_zero,Fin.cons_succ]
    exact and_congr Iff.rfl (and_congr Iff.rfl (not_congr Subtype.val_injective.eq_iff.symm))
  apply (UniformDefinable.exists_finset univ (fun f _ => hf f)).neg.congr
  intro i v
  simp only [mem_univ,true_and]
  constructor
  · intro h l x y hx hy
    by_contra hne
    let w : Fin (arity l.1+2) → Domain (d i) := Fin.cons ⟨x,(hd i l x hx).1⟩
      (Fin.cons ⟨y,(hd i l y hy).1⟩ (fun j => ⟨l.2 j,(hd i l x hx).2 j⟩))
    exact h ⟨l.1,w,hx,hy,hne⟩
  · intro hc
    rintro ⟨f,w,hx,hy,hne⟩
    exact hne (hc _ _ _ hx hy)

end CPTSeparation.Operational

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Finset

local instance instDecidableEqHF_2_redf58b_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable {n m M N : ℕ} (P : Operational.Machine Symbol) (vstar : Vertex n)

lemma op_observations_agree (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (ss : ∀ i : Bool, ℕ → P.Store (A := Atom (twoCharges vstar i)))
    (hr : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j))
    (ha : ∀ i j, j ≤ h → (ss i j).active.card ≤ K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+P.rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (∀ c, P.flag (ss false h) c ↔ P.flag (ss true h) c) ∧
    (State.Consistent (P.rule.updates (atomInput (twoCharges vstar false)).rel (ss false h) Fin.elim0) ↔
      State.Consistent (P.rule.updates (atomInput (twoCharges vstar true)).rel (ss true h) Fin.elim0)) ∧
    (ss false h).active.card = (ss true h).active.card := by
  let s := ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊
  let D := programDomain (twoCharges vstar) (s := s)
  let C := programHF (twoCharges vstar) (s := s)
  have hbound (i : Bool) : ∀ j ≤ h, ∀ st, P.run (atomInput (twoCharges vstar i)).rel j = some st → st.active.card ≤ K := by
    intro j hj st hh
    have he : st = ss i j := Option.some.inj (hh.symm.trans (hr i j hj))
    exact he ▸ ha i j hj
  have hfamily (i : Bool) : ∀ x ∈ P.runTrace (atomInput (twoCharges vstar i)).rel h, x ∈ D i :=
    opTrace_supported (twoCharges vstar i) P hn h K N hN (hbound i) q hq hb
  have ht : ∀ i j, j ≤ h → ∀ x ∈ P.rule.trace (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0,
      x ∈ D i ∧ (elements x).card ≤ (h+1)*(K+P.rule.bound.eval K) := by
    intro i j hj x hx
    have hx' := P.rule_trace_subset (atomInput (twoCharges vstar i)).rel hj (hr i j (by omega)) hx
    refine ⟨hfamily i x hx',?_⟩
    have he : elements x ⊆ P.runTrace (atomInput (twoCharges vstar i)).rel h := by
      intro y hy
      exact P.runTrace_closed _ h x hx' y hy
    exact (card_le_card he).trans (P.card_runTrace_le _ h K (hbound i))
  let := P.finiteFunctions
  have htrans : ∀ Q : Bool → Prop, UniformDefinable C m 0 (fun i _ => Q i) → (Q false ↔ Q true) := by
    intro Q hQ
    obtain ⟨φ,hφ,hφsem⟩ := hQ (Fin.elim0 : Fin 0 → Fin m)
    have hfree : φ.free = ∅ := subset_empty.mp (by simpa using hφ)
    let v : Fin m → Domain (D false) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
    let w : Fin m → Domain (D true) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
    let := atom_nonempty hn (0 : Vertex n → Scalar)
    let := atom_nonempty hn (Pi.single vstar 1)
    exact (hφsem false v).symm.trans ((grid_hf_transfer hn hs (by omega) vstar
      hwidth hhom hgiant φ hfree v w).trans (hφsem true w))
  have hstate := P.uniform_run D C (program_domain_transitive (twoCharges vstar))
    (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
    (fun i => (atomInput (twoCharges vstar i)).rel) (op_input_uniform (twoCharges vstar))
    ss h ((h+1)*(K+P.rule.bound.eval K)) hr hm hroom (fun i j hj => ht i j (by omega))
  have hac : ∀ i x, x ∈ (ss i h).active → x ∈ D i := by
    intro i x hx
    exact hfamily i x (P.active_subset_trace _ (le_refl h) (hr i h (le_refl h)) hx)
  have har : ∀ f, P.functionArity f+2 ≤ m := fun f => by have := hm f; omega
  refine ⟨?_,?_,?_⟩
  · intro c
    apply htrans (fun i => P.flag (ss i h) c)
    exact P.uniform_flag D C (program_domain_transitive (twoCharges vstar))
      (program_pure (twoCharges vstar) hn) (program_mem_uniform (twoCharges vstar))
      (program_set_uniform (twoCharges vstar)) (fun i => ss i h) hstate hroom c
  · apply htrans (fun i => State.Consistent (P.rule.updates (atomInput (twoCharges vstar i)).rel (ss i h) Fin.elim0))
    apply uniform_consistency D C
      (fun i => P.rule.updates (atomInput (twoCharges vstar i)).rel (ss i h) Fin.elim0)
    · intro f
      exact uniform_updates D C (program_domain_transitive (twoCharges vstar))
        (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
        (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
        (fun i => (atomInput (twoCharges vstar i)).rel) (fun i => ss i h)
        (op_input_uniform (twoCharges vstar)) hstate ((h+1)*(K+P.rule.bound.eval K)) P.rule f
        (by have := hm f; omega) (fun i x hx => ht i h (le_refl h) x hx)
    · intro i l z hz
      have hh := P.rule.closure_update_subset_trace (atomInput (twoCharges vstar i)).rel (ss i h) Fin.elim0 hz
      exact ⟨(ht i h (le_refl h) z (hh.1 (mem_closure_self z))).1,
        fun j => (ht i h (le_refl h) (l.2 j) (hh.2 j (mem_closure_self _))).1⟩
    · exact har
  · have hc := State.uniform_active_card D C (program_domain_transitive (twoCharges vstar))
      (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
      (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
      (fun i => ss i h) hstate hroom har hac K (fun i => ha i h (le_refl h)) (ss false h).active.card
    exact ((htrans _ hc).mp rfl).symm

end CPTSeparation.Grid

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

variable {A R F : Type} [Fintype A] {arity : F → ℕ}

namespace State

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_9
lemma active_apply_subset (rel : R → A → A → Bool) (s : State F arity A)
    (r : Rule R F arity 0) :
    (s.applyUpdates (r.updates rel s Fin.elim0)).active ⊆ s.active ∪ r.trace rel s Fin.elim0 := by
  let u := r.updates rel s Fin.elim0
  have hc : Closed (s.active ∪ r.trace rel s Fin.elim0) :=
    Closed.union (fun x hx y hy => s.active_transitive hx hy) (r.trace_closed rel s Fin.elim0)
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
  apply closure_subset_of_transitive hc (x := y) ?_ hxy
  rcases mem_union.mp hy with hy | hy
  · rcases mem_union.mp hy with hy | hy
    · obtain ⟨l,hl,hy⟩ := mem_biUnion.mp hy
      have hn := (mem_support (s.applyUpdates u) l).mp hl
      by_cases hu : ∃ z, (l,z) ∈ u
      · have hv : (l,(s.applyUpdates u).value l) ∈ u := by
          change (l,s.updatedValue u l) ∈ u
          simp only [updatedValue,dite_eq_left hu]
          exact hu.choose_spec
        have ht := r.closure_update_subset_trace rel s Fin.elim0 hv
        rcases mem_insert.mp hy with he | hy
        · subst y; exact mem_union_right _ (ht.1 (mem_closure_self _))
        · obtain ⟨j,hj,he⟩ := mem_image.mp hy
          subst y
          exact mem_union_right _ (ht.2 j (mem_closure_self _))
      · have he : (s.applyUpdates u).value l = s.value l := s.updatedValue_default u hu
        have hn' : s.value l ≠ empty := he ▸ hn
        rcases mem_insert.mp hy with hy | hy
        · rw [hy,he]
          exact mem_union_left _ (s.closure_value_subset_active l (mem_closure_self _))
        · obtain ⟨j,hj,heq⟩ := mem_image.mp hy
          subst y
          exact mem_union_left _ (familyClosure_contains (mem_union_left _ (mem_union_left _ (s.argument_mem_critical hn' j))))
    · exact mem_union_left _ (familyClosure_contains (mem_union_left _ (mem_union_right _ hy)))
  · exact mem_union_left _ (familyClosure_contains (mem_union_right _ hy))

lemma initial_active_card : (initial : State F arity A).active.card ≤ Fintype.card A+3 := by
  let t : Finset (HF A) := {allAtoms,empty,truth} ∪ univ.image atom
  have hc : Closed t := by
    intro x hx y hy
    rcases mem_union.mp hx with hx | hx
    · simp only [mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_union_right _ (by simpa only [allAtoms,mem_ofFinset] using hy)
      · obtain ⟨k,hk,he⟩ := (mem_ordinal y 0).mp hy
        omega
      · obtain ⟨k,hk,he⟩ := (mem_ordinal y 1).mp hy
        have hk0 : k = 0 := by omega
        rw [he,hk0]
        exact mem_union_left _ (by simp)
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      have hh : y ∈ (∅ : Finset (HF A)) := hy
      exact (notMem_empty _ hh).elim
  have he : (initial : State F arity A).critical = ∅ := by
    ext x
    simp [critical,mem_support,initial]
  have hsub : (initial : State F arity A).active ⊆ t := by
    intro x hx
    change x ∈ familyClosure _ at hx
    rw [he,empty_union] at hx
    obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
    exact closure_subset_of_transitive hc hy hxy
  apply (card_le_card hsub).trans
  have h3 : ({allAtoms,empty,truth} : Finset (HF A)).card ≤ 3 := by
    have h1 := card_insert_le (allAtoms : HF A) ({empty,truth} : Finset (HF A))
    have h2 := card_insert_le (empty : HF A) ({truth} : Finset (HF A))
    simp only [card_singleton] at h2
    omega
  have hi : (univ.image (atom : A → HF A)).card ≤ Fintype.card A := card_image_le.trans (by simp)
  exact (card_union_le _ _).trans (by omega)

end State

namespace Machine

attribute [local instance] OAI.CPTSeparation.Operational.instDecidableEqHF_9
variable (P : Machine R)

lemma step_exists_iff (rel : R → A → A → Bool) (s : P.Store (A := A)) :
    (∃ t, P.step rel s = some t) ↔ P.flag s .halt ∨ State.Consistent (P.rule.updates rel s Fin.elim0) := by
  unfold step
  split
  · simp_all
  · dsimp only
    split <;> simp_all

lemma active_step_bound (rel : R → A → A → Bool) {s t : P.Store (A := A)}
    (he : P.step rel s = some t) (K : ℕ) (hK : s.active.card ≤ K) :
    t.active.card ≤ K+P.rule.bound.eval K := by
  unfold step at he
  split at he
  · have ht := Option.some.inj he
    subst t
    exact hK.trans (Nat.le_add_right _ _)
  · dsimp only at he
    split at he
    · have ht := Option.some.inj he
      subst t
      apply (card_le_card (State.active_apply_subset rel s P.rule)).trans
      apply (card_union_le _ _).trans
      apply add_le_add hK
      apply P.rule.card_trace_le rel s Fin.elim0 K
      simpa only [Term.potential,univ_eq_empty,Finset.sum_empty,Nat.add_zero] using hK
    · contradiction

end Machine

end CPTSeparation.Operational

namespace CPTSeparation.Operational.Machine

open Classical Hereditary Counting HFCoding Finset

variable {R : Type} {A : Bool → Type} [∀ i, Fintype (A i)]

local instance instDecidableEqHF_2_redf58b_2 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable (P : Machine R) (rel : ∀ i, R → A i → A i → Bool)

lemma bounded_accept_transfer (time space K : ℕ) (hS : space ≤ K)
    (hnext : space+P.rule.bound.eval space ≤ K)
    (hroot : ∀ i, (State.initial : P.Store (A := A i)).active.card ≤ K)
    (hobs : ∀ h, h ≤ time → P.PrefixBound rel h K → P.ObservationsAt rel h)
    (i j : Bool) (hacc : P.boundedAccepts (rel i) time space) :
    P.boundedAccepts (rel j) time space := by
  by_cases hij : i = j
  · subst j; exact hacc
  have hcases (b : Bool) : b = i ∨ b = j := by cases i <;> cases j <;> cases b <;> simp_all
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := hacc
  have hsource (k : ℕ) (hk : k ≤ h) : ∃ u, P.run (rel i) k = some u ∧ u.active.card ≤ space := by
    obtain ⟨u,hu⟩ := P.run_prefix_exists (rel i) hhr hk
    exact ⟨u,hu,hbudget k hk u hu⟩
  have hext : ∀ k, k ≤ h → ∃ t, P.run (rel j) k = some t ∧
      ∀ l, l ≤ k → ∀ u, P.run (rel j) l = some u → u.active.card ≤ space := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hp : P.PrefixBound rel 0 K := by
        intro b l hl
        have he : l = 0 := by omega
        subst l
        exact ⟨State.initial,rfl,hroot b⟩
      have ho := hobs 0 (by omega) hp i j State.initial State.initial rfl rfl
      have hb := hbudget 0 (by omega) State.initial rfl
      refine ⟨State.initial,rfl,?_⟩
      intro l hl u hu
      have he : l = 0 := by omega
      subst l
      have hh : State.initial = u := Option.some.inj hu
      subst u
      omega
    | succ k ih =>
      intro hkh
      obtain ⟨t,hrt,hbt⟩ := ih (by omega)
      obtain ⟨s,hrs,hbs⟩ := hsource k (by omega)
      obtain ⟨s1,hrs1,hbs1⟩ := hsource (k+1) hkh
      have hp : P.PrefixBound rel k K := by
        intro b l hl
        rcases hcases b with rfl | rfl
        · obtain ⟨u,hu,hbu⟩ := hsource l (by omega)
          exact ⟨u,hu,hbu.trans hS⟩
        · obtain ⟨u,hu⟩ := P.run_prefix_exists _ hrt hl
          exact ⟨u,hu,(hbt l hl u hu).trans hS⟩
      have ho := hobs k (by omega) hp i j s t hrs hrt
      have hstep : P.step (rel i) s = some s1 := by
        simpa only [run,hrs,Option.bind_some] using hrs1
      have hsuc : ∃ t1, P.step (rel j) t = some t1 := by
        apply (P.step_exists_iff (rel j) t).mpr
        rcases (P.step_exists_iff (rel i) s).mp ⟨s1,hstep⟩ with hf | hc
        · exact Or.inl ((ho.1 .halt).mp hf)
        · exact Or.inr (ho.2.1.mp hc)
      obtain ⟨t1,ht1⟩ := hsuc
      have hrt1 : P.run (rel j) (k+1) = some t1 := by
        simp only [run,hrt,Option.bind_some,ht1]
      have hbt1 : t1.active.card ≤ K :=
        (P.active_step_bound (rel j) ht1 space (hbt k (le_refl k) t hrt)).trans hnext
      have hp1 : P.PrefixBound rel (k+1) K := by
        intro b l hl
        rcases hcases b with rfl | rfl
        · obtain ⟨u,hu,hbu⟩ := hsource l (by omega)
          exact ⟨u,hu,hbu.trans hS⟩
        · by_cases he : l = k+1
          · subst l; exact ⟨t1,hrt1,hbt1⟩
          · obtain ⟨u,hu⟩ := P.run_prefix_exists _ hrt (j := l) (by omega)
            exact ⟨u,hu,(hbt l (by omega) u hu).trans hS⟩
      have ho1 := hobs (k+1) (by omega) hp1 i j s1 t1 hrs1 hrt1
      have ht1small : t1.active.card ≤ space := by rw [← ho1.2.2]; exact hbs1
      refine ⟨t1,hrt1,?_⟩
      intro l hl u hu
      by_cases he : l = k+1
      · subst l
        have hh : u = t1 := Option.some.inj (hu.symm.trans hrt1)
        exact hh ▸ ht1small
      · exact hbt l (by omega) u hu
  obtain ⟨t,hrt,hbt⟩ := hext h (le_refl h)
  have hp : P.PrefixBound rel h K := by
    intro b l hl
    rcases hcases b with rfl | rfl
    · obtain ⟨u,hu,hbu⟩ := hsource l hl
      exact ⟨u,hu,hbu.trans hS⟩
    · obtain ⟨u,hu⟩ := P.run_prefix_exists _ hrt hl
      exact ⟨u,hu,(hbt l hl u hu).trans hS⟩
  have ho := hobs h hht hp i j st t hhr hrt
  exact ⟨h,t,hht,hrt,(ho.1 .halt).mp hhf,(ho.1 .accept).mp hha,hbt⟩

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Finset

local instance instDecidableEqHF_3_redf58b_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable {n m M N : ℕ} (P : Operational.Machine Symbol) (vstar : Vertex n)

lemma op_prefix_observations (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (hr : P.PrefixBound (fun i => (atomInput (twoCharges vstar i)).rel) h K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+P.rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    P.ObservationsAt (fun i => (atomInput (twoCharges vstar i)).rel) h := by
  let ss := fun i j => (P.run (atomInput (twoCharges vstar i)).rel j).getD State.initial
  have hrs : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j) := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simp only [ss,hst,Option.getD_some]
  have hact : ∀ i j, j ≤ h → (ss i j).active.card ≤ K := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simpa only [ss,hst,Option.getD_some] using hb
  have ho := op_observations_agree P vstar hn h K hN ss hrs hact q hq hb hm hroom hs hwidth hhom hgiant
  intro i j st tt hst htt
  have he : st = ss i h := Option.some.inj (hst.symm.trans (hrs i h (le_refl h)))
  have he' : tt = ss j h := Option.some.inj (htt.symm.trans (hrs j h (le_refl h)))
  subst st; subst tt
  cases i <;> cases j
  · exact ⟨fun _ => Iff.rfl,Iff.rfl,rfl⟩
  · exact ho
  · exact ⟨fun c => (ho.1 c).symm,ho.2.1.symm,ho.2.2.symm⟩
  · exact ⟨fun _ => Iff.rfl,Iff.rfl,rfl⟩

end CPTSeparation.Grid

namespace CPTSeparation.PolynomialCost

lemma eval_mono (p : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using add_le_add hp hq
  | monomial n c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

end CPTSeparation.PolynomialCost

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Quantitative Finset

local instance instDecidableEqHF_4_redf58b_2 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable {n : ℕ}

lemma atom_card_independent (hn : 1 ≤ n) (b b' : Vertex n → Scalar) :
    Fintype.card (Atom b) = Fintype.card (Atom b') := by
  have hv (v : Vertex n) : ∃ t : Edge n → Scalar, boundary t v = b' v - b v := by
    obtain ⟨e,he⟩ := exists_head_or_tail hn v
    rcases he with he | he
    · refine ⟨Pi.single e (b' v-b v),?_⟩
      rw [boundary_single]
      subst v
      simp [head_ne_tail]
    · refine ⟨Pi.single e (-(b' v-b v)),?_⟩
      rw [boundary_single]
      subst v
      simp [Ne.symm (head_ne_tail e)]
  choose tv htv using hv
  exact Fintype.card_congr (blockShiftEquiv (fun _ _ => 0) tv htv)

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.LowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Operational.Machine

open Classical Hereditary Counting HFCoding Finset

variable {R ι L : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)]

local instance instDecidableEqHF_3_redf58b_2 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable (P : Machine R)

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool)

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

include hd hp ha hmem hset hinput in
lemma uniform_runActive (ss : ∀ i, ℕ → P.Store (A := A i)) (h K J : ℕ)
    (hr : ∀ i j, j ≤ h → P.run (rel i) j = some (ss i j))
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (ht : ∀ i j, j < h → ∀ x ∈ P.rule.trace (rel i) (ss i j) Fin.elim0,
      x ∈ d i ∧ (elements x).card ≤ J)
    (hs : ∀ i j, j ≤ h → ∀ x ∈ (ss i j).active, x ∈ d i)
    (hK : ∀ i j, j ≤ h → (ss i j).active.card ≤ K) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ P.runActive (rel i) h) := by
  let := P.finiteFunctions
  have hstage (j : ℕ) (hj : j ∈ range (h+1)) :
      UniformDefinable S m 1 (fun i v => (v 0).val ∈ (ss i j).active) := by
    have hjh : j ≤ h := by simpa using hj
    have hst := P.uniform_run d S hd hp ha hmem hset rel hinput ss j J
      (fun i k hk => hr i k (by omega)) hm hroom (fun i k hk => ht i k (by omega))
    exact State.uniform_active d S hd hp ha hmem hset (fun i => ss i j) hst hroom
      (fun f => by have := hm f; omega) (fun i => hs i j hjh) K (fun i => hK i j hjh)
  apply (UniformDefinable.exists_finset (range (h+1)) hstage).congr
  intro i v
  simp only [runActive,mem_biUnion]
  constructor
  · rintro ⟨j,hj,hv⟩
    exact ⟨j,hj,by simpa only [hr i j (by simpa using hj)] using hv⟩
  · rintro ⟨j,hj,hv⟩
    exact ⟨j,hj,by simpa only [hr i j (by simpa using hj)] using hv⟩

omit ι L A d S m in
lemma uniform_finite_family_card
    {ι : Type}
    {L : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ} (t : ∀ i, Finset (HF (A i)))
    (ht : UniformDefinable S m 1 (fun i v => (v 0).val ∈ t i))
    (hs : ∀ i x, x ∈ t i → x ∈ d i) (hm : 1 ≤ m) (k : ℕ) :
    UniformDefinable S m 0 (fun i _ => (t i).card = k) := by
  apply (ht.exact (by omega) k).congr
  intro i v
  change Nonempty ({x : Domain (d i) // x.val ∈ t i} ≃ Fin k) ↔ _
  let e : {x : Domain (d i) // x.val ∈ t i} ≃ {x // x ∈ t i} :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      invFun := fun x => ⟨⟨x.val,hs i x.val x.property⟩,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨f⟩
    have h := Fintype.card_congr (e.symm.trans f)
    simpa using h
  · intro h
    exact ⟨e.trans ((Fintype.equivFin _).trans (finCongr (by simpa using h)))⟩

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Operational.Machine

section

open Classical Hereditary Finset

variable {A R : Type} [Fintype A]

local instance instDecidableEqHF_4_redf58b_3 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable (P : Machine R)

lemma bounded_active_all (rel : R → A → A → Bool) {time space : ℕ}
    (ha : P.boundedAccepts rel time space) :
    ∀ j, ∃ st, P.run rel j = some st ∧ st.active.card ≤ space := by
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := ha
  intro j
  by_cases hj : j ≤ h
  · obtain ⟨t,ht⟩ := P.run_prefix_exists rel hhr hj
    exact ⟨t,ht,hbudget j hj t ht⟩
  · exact ⟨st,P.halted_persists rel hhr hhf j (by omega),hbudget h (le_refl h) st hhr⟩

end

end CPTSeparation.Operational.Machine

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.FullLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.FullCPT

noncomputable section

open Classical Hereditary Finset

open Operational (State Control Location Update)

attribute [local instance] CPTSeparation.FullCPT.instDecidableEqHF

variable {A R F : Type} {arity : F → ℕ}

lemma agrees_bind {k : ℕ} {slots : ℕ → Option (Fin k)} {env : ℕ → HF A}
    {values : Fin k → HF A} (h : Agrees slots env values) (name : ℕ) (x : HF A) :
    Agrees (bindSlots slots name) (Function.update env name x) (Fin.cons x values) := by
  intro y
  by_cases he : y = name
  · subst y
    simp [bindSlots]
  · rw [Function.update_of_ne he]
    rw [h y]
    simp only [bindSlots, ite_eq_right he]
    cases slots y <;> rfl

namespace Term

theorem eval_compile [Fintype A] (rel : R → A → A → Bool) (s : State F arity A)
    (t : Term R F arity) {k : ℕ} (slots : ℕ → Option (Fin k))
    (env : ℕ → HF A) (values : Fin k → HF A) (h : Agrees slots env values) :
    (t.compile slots).eval rel s values = t.eval rel s env := by
  induction t generalizing k env with
  | var n =>
      simp only [compile, eval]
      rw [h n]
      cases slots n <;> rfl
  | ordinal n => rfl
  | atoms => rfl
  | app f args ih =>
      simp only [compile, Operational.Term.eval, eval]
      congr 2
      funext i
      exact ih i slots env values h
  | pair a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | union a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | unique a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | card a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | equal a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | member a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | isAtom a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | input r a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | not a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | and a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | or a b iha ihb =>
      simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
      simp only [ne_eq, Operational.boolean_truth, not_and_or, not_not]
  | conditional c a b ihc iha ihb =>
      simp only [compile, Operational.Term.eval, eval, ihc slots env values h, iha slots env values h, ihb slots env values h]
  | comprehend n bound guard body ihbound ihguard ihbody =>
      simp only [compile, Operational.Term.eval, eval, ihbound slots env values h]
      have hg : (fun x => Operational.Term.eval rel s (guard.compile (bindSlots slots n)) (Fin.cons x values)) =
          (fun x => eval rel s guard (Function.update env n x)) := by
        funext x
        exact ihguard _ _ _ (agrees_bind h n x)
      have hb : (fun x => Operational.Term.eval rel s (body.compile (bindSlots slots n)) (Fin.cons x values)) =
          (fun x => eval rel s body (Function.update env n x)) := by
        funext x
        exact ihbody _ _ _ (agrees_bind h n x)
      have hg' (x : HF A) := congrFun hg x
      simp only [hg', hb]

end Term

namespace Rule

theorem updates_compile [Fintype A] (rel : R → A → A → Bool) (s : State F arity A)
    (r : Rule R F arity) {k : ℕ} (slots : ℕ → Option (Fin k))
    (env : ℕ → HF A) (values : Fin k → HF A) (h : Agrees slots env values) :
    (r.compile slots).updates rel s values = r.updates rel s env := by
  induction r generalizing k env with
  | skip => rfl
  | update f args v =>
      simp only [compile, Operational.Rule.updates, updates, Term.eval_compile rel s _ _ _ _ h]
  | parallel a b iha ihb =>
      simp only [compile, Operational.Rule.updates, updates, iha slots env values h, ihb slots env values h]
  | conditional c a b iha ihb =>
      simp only [compile, Operational.Rule.updates, updates, Term.eval_compile rel s _ _ _ _ h,
        iha slots env values h, ihb slots env values h]
  | «forall» n bound body ih =>
      simp only [compile, Operational.Rule.updates, updates, Term.eval_compile rel s _ _ _ _ h]
      congr 1
      funext x
      exact ih _ _ _ (agrees_bind h n x)
  | letValue n value body ih =>
      simp only [compile, Operational.Rule.updates, updates, Term.eval_compile rel s _ _ _ _ h]
      exact ih _ _ _ (agrees_bind h n (value.eval rel s env))

end Rule

namespace Program

variable (P : Program R) [finiteA : Fintype A]

lemma step_compile (rel : R → A → A → Bool) (s : P.Store (A := A)) :
    P.compile.step rel s = P.step rel s := by
  change (if P.flag s .halt then some s else
    let u := (P.body.compile (fun _ => none)).updates rel s Fin.elim0
    if State.Consistent u then some (s.applyUpdates u) else none) = _
  have hu := Rule.updates_compile rel s P.body (fun _ => none)
    (fun _ => Operational.empty) Fin.elim0 (fun _ => rfl)
  dsimp only
  rw [hu]
  rfl

lemma run_compile (rel : R → A → A → Bool) (h : ℕ) :
    P.compile.run rel h = P.run rel h := by
  induction h with
  | zero => rfl
  | succ h ih =>
      simp only [Operational.Machine.run, run, ih]
      congr 1
      funext s
      exact P.step_compile rel s

lemma active_compile (rel : R → A → A → Bool) (h : ℕ) :
    P.compile.runActive rel h = P.active rel h := by
  unfold Operational.Machine.runActive active
  simp only [P.run_compile]
  congr 1
  funext j
  cases P.run rel j <;> simp ; rfl

end Program

end

end CPTSeparation.FullCPT

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Observers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Operational.Machine

open Classical Hereditary Counting HFCoding Finset

variable {A R : Type} [Fintype A]

attribute [local instance] OAI.CPTSeparation.Operational.Machine.instDecidableEqHF_5
variable (P : Machine R) (O : P.Observer)

lemma observer_trace_subset (rel : R → A → A → Bool) (s : P.Store (A := A)) :
 O.trace rel s Fin.elim0 ⊆ (P.instrument O).rule.trace rel s Fin.elim0 := by
 intro x hx
 exact mem_union_right _ (mem_union_left _ hx)

lemma original_trace_subset (rel : R → A → A → Bool) (s : P.Store (A := A)) :
 P.rule.trace rel s Fin.elim0 ⊆ (P.instrument O).rule.trace rel s Fin.elim0 := subset_union_left

lemma observed_subset_trace (rel : R → A → A → Bool) (h : ℕ) :
 P.observed O rel h ⊆ (P.instrument O).runTrace rel h := by
 intro x hx
 rcases mem_union.mp hx with hx | hx
 · exact mem_union_left _ (by simpa only [instrument_active] using hx)
 · obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
   cases hr : P.run rel j with
   | none => simp only [hr,notMem_empty] at hx
   | some s =>
     simp only [hr] at hx
     obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
     have hy' := Term.closure_eval_subset_trace rel s O Fin.elim0
       (elements_subset_closure _ hy)
     have hy'' := (P.instrument O).rule_trace_subset rel (h := h) (j := j) (s := s)
       (by have := mem_range.mp hj; omega) (by simpa only [instrument_run] using hr)
       (P.observer_trace_subset O rel s hy')
     exact closure_subset_of_transitive ((P.instrument O).runTrace_closed rel h) hy'' hxy

lemma active_subset_observed (rel : R → A → A → Bool) {h j : ℕ} {s : P.Store (A := A)}
 (hj : j ≤ h) (hs : P.run rel j = some s) : s.active ⊆ P.observed O rel h :=
 (P.state_active_subset rel hj hs).trans subset_union_left

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Operational.Term

open Classical Hereditary Counting HFCoding Finset

variable {ι R F L : Type} {arity : F → ℕ} {A : ι → Type} [∀ i, Fintype (A i)]

local instance instDecidableEqHF_2_redf58b_3 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool) (s : ∀ i, State F arity (A i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
 (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

include hd hp ha hmem hset hinput hstate in
lemma uniform_root_members (K : ℕ) (O : Term R F arity 0) (hO : O.width ≤ m) (hm : 2 ≤ m)
 (ht : ∀ i x, x ∈ O.trace (rel i) (s i) Fin.elim0 → x ∈ d i ∧ (elements x).card ≤ K) :
 UniformDefinable S m 1 (fun i v => (v 0).val ∈ elements (O.eval (rel i) (s i) Fin.elim0)) := by
 have hg := uniform_graph d S hd hp ha hmem hset rel s hinput hstate K O hO
 have hvalue : UniformDefinable S m 1
     (fun i v => (v 0).val = O.eval (rel i) (s i) Fin.elim0) := by
   apply hg.congr
   intro i v
   have hv : (fun j : Fin 0 => (Fin.tail v j).val) = Fin.elim0 := Subsingleton.elim _ _
   constructor
   · intro h
     simpa only [hv] using graph_sound (d i) K (rel i) (s i) (hd i) O (v 0) (Fin.tail v) h
   · intro he
     obtain ⟨y,hy,hey⟩ := graph_complete (d i) K (rel i) (s i) (hd i) O (Fin.tail v)
       (by simpa only [hv] using ht i)
     rw [hv] at hey
     have hyy : y = v 0 := Subtype.ext (hey.trans he.symm)
     rwa [hyy] at hy
 have hh := ((hvalue.reindex (![0] : Fin 1 → Fin 2)).and
   (hmem.reindex (![1,0] : Fin 2 → Fin 2))).ex (by omega)
 apply hh.congr
 intro i v
 change (∃ y : Domain (d i), y.val = O.eval (rel i) (s i) Fin.elim0 ∧
   (v 0).val ∈ y.val) ↔ _
 constructor
 · rintro ⟨y,hy,hxy⟩
   change (v 0).val ∈ O.eval (rel i) (s i) Fin.elim0
   rwa [hy] at hxy
 · intro hx
   have hv : O.eval (rel i) (s i) Fin.elim0 ∈ d i :=
     (ht i _ (eval_mem_trace (rel i) (s i) O Fin.elim0)).1
   exact ⟨⟨_,hv⟩,rfl,hx⟩

end CPTSeparation.Operational.Term

namespace CPTSeparation.Operational.Machine

open Classical Hereditary Counting HFCoding Finset

variable {R ι L : Type} {A : ι → Type} [∀ i, Fintype (A i)]

local instance instDecidableEqHF_6_redf58b_3 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable (P : Machine R) (O : P.Observer)

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool)

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

include hd hp ha hmem hset hinput in
lemma uniform_observed (ss : ∀ i, ℕ → P.Store (A := A i)) (h K J : ℕ)
 (hr : ∀ i j, j ≤ h → P.run (rel i) j = some (ss i j))
 (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m) (hO : O.width ≤ m)
 (ht : ∀ i j, j < h → ∀ x ∈ (P.instrument O).rule.trace (rel i) (ss i j) Fin.elim0,
   x ∈ d i ∧ (elements x).card ≤ J)
 (hs : ∀ i j, j ≤ h → ∀ x ∈ (ss i j).active, x ∈ d i)
 (hK : ∀ i j, j ≤ h → (ss i j).active.card ≤ K)
 (hJ : ∀ i j, j < h → (familyClosure (elements (O.eval (rel i) (ss i j) Fin.elim0))).card ≤ J) :
 UniformDefinable S m 1 (fun i v => (v 0).val ∈ P.observed O (rel i) h) := by
 have htP : ∀ i j, j < h → ∀ x ∈ P.rule.trace (rel i) (ss i j) Fin.elim0,
     x ∈ d i ∧ (elements x).card ≤ J :=
   fun i j hj x hx => ht i j hj x (P.original_trace_subset O (rel i) (ss i j) hx)
 have hactive := P.uniform_runActive d S hd hp ha hmem hset rel hinput ss h K J hr hm hroom htP hs hK
 have hstage (j : ℕ) (hj : j ∈ range h) :
     UniformDefinable S m 1 (fun i v => (v 0).val ∈ familyClosure (elements (O.eval (rel i) (ss i j) Fin.elim0))) := by
   have hjh : j < h := mem_range.mp hj
   have hstate := P.uniform_run d S hd hp ha hmem hset rel hinput ss j J
     (fun i k hk => hr i k (by omega)) hm hroom (fun i k hk => htP i k (by omega))
   have htO : ∀ i x, x ∈ O.trace (rel i) (ss i j) Fin.elim0 → x ∈ d i ∧ (elements x).card ≤ J :=
     fun i x hx => ht i j hjh x (P.observer_trace_subset O (rel i) (ss i j) hx)
   have hroot := Term.uniform_root_members d S hd hp ha hmem hset rel (fun i => ss i j)
     hinput hstate J O hO (by omega) htO
   have hc : ∀ i x, x ∈ familyClosure (elements (O.eval (rel i) (ss i j) Fin.elim0)) → x ∈ d i := by
     intro i x hx
     obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
     exact (htO i x (Term.closure_eval_subset_trace (rel i) (ss i j) O Fin.elim0
       (closure_member_subset hy hxy))).1
   have hh := State.uniform_descendants d S hmem
     (fun i => elements (O.eval (rel i) (ss i j) Fin.elim0)) hroot hc (by omega) J
   apply hh.congr
   intro i v
   rw [descendants_eq _ J (hJ i j hjh)]
 apply (hactive.or (UniformDefinable.exists_finset (range h) hstage)).congr
 intro i v
 simp only [observed,mem_union,mem_biUnion]
 apply or_congr Iff.rfl
 constructor
 · rintro ⟨j,hj,hv⟩
   exact ⟨j,hj,by simpa only [hr i j (by have := mem_range.mp hj; omega)] using hv⟩
 · rintro ⟨j,hj,hv⟩
   exact ⟨j,hj,by simpa only [hr i j (by have := mem_range.mp hj; omega)] using hv⟩

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Finset

local instance instDecidableEqHF_10_redf58b_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable {n m M N : ℕ} (P : Operational.Machine Symbol) (O : P.Observer) (vstar : Vertex n)

lemma op_observed_agrees (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (ss : ∀ i : Bool, ℕ → P.Store (A := Atom (twoCharges vstar i)))
    (hr : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j))
    (ha : ∀ i j, j ≤ h → (ss i j).active.card ≤ K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+(P.instrument O).rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+(P.instrument O).rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (P.observed O (atomInput (twoCharges vstar false)).rel h).card =
      (P.observed O (atomInput (twoCharges vstar true)).rel h).card := by
  let s := ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊
  let D := programDomain (twoCharges vstar) (s := s)
  let C := programHF (twoCharges vstar) (s := s)
  have hbound (i : Bool) : ∀ j ≤ h, ∀ st, P.run (atomInput (twoCharges vstar i)).rel j = some st → st.active.card ≤ K := by
    intro j hj st hh
    have he : st = ss i j := Option.some.inj (hh.symm.trans (hr i j hj))
    exact he ▸ ha i j hj
  have hfamily (i : Bool) : ∀ x ∈ (P.instrument O).runTrace (atomInput (twoCharges vstar i)).rel h, x ∈ D i :=
    opTrace_supported (twoCharges vstar i) (P.instrument O) hn h K N hN
      (fun j hj st hh => hbound i j hj st (by simpa only [Machine.instrument_run] using hh)) q hq hb
  have ht : ∀ i j, j < h → ∀ x ∈ (P.instrument O).rule.trace (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0,
      x ∈ D i ∧ (elements x).card ≤ (h+1)*(K+(P.instrument O).rule.bound.eval K) := by
    intro i j hj x hx
    have hx' := (P.instrument O).rule_trace_subset (h := h) (j := j) (s := ss i j) (atomInput (twoCharges vstar i)).rel (by omega) (by simpa only [Machine.instrument_run] using hr i j (by omega)) hx
    refine ⟨hfamily i x hx',?_⟩
    have he : elements x ⊆ (P.instrument O).runTrace (atomInput (twoCharges vstar i)).rel h := by
      intro y hy
      exact (P.instrument O).runTrace_closed _ h x hx' y hy
    exact (card_le_card he).trans ((P.instrument O).card_runTrace_le _ h K
      (fun j hj st hh => hbound i j hj st (by simpa only [Machine.instrument_run] using hh)))
  have hmP : ∀ f, P.functionArity f+2+P.rule.width ≤ m := by
    intro f
    have hh := hm f
    change P.functionArity f + 2 + (6 + P.rule.width + (6 + O.width + 6)) ≤ m at hh
    omega
  have hO : O.width ≤ m := by
    have hh := hm (.inl .halt)
    simp only [Machine.instrument,Rule.width] at hh
    omega
  have hJ (i : Bool) (j : ℕ) (hj : j < h) :
      (familyClosure (elements (O.eval (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0))).card ≤
        (h+1)*(K+(P.instrument O).rule.bound.eval K) := by
    have hsub : familyClosure (elements (O.eval (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0)) ⊆
        (P.instrument O).runTrace (atomInput (twoCharges vstar i)).rel h := by
      intro x hx
      apply P.observed_subset_trace O _ h
      exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_range.mpr hj,by simpa only [hr i j (by omega)] using hx⟩)
    exact (card_le_card hsub).trans ((P.instrument O).card_runTrace_le _ h K
      (fun j hj st hh => hbound i j hj st (by simpa only [Machine.instrument_run] using hh)))
  have hdef := P.uniform_observed O D C (program_domain_transitive (twoCharges vstar))
    (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
    (fun i => (atomInput (twoCharges vstar i)).rel) (op_input_uniform (twoCharges vstar))
    ss h K ((h+1)*(K+(P.instrument O).rule.bound.eval K)) hr hmP hroom hO ht
    (fun i j hj x hx => hfamily i x ((P.instrument O).active_subset_trace (h := h) (j := j) (s := ss i j) _ hj
      (by simpa only [Machine.instrument_run] using hr i j hj) hx)) ha hJ
  have hc := Operational.Machine.uniform_finite_family_card D C
    (fun i => P.observed O (atomInput (twoCharges vstar i)).rel h) hdef
    (fun i x hx => hfamily i x (P.observed_subset_trace O _ h hx)) (by omega)
    (P.observed O (atomInput (twoCharges vstar false)).rel h).card
  obtain ⟨φ,hφ,hφsem⟩ := hc (Fin.elim0 : Fin 0 → Fin m)
  have hfree : φ.free = ∅ := subset_empty.mp (by simpa using hφ)
  let v : Fin m → Domain (D false) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
  let w : Fin m → Domain (D true) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
  let := atom_nonempty hn (0 : Vertex n → Scalar)
  let := atom_nonempty hn (Pi.single vstar 1)
  have he := (hφsem false v).symm.trans ((grid_hf_transfer hn hs (by omega) vstar
    hwidth hhom hgiant φ hfree v w).trans (hφsem true w))
  exact (he.mp rfl).symm

end CPTSeparation.Grid

namespace CPTSeparation.Operational.Machine

section

open Classical Hereditary Finset

variable {A R : Type} [Fintype A]

local instance instDecidableEqHF_7_redf58b_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable (P : Machine R) (O : P.Observer)

lemma observed_implies_bounded (rel : R → A → A → Bool) {time space : ℕ}
    (ha : P.observedAccepts O rel time space) : P.boundedAccepts rel time space := by
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := ha
  refine ⟨h,st,hht,hhr,hhf,hha,?_⟩
  intro j hj t ht
  exact (card_le_card (P.active_subset_observed O rel hj ht)).trans hbudget

variable {B : Bool → Type} [∀ i, Fintype (B i)]

variable (rel : ∀ i, R → B i → B i → Bool)

lemma observed_accept_transfer (time space K : ℕ) (hS : space ≤ K)
    (hnext : space+P.rule.bound.eval space ≤ K)
    (hroot : ∀ i, (State.initial : P.Store (A := B i)).active.card ≤ K)
    (hobs : ∀ h, h ≤ time → P.PrefixBound rel h K → P.ObservationsAt rel h)
    (hcum : ∀ h, h ≤ time → P.PrefixBound rel h K →
      (P.observed O (rel false) h).card = (P.observed O (rel true) h).card)
    (i j : Bool) (hacc : P.observedAccepts O (rel i) time space) :
    P.observedAccepts O (rel j) time space := by
  by_cases hij : i = j
  · subst j; exact hacc
  have hcases (b : Bool) : b = i ∨ b = j := by cases i <;> cases j <;> cases b <;> simp_all
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := hacc
  have hsource : P.observedAccepts O (rel i) h space := ⟨h,st,le_refl _,hhr,hhf,hha,hbudget⟩
  have htarget := P.bounded_accept_transfer rel h space K hS hnext hroot
    (fun k hk => hobs k (by omega)) i j (P.observed_implies_bounded O (rel i) hsource)
  have hsource' := P.bounded_active_all (rel i) (P.observed_implies_bounded O (rel i) hsource)
  have htarget' := P.bounded_active_all (rel j) htarget
  have hp : P.PrefixBound rel h K := by
    intro b k hk
    rcases hcases b with rfl | rfl
    · obtain ⟨t,ht,hb⟩ := hsource' k
      exact ⟨t,ht,hb.trans hS⟩
    · obtain ⟨t,ht,hb⟩ := htarget' k
      exact ⟨t,ht,hb.trans hS⟩
  obtain ⟨t,ht,hbt⟩ := htarget' h
  have ho := hobs h hht hp i j st t hhr ht
  have he : (P.observed O (rel i) h).card = (P.observed O (rel j) h).card := by
    have he := hcum h hht hp
    cases i <;> cases j <;> simp_all
  exact ⟨h,t,hht,ht,(ho.1 .halt).mp hhf,(ho.1 .accept).mp hha,he ▸ hbudget⟩

lemma observed_accept_iff (time space K : ℕ) (hS : space ≤ K)
    (hnext : space+P.rule.bound.eval space ≤ K)
    (hroot : ∀ i, (State.initial : P.Store (A := B i)).active.card ≤ K)
    (hobs : ∀ h, h ≤ time → P.PrefixBound rel h K → P.ObservationsAt rel h)
    (hcum : ∀ h, h ≤ time → P.PrefixBound rel h K →
      (P.observed O (rel false) h).card = (P.observed O (rel true) h).card) :
    P.observedAccepts O (rel false) time space ↔ P.observedAccepts O (rel true) time space :=
  ⟨P.observed_accept_transfer O rel time space K hS hnext hroot hobs hcum false true,
   P.observed_accept_transfer O rel time space K hS hnext hroot hobs hcum true false⟩

end

lemma observedAccepts_fintype {A R : Type} (t u : Fintype A) (P : Machine R) (O : P.Observer)
 (rel : R → A → A → Bool) (T S : ℕ) :
 @observedAccepts A R t P O rel T S ↔ @observedAccepts A R u P O rel T S := by
 have h : t = u := Subsingleton.elim _ _
 cases h
 rfl

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

section

open Classical Hereditary Counting HFCoding Operational Finset

local instance instDecidableEqHF_11_redf58b_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable {n m M N : ℕ} (P : Operational.Machine Symbol) (O : P.Observer) (vstar : Vertex n)

lemma op_prefix_observed (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (hr : P.PrefixBound (fun i => (atomInput (twoCharges vstar i)).rel) h K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+(P.instrument O).rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+(P.instrument O).rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (P.observed O (atomInput (twoCharges vstar false)).rel h).card =
      (P.observed O (atomInput (twoCharges vstar true)).rel h).card := by
  let ss := fun i j => (P.run (atomInput (twoCharges vstar i)).rel j).getD State.initial
  have hrs : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j) := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simp only [ss,hst,Option.getD_some]
  have hact : ∀ i j, j ≤ h → (ss i j).active.card ≤ K := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simpa only [ss,hst,Option.getD_some] using hb
  exact op_observed_agrees P O vstar hn h K hN ss hrs hact q hq hb hm hroom hs hwidth hhom hgiant

end

open Classical Hereditary Counting HFCoding Operational Quantitative Finset

local instance instDecidableEqHF_12_redf58b_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _
theorem polynomial_observed_agrees_on_some_box (P : Operational.Machine Symbol) (O : P.Observer) (time space : Polynomial ℕ) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (vstar : Vertex n),
      P.polynomialObservedAccepts O time space (atomInput (0 : Vertex n → Scalar)).rel ↔
        P.polynomialObservedAccepts O time space (atomInput (Pi.single vstar 1)).rel := by
  obtain ⟨ct,dt,hpt⟩ := PolynomialCost.eval_bound time
  obtain ⟨cs,ds,hps⟩ := PolynomialCost.eval_bound space
  let c := ct+cs
  let d := dt+ds
  have hmaj (N : ℕ) : time.eval N ≤ c*(N+1)^d ∧ space.eval N ≤ c*(N+1)^d := by
    constructor
    · exact (hpt N).trans (Nat.mul_le_mul (by dsimp [c]; omega)
        (Nat.pow_le_pow_right (by omega) (by dsimp [d]; omega)))
    · exact (hps N).trans (Nat.mul_le_mul (by dsimp [c]; omega)
        (Nat.pow_le_pow_right (by omega) (by dsimp [d]; omega)))
  obtain ⟨m,hroom,hm⟩ := (P.instrument O).exists_palette
  let p₀ : Polynomial ℕ := Polynomial.X+P.rule.bound
  let p : Polynomial ℕ := (Polynomial.X+1)*(p₀+(P.instrument O).rule.bound.comp p₀)
  obtain ⟨cp,dp,hp⟩ := PolynomialCost.eval_bound p
  let e := timeExponent c d+2
  let a := timeExponent cp dp
  let q := e*a
  have he : 4 ≤ e := by have := timeExponent_ge_two c d; omega
  have ha : 2 ≤ a := timeExponent_ge_two cp dp
  have hq : 0 < q := Nat.mul_pos (by omega) (by omega)
  obtain ⟨n,hn,hnum⟩ := exists_numeric_box q hq m
  let N := atomSizeConstant*(n+1)^3
  let B := N^e
  let K := B+P.rule.bound.eval B
  let vstar : Vertex n := ⟨0,0,0⟩
  let rel := fun i => (atomInput (twoCharges vstar i)).rel
  let T := time.eval (Fintype.card (Atom (0 : Vertex n → Scalar)))
  let S := space.eval (Fintype.card (Atom (0 : Vertex n → Scalar)))
  have hN : 2 ≤ N := hnum.1
  have hinput : ∀ i, Fintype.card (Atom (twoCharges vstar i)) ≤ N :=
    fun i => (atom_card_bounds hn (twoCharges vstar i)).2
  have hBB : N^timeExponent c d ≤ B := Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega)
  have hB : 2 ≤ B := (polynomial_bounds c d N hN).1.trans hBB
  have hinit : N+3 ≤ B := by
    have hs : 4 ≤ N^2 := by nlinarith
    have ht := Nat.mul_le_mul_left N hs
    calc
      N+3 ≤ N^3 := by nlinarith
      _ ≤ B := Nat.pow_le_pow_right (by omega) (by omega)
  have hTB : T ≤ B := by
    exact ((PolynomialCost.eval_mono time (hinput false)).trans (hmaj N).1).trans
      ((polynomial_bounds c d N hN).2.2.1.trans hBB)
  have hSB : S ≤ B := by
    exact ((PolynomialCost.eval_mono space (hinput false)).trans (hmaj N).2).trans
      ((polynomial_bounds c d N hN).2.2.1.trans hBB)
  have hsK : S ≤ K := hSB.trans (Nat.le_add_right _ _)
  have hnext : S+P.rule.bound.eval S ≤ K :=
    add_le_add hSB (PolynomialCost.eval_mono _ hSB)
  have hroot (i : Bool) : (State.initial : P.Store (A := Atom (twoCharges vstar i))).active.card ≤ K :=
    State.initial_active_card.trans ((Nat.add_le_add_right (hinput i) 3).trans (hinit.trans (Nat.le_add_right _ _)))
  have hpoly (h : ℕ) (hh : h ≤ T) : (h+1)*(K+(P.instrument O).rule.bound.eval K) ≤ N^q := by
    calc
      (h+1)*(K+(P.instrument O).rule.bound.eval K) ≤ (B+1)*(K+(P.instrument O).rule.bound.eval K) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = p.eval B := by simp only [p,p₀,K,Polynomial.eval_mul,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
      _ ≤ cp*(B+1)^dp := hp B
      _ ≤ B^a := (polynomial_bounds cp dp B hB).2.2.1
      _ = N^q := by simp only [B,q,pow_mul]
  have hb_le (K : ℕ) : P.rule.bound.eval K ≤ (P.instrument O).rule.bound.eval K := by
    simp only [Machine.instrument,Rule.bound,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_zero]
    omega
  have hmP : ∀ f, P.functionArity f+2+P.rule.width ≤ m := by
    intro f
    have hh := hm f
    change P.functionArity f + 2 + (6 + P.rule.width + (6 + O.width + 6)) ≤ m at hh
    omega
  have hobs := fun (h : ℕ) (hht : h ≤ T) hprefix =>
    op_prefix_observations (N := N) P vstar hn h K (by omega) hprefix (q:ℝ) (by positivity)
      (by rw [Real.rpow_natCast]
          exact_mod_cast (le_trans (Nat.mul_le_mul_left (h+1) (Nat.add_le_add_left (hb_le K) K)) (hpoly h hht))) hmP hroom
      hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2
  have hcum := fun (h : ℕ) (hht : h ≤ T) hprefix =>
    op_prefix_observed (N := N) P O vstar hn h K (by omega) hprefix (q:ℝ) (by positivity)
      (by rw [Real.rpow_natCast]; exact_mod_cast hpoly h hht) hm hroom
      hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2
  have hh := P.observed_accept_iff O rel T S K hsK hnext hroot hobs hcum
  refine ⟨n,hn,vstar,?_⟩
  have hcard := atom_card_independent hn (0 : Vertex n → Scalar) (Pi.single vstar 1)
  simp only [Operational.Machine.polynomialObservedAccepts,rel,T,S,twoCharges,← hcard] at hh ⊢
  convert hh using 1 <;> apply Operational.Machine.observedAccepts_fintype

end CPTSeparation.Grid

namespace CPTSeparation

theorem query_not_polynomial_observed_HF :
 ¬ ∃ (P : Operational.Machine Symbol) (O : P.Observer) (time space : Polynomial ℕ),
   ∀ (A : Type) [Fintype A] (I : Input A), P.polynomialObservedAccepts O time space I.rel ↔ I.query := by
 rintro ⟨P,O,time,space,hdecides⟩
 obtain ⟨n,hn,vstar,hagree⟩ := Grid.polynomial_observed_agrees_on_some_box P O time space
 obtain ⟨hzero,hunit⟩ := Grid.opposite_answers hn vstar
 exact hunit ((hdecides _ _).mp (hagree.mp ((hdecides _ _).mpr hzero)))

end CPTSeparation

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Evaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.FullCPT

noncomputable section

open Classical Hereditary Finset

open Operational (State Control)

attribute [local instance] CPTSeparation.FullCPT.instDecidableEqHF_1

variable {A R F : Type} {arity : F → ℕ}

namespace Term

variable [finiteA : Fintype A]

lemma eval_collect (rel : R → A → A → Bool) (s : State F arity A) (t : Term R F arity) (v : ℕ → HF A) :
 t.collect.eval rel s v = ofFinset (t.roots rel s v) := by
 induction t generalizing v with
 | var n => simp only [collect,roots,eval_pack]
 | ordinal n => simp only [collect,roots,eval_pack]
 | atoms => simp only [collect,roots,eval_pack]
 | app f args ih => simp only [collect,roots,eval_merge,eval_pack,eval_merges,List.map_ofFn,Function.comp_def,ih,elements_ofFinset,singleton_union]
 | pair a b iha ihb | equal a b iha ihb | member a b iha ihb
 | input r a b iha ihb | and a b iha ihb | or a b iha ihb =>
   simp only [collect,roots,eval_merge,eval_pack,iha,ihb,elements_ofFinset,singleton_union]
 | union a ih | unique a ih | card a ih | isAtom a ih | not a ih =>
   simp only [collect,roots,eval_merge,eval_pack,ih,elements_ofFinset,singleton_union]
 | conditional c a b ihc iha ihb =>
   simp only [collect,roots,eval_merge,eval,ihc,iha,ihb,elements_ofFinset]
   split <;> simp only [elements_ofFinset]
 | comprehend n bound guard body ihbound ihguard ihbody =>
   simp only [collect,roots,eval_merge,eval_pack,eval,ihbound,ihguard,ihbody,elements_ofFinset,singleton_union]
   congr 2
   simp only [Operational.unionHF,elements_ofFinset]
   congr 1
   simp only [Finset.filter_true,image_biUnion,elements_ofFinset]
   apply biUnion_congr rfl
   intro x hx
   split <;> simp [elements_ofFinset,elements_zero]

end Term

namespace Rule

variable [Fintype A]

lemma eval_collect (rel : R → A → A → Bool) (s : State F arity A) (r : Rule R F arity) (v : ℕ → HF A) :
 r.collect.eval rel s v = ofFinset (r.roots rel s v) := by
 induction r generalizing v with
 | skip => rfl
 | update f args value =>
   simp only [collect,roots,Term.eval_merge,Term.eval_merges,List.map_ofFn,Function.comp_def,Term.eval_collect,elements_ofFinset]
 | parallel a b iha ihb => simp only [collect,roots,Term.eval_merge,iha,ihb,elements_ofFinset]
 | conditional c a b iha ihb =>
   simp only [collect,roots,Term.eval_merge,Term.eval,Term.eval_collect,iha,ihb,elements_ofFinset]
   split <;> simp only [elements_ofFinset]
 | «forall» n bound body ih =>
   simp only [collect,roots,Term.eval_merge,Term.eval_spread,Term.eval_collect,ih,elements_ofFinset]
 | letValue n value body ih =>
   simp only [collect,roots,Term.eval_merge,Term.eval_spread,Term.eval_pack,Term.eval_collect,ih,elements_ofFinset,singleton_biUnion]

end Rule

namespace Program

variable (P : Program R) [Fintype A]

lemma rootObserver_eval (rel : R → A → A → Bool) (s : P.Store (A := A)) :
 P.rootObserver.eval rel s Fin.elim0 = ofFinset (P.stepRoots rel s) := by
 rw [rootObserver,Term.eval_compile rel s _ _ (fun _ => Operational.empty) Fin.elim0 (fun _ => rfl)]
 simp only [Term.eval,Rule.eval_collect,stepRoots,flag]
 have he : (fun i : Fin (P.functionArity (.inl Control.halt)) =>
     Term.eval rel s (Fin.elim0 i) (fun _ => Operational.empty)) = Fin.elim0 := by
   funext i
   exact Fin.elim0 i
 rw [he]
 split <;> simp_all only [ite_true,ite_false] ; rfl

lemma observed_compile (rel : R → A → A → Bool) (h : ℕ) :
 P.compile.observed P.rootObserver rel h = P.occurring rel h := by
 simp only [Operational.Machine.observed,occurring,P.active_compile,P.run_compile]
 congr 1
 apply biUnion_congr rfl
 intro j hj
 cases P.run rel j with
 | none => rfl
 | some s =>
   exact congrArg familyClosure ((congrArg elements (P.rootObserver_eval rel s)).trans (elements_ofFinset _))

lemma evaluationAccepts_compile (time space : Polynomial ℕ) (rel : R → A → A → Bool) :
 P.compile.polynomialObservedAccepts P.rootObserver time space rel ↔ P.evaluationAccepts time space rel := by
 simp only [Operational.Machine.polynomialObservedAccepts,Operational.Machine.observedAccepts,
   evaluationAccepts,P.run_compile,P.observed_compile,Operational.Machine.flag,flag]
 rfl

end Program

theorem query_not_evaluationDefinable : ¬ EvaluationDefinable (fun {_} [_] I => I.query) := by
 rintro ⟨P,time,space,h⟩
 apply query_not_polynomial_observed_HF
 refine ⟨P.compile,P.rootObserver,time,space,?_⟩
 intro A inst I
 exact (P.evaluationAccepts_compile time space I.rel).trans (h A I)

end

end CPTSeparation.FullCPT

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.Gaussian

namespace Row

lemma satisfies_cons {n} (r : Row (n+1)) (x : Scalar) (v : Fin n → Scalar) :
    r.satisfies (Fin.cons x v) ↔
      r.coeff 0*x + (∑ i, r.coeff i.succ * v i) = r.rhs := by
  simp [satisfies,Fin.sum_univ_succ]

lemma tail_iff {n} (r : Row (n+1)) (h : r.coeff 0 = 0) (x : Scalar) (v : Fin n → Scalar) :
    r.satisfies (Fin.cons x v) ↔ r.tail.satisfies v := by
  rw [satisfies_cons,h]
  simp [satisfies,tail]

lemma pivot_solution {n} (p : Row (n+1)) (hp : p.coeff 0 ≠ 0) (v : Fin n → Scalar) :
    p.satisfies (Fin.cons ((p.rhs - ∑ i, p.coeff i.succ * v i)/p.coeff 0) v) := by
  rw [satisfies_cons]
  field_simp
  ring

lemma reduce_iff {n} (p r : Row (n+1)) (hp : p.coeff 0 ≠ 0)
    (x : Scalar) (v : Fin n → Scalar) (hpx : p.satisfies (Fin.cons x v)) :
    r.satisfies (Fin.cons x v) ↔ (p.reduce r).satisfies v := by
  rw [satisfies_cons] at hpx ⊢
  simp only [satisfies,reduce,sub_mul,Finset.sum_sub_distrib,
    mul_assoc,← Finset.mul_sum]
  have h : (r.coeff 0 / p.coeff 0)*p.coeff 0 = r.coeff 0 := div_mul_cancel₀ _ hp
  have heq : r.coeff 0*x + ∑ i, r.coeff i.succ*v i - r.rhs =
      (∑ i, r.coeff i.succ*v i) - (r.coeff 0/p.coeff 0)*(∑ i, p.coeff i.succ*v i) -
        (r.rhs-(r.coeff 0/p.coeff 0)*p.rhs) := by
    rw [← hpx]
    linear_combination -(x*h)
  exact (sub_eq_zero.symm.trans (iff_of_eq (congrArg (fun z => z = 0) heq))).trans sub_eq_zero

end Row

lemma pivot_some {n} {rows : List (Row (n+1))} {p : Row (n+1)} (h : pivot rows = some p) :
    p ∈ rows ∧ p.coeff 0 ≠ 0 := by
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

lemma pivot_none {n} {rows : List (Row (n+1))} (h : pivot rows = none) :
    ∀ r ∈ rows, r.coeff 0 = 0 := by
  simpa [pivot,List.find?_eq_none] using h

lemma solvable_tail {n} {rows : List (Row (n+1))} (h : pivot rows = none) :
    Solvable rows ↔ Solvable (rows.map Row.tail) := by
  have hz := pivot_none h
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨fun i => v i.succ,?_⟩
    intro r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    have hv' : Fin.cons (v 0) (fun i => v i.succ) = v := by ext i; cases i using Fin.cases <;> rfl
    exact (Row.tail_iff s (hz s hs) (v 0) _).mp (hv' ▸ hv s hs)
  · rintro ⟨v,hv⟩
    refine ⟨Fin.cons 0 v,?_⟩
    intro r hr
    exact (Row.tail_iff r (hz r hr) 0 v).mpr (hv _ (List.mem_map_of_mem hr))

lemma solvable_reduce {n} {rows : List (Row (n+1))} {p : Row (n+1)}
    (h : pivot rows = some p) : Solvable rows ↔ Solvable (rows.map (Row.reduce p)) := by
  obtain ⟨hpm,hp⟩ := pivot_some h
  constructor
  · rintro ⟨v,hv⟩
    have hv' : Fin.cons (v 0) (fun i => v i.succ) = v := by ext i; cases i using Fin.cases <;> rfl
    refine ⟨fun i => v i.succ,?_⟩
    intro r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact (Row.reduce_iff p s hp (v 0) _ (hv' ▸ hv p hpm)).mp (hv' ▸ hv s hs)
  · rintro ⟨v,hv⟩
    let x := (p.rhs - ∑ i, p.coeff i.succ * v i)/p.coeff 0
    refine ⟨Fin.cons x v,?_⟩
    intro r hr
    exact (Row.reduce_iff p r hp x v (Row.pivot_solution p hp v)).mpr
      (hv _ (List.mem_map_of_mem hr))

theorem solve_correct {n} (rows : List (Row n)) : solve rows = true ↔ Solvable rows := by
  induction n with
  | zero =>
    simp only [solve,List.all_eq_true,beq_iff_eq]
    constructor
    · intro h
      exact ⟨Fin.elim0,fun r hr => by simpa [Row.satisfies] using (h r hr).symm⟩
    · rintro ⟨v,hv⟩ r hr
      simpa [Row.satisfies] using (hv r hr).symm
  | succ n ih =>
    cases hp : pivot rows with
    | none => simpa only [solve,hp] using (ih (rows.map Row.tail)).trans (solvable_tail hp).symm
    | some p => simpa only [solve,hp] using (ih (rows.map (Row.reduce p))).trans (solvable_reduce hp).symm

end CPTSeparation.Gaussian

namespace CPTSeparation.OrderedQuery

open Finset

variable {N : ℕ}

lemma sum_subtype {A : Type} [Fintype A] [DecidableEq A] (p : A → Prop) [DecidablePred p]
    (f : A → Scalar) : (∑ a, if p a then f a else 0) = ∑ a : {a // p a}, f a := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

lemma coefficient_eq (S : Data N) (y : S.Edge) (a : S.Config) :
    coefficient S y a = S.coefficient y a := by
  unfold coefficient Input.coefficient
  rw [← sum_subtype (fun x => S.rel .Ed x x = true) (fun x => if S.rel .I a x then ∑ δ : Scalar, if S.rel (.Z δ) y x then δ else 0 else 0)]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : S.rel .Ed x x = true <;> by_cases h' : S.rel .I a x = true <;> simp [h,h']

lemma incident_eq (S : Data N) (t : S.Config) (y : S.Edge) :
    incident S t y = true ↔ S.incident t y := by
  simp only [incident,List.any_eq_true,Bool.and_eq_true,List.mem_finRange,true_and,
    Input.incident]
  constructor
  · rintro ⟨a,⟨ha,hva⟩,x,⟨hx,hix⟩,hby⟩
    exact ⟨⟨a,ha⟩,hva,⟨x,hx⟩,hix,hby⟩
  · rintro ⟨a,hva,x,hix,hby⟩
    exact ⟨a,⟨a.property,hva⟩,x,⟨x.property,hix⟩,hby⟩

lemma row_zero (v : Fin (N+N) → Scalar) :
    (⟨fun _ => 0,0⟩ : Gaussian.Row (N+N)).satisfies v := by simp [Gaussian.Row.satisfies]

lemma normalization_satisfies (S : Data N) (t : Fin N) (v : Fin (N+N) → Scalar) :
    (normalizationRow S t).satisfies v ↔
      S.rel .Cf t t = true →
        (∑ a : S.Config, if S.rel .VB t a then left v a else 0) = 1 := by
  by_cases ht : S.rel .Cf t t = true
  · simp only [normalizationRow,ht,ite_true,Gaussian.Row.satisfies,Fin.sum_univ_add,
      Fin.addCases_left,Fin.addCases_right,zero_mul,Finset.sum_const_zero,add_zero,
      true_implies]
    have heq : (∑ a : Fin N, (if S.rel .Cf a a && S.rel .VB t a then (1:Scalar) else 0) * left v a) =
        ∑ a : S.Config, if S.rel .VB t a then left v a else 0 := by
      rw [← sum_subtype (fun a => S.rel .Cf a a = true) (fun a => if S.rel .VB t a then left v a else 0)]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : S.rel .Cf a a = true <;> by_cases hv : S.rel .VB t a = true <;> simp [ha,hv]
    exact (congrArg (fun z => z = 1) heq).to_iff
  · simp [normalizationRow,ht,Gaussian.Row.satisfies]

lemma consistency_satisfies (S : Data N) (t y : Fin N) (v : Fin (N+N) → Scalar) :
    (consistencyRow S t y).satisfies v ↔
      ∀ (ht : S.rel .Cf t t = true) (hy : S.rel .Ed y y = true),
        S.incident ⟨t,ht⟩ ⟨y,hy⟩ →
        right v y = ∑ a : S.Config, if S.rel .VB t a then left v a*S.coefficient ⟨y,hy⟩ a else 0 := by
  by_cases ht : S.rel .Cf t t = true
  · by_cases hy : S.rel .Ed y y = true
    · have hi := incident_eq S ⟨t,ht⟩ ⟨y,hy⟩
      by_cases hin : incident S t y = true
      · simp only [consistencyRow,ht,hy,hin,Bool.true_and,ite_true,
          Gaussian.Row.satisfies,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
        have hr : (∑ z : Fin N, (if z = y then (1:Scalar) else 0)*right v z) = right v y := by
          simp
        have hl : (∑ a : Fin N, (if S.rel .Cf a a && S.rel .VB t a then -coefficient S y a else 0)*left v a) =
            -(∑ a : S.Config, if S.rel .VB t a then left v a*S.coefficient ⟨y,hy⟩ a else 0) := by
          rw [← Finset.sum_neg_distrib]
          trans ∑ a : S.Config, (if S.rel .VB t a then -coefficient S y a else 0)*left v a
          · rw [← sum_subtype (fun a => S.rel .Cf a a = true) (fun a => (if S.rel .VB t a then -coefficient S y a else 0)*left v a)]
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : S.rel .Cf a a = true <;> by_cases hv : S.rel .VB t a = true <;> simp [ha,hv]
          · apply Finset.sum_congr rfl
            intro a _
            rw [coefficient_eq S ⟨y,hy⟩ a]
            by_cases hv : S.rel .VB t a = true <;> simp [hv,mul_comm]
        change (_ + _ = 0) ↔ _
        rw [show (∑ i : Fin N, (if i = y then (1:Scalar) else 0) * v (Fin.natAdd N i)) = right v y from hr]
        rw [show (∑ i : Fin N, (if S.rel .Cf i i && S.rel .VB t i then -coefficient S y i else 0) * v (Fin.castAdd N i)) = _ from hl]
        constructor
        · intro h _ _ _
          linear_combination h
        · intro h
          have hh := h True.intro True.intro (hi.mp hin)
          linear_combination hh
      · have hni : ¬ S.incident ⟨t,ht⟩ ⟨y,hy⟩ := fun h => hin (hi.mpr h)
        simp only [consistencyRow,ht,hy,Bool.true_and,hin,true_implies,hni,false_implies,iff_true]
        exact row_zero v
    · simp [consistencyRow,hy,Gaussian.Row.satisfies]
  · simp [consistencyRow,ht,Gaussian.Row.satisfies]

lemma norm_mem (S : Data N) (t : Fin N) : normalizationRow S t ∈ rows S := by
  apply List.mem_append_left
  exact List.mem_map_of_mem (List.mem_finRange t)

lemma consistency_mem (S : Data N) (t y : Fin N) : consistencyRow S t y ∈ rows S := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨t,List.mem_finRange t,List.mem_map_of_mem (List.mem_finRange y)⟩

theorem rows_solvable_iff (S : Data N) : Gaussian.Solvable (rows S) ↔ S.query := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨fun a => left v a,fun y => right v y,?_,?_⟩
    · intro t
      exact (normalization_satisfies S t v).mp (hv _ (norm_mem S t)) t.property
    · intro t y hinc
      exact (consistency_satisfies S t y v).mp (hv _ (consistency_mem S t y)) t.property y.property hinc
  · rintro ⟨lam,mu,hnorm,hcons⟩
    let l : Fin N → Scalar := fun a => if ha : S.rel .Cf a a = true then lam ⟨a,ha⟩ else 0
    let r : Fin N → Scalar := fun y => if hy : S.rel .Ed y y = true then mu ⟨y,hy⟩ else 0
    let v : Fin (N+N) → Scalar := Fin.addCases l r
    have hl (a : S.Config) : left v a = lam a := by simp [left,v,l,a.property]
    have hr (y : S.Edge) : right v y = mu y := by
      simp only [right,v,Fin.addCases_right]
      simp only [r,dite_eq_left y.property]
    refine ⟨v,?_⟩
    intro row hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hrow
      apply (normalization_satisfies S t v).mpr
      intro ht
      simpa only [hl] using hnorm ⟨t,ht⟩
    · obtain ⟨t,ht,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hrow
      apply (consistency_satisfies S t y v).mpr
      intro ht hy hi
      rw [show right v y = mu ⟨y,hy⟩ from hr ⟨y,hy⟩]
      simpa only [hl] using hcons ⟨t,ht⟩ ⟨y,hy⟩ hi

theorem decideQuery_correct (S : Data N) : decideQuery S = true ↔ S.query := by
  simp only [decideQuery,Gaussian.metered_answer,Gaussian.solve_correct]
  have he : (rows S).map Gaussian.Row.dense = rows S := by
    have hf : Gaussian.Row.dense (n := N+N) = id := funext Gaussian.Row.dense_eq
    rw [hf,List.map_id]
  rw [he,rows_solvable_iff]

end CPTSeparation.OrderedQuery

namespace CPTSeparation.SerialGaussian

theorem solve_decode {n} (rows : List (Row n)) :
    solve rows = Gaussian.solve (rows.map Row.decode) := by
  induction n with
  | zero => simp [solve,Gaussian.solve,Row.decode,Function.comp_def]
  | succ n ih =>
    cases hp : pivot rows with
    | none => simp [solve,Gaussian.solve,pivot_decode,hp,ih,List.map_map,Function.comp_def]
    | some p => simp [solve,Gaussian.solve,pivot_decode,hp,ih,List.map_map,Function.comp_def]

theorem queryRows_correct {N} (S : OrderedQuery.Data N) :
    solve (queryRows S) = true ↔ S.query := by
  rw [solve_decode]
  have hd : Gaussian.Row.dense (n := N+N) = id := funext Gaussian.Row.dense_eq
  simpa [queryRows,List.map_map,Function.comp_def,OrderedQuery.decideQuery,
    Gaussian.metered_answer,hd] using OrderedQuery.decideQuery_correct S

end CPTSeparation.SerialGaussian

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.QueryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.QueryMachine

open StackLang StackLang.Macros

open StackLang StackLang.Macros

open Turing StateTransition

lemma answer_correct (S : OrderedQuery.OrderedInput) : answer S = true ↔ S.2.query :=
 SerialGaussian.queryRows_correct S.2

end CPTSeparation.QueryMachine

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Separation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation

theorem main_oai :
    (∀ (A B : Type) [Fintype A] [Fintype B] (S : Input A) (T : Input B),
      S.Iso T → (S.query ↔ T.query)) ∧
    OrdinaryPolynomialTime ∧
    ¬ FullCPT.EvaluationDefinable (fun {_} [_] I => I.query) := by
  refine ⟨?_, ?_, FullCPT.query_not_evaluationDefinable⟩
  · intro A B _ _ S T e
    exact Input.query_invariant e
  · refine ⟨QueryMachine.answer, QueryMachine.polynomialAlgorithm, ?_, ?_⟩
    · intro k
      change Finite QueryMachine.Letter
      infer_instance
    · intro A _ N e S
      let iso : S.Iso (S.ordered e) :=
        { toEquiv := e
          rel_eq := by intro r x y; simp [Input.ordered] }
      exact (QueryMachine.answer_correct ⟨N,S.ordered e⟩).trans
        (Input.query_invariant iso).symm

end CPTSeparation

end OAI
end

theorem solution : type_of% @OAI.CPTSeparation.main_oai := @OAI.CPTSeparation.main_oai
