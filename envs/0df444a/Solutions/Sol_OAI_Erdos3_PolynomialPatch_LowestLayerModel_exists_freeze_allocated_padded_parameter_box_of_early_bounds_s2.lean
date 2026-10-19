-- Prove2me | solution 1 for OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:37:10.346196+00:00
-- url     : https://prove2.me/submissions/5197adcf-8e3c-4abd-9ffb-bdb12d4180a8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B229
import Definitions.Def_OAIE3v2B230
import Definitions.Def_OAIE3v2B233
import Definitions.Def_OAIE3v2B248

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFreezingEarlyLogBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem preparedFreezingRadiusBudget_of_terms {m D : ℕ} {Lip gain δ : ℝ}
    (term : Fin m → ℝ) (hLip : 0 ≤ Lip) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (hterm : ∀ j, term j ≤ gain / (128 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1)))
    (hδ : δ ≤ gain / (128 * ((D : ℝ) + 1) * (Lip + 1))) :
    (D : ℝ) * 2 * ((∑ j, term j) + δ) < 1 / 12 ∧
      Lip * ((D : ℝ) * 2 * ((∑ j, term j) + δ)) ≤ gain / 16 := by
  let b := gain / (128 * ((D : ℝ) + 1) * (Lip + 1))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsum : (∑ j, term j) ≤ b := by
    calc
      _ ≤ ∑ _j : Fin m, gain / (128 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
      _ = (m : ℝ) * (b / ((m : ℝ) + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, b, div_div]
      _ ≤ ((m : ℝ) + 1) * (b / ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hb (by positivity))
      _ = b := by field_simp
  have hoscb : (D : ℝ) * 2 * ((∑ j, term j) + δ) ≤ gain / (32 * (Lip + 1)) := by
    calc
      _ ≤ (D : ℝ) * 2 * (b + b) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum hδ) (by positivity)
      _ = 4 * (D : ℝ) * b := by ring
      _ ≤ 4 * ((D : ℝ) + 1) * b := mul_le_mul_of_nonneg_right (by linarith) hb
      _ = gain / (32 * (Lip + 1)) := by
        dsimp [b]
        field_simp
        ring
  have hLp : 0 < Lip + 1 := by positivity
  refine ⟨hoscb.trans_lt ?_, (mul_le_mul_of_nonneg_left hoscb hLip).trans ?_⟩
  · apply (div_lt_iff₀ (by positivity : 0 < 32 * (Lip + 1))).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 32 * (Lip + 1))).mpr
    nlinarith [mul_nonneg hgain.le hLip]

theorem preparedFreezingRadiusBudget_of_inflated_chart {m D : ℕ} {Lip gain δ : ℝ}
    (N I : Fin m → ℕ) (C R : Fin m → ℝ)
    (hLip : 0 ≤ Lip) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (hchart : ∀ j,
      ((32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain) * (N j : ℝ) * C j) *
        ((I j : ℝ) + 1) * R j ≤ 1 / 4)
    (hδ : δ ≤ gain / (128 * ((D : ℝ) + 1) * (Lip + 1))) :
    (D : ℝ) * 2 * ((∑ j, (N j : ℝ) * C j * ((I j : ℝ) + 1) * R j) + δ) < 1 / 12 ∧
      Lip * ((D : ℝ) * 2 * ((∑ j, (N j : ℝ) * C j * ((I j : ℝ) + 1) * R j) + δ)) ≤ gain / 16 := by
  apply preparedFreezingRadiusBudget_of_terms _ hLip hgain hgain1 _ hδ
  intro j
  have hf : 0 < 32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain := by positivity
  have hj : (32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain) *
      ((N j : ℝ) * C j * ((I j : ℝ) + 1) * R j) ≤ 1 / 4 := by
    convert hchart j using 1; ring
  have h : (N j : ℝ) * C j * ((I j : ℝ) + 1) * R j ≤
      (1 / 4) / (32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain) :=
    (le_div_iff₀ hf).mpr (by simpa only [mul_comm] using hj)
  refine h.trans_eq ?_
  field_simp
  ring

theorem preparedFreezingInflation_exp_bound {F N C gF gN gC : ℝ}
    (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hFexp : F ≤ Real.exp gF) (hNexp : N ≤ Real.exp gN) (hCexp : C ≤ Real.exp gC) :
    F * N * C ≤ Real.exp (gF + gN + gC) := by
  rw [Real.exp_add, Real.exp_add]
  exact mul_le_mul (mul_le_mul hFexp hNexp hN (Real.exp_nonneg _)) hCexp hC (by positivity)

end Erdos3

end

section

namespace Erdos3

private theorem exp_succ_bounds_add_one {x p : ℝ} (hp : 0 ≤ p)
    (hx : x ≤ Real.exp p) : x + 1 ≤ Real.exp (p + 1) := by
  have h1 : 1 ≤ Real.exp p := Real.one_le_exp hp
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  nlinarith [Real.exp_pos p]

theorem preparedFreezingEarlyLogBudget {D m N : ℕ} {Lip C gain δ p : ℝ}
    (hp : 0 ≤ p) (hLip : 0 ≤ Lip) (hC : 0 ≤ C)
    (hD : (D : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p)
    (hL : Lip ≤ Real.exp p) (hN : (N : ℝ) ≤ Real.exp p)
    (hCexp : C ≤ Real.exp p) (hgain : Real.exp (-p) ≤ gain)
    (hδ : δ ≤ Real.exp (-(3 * p + 130))) :
    (32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain) *
      (N : ℝ) * C ≤ Real.exp (6 * p + 35) ∧
      δ ≤ gain / (128 * ((D : ℝ) + 1) * (Lip + 1)) := by
  have hgain0 : 0 < gain := (Real.exp_pos _).trans_le hgain
  have hD' := exp_succ_bounds_add_one hp hD
  have hm' := exp_succ_bounds_add_one hp hm
  have hL' := exp_succ_bounds_add_one hp hL
  have hi : gain⁻¹ ≤ Real.exp p := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (-p)) hgain
    simpa only [one_div, Real.exp_neg, inv_inv] using h
  have h32 : (32 : ℝ) ≤ Real.exp 32 := by linarith [Real.add_one_le_exp (32 : ℝ)]
  have h128 : (128 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  have hF : 32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain ≤
      Real.exp (4 * p + 35) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 32 * Real.exp (p+1) * Real.exp (p+1) * Real.exp (p+1) * Real.exp p := by
        exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h32 hD'
          (by positivity) (Real.exp_nonneg _)) hL' (by positivity) (by positivity))
          hm' (by positivity) (by positivity)) hi (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨?_, ?_⟩
  · have h := preparedFreezingInflation_exp_bound (Nat.cast_nonneg N) hC hF hN hCexp
    convert h using 1
    congr 1
    ring
  · have hden : (128 * ((D : ℝ) + 1) * (Lip + 1)) * gain⁻¹ ≤ Real.exp (3*p+130) := by
      calc
        _ ≤ Real.exp 128 * Real.exp (p+1) * Real.exp (p+1) * Real.exp p := by
          exact mul_le_mul (mul_le_mul (mul_le_mul h128 hD' (by positivity)
            (Real.exp_nonneg _)) hL' (by positivity) (by positivity)) hi
            (by positivity) (by positivity)
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hden0 : 0 < 128 * ((D : ℝ) + 1) * (Lip + 1) := by positivity
    apply hδ.trans
    have hinv := one_div_le_one_div_of_le (mul_pos hden0 (inv_pos.mpr hgain0)) hden
    simpa only [one_div, mul_inv_rev, inv_inv, Real.exp_neg, div_eq_mul_inv, one_mul] using hinv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

theorem patchValue_eq_at_residual {b : Fin d → ℤ}
    (hb : ∀ i, |A.residual b i| ≤ 1 / 4) :
    A.patchValue Φ = Φ.value (A.residual b) := by
  apply tsum_eq_single b
  intro c hcb
  by_contra hc
  exact hcb (A.integer_unique (by norm_num) (Φ.support _ hc) hb)

theorem patchValue_dist_le (Ψ : PatchKernel d) {δ : ℝ} (hδ : 0 ≤ δ)
    (herror : ∀ z, dist (Φ.value z) (Ψ.value z) ≤ δ) :
    dist (A.patchValue Φ) (A.patchValue Ψ) ≤ δ := by
  by_cases h : ∃ b : Fin d → ℤ, Φ.value (A.residual b) ≠ 0 ∨ Ψ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    have hres : ∀ i, |A.residual b i| ≤ 1 / 4 := hb.elim (Φ.support _) (Ψ.support _)
    rw [A.patchValue_eq_at_residual Φ hres, A.patchValue_eq_at_residual Ψ hres]
    exact herror _
  · have hΦ : ∀ b, Φ.value (A.residual b) = 0 := by
      intro b
      by_contra hb
      exact h ⟨b, Or.inl hb⟩
    have hΨ : ∀ b, Ψ.value (A.residual b) = 0 := by
      intro b
      by_contra hb
      exact h ⟨b, Or.inr hb⟩
    rw [A.patchValue_eq_zero Φ hΦ, A.patchValue_eq_zero Ψ hΨ, dist_self]
    exact hδ

end TriangularSlots

end Erdos3

end

section

namespace Erdos3

variable {D E : ℕ}

theorem append_slotPrefix_slotSuffix {R : Type*} (x : Fin (D + E) → R) :
    Fin.append (slotPrefix x) (slotSuffix x) = x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [slotPrefix, slotSuffix]

namespace TriangularSlots

theorem append_residual (A : TriangularSlots D) (B : (Fin D → ℝ) → TriangularSlots E)
    (b : Fin D → ℤ) (c : Fin E → ℤ) :
    (A.append B).residual (Fin.append b c) =
      Fin.append (A.residual b) ((B (fun i => (b i : ℝ))).residual c) := by
  have hp : slotPrefix (D := D) (E := E) (fun j => ((Fin.append b c j : ℤ) : ℝ)) =
      fun i => (b i : ℝ) := by ext i; simp [slotPrefix]
  have hs : slotSuffix (D := D) (E := E) (fun j => ((Fin.append b c j : ℤ) : ℝ)) =
      fun i => (c i : ℝ) := by ext i; simp [slotSuffix]
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [residual, append, hp, hs]

end TriangularSlots

theorem dist_append_same_right_le (x y : Fin D → ℝ) (z : Fin E → ℝ) :
    dist (Fin.append x z) (Fin.append y z) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using dist_le_pi_dist x y j
  · simp

namespace PatchKernel

theorem freeze_value_dist_le (Φ : PatchKernel (D + E)) (x y : Fin D → ℝ)
    (z : Fin E → ℝ) :
    dist ((Φ.freeze x).value z) ((Φ.freeze y).value z) ≤ Φ.lip * dist x y :=
  (Φ.lipschitz.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (dist_append_same_right_le x y z) Φ.lip.coe_nonneg)

end PatchKernel

end Erdos3

end

section

namespace Erdos3

namespace TriangularSlots

variable {D E : ℕ}

theorem patchValue_freeze_dist_le (A : TriangularSlots E) (Φ : PatchKernel (D + E))
    (x y : Fin D → ℝ) :
    dist (A.patchValue (Φ.freeze x)) (A.patchValue (Φ.freeze y)) ≤ Φ.lip * dist x y :=
  A.patchValue_dist_le _ _ (mul_nonneg Φ.lip.coe_nonneg dist_nonneg)
    (Φ.freeze_value_dist_le x y)

theorem contributing_prefix_eq (A : TriangularSlots D)
    (B : (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (b : Fin D → ℤ) (hb : ∀ i, |A.residual b i| ≤ 1 / 3)
    {v : Fin (D + E) → ℤ} (hv : Φ.value ((A.append B).residual v) ≠ 0) :
    slotPrefix v = b := by
  have hr := A.append_residual B (slotPrefix v) (slotSuffix v)
  rw [append_slotPrefix_slotSuffix] at hr
  have hp : ∀ i, |A.residual (slotPrefix v) i| ≤ 1 / 4 := by
    intro i
    have h := Φ.support _ hv (i.castAdd E)
    simpa only [hr, Fin.append_left] using h
  exact A.integer_unique (by norm_num) hp hb

theorem patchValue_append_eq (A : TriangularSlots D)
    (B : (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (b : Fin D → ℤ) (hb : ∀ i, |A.residual b i| ≤ 1 / 3) :
    (A.append B).patchValue Φ =
      (B (fun i => (b i : ℝ))).patchValue (Φ.freeze (A.residual b)) := by
  by_cases h : ∃ v : Fin (D + E) → ℤ, Φ.value ((A.append B).residual v) ≠ 0
  · obtain ⟨v, hv⟩ := h
    have hp := A.contributing_prefix_eq B Φ b hb hv
    have hvform : Fin.append b (slotSuffix v) = v := by
      rw [← hp, append_slotPrefix_slotSuffix]
    have heq : Φ.value ((A.append B).residual v) =
        (Φ.freeze (A.residual b)).value ((B (fun i => (b i : ℝ))).residual (slotSuffix v)) := by
      rw [← hvform, A.append_residual]
      simp only [slotSuffix_append]
      rfl
    rw [(A.append B).patchValue_eq_of_nonzero Φ hv,
      (B (fun i => (b i : ℝ))).patchValue_eq_of_nonzero _ (by rwa [← heq]), heq]
  · have hz : ∀ v, Φ.value ((A.append B).residual v) = 0 := by simpa using h
    have ht : ∀ c, (Φ.freeze (A.residual b)).value
        ((B (fun i => (b i : ℝ))).residual c) = 0 := by
      intro c
      have heq := hz (Fin.append b c)
      simpa only [A.append_residual, PatchKernel.freeze] using heq
    rw [(A.append B).patchValue_eq_zero Φ hz,
      (B (fun i => (b i : ℝ))).patchValue_eq_zero _ ht]

theorem patchValue_freeze_prefix (A : TriangularSlots D)
    (B : (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (b : Fin D → ℤ) (z : Fin D → ℝ) {ε : ℝ}
    (hz : ∀ i, |z i| ≤ 1 / 4) (hε : ε < 1 / 12)
    (hclose : dist (A.residual b) z ≤ ε) :
    dist ((A.append B).patchValue Φ)
      ((B (fun i => (b i : ℝ))).patchValue (Φ.freeze z)) ≤ Φ.lip * ε := by
  have hb : ∀ i, |A.residual b i| ≤ 1 / 3 := by
    intro i
    have hcoord := (dist_le_pi_dist (A.residual b) z i).trans hclose
    rw [Real.dist_eq] at hcoord
    have htriangle : |A.residual b i| ≤ |A.residual b i - z i| + |z i| := by
      simpa only [sub_add_cancel] using abs_add_le (A.residual b i - z i) (z i)
    linarith [hz i]
  rw [A.patchValue_append_eq B Φ b hb]
  exact (patchValue_freeze_dist_le _ Φ _ _).trans
    (mul_le_mul_of_nonneg_left hclose Φ.lip.coe_nonneg)

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {D E d : ℕ}

theorem append_take_drop (A : TriangularSlots (D + E)) :
    A.takePrefix.append A.dropPrefix = A := by
  apply ext
  intro x i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [append, takePrefix, Fin.append_left]
    apply A.lower
    intro k
    refine Fin.addCases (fun l hk => ?_) (fun l hk => ?_) k
    · simp [slotPrefix]
    · have hbad : D + l.val < j.val := by simpa only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] using hk
      omega
  · simp only [append, dropPrefix, Fin.append_right, append_slotPrefix_slotSuffix]

theorem takePrefix_residual (A : TriangularSlots (D + E)) (v : Fin (D + E) → ℤ) :
    A.takePrefix.residual (slotPrefix v) = slotPrefix (A.residual v) := by
  have h := A.takePrefix.append_residual A.dropPrefix (slotPrefix v) (slotSuffix v)
  rw [append_take_drop, append_slotPrefix_slotSuffix] at h
  have hp := congrArg slotPrefix h
  simpa only [slotPrefix_append] using hp.symm

end Erdos3.TriangularSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineLowestLayer
namespace OAI

section

namespace Erdos3

namespace TriangularSlots

variable {D : ℕ}

theorem affineBlock_residual (M : Matrix (Fin D) (Fin D) ℝ)
    (hM : ∀ i j, i ≤ j → M i j = 0) (P : Fin D → ℝ) (b : Fin D → ℤ) :
    (affineBlock M hM P).residual b = (1 - M).mulVec ((fun i => (b i : ℝ)) - P) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  ext i
  simp only [residual, affineBlock, Pi.sub_apply, Pi.add_apply]
  ring

end TriangularSlots

theorem affine_residual_shift_identity {T : Type*} {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (P : T → Fin D → ℝ) (I : T → Fin D → ℤ) (t₀ t : T) (b₀ : Fin D → ℤ) :
    (TriangularSlots.affineBlock M hM (P t)).residual (shiftedIntegerBlock I t₀ b₀ t) -
      (TriangularSlots.affineBlock M hM (P t₀)).residual b₀ =
    -(1 - M).mulVec ((P t - fun i => (I t i : ℝ)) - (P t₀ - fun i => (I t₀ i : ℝ))) := by
  rw [TriangularSlots.affineBlock_residual, TriangularSlots.affineBlock_residual,
    ← Matrix.mulVec_sub, ← Matrix.mulVec_neg]
  congr 1
  ext i
  simp only [shiftedIntegerBlock, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Int.cast_sub, Int.cast_add]
  ring

theorem affine_residual_shift_dist {T : Type*} {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (P : T → Fin D → ℝ) (I : T → Fin D → ℤ) (t₀ t : T) (b₀ : Fin D → ℤ) :
    dist ((TriangularSlots.affineBlock M hM (P t)).residual (shiftedIntegerBlock I t₀ b₀ t))
      ((TriangularSlots.affineBlock M hM (P t₀)).residual b₀) =
    ‖(1 - M).mulVec ((P t - fun i => (I t i : ℝ)) - (P t₀ - fun i => (I t₀ i : ℝ)))‖ := by
  rw [dist_eq_norm, affine_residual_shift_identity, norm_neg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

theorem freezePrefix_center_eval {w : Fin (D + E) → ℕ}
    (A : PolynomialSlots σ (D + E) w) (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E)))
    (t : σ → ℝ) (x : Fin E → ℝ) (i : Fin E) :
    ((A.freezePrefix I hI).slots t).center x i =
      (A.slots t).center (Fin.append (fun j => aeval t (I j)) x) (i.natAdd D) := by
  simp only [slots, freezePrefix, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f : σ ⊕ Fin (D + i.val) → ℝ => aeval f (A.center (i.natAdd D)))
  funext v
  cases v with
  | inl a => simp [prefixSubstitution]
  | inr j =>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_left]
      change aeval (Sum.elim t (fun j => x (earlierSlot i j)))
        (aeval (fun a => (X (Sum.inl a) : MvPolynomial (σ ⊕ Fin i.val) ℝ)) (I k)) =
        Fin.append (fun j => aeval t (I j)) x (k.castAdd E)
      rw [MvPolynomial.comp_aeval_apply, Fin.append_left]
      simp only [aeval_X, Sum.elim_inl]
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_right]
      change aeval (Sum.elim t (fun j => x (earlierSlot i j)))
        (X (Sum.inr k) : MvPolynomial (σ ⊕ Fin i.val) ℝ) =
        Fin.append (fun j => aeval t (I j)) x ((earlierSlot i k).natAdd D)
      simp only [aeval_X, Sum.elim_inr, Fin.append_right]

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

theorem slots_freezePrefix {σ : Type*} {D E : ℕ} {w : Fin (D + E) → ℕ}
    (A : PolynomialSlots σ (D + E) w) (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E)))
    (t : σ → ℝ) :
    (A.freezePrefix I hI).slots t = (A.slots t).dropPrefix (fun j => aeval t (I j)) := by
  apply TriangularSlots.ext
  intro x i
  exact A.freezePrefix_center_eval I hI t x i

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

theorem freezePrefix_value (A : PolynomialPatch σ s (D + E))
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (z : Fin D → ℝ) (t : σ → ℝ) :
    (A.freezePrefix I (by exact hI) z).value t =
      ((A.form.slots t).dropPrefix (fun j => aeval t (I j))).patchValue (A.kernel.freeze z) := by
  change ((A.form.freezePrefix I hI).slots t).patchValue _ = _
  rw [PolynomialSlots.slots_freezePrefix]
  rfl

theorem freezePrefix_error (A : PolynomialPatch σ s (D + E))
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (z : Fin D → ℝ) (t : σ → ℝ) (b : Fin D → ℤ) {ε : ℝ}
    (hint : ∀ j, aeval t (I j) = (b j : ℝ))
    (hz : ∀ i, |z i| ≤ 1 / 4) (hε : ε < 1 / 12)
    (hclose : dist ((A.form.slots t).takePrefix.residual b) z ≤ ε) :
    dist (A.value t) ((A.freezePrefix I hI z).value t) ≤ A.kernel.lip * ε := by
  have h := (A.form.slots t).takePrefix.patchValue_freeze_prefix
    (A.form.slots t).dropPrefix A.kernel b z hz hε hclose
  rw [TriangularSlots.append_take_drop] at h
  rw [freezePrefix_value, show (fun j => aeval t (I j)) = (fun j => (b j : ℝ)) from funext hint]
  exact h

end PolynomialPatch

theorem shiftedParameterPolynomials_degree {σ : Type*} {D : ℕ}
    (I : Fin D → MvPolynomial σ ℝ) (t₀ : σ → ℝ) (b₀ : Fin D → ℤ)
    (w : Fin D → ℕ)
    (hI : ∀ i, I i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) :
    ∀ i, shiftedParameterPolynomials I t₀ b₀ i ∈ weightedSupportLE (fun _ : σ => 1) (w i) := by
  intro i
  exact (weightedSupportLE _ _).sub_mem
    ((weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _) (hI i))
    (weightedSupportLE_C _ _ _)

theorem shiftedParameterPolynomials_eval {σ : Type*} {D : ℕ}
    (I : Fin D → MvPolynomial σ ℝ) (t₀ t : σ → ℝ) (b₀ : Fin D → ℤ) :
    ∀ i, aeval t (shiftedParameterPolynomials I t₀ b₀ i) =
      (b₀ i : ℝ) + aeval t (I i) - aeval t₀ (I i) := by
  intro i
  simp only [shiftedParameterPolynomials, map_add, map_sub, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply]

namespace PolynomialPatch

theorem exists_freeze_affine_layer {σ : Type*} {s D E : ℕ}
    (A : PolynomialPatch σ s (D + E))
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (U : Set (σ → ℝ)) (P : (σ → ℝ) → Fin D → ℝ)
    (I : Fin D → MvPolynomial σ ℝ) (v : (σ → ℝ) → Fin D → ℤ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (hint : ∀ t ∈ U, ∀ j, aeval t (I j) = (v t j : ℝ))
    (hhead : ∀ t ∈ U, (A.form.slots t).takePrefix = TriangularSlots.affineBlock M hM (P t))
    (t₀ : σ → ℝ) (ht₀ : t₀ ∈ U) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots t₀).residual bref) ≠ 0)
    {ε : ℝ} (hε : ε < 1 / 12)
    (hosc : ∀ t ∈ U, ‖(1 - M).mulVec
      ((P t - fun j => aeval t (I j)) - (P t₀ - fun j => aeval t₀ (I j)))‖ ≤ ε) :
    ∃ F : PolynomialPatch σ s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ t ∈ U, dist (A.value t) (F.value t) ≤ A.kernel.lip * ε := by
  let b₀ := slotPrefix bref
  let z := (A.form.slots t₀).takePrefix.residual b₀
  let J := shiftedParameterPolynomials I t₀ b₀
  have hJ : ∀ j, J j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)) :=
    shiftedParameterPolynomials_degree I t₀ b₀ _ hI
  refine ⟨A.freezePrefix J hJ z, rfl, (fun _ => rfl), ?_⟩
  have hz : ∀ i, |z i| ≤ 1 / 4 := by
    intro i
    have h := A.kernel.support _ href (i.castAdd E)
    simpa only [z, b₀, TriangularSlots.takePrefix_residual, slotPrefix] using h
  intro t ht
  have hJvalue : ∀ j, aeval t (J j) = (shiftedIntegerBlock v t₀ b₀ t j : ℝ) := by
    intro j
    simp only [J, shiftedParameterPolynomials_eval, hint t ht, hint t₀ ht₀,
      shiftedIntegerBlock, Pi.add_apply, Pi.sub_apply, Int.cast_sub, Int.cast_add]
  apply A.freezePrefix_error J hJ z t (shiftedIntegerBlock v t₀ b₀ t) hJvalue hz hε
  change dist ((A.form.slots t).takePrefix.residual (shiftedIntegerBlock v t₀ b₀ t))
    ((A.form.slots t₀).takePrefix.residual b₀) ≤ ε
  rw [hhead t ht, hhead t₀ ht₀, affine_residual_shift_dist]
  simpa only [hint t ht, hint t₀ ht₀] using hosc t ht

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

@[simp] theorem constant_value (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (t : σ → ℝ) :
    (constant σ s c hc).value t = c := by
  exact ((constant σ s c hc).form.slots t).patchValue_eq_at_residual (constant σ s c hc).kernel
    (b := 0) (fun i => Fin.elim0 i)

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateCopySum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coordinateCopySum_abs_le {C J : Type*} [Fintype C] [DecidableEq J]
    (label : C → J) {x : C → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ c, |x c| ≤ δ) (j : J) :
    |coordinateCopySum label x j| ≤ Fintype.card C * δ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ c, |if label c = j then x c else 0|) ≤ ∑ _c : C, δ := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs <;> simp_all
    _ = _ := by simp

theorem coordinateCopySum_map {C J R S : Type*} [Fintype C] [DecidableEq J]
    [CommRing R] [CommRing S] (label : C → J) (f : R →+* S) (x : C → R) (j : J) :
    f (coordinateCopySum label x j) = coordinateCopySum label (fun c => f (x c)) j := by
  simp only [coordinateCopySum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

theorem coordinateCopySum_polynomial_degree {C J I R : Type*} [Fintype C] [DecidableEq J]
    [CommRing R] (label : C → J) (p : C → MvPolynomial I R) {d : ℕ}
    (hp : ∀ c, (p c).totalDegree ≤ d) (j : J) :
    (coordinateCopySum label p j).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro c _
  split_ifs
  · exact hp c
  · simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct
open VectorPolynomial

namespace VectorPolynomial

theorem integerCoordinates_eval_real {I J : Type*} [Fintype J]
    (ip : J → MvPolynomial I ℤ) (x : I → ℝ) :
    eval x (integerCoordinates ip) =
      fun j => MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (ip j)) := by
  have he : eval₂ x (integerCoordinates ip) = eval x (integerCoordinates ip) := by
    simpa using (eval₂_algebraMap (S := ℝ) x (integerCoordinates ip))
  rw [← he, integerCoordinates, eval₂_ofCoordinates, Pi.basisFun_equivFun]
  rfl

end VectorPolynomial

namespace RankPreparationFamily

theorem polynomial_eval {I J : Type} [DecidableEq J] {s : ℕ}
    (L : RankPreparationFamily I J s) (x : I → ℝ) : eval x L.polynomial = L.value x := by
  simp only [polynomial, map_sum, eval_map]
  rfl

end RankPreparationFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PreparedIntegerRemainder
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {X J : Type} [Fintype J] [DecidableEq J] {m : ℕ}
variable (L : RankPreparationFamily X J m)

omit [Fintype J] in
theorem integerRemainder_degree (ip : J → MvPolynomial X ℤ)
    (hip : ∀ j, (ip j).totalDegree ≤ m) (β : ∀ u, (L u).Coord → MvPolynomial X ℤ)
    (hβ : ∀ u i, (β u i).totalDegree ≤ u.val + 1) (j : J) :
    (L.integerRemainder ip β j).totalDegree ≤ m := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (hip j)
  rw [Finset.sum_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro u _
  exact (coordinateCopySum_polynomial_degree (L u).label (β u) (hβ u) j).trans
    (Nat.succ_le_of_lt u.isLt)

omit [Fintype J] in
theorem integerRemainder_eval (ip : J → MvPolynomial X ℤ)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ) (x : X → ℝ) (j : J) :
    MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) =
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (ip j)) +
        ∑ u, coordinateCopySum (L u).label
          (fun i => MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))) j := by
  let f : MvPolynomial X ℤ →+* ℝ :=
    (MvPolynomial.eval x).comp (MvPolynomial.map (Int.castRingHom ℝ))
  change f (ip j + (∑ u, coordinateCopySum (L u).label (β u)) j) = _
  rw [Finset.sum_apply, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  exact coordinateCopySum_map (L u).label f (β u) j

theorem integerRemainder_bound
    (P E : VectorPolynomial X ℝ (J → ℝ)) (ip : J → MvPolynomial X ℤ) (c : J → ℝ)
    (hP : P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ) (center : ∀ u, (L u).Coord → ℝ)
    (ε : Fin m → ℝ) (hε : ∀ u, 0 ≤ ε u) {δ : ℝ} (Ω : Set (X → ℝ))
    (hsmall : ∀ x ∈ Ω, ∀ u i, |eval x (L u).poly i - center u i -
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u)
    (herr : ∀ x ∈ Ω, ∀ j, |eval x E j| ≤ δ) :
    ∀ x ∈ Ω, ∀ j,
      |eval x P j - MvPolynomial.eval x
          (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) -
        (c j + ∑ u, coordinateCopySum (L u).label (center u) j)| ≤
          (∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ := by
  intro x hx j
  let r : ∀ u, (L u).Coord → ℝ := fun u i => eval x (L u).poly i - center u i -
    MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))
  have heq : eval x P j - MvPolynomial.eval x
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) -
      (c j + ∑ u, coordinateCopySum (L u).label (center u) j) =
      (∑ u, coordinateCopySum (L u).label (r u) j) + eval x E j := by
    rw [hP, map_add, map_add, map_add, polynomial_eval, integerCoordinates_eval_real,
      integerRemainder_eval]
    simp only [Pi.add_apply, eval_tmul, map_one, one_smul]
    have hr (u) : r u = eval x (L u).poly - center u -
        (fun i => MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))) := rfl
    simp only [hr, map_sub, Pi.sub_apply, Finset.sum_sub_distrib, value,
      RankPreparationLayer.value, Finset.sum_apply]
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  apply add_le_add _ (herr x hx j)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro u _
  exact coordinateCopySum_abs_le (L u).label (hε u) (hsmall x hx u) j

theorem integerRemainder_oscillation
    (P E : VectorPolynomial X ℝ (J → ℝ)) (ip : J → MvPolynomial X ℤ) (c : J → ℝ)
    (hP : P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ) (center : ∀ u, (L u).Coord → ℝ)
    (ε : Fin m → ℝ) (hε : ∀ u, 0 ≤ ε u) {δ : ℝ} (hδ : 0 ≤ δ) (Ω : Set (X → ℝ))
    (hsmall : ∀ x ∈ Ω, ∀ u i, |eval x (L u).poly i - center u i -
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u)
    (herr : ∀ x ∈ Ω, ∀ j, |eval x E j| ≤ δ) (x₀ : X → ℝ) (hx₀ : x₀ ∈ Ω) :
    ∀ x ∈ Ω,
      ‖(eval x P - fun j => MvPolynomial.eval x
          (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j))) -
        (eval x₀ P - fun j => MvPolynomial.eval x₀
          (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)))‖ ≤
            2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ) := by
  intro x hx
  have hsum : 0 ≤ ∑ u, (Fintype.card (L u).Coord : ℝ) * ε u :=
    Finset.sum_nonneg (fun u _ => mul_nonneg (Nat.cast_nonneg _) (hε u))
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [Real.norm_eq_abs]
  let a := c j + ∑ u, coordinateCopySum (L u).label (center u) j
  have hxBound := L.integerRemainder_bound P E ip c hP β center ε hε Ω hsmall herr x hx j
  have h₀Bound := L.integerRemainder_bound P E ip c hP β center ε hε Ω hsmall herr x₀ hx₀ j
  have heq : ((eval x P - fun j => MvPolynomial.eval x
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j))) -
      (eval x₀ P - fun j => MvPolynomial.eval x₀
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)))) j =
      (eval x P j - MvPolynomial.eval x
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) - a) -
      (eval x₀ P j - MvPolynomial.eval x₀
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) - a) := by
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowestPolynomialLayer
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

namespace PolynomialPatch

variable {σ : Type*} {s D E h : ℕ}

theorem LowestLayerModel.exists_freeze (A : PolynomialPatch σ s (D + E))
    (L : A.LowestLayerModel h) (U : Set (σ → ℝ))
    (I : Fin D → MvPolynomial σ ℝ) (v : (σ → ℝ) → Fin D → ℤ)
    (hI : ∀ i, I i ∈ weightedSupportLE (fun _ : σ => 1) h)
    (hint : ∀ t ∈ U, ∀ i, aeval t (I i) = (v t i : ℝ))
    (t₀ : σ → ℝ) (ht₀ : t₀ ∈ U) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots t₀).residual bref) ≠ 0)
    {ε : ℝ} (hε : ε < 1 / 12)
    (hosc : ∀ t ∈ U, ‖(1 - L.matrix).mulVec
      ((fun i => aeval t (L.origin i) - aeval t (I i)) -
        (fun i => aeval t₀ (L.origin i) - aeval t₀ (I i)))‖ ≤ ε) :
    ∃ F : PolynomialPatch σ s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ t ∈ U, dist (A.value t) (F.value t) ≤ A.kernel.lip * ε := by
  apply A.exists_freeze_affine_layer L.matrix L.strict U
    (fun t i => aeval t (L.origin i)) I v
    (fun i => by rw [L.weights i]; exact hI i) hint
    (fun t _ => L.form_eq t) t₀ ht₀ bref href hε
  exact hosc

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.TriangularAffineReset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d : ℕ}

theorem earlierSlotMatrix_apply_lt {R : Type*} [CommRing R]
    (m : (i : Fin d) → Fin i.val → R) (i j : Fin d) (hji : j < i) :
    earlierSlotMatrix m i j = m i ⟨j.val, hji⟩ := by
  classical
  unfold earlierSlotMatrix
  rw [Finset.sum_eq_single (⟨j.val, hji⟩ : Fin i.val)]
  · simp [earlierSlot]
  · intro k _ hk
    apply if_neg
    intro heq
    apply hk
    exact Fin.ext (congrArg (fun t : Fin d => t.val) heq)
  · simp

theorem unitLower_mulVec {R : Type*} [CommRing R]
    (T : Matrix (Fin d) (Fin d) R) (htri : T.IsLowerTriangular)
    (hdiag : ∀ i, T i i = 1) (v : Fin d → R) (i : Fin d) :
    T.mulVec v i = v i + ∑ k : Fin i.val, T i (earlierSlot i k) * v (earlierSlot i k) := by
  classical
  have hT : T = 1 + earlierSlotMatrix (fun i k => T i (earlierSlot i k)) := by
    ext a b
    by_cases hba : b < a
    · rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne.symm,
        earlierSlotMatrix_apply_lt _ a b hba, zero_add]
      rfl
    · rw [Matrix.add_apply, earlierSlotMatrix_strict _ a b (le_of_not_gt hba), add_zero]
      by_cases hab : a = b
      · subst b
        simp [hdiag]
      · have hablt : a < b := lt_of_le_of_ne (le_of_not_gt hba) hab
        rw [htri hablt, Matrix.one_apply_ne hab]
  conv_lhs =>
    rw [hT, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, earlierSlotMatrix_mulVec]

theorem triangularReductionMatrix_above (T : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) (hij : i < j) : triangularReductionMatrix T i j = 0 := by
  unfold triangularReductionMatrix
  rw [reducedLatticeColumn]
  simp only [if_pos hij]

theorem triangularReductionMatrix_diag (T : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) : triangularReductionMatrix T i i = 1 := by
  unfold triangularReductionMatrix
  rw [reducedLatticeColumn]
  simp

theorem triangularReductionMatrix_det (T : Matrix (Fin d) (Fin d) ℝ) :
    (triangularReductionMatrix T).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (triangularReductionMatrix_above T)]
  exact Finset.prod_eq_one (fun i _ => triangularReductionMatrix_diag T i)

theorem reducedTriangularMatrix_entry (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i j : Fin d) :
    reducedTriangularMatrix T i j = (triangularReductionMatrix T i j : ℝ) +
      ∑ k : Fin i.val, T i (earlierSlot i k) *
        (triangularReductionMatrix T (earlierSlot i k) j : ℝ) := by
  exact unitLower_mulVec T htri hdiag (fun k => (triangularReductionMatrix T k j : ℝ)) i

theorem reducedTriangularMatrix_above (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i j : Fin d)
    (hij : i < j) : reducedTriangularMatrix T i j = 0 := by
  rw [reducedTriangularMatrix_entry T htri hdiag,
    triangularReductionMatrix_above T i j hij, Int.cast_zero, zero_add]
  apply Finset.sum_eq_zero
  intro k _
  rw [triangularReductionMatrix_above T (earlierSlot i k) j
    (lt_trans (show earlierSlot i k < i from k.isLt) hij), Int.cast_zero, mul_zero]

theorem reducedTriangularMatrix_diag (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i : Fin d) :
    reducedTriangularMatrix T i i = 1 := by
  rw [reducedTriangularMatrix_entry T htri hdiag, triangularReductionMatrix_diag,
    Int.cast_one]
  have hz : (∑ k : Fin i.val, T i (earlierSlot i k) *
      (triangularReductionMatrix T (earlierSlot i k) i : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [triangularReductionMatrix_above T (earlierSlot i k) i k.isLt,
      Int.cast_zero, mul_zero]
  rw [hz, add_zero]

theorem reducedTriangularMatrix_lower_bound (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i j : Fin d)
    (hji : j < i) : |reducedTriangularMatrix T i j| ≤ 1 / 2 := by
  rw [reducedTriangularMatrix_entry T htri hdiag]
  have hu : triangularReductionMatrix T i j =
      -round (∑ k : Fin i.val, T i (earlierSlot i k) *
        (triangularReductionMatrix T (earlierSlot i k) j : ℝ)) := by
    unfold triangularReductionMatrix
    rw [reducedLatticeColumn]
    simp only [if_neg (not_lt_of_ge hji.le), if_neg hji.ne.symm]
  rw [hu, Int.cast_neg, neg_add_eq_sub]
  exact abs_sub_round _

theorem reducedTriangularMatrix_bound (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i j : Fin d) :
    |reducedTriangularMatrix T i j| ≤ 1 := by
  rcases lt_trichotomy i j with h | h | h
  · simp [reducedTriangularMatrix_above T htri hdiag i j h]
  · subst j
    simp [reducedTriangularMatrix_diag T htri hdiag]
  · exact (reducedTriangularMatrix_lower_bound T htri hdiag i j h).trans (by norm_num)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {d : ℕ}

theorem bounded_matrix_mulVec_lipschitz (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : ∀ i j, |T i j| ≤ 1) : LipschitzWith (d : ℝ≥0) T.mulVec := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (T.mulVec x) (T.mulVec y) ≤ (d : ℝ) * dist x y
  apply (dist_pi_le_iff (mul_nonneg (Nat.cast_nonneg d) dist_nonneg)).mpr
  intro i
  simp only [Real.dist_eq, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |T i j * x j - T i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, dist x y := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul]
      have hj : |x j - y j| ≤ dist x y := by
        simpa only [Real.dist_eq] using dist_le_pi_dist x y j
      exact (mul_le_mul (hT i j) hj (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (d : ℝ) * dist x y := by simp

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {d : ℕ}

theorem integerMatrix_cast_mul_inv (U : Matrix (Fin d) (Fin d) ℤ)
    (hU : IsUnit U.det) :
    U.map (Int.castRingHom ℝ) * U⁻¹.map (Int.castRingHom ℝ) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv U hU]
  exact Matrix.map_one _ (map_zero (Int.castRingHom ℝ)) (map_one (Int.castRingHom ℝ))

theorem real_basis_change_residual (T : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnit U.det) (x y : Fin d → ℝ) :
    T.mulVec (x - (U.map (Int.castRingHom ℝ)).mulVec y) =
      (T * U.map (Int.castRingHom ℝ)).mulVec
        ((U⁻¹.map (Int.castRingHom ℝ)).mulVec x - y) := by
  conv_rhs =>
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      integerMatrix_cast_mul_inv U hU, Matrix.one_mulVec]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedLayerFreezing
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch.LowestLayerModel

variable {σ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}
    (L : A.LowestLayerModel h)

theorem residualMatrix_lower : (1 - L.matrix).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  simp [Matrix.sub_apply, Matrix.one_apply_ne hij.ne, L.strict i j hij.le]

theorem residualMatrix_diag (i : Fin D) : (1 - L.matrix) i i = 1 := by
  simp [Matrix.sub_apply, L.strict i i le_rfl]

theorem integerChange_det : L.integerChange.det = 1 :=
  triangularReductionMatrix_det (1 - L.matrix)

theorem normalizedOrigin_residual (t : σ → ℝ) (y : Fin D → ℝ) :
    (1 - L.matrix).mulVec ((fun i => aeval t (L.origin i)) -
      (L.integerChange.map (Int.castRingHom ℝ)).mulVec y) =
      (reducedTriangularMatrix (1 - L.matrix)).mulVec
        ((fun i => aeval t (L.normalizedOrigin i)) - y) := by
  have hU : IsUnit L.integerChange.det := by rw [L.integerChange_det]; exact isUnit_one
  simpa only [normalizedOrigin, polynomialMatrixAction_eval, integerChange,
    reducedTriangularMatrix] using real_basis_change_residual (1 - L.matrix)
      L.integerChange hU (fun i => aeval t (L.origin i)) y

theorem exists_freeze_normalized (U : Set (σ → ℝ))
    (J : Fin D → MvPolynomial σ ℝ) (v : (σ → ℝ) → Fin D → ℤ)
    (hJ : ∀ i, J i ∈ weightedSupportLE (fun _ : σ => 1) h)
    (hint : ∀ t ∈ U, ∀ i, aeval t (J i) = (v t i : ℝ))
    (t₀ : σ → ℝ) (ht₀ : t₀ ∈ U) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots t₀).residual bref) ≠ 0)
    {ε : ℝ} (hε : (D : ℝ) * ε < 1 / 12)
    (hosc : ∀ t ∈ U, ‖(fun i => aeval t (L.normalizedOrigin i) - aeval t (J i)) -
      (fun i => aeval t₀ (L.normalizedOrigin i) - aeval t₀ (J i))‖ ≤ ε) :
    ∃ F : PolynomialPatch σ s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ t ∈ U, dist (A.value t) (F.value t) ≤ A.kernel.lip * ((D : ℝ) * ε) := by
  let I := polynomialMatrixAction (L.integerChange.map (Int.castRingHom ℝ)) J
  let w (t : σ → ℝ) := L.integerChange.mulVec (v t)
  have hI : ∀ i, I i ∈ weightedSupportLE (fun _ : σ => 1) h :=
    polynomialMatrixAction_degree _ J hJ
  have hIeval : ∀ t ∈ U, ∀ i, aeval t (I i) = (w t i : ℝ) := by
    intro t ht i
    have heval := congrFun (polynomialMatrixAction_eval
      (L.integerChange.map (Int.castRingHom ℝ)) J t) i
    change aeval t (I i) = _ at heval
    rw [heval]
    simp only [hint t ht]
    exact (RingHom.map_mulVec (Int.castRingHom ℝ) L.integerChange (v t) i).symm
  have hres (t : σ → ℝ) :
      (1 - L.matrix).mulVec (fun i => aeval t (L.origin i) - aeval t (I i)) =
        (reducedTriangularMatrix (1 - L.matrix)).mulVec
          (fun i => aeval t (L.normalizedOrigin i) - aeval t (J i)) := by
    change (1 - L.matrix).mulVec ((fun i => aeval t (L.origin i)) -
      (fun i => aeval t (polynomialMatrixAction _ J i))) = _
    rw [polynomialMatrixAction_eval]
    exact L.normalizedOrigin_residual t (fun i => aeval t (J i))
  apply L.exists_freeze A U I w hI hIeval t₀ ht₀ bref href hε
  intro t ht
  rw [Matrix.mulVec_sub, hres t, hres t₀, ← dist_eq_norm]
  have hbound := (bounded_matrix_mulVec_lipschitz
    (reducedTriangularMatrix (1 - L.matrix))
    (reducedTriangularMatrix_bound (1 - L.matrix) L.residualMatrix_lower
      L.residualMatrix_diag)).dist_le_mul
        (fun i => aeval t (L.normalizedOrigin i) - aeval t (J i))
        (fun i => aeval t₀ (L.normalizedOrigin i) - aeval t₀ (J i))
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (by simpa only [dist_eq_norm] using hosc t ht) (Nat.cast_nonneg D))

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open _root_.MvPolynomial

variable {σ τ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}

theorem reparam_normalizedOrigin (L : A.LowestLayerModel h)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin D) :
    (L.reparam f hf).normalizedOrigin i = aeval f (L.normalizedOrigin i) := by
  simp [normalizedOrigin, polynomialMatrixAction, reparam, integerChange]

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel

open VectorPolynomial _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {X : Type} {s D E m : ℕ} {A : PolynomialPatch X s (D + E)}

theorem exists_freeze_prepared (F : A.LowestLayerModel m)
    (L : RankPreparationFamily X (Fin D) m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ)
    (hβ : ∀ u i, (β u i).totalDegree ≤ u.val + 1)
    (center : ∀ u, (L u).Coord → ℝ) (ε : Fin m → ℝ) (hε : ∀ u, 0 ≤ ε u)
    {δ : ℝ} (hδ : 0 ≤ δ) (Ω : Set (X → ℝ))
    (hinteger : ∀ x ∈ Ω, ∃ z : X → ℤ, x = fun i => (z i : ℝ))
    (hsmall : ∀ x ∈ Ω, ∀ u i, |VectorPolynomial.eval x (L u).poly i - center u i -
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u)
    (herr : ∀ x ∈ Ω, ∀ i, |VectorPolynomial.eval x err i| ≤ δ)
    (x₀ : X → ℝ) (hx₀ : x₀ ∈ Ω) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots x₀).residual bref) ≠ 0)
    (hbudget : (D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ)) < 1 / 12) :
    ∃ A' : PolynomialPatch X s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      ∀ x ∈ Ω, dist (A.value x) (A'.value x) ≤
        A.kernel.lip * ((D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ))) := by
  let Γ := L.integerRemainder ip β
  let J : Fin D → MvPolynomial X ℝ := fun i => MvPolynomial.map (Int.castRingHom ℝ) (Γ i)
  let z : (X → ℝ) → Fin D → ℤ := fun x i => MvPolynomial.eval (fun v => ⌊x v⌋) (Γ i)
  have hJ : ∀ i, J i ∈ weightedSupportLE (fun _ : X => 1) m := by
    intro i
    apply (mem_weightedSupportLE_iff _ _ _).mpr
    change (J i).weightedTotalDegree 1 ≤ m
    rw [MvPolynomial.weightedTotalDegree_one]
    have hmap : (J i).totalDegree ≤ (Γ i).totalDegree :=
      Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    exact hmap.trans (L.integerRemainder_degree ip hip β hβ i)
  have hint : ∀ x ∈ Ω, ∀ i, aeval x (J i) = (z x i : ℝ) := by
    intro x hx i
    obtain ⟨v, rfl⟩ := hinteger x hx
    simp only [J, z, Int.floor_intCast, MvPolynomial.aeval_eq_eval]
    exact (MvPolynomial.map_eval (Int.castRingHom ℝ) v (Γ i)).symm
  apply F.exists_freeze_normalized Ω J z hJ hint x₀ hx₀ bref href hbudget
  have heval (x : X → ℝ) :
      VectorPolynomial.eval x (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) =
        fun i => aeval x (F.normalizedOrigin i) := by
    have he : eval₂ (R := ℝ) x (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) =
        VectorPolynomial.eval x (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) := by
      simpa using (eval₂_algebraMap (S := ℝ) x
        (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin))
    rw [← he, eval₂_ofCoordinates, Pi.basisFun_equivFun]
    rfl
  intro x hx
  have hosc := L.integerRemainder_oscillation
    (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) err ip c hprepare
    β center ε hε hδ Ω hsmall herr x₀ hx₀ x hx
  simpa only [heval, J, Γ, Pi.sub_def, MvPolynomial.aeval_eq_eval] using hosc

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialPullback
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

namespace VectorPolynomial

theorem ofCoordinates_eq_sum_tmul {X J V : Type*} [Fintype J]
    [AddCommGroup V] [Module ℝ V] (e : Module.Basis J ℝ V)
    (p : J → MvPolynomial X ℝ) :
    ofCoordinates (R := ℝ) e p = ∑ j, p j ⊗ₜ[ℝ] e j := by
  apply coefficients.injective
  ext α
  simp only [coefficients_ofCoordinates, map_sum, Finsupp.finsetSum_apply, coefficients_tmul]

theorem substitute_ofCoordinates {X Y J V : Type*} [Fintype J]
    [AddCommGroup V] [Module ℝ V] (f : X → MvPolynomial Y ℝ)
    (e : Module.Basis J ℝ V) (p : J → MvPolynomial X ℝ) :
    substitute f (ofCoordinates (R := ℝ) e p) =
      ofCoordinates e (fun j => MvPolynomial.aeval f (p j)) := by
  simp only [ofCoordinates_eq_sum_tmul, map_sum, substitute_tmul]

theorem substitute_integerCoordinates {X Y J : Type*} [Fintype J]
    (f : X → MvPolynomial Y ℤ) (ip : J → MvPolynomial X ℤ) :
    substitute (fun i => MvPolynomial.map (Int.castRingHom ℝ) (f i)) (integerCoordinates ip) =
      integerCoordinates (fun j => MvPolynomial.aeval f (ip j)) := by
  rw [integerCoordinates, substitute_ofCoordinates, integerCoordinates]
  congr 1
  funext j
  exact (MvPolynomial.map_bind₁ (Int.castRingHom ℝ) f (ip j)).symm

end VectorPolynomial

namespace RankPreparationFamily

variable {X Y J : Type} {m : ℕ}

theorem pullback_polynomial [DecidableEq J] (L : RankPreparationFamily X J m)
    (f : X → MvPolynomial Y ℝ) : (L.pullback f).polynomial = substitute f L.polynomial := by
  simp only [polynomial, map_sum, ← map_substitute]
  rfl

theorem pullback_identity [Fintype J] [DecidableEq J] (L : RankPreparationFamily X J m)
    (P E : VectorPolynomial X ℝ (J → ℝ)) (ip : J → MvPolynomial X ℤ) (c : J → ℝ)
    (hP : P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E)
    (f : X → MvPolynomial Y ℤ) :
    let fr := fun i => MvPolynomial.map (Int.castRingHom ℝ) (f i)
    substitute fr P = (L.pullback fr).polynomial +
      integerCoordinates (fun j => MvPolynomial.aeval f (ip j)) + (1 ⊗ₜ[ℝ] c) + substitute fr E := by
  intro fr
  rw [hP, map_add, map_add, map_add, ← pullback_polynomial,
    substitute_integerCoordinates, substitute_tmul, map_one]

end RankPreparationFamily
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X R : Type*} [Fintype K] [CommRing R] [Nontrivial R]

theorem affineFramePolynomial_support (frame : Option K → X → R) (i : X) :
    affineFramePolynomial frame i ∈ weightedSupportLE (fun _ : K => 1) 1 := by
  apply (mem_weightedSupportLE_iff _ _ _).mpr
  change (affineFramePolynomial frame i).weightedTotalDegree 1 ≤ 1
  rw [MvPolynomial.weightedTotalDegree_one]
  exact affineFramePolynomial_degree frame i

end Erdos3

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel

open VectorPolynomial _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {X K : Type} [Fintype K] {s D E m : ℕ} {A : PolynomialPatch X s (D + E)}

theorem exists_freeze_prepared_affine (F : A.LowestLayerModel m)
    (L : RankPreparationFamily X (Fin D) m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err)
    (frame : Option K → X → ℤ)
    (β : ∀ u, (L u).Coord → MvPolynomial K ℤ)
    (hβ : ∀ u i, (β u i).totalDegree ≤ u.val + 1)
    (center : ∀ u, (L u).Coord → ℝ) (ε : Fin m → ℝ) (hε : ∀ u, 0 ≤ ε u)
    {δ : ℝ} (hδ : 0 ≤ δ) (Ω : Set (K → ℝ))
    (hinteger : ∀ x ∈ Ω, ∃ z : K → ℤ, x = fun i => (z i : ℝ))
    (hsmall : ∀ x ∈ Ω, ∀ u i,
      |VectorPolynomial.eval (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)
        (L u).poly i - center u i -
        MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u)
    (herr : ∀ x ∈ Ω, ∀ i,
      |VectorPolynomial.eval (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)
        err i| ≤ δ)
    (x₀ : K → ℝ) (hx₀ : x₀ ∈ Ω) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots
      (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x₀ k)).residual bref) ≠ 0)
    (hbudget : (D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ)) < 1 / 12) :
    ∃ A' : PolynomialPatch K s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      ∀ x ∈ Ω, dist (A.value
          (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)) (A'.value x) ≤
        A.kernel.lip * ((D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ))) := by
  let fi := affineFramePolynomial frame
  let f := affineFramePolynomial (fun k v => (frame k v : ℝ))
  have hf : ∀ v, f v ∈ weightedSupportLE (fun _ : K => 1) 1 :=
    affineFramePolynomial_support _
  have hmap : (fun v => MvPolynomial.map (Int.castRingHom ℝ) (fi v)) = f :=
    funext (affineFramePolynomial_map (Int.castRingHom ℝ) frame)
  let L' := L.pullback f
  let ip' := fun i => MvPolynomial.aeval fi (ip i)
  have hip' : ∀ i, (ip' i).totalDegree ≤ m := by
    intro i
    exact (aeval_polynomial_totalDegree_le (ip i) fi (hip i) (affineFramePolynomial_degree frame)).trans_eq
      (Nat.mul_one m)
  have hpull : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) (F.reparam f hf).normalizedOrigin =
      L'.polynomial + integerCoordinates ip' + (1 ⊗ₜ[ℝ] c) + substitute f err := by
    have he := L.pullback_identity
      (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) err ip c hprepare fi
    dsimp only at he
    rw [hmap, substitute_ofCoordinates] at he
    have hn : (F.reparam f hf).normalizedOrigin =
        fun i => MvPolynomial.aeval f (F.normalizedOrigin i) :=
      funext (reparam_normalizedOrigin F f hf)
    rw [hn]
    exact he
  have href' : (A.reparam f hf).kernel.value
      (((A.reparam f hf).form.slots x₀).residual bref) ≠ 0 := by
    change A.kernel.value (((A.form.reparam f hf).slots x₀).residual bref) ≠ 0
    rw [PolynomialSlots.reparam_slots]
    simpa only [f, affineFramePolynomial_eval] using href
  obtain ⟨A', hLip, hweight, hval⟩ := (F.reparam f hf).exists_freeze_prepared L' ip' hip' c
    (substitute f err) hpull β hβ center ε hε hδ Ω hinteger
    (by
      intro x hx u i
      change |VectorPolynomial.eval x (substitute f (L u).poly) i - center u i -
        MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u
      rw [eval_substitute]
      simpa only [f, affineFramePolynomial_eval] using hsmall x hx u i)
    (by simpa only [eval_substitute, f, affineFramePolynomial_eval] using herr)
    x₀ hx₀ bref href' hbudget
  refine ⟨A', hLip, hweight, ?_⟩
  intro x hx
  have hv := hval x hx
  rw [PolynomialPatch.reparam_value] at hv
  change dist (A.value (fun v => MvPolynomial.aeval x (f v))) (A'.value x) ≤
    A.kernel.lip * ((D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ))) at hv
  simpa only [f, affineFramePolynomial_eval] using hv

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedLayerScore
namespace OAI

section

namespace Erdos3.PolynomialPatch
open scoped BigOperators

theorem exists_contributing_site_of_pos_score
    {X Ω : Type*} [Fintype Ω] {s d : ℕ}
    (A : PolynomialPatch X s d) (t : Ω → X → ℝ) (score : Ω → ℝ)
    (hscore : 0 < 𝔼 u, score u * A.value (t u)) :
    ∃ u b, A.kernel.value ((A.form.slots (t u)).residual b) ≠ 0 := by
  classical
  by_contra h
  have hz (u : Ω) : A.value (t u) = 0 := by
    have hzero : ∀ b, A.kernel.value ((A.form.slots (t u)).residual b) = 0 := by
      intro b
      by_contra hb
      exact h ⟨u, b, hb⟩
    simp only [value, TriangularSlots.patchValue, hzero, tsum_zero]
  simp [hz] at hscore

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem AllocatedCenteredFramedRecoveredSampleAt.freezing_lifts
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      c a v sample read) :
    ∃ β : ∀ j, J j → MvPolynomial (LayerSamplerVariables G I n B) ℤ,
      (∀ j i, (β j i).totalDegree ≤ j.val + 1) ∧
      (∀ x : LayerSamplerVariables G I n B → ℝ, ∀ j i,
        eval (fun z => (jointIntegerFrame (a,v) none z : ℝ) +
          ∑ k, (jointIntegerFrame (a,v) (some k) z : ℝ) * x k) (poly j) i - (c j).val i =
        mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
          (sample j).1 (sample j).2 x i +
            MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β j i))) ∧
      ∀ x : LayerSamplerVariables G I n B → ℝ,
        (∀ k, |x k| ≤ layerSamplerBox B U b S k) → ∀ j i,
        |eval (fun z => (jointIntegerFrame (a,v) none z : ℝ) +
          ∑ k, (jointIntegerFrame (a,v) (some k) z : ℝ) * x k) (poly j) i - (c j).val i -
          MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β j i))| ≤
            C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
  let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
    fun k z => (jointIntegerFrame (a,v) k z : ℝ)
  have hc : canonicalCoefficientSample U b hb o sample =
      QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (centeredAffineCoefficientArray U poly hm c frame) :=
    h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
  let β := coefficientIntegerFloorPolynomial U b o sample
    (centeredAffineCoefficientArray U poly hm c frame)
  have hβ := canonicalCoefficientSample_floor_polynomial_remainder U b hb o sample
    (centeredAffineCoefficientArray U poly hm c frame) hc
  have heval (x : LayerSamplerVariables G I n B → ℝ) (j : Fin m) (i : J j) :
      eval (fun z => frame none z + ∑ k, frame (some k) z * x k) (poly j) i - (c j).val i =
        mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
          (sample j).1 (sample j).2 x i +
            MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β j i)) := by
    rw [← coefficientRowPolynomial_centered_affine_eval U poly hm hp c frame j i x,
      (hβ j i).1, map_add, mixedLiftPolynomial_eval]
  refine ⟨β, fun j i => (hβ j i).2, heval, ?_⟩
  intro x hx j i
  change |eval (fun z => frame none z + ∑ k, frame (some k) z * x k) (poly j) i -
    (c j).val i - _| ≤ _
  rw [heval, add_sub_cancel_right]
  exact allocatedLayerSupported_polynomial_bound B U b o hR hσ S hσ1 C hC hchart j
    (sample j) (h.2.2.1 j).2 x hx i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationPaddedFreezingLifts
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

private theorem eval_cast {A B : RankPreparationLayer X J} (h : A = B)
    (x : X → ℝ) (i : A.Coord) :
    eval x B.poly (cast (congrArg RankPreparationLayer.Coord h) i) = eval x A.poly i := by
  cases h
  rfl

@[simp] theorem padCoordInclusion_eval (hmq : m ≤ q) (x : X → ℝ)
    (a : Σ j, (L j).Coord) :
    eval x (L.pad q (L.padCoordInclusion hmq a).1).poly (L.padCoordInclusion hmq a).2 =
      eval x (L a.1).poly a.2 :=
  eval_cast (L.pad_apply_castLE hmq a.1).symm x a.2

@[simp] theorem padCoordEquiv_eval (hmq : m ≤ q) (x : X → ℝ)
    (a : Σ j, (L.pad q j).Coord) :
    eval x (L (L.padCoordEquiv hmq a).1).poly (L.padCoordEquiv hmq a).2 =
      eval x (L.pad q a.1).poly a.2 := by
  have h := L.padCoordInclusion_eval hmq x (L.padCoordRestriction a)
  rw [L.padCoordInclusion_restriction hmq a] at h
  exact h.symm

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {X J : Type} {Vars : Type*} {m q : ℕ}
    (L : RankPreparationFamily X J m)

theorem unpadFreezingLifts_degree (hmq : m ≤ q)
    (β : ∀ j, (L.pad q j).Coord → MvPolynomial Vars ℤ)
    (hβ : ∀ j i, (β j i).totalDegree ≤ j.val + 1) :
    ∀ j i, (L.unpadFreezingLifts hmq β j i).totalDegree ≤ j.val + 1 := by
  intro j i
  exact hβ (L.padCoordInclusion hmq ⟨j, i⟩).1 (L.padCoordInclusion hmq ⟨j, i⟩).2

theorem unpadFreezingLifts_bound (hmq : m ≤ q)
    (β : ∀ j, (L.pad q j).Coord → MvPolynomial Vars ℤ)
    (c : ∀ j, (L.pad q j).Coord → ℝ)
    (point : (Vars → ℝ) → X → ℝ) (domain : Set (Vars → ℝ)) (ε : Fin q → ℝ)
    (hsmall : ∀ t ∈ domain, ∀ j i,
      |eval (point t) (L.pad q j).poly i - c j i -
        MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (β j i))| ≤ ε j) :
    ∀ t ∈ domain, ∀ j i,
      |eval (point t) (L j).poly i - L.unpadCenter hmq c j i -
        MvPolynomial.eval t
          (MvPolynomial.map (Int.castRingHom ℝ) (L.unpadFreezingLifts hmq β j i))| ≤
        ε (j.castLE hmq) := by
  intro t ht j i
  have h := hsmall t ht (L.padCoordInclusion hmq ⟨j, i⟩).1
    (L.padCoordInclusion hmq ⟨j, i⟩).2
  rw [L.padCoordInclusion_eval hmq (point t)] at h
  exact h

theorem pad_coordinateWeighted_sum (hmq : m ≤ q) (ε : Fin q → ℝ) :
    (∑ j : Fin m, (Fintype.card (L j).Coord : ℝ) * ε (j.castLE hmq)) =
      ∑ j : Fin q, (Fintype.card (L.pad q j).Coord : ℝ) * ε j := by
  apply Fintype.sum_of_injective (Fin.castLE hmq)
    (fun i j hij => Fin.ext (congrArg (fun k : Fin q => k.val) hij))
  · intro j hj
    have hge : m ≤ j.val := by
      by_contra hnot
      have hlt : j.val < m := by omega
      exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
    rw [L.pad_apply_ge j hge]
    change (Fintype.card PEmpty : ℝ) * ε j = 0
    simp
  · intro j
    rw [L.pad_apply_castLE hmq j]

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPaddedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
variable (L : RankPreparationFamily X (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

include hmq in
omit [Fintype X] [∀ j, Fintype (Deck j)] in

theorem exists_freeze_allocated_padded_recovered_sample
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (a : X → ℤ) (v : Option Vars × X → ℤ)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c a v sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (parentDomain : Set (X → ℤ))
    (herr : ∀ x ∈ parentDomain, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    (hbudget : (D : ℝ) * (2 * ((∑ j, (Fintype.card (L.pad q j).Coord : ℝ) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ)) < 1 / 12)
    (hscoreBudget : A.kernel.lip * ((D : ℝ) * (2 *
      ((∑ j, (Fintype.card (L.pad q j).Coord : ℝ) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ))) ≤ gain / 16)
    {Ω : Type} [Fintype Ω] (t : Ω → Vars → ℤ)
    (hbox : ∀ u k, |(t u k : ℝ)| ≤ layerSamplerBox B U b S k)
    (hinside : ∀ u, integerAffineMap (fun x k => jointIntegerFrame (a,v) (some k) x)
      (jointIntegerFrame (a,v) none) (t u) ∈ parentDomain)
    (score : Ω → ℝ) (hscoreBound : ∀ u, |score u| ≤ 1)
    (hscore : gain / 2 ≤ 𝔼 u, score u * A.value
      (fun x => (integerAffineMap (fun x k => jointIntegerFrame (a,v) (some k) x)
        (jointIntegerFrame (a,v) none) (t u) x : ℝ))) :
    ∃ A' : PolynomialPatch Vars s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      7 * gain / 16 ≤ 𝔼 u, score u * A'.value (fun k => (t u k : ℝ)) := by
  let frame := jointIntegerFrame (a,v)
  let point : Ω → X → ℝ := fun u x =>
    (frame none x : ℝ) + ∑ k, (frame (some k) x : ℝ) * (t u k : ℝ)
  have hscore' : gain / 2 ≤ 𝔼 u, score u * A.value (point u) := by
    simpa only [point, frame, integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul] using hscore
  obtain ⟨β, hβ, _, hsmall⟩ := hread.freezing_lifts B U b hb o S hR hσ
    (fun j => (L.pad q j).poly) hm hσ1 C hC hchart hp c a v sample read
  let ε : Fin q → ℝ := fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * R j)
  have hε : ∀ j, 0 ≤ ε j := by
    intro j
    exact mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j).le)
  let domain : Set (Vars → ℝ) := Set.range (fun u k => (t u k : ℝ))
  obtain ⟨u₀, bref, href⟩ := A.exists_contributing_site_of_pos_score point score
    ((half_pos hgain).trans_le hscore')
  let : Nonempty Ω := ⟨u₀⟩
  let βold := L.unpadFreezingLifts hmq β
  have hβold : ∀ j i, (βold j i).totalDegree ≤ j.val + 1 :=
    L.unpadFreezingLifts_degree hmq β hβ
  let εold := fun j : Fin m => ε (j.castLE hmq)
  have hsum : (∑ j : Fin m, (Fintype.card (L j).Coord : ℝ) * εold j) =
      ∑ j : Fin q, (Fintype.card (L.pad q j).Coord : ℝ) * ε j :=
    L.pad_coordinateWeighted_sum hmq ε
  have hbudgetOld : (D : ℝ) * (2 *
      ((∑ j : Fin m, (Fintype.card (L j).Coord : ℝ) * εold j) + δ)) < 1 / 12 := by
    rw [hsum]
    exact hbudget
  have hsmallOld := L.unpadFreezingLifts_bound hmq β (fun j => (c j).val)
    (fun x v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)
    domain ε (by
      rintro x ⟨u, rfl⟩
      exact hsmall _ (hbox u))
  obtain ⟨A', hLip, hweight, hclose⟩ := F.exists_freeze_prepared_affine L ip hip c₀ err
    hprepare frame βold hβold (L.unpadCenter hmq (fun j => (c j).val))
    εold (fun j => hε _) hδ domain
    (by rintro x ⟨u, rfl⟩; exact ⟨t u, rfl⟩)
    hsmallOld
    (by
      rintro x ⟨u, rfl⟩ i
      simpa only [frame, integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul] using
        herr _ (hinside u) i)
    (fun k => (t u₀ k : ℝ)) ⟨u₀, rfl⟩ bref href hbudgetOld
  rw [hsum] at hclose
  refine ⟨A', hLip, hweight, ?_⟩
  have hcompare : (𝔼 u, score u * A.value (point u)) ≤
      (𝔼 u, score u * A'.value (fun k => (t u k : ℝ))) + gain / 16 := by
    calc
      _ ≤ 𝔼 u, (score u * A'.value (fun k => (t u k : ℝ)) + gain / 16) := by
        apply Finset.expect_le_expect
        intro u _
        exact unit_weight_score_error (hscoreBound u)
          ((hclose _ ⟨u, rfl⟩).trans hscoreBudget)
      _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
  linarith

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedPaddedParameterBoxEarlyFreeze
namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
variable (L : RankPreparationFamily X (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_freeze_allocated_padded_parameter_box
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c z.1.val z.2.val sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    (hδbudget : δ ≤ gain / (128 * ((D : ℝ) + 1) * (A.kernel.lip + 1)))
    {Pearly : ℝ}
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hinflation : ∀ j,
      (32 * ((D : ℝ) + 1) * (A.kernel.lip + 1) * ((q : ℝ) + 1) / gain) *
        (Fintype.card (L.pad q j).Coord : ℝ) * C j ≤ Real.exp Pearly)
    (score : integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) → ℝ) (hscoreBound : ∀ u, |score u| ≤ 1)
    (hscore : gain / 2 ≤ 𝔼 u, score u * A.value
      (fun x => (integerAffineMap (fun x k => jointIntegerFrame (z.1.val,z.2.val) (some k) x)
        (jointIntegerFrame (z.1.val,z.2.val) none) u.val x : ℝ))) :
    ∃ A' : PolynomialPatch Vars s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      7 * gain / 16 ≤ 𝔼 u, score u * A'.value (fun k => (u.val k : ℝ)) := by
  classical
  have hLip : 0 ≤ (A.kernel.lip : ℝ) := NNReal.coe_nonneg _
  let C' : Fin q → ℝ := fun j =>
    (32 * ((D : ℝ) + 1) * (A.kernel.lip + 1) * ((q : ℝ) + 1) / gain) *
      (Fintype.card (L.pad q j).Coord : ℝ) * C j
  have hC' : ∀ j, 0 ≤ C' j := by
    intro j
    dsimp [C']
    exact mul_nonneg (mul_nonneg (div_nonneg (by positivity) hgain.le)
      (Nat.cast_nonneg _)) (hC j)
  have hbud := preparedFreezingRadiusBudget_of_inflated_chart
    (fun j => Fintype.card (L.pad q j).Coord) (fun j => Fintype.card (I j)) C R
    hLip hgain hgain1 (hearly C' hC' hinflation) hδbudget
  have hbox : ∀ (u : integerBox sides) k,
      |(u.val k : ℝ)| ≤ layerSamplerBox B U b S k := by
    intro u k
    have hu := (mem_integerBox sides u.val).mp u.property k
    have h0 : (0 : ℝ) ≤ u.val k := by exact_mod_cast hu.1
    rw [abs_of_nonneg h0]
    have hk : layerSamplerBox B U b S k = (sides k : ℝ) := by cases k <;> rfl
    rw [hk]
    exact_mod_cast hu.2.le
  have hinside : ∀ u : integerBox sides,
      integerAffineMap (fun x k => jointIntegerFrame (z.1.val,z.2.val) (some k) x)
        (jointIntegerFrame (z.1.val,z.2.val) none) u.val ∈ (integerBox N : Set (X → ℤ)) := by
    intro u
    rw [integerAffineMap_jointIntegerFrame]
    exact narrow_jointIntegerPhysicalSite_mem_box
      (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hτhalf hξ1 u.val
      (allocatedParameterBox_root_bound B U b S u) N hN hsize z
  apply F.exists_freeze_allocated_padded_recovered_sample L hmq B U b hb o S hR hσ ip hip c₀ err
    hprepare hm hp hσ1 C hC hchart c z.1.val z.2.val sample read hread hδ hgain
    (integerBox N) herr _ _ Subtype.val hbox hinside score hscoreBound hscore
  · simpa only [mul_assoc] using hbud.1
  · simpa only [mul_assoc] using hbud.2

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
variable (L : RankPreparationFamily X (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2_oai
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c z.1.val z.2.val sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (A.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (score : integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) → ℝ) (hscoreBound : ∀ u, |score u| ≤ 1)
    (hscore : gain / 2 ≤ 𝔼 u, score u * A.value
      (fun x => (integerAffineMap (fun x k => jointIntegerFrame (z.1.val,z.2.val) (some k) x)
        (jointIntegerFrame (z.1.val,z.2.val) none) u.val x : ℝ))) :
    ∃ A' : PolynomialPatch Vars s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      7 * gain / 16 ≤ 𝔼 u, score u * A'.value (fun k => (u.val k : ℝ)) := by
  have hδbudget := (preparedFreezingEarlyLogBudget (N := 0) (C := 0)
    hp0 (NNReal.coe_nonneg A.kernel.lip) le_rfl hDlog hqlog hLlog
    (by simpa only [Nat.cast_zero] using Real.exp_nonneg p) (Real.exp_nonneg p) hgainlog hδearly).2
  have hinflation : ∀ j,
      (32 * ((D : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) * ((q : ℝ) + 1) / gain) *
        (Fintype.card (L.pad q j).Coord : ℝ) * C j ≤ Real.exp Pearly := by
    intro j
    exact ((preparedFreezingEarlyLogBudget hp0 (NNReal.coe_nonneg A.kernel.lip)
      (hC j) hDlog hqlog hLlog (hNlog j) (hClog j) hgainlog hδearly).1).trans
      (Real.exp_le_exp.mpr hPearly)
  exact F.exists_freeze_allocated_padded_parameter_box L hmq B U b hb o S hR hσ ip hip c₀ err
    hprepare hm hp hσ1 C hC hchart c N hN hτ hτhalf hξ1 hsize z sample read hread
    hδ hgain hgain1 herr hδbudget hearly hinflation score hscoreBound hscore

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2_oai := @OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_freeze_allocated_padded_parameter_box_of_early_bounds_s2_oai
