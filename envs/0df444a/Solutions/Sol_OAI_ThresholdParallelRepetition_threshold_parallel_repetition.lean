-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.threshold_parallel_repetition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T13:16:21.697826+00:00
-- url     : https://prove2.me/submissions/d3100a6c-4ea8-4a2b-b33a-87756b839da6

import Mathlib
import Definitions.Def_EntangledGames

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

universe u_n u_J u_α u_m u_p u_r u_R u_A u_q u_ι u_B u_β u_γ u_E u_F u_X u_Y u_I u_K u_Z u_u u_v u_T u_U u_Ω

section
section
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

open scoped Kronecker
open Matrix

namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]

lemma born_eq_quadratic (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b =
      (star S.state ⬝ᵥ ((S.alice x a ⊗ₖ S.bob y b) *ᵥ S.state)).re := by
  simp only [born, dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, Pi.star_apply,
    Finset.mul_sum, ← mul_assoc, Complex.re_sum]

lemma born_nonneg (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.born x y a b := by
  rw [born_eq_quadratic]
  exact (Complex.nonneg_iff.mp
    (((S.alice_pos x a).kronecker (S.bob_pos y b)).dotProduct_mulVec_nonneg S.state)).1

lemma total_effect (S : Strategy X Y A B) (x : X) (y : Y) :
    ∑ a, ∑ b, S.alice x a ⊗ₖ S.bob y b = 1 := by
  classical
  calc
    _ = (∑ a, S.alice x a) ⊗ₖ (∑ b, S.bob y b) := by
      ext i j
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = 1 := by rw [S.alice_total, S.bob_total, Matrix.one_kronecker_one]

lemma born_sum (S : Strategy X Y A B) (x : X) (y : Y) :
    ∑ a, ∑ b, S.born x y a b = 1 := by
  simp_rw [born_eq_quadratic]
  simp_rw [← Complex.re_sum, ← dotProduct_sum, ← Matrix.sum_mulVec]
  rw [total_effect, Matrix.one_mulVec]
  rw [dotProduct, Complex.re_sum]
  convert S.state_unit using 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.normSq, Complex.mul_re]

lemma born_le_one (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b ≤ 1 := by
  classical
  rw [← born_sum S x y]
  exact (Finset.single_le_sum (fun b' _ => born_nonneg S x y a b') (Finset.mem_univ b)).trans
    (Finset.single_le_sum (fun a' _ => Finset.sum_nonneg
      (fun b' _ => born_nonneg S x y a' b')) (Finset.mem_univ a))

end Strategy

namespace Strategy

def deterministic {X Y A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a₀ : A) (b₀ : B) : Strategy X Y A B where
  dimA := 0
  dimB := 0
  state := fun _ => 1
  state_unit := by simp
  alice := fun _ a => if a = a₀ then 1 else 0
  bob := fun _ b => if b = b₀ then 1 else 0
  alice_pos := by
    intro _ a
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  bob_pos := by
    intro _ b
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  alice_total := by intro _; simp
  bob_total := by intro _; simp

end Strategy

lemma successProbability_nonneg {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : 0 ≤ successProbability G S := by
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg (G.questionProb_nonneg z)
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact S.born_nonneg _ _ _ _
  · exact le_rfl

lemma successProbability_le_one {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : successProbability G S ≤ 1 := by
  calc
    successProbability G S ≤ ∑ z, G.questionProb z *
        ∑ w : Fin (a + 1) × Fin (b + 1), S.born z.1 z.2 w.1 w.2 := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (G.questionProb_nonneg z)
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · exact le_rfl
      · exact S.born_nonneg _ _ _ _
    _ = 1 := by
      simp_rw [Fintype.sum_prod_type, S.born_sum, mul_one]
      simpa only [Fintype.sum_prod_type] using G.questionProb_sum

lemma entangledValue_nonneg {x y a b : ℕ} (G : Game x y a b) :
    0 ≤ entangledValue G := by
  let S : SingleStrategy x y a b := Strategy.deterministic 0 0
  exact (successProbability_nonneg G S).trans (le_csSup
    (show BddAbove (Set.range (successProbability G)) from
      ⟨1, by rintro _ ⟨T, rfl⟩; exact successProbability_le_one G T⟩)
    (Set.mem_range_self S))

lemma successProbability_le_value {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : successProbability G S ≤ entangledValue G := by
  exact le_csSup ⟨1, by rintro _ ⟨T, rfl⟩; exact successProbability_le_one G T⟩
    (Set.mem_range_self S)

lemma entangledValue_le_one {x y a b : ℕ} (G : Game x y a b) :
    entangledValue G ≤ 1 := by
  apply csSup_le
  · exact ⟨_, Set.mem_range_self (Strategy.deterministic (X := Fin (x + 1))
      (Y := Fin (y + 1)) (0 : Fin (a + 1)) (0 : Fin (b + 1)))⟩
  · rintro _ ⟨S, rfl⟩
    exact successProbability_le_one G S

end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators ComplexOrder

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ThresholdParallelRepetition.Resolvent

variable {n : Type u_n} [Fintype n] [DecidableEq n]

omit [Fintype n] in

lemma shift_posDef {A : Matrix n n ℂ} (hA : A.PosSemidef) {s : ℝ} (hs : 0 < s) :
    (A + s • (1 : Matrix n n ℂ)).PosDef := by
  simpa only [add_comm] using ((Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hs).add_posSemidef hA

lemma second_resolvent_identity (A B : Matrix n n ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹ = B⁻¹ - B⁻¹ * (A - B) * B⁻¹ +
      B⁻¹ * (A - B) * A⁻¹ * (A - B) * B⁻¹ := by
  have h₁ : B⁻¹ - A⁻¹ = B⁻¹ * (A - B) * A⁻¹ :=
    Matrix.inv_sub_inv (by simp [hA, hB])
  have h₂ : A⁻¹ - B⁻¹ = -(A⁻¹ * (A - B) * B⁻¹) := by
    rw [Matrix.inv_sub_inv (by simp [hA, hB]), ← neg_sub A B, mul_neg, neg_mul]
  rw [← h₁]
  calc
    A⁻¹ = B⁻¹ - A⁻¹ * (A - B) * B⁻¹ := by
      apply sub_eq_iff_eq_add.mp at h₂
      simpa only [sub_eq_add_neg, add_comm] using h₂
    _ = B⁻¹ - B⁻¹ * (A - B) * B⁻¹ +
        (B⁻¹ - A⁻¹) * (A - B) * B⁻¹ := by noncomm_ring

def resolvent (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  (A + s • (1 : Matrix n n ℂ))⁻¹

def purificationKernel (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  A * resolvent A s

lemma resolvent_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : (resolvent A s).PosSemidef :=
  (shift_posDef hA hs).posSemidef.inv

lemma resolvent_mul_shift {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : resolvent A s * (A + s • 1) = 1 := by
  exact Matrix.nonsing_inv_mul _ ((shift_posDef hA hs).isUnit.map Matrix.detMonoidHom)

lemma shift_mul_resolvent {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : (A + s • 1) * resolvent A s = 1 := by
  exact Matrix.mul_nonsing_inv _ ((shift_posDef hA hs).isUnit.map Matrix.detMonoidHom)

lemma purificationKernel_eq {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : purificationKernel A s = 1 - s • resolvent A s := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_mul, smul_mul_assoc, one_mul, purificationKernel] using
    shift_mul_resolvent hA hs

lemma resolvent_mul_eq {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : resolvent A s * A = 1 - s • resolvent A s := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [mul_add, mul_smul_comm, mul_one] using resolvent_mul_shift hA hs

lemma resolvent_square_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    s • (resolvent A s * resolvent A s) ≤ resolvent A s := by
  rw [Matrix.le_iff]
  have hp := hA.conjTranspose_mul_mul_same (resolvent A s)
  rw [(resolvent_posSemidef hA hs).isHermitian.eq, resolvent_mul_eq hA hs,
    sub_mul, one_mul, smul_mul_assoc] at hp
  exact hp

lemma purificationKernel_sub {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {s : ℝ} (hs : 0 < s) :
    purificationKernel A s - purificationKernel B s =
      s • (resolvent A s * (A - B) * resolvent B s) := by
  rw [purificationKernel_eq hA hs, purificationKernel_eq hB hs]
  have h : resolvent A s - resolvent B s =
      -(resolvent A s * (A - B) * resolvent B s) := by
    dsimp only [resolvent]
    rw [Matrix.inv_sub_inv (by simp [(shift_posDef hA hs).isUnit,
      (shift_posDef hB hs).isUnit])]
    rw [add_sub_add_right_eq_sub, ← neg_sub A B, mul_neg, neg_mul]
  calc
    _ = -(s • (resolvent A s - resolvent B s)) := by module
    _ = _ := by rw [h, smul_neg, neg_neg]

lemma purificationKernel_square_le {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {s : ℝ} (hs : 0 < s) :
    (purificationKernel A s - purificationKernel B s)ᴴ *
      (purificationKernel A s - purificationKernel B s) ≤
      s • (resolvent B s * (A - B) * resolvent A s * (A - B) * resolvent B s) := by
  have hRA := (resolvent_posSemidef hA hs).isHermitian.eq
  have hRB := (resolvent_posSemidef hB hs).isHermitian.eq
  have hD := (hA.isHermitian.sub hB.isHermitian).eq
  have hp := ((Matrix.le_iff.mp (resolvent_square_le hA hs)).conjTranspose_mul_mul_same
    ((A - B) * resolvent B s)).smul hs.le
  rw [Matrix.le_iff, purificationKernel_sub hA hB hs]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial,
    hRA, hRB, hD] at hp ⊢
  simp only [smul_sub, Matrix.mul_sub, Matrix.sub_mul,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc] at hp ⊢
  convert hp using 1
  first | rfl | module

lemma weighted_resolvent_identity {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : B.PosSemidef)
    (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B)
    {s : ℝ} (hs : 0 < s) :
    ∑ j, w j • (resolvent (A j) s - resolvent B s) =
      ∑ j, w j • (resolvent B s * (A j - B) * resolvent (A j) s *
        (A j - B) * resolvent B s) := by
  have hlinear : ∑ j, w j • (A j - B) = 0 := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, hmean, ← Finset.sum_smul, hw, one_smul, sub_self]
  have hzero : ∑ j, w j • (resolvent B s * (A j - B) * resolvent B s) = 0 := by
    calc
      _ = resolvent B s * (∑ j, w j • (A j - B)) * resolvent B s := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_smul_comm, smul_mul_assoc]
      _ = 0 := by rw [hlinear, mul_zero, zero_mul]
  have hsecond (j : J) : resolvent (A j) s =
      resolvent B s - resolvent B s * (A j - B) * resolvent B s +
        resolvent B s * (A j - B) * resolvent (A j) s * (A j - B) * resolvent B s := by
    simpa only [resolvent, add_sub_add_right_eq_sub] using
      second_resolvent_identity (A j + s • 1) (B + s • 1)
        (shift_posDef (hA j) hs).isUnit (shift_posDef hB hs).isUnit
  have heq (j : J) : resolvent (A j) s - resolvent B s =
      -(resolvent B s * (A j - B) * resolvent B s) +
        resolvent B s * (A j - B) * resolvent (A j) s * (A j - B) * resolvent B s := by
    rw [sub_eq_iff_eq_add]
    calc
      _ = _ := hsecond j
      _ = _ := by abel
  simp_rw [heq, smul_add, smul_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hzero, neg_zero, zero_add]

lemma weighted_kernel_square_le {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : B.PosSemidef)
    (hw0 : ∀ j, 0 ≤ w j) (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B)
    {s : ℝ} (hs : 0 < s) :
    ∑ j, w j • ((purificationKernel (A j) s - purificationKernel B s)ᴴ *
      (purificationKernel (A j) s - purificationKernel B s)) ≤
    s • ∑ j, w j • (resolvent (A j) s - resolvent B s) := by
  calc
    _ ≤ ∑ j, w j • (s • (resolvent B s * (A j - B) * resolvent (A j) s *
        (A j - B) * resolvent B s)) := by
      exact Finset.sum_le_sum fun j _ => smul_le_smul_of_nonneg_left
        (purificationKernel_square_le (hA j) hB hs) (hw0 j)
    _ = s • ∑ j, w j • (resolvent B s * (A j - B) * resolvent (A j) s *
        (A j - B) * resolvent B s) := by
      simp only [Finset.smul_sum, smul_smul, mul_comm (w _) s]
    _ = _ := by rw [weighted_resolvent_identity A w B hA hB hw hmean hs]

end ThresholdParallelRepetition.Resolvent

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace ThresholdParallelRepetition.Resolvent

lemma scalar_square_integral {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => t ^ 2 / (t + s) ^ 2) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, t ^ 2 / (t + s) ^ 2) = t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun u : ℝ => -(t ^ 2) / (t + u)) (t ^ 2 / (t + s) ^ 2) s := by
    convert! (hasDerivAt_const s (-(t ^ 2))).div
      ((hasDerivAt_id s).const_add t) (ne_of_gt (add_pos_of_pos_of_nonneg ht hs)) using 1
    simp only [id_eq]
    ring
  have htop : Tendsto (fun s : ℝ => t + s) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b - t)] with s hs
    linarith
  have hl := htop.const_div_atTop (-(t ^ 2))
  have hpos (s : ℝ) (_hs : s ∈ Ioi (0 : ℝ)) : 0 ≤ t ^ 2 / (t + s) ^ 2 := by positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hl]
  simp only [add_zero, zero_sub, neg_div, neg_neg]
  field_simp

lemma scalar_entropy_integral {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntegrableOn (fun s : ℝ => t / (1 + s) - t / (t + s)) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, t / (1 + s) - t / (t + s)) = t * Real.log t := by
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · simp
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun u : ℝ => t * (Real.log (1 + u) - Real.log (t + u)))
        (t / (1 + s) - t / (t + s)) s := by
    have h₁ := ((hasDerivAt_id s).const_add (1 : ℝ)).log
      (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hs))
    have h₂ := ((hasDerivAt_id s).const_add t).log
      (ne_of_gt (add_pos_of_pos_of_nonneg ht hs))
    convert! (h₁.sub h₂).const_mul t using 1
    simp only [id_eq]
    ring
  have htop : Tendsto (fun s : ℝ => t + s) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b - t)] with s hs
    linarith
  have hratio : Tendsto (fun s : ℝ => (1 + s) / (t + s)) atTop (𝓝 1) := by
    have hh := (htop.const_div_atTop (1 - t)).const_add (1 : ℝ)
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have ht' : t + s ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ht hs)
    field_simp
    ring
  have hlog : Tendsto (fun s : ℝ => Real.log ((1 + s) / (t + s))) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hl : Tendsto (fun s : ℝ => t * (Real.log (1 + s) - Real.log (t + s)))
      atTop (𝓝 0) := by
    have hh := hlog.const_mul t
    rw [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    rw [Real.log_div (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hs))
      (ne_of_gt (add_pos_of_pos_of_nonneg ht hs))]
  have hneg (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      t / (1 + s) - t / (t + s) ≤ 0 := by
    apply sub_nonpos.mpr
    apply div_le_div_of_nonneg_left ht.le (add_pos ht hs)
    linarith
  refine ⟨integrableOn_Ioi_deriv_of_nonpos' hd hneg hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonpos' hd hneg hl]
  simp

end ThresholdParallelRepetition.Resolvent

end
end

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix MeasureTheory Set
namespace ThresholdParallelRepetition.Resolvent
variable {n : Type u_n} [Fintype n] [DecidableEq n]

local instance matrixContinuousENorm : ContinuousENorm (Matrix n n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ inferInstance

local instance matrixPreorder : Preorder (Matrix n n ℂ) :=
  (Matrix.instPartialOrder : PartialOrder (Matrix n n ℂ)).toPreorder

omit [DecidableEq n] in
lemma isClosed_posSemidef : IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · have heq : {A : Matrix n n ℂ | ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x)} =
        ⋂ x : n → ℂ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by ext; simp
    change IsClosed {A : Matrix n n ℂ | ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x)}
    rw [heq]
    apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [Matrix.mulVec, dotProduct]
    fun_prop

local instance matrixClosedIci : ClosedIciTopology (Matrix n n ℂ) where
  isClosed_Ici A := by
    exact isClosed_posSemidef.preimage (continuous_id.sub continuous_const)

lemma integral_matrix_nonneg {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {f : α → Matrix n n ℂ} (hf : ∀ᵐ s ∂μ, (f s).PosSemidef) :
    (∫ s, f s ∂μ).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact @integral_nonneg_of_ae α (Matrix n n ℂ) _ _ _ μ _ _ _
    matrixClosedIci f (hf.mono fun _ h => h.nonneg)

lemma integral_matrix_mono {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {f g : α → Matrix n n ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : f ≤ᵐ[μ] g) : (∫ s, f s ∂μ) ≤ ∫ s, g s ∂μ :=
  @integral_mono_ae α (Matrix n n ℂ) _ _ _ μ _ _ _ matrixClosedIci f g hf hg hfg

def spectralLinear (U : Matrix n n ℂ) : (n → ℝ) →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => U * diagonal (fun i => (v i : ℂ)) * Uᴴ
      map_add' := by
        intro v w
        simp only [Pi.add_apply, Complex.ofReal_add]
        change U * diagonal ((fun i => (v i : ℂ)) + (fun i => (w i : ℂ))) * Uᴴ = _
        erw [← Matrix.diagonal_add]
        rw [mul_add, add_mul]
      map_smul' := by
        intro c v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have hd : diagonal (fun i => ((c * v i : ℝ) : ℂ)) =
            c • diagonal (fun i => (v i : ℂ)) := by
          ext i j
          simp only [Matrix.diagonal_apply, Matrix.smul_apply, Complex.ofReal_mul,
            Complex.real_smul]
          split_ifs <;> simp
        rw [hd, Matrix.mul_smul, Matrix.smul_mul] }

lemma spectralLinear_apply (U : Matrix n n ℂ) (v : n → ℝ) :
    spectralLinear U v = U * diagonal (fun i => (v i : ℂ)) * Uᴴ := rfl

lemma cfc_eq_spectralLinear {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = spectralLinear (hA.eigenvectorUnitary : Matrix n n ℂ)
      (fun i => f (hA.eigenvalues i)) := by
  rw [hA.cfc_eq]
  rfl

lemma integrable_cfc {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : α → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun s => f s (hA.eigenvalues i)) μ) :
    Integrable (fun s => cfc (f s) A) μ := by
  simp_rw [cfc_eq_spectralLinear hA]
  exact (spectralLinear _).integrable_comp (Integrable.of_eval hf)

lemma integral_cfc {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : α → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun s => f s (hA.eigenvalues i)) μ) :
    (∫ s, cfc (f s) A ∂μ) = cfc (fun t => ∫ s, f s t ∂μ) A := by
  simp_rw [cfc_eq_spectralLinear hA]
  erw [(spectralLinear _).integral_comp_comm (Integrable.of_eval hf)]
  congr 1
  ext i
  exact eval_integral hf i

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma spectrum_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {t : ℝ} (ht : t ∈ spectrum ℝ A) : 0 ≤ t := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hA.eigenvalues_nonneg i

lemma eigenvalues_le_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (hA1 : A ≤ 1) (i : n) : hA.isHermitian.eigenvalues i ≤ 1 := by
  have h : cfc (fun t : ℝ => t) A ≤ cfc (fun _ : ℝ => (1 : ℝ)) A := by
    erw [cfc_id' ℝ A hA.isHermitian, cfc_const (1 : ℝ) A hA.isHermitian,
      map_one]
    exact hA1
  exact (cfc_le_iff (fun t : ℝ => t) (fun _ : ℝ => (1 : ℝ)) A
    (ha := hA.isHermitian)).mp h _ (hA.isHermitian.eigenvalues_mem_spectrum_real i)

lemma resolvent_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    resolvent A s = cfc (fun t : ℝ => (t + s)⁻¹) A := by
  erw [cfc_inv (fun t : ℝ => t + s) A
    (fun t ht => ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg hA ht) hs))
    (ha := hA.isHermitian)]
  erw [cfc_add A (fun t : ℝ => t) (fun _ : ℝ => s),
    cfc_id' ℝ A hA.isHermitian, cfc_const s A hA.isHermitian,
    Algebra.algebraMap_eq_smul_one, ← Matrix.nonsing_inv_eq_ringInverse]
  rfl

lemma purificationKernel_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    purificationKernel A s = cfc (fun t : ℝ => t / (t + s)) A := by
  rw [purificationKernel, resolvent_cfc hA hs]
  calc
    A * cfc (fun t : ℝ => (t + s)⁻¹) A =
        cfc (fun t : ℝ => t) A * cfc (fun t : ℝ => (t + s)⁻¹) A := by
      erw [cfc_id' ℝ A hA.isHermitian]
    _ = _ := by
      rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + s)⁻¹) A
        (hg := A.finite_real_spectrum.continuousOn _)]
      rfl

lemma purificationKernel_square_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (purificationKernel A s)ᴴ * purificationKernel A s =
      cfc (fun t : ℝ => t ^ 2 / (t + s) ^ 2) A := by
  rw [purificationKernel_cfc hA hs,
    (cfc_predicate (fun t : ℝ => t / (t + s)) A).isHermitian.eq,
    ← cfc_mul (fun t : ℝ => t / (t + s)) (fun t : ℝ => t / (t + s)) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t _
  change t / (t + s) * (t / (t + s)) = t ^ 2 / (t + s) ^ 2
  rw [← pow_two, div_pow]

lemma kernel_square_integrable {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    IntegrableOn (fun s : ℝ => (purificationKernel A s)ᴴ * purificationKernel A s)
      (Ioi 0) := by
  have hi := integrable_cfc hA.isHermitian (fun (s t : ℝ) => t ^ 2 / (t + s) ^ 2)
    (fun i => (scalar_square_integral (hA.eigenvalues_nonneg i)).1)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (purificationKernel_square_cfc hA hs).symm

lemma kernel_square_integral {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (∫ s : ℝ in Ioi 0, (purificationKernel A s)ᴴ * purificationKernel A s) = A := by
  calc
    _ = ∫ s : ℝ in Ioi 0, cfc (fun t : ℝ => t ^ 2 / (t + s) ^ 2) A := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact purificationKernel_square_cfc hA hs
    _ = cfc (fun t : ℝ => ∫ s : ℝ in Ioi 0, t ^ 2 / (t + s) ^ 2) A :=
      integral_cfc hA.isHermitian _ (fun i => (scalar_square_integral (hA.eigenvalues_nonneg i)).1)
    _ = cfc (fun t : ℝ => t) A := by
      apply cfc_congr
      intro t ht
      exact (scalar_square_integral (spectrum_nonneg hA ht)).2
    _ = A := cfc_id' ℝ A hA.isHermitian

def effectEntropy (A : Matrix n n ℂ) : Matrix n n ℂ := cfc (fun t : ℝ => t * Real.log t) A

def entropyIntegrand (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  (1 / (1 + s) : ℝ) • A - purificationKernel A s

lemma entropyIntegrand_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    entropyIntegrand A s = cfc (fun t : ℝ => t / (1 + s) - t / (t + s)) A := by
  rw [entropyIntegrand, purificationKernel_cfc hA hs,
    cfc_sub (fun t : ℝ => t / (1 + s)) (fun t : ℝ => t / (t + s)) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  congr 1
  calc
    _ = cfc (fun t : ℝ => (1 / (1 + s)) • t) A := by
      erw [cfc_smul (1 / (1 + s) : ℝ) (fun t : ℝ => t) A,
        cfc_id' ℝ A hA.isHermitian]
    _ = _ := by apply cfc_congr; intro t _; simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma entropy_integrable {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    IntegrableOn (entropyIntegrand A) (Ioi 0) := by
  have hi := integrable_cfc hA.isHermitian
    (fun (s t : ℝ) => t / (1 + s) - t / (t + s))
    (fun i => (scalar_entropy_integral (hA.eigenvalues_nonneg i) (eigenvalues_le_one hA hA1 i)).1)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (entropyIntegrand_cfc hA hs).symm

lemma entropy_integral {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    (∫ s : ℝ in Ioi 0, entropyIntegrand A s) = effectEntropy A := by
  calc
    _ = ∫ s : ℝ in Ioi 0, cfc (fun t : ℝ => t / (1 + s) - t / (t + s)) A := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact entropyIntegrand_cfc hA hs
    _ = cfc (fun t : ℝ => ∫ s : ℝ in Ioi 0, t / (1 + s) - t / (t + s)) A :=
      integral_cfc hA.isHermitian _ (fun i =>
        (scalar_entropy_integral (hA.eigenvalues_nonneg i) (eigenvalues_le_one hA hA1 i)).1)
    _ = effectEntropy A := by
      apply cfc_congr
      intro t ht
      rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
      obtain ⟨i, rfl⟩ := ht
      exact (scalar_entropy_integral (hA.eigenvalues_nonneg i) (eigenvalues_le_one hA hA1 i)).2

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]
local instance rectContinuousENorm {m : Type u_m} {p : Type u_p} [Fintype m] [Fintype p] :
    ContinuousENorm (Matrix m p ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ inferInstance

lemma scalar_kernel_memLp {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun s : ℝ => t / (t + s)) 2 (volume.restrict (Ioi 0)) := by
  have hm : Measurable (fun s : ℝ => t / (t + s)) := by fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  simpa only [IntegrableOn, div_pow] using (scalar_square_integral ht).1

lemma kernel_entry_memLp {A : Matrix n n ℂ} (hA : A.PosSemidef) (i j : n) :
    MemLp (fun s : ℝ => purificationKernel A s i j) 2 (volume.restrict (Ioi 0)) := by
  let U : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let t : n → ℝ := hA.isHermitian.eigenvalues
  have hf (k : n) : MemLp (fun s : ℝ => U i k * (t k / (t k + s) : ℝ) * star (U j k))
      2 (volume.restrict (Ioi 0)) :=
    (((scalar_kernel_memLp (hA.eigenvalues_nonneg k)).ofReal (K := ℂ)).const_mul
      (U i k)).mul_const (star (U j k))
  have hi := memLp_finsetSum Finset.univ (fun k _ => hf k)
  apply hi.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [purificationKernel_cfc hA hs, hA.isHermitian.cfc_eq]
  change (∑ k, U i k * (t k / (t k + s) : ℝ) * star (U j k)) =
    (U * diagonal (fun k => ((t k / (t k + s) : ℝ) : ℂ)) * Uᴴ) i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma integrable_gram {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {m : Type u_m} {p : Type u_p} {r : Type u_r} [Fintype m] [Fintype p] [Fintype r]
    {f : α → Matrix r m ℂ} {g : α → Matrix r p ℂ}
    (hf : ∀ i j, MemLp (fun s => f s i j) 2 μ)
    (hg : ∀ i j, MemLp (fun s => g s i j) 2 μ) :
    Integrable (fun s => (f s)ᴴ * g s) μ := by
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  change Integrable (fun s => ∑ k, star (f s k i) * g s k j) μ
  apply integrable_finsetSum
  intro k _
  exact memLp_one_iff_integrable.mp ((hg k j).mul' (hf k i).star)

lemma kernel_cross_integrable {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IntegrableOn (fun s : ℝ => (purificationKernel A s)ᴴ * purificationKernel B s) (Ioi 0) :=
  integrable_gram (kernel_entry_memLp hA) (kernel_entry_memLp hB)

lemma kernel_distance_integrable {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IntegrableOn (fun s : ℝ => (purificationKernel A s - purificationKernel B s)ᴴ *
      (purificationKernel A s - purificationKernel B s)) (Ioi 0) := by
  apply integrable_gram <;> intro i j <;>
    exact (kernel_entry_memLp hA i j).sub (kernel_entry_memLp hB i j)

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma entropy_gap_integrand_eq {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : B.PosSemidef)
    (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B)
    {s : ℝ} (hs : 0 < s) :
    (∑ j, w j • entropyIntegrand (A j) s) - entropyIntegrand B s =
      s • ∑ j, w j • (resolvent (A j) s - resolvent B s) := by
  have hc (c : ℝ) : ∑ j, w j • (c • A j) = c • B := by
    simp_rw [smul_comm (w _) c]
    rw [← Finset.smul_sum, hmean]
  have hone : ∑ j, w j • (1 : Matrix n n ℂ) = 1 := by
    rw [← Finset.sum_smul, hw, one_smul]
  have hr : ∑ j, w j • (s • resolvent (A j) s) = s • ∑ j, w j • resolvent (A j) s := by
    simp_rw [smul_comm (w _) s]
    rw [Finset.smul_sum]
  simp_rw [entropyIntegrand, purificationKernel_eq (hA _) hs, purificationKernel_eq hB hs,
    smul_sub, Finset.sum_sub_distrib]
  rw [hc, hone, hr, ← Finset.sum_smul, hw, one_smul]
  module

lemma weighted_distance_jensen {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (hB : B.PosSemidef) (hB1 : B ≤ 1)
    (hw0 : ∀ j, 0 ≤ w j) (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B) :
    (∑ j, w j • (∫ s : ℝ in Ioi 0,
        (purificationKernel (A j) s - purificationKernel B s)ᴴ *
          (purificationKernel (A j) s - purificationKernel B s))) ≤
      (∑ j, w j • effectEntropy (A j)) - effectEntropy B := by
  have hf (j : J) := (kernel_distance_integrable (hA j) hB).smul (w j)
  have hg (j : J) := (entropy_integrable (hA j) (hA1 j)).smul (w j)
  have hleft := integrable_finsetSum Finset.univ (fun j _ => hf j)
  have hright := (integrable_finsetSum Finset.univ (fun j _ => hg j)).sub
    (entropy_integrable hB hB1)
  have hi := integral_matrix_mono hleft hright (show
      (fun s => ∑ j, w j • ((purificationKernel (A j) s - purificationKernel B s)ᴴ *
        (purificationKernel (A j) s - purificationKernel B s))) ≤ᵐ[volume.restrict (Ioi 0)]
      (fun s => (∑ j, w j • entropyIntegrand (A j) s) - entropyIntegrand B s) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [entropy_gap_integrand_eq A w B hA hB hw hmean hs]
    exact weighted_kernel_square_le A w B hA hB hw0 hw hmean hs)
  erw [integral_finsetSum _ (fun j _ => hf j),
    integral_sub (integrable_finsetSum Finset.univ (fun j _ => hg j))
      (entropy_integrable hB hB1),
    integral_finsetSum _ (fun j _ => hg j)] at hi
  simp only [Pi.smul_apply] at hi
  simp_rw [integral_smul, entropy_integral (hA _) (hA1 _), entropy_integral hB hB1] at hi
  exact hi

end ThresholdParallelRepetition.Resolvent

end
end
end
end

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci rectContinuousENorm
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma integral_matrix_apply {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {m : Type u_m} {p : Type u_p} [Fintype m] [Fintype p] {f : α → Matrix m p ℂ}
    (hf : Integrable f μ) (i : m) (j : p) :
    (∫ s, f s ∂μ) i j = ∫ s, f s i j ∂μ := by
  erw [eval_integral (fun i => hf.eval i), eval_integral (fun j => (hf.eval i).eval j)]

variable {J : Type u_J} [Fintype J] [DecidableEq J]

def commonKernel (A : J → Matrix n n ℂ) (s : ℝ) : Matrix n (J × n) ℂ :=
  fun r v => purificationKernel (A v.1) s r v.2

def commonGram (A : J → Matrix n n ℂ) : Matrix (J × n) (J × n) ℂ :=
  ∫ s : ℝ in Ioi 0, (commonKernel A s)ᴴ * commonKernel A s

omit [DecidableEq J] in
lemma commonGram_integrable (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) :
    IntegrableOn (fun s : ℝ => (commonKernel A s)ᴴ * commonKernel A s) (Ioi 0) := by
  apply integrable_gram <;> intro i j <;> exact kernel_entry_memLp (hA j.1) i j.2

lemma commonGram_posSemidef (A : J → Matrix n n ℂ) : (commonGram A).PosSemidef := by
  apply integral_matrix_nonneg
  exact Filter.Eventually.of_forall fun s => posSemidef_conjTranspose_mul_self (commonKernel A s)

omit [DecidableEq J] in
lemma commonGram_block (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (commonGram A).submatrix (fun i => (j, i)) (fun i => (k, i)) =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s := by
  ext i l
  change (∫ s : ℝ in Ioi 0, (commonKernel A s)ᴴ * commonKernel A s) (j, i) (k, l) = _
  rw [integral_matrix_apply (commonGram_integrable A hA),
    integral_matrix_apply (kernel_cross_integrable (hA j) (hA k))]
  rfl

def finitePurification (A : J → Matrix n n ℂ) (j : J) : Matrix (J × n) n ℂ :=
  (CFC.sqrt (commonGram A)).submatrix id (fun i => (j, i))

lemma finitePurification_product (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (finitePurification A j)ᴴ * finitePurification A k =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s := by
  have hh := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (commonGram A))).isHermitian.eq
  unfold finitePurification
  rw [Matrix.conjTranspose_submatrix]
  change (CFC.sqrt (commonGram A))ᴴ.submatrix (fun i => (j, i)) (Equiv.refl (J × n)) *
      (CFC.sqrt (commonGram A)).submatrix (Equiv.refl (J × n)) (fun i => (k, i)) = _
  rw [Matrix.submatrix_mul_equiv, hh,
    CFC.sqrt_mul_sqrt_self (commonGram A) (commonGram_posSemidef A).nonneg]
  exact commonGram_block A hA j k

lemma finitePurification_self (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j : J) :
    (finitePurification A j)ᴴ * finitePurification A j = A j := by
  rw [finitePurification_product A hA, kernel_square_integral (hA j)]

lemma finitePurification_distance (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (finitePurification A j - finitePurification A k)ᴴ *
      (finitePurification A j - finitePurification A k) =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s - purificationKernel (A k) s)ᴴ *
        (purificationKernel (A j) s - purificationKernel (A k) s) := by
  conv_lhs => rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  have hd (s : ℝ) :
      (purificationKernel (A j) s - purificationKernel (A k) s)ᴴ *
        (purificationKernel (A j) s - purificationKernel (A k) s) =
      ((purificationKernel (A j) s)ᴴ * purificationKernel (A j) s -
        (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s) -
      ((purificationKernel (A k) s)ᴴ * purificationKernel (A j) s -
        (purificationKernel (A k) s)ᴴ * purificationKernel (A k) s) := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp_rw [hd]
  erw [integral_sub ((kernel_cross_integrable (hA j) (hA j)).sub
      (kernel_cross_integrable (hA j) (hA k)))
      ((kernel_cross_integrable (hA k) (hA j)).sub (kernel_cross_integrable (hA k) (hA k))),
    integral_sub (kernel_cross_integrable (hA j) (hA j)) (kernel_cross_integrable (hA j) (hA k)),
    integral_sub (kernel_cross_integrable (hA k) (hA j)) (kernel_cross_integrable (hA k) (hA k))]
  simp only [finitePurification_product A hA]

lemma finitePurification_jensen {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (e : R → J) (w : R → ℝ) (k : J)
    (hw0 : ∀ r, 0 ≤ w r) (hw : ∑ r, w r = 1)
    (hmean : ∑ r, w r • A (e r) = A k) :
    (∑ r, w r • ((finitePurification A (e r) - finitePurification A k)ᴴ *
      (finitePurification A (e r) - finitePurification A k))) ≤
      (∑ r, w r • effectEntropy (A (e r))) - effectEntropy (A k) := by
  simp_rw [finitePurification_distance A hA]
  exact weighted_distance_jensen (A ∘ e) w (A k) (fun r => hA (e r))
    (fun r => hA1 (e r)) (hA k) (hA1 k) hw0 hw hmean

theorem finite_common_purification (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) :
    ∃ F : J → Matrix (J × n) n ℂ,
      (∀ j, (F j)ᴴ * F j = A j) ∧
      ∀ j k, (F j)ᴴ * F k =
        ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s :=
  ⟨finitePurification A, finitePurification_self A hA, finitePurification_product A hA⟩

end ThresholdParallelRepetition.Resolvent

end

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace ThresholdParallelRepetition.MeasurementTransport
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def supportInverse (T : Matrix n n ℂ) : Matrix n n ℂ := cfc (fun t : ℝ => t⁻¹) T

lemma supportInverse_isHermitian (T : Matrix n n ℂ) : (supportInverse T).IsHermitian :=
  (cfc_predicate (fun t : ℝ => t⁻¹) T).isHermitian

lemma supportInverse_mul_self_mul {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    supportInverse T * T * supportInverse T = supportInverse T := by
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id' ℝ T hT
  change cfc (fun t : ℝ => t⁻¹) T * T * cfc (fun t : ℝ => t⁻¹) T = _
  calc
    _ = cfc (fun t : ℝ => t⁻¹) T * cfc (fun t : ℝ => t) T *
        cfc (fun t : ℝ => t⁻¹) T := by rw [hid]
    _ = cfc (fun t : ℝ => t⁻¹ * t * t⁻¹) T := by
      erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _),
        ← cfc_mul (fun t : ℝ => t⁻¹ * t) (fun t : ℝ => t⁻¹) T
          (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = _ := by apply cfc_congr; intro t _; by_cases ht : t = 0 <;> simp [ht]

lemma self_mul_supportInverse_mul {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    T * supportInverse T * T = T := by
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id' ℝ T hT
  change T * cfc (fun t : ℝ => t⁻¹) T * T = T
  calc
    _ = cfc (fun t : ℝ => t) T * cfc (fun t : ℝ => t⁻¹) T *
        cfc (fun t : ℝ => t) T := by rw [hid]
    _ = cfc (fun t : ℝ => t * t⁻¹ * t) T := by
      erw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => t⁻¹) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _),
        ← cfc_mul (fun t : ℝ => t * t⁻¹) (fun t : ℝ => t) T
          (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = cfc (fun t : ℝ => t) T := by apply cfc_congr; intro t _; simp
    _ = T := hid

lemma supportInverse_commute {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    supportInverse T * T = T * supportInverse T := by
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id' ℝ T hT
  change cfc (fun t : ℝ => t⁻¹) T * T = T * cfc (fun t : ℝ => t⁻¹) T
  calc
    _ = cfc (fun t : ℝ => t⁻¹) T * cfc (fun t : ℝ => t) T := by rw [hid]
    _ = cfc (fun t : ℝ => t⁻¹ * t) T := by
      erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = cfc (fun t : ℝ => t * t⁻¹) T := by
      apply cfc_congr; intro t _; exact mul_comm _ _
    _ = cfc (fun t : ℝ => t) T * cfc (fun t : ℝ => t⁻¹) T := by
      erw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t⁻¹) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = _ := by rw [hid]

omit [DecidableEq n] in
lemma bounded_mulVec_zero {G T : Matrix n n ℂ} (hG : G.PosSemidef) (hGT : G ≤ T)
    (x : n → ℂ) (hx : T *ᵥ x = 0) : G *ᵥ x = 0 := by
  apply (hG.dotProduct_mulVec_zero_iff x).mp
  apply le_antisymm _ (hG.dotProduct_mulVec_nonneg x)
  have ht := (Matrix.le_iff.mp hGT).dotProduct_mulVec_nonneg x
  simpa only [Matrix.sub_mulVec, dotProduct_sub, hx, dotProduct_zero, zero_sub,
    dotProduct_neg, neg_nonneg] using ht

omit [DecidableEq n] in
lemma bounded_mul_zero {m : Type u_m} {G T : Matrix n n ℂ}
    (hG : G.PosSemidef) (hGT : G ≤ T) (R : Matrix n m ℂ)
    (hTR : T * R = 0) : G * R = 0 := by
  ext i j
  exact congrFun (bounded_mulVec_zero hG hGT (fun k => R k j)
    (funext fun k => congrFun (congrFun hTR k) j)) i

lemma right_support {G T : Matrix n n ℂ} (hT : T.IsHermitian)
    (hG : G.PosSemidef) (hGT : G ≤ T) : G * (supportInverse T * T) = G := by
  have hzero : T * (1 - supportInverse T * T) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, self_mul_supportInverse_mul hT, sub_self]
  have hz := bounded_mul_zero hG hGT _ hzero
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz
  exact hz.symm

lemma left_support {G T : Matrix n n ℂ} (hT : T.IsHermitian)
    (hG : G.PosSemidef) (hGT : G ≤ T) : (T * supportInverse T) * G = G := by
  have h := congrArg Matrix.conjTranspose (right_support hT hG hGT)
  simpa only [Matrix.conjTranspose_mul, hT.eq, (supportInverse_isHermitian T).eq,
    hG.isHermitian.eq, Matrix.mul_assoc] using h

variable {m : Type u_m} [Fintype m] [DecidableEq m]

def rangeProjection (F : Matrix m n ℂ) : Matrix m m ℂ :=
  F * supportInverse (Fᴴ * F) * Fᴴ

omit [DecidableEq m] in
lemma rangeProjection_isHermitian (F : Matrix m n ℂ) :
    (rangeProjection F).IsHermitian := by
  unfold Matrix.IsHermitian
  simp only [rangeProjection, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (supportInverse_isHermitian _).eq, Matrix.mul_assoc]

omit [DecidableEq m] in
lemma rangeProjection_sq (F : Matrix m n ℂ) :
    rangeProjection F * rangeProjection F = rangeProjection F := by
  have h := supportInverse_mul_self_mul (Matrix.isHermitian_conjTranspose_mul_self F)
  unfold rangeProjection
  calc
    _ = F * (supportInverse (Fᴴ * F) * (Fᴴ * F) * supportInverse (Fᴴ * F)) * Fᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

lemma complement_posSemidef (F : Matrix m n ℂ) : (1 - rangeProjection F).PosSemidef := by
  have h : (1 - rangeProjection F)ᴴ * (1 - rangeProjection F) = 1 - rangeProjection F := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (rangeProjection_isHermitian F).eq,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, rangeProjection_sq]
    abel
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma complement_pullback (F : Matrix m n ℂ) :
    Fᴴ * (1 - rangeProjection F) * F = 0 := by
  have h := self_mul_supportInverse_mul (Matrix.isHermitian_conjTranspose_mul_self F)
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  change Fᴴ * F - Fᴴ * (F * supportInverse (Fᴴ * F) * Fᴴ) * F = 0
  rw [show Fᴴ * (F * supportInverse (Fᴴ * F) * Fᴴ) * F =
      (Fᴴ * F) * supportInverse (Fᴴ * F) * (Fᴴ * F) by simp only [Matrix.mul_assoc], h,
    sub_self]

variable {A : Type u_A} [Fintype A] [DecidableEq A]

def transportedEffect (F : Matrix m n ℂ) (G : A → Matrix n n ℂ) (a₀ a : A) : Matrix m m ℂ :=
  (F * supportInverse (Fᴴ * F)) * G a * (F * supportInverse (Fᴴ * F))ᴴ +
    if a = a₀ then 1 - rangeProjection F else 0

omit [Fintype A] in
lemma transportedEffect_pos (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (a₀ a : A) : (transportedEffect F G a₀ a).PosSemidef := by
  apply ((hG a).mul_mul_conjTranspose_same _).add
  split_ifs
  · exact complement_posSemidef F
  · exact Matrix.PosSemidef.zero

lemma transportedEffect_sum (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∑ a, G a = Fᴴ * F) (a₀ : A) : ∑ a, transportedEffect F G a₀ a = 1 := by
  have h := supportInverse_mul_self_mul (Matrix.isHermitian_conjTranspose_mul_self F)
  simp only [transportedEffect, Finset.sum_add_distrib, ← Matrix.sum_mul, ← Matrix.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hG, Matrix.conjTranspose_mul,
    (supportInverse_isHermitian _).eq]
  rw [show (F * supportInverse (Fᴴ * F)) * (Fᴴ * F) * (supportInverse (Fᴴ * F) * Fᴴ) =
      F * (supportInverse (Fᴴ * F) * (Fᴴ * F) * supportInverse (Fᴴ * F)) * Fᴴ by
      simp only [Matrix.mul_assoc], h]
  unfold rangeProjection
  abel

lemma transportedEffect_pullback (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ * F) (a₀ a : A) :
    Fᴴ * transportedEffect F G a₀ a * F = G a := by
  have hle : G a ≤ Fᴴ * F := by
    rw [← hGT]
    exact Finset.single_le_sum (fun b _ => (hG b).nonneg) (Finset.mem_univ a)
  have hherm := Matrix.isHermitian_conjTranspose_mul_self F
  unfold transportedEffect
  rw [Matrix.mul_add, Matrix.add_mul]
  have hzero : Fᴴ * (if a = a₀ then 1 - rangeProjection F else 0) * F = 0 := by
    split_ifs
    · exact complement_pullback F
    · simp
  rw [hzero, add_zero, Matrix.conjTranspose_mul,
    (supportInverse_isHermitian _).eq]
  calc
    _ = ((Fᴴ * F) * supportInverse (Fᴴ * F)) * G a * (supportInverse (Fᴴ * F) * (Fᴴ * F)) := by
      simp only [Matrix.mul_assoc]
    _ = G a := by rw [left_support hherm (hG a) hle, right_support hherm (hG a) hle]

theorem measurement_transport (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ * F) (a₀ : A) :
    ∃ E : A → Matrix m m ℂ, (∀ a, (E a).PosSemidef) ∧ ∑ a, E a = 1 ∧
      ∀ a, Fᴴ * E a * F = G a := by
  exact ⟨transportedEffect F G a₀, transportedEffect_pos F G hG a₀,
    transportedEffect_sum F G hGT a₀, transportedEffect_pullback F G hG hGT a₀⟩

end ThresholdParallelRepetition.MeasurementTransport

end

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

def hsSq (M : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

lemma hsSq_nonneg (M : Matrix m n ℂ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma hsSq_conjTranspose (M : Matrix m n ℂ) : hsSq Mᴴ = hsSq M := by
  simp only [hsSq, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

lemma hsSq_eq_trace (M : Matrix m n ℂ) : hsSq M = (Matrix.trace (Mᴴ * M)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, hsSq]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  simp [Complex.mul_re, Complex.normSq_apply]

lemma hsSq_eq_trace' (M : Matrix m n ℂ) : hsSq M = (Matrix.trace (M * Mᴴ)).re := by
  rw [← hsSq_conjTranspose M, hsSq_eq_trace, Matrix.conjTranspose_conjTranspose]

lemma hsSq_mul_left {U : Matrix m m ℂ} [DecidableEq m] (hU : Uᴴ * U = 1)
    (M : Matrix m n ℂ) : hsSq (U * M) = hsSq M := by
  rw [hsSq_eq_trace, Matrix.conjTranspose_mul]
  rw [show (Mᴴ * Uᴴ) * (U * M) = Mᴴ * (Uᴴ * U) * M by simp only [Matrix.mul_assoc],
    hU, Matrix.mul_one, ← hsSq_eq_trace]

lemma hsSq_mul_right {U : Matrix n n ℂ} [DecidableEq n] (hU : U * Uᴴ = 1)
    (M : Matrix m n ℂ) : hsSq (M * U) = hsSq M := by
  rw [← hsSq_conjTranspose, Matrix.conjTranspose_mul]
  rw [hsSq_mul_left (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hU),
    hsSq_conjTranspose]

lemma hsSq_spectral_mixed [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    hsSq (cfc f A - cfc g B) =
      ∑ i, ∑ j, (f (hA.eigenvalues i) - g (hB.eigenvalues j)) ^ 2 *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hB.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let V : Matrix n n ℂ := hB.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property
  have hUU' : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
  have hVV : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.property
  have hVV' : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.property
  have hf : cfc f A = U * Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * Uᴴ := by
    erw [hA.cfc_eq]
    rfl
  have hg : cfc g B = V * Matrix.diagonal (fun i => (g (hB.eigenvalues i) : ℂ)) * Vᴴ := by
    erw [hB.cfc_eq]
    rfl
  have hmixed : Uᴴ * (cfc f A - cfc g B) * V =
      Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * (Uᴴ * V) -
      (Uᴴ * V) * Matrix.diagonal (fun i => (g (hB.eigenvalues i) : ℂ)) := by
    rw [hf, hg, Matrix.mul_sub, Matrix.sub_mul]
    simp only [← Matrix.mul_assoc, hUU', Matrix.one_mul]
    simp only [Matrix.mul_assoc, hVV', Matrix.mul_one]
  rw [← hsSq_mul_left (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hUU)
      (cfc f A - cfc g B),
    ← hsSq_mul_right hVV (Uᴴ * (cfc f A - cfc g B)), hmixed]
  unfold hsSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_comm ((Uᴴ * V) i j), ← sub_mul, ← Complex.ofReal_sub, Complex.normSq_mul,
    Complex.normSq_ofReal]
  simp only [pow_two]
  rfl

lemma hsSq_cfc_sub_le [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ)
    (hf : ∀ s t : ℝ, (f s - f t)^2 ≤ L * (s - t)^2) :
    hsSq (cfc f A - cfc f B) ≤ L * hsSq (A - B) := by
  have hident := hsSq_spectral_mixed hA hB (fun x => x) (fun x => x)
  erw [cfc_id' ℝ A hA, cfc_id' ℝ B hB] at hident
  rw [hsSq_spectral_mixed hA hB, hident, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (hf (hA.eigenvalues i) (hB.eigenvalues j)) (Complex.normSq_nonneg _)

lemma hsSq_abs_sub_le [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hsSq (cfc (fun t : ℝ => |t|) A - cfc (fun t : ℝ => |t|) B) ≤ hsSq (A - B) := by
  simpa using hsSq_cfc_sub_le hA hB (fun t : ℝ => |t|) 1 (fun s t => by
    have h := abs_abs_sub_abs_le_abs_sub s t
    nlinarith [sq_nonneg (|s-t| - |(|s| - |t|)|), abs_nonneg (s-t), abs_nonneg (|s|-|t|),
      sq_abs (s-t), sq_abs (|s|-|t|)])

lemma hsSq_zero : hsSq (0 : Matrix m n ℂ) = 0 := by simp [hsSq]

lemma hsSq_blocks {q : Type u_q} [Fintype q] (A : Matrix m n ℂ) (B : Matrix m p ℂ)
    (C : Matrix q n ℂ) (D : Matrix q p ℂ) :
    hsSq (Matrix.fromBlocks A B C D) = hsSq A + hsSq B + hsSq C + hsSq D := by
  simp only [hsSq, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Finset.sum_add_distrib]
  ring

omit [Fintype m] [Fintype n] [Fintype p] in
lemma fromBlocks_sub {q : Type u_q} (A A' : Matrix m n ℂ) (B B' : Matrix m p ℂ)
    (C C' : Matrix q n ℂ) (D D' : Matrix q p ℂ) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A-A') (B-B') (C-C') (D-D') := by
  ext i j
  cases i <;> cases j <;> rfl

lemma block_diagonal_pos [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  have hRa := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hRb := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  have hR : (Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B))ᴴ *
      (Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B)) = Matrix.fromBlocks A 0 0 B := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, hRa, hRb,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  rw [← hR]
  exact Matrix.posSemidef_conjTranspose_mul_self _

def dilation (M : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks 0 M Mᴴ 0

omit [Fintype m] [Fintype n] in
lemma dilation_isHermitian (M : Matrix m n ℂ) : (dilation M).IsHermitian := by
  unfold Matrix.IsHermitian dilation
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_conjTranspose]

lemma abs_square [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun t : ℝ => |t|) A * cfc (fun t : ℝ => |t|) A = A * A := by
  erw [← cfc_mul (fun t : ℝ => |t|) (fun t : ℝ => |t|) A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  calc
    _ = cfc (fun t : ℝ => t * t) A := by
      apply cfc_congr
      intro t _
      nlinarith [sq_abs t]
    _ = cfc (fun t : ℝ => t) A * cfc (fun t : ℝ => t) A := by
      erw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ = _ := by erw [cfc_id' ℝ A hA]

lemma abs_eq_sqrt_square [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun t : ℝ => |t|) A = CFC.sqrt (A * A) := by
  apply Eq.symm
  exact CFC.sqrt_unique (abs_square hA) (cfc_nonneg fun t _ => abs_nonneg t)

lemma sqrt_block_diagonal [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) := by
  have hpos : 0 ≤ Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) :=
    (block_diagonal_pos (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg
  apply CFC.sqrt_unique _ hpos
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, CFC.sqrt_mul_sqrt_self _ hA.nonneg, CFC.sqrt_mul_sqrt_self _ hB.nonneg]

lemma abs_dilation [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) :
    cfc (fun t : ℝ => |t|) (dilation M) =
      Matrix.fromBlocks (CFC.sqrt (M * Mᴴ)) 0 0 (CFC.sqrt (Mᴴ * M)) := by
  rw [abs_eq_sqrt_square (dilation_isHermitian M)]
  unfold dilation
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  exact sqrt_block_diagonal (Matrix.posSemidef_self_mul_conjTranspose M)
    (Matrix.posSemidef_conjTranspose_mul_self M)

theorem hsSq_right_absolute_sub_le [DecidableEq m] [DecidableEq n] (M N : Matrix m n ℂ) :
    hsSq (CFC.sqrt (Mᴴ * M) - CFC.sqrt (Nᴴ * N)) ≤ 2 * hsSq (M - N) := by
  have h := hsSq_abs_sub_le (dilation_isHermitian M) (dilation_isHermitian N)
  rw [abs_dilation M, abs_dilation N] at h
  simp only [dilation, fromBlocks_sub, sub_self, hsSq_blocks, hsSq_zero, zero_add, add_zero] at h
  rw [← Matrix.conjTranspose_sub, hsSq_conjTranspose] at h
  linarith [hsSq_nonneg (CFC.sqrt (M * Mᴴ) - CFC.sqrt (N * Nᴴ))]

end ThresholdParallelRepetition.QuantumSampling

end

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open MeasureTheory Set
open scoped Interval

namespace ThresholdParallelRepetition.QuantumSampling

lemma floor_shift_monotone (u : ℝ) : Monotone (fun s : ℝ => (⌊u+s⌋ : ℝ)) := by
  intro s t h
  change (⌊u+s⌋ : ℝ) ≤ (⌊u+t⌋ : ℝ)
  exact_mod_cast Int.floor_mono (show u+s ≤ u+t by linarith)

lemma integral_floor_shift (u : ℝ) : (∫ s in (0:ℝ)..1, (⌊u+s⌋ : ℝ)) = u := by
  let c := 1 - Int.fract u
  have hc0 : 0 ≤ c := by dsimp [c]; linarith [Int.fract_lt_one u]
  have hc1 : c ≤ 1 := by dsimp [c]; linarith [Int.fract_nonneg u]
  have hu : Int.fract u + (⌊u⌋ : ℝ) = u := Int.fract_add_floor u
  have hleft : (∫ s in (0:ℝ)..c, (⌊u+s⌋ : ℝ)) = c * (⌊u⌋ : ℝ) := by
    calc
      _ = ∫ _ in (0:ℝ)..c, (⌊u⌋ : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc0
        intro s hs
        dsimp only
        have he : ⌊u+s⌋ = ⌊u⌋ := Int.floor_eq_iff.mpr ⟨by linarith [Int.fract_nonneg u, hs.1], by dsimp [c] at hs; linarith [hs.2]⟩
        rw [he]
      _ = _ := by simp
  have hright : (∫ s in c..(1:ℝ), (⌊u+s⌋ : ℝ)) = (1-c) * ((⌊u⌋ : ℝ)+1) := by
    calc
      _ = ∫ _ in c..(1:ℝ), ((⌊u⌋ : ℝ)+1) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc1
        intro s hs
        dsimp only
        have he : ⌊u+s⌋ = ⌊u⌋ + 1 := Int.floor_eq_iff.mpr ⟨by push_cast; dsimp [c] at hs; linarith [hs.1], by push_cast; linarith [Int.fract_lt_one u, hs.2]⟩
        rw [he]; push_cast; rfl
      _ = _ := by simp; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((floor_shift_monotone u).intervalIntegrable (μ := volume) (a := 0) (b := c))
    ((floor_shift_monotone u).intervalIntegrable (μ := volume) (a := c) (b := 1)), hleft, hright]
  dsimp [c]
  nlinarith

def separated (u v s : ℝ) : ℝ := if ⌊u+s⌋ = ⌊v+s⌋ then 0 else 1

lemma separated_nonneg (u v s : ℝ) : 0 ≤ separated u v s := by unfold separated; split <;> norm_num
lemma separated_le_one (u v s : ℝ) : separated u v s ≤ 1 := by unfold separated; split <;> norm_num
lemma separated_symm (u v s : ℝ) : separated u v s = separated v u s := by simp [separated, eq_comm]

lemma separated_measurable (u v : ℝ) : Measurable (separated u v) := by
  unfold separated
  exact measurable_const.ite (measurableSet_eq_fun ((measurable_const.add measurable_id).floor)
    ((measurable_const.add measurable_id).floor)) measurable_const

lemma separated_integrable (u v a b : ℝ) : IntervalIntegrable (separated u v) volume a b := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun' (separated_measurable u v).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by dsimp only; rw [Real.norm_eq_abs, abs_of_nonneg (separated_nonneg u v s)]; exact separated_le_one u v s

lemma separated_le_floor_sub {u v : ℝ} (huv : u ≤ v) (s : ℝ) :
    separated u v s ≤ (⌊v+s⌋ : ℝ) - (⌊u+s⌋ : ℝ) := by
  unfold separated
  split_ifs with h
  · rw [h]; simp
  · have hle : ⌊u+s⌋ ≤ ⌊v+s⌋ := Int.floor_mono (by linarith)
    have hlt : ⌊u+s⌋ + 1 ≤ ⌊v+s⌋ := by omega
    exact_mod_cast (show (1:ℤ) ≤ ⌊v+s⌋ - ⌊u+s⌋ by omega)

lemma integral_separated_le {u v : ℝ} :
    (∫ s in (0:ℝ)..1, separated u v s) ≤ |u-v| := by
  wlog huv : u ≤ v generalizing u v
  · rw [show separated u v = separated v u by funext s; exact separated_symm _ _ _]
    simpa only [abs_sub_comm] using this (le_of_not_ge huv)
  calc
    _ ≤ ∫ s in (0:ℝ)..1, ((⌊v+s⌋ : ℝ) - (⌊u+s⌋ : ℝ)) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (separated_integrable _ _ _ _)
        (((floor_shift_monotone v).intervalIntegrable).sub ((floor_shift_monotone u).intervalIntegrable))
      intro s _
      exact separated_le_floor_sub huv s
    _ = v-u := by rw [intervalIntegral.integral_sub
      ((floor_shift_monotone v).intervalIntegrable) ((floor_shift_monotone u).intervalIntegrable),
      integral_floor_shift, integral_floor_shift]
    _ = |u-v| := by rw [abs_of_nonpos (by linarith)]; ring

def binEnvelope (a b ε s : ℝ) : ℝ :=
  (a-b)^2 + 2*a*b*separated (Real.log a/ε) (Real.log b/ε) s

lemma binEnvelope_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ε s : ℝ) :
    0 ≤ binEnvelope a b ε s := by
  unfold binEnvelope
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (separated_nonneg _ _ _))

lemma binEnvelope_integrable (a b ε l r : ℝ) :
    IntervalIntegrable (binEnvelope a b ε) volume l r := by
  exact intervalIntegrable_const.add ((separated_integrable _ _ _ _).const_mul _)

lemma log_difference_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a * (Real.log b - Real.log a) ≤ b-a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hh := mul_le_mul_of_nonneg_left h ha.le
  calc
    _ ≤ a*(b/a-1) := hh
    _ = b-a := by field_simp

lemma logarithmic_envelope_bound {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (a-b)^2 + 2*a*b*(|Real.log a-Real.log b|/ε) ≤ 3/ε * |a-b| * (a+b) := by
  wlog hab : a ≤ b generalizing a b
  · have hh := this hb ha (le_of_not_ge hab)
    simpa only [abs_sub_comm b a, abs_sub_comm (Real.log b) (Real.log a),
      add_comm b a, sub_sq_comm b a, mul_right_comm (2:ℝ) b a] using hh
  rw [abs_of_nonpos (sub_nonpos.mpr hab)]
  by_cases ha0 : a = 0
  · subst a
    simp only [zero_sub, neg_neg, zero_mul, mul_zero, zero_add, neg_sq, add_zero]
    apply (le_mul_of_one_le_left (sq_nonneg b) (show 1 ≤ 3/ε by apply (le_div_iff₀ hε).mpr; linarith)).trans_eq
    ring
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_lt_of_le hap hab
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hap hab))]
  have hl := log_difference_bound hap hab
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*b by positivity)
  have hsq : (a-b)^2 ≤ (b-a)*(a+b) := by nlinarith
  apply (mul_le_mul_iff_of_pos_right hε).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hε1 (sq_nonneg (a-b)), mul_nonneg ha (sub_nonneg.mpr hab)]

lemma integral_binEnvelope_le {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ s in (0:ℝ)..1, binEnvelope a b ε s) ≤ 3/ε * |a-b| * (a+b) := by
  calc
    _ ≤ (a-b)^2 + 2*a*b*(|Real.log a-Real.log b|/ε) := by
      unfold binEnvelope
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((separated_integrable _ _ _ _).const_mul _), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul]
      simp only [sub_zero, one_smul]
      apply add_le_add_right
      have hi := integral_separated_le (u := Real.log a/ε) (v := Real.log b/ε)
      rw [← sub_div, abs_div, abs_of_pos hε] at hi
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ _ := logarithmic_envelope_bound ha hb hε hε1

def binWeight (a ε s : ℝ) : ℝ :=
  if 0 < a then Real.exp (ε*((⌊Real.log a/ε+s⌋ : ℝ)-s)) else 0

lemma binWeight_nonneg (a ε s : ℝ) : 0 ≤ binWeight a ε s := by
  unfold binWeight; split <;> positivity

lemma binWeight_le {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (s : ℝ) :
    binWeight a ε s ≤ a := by
  unfold binWeight
  split_ifs with hap
  · apply le_trans (b := Real.exp (Real.log a))
    · apply Real.exp_le_exp.mpr
      have hf := Int.floor_le (Real.log a/ε+s)
      have hm := mul_le_mul_of_nonneg_left hf hε.le
      have he : ε*(Real.log a/ε+s) = Real.log a + ε*s := by field_simp
      linarith
    · exact (Real.exp_log hap).le
  · exact ha

lemma sub_binWeight_le {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (s : ℝ) :
    a - binWeight a ε s ≤ ε*a := by
  unfold binWeight
  split_ifs with hap
  · have hf := Int.lt_floor_add_one (Real.log a/ε+s)
    have hm := mul_lt_mul_of_pos_left hf hε
    have he : ε*(Real.log a/ε+s) = Real.log a + ε*s := by field_simp
    have hex : Real.exp (Real.log a - ε) ≤ Real.exp (ε*((⌊Real.log a/ε+s⌋ : ℝ)-s)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_sub, Real.exp_log hap] at hex
    have hex' : (1-ε)*a ≤ a / Real.exp ε := by
      have hh := Real.add_one_le_exp (-ε)
      rw [Real.exp_neg] at hh
      have hmul := mul_le_mul_of_nonneg_right hh ha
      simpa only [neg_add_eq_sub, div_eq_mul_inv, mul_comm] using hmul
    linarith
  · have : a = 0 := le_antisymm (le_of_not_gt hap) ha
    simp [this]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma unitary_row_normSq {U : Matrix n n ℂ} (hU : U * Uᴴ = 1) (i : n) :
    ∑ j, Complex.normSq (U i j) = 1 := by
  have h := congrArg Complex.re (congrFun (congrFun hU i) i)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.re_sum, Complex.one_re, Complex.star_def, Complex.mul_conj, Complex.ofReal_re] using h

lemma unitary_col_normSq {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (j : n) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj] using
    unitary_row_normSq (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hU) j

lemma hsSq_cfc_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    hsSq (cfc f A) = ∑ i, (f (hA.eigenvalues i))^2 := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
  have he : cfc f A = U * Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * Uᴴ := by
    erw [hA.cfc_eq]; rfl
  rw [he, hsSq_mul_right (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hU), hsSq_mul_left hU]
  unfold hsSq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [Complex.normSq_ofReal, pow_two]
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hji), Complex.normSq_zero]
  · simp

lemma hsSq_eq_sum_eigenvalues_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hsSq A = ∑ i, (hA.eigenvalues i)^2 := by
  have h := hsSq_cfc_eq hA (fun t => t)
  erw [cfc_id' ℝ A hA] at h
  exact h

def overlap {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) : ℝ :=
  Complex.normSq (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
    (hB.eigenvectorUnitary : Matrix n n ℂ)) i j)

lemma overlap_nonneg {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    0 ≤ overlap hA hB i j := Complex.normSq_nonneg _

lemma overlap_row {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i : n) :
    ∑ j, overlap hA hB i j = 1 := by
  apply unitary_row_normSq
  have h1 : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * hA.eigenvectorUnitary = 1 :=
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
  have h2 : (hB.eigenvectorUnitary : Matrix n n ℂ) * (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.property
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hB.eigenvectorUnitary : Matrix n n ℂ), h2, Matrix.one_mul, h1]

lemma overlap_col {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (j : n) :
    ∑ i, overlap hA hB i j = 1 := by
  apply unitary_col_normSq
  have h1 : (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property
  have h2 : (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ * hB.eigenvectorUnitary = 1 :=
    Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.property
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hA.eigenvectorUnitary : Matrix n n ℂ), h1, Matrix.one_mul, h2]

lemma overlap_distance {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i, ∑ j, (hA.eigenvalues i - hB.eigenvalues j)^2 * overlap hA hB i j) = hsSq (A-B) := by
  have h := hsSq_spectral_mixed hA hB (fun t => t) (fun t => t)
  erw [cfc_id' ℝ A hA, cfc_id' ℝ B hB] at h
  exact h.symm

lemma overlap_square_sum_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i, ∑ j, (hA.eigenvalues i + hB.eigenvalues j)^2 * overlap hA hB i j) ≤
    2 * (hsSq A + hsSq B) := by
  calc
    _ ≤ ∑ i, ∑ j, (2*(hA.eigenvalues i)^2 + 2*(hB.eigenvalues j)^2) * overlap hA hB i j := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (hA.eigenvalues i-hB.eigenvalues j)]) (overlap_nonneg _ _ _ _)
    _ = _ := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => 2*(hB.eigenvalues j)^2 * overlap hA hB i j)]
      simp_rw [← Finset.mul_sum, overlap_row, overlap_col, mul_one]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← hsSq_eq_sum_eigenvalues_sq hA,
        ← hsSq_eq_sum_eigenvalues_sq hB]
      ring

lemma overlap_transport_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i, ∑ j, |hA.eigenvalues i - hB.eigenvalues j| *
      (hA.eigenvalues i + hB.eigenvalues j) * overlap hA hB i j) ≤
      Real.sqrt (hsSq (A-B)) * Real.sqrt (2 * (hsSq A + hsSq B)) := by
  let r : n × n → ℝ := fun ij => |hA.eigenvalues ij.1 - hB.eigenvalues ij.2| *
    (hA.eigenvalues ij.1 + hB.eigenvalues ij.2) * overlap hA hB ij.1 ij.2
  let f : n × n → ℝ := fun ij => (hA.eigenvalues ij.1 - hB.eigenvalues ij.2)^2 * overlap hA hB ij.1 ij.2
  let g : n × n → ℝ := fun ij => (hA.eigenvalues ij.1 + hB.eigenvalues ij.2)^2 * overlap hA hB ij.1 ij.2
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (n × n))
    (r := r) (f := f) (g := g)
    (fun ij _ => mul_nonneg (sq_nonneg _) (overlap_nonneg _ _ _ _))
    (fun ij _ => mul_nonneg (sq_nonneg _) (overlap_nonneg _ _ _ _))
    (fun ij _ => by dsimp [r,f,g]; rw [mul_pow, mul_pow, sq_abs]; exact le_of_eq (by ring))
  have hf : ∑ ij, f ij = hsSq (A-B) := by rw [Fintype.sum_prod_type]; exact overlap_distance hA hB
  have hg : ∑ ij, g ij ≤ 2 * (hsSq A + hsSq B) := by rw [Fintype.sum_prod_type]; exact overlap_square_sum_le hA hB
  rw [hf] at hc
  have hbound := hc.trans (mul_le_mul_of_nonneg_left hg (hsSq_nonneg _))
  have hr : ∑ ij, r ij = ∑ i, ∑ j, |hA.eigenvalues i - hB.eigenvalues j| *
      (hA.eigenvalues i + hB.eigenvalues j) * overlap hA hB i j := by rw [Fintype.sum_prod_type]
  rw [hr] at hbound
  have hprod : (Real.sqrt (hsSq (A-B)) * Real.sqrt (2*(hsSq A+hsSq B)))^2 =
      hsSq (A-B)*(2*(hsSq A+hsSq B)) := by
    rw [mul_pow, Real.sq_sqrt (hsSq_nonneg _), Real.sq_sqrt (by linarith [hsSq_nonneg A, hsSq_nonneg B])]
  have hnon : 0 ≤ Real.sqrt (hsSq (A-B)) * Real.sqrt (2*(hsSq A+hsSq B)) := by positivity
  rw [← hprod] at hbound
  exact le_of_sq_le_sq hbound hnon

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Interval
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def spectralEnvelope {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ε s : ℝ) : ℝ := ∑ i, ∑ j, binEnvelope (hA.eigenvalues i) (hB.eigenvalues j) ε s * overlap hA hB i j

lemma spectralEnvelope_integrable {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ε : ℝ) : IntervalIntegrable (spectralEnvelope hA hB ε) volume 0 1 := by
  unfold spectralEnvelope
  simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ
    (fun i _ => IntervalIntegrable.sum Finset.univ
      (fun j _ => (binEnvelope_integrable (hA.eigenvalues i) (hB.eigenvalues j) ε 0 1).mul_const (overlap hA hB i j)))

lemma integral_spectralEnvelope_le {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ s in (0:ℝ)..1, spectralEnvelope hA.isHermitian hB.isHermitian ε s) ≤
    3/ε * (Real.sqrt (hsSq (A-B)) * Real.sqrt (2*(hsSq A+hsSq B))) := by
  unfold spectralEnvelope
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (by simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun j _ => (binEnvelope_integrable (hA.isHermitian.eigenvalues i) (hB.isHermitian.eigenvalues j) ε 0 1).mul_const (overlap hA.isHermitian hB.isHermitian i j))))]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => (binEnvelope_integrable _ _ _ _ _).mul_const _),
    intervalIntegral.integral_mul_const]
  calc
    _ ≤ ∑ i, ∑ j, (3/ε * |hA.isHermitian.eigenvalues i-hB.isHermitian.eigenvalues j| *
        (hA.isHermitian.eigenvalues i+hB.isHermitian.eigenvalues j)) * overlap hA.isHermitian hB.isHermitian i j := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_right
        (integral_binEnvelope_le (hA.eigenvalues_nonneg i) (hB.eigenvalues_nonneg j) hε hε1)
        (overlap_nonneg _ _ _ _)
    _ = (3/ε) * (∑ i, ∑ j, |hA.isHermitian.eigenvalues i-hB.isHermitian.eigenvalues j| *
        (hA.isHermitian.eigenvalues i+hB.isHermitian.eigenvalues j) * overlap hA.isHermitian hB.isHermitian i j) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (overlap_transport_le hA.isHermitian hB.isHermitian) (by positivity)

lemma hsSq_sqrt_gram (M : Matrix n n ℂ) : hsSq (CFC.sqrt (Mᴴ * M)) = hsSq M := by
  have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Mᴴ*M))).isHermitian.eq
  rw [hsSq_eq_trace, h, CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg,
    ← hsSq_eq_trace]

lemma integral_spectralEnvelope_unit_le {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAe : hsSq A = 1) (hBe : hsSq B = 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ s in (0:ℝ)..1, spectralEnvelope hA.isHermitian hB.isHermitian ε s) ≤
    (6/ε) * Real.sqrt (hsSq (A-B)) := by
  have h := integral_spectralEnvelope_le hA hB hε hε1
  rw [hAe, hBe] at h
  norm_num at h
  convert h using 1; ring

lemma weighted_sqrt_le {ι : Type u_ι} [Fintype ι] (w e : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hE : ∀ i, 0 ≤ e i) (hs : ∑ i, w i = 1) :
    (∑ i, w i * Real.sqrt (e i)) ≤ Real.sqrt (∑ i, w i * e i) := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (r := fun i => w i * Real.sqrt (e i)) (f := fun i => w i) (g := fun i => w i * e i)
    (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (hE i))
    (fun i _ => by rw [mul_pow, Real.sq_sqrt (hE i)]; exact le_of_eq (by ring))
  rw [hs, one_mul, ← Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hE i)))] at hc
  exact le_of_sq_le_sq hc (Real.sqrt_nonneg _)

lemma exists_shift_spectralEnvelope_le {ι : Type u_ι} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (hAe : ∀ i, hsSq (A i) = 1) (hBe : ∀ i, hsSq (B i) = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ s : ℝ, (∑ i, w i * spectralEnvelope (hA i).isHermitian (hB i).isHermitian ε s) ≤
      (6/ε) * Real.sqrt (∑ i, w i * hsSq (A i-B i)) := by
  let F : ℝ → ℝ := fun s => ∑ i, w i * spectralEnvelope (hA i).isHermitian (hB i).isHermitian ε s
  have hF : IntervalIntegrable F volume 0 1 := by
    simpa only [F, Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun i _ => (spectralEnvelope_integrable (hA i).isHermitian (hB i).isHermitian ε).const_mul (w i))
  let : IsProbabilityMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := ⟨by simp⟩
  obtain ⟨s, hsF⟩ := MeasureTheory.exists_le_integral hF.1
  refine ⟨s, hsF.trans ?_⟩
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  unfold F
  rw [intervalIntegral.integral_finsetSum (fun i _ => (spectralEnvelope_integrable _ _ _).const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul]
  calc
    _ ≤ ∑ i, w i * ((6/ε) * Real.sqrt (hsSq (A i-B i))) := by
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (integral_spectralEnvelope_unit_le (hA i) (hB i) (hAe i) (hBe i) hε hε1) (hw i)
    _ = (6/ε) * ∑ i, w i * Real.sqrt (hsSq (A i-B i)) := by simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_sqrt_le w _ hw (fun i => hsSq_nonneg _) hs) (by positivity)

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

def binScale (ε s : ℝ) (l : ℤ) : ℝ := Real.exp (ε*((l:ℝ)-s))
def binIndicator (ε s : ℝ) (l : ℤ) (a : ℝ) : ℝ :=
  if 0 < a ∧ ⌊Real.log a/ε+s⌋ = l then 1 else 0

lemma binIndicator_nonneg (ε s : ℝ) (l : ℤ) (a : ℝ) : 0 ≤ binIndicator ε s l a := by
  unfold binIndicator; split <;> norm_num
lemma binIndicator_sq (ε s : ℝ) (l : ℤ) (a : ℝ) : (binIndicator ε s l a)^2 = binIndicator ε s l a := by
  unfold binIndicator; split <;> norm_num
lemma binIndicator_mul_ne (ε s : ℝ) {l k : ℤ} (hlk : l ≠ k) (a : ℝ) :
    binIndicator ε s l a * binIndicator ε s k a = 0 := by
  unfold binIndicator
  split_ifs <;> simp_all

lemma sum_binIndicator_weight_sq_le (L : Finset ℤ) (ε s a : ℝ) :
    (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l a)^2) ≤ (binWeight a ε s)^2 := by
  simp only [binIndicator_sq]
  by_cases ha : 0 < a
  · simp only [binIndicator, ha, true_and, mul_ite, mul_one, mul_zero, binWeight, ite_true]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · positivity
  · simp [binIndicator, ha, binWeight]

lemma scalar_mismatch_le (L : Finset ℤ) (ε s : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l a-binIndicator ε s l b)^2) ≤
      binEnvelope a b ε s := by
  have hh : (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l a-binIndicator ε s l b)^2) ≤ a^2+b^2 := by
    calc
      _ ≤ ∑ l ∈ L, (binScale ε s l)^2 * ((binIndicator ε s l a)^2+(binIndicator ε s l b)^2) := by
        apply Finset.sum_le_sum; intro l _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith [mul_nonneg (binIndicator_nonneg ε s l a) (binIndicator_nonneg ε s l b)]
      _ = (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l a)^2) +
        (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l b)^2) := by simp [mul_add, Finset.sum_add_distrib]
      _ ≤ (binWeight a ε s)^2 + (binWeight b ε s)^2 := add_le_add
          (sum_binIndicator_weight_sq_le L ε s a) (sum_binIndicator_weight_sq_le L ε s b)
      _ ≤ a^2+b^2 := by
        have ha' := binWeight_le ha hε s
        have hb' := binWeight_le hb hε s
        nlinarith [binWeight_nonneg a ε s, binWeight_nonneg b ε s]
  by_cases ha0 : a = 0
  · simpa [binEnvelope, ha0] using hh
  by_cases hb0 : b = 0
  · simpa [binEnvelope, hb0] using hh
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases he : ⌊Real.log a/ε+s⌋ = ⌊Real.log b/ε+s⌋
  · have hi : ∀ l, binIndicator ε s l a = binIndicator ε s l b := by intro l; simp [binIndicator, hap, hbp, he]
    simp only [hi, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
    exact binEnvelope_nonneg ha hb ε s
  · have hen : binEnvelope a b ε s = a^2+b^2 := by simp only [binEnvelope, separated, ite_eq_right he]; ring
    rw [hen]; exact hh

variable {n : Type u_n} [Fintype n] [DecidableEq n]

def binProjection (A : Matrix n n ℂ) (ε s : ℝ) (l : ℤ) : Matrix n n ℂ :=
  cfc (binIndicator ε s l) A

lemma binProjection_hermitian (A : Matrix n n ℂ) (ε s : ℝ) (l : ℤ) :
    (binProjection A ε s l).IsHermitian := (cfc_predicate (binIndicator ε s l) A).isHermitian

lemma binProjection_pos (A : Matrix n n ℂ) (ε s : ℝ) (l : ℤ) :
    (binProjection A ε s l).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg (fun a _ => binIndicator_nonneg ε s l a))

lemma binProjection_sq {A : Matrix n n ℂ} (_hA : A.IsHermitian) (ε s : ℝ) (l : ℤ) :
    binProjection A ε s l * binProjection A ε s l = binProjection A ε s l := by
  unfold binProjection
  erw [← cfc_mul (binIndicator ε s l) (binIndicator ε s l) A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro a _
  simpa only [pow_two] using binIndicator_sq ε s l a

lemma binProjection_orthogonal {A : Matrix n n ℂ} (_hA : A.IsHermitian) (ε s : ℝ)
    {l k : ℤ} (hlk : l ≠ k) : binProjection A ε s l * binProjection A ε s k = 0 := by
  unfold binProjection
  erw [← cfc_mul (binIndicator ε s l) (binIndicator ε s k) A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 0) A := by apply cfc_congr; intro a _; exact binIndicator_mul_ne ε s hlk a
    _ = 0 := cfc_zero ℝ A

lemma binProjection_mismatch_le (L : Finset ℤ) {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    (∑ l ∈ L, (binScale ε s l)^2 * hsSq (binProjection A ε s l-binProjection B ε s l)) ≤
    spectralEnvelope hA.isHermitian hB.isHermitian ε s := by
  unfold binProjection spectralEnvelope
  simp_rw [hsSq_spectral_mixed hA.isHermitian hB.isHermitian, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro j _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (scalar_mismatch_le L ε s (hA.eigenvalues_nonneg i) (hB.eigenvalues_nonneg j) hε)
    (overlap_nonneg _ _ _ _)

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open ThresholdParallelRepetition.MeasurementTransport
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq n]

lemma hsSq_mul_contraction {W : Matrix m n ℂ} (hW : Wᴴ*W ≤ 1)
    {p : Type u_p} [Fintype p] (M : Matrix n p ℂ) : hsSq (W*M) ≤ hsSq M := by
  have hpos := (Matrix.le_iff.mp hW).conjTranspose_mul_mul_same M
  have ht := (Complex.nonneg_iff.mp hpos.trace_nonneg).1
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at ht
  rw [hsSq_eq_trace, hsSq_eq_trace]
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using sub_nonneg.mp ht

def rightAbs (M : Matrix m n ℂ) : Matrix n n ℂ := CFC.sqrt (Mᴴ*M)
def polar (M : Matrix m n ℂ) : Matrix m n ℂ := M * supportInverse (rightAbs M)

lemma rightAbs_pos (M : Matrix m n ℂ) : (rightAbs M).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
lemma rightAbs_sq (M : Matrix m n ℂ) : rightAbs M * rightAbs M = Mᴴ*M :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg

lemma supportInverse_mul_le_one {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    supportInverse A * A ≤ 1 := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  change cfc (fun t : ℝ => t⁻¹) A * A ≤ 1
  calc
    _ = cfc (fun t : ℝ => t⁻¹*t) A := by
      calc
        _ = cfc (fun t : ℝ => t⁻¹) A * cfc (fun t : ℝ => t) A := by rw [hid]
        _ = _ := by
          erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ ≤ 1 := cfc_le_one _ A (by intro t _; by_cases ht : t = 0 <;> simp [ht])

lemma polar_gram (M : Matrix m n ℂ) :
    (polar M)ᴴ * polar M = supportInverse (rightAbs M) * rightAbs M := by
  let A := rightAbs M
  let D := supportInverse A
  have hA : A.IsHermitian := (rightAbs_pos M).isHermitian
  have hD : Dᴴ = D := (supportInverse_isHermitian A).eq
  change (M*D)ᴴ*(M*D) = D*A
  rw [Matrix.conjTranspose_mul, hD]
  calc
    _ = D*(Mᴴ*M)*D := by simp only [Matrix.mul_assoc]
    _ = D*(A*A)*D := by rw [rightAbs_sq]
    _ = D*A*(A*D) := by simp only [Matrix.mul_assoc]
    _ = D*A*(D*A) := by rw [show A*D=D*A from (supportInverse_commute hA).symm]
    _ = (D*A*D)*A := by simp only [Matrix.mul_assoc]
    _ = D*A := by rw [supportInverse_mul_self_mul hA]

lemma polar_contraction (M : Matrix m n ℂ) : (polar M)ᴴ*polar M ≤ 1 := by
  rw [polar_gram]
  exact supportInverse_mul_le_one (rightAbs_pos M).isHermitian

lemma polar_mul_rightAbs (M : Matrix m n ℂ) : polar M * rightAbs M = M := by
  let A := rightAbs M
  let D := supportInverse A
  have hA : A.IsHermitian := (rightAbs_pos M).isHermitian
  have hzero : (Mᴴ*M)*(1-D*A) = 0 := by
    rw [← rightAbs_sq M]
    change (A*A)*(1-D*A)=0
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      self_mul_supportInverse_mul hA, sub_self, Matrix.mul_zero]
  have hz := (Matrix.conjTranspose_mul_self_mul_eq_zero M (1-D*A)).mp hzero
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz
  simpa only [polar, Matrix.mul_assoc] using hz.symm

lemma supportInverse_bin {A : Matrix n n ℂ} (hA : A.IsHermitian) (ε s : ℝ) (l : ℤ) :
    (supportInverse A*A)*binProjection A ε s l = binProjection A ε s l := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  unfold supportInverse binProjection
  calc
    _ = cfc (fun t : ℝ => t⁻¹*t*binIndicator ε s l t) A := by
      calc
        _ = cfc (fun t : ℝ => t⁻¹) A * cfc (fun t : ℝ => t) A * cfc (binIndicator ε s l) A := by rw [hid]
        _ = _ := by
          erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
        ← cfc_mul (fun t : ℝ => t⁻¹*t) (binIndicator ε s l) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ = _ := by
      apply cfc_congr; intro t _
      by_cases ht : 0 < t
      · simp [ne_of_gt ht]
      · simp [binIndicator, ht]

lemma polar_gram_bin (M : Matrix m n ℂ) (ε s : ℝ) (l : ℤ) :
    ((polar M)ᴴ*polar M)*binProjection (rightAbs M) ε s l = binProjection (rightAbs M) ε s l := by
  rw [polar_gram]
  exact supportInverse_bin (rightAbs_pos M).isHermitian ε s l

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma projection_le_one {P : Matrix n n ℂ} (hP : P.IsHermitian) (hPP : P*P=P) : P ≤ 1 := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1-P)
  have he : (1-P)ᴴ*(1-P)=1-P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP, sub_self, sub_zero]
  rw [he] at h
  exact Matrix.le_iff.mpr h

def binFilter (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) : Matrix n (n × L) ℂ :=
  fun i jl => (polar M * binProjection (rightAbs M) ε s jl.2) i jl.1

lemma binFilter_gram (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) :
    (binFilter L M ε s)ᴴ * binFilter L M ε s =
      Matrix.blockDiagonal (fun l : L => binProjection (rightAbs M) ε s l) := by
  ext ⟨i,l⟩ ⟨j,k⟩
  change (((polar M * binProjection (rightAbs M) ε s l)ᴴ *
    (polar M * binProjection (rightAbs M) ε s k)) i j) = _
  rw [Matrix.conjTranspose_mul, (binProjection_hermitian _ _ _ _).eq]
  rw [show (binProjection (rightAbs M) ε s l * (polar M)ᴴ) *
      (polar M * binProjection (rightAbs M) ε s k) =
      binProjection (rightAbs M) ε s l * (((polar M)ᴴ*polar M)*binProjection (rightAbs M) ε s k)
      by simp only [Matrix.mul_assoc], polar_gram_bin]
  by_cases hlk : l = k
  · subst k
    rw [binProjection_sq (rightAbs_pos M).isHermitian]
    exact (Matrix.blockDiagonal_apply_eq (fun l : L => binProjection (rightAbs M) ε s l) i j l).symm
  · rw [binProjection_orthogonal (rightAbs_pos M).isHermitian ε s (Subtype.coe_ne_coe.mpr hlk)]
    simp only [Matrix.zero_apply, Matrix.blockDiagonal_apply, ite_eq_right hlk]

lemma binFilter_contraction (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) :
    (binFilter L M ε s)ᴴ * binFilter L M ε s ≤ 1 := by
  rw [binFilter_gram]
  apply projection_le_one
  · change (Matrix.blockDiagonal (fun l : L => binProjection (rightAbs M) ε s l))ᴴ = _
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext l
    exact (binProjection_hermitian _ _ _ _).eq
  · rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext l
    exact binProjection_sq (rightAbs_pos M).isHermitian ε s l

def roundedAbs (A : Matrix n n ℂ) (ε s : ℝ) : Matrix n n ℂ := cfc (fun a => binWeight a ε s) A

lemma roundedAbs_energy_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) : hsSq (roundedAbs A ε s) ≤ hsSq A := by
  rw [roundedAbs, hsSq_cfc_eq hA.isHermitian, hsSq_eq_sum_eigenvalues_sq hA.isHermitian]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [binWeight_le (hA.eigenvalues_nonneg i) hε s, binWeight_nonneg (hA.isHermitian.eigenvalues i) ε s]

lemma roundedAbs_error_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) : hsSq (A-roundedAbs A ε s) ≤ ε^2*hsSq A := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA.isHermitian
  have he : A-roundedAbs A ε s = cfc (fun a => a-binWeight a ε s) A := by
    erw [cfc_sub (fun t : ℝ => t) (fun a => binWeight a ε s) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    rw [hid]; rfl
  rw [he, hsSq_cfc_eq hA.isHermitian, hsSq_eq_sum_eigenvalues_sq hA.isHermitian, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 := binWeight_le (hA.eigenvalues_nonneg i) hε s
  have h2 := sub_binWeight_le (hA.eigenvalues_nonneg i) hε s
  have h3 : 0 ≤ ε * hA.isHermitian.eigenvalues i := mul_nonneg hε.le (hA.eigenvalues_nonneg i)
  nlinarith [sq_nonneg (hA.isHermitian.eigenvalues i-binWeight (hA.isHermitian.eigenvalues i) ε s-ε*hA.isHermitian.eigenvalues i)]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

lemma hsSq_neg (M : Matrix m n ℂ) : hsSq (-M) = hsSq M := by
  simp [hsSq, Complex.normSq_neg]
lemma hsSq_sub_comm (M N : Matrix m n ℂ) : hsSq (M-N) = hsSq (N-M) := by
  rw [← hsSq_neg]; congr 1; abel
lemma hsSq_smul (r : ℝ) (M : Matrix m n ℂ) : hsSq (r • M) = r^2*hsSq M := by
  simp only [hsSq, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, ← Finset.mul_sum]
  congr 1
  ring
lemma hsSq_add_le (M N : Matrix m n ℂ) : hsSq (M+N) ≤ 2*(hsSq M+hsSq N) := by
  unfold hsSq
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  simp only [Matrix.add_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg ((M i j).re-(N i j).re), sq_nonneg ((M i j).im-(N i j).im)]

lemma hsSq_sum_orthogonal {ι : Type u_ι} [Fintype ι] [DecidableEq ι]
    (F : ι → Matrix m n ℂ) (hF : ∀ i j, i ≠ j → (F i)ᴴ*F j=0) :
    hsSq (∑ i, F i) = ∑ i, hsSq (F i) := by
  simp only [hsSq_eq_trace, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [hF j i hji, Matrix.trace_zero, Complex.zero_re]
  · simp

lemma hsSq_mul_right_contraction [DecidableEq n] {W : Matrix n p ℂ} (hW : W*Wᴴ ≤ 1)
    (M : Matrix m n ℂ) : hsSq (M*W) ≤ hsSq M := by
  rw [← hsSq_conjTranspose (M*W), Matrix.conjTranspose_mul, ← hsSq_conjTranspose M]
  exact hsSq_mul_contraction (W := Wᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hW) _

variable [DecidableEq m]
lemma hsSq_mul_projection_le {P : Matrix m m ℂ} (hP : P.IsHermitian) (hPP : P*P=P)
    (M : Matrix m n ℂ) : hsSq (P*M) ≤ hsSq M := by
  apply hsSq_mul_contraction
  rw [hP.eq, hPP]
  exact projection_le_one hP hPP

omit [DecidableEq m] in

lemma hsSq_orthogonal_projection_sum {ι : Type u_ι} [Fintype ι] [DecidableEq ι]
    (P : ι → Matrix m m ℂ) (F : ι → Matrix m n ℂ) (r : ι → ℝ)
    (hP : ∀ i, (P i).IsHermitian) (hPP : ∀ i j, i ≠ j → P i*P j=0) :
    hsSq (∑ i, r i • (P i*F i)) = ∑ i, (r i)^2*hsSq (P i*F i) := by
  rw [hsSq_sum_orthogonal]
  · simp only [hsSq_smul]
  · intro i j hij
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul,
      (hP i).eq, Matrix.smul_mul, Matrix.mul_smul]
    rw [show ((F i)ᴴ*P i)*(P j*F j)=(F i)ᴴ*(P i*P j)*F j by simp only [Matrix.mul_assoc],
      hPP i j hij, Matrix.mul_zero, Matrix.zero_mul, smul_zero, smul_zero]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def CoversBins (L : Finset ℤ) (A : Matrix n n ℂ) (ε s : ℝ) : Prop :=
  ∀ a ∈ spectrum ℝ A, 0 < a → ⌊Real.log a/ε+s⌋ ∈ L

lemma sum_binScale_indicator (L : Finset ℤ) (ε s a : ℝ)
    (h : 0 < a → ⌊Real.log a/ε+s⌋ ∈ L) :
    (∑ l ∈ L, binScale ε s l * binIndicator ε s l a) = binWeight a ε s := by
  by_cases ha : 0 < a
  · simp only [binIndicator, ha, true_and, binWeight, ite_true, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left (h ha)]
    rfl
  · simp [binIndicator, binWeight, ha]

lemma roundedAbs_eq_sum (L : Finset ℤ) {A : Matrix n n ℂ} (ε s : ℝ)
    (hL : CoversBins L A ε s) :
    roundedAbs A ε s = ∑ l : L, binScale ε s l • binProjection A ε s l := by
  unfold roundedAbs binProjection
  calc
    _ = cfc (∑ l : L, fun a => binScale ε s l * binIndicator ε s l a) A := by
      apply cfc_congr; intro a ha
      simp only [Finset.sum_apply]
      rw [Finset.sum_coe_sort L (fun l => binScale ε s l * binIndicator ε s l a)]
      exact (sum_binScale_indicator L ε s a (hL a ha)).symm
    _ = _ := by
      erw [cfc_sum_univ (fun l : L => fun a => binScale ε s l * binIndicator ε s l a) A
        (fun _ => A.finite_real_spectrum.continuousOn _)]
      apply Finset.sum_congr rfl; intro l _
      exact cfc_const_mul _ _ _ (A.finite_real_spectrum.continuousOn _)

lemma exists_common_bins {ι : Type u_ι} [Fintype ι] (A : ι → Matrix n n ℂ) (ε s : ℝ) :
    ∃ L : Finset ℤ, 0 ∈ L ∧ ∀ i, CoversBins L (A i) ε s := by
  classical
  let L := insert 0 (Finset.univ.biUnion (fun i =>
    (A i).finite_real_spectrum.toFinset.image (fun a => ⌊Real.log a/ε+s⌋)))
  refine ⟨L, Finset.mem_insert_self _ _, ?_⟩
  intro i a ha _
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  exact ⟨a, ((A i).finite_real_spectrum.mem_toFinset).mpr ha, rfl⟩

def crossBins (L : Finset ℤ) (A B : Matrix n n ℂ) (ε s : ℝ) : Matrix n n ℂ :=
  ∑ l : L, binScale ε s l • (binProjection A ε s l * binProjection B ε s l)

def binMismatch (L : Finset ℤ) (A B : Matrix n n ℂ) (ε s : ℝ) : ℝ :=
  ∑ l : L, (binScale ε s l)^2 * hsSq (binProjection A ε s l-binProjection B ε s l)

lemma crossBins_error_le (L : Finset ℤ) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (_hB : B.IsHermitian) (ε s : ℝ) (hL : CoversBins L A ε s) :
    hsSq (roundedAbs A ε s-crossBins L A B ε s) ≤ binMismatch L A B ε s := by
  have he : roundedAbs A ε s-crossBins L A B ε s =
      ∑ l : L, binScale ε s l • (binProjection A ε s l * (binProjection A ε s l-binProjection B ε s l)) := by
    rw [roundedAbs_eq_sum L ε s hL, crossBins, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.mul_sub, binProjection_sq hA, smul_sub]
  rw [he, hsSq_orthogonal_projection_sum _ _ _ (fun _ => binProjection_hermitian _ _ _ _)
    (fun i j hij => binProjection_orthogonal hA ε s (Subtype.coe_ne_coe.mpr hij))]
  unfold binMismatch
  apply Finset.sum_le_sum; intro l _
  exact mul_le_mul_of_nonneg_left
    (hsSq_mul_projection_le (binProjection_hermitian _ _ _ _) (binProjection_sq hA ε s l) _) (sq_nonneg _)

lemma polar_crossBins_error_le (L : Finset ℤ) (M N : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) (hL : CoversBins L (rightAbs M) ε s) :
    hsSq (M-polar M*crossBins L (rightAbs M) (rightAbs N) ε s) ≤
      2*ε^2*hsSq M + 2*binMismatch L (rightAbs M) (rightAbs N) ε s := by
  have hm : M-polar M*crossBins L (rightAbs M) (rightAbs N) ε s =
      polar M*(rightAbs M-roundedAbs (rightAbs M) ε s) +
      polar M*(roundedAbs (rightAbs M) ε s-crossBins L (rightAbs M) (rightAbs N) ε s) := by
    simp only [Matrix.mul_sub, polar_mul_rightAbs]
    abel
  rw [hm]
  have h1 := hsSq_mul_contraction (polar_contraction M) (rightAbs M-roundedAbs (rightAbs M) ε s)
  have h2 := hsSq_mul_contraction (polar_contraction M)
    (roundedAbs (rightAbs M) ε s-crossBins L (rightAbs M) (rightAbs N) ε s)
  have h3 := roundedAbs_error_le (rightAbs_pos M) hε s
  have h4 := crossBins_error_le L (rightAbs_pos M).isHermitian (rightAbs_pos N).isHermitian ε s hL
  have h5 : hsSq (rightAbs M) = hsSq M := hsSq_sqrt_gram M
  rw [h5] at h3
  have h6 := hsSq_add_le (polar M*(rightAbs M-roundedAbs (rightAbs M) ε s))
    (polar M*(roundedAbs (rightAbs M) ε s-crossBins L (rightAbs M) (rightAbs N) ε s))
  linarith

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

def vec (C : Matrix m n ℂ) : m × n → ℂ := fun i => C i.1 i.2

def eval (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) : ℂ :=
  star (vec C) ⬝ᵥ ((A ⊗ₖ B) *ᵥ vec C)

def prob (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) : ℝ :=
  (eval C A B).re

lemma eval_eq_sum (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    eval C A B = ∑ i, ∑ j, ∑ k, ∑ l, star (C i j) * (A i k * B j l) * C k l := by
  simp only [eval, vec, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]

lemma prob_nonneg {C : Matrix m n ℂ} {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ prob C A B :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg _)).1

lemma eval_add_left (C : Matrix m n ℂ) (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    eval C (A+A') B = eval C A B + eval C A' B := by
  simp [eval, Matrix.add_kronecker, Matrix.add_mulVec, dotProduct_add]
lemma eval_add_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    eval C A (B+B') = eval C A B + eval C A B' := by
  simp [eval, Matrix.kronecker_add, Matrix.add_mulVec, dotProduct_add]
lemma prob_add_left (C : Matrix m n ℂ) (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (A+A') B = prob C A B + prob C A' B := by
  simp [prob, eval_add_left]
lemma prob_add_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    prob C A (B+B') = prob C A B + prob C A B' := by
  simp [prob, eval_add_right]

lemma eval_one [DecidableEq m] [DecidableEq n] (C : Matrix m n ℂ) :
    eval C 1 1 = (hsSq C : ℂ) := by
  simp only [eval, Matrix.one_kronecker_one, Matrix.one_mulVec, dotProduct,
    Pi.star_apply, Fintype.sum_prod_type, vec, hsSq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  exact Complex.normSq_eq_conj_mul_self.symm

lemma prob_one [DecidableEq m] [DecidableEq n] (C : Matrix m n ℂ) :
    prob C 1 1 = hsSq C := by simp [prob, eval_one]

lemma eval_real {C : Matrix m n ℂ} {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : eval C A B = (prob C A B : ℂ) := by
  have h := ((hA.kronecker hB).dotProduct_mulVec_nonneg (vec C))
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp h).2.symm

lemma eval_eq_trace (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    eval C A B = Matrix.trace (Cᴴ * (A * (C * Bᵀ))) := by
  simp only [eval_eq_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  simp only [star, mul_assoc, mul_comm (B j l)]

lemma eval_kronecker (C : Matrix m n ℂ) (D : Matrix p q ℂ)
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (E : Matrix p p ℂ) (F : Matrix q q ℂ) :
    eval (C ⊗ₖ D) (A ⊗ₖ E) (B ⊗ₖ F) = eval C A B * eval D E F := by
  simp only [eval_eq_trace, Matrix.conjTranspose_kronecker, ← Matrix.kroneckerMap_transpose,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

lemma prob_kronecker (C : Matrix m n ℂ) (D : Matrix p q ℂ)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} {E : Matrix p p ℂ} {F : Matrix q q ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hE : E.PosSemidef) (hF : F.PosSemidef) :
    prob (C ⊗ₖ D) (A ⊗ₖ E) (B ⊗ₖ F) = prob C A B * prob D E F := by
  change (eval _ _ _).re = _
  rw [eval_kronecker, eval_real hA hB, eval_real hE hF,
    ← Complex.ofReal_mul, Complex.ofReal_re]

lemma hsSq_kronecker (C : Matrix m n ℂ) (D : Matrix p q ℂ) :
    hsSq (C ⊗ₖ D) = hsSq C * hsSq D := by
  classical
  simpa only [prob_one, Matrix.one_kronecker_one] using
    (prob_kronecker C D (A := 1) (B := 1) (E := 1) (F := 1)
      Matrix.PosSemidef.one Matrix.PosSemidef.one Matrix.PosSemidef.one Matrix.PosSemidef.one)

lemma eval_pullback (C : Matrix m n ℂ) (K : Matrix p m ℂ) (L : Matrix q n ℂ)
    (A : Matrix p p ℂ) (B : Matrix q q ℂ) :
    eval C (Kᴴ*A*K) (Lᴴ*B*L) = eval (K*C*Lᵀ) A B := by
  simp only [eval_eq_trace, Matrix.conjTranspose_mul, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose,
    Matrix.mul_assoc]
  conv_rhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma prob_pullback (C : Matrix m n ℂ) (K : Matrix p m ℂ) (L : Matrix q n ℂ)
    (A : Matrix p p ℂ) (B : Matrix q q ℂ) :
    prob C (Kᴴ*A*K) (Lᴴ*B*L) = prob (K*C*Lᵀ) A B := by
  simp only [prob, eval_pullback]

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end
end

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker

noncomputable section
namespace ThresholdParallelRepetition.QuantumSampling

structure POVM (n : Type u_n) (A : Type u_A) [Fintype n] [DecidableEq n] [Fintype A] where
  effect : A → Matrix n n ℂ
  pos : ∀ a, (effect a).PosSemidef
  total : ∑ a, effect a = 1

variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A]

def POVM.default (a₀ : A) : POVM n A := by
  classical
  exact { effect := fun a => if a = a₀ then 1 else 0
          pos := fun a => by split <;> first | exact Matrix.PosSemidef.one | exact Matrix.PosSemidef.zero
          total := by simp }

def POVM.pull (P : POVM m A) (K : Matrix m n ℂ) (a : A) : Matrix n n ℂ :=
  Kᴴ * P.effect a * K

omit [DecidableEq n] in
lemma POVM.pull_pos (P : POVM m A) (K : Matrix m n ℂ) (a : A) :
    (P.pull K a).PosSemidef := (P.pos a).conjTranspose_mul_mul_same K
omit [Fintype n] [DecidableEq n] in
lemma POVM.pull_sum (P : POVM m A) (K : Matrix m n ℂ) :
    ∑ a, P.pull K a = Kᴴ * K := by
  simp only [POVM.pull, ← Matrix.sum_mul, ← Matrix.mul_sum, P.total, Matrix.mul_one]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma kronecker_sum_left {ι : Type u_ι} [Fintype ι] (M : ι → Matrix m m ℂ)
    (N : Matrix n n ℂ) : (∑ i, M i) ⊗ₖ N = ∑ i, M i ⊗ₖ N := by
  ext i j; simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]
omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma kronecker_sum_right {ι : Type u_ι} [Fintype ι] (M : Matrix m m ℂ)
    (N : ι → Matrix n n ℂ) : M ⊗ₖ (∑ i, N i) = ∑ i, M ⊗ₖ N i := by
  ext i j; simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

@[reducible] def Copies (n : Type) : ℕ → Type
  | 0 => Unit
  | t+1 => n × Copies n t
instance copiesFintype {n : Type} [Fintype n] : (t : ℕ) → Fintype (Copies n t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t+1 => by
    letI := copiesFintype (n := n) t
    exact inferInstanceAs (Fintype (n × Copies n t))
instance copiesDecidableEq {n : Type} [DecidableEq n] : (t : ℕ) → DecidableEq (Copies n t)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | t+1 => @instDecidableEqProd n (Copies n t) _ (copiesDecidableEq t)
instance copiesNonempty {n : Type} [Nonempty n] : (t : ℕ) → Nonempty (Copies n t)
  | 0 => inferInstanceAs (Nonempty Unit)
  | t+1 => by
    let := copiesNonempty (n := n) t
    exact inferInstanceAs (Nonempty (n × Copies n t))

def tensorPower {m n : Type} (D : Matrix m n ℂ) : (t : ℕ) → Matrix (Copies m t) (Copies n t) ℂ
  | 0 => fun _ _ => 1
  | t+1 => D ⊗ₖ tensorPower D t

lemma hsSq_tensorPower {m n : Type} [Fintype m] [Fintype n] (D : Matrix m n ℂ) (t : ℕ) :
    hsSq (tensorPower D t) = hsSq D ^ t := by
  induction t with
  | zero => simp [tensorPower, hsSq]
  | succ t ih => rw [tensorPower, hsSq_kronecker, ih, pow_succ']

def firstSuccess {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Type} [Fintype A] (P : POVM m A) (K : Matrix m n ℂ)
    (hK : Kᴴ*K ≤ 1) (a₀ : A) : (t : ℕ) → POVM (Copies n t) A
  | 0 => POVM.default a₀
  | t+1 => {
      effect := fun a => P.pull K a ⊗ₖ 1 + (1-Kᴴ*K) ⊗ₖ (firstSuccess P K hK a₀ t).effect a
      pos := fun a => ((P.pull_pos K a).kronecker Matrix.PosSemidef.one).add
        ((Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hK)).kronecker
          ((firstSuccess P K hK a₀ t).pos a))
      total := by
        rw [Finset.sum_add_distrib, ← kronecker_sum_left, ← kronecker_sum_right,
          P.pull_sum, (firstSuccess P K hK a₀ t).total, ← Matrix.add_kronecker]
        simp only [add_sub_cancel, Matrix.one_kronecker_one] }

lemma eval_submatrix {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (C : Matrix m n ℂ) (U : Matrix m m ℂ) (V : Matrix n n ℂ) (e : p ≃ m) (f : q ≃ n) :
    eval (C.submatrix e f) (U.submatrix e e) (V.submatrix f f) = eval C U V := by
  simp only [eval_eq_sum, Matrix.submatrix_apply]
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv f
  intro j
  apply Fintype.sum_equiv e
  intro k
  exact Fintype.sum_equiv f _ _ (fun _ => rfl)

lemma exists_strategy_of_finite {m n X Y A B : Type}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n]
    [Fintype A] [Fintype B] (C : Matrix m n ℂ) (hC : hsSq C = 1)
    (P : X → POVM m A) (Q : Y → POVM n B) :
    ∃ S : Strategy X Y A B, ∀ x y a b, S.born x y a b = prob C ((P x).effect a) ((Q y).effect b) := by
  let e : Fin (Fintype.card m - 1 + 1) ≃ m :=
    (Fintype.equivFinOfCardEq (Nat.sub_add_cancel Fintype.card_pos).symm).symm
  let f : Fin (Fintype.card n - 1 + 1) ≃ n :=
    (Fintype.equivFinOfCardEq (Nat.sub_add_cancel Fintype.card_pos).symm).symm
  let S : Strategy X Y A B := {
    dimA := Fintype.card m - 1
    dimB := Fintype.card n - 1
    state := vec (C.submatrix e f)
    state_unit := by
      simp only [vec, Matrix.submatrix_apply, Fintype.sum_prod_type]
      rw [show (∑ i, ∑ j, Complex.normSq (C (e i) (f j))) = hsSq C by
        unfold hsSq
        apply Fintype.sum_equiv e
        intro i
        exact Fintype.sum_equiv f _ _ (fun _ => rfl)]
      exact hC
    alice := fun x a => ((P x).effect a).submatrix e e
    bob := fun y b => ((Q y).effect b).submatrix f f
    alice_pos := fun x a => ((P x).pos a).submatrix e
    bob_pos := fun y b => ((Q y).pos b).submatrix f
    alice_total := fun x => by
      calc
        _ = (∑ a, (P x).effect a).submatrix e e := by ext i j; simp [Matrix.sum_apply]
        _ = 1 := by rw [(P x).total, Matrix.submatrix_one_equiv]
    bob_total := fun y => by
      calc
        _ = (∑ b, (Q y).effect b).submatrix f f := by ext i j; simp [Matrix.sum_apply]
        _ = 1 := by rw [(Q y).total, Matrix.submatrix_one_equiv] }
  refine ⟨S, ?_⟩
  intro x y a b
  rw [Strategy.born_eq_quadratic]
  change prob (C.submatrix e f) (((P x).effect a).submatrix e e)
    (((Q y).effect b).submatrix f f) = _
  exact congrArg Complex.re (eval_submatrix C _ _ e f)

lemma prob_first_step_ge {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (C : Matrix m n ℂ) (D : Matrix p q ℂ) (hD : hsSq D = 1)
    {G F : Matrix m m ℂ} {H J : Matrix n n ℂ} {E : Matrix p p ℂ} {T : Matrix q q ℂ}
    (hG : G.PosSemidef) (hF : F.PosSemidef) (hH : H.PosSemidef) (hJ : J.PosSemidef)
    (hE : E.PosSemidef) (hT : T.PosSemidef) :
    prob C G H + prob C F J * prob D E T ≤
      prob (C ⊗ₖ D) (G ⊗ₖ 1 + F ⊗ₖ E) (H ⊗ₖ 1 + J ⊗ₖ T) := by
  rw [prob_add_left, prob_add_right, prob_add_right,
    prob_kronecker C D hG hH Matrix.PosSemidef.one Matrix.PosSemidef.one,
    prob_one, hD, mul_one, prob_kronecker C D hF hJ hE hT]
  have h1 := prob_nonneg (C := C ⊗ₖ D) (hG.kronecker Matrix.PosSemidef.one) (hJ.kronecker hT)
  have h2 := prob_nonneg (C := C ⊗ₖ D) (hF.kronecker hE) (hH.kronecker Matrix.PosSemidef.one)
  linarith

lemma firstSuccess_prob_succ {m n p q A B : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Fintype A] [Fintype B]
    (D : Matrix n q ℂ) (hD : hsSq D = 1) (P : POVM m A) (Q : POVM p B)
    (K : Matrix m n ℂ) (L : Matrix p q ℂ) (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1)
    (a₀ : A) (b₀ : B) (t : ℕ) (a : A) (b : B) :
    prob (K*D*Lᵀ) (P.effect a) (Q.effect b) +
      prob D (1-Kᴴ*K) (1-Lᴴ*L) *
        prob (tensorPower D t) ((firstSuccess P K hK a₀ t).effect a)
          ((firstSuccess Q L hL b₀ t).effect b) ≤
      prob (tensorPower D (t+1)) ((firstSuccess P K hK a₀ (t+1)).effect a)
        ((firstSuccess Q L hL b₀ (t+1)).effect b) := by
  change _ ≤ prob (D ⊗ₖ tensorPower D t)
    (P.pull K a ⊗ₖ 1 + (1-Kᴴ*K) ⊗ₖ (firstSuccess P K hK a₀ t).effect a)
    (Q.pull L b ⊗ₖ 1 + (1-Lᴴ*L) ⊗ₖ (firstSuccess Q L hL b₀ t).effect b)
  have hnorm : hsSq (tensorPower D t) = 1 := by rw [hsSq_tensorPower, hD, one_pow]
  have h := prob_first_step_ge D (tensorPower D t) hnorm (P.pull_pos K a)
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hK)) (Q.pull_pos L b)
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hL))
    ((firstSuccess P K hK a₀ t).pos a) ((firstSuccess Q L hL b₀ t).pos b)
  simpa only [POVM.pull, prob_pullback] using h

lemma prob_sum_left {m : Type u_m} {n : Type u_n} {ι : Type u_ι} [Fintype m] [Fintype n] [Fintype ι]
    (C : Matrix m n ℂ) (A : ι → Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (∑ i, A i) B = ∑ i, prob C (A i) B := by
  simp only [prob, eval_eq_trace, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
lemma prob_sum_right {m : Type u_m} {n : Type u_n} {ι : Type u_ι} [Fintype m] [Fintype n] [Fintype ι]
    (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : ι → Matrix n n ℂ) :
    prob C A (∑ i, B i) = ∑ i, prob C A (B i) := by
  simp only [prob, eval_eq_trace, Matrix.transpose_sum, Matrix.mul_sum,
    Matrix.trace_sum, Complex.re_sum]

section Payoff
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B]

def payoff (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) : ℝ :=
  ∑ a, ∑ b, if V a b then prob C (P.effect a) (Q.effect b) else 0
lemma prob_total (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) :
    ∑ a, ∑ b, prob C (P.effect a) (Q.effect b) = hsSq C := by
  simp_rw [← prob_sum_right, ← prob_sum_left, P.total, Q.total, prob_one]
lemma payoff_nonneg (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    0 ≤ payoff C P Q V := by
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro b _
  split
  · exact prob_nonneg (P.pos a) (Q.pos b)
  · exact le_rfl
lemma payoff_le_hsSq (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    payoff C P Q V ≤ hsSq C := by
  rw [← prob_total C P Q]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  split
  · exact le_rfl
  · exact prob_nonneg (P.pos a) (Q.pos b)
end Payoff

lemma firstSuccess_prob_geometric {m n p q A B : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Fintype A] [Fintype B]
    (D : Matrix n q ℂ) (hD : hsSq D = 1) (P : POVM m A) (Q : POVM p B)
    (K : Matrix m n ℂ) (L : Matrix p q ℂ) (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1)
    (a₀ : A) (b₀ : B) (t : ℕ) (a : A) (b : B) :
    prob (K*D*Lᵀ) (P.effect a) (Q.effect b) *
      (∑ j ∈ Finset.range t, (prob D (1-Kᴴ*K) (1-Lᴴ*L))^j) ≤
      prob (tensorPower D t) ((firstSuccess P K hK a₀ t).effect a)
        ((firstSuccess Q L hL b₀ t).effect b) := by
  let z := prob D (1-Kᴴ*K) (1-Lᴴ*L)
  have hz : 0 ≤ z := prob_nonneg
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hK))
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hL))
  induction t with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero] using
      (prob_nonneg ((firstSuccess P K hK a₀ 0).pos a) ((firstSuccess Q L hL b₀ 0).pos b)
        (C := tensorPower D 0))
  | succ t ih =>
    calc
      _ = prob (K*D*Lᵀ) (P.effect a) (Q.effect b) + z *
          (prob (K*D*Lᵀ) (P.effect a) (Q.effect b) * ∑ j ∈ Finset.range t, z^j) := by
        change _ * (∑ j ∈ Finset.range (t+1), z^j) = _
        rw [Finset.sum_range_succ']
        simp only [pow_succ', ← Finset.mul_sum, pow_zero]
        ring
      _ ≤ prob (K*D*Lᵀ) (P.effect a) (Q.effect b) + z *
          prob (tensorPower D t) ((firstSuccess P K hK a₀ t).effect a)
            ((firstSuccess Q L hL b₀ t).effect b) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hz)
      _ ≤ _ := firstSuccess_prob_succ D hD P Q K L hK hL a₀ b₀ t a b

lemma firstSuccess_payoff_geometric {m n p q A B : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Fintype A] [Fintype B]
    (D : Matrix n q ℂ) (hD : hsSq D = 1) (P : POVM m A) (Q : POVM p B)
    (K : Matrix m n ℂ) (L : Matrix p q ℂ) (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1)
    (a₀ : A) (b₀ : B) (t : ℕ) (V : A → B → Bool) :
    payoff (K*D*Lᵀ) P Q V *
      (∑ j ∈ Finset.range t, (prob D (1-Kᴴ*K) (1-Lᴴ*L))^j) ≤
      payoff (tensorPower D t) (firstSuccess P K hK a₀ t) (firstSuccess Q L hL b₀ t) V := by
  simp only [payoff, Finset.sum_mul]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  split
  · exact firstSuccess_prob_geometric D hD P Q K L hK hL a₀ b₀ t a b
  · simp

lemma finite_filter_geometric_value {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : hsSq D = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1) (t : ℕ) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) *
        ∑ j ∈ Finset.range t, (prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2))^j)) ≤
      entangledValue G := by
  have hnorm : hsSq (tensorPower D t) = 1 := by rw [hsSq_tensorPower, hD, one_pow]
  obtain ⟨S, hS⟩ := exists_strategy_of_finite (tensorPower D t) hnorm
    (fun x => firstSuccess (P x) (K x) (hK x) 0 t)
    (fun y => firstSuccess (Q y) (L y) (hL y) 0 t)
  apply le_trans ?_ (successProbability_le_value G S)
  unfold successProbability
  apply Finset.sum_le_sum; intro z _
  apply mul_le_mul_of_nonneg_left _ (G.questionProb_nonneg z)
  rw [Fintype.sum_prod_type]
  simp_rw [hS]
  exact firstSuccess_payoff_geometric D hD (P z.1) (Q z.2) (K z.1) (L z.2)
    (hK z.1) (hL z.2) 0 0 t (G.accepts z.1 z.2)

section FilterMass
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

omit [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] in
lemma prob_sub_left (C : Matrix m n ℂ) (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (A-A') B = prob C A B - prob C A' B := by
  simp only [prob, eval_eq_trace, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
omit [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] in
lemma prob_sub_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    prob C A (B-B') = prob C A B - prob C A B' := by
  simp only [prob, eval_eq_trace, Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

omit [DecidableEq n] [DecidableEq q] in
lemma prob_gram (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ) :
    prob D (Kᴴ*K) (Lᴴ*L) = hsSq (K*D*Lᵀ) := by
  simpa only [Matrix.mul_one, prob_one] using prob_pullback D K L (1 : Matrix m m ℂ) (1 : Matrix p p ℂ)
omit [Fintype p] [DecidableEq p] [DecidableEq n] in
lemma prob_left_gram (D : Matrix n q ℂ) (K : Matrix m n ℂ) :
    prob D (Kᴴ*K) 1 = hsSq (K*D) := by
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] using
    prob_gram D K (1 : Matrix q q ℂ)
omit [Fintype m] [DecidableEq m] [DecidableEq q] in
lemma prob_right_gram (D : Matrix n q ℂ) (L : Matrix p q ℂ) :
    prob D 1 (Lᴴ*L) = hsSq (D*Lᵀ) := by
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul] using
    prob_gram D (1 : Matrix n n ℂ) L

lemma prob_fail (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ) :
    prob D (1-Kᴴ*K) (1-Lᴴ*L) =
      hsSq D - hsSq (K*D) - hsSq (D*Lᵀ) + hsSq (K*D*Lᵀ) := by
  rw [prob_sub_left, prob_sub_right, prob_sub_right, prob_one, prob_right_gram,
    prob_left_gram, prob_gram]
  ring

lemma filter_mass_bounds (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ)
    (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1) :
    hsSq (K*D*Lᵀ) ≤ hsSq (K*D) ∧ hsSq (K*D*Lᵀ) ≤ hsSq (D*Lᵀ) ∧
      hsSq (K*D) ≤ hsSq D ∧ hsSq (D*Lᵀ) ≤ hsSq D := by
  have hF := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hK)
  have hJ := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hL)
  have hG := Matrix.posSemidef_conjTranspose_mul_self K
  have hH := Matrix.posSemidef_conjTranspose_mul_self L
  have h1 := prob_nonneg (C := D) hG hJ
  have h2 := prob_nonneg (C := D) hF hH
  have h3 := prob_nonneg (C := D) hF Matrix.PosSemidef.one
  have h4 := prob_nonneg (C := D) Matrix.PosSemidef.one hJ
  rw [prob_sub_right, prob_left_gram, prob_gram] at h1
  rw [prob_sub_left, prob_right_gram, prob_gram] at h2
  rw [prob_sub_left, prob_one, prob_left_gram] at h3
  rw [prob_sub_right, prob_one, prob_right_gram] at h4
  exact ⟨sub_nonneg.mp h1, sub_nonneg.mp h2, sub_nonneg.mp h3, sub_nonneg.mp h4⟩

lemma prob_fail_le (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ)
    (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1) :
    prob D (1-Kᴴ*K) (1-Lᴴ*L) ≤ hsSq D := by
  rw [prob_fail]
  have h := (filter_mass_bounds D K L hK hL).1
  have hb := hsSq_nonneg (D*Lᵀ)
  linarith

lemma output_zero_of_fail_full (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ)
    (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1)
    (h : prob D (1-Kᴴ*K) (1-Lᴴ*L) = hsSq D) : hsSq (K*D*Lᵀ) = 0 := by
  rw [prob_fail] at h
  obtain ⟨h1,h2,_,_⟩ := filter_mass_bounds D K L hK hL
  have h0 := hsSq_nonneg (K*D*Lᵀ)
  linarith
end FilterMass

open Filter Topology
lemma geometric_contribution_tendsto {w z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hw : z = 1 → w = 0) :
    Tendsto (fun t : ℕ => w * ∑ j ∈ Finset.range t, z^j) atTop (𝓝 (w/(1-z))) := by
  by_cases hz : z = 1
  · simp only [hw hz, zero_mul, zero_div]
    exact tendsto_const_nhds
  · simpa only [div_eq_mul_inv] using
      ((hasSum_geometric_of_lt_one hz0 (lt_of_le_of_ne hz1 hz)).tendsto_sum_nat.const_mul w)

theorem finite_filter_value {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : hsSq D = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) /
        (1-prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2)))) ≤ entangledValue G := by
  apply le_of_tendsto' (x := atTop) (f := fun t : ℕ => ∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
    (payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) *
       ∑ j ∈ Finset.range t, (prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2))^j))
  · apply tendsto_finsetSum
    intro z _
    apply Filter.Tendsto.const_mul
    apply geometric_contribution_tendsto
    · exact prob_nonneg (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (hK z.1)))
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (hL z.2)))
    · rw [← hD]; exact prob_fail_le D (K z.1) (L z.2) (hK z.1) (hL z.2)
    · intro hz
      have hn := output_zero_of_fail_full D (K z.1) (L z.2) (hK z.1) (hL z.2) (hz.trans hD.symm)
      exact le_antisymm ((payoff_le_hsSq _ _ _ _).trans_eq hn) (payoff_nonneg _ _ _ _)
  · exact fun t => finite_filter_geometric_value G D hD P Q K L hK hL t

lemma prob_smul {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
    (r : ℝ) (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob (r • C) A B = r^2 * prob C A B := by
  simp only [prob, eval_eq_trace, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

lemma payoff_smul {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B] (r : ℝ) (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) : payoff (r • C) P Q V = r^2 * payoff C P Q V := by
  simp only [payoff, prob_smul, Finset.mul_sum, mul_ite, mul_zero]

theorem finite_filter_value_unnormalized {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : 0 < hsSq D)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) /
        (hsSq (K z.1*D) + hsSq (D*(L z.2)ᵀ) - hsSq (K z.1*D*(L z.2)ᵀ)))) ≤
      entangledValue G := by
  let r : ℝ := (Real.sqrt (hsSq D))⁻¹
  have hr : r^2 = (hsSq D)⁻¹ := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hD.le]
  have hnorm : hsSq (r • D) = 1 := by
    rw [hsSq_smul, hr, inv_mul_cancel₀ hD.ne']
  have hv := finite_filter_value G (r • D) hnorm P Q K L hK hL
  convert hv using 1
  apply Finset.sum_congr rfl; intro z _
  refine congrArg (G.questionProb z * ·) ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, payoff_smul, prob_smul, hr]
  have hden : (1 - (hsSq D)⁻¹ * prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2)) =
      (hsSq D - prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2)) / hsSq D := by
    field_simp
  rw [hden, inv_mul_eq_div, div_div_div_cancel_right₀ hD.ne', prob_fail]
  congr 1
  ring

end ThresholdParallelRepetition.QuantumSampling

end

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
section Norm
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
lemma norm_eq_sqrt_hsSq (M : Matrix m n ℂ) : ‖M‖ = Real.sqrt (hsSq M) := by
  simp only [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, hsSq,
    Real.rpow_two, Complex.sq_norm]
lemma hsSq_le_one_norm {M : Matrix m n ℂ} (hM : hsSq M ≤ 1) : ‖M‖ ≤ 1 := by
  rw [norm_eq_sqrt_hsSq]
  exact Real.sqrt_le_one.mpr hM
lemma hsSq_difference_le (M N : Matrix m n ℂ) (hM : hsSq M ≤ 1) (hN : hsSq N ≤ 1) :
    hsSq M - hsSq N ≤ 2 * Real.sqrt (hsSq (M-N)) := by
  have hm := hsSq_le_one_norm hM
  have hn := hsSq_le_one_norm hN
  have hd := norm_sub_norm_le M N
  have h0 := norm_nonneg M
  have h1 := norm_nonneg N
  have h2 := norm_nonneg (M-N)
  have hh := mul_le_mul_of_nonneg_left hd (add_nonneg h0 h1)
  have hh' := mul_le_mul_of_nonneg_right (add_le_add hm hn) h2
  rw [norm_eq_sqrt_hsSq M, norm_eq_sqrt_hsSq N, norm_eq_sqrt_hsSq (M-N)] at hh hh'
  have hsqM := Real.sq_sqrt (hsSq_nonneg M)
  have hsqN := Real.sq_sqrt (hsSq_nonneg N)
  nlinarith
end Norm

section WinEffect
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B]
def winEffect (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    Matrix (m × n) (m × n) ℂ := ∑ a, ∑ b, if V a b then P.effect a ⊗ₖ Q.effect b else 0
lemma winEffect_pos (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    (winEffect P Q V).PosSemidef := by
  apply Matrix.posSemidef_sum; intro a _
  apply Matrix.posSemidef_sum; intro b _
  split
  · exact (P.pos a).kronecker (Q.pos b)
  · exact Matrix.PosSemidef.zero
lemma winEffect_le_one (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    winEffect P Q V ≤ 1 := by
  have hsum : (∑ a, ∑ b, P.effect a ⊗ₖ Q.effect b) = (1 : Matrix (m × n) (m × n) ℂ) := by
    simp only [← kronecker_sum_right, ← kronecker_sum_left, P.total, Q.total,
      Matrix.one_kronecker_one]
  rw [← hsum]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  split
  · exact le_rfl
  · exact ((P.pos a).kronecker (Q.pos b)).nonneg

def flat (C : Matrix m n ℂ) : Matrix (m × n) Unit ℂ := Matrix.replicateCol Unit (vec C)
omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_flat (C : Matrix m n ℂ) : hsSq (flat C) = hsSq C := by
  simp [hsSq, flat, vec, Fintype.sum_prod_type]
omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma flat_sub (C D : Matrix m n ℂ) : flat (C-D) = flat C-flat D := rfl
omit [DecidableEq m] [DecidableEq n] in
lemma flat_form (C : Matrix m n ℂ) (W : Matrix (m × n) (m × n) ℂ) :
    Matrix.trace ((flat C)ᴴ*(W*flat C)) = star (vec C) ⬝ᵥ (W *ᵥ vec C) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_unique, Matrix.mul_apply,
    Matrix.conjTranspose_apply, flat, Matrix.replicateCol_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply]
lemma payoff_eq_form (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) :
    payoff C P Q V = (star (vec C) ⬝ᵥ (winEffect P Q V *ᵥ vec C)).re := by
  simp only [winEffect, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, payoff]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  split
  · rfl
  · simp only [Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
lemma payoff_eq_hsSq (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) :
    payoff C P Q V = hsSq (CFC.sqrt (winEffect P Q V) * flat C) := by
  rw [hsSq_eq_trace, Matrix.conjTranspose_mul]
  have hh : (CFC.sqrt (winEffect P Q V)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  rw [hh.eq, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt _) (CFC.sqrt _),
    CFC.sqrt_mul_sqrt_self _ (winEffect_pos P Q V).nonneg, flat_form, payoff_eq_form]
lemma winSqrt_contraction (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    (CFC.sqrt (winEffect P Q V))ᴴ*CFC.sqrt (winEffect P Q V) ≤ 1 := by
  have hh : (CFC.sqrt (winEffect P Q V)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  rw [hh.eq, CFC.sqrt_mul_sqrt_self _ (winEffect_pos P Q V).nonneg]
  exact winEffect_le_one P Q V
lemma payoff_difference_le (C D : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) (hC : hsSq C ≤ 1) (hD : hsSq D ≤ 1) :
    payoff C P Q V - payoff D P Q V ≤ 2*Real.sqrt (hsSq (C-D)) := by
  have hsc := (hsSq_mul_contraction (winSqrt_contraction P Q V) (flat C)).trans
    (le_trans (le_of_eq (hsSq_flat C)) hC)
  have hsd := (hsSq_mul_contraction (winSqrt_contraction P Q V) (flat D)).trans
    (le_trans (le_of_eq (hsSq_flat D)) hD)
  rw [payoff_eq_hsSq, payoff_eq_hsSq]
  refine (hsSq_difference_le _ _ hsc hsd).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  rw [← Matrix.mul_sub, ← flat_sub]
  exact (hsSq_mul_contraction (winSqrt_contraction P Q V) _).trans_eq (hsSq_flat _)
end WinEffect

lemma payoff_ratio_loss {w q a b c e : ℝ} (_he : 0 ≤ e) (hq : 0 ≤ q) (hqc : q ≤ c)
    (hca : c ≤ a) (hcb : c ≤ b) (ha : a ≤ 1) (hb : b ≤ 1)
    (hwq : w-q ≤ 2*Real.sqrt e) (hc : 1-c ≤ 2*Real.sqrt e) :
    w ≤ q/(a+b-c) + 4*Real.sqrt e := by
  have hc0 : 0 ≤ c := hq.trans hqc
  have hd0 : 0 ≤ a+b-c := by linarith
  by_cases hd : a+b-c = 0
  · have hq0 : q = 0 := by linarith
    rw [hq0, zero_div]
    rw [hq0, sub_zero] at hwq
    linarith [Real.sqrt_nonneg e]
  · have hdpos : 0 < a+b-c := lt_of_le_of_ne hd0 (Ne.symm hd)
    have hr0 : 0 ≤ q/(a+b-c) := div_nonneg hq hd0
    have hr1 : q/(a+b-c) ≤ 1 := (div_le_one hdpos).mpr (by linarith)
    have hde : a+b-c ≤ 1+2*Real.sqrt e := by linarith
    have hm := mul_le_mul_of_nonneg_left hde hr0
    have hprod : q/(a+b-c)*(a+b-c) = q := div_mul_cancel₀ q hd
    rw [hprod] at hm
    have he' := Real.sqrt_nonneg e
    nlinarith

theorem filter_approximation_value {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : 0 < hsSq D)
    (M : Fin (x+1) → Matrix m p ℂ) (hM : ∀ x, hsSq (M x) = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1)
    (hA : ∀ x, hsSq (K x*D) ≤ 1) (hB : ∀ y, hsSq (D*(L y)ᵀ) ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        hsSq (M z.1 - K z.1*D*(L z.2)ᵀ)) := by
  have hv := finite_filter_value_unnormalized G D hD P Q K L hK hL
  have hp : ∀ z : Fin (x+1) × Fin (y+1),
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2) ≤
        payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) /
          (hsSq (K z.1*D)+hsSq (D*(L z.2)ᵀ)-hsSq (K z.1*D*(L z.2)ᵀ)) +
          4*Real.sqrt (hsSq (M z.1-K z.1*D*(L z.2)ᵀ)) := by
    intro z
    obtain ⟨hca,hcb,_,_⟩ := filter_mass_bounds D (K z.1) (L z.2) (hK z.1) (hL z.2)
    apply payoff_ratio_loss (hsSq_nonneg _) (payoff_nonneg _ _ _ _) (payoff_le_hsSq _ _ _ _)
      hca hcb (hA z.1) (hB z.2)
    · exact payoff_difference_le _ _ _ _ _ (le_of_eq (hM z.1)) (hca.trans (hA z.1))
    · simpa only [hM z.1] using
        hsSq_difference_le (M z.1) (K z.1*D*(L z.2)ᵀ) (le_of_eq (hM z.1)) (hca.trans (hA z.1))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun z _ =>
    mul_le_mul_of_nonneg_left (hp z) (G.questionProb_nonneg z))
  simp only [mul_add, Finset.sum_add_distrib] at hh
  have hroot := weighted_sqrt_le G.questionProb
    (fun z => hsSq (M z.1-K z.1*D*(L z.2)ᵀ)) G.questionProb_nonneg
    (fun _ => hsSq_nonneg _) G.questionProb_sum
  have hfour : (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (4*Real.sqrt (hsSq (M z.1-K z.1*D*(L z.2)ᵀ)))) =
      4*∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        Real.sqrt (hsSq (M z.1-K z.1*D*(L z.2)ᵀ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
  rw [hfour] at hh
  linarith

section Blocks
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {ι : Type u_ι} [Fintype m] [Fintype n] [Fintype p] [Fintype ι]
def rowBlocks (F : ι → Matrix m n ℂ) : Matrix m (n × ι) ℂ := fun i j => F j.2 i j.1
omit [Fintype m] [Fintype n] [Fintype p] in
lemma rowBlocks_mul_transpose (F : ι → Matrix m n ℂ) (G : ι → Matrix p n ℂ) [Fintype n] :
    rowBlocks F * (rowBlocks G)ᵀ = ∑ l, F l*(G l)ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, rowBlocks, Matrix.transpose_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]
  rw [Finset.sum_comm]
omit [Fintype m] [Fintype p] in
lemma rowBlocks_mul_diagonal [DecidableEq n] [DecidableEq ι]
    (F : ι → Matrix m n ℂ) (r : ι → ℝ) :
    rowBlocks F * Matrix.diagonal (fun j : n × ι => (r j.2 : ℂ)) =
      rowBlocks (fun l => r l • F l) := by
  ext i j
  simp only [Matrix.mul_diagonal, rowBlocks, Matrix.smul_apply, Complex.real_smul]
  ring
omit [Fintype p] in
lemma hsSq_rowBlocks (F : ι → Matrix m n ℂ) :
    hsSq (rowBlocks F) = ∑ l, hsSq (F l) := by
  simp only [hsSq, rowBlocks, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
omit [Fintype p] [Fintype ι] in
lemma hsSq_transpose (C : Matrix m n ℂ) : hsSq Cᵀ = hsSq C := by
  simp only [hsSq, Matrix.transpose_apply]
  exact Finset.sum_comm
omit [Fintype m] [Fintype p] [Fintype ι] in
lemma projectionRows_gram [DecidableEq ι] (P : ι → Matrix n n ℂ)
    (hP : ∀ l, (P l).IsHermitian) (hPP : ∀ l, P l*P l = P l)
    (horth : ∀ l t, l ≠ t → P l*P t = 0) :
    (rowBlocks P)ᴴ*rowBlocks P = Matrix.blockDiagonal P := by
  ext ⟨i,l⟩ ⟨j,t⟩
  change ((P l)ᴴ*P t) i j = _
  rw [(hP l).eq]
  by_cases hlt : l = t
  · subst t
    rw [hPP l, Matrix.blockDiagonal_apply_eq]
  · rw [horth l t hlt]
    simp only [Matrix.zero_apply, Matrix.blockDiagonal_apply, ite_eq_right hlt]
omit [Fintype m] [Fintype p] in
lemma projectionRows_contraction [DecidableEq n] [DecidableEq ι] (P : ι → Matrix n n ℂ)
    (hP : ∀ l, (P l).IsHermitian) (hPP : ∀ l, P l*P l = P l)
    (horth : ∀ l t, l ≠ t → P l*P t = 0) : (rowBlocks P)ᴴ*rowBlocks P ≤ 1 := by
  rw [projectionRows_gram P hP hPP horth]
  apply projection_le_one
  · change (Matrix.blockDiagonal P)ᴴ = _
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1; funext l; exact (hP l).eq
  · rw [← Matrix.blockDiagonal_mul]
    congr 1; funext l; exact hPP l
end Blocks

section Resource
variable {n : Type u_n} [Fintype n] [DecidableEq n]
def binResource (L : Finset ℤ) (ε s : ℝ) : Matrix (n × L) (n × L) ℂ :=
  Matrix.diagonal (fun j => (binScale ε s j.2 : ℂ))
def bobBinFilter (L : Finset ℤ) (N : Matrix n n ℂ) (ε s : ℝ) : Matrix n (n × L) ℂ :=
  rowBlocks (fun l : L => (binProjection (rightAbs N) ε s l)ᵀ)
lemma bobBinFilter_contraction (L : Finset ℤ) (N : Matrix n n ℂ) (ε s : ℝ) :
    (bobBinFilter L N ε s)ᴴ*bobBinFilter L N ε s ≤ 1 := by
  apply projectionRows_contraction
  · intro l; exact (binProjection_hermitian _ _ _ _).transpose
  · intro l
    rw [← Matrix.transpose_mul, binProjection_sq (rightAbs_pos N).isHermitian]
  · intro l t hlt
    rw [← Matrix.transpose_mul,
      binProjection_orthogonal (rightAbs_pos N).isHermitian ε s (Subtype.coe_ne_coe.mpr (Ne.symm hlt)),
      Matrix.transpose_zero]
omit [Fintype n] in
lemma binResource_transpose (L : Finset ℤ) (ε s : ℝ) :
    (binResource (n := n) L ε s)ᵀ = binResource (n := n) L ε s := Matrix.diagonal_transpose _
lemma binResource_pos [Nonempty n] (L : Finset ℤ) [Nonempty L] (ε s : ℝ) :
    0 < hsSq (binResource (n := n) L ε s) := by
  simp only [hsSq, binResource, Matrix.diagonal_apply, apply_ite Complex.normSq,
    Complex.normSq_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Complex.normSq_ofReal]
  apply Finset.sum_pos'
  · intro i _; exact mul_self_nonneg _
  · exact ⟨(Classical.choice ‹Nonempty n›, Classical.choice ‹Nonempty L›), Finset.mem_univ _,
      mul_pos (Real.exp_pos _) (Real.exp_pos _)⟩
lemma bin_output (L : Finset ℤ) (M N : Matrix n n ℂ) (ε s : ℝ) :
    binFilter L M ε s * binResource (n := n) L ε s * (bobBinFilter L N ε s)ᵀ =
      polar M*crossBins L (rightAbs M) (rightAbs N) ε s := by
  change rowBlocks (fun l : L => polar M*binProjection (rightAbs M) ε s l) *
    Matrix.diagonal (fun j : n × L => (binScale ε s j.2 : ℂ)) *
    (rowBlocks (fun l : L => (binProjection (rightAbs N) ε s l)ᵀ))ᵀ = _
  rw [rowBlocks_mul_diagonal _ (fun l : L => binScale ε s l), rowBlocks_mul_transpose]
  simp only [Matrix.transpose_transpose, Matrix.smul_mul, crossBins, Matrix.mul_sum,
    Matrix.mul_smul, Matrix.mul_assoc]
lemma hsSq_polar_bin (M : Matrix n n ℂ) (ε s : ℝ) (l : ℤ) :
    hsSq (polar M*binProjection (rightAbs M) ε s l) =
      hsSq (binProjection (rightAbs M) ε s l) := by
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (polar M)ᴴ (polar M), polar_gram_bin]
lemma hsSq_roundedAbs_eq_sum (L : Finset ℤ) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (ε s : ℝ) (hL : CoversBins L A ε s) :
    hsSq (roundedAbs A ε s) = ∑ l : L, (binScale ε s l)^2*hsSq (binProjection A ε s l) := by
  rw [roundedAbs_eq_sum L ε s hL, hsSq_sum_orthogonal]
  · simp only [hsSq_smul]
  · intro l t hlt
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      (binProjection_hermitian A ε s l).eq]
    rw [binProjection_orthogonal hA ε s (Subtype.coe_ne_coe.mpr hlt), smul_zero, smul_zero]
lemma bin_left_mass (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ)
    (hL : CoversBins L (rightAbs M) ε s) :
    hsSq (binFilter L M ε s*binResource (n := n) L ε s) = hsSq (roundedAbs (rightAbs M) ε s) := by
  change hsSq (rowBlocks (fun l : L => polar M*binProjection (rightAbs M) ε s l) *
    Matrix.diagonal (fun j : n × L => (binScale ε s j.2 : ℂ))) = _
  rw [rowBlocks_mul_diagonal _ (fun l : L => binScale ε s l), hsSq_rowBlocks, hsSq_roundedAbs_eq_sum L (rightAbs_pos M).isHermitian ε s hL]
  simp only [hsSq_smul, hsSq_polar_bin]
lemma bin_right_mass (L : Finset ℤ) (N : Matrix n n ℂ) (ε s : ℝ)
    (hL : CoversBins L (rightAbs N) ε s) :
    hsSq (binResource (n := n) L ε s*(bobBinFilter L N ε s)ᵀ) = hsSq (roundedAbs (rightAbs N) ε s) := by
  rw [← hsSq_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, binResource_transpose]
  change hsSq (rowBlocks (fun l : L => (binProjection (rightAbs N) ε s l)ᵀ) *
    Matrix.diagonal (fun j : n × L => (binScale ε s j.2 : ℂ))) = _
  rw [rowBlocks_mul_diagonal _ (fun l : L => binScale ε s l), hsSq_rowBlocks, hsSq_roundedAbs_eq_sum L (rightAbs_pos N).isHermitian ε s hL]
  simp only [hsSq_smul, hsSq_transpose]
end Resource

theorem correlated_sampling_value {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (M : Fin (x+1) → Matrix n n ℂ) (N : Fin (y+1) → Matrix n n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM n (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) := by
  have hMA : ∀ x, hsSq (rightAbs (M x)) = 1 := fun x => (hsSq_sqrt_gram (M x)).trans (hM x)
  have hNA : ∀ y, hsSq (rightAbs (N y)) = 1 := fun y => (hsSq_sqrt_gram (N y)).trans (hN y)
  obtain ⟨s,hs⟩ := exists_shift_spectralEnvelope_le G.questionProb G.questionProb_nonneg
    G.questionProb_sum (fun z => rightAbs (M z.1)) (fun z => rightAbs (N z.2))
    (fun z => rightAbs_pos (M z.1)) (fun z => rightAbs_pos (N z.2))
    (fun z => hMA z.1) (fun z => hNA z.2) hε hε1
  obtain ⟨L,hL0,hL⟩ := exists_common_bins
    (Sum.elim (fun x => rightAbs (M x)) (fun y => rightAbs (N y))) ε s
  let : Nonempty L := ⟨⟨0,hL0⟩⟩
  have hLM : ∀ x, CoversBins L (rightAbs (M x)) ε s := fun x => hL (Sum.inl x)
  have hLN : ∀ y, CoversBins L (rightAbs (N y)) ε s := fun y => hL (Sum.inr y)
  have hleft : ∀ x, hsSq (binFilter L (M x) ε s*binResource (n := n) L ε s) ≤ 1 := by
    intro x
    rw [bin_left_mass L (M x) ε s (hLM x)]
    exact (roundedAbs_energy_le (rightAbs_pos (M x)) hε s).trans_eq (hMA x)
  have hright : ∀ y, hsSq (binResource (n := n) L ε s*(bobBinFilter L (N y) ε s)ᵀ) ≤ 1 := by
    intro y
    rw [bin_right_mass L (N y) ε s (hLN y)]
    exact (roundedAbs_energy_le (rightAbs_pos (N y)) hε s).trans_eq (hNA y)
  have hv := filter_approximation_value G (binResource (n := n) L ε s) (binResource_pos L ε s)
    M hM P Q (fun x => binFilter L (M x) ε s) (fun y => bobBinFilter L (N y) ε s)
    (fun x => binFilter_contraction L (M x) ε s)
    (fun y => bobBinFilter_contraction L (N y) ε s) hleft hright
  apply hv.trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (show (0 : ℝ) ≤ 4 by norm_num)
  apply Real.sqrt_le_sqrt
  simp only [bin_output]
  have he : ∀ z : Fin (x+1) × Fin (y+1),
      hsSq (M z.1-polar (M z.1)*crossBins L (rightAbs (M z.1)) (rightAbs (N z.2)) ε s) ≤
      2*ε^2 + 2*spectralEnvelope (rightAbs_pos (M z.1)).isHermitian
        (rightAbs_pos (N z.2)).isHermitian ε s := by
    intro z
    have herr := polar_crossBins_error_le L (M z.1) (N z.2) hε s (hLM z.1)
    rw [hM z.1, mul_one] at herr
    have hmis := binProjection_mismatch_le L (rightAbs_pos (M z.1)) (rightAbs_pos (N z.2)) hε s
    rw [← Finset.sum_coe_sort L] at hmis
    change binMismatch L _ _ ε s ≤ _ at hmis
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun z _ => mul_le_mul_of_nonneg_left (he z) (G.questionProb_nonneg z))
  have heq : (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (2*ε^2+2*spectralEnvelope (rightAbs_pos (M z.1)).isHermitian
        (rightAbs_pos (N z.2)).isHermitian ε s)) =
      2*ε^2 + 2*∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        spectralEnvelope (rightAbs_pos (M z.1)).isHermitian
          (rightAbs_pos (N z.2)).isHermitian ε s := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, G.questionProb_sum, one_mul, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro z _; ring
  rw [heq] at hsum
  have habs : (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      hsSq (rightAbs (M z.1)-rightAbs (N z.2))) ≤
      2*∑ z : Fin (x+1) × Fin (y+1), G.questionProb z * hsSq (M z.1-N z.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro z _
    have hh := mul_le_mul_of_nonneg_left (hsSq_right_absolute_sub_le (M z.1) (N z.2))
      (G.questionProb_nonneg z)
    dsimp [rightAbs]
    convert hh using 1
    ring
  have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt habs) (show 0 ≤ 6/ε by positivity)
  have hh' := hs.trans hh
  calc
    _ ≤ 2*ε^2 + 2*((6/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) :=
      hsum.trans (add_le_add_right (mul_le_mul_of_nonneg_left hh' (by norm_num)) _)
    _ = _ := by ring
end ThresholdParallelRepetition.QuantumSampling

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability

structure Law (α : Type u_α) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace Law
variable {α : Type u_α} {β : Type u_β} {γ : Type u_γ} {E : Type u_E} [Fintype α] [Fintype β] [Fintype γ]
  [AddCommMonoid E] [Module ℝ E]

def avg (p : Law α) (f : α → E) : E := ∑ x, p.weight x • f x

lemma avg_const (p : Law α) (e : E) : p.avg (fun _ => e) = e := by
  rw [avg, ← Finset.sum_smul, p.total, one_smul]
lemma avg_add (p : Law α) (f g : α → E) :
    p.avg (fun x => f x+g x) = p.avg f+p.avg g := by
  simp [avg, smul_add, Finset.sum_add_distrib]
lemma avg_sub {F : Type u_F} [AddCommGroup F] [Module ℝ F]
    (p : Law α) (f g : α → F) :
    p.avg (fun x => f x-g x) = p.avg f-p.avg g := by
  simp only [avg, smul_sub, Finset.sum_sub_distrib]
lemma avg_smul (p : Law α) (r : ℝ) (f : α → E) :
    p.avg (fun x => r • f x) = r • p.avg f := by
  simp only [avg, Finset.smul_sum, smul_comm (p.weight _) r]
lemma avg_sum {ι : Type u_ι} [Fintype ι] (p : Law α) (f : ι → α → E) :
    p.avg (fun x => ∑ i, f i x) = ∑ i, p.avg (f i) := by
  simp only [avg, Finset.smul_sum]; exact Finset.sum_comm
lemma avg_linear (p : Law α) (f : α → E) {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) : L (p.avg f) = p.avg (fun x => L (f x)) := by
  simp [avg]

lemma avg_nonneg (p : Law α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ p.avg f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (hf x)
lemma avg_mono (p : Law α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : p.avg f ≤ p.avg g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x)
lemma avg_le_const (p : Law α) {f : α → ℝ} {r : ℝ} (h : ∀ x, f x ≤ r) : p.avg f ≤ r := by
  simpa only [avg_const] using p.avg_mono h
lemma weight_le_one (p : Law α) (x : α) : p.weight x ≤ 1 := by
  rw [← p.total]; exact Finset.single_le_sum (fun y _ => p.nonneg y) (Finset.mem_univ x)

def point [DecidableEq α] (x : α) : Law α where
  weight y := if y=x then 1 else 0
  nonneg y := by split_ifs <;> norm_num
  total := by simp

lemma point_avg [DecidableEq α] (x : α) (f : α → E) : (point x).avg f = f x := by
  simp [point, avg]

def bind (p : Law α) (q : α → Law β) : Law β where
  weight y := ∑ x, p.weight x*(q x).weight y
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) ((q x).nonneg y)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (q _).total, mul_one, p.total]

lemma bind_avg (p : Law α) (q : α → Law β) (f : β → E) :
    (p.bind q).avg f = p.avg (fun x => (q x).avg f) := by
  simp only [bind, avg, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

def map [DecidableEq β] (p : Law α) (f : α → β) : Law β := p.bind (fun x => point (f x))
lemma map_avg [DecidableEq β] (p : Law α) (f : α → β) (g : β → E) :
    (p.map f).avg g = p.avg (fun x => g (f x)) := by
  simp only [map, bind_avg, point_avg]

def prod (p : Law α) (q : Law β) : Law (α × β) where
  weight z := p.weight z.1*q.weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, p.total, q.total]

lemma prod_avg (p : Law α) (q : Law β) (f : α × β → E) :
    (p.prod q).avg f = p.avg (fun x => q.avg (fun y => f (x,y))) := by
  simp only [prod, avg, Fintype.sum_prod_type, mul_smul, Finset.smul_sum]

lemma avg_comm (p : Law α) (q : Law β) (f : α → β → E) :
    p.avg (fun x => q.avg (f x)) = q.avg (fun y => p.avg (fun x => f x y)) := by
  simp only [avg, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro x _
  exact smul_comm _ _ _

def pi {ι : Type u_ι} [Fintype ι] [DecidableEq ι] (p : ι → Law α) : Law (ι → α) where
  weight f := ∏ i, (p i).weight (f i)
  nonneg f := Finset.prod_nonneg fun i _ => (p i).nonneg _
  total := by rw [← Fintype.prod_sum]; simp only [(p _).total, Finset.prod_const_one]

lemma pi_avg_prod {ι : Type u_ι} [Fintype ι] [DecidableEq ι] (p : ι → Law α)
    (f : ι → α → ℝ) :
    (pi p).avg (fun z => ∏ i, f i (z i)) = ∏ i, (p i).avg (f i) := by
  simp only [avg, pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (p i).weight x*f i x)).symm

lemma avg_eq_sum (p : Law α) (f : α → ℝ) : p.avg f = ∑ x, p.weight x*f x := rfl

def normalize [DecidableEq α] (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (a₀ : α) : Law α :=
  if h : ∑ x, w x = 0 then point a₀ else
  { weight := fun x => w x/(∑ y, w y)
    nonneg := fun x => div_nonneg (hw x) (Finset.sum_nonneg fun y _ => hw y)
    total := by rw [← Finset.sum_div, div_self h] }

lemma normalize_weight [DecidableEq α] (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (a₀ x : α) :
    (∑ y, w y)*(normalize w hw a₀).weight x = w x := by
  rw [normalize]
  split_ifs with h
  · have hx : w x = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hw y)).mp h x (Finset.mem_univ x)
    simp [h, hx]
  · simp only
    field_simp

section Pair
variable [DecidableEq α] [DecidableEq β]

def first (p : Law (α×β)) : Law α where
  weight x := ∑ y, p.weight (x,y)
  nonneg x := Finset.sum_nonneg fun y _ => p.nonneg (x,y)
  total := by simpa only [Fintype.sum_prod_type] using p.total

def second (p : Law (α×β)) : Law β where
  weight y := ∑ x, p.weight (x,y)
  nonneg y := Finset.sum_nonneg fun x _ => p.nonneg (x,y)
  total := by rw [Finset.sum_comm]; simpa only [Fintype.sum_prod_type] using p.total

def givenFirst (p : Law (α×β)) (b₀ : β) (x : α) : Law β :=
  normalize (fun y => p.weight (x,y)) (fun y => p.nonneg (x,y)) b₀

def givenSecond (p : Law (α×β)) (a₀ : α) (y : β) : Law α :=
  normalize (fun x => p.weight (x,y)) (fun x => p.nonneg (x,y)) a₀

omit [DecidableEq α] in
lemma first_given (p : Law (α×β)) (b₀ : β) (x : α) (y : β) :
    p.first.weight x*(p.givenFirst b₀ x).weight y = p.weight (x,y) :=
  normalize_weight _ _ _ _
omit [DecidableEq β] in
lemma second_given (p : Law (α×β)) (a₀ : α) (x : α) (y : β) :
    p.second.weight y*(p.givenSecond a₀ y).weight x = p.weight (x,y) :=
  normalize_weight _ _ _ _

omit [DecidableEq α] in
lemma disintegrate_first (p : Law (α×β)) (b₀ : β) (f : α×β → E) :
    p.avg f = p.first.avg (fun x => (p.givenFirst b₀ x).avg (fun y => f (x,y))) := by
  simp only [avg, Fintype.sum_prod_type, Finset.smul_sum, ← mul_smul, first_given]
omit [DecidableEq β] in
lemma disintegrate_second (p : Law (α×β)) (a₀ : α) (f : α×β → E) :
    p.avg f = p.second.avg (fun y => (p.givenSecond a₀ y).avg (fun x => f (x,y))) := by
  simp only [avg, Fintype.sum_prod_type, Finset.smul_sum, ← mul_smul, second_given]
  exact Finset.sum_comm
end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

lemma prod_split (f : ι → ℝ) (i : ι) :
    ∏ j, f j = f i * ∏ j : {j // j ≠ i}, f j := by
  have h := Fintype.prod_subtype_mul_prod_subtype (fun j => j=i) f
  have hd : ((default : {j : ι // j=i}) : ι) = i := (default : {j : ι // j=i}).property
  simpa [hd] using h.symm

lemma pi_weight_split (p : ι → Law α) (i : ι) (u : α) (r : {j // j ≠ i} → α) :
    (pi p).weight ((Equiv.funSplitAt i α).symm (u,r)) =
      (p i).weight u * (pi (fun j : {j // j ≠ i} => p j)).weight r := by
  change (∏ j, (p j).weight (((Equiv.funSplitAt i α).symm (u,r)) j)) = _
  rw [prod_split _ i]
  simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, dite_eq_left, pi]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp [j.property]

lemma pi_avg_split (p : ι → Law α) (i : ι) (f : (ι → α) → E) :
    (pi p).avg f = (p i).avg (fun u =>
      (pi (fun j : {j // j ≠ i} => p j)).avg
        (fun r => f ((Equiv.funSplitAt i α).symm (u,r)))) := by
  rw [avg, ← (Equiv.funSplitAt i α).symm.sum_comp]
  simp only [Fintype.sum_prod_type, pi_weight_split, avg, mul_smul, Finset.smul_sum]

omit [Fintype α] [Fintype ι] in
lemma split_update (i : ι) (z : ι → α) (u : α) :
    Function.update z i u = (Equiv.funSplitAt i α).symm (u, fun j => z j) := by
  ext j; by_cases h : j=i
  · subst j; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

omit [Fintype α] [Fintype ι] in
lemma update_split (i : ι) (r : {j // j ≠ i} → α) (u v : α) :
    Function.update ((Equiv.funSplitAt i α).symm (u,r)) i v =
      (Equiv.funSplitAt i α).symm (v,r) := by
  ext j; by_cases h : j=i
  · subst j; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

lemma pi_avg_update (p : ι → Law α) (i : ι) (f : (ι → α) → E) :
    (pi p).avg (fun z => (p i).avg (fun u => f (Function.update z i u))) = (pi p).avg f := by
  rw [pi_avg_split p i, pi_avg_split p i f]
  simp only [update_split, avg_const]
  exact avg_comm _ _ _
end Pi

section Information

def kl (p q : Law α) : ℝ := p.avg (fun x => Real.log (p.weight x/q.weight x))

def Supports (p q : Law α) : Prop := ∀ x, p.weight x ≠ 0 → q.weight x ≠ 0

lemma mul_log_ratio_lower {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : p ≠ 0 → q ≠ 0) : p-q ≤ p*Real.log (p/q) := by
  by_cases hz : p = 0
  · simp [hz, hq]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm (hs hz))
  have h := Real.log_le_sub_one_of_pos (div_pos hq' hp')
  have h := mul_le_mul_of_nonneg_left h hp
  rw [Real.log_div hq'.ne' hp'.ne'] at h
  rw [Real.log_div hp'.ne' hq'.ne']
  have he : p*(q/p-1) = q-p := by field_simp
  rw [he] at h
  nlinarith

lemma kl_nonneg (p q : Law α) (hs : Supports p q) : 0 ≤ p.kl q := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_log_ratio_lower (p.nonneg x) (q.nonneg x) (hs x))
  simpa [kl, avg, Finset.sum_sub_distrib, p.total, q.total] using h

lemma kl_log_sub (p q : Law α) (hs : Supports p q) :
    p.kl q = p.avg (fun x => Real.log (p.weight x)) -
      p.avg (fun x => Real.log (q.weight x)) := by
  simp only [kl, avg, smul_eq_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p.weight x = 0
  · simp [h]
  · rw [Real.log_div h (hs x h), mul_sub]

lemma map_weight_pos [DecidableEq β] (p : Law α) (f : α → β) (x : α)
    (hx : 0 < p.weight x) : 0 < (p.map f).weight (f x) := by
  have h : p.weight x ≤ (p.map f).weight (f x) := by
    change _ ≤ ∑ y, p.weight y*(point (f y)).weight (f x)
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun y _ => mul_nonneg (p.nonneg y) ((point (f y)).nonneg (f x)))
      (Finset.mem_univ x)
    simpa [point] using hh
  exact hx.trans_le h

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
def marginal (p : Law (ι → α)) (i : ι) : Law α := p.map (fun z => z i)

lemma marginal_avg (p : Law (ι → α)) (i : ι) (f : α → E) :
    (p.marginal i).avg f = p.avg (fun z => f (z i)) := map_avg _ _ _

lemma supports_marginal_pi (p : Law (ι → α)) : Supports p (pi p.marginal) := by
  intro z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt (map_weight_pos p (fun z => z i) z
    (lt_of_le_of_ne (p.nonneg z) (Ne.symm hz)))

lemma avg_log_pi (p : Law (ι → α)) (q : ι → Law α) (hs : Supports p (pi q)) :
    p.avg (fun z => Real.log ((pi q).weight z)) =
      ∑ i, (p.marginal i).avg (fun x => Real.log ((q i).weight x)) := by
  simp_rw [marginal_avg]
  rw [← avg_sum]
  simp only [avg, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : p.weight z = 0
  · simp [hz]
  have hq := hs z hz
  change (∏ i, (q i).weight (z i)) ≠ 0 at hq
  rw [pi, Real.log_prod (Finset.prod_ne_zero_iff.mp hq)]

lemma supports_marginal (p : Law (ι → α)) (q : ι → Law α)
    (hs : Supports p (pi q)) (i : ι) : Supports (p.marginal i) (q i) := by
  intro x hx
  by_contra hqx
  apply hx
  change (∑ z, p.weight z*(point (z i)).weight x) = 0
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : p.weight z = 0
  · simp [hz]
  have hne := Finset.prod_ne_zero_iff.mp (hs z hz) i (Finset.mem_univ i)
  have hzi : z i ≠ x := by intro he; rw [he, hqx] at hne; exact hne rfl
  simp [point, Ne.symm hzi]

lemma kl_tensorization (p : Law (ι → α)) (q : ι → Law α)
    (hs : Supports p (pi q)) :
    (∑ i, (p.marginal i).kl (q i)) ≤ p.kl (pi q) := by
  have h := kl_nonneg p (pi p.marginal) (supports_marginal_pi p)
  rw [kl_log_sub p _ (supports_marginal_pi p), avg_log_pi p _
    (supports_marginal_pi p)] at h
  rw [kl_log_sub p _ hs, avg_log_pi p _ hs]
  simp_rw [kl_log_sub _ _ (supports_marginal p q hs _)]
  rw [Finset.sum_sub_distrib]
  linarith

def tilt (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) : Law α where
  weight x := p.weight x*f x
  nonneg x := mul_nonneg (p.nonneg x) (hf x)
  total := ht

omit [DecidableEq α] in
lemma tilt_avg (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1)
    (g : α → ℝ) : (p.tilt f hf ht).avg g = p.avg (fun x => f x*g x) := by
  simp only [avg, tilt, smul_eq_mul, mul_assoc]

omit [DecidableEq α] in
lemma tilt_supports (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) :
    Supports (p.tilt f hf ht) p := by
  intro x hx
  exact (mul_ne_zero_iff.mp hx).1

omit [DecidableEq α] in
lemma kl_tilt (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) :
    (p.tilt f hf ht).kl p = p.avg (fun x => f x*Real.log (f x)) := by
  simp only [kl, avg, tilt, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p.weight x = 0
  · simp [h]
  · rw [mul_div_cancel_left₀ _ h, mul_assoc]

omit [DecidableEq α] in
lemma kl_tilt_le (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1)
    {B : ℝ} (_hB : 0 < B) (hb : ∀ x, f x ≤ B) : (p.tilt f hf ht).kl p ≤ Real.log B := by
  rw [kl_tilt]
  have h := p.avg_mono (fun x => show f x*Real.log (f x) ≤ f x*Real.log B from by
    by_cases hz : f x = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log
        (lt_of_le_of_ne (hf x) (Ne.symm hz)) (hb x)) (hf x))
  have he : p.avg (fun x => f x*Real.log B) = Real.log B := by
    simp only [avg, smul_eq_mul, ← mul_assoc, ← Finset.sum_mul]
    change p.avg f*Real.log B = _
    rw [ht, one_mul]
  exact h.trans_eq he

lemma avg_indicator (p : Law α) (x : α) :
    p.avg (fun y => if y=x then (1 : ℝ) else 0) = p.weight x := by
  simp [avg]

def coordDensity (q : ι → Law α) (f : (ι → α) → ℝ) (i : ι) (x : α) : ℝ :=
  (pi q).avg (fun z => f (Function.update z i x))

omit [DecidableEq α] in
lemma coordDensity_eq (q : ι → Law α) (f : (ι → α) → ℝ) (i : ι) (x : α) :
    coordDensity q f i x = (pi (fun j : {j // j ≠ i} => q j)).avg
      (fun r => f ((Equiv.funSplitAt i α).symm (x,r))) := by
  rw [coordDensity, pi_avg_split _ i]
  simp only [update_split, avg_const]

lemma marginal_density_avg (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : ι) (g : α → ℝ) :
    (((pi q).tilt f hf ht).marginal i).avg g =
      (q i).avg (fun x => coordDensity q f i x*g x) := by
  rw [marginal_avg, tilt_avg, pi_avg_split _ i]
  congr 1
  funext x
  rw [coordDensity_eq]
  simp only [Equiv.funSplitAt_symm_apply, dite_eq_left]
  simp only [avg, smul_eq_mul, ← mul_assoc, Finset.sum_mul]

lemma marginal_density_weight (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : ι) (x : α) :
    (((pi q).tilt f hf ht).marginal i).weight x = (q i).weight x*coordDensity q f i x := by
  have h := marginal_density_avg q f hf ht i (fun y => if y=x then (1 : ℝ) else 0)
  rw [avg_indicator] at h
  simpa [avg] using h

omit [DecidableEq α] in
lemma coordDensity_nonneg (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (i : ι) (x : α) : 0 ≤ coordDensity q f i x := (pi q).avg_nonneg fun _ => hf _

omit [DecidableEq α] in
lemma coordDensity_total (q : ι → Law α) (f : (ι → α) → ℝ)
    (ht : (pi q).avg f = 1) (i : ι) : (q i).avg (coordDensity q f i) = 1 := by
  rw [show (q i).avg (coordDensity q f i) = (pi q).avg f from by
    change (q i).avg (fun x => (pi q).avg (fun z => f (Function.update z i x))) = _
    rw [avg_comm, pi_avg_update]]
  exact ht

lemma marginal_tilt_eq (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : ι) :
    ((pi q).tilt f hf ht).marginal i = (q i).tilt (coordDensity q f i)
      (coordDensity_nonneg q f hf i) (coordDensity_total q f ht i) := by
  cases he : ((pi q).tilt f hf ht).marginal i
  congr 1
  funext x
  exact (congrArg (fun p : Law α => p.weight x) he).symm.trans
    (marginal_density_weight q f hf ht i x)

lemma coord_entropy_sum_le (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) :
    (∑ i, (q i).avg (fun x => coordDensity q f i x*Real.log (coordDensity q f i x))) ≤
      (pi q).avg (fun z => f z*Real.log (f z)) := by
  have h := kl_tensorization ((pi q).tilt f hf ht) q (tilt_supports _ _ _ _)
  simp_rw [marginal_tilt_eq q f hf ht, kl_tilt] at h
  exact h

end Information

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ThresholdParallelRepetition
namespace ScalarEntropy

lemma negMulLog_subprob {ι : Type u_ι} [Fintype ι]
    (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1)
    (ht : ∀ i, 0 ≤ t i) :
    (∑ i, w i * Real.negMulLog (t i)) ≤ Real.negMulLog (∑ i, w i*t i) := by
  let W : Option ι → ℝ := fun i => i.elim (1-∑ j, w j) w
  let T : Option ι → ℝ := fun i => i.elim 0 t
  have hW : ∀ i, 0 ≤ W i := by
    intro i; cases i with
    | none => exact sub_nonneg.mpr hs
    | some i => exact hw i
  have hsum : ∑ i, W i = 1 := by simp [W, Fintype.sum_option]
  have hT : ∀ i, T i ∈ Set.Ici (0 : ℝ) := by
    intro i; cases i with
    | none => change (0 : ℝ) ≤ 0; rfl
    | some i => exact ht i
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := W) (p := T) (fun i _ => hW i) hsum (fun i _ => hT i)
  simpa [W, T, Fintype.sum_option] using h

lemma hellinger_le_entropy {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t-1)^2 ≤ t*Real.log t-t+1 := by
  have hs := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht
  by_cases hz : t = 0
  · simp [hz]
  have hp : 0 < Real.sqrt t := Real.sqrt_pos.mpr (lt_of_le_of_ne ht (Ne.symm hz))
  have h := Real.self_sub_one_le_mul_log (le_of_lt hp)
  have hl : Real.log t = 2*Real.log (Real.sqrt t) := by
    have he : t = (Real.sqrt t)^2 := hsq.symm
    rw [he, Real.log_pow]
    norm_num
  rw [hl]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr h)]

lemma weighted_negMulLog_le {ι : Type u_ι} [Fintype ι]
    (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 ≤ t i)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ i, w i ≤ d) (hp : 0 < p)
    (hm : ∑ i, w i*t i = p) :
    (∑ i, w i*Real.negMulLog (t i)) ≤ p*Real.log (d/p) := by
  have hw' : ∀ i, 0 ≤ w i/d := fun i => div_nonneg (hw i) hd.le
  have hs' : ∑ i, w i/d ≤ 1 := by rw [← Finset.sum_div]; exact (div_le_one hd).mpr hs
  have h := negMulLog_subprob (fun i => w i/d) t hw' hs' ht
  have hm' : (∑ i, w i/d*t i) = p/d := by
    simp_rw [div_mul_eq_mul_div]; rw [← Finset.sum_div, hm]
  rw [hm'] at h
  have hleft : (∑ i, w i/d*Real.negMulLog (t i)) =
      (∑ i, w i*Real.negMulLog (t i))/d := by
    simp_rw [div_mul_eq_mul_div]; rw [Finset.sum_div]
  rw [hleft] at h
  have h := (div_le_iff₀ hd).mp h
  have he : Real.negMulLog (p/d)*d = p*Real.log (d/p) := by
    change -(p/d)*Real.log (p/d)*d = p*Real.log (d/p)
    rw [Real.log_div hp.ne' hd.ne', Real.log_div hd.ne' hp.ne']
    field_simp
    ring
  exact h.trans_eq he

open FiniteProbability
variable {α : Type u_α} {β : Type u_β} [Fintype α] [Fintype β]

lemma avg_entropy_jensen (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    p.avg f * Real.log (p.avg f) ≤ p.avg (fun x => f x*Real.log (f x)) := by
  have h := negMulLog_subprob p.weight f p.nonneg p.total.le hf
  change -(∑ x, p.weight x*f x)*Real.log (∑ x, p.weight x*f x) ≥ _ at h
  have he : (∑ x, p.weight x*Real.negMulLog (f x)) =
      -(p.avg (fun x => f x*Real.log (f x))) := by
    simp only [Real.negMulLog_def, Law.avg, smul_eq_mul, mul_neg, ← mul_assoc, neg_mul,
      Finset.sum_neg_distrib]
  rw [he] at h
  change p.avg f*Real.log (p.avg f) ≤ _
  dsimp only [Law.avg, smul_eq_mul] at *
  linarith

lemma avg_entropy_nonneg (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ht : p.avg f = 1) : 0 ≤ p.avg (fun x => f x*Real.log (f x)) := by
  have h := avg_entropy_jensen p f hf
  simpa [ht] using h

lemma avg_hellinger_le_entropy (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ht : p.avg f = 1) :
    p.avg (fun x => (Real.sqrt (f x)-1)^2) ≤ p.avg (fun x => f x*Real.log (f x)) := by
  have h := p.avg_mono fun x => hellinger_le_entropy (hf x)
  have he : p.avg (fun x => f x*Real.log (f x)-f x+1) =
      p.avg (fun x => f x*Real.log (f x)) := by
    simp only [Law.avg, smul_eq_mul, mul_add, mul_sub, mul_one,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, p.total]
    change _ - p.avg f + 1 = _
    rw [ht]; ring
  exact h.trans_eq he

lemma first_density_entropy_le [DecidableEq β] (p : Law (α×β)) (b₀ : β)
    (f : α×β → ℝ) (hf : ∀ z, 0 ≤ f z) :
    p.first.avg (fun x => (p.givenFirst b₀ x).avg (fun y => f (x,y)) *
      Real.log ((p.givenFirst b₀ x).avg (fun y => f (x,y)))) ≤
      p.avg (fun z => f z*Real.log (f z)) := by
  rw [Law.disintegrate_first p b₀]
  exact p.first.avg_mono fun x => avg_entropy_jensen _ _ (fun y => hf (x,y))

lemma second_density_entropy_le [DecidableEq α] (p : Law (α×β)) (a₀ : α)
    (f : α×β → ℝ) (hf : ∀ z, 0 ≤ f z) :
    p.second.avg (fun y => (p.givenSecond a₀ y).avg (fun x => f (x,y)) *
      Real.log ((p.givenSecond a₀ y).avg (fun x => f (x,y)))) ≤
      p.avg (fun z => f z*Real.log (f z)) := by
  rw [Law.disintegrate_second p a₀]
  exact p.second.avg_mono fun y => avg_entropy_jensen _ _ (fun x => hf (x,y))

end ScalarEntropy
namespace OperatorEntropy
open Resolvent QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma effectEntropy_nonpos {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    effectEntropy A ≤ 0 := by
  rw [effectEntropy]
  have hz : cfc (fun _ : ℝ => (0 : ℝ)) A = 0 := by simp
  rw [← hz]
  apply (cfc_le_iff _ _ A (hf := Real.continuous_mul_log.continuousOn) (ha := hA.isHermitian)).mpr
  intro t ht
  have ht0 := spectrum_nonneg hA ht
  have ht1 : t ≤ 1 := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i,rfl⟩ := ht
    exact eigenvalues_le_one hA hA1 i
  exact Real.mul_log_nonpos ht0 ht1

lemma spectralLinear_sum (U : Matrix n n ℂ) (v : n → ℝ) :
    spectralLinear U v = ∑ i, v i • spectralLinear U (Pi.single i 1) := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul]

lemma spectralLinear_single_pos (U : Matrix n n ℂ) (i : n) :
    (spectralLinear U (Pi.single i 1)).PosSemidef := by
  rw [spectralLinear_apply]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro j
  simp only [Pi.single_apply]
  split_ifs <;> simp

lemma spectralLinear_one (U : Matrix n n ℂ) (hU : U*Uᴴ=1) :
    spectralLinear U (fun _ => 1) = 1 := by
  simp [spectralLinear_apply, Matrix.diagonal_one, hU]

lemma functional_entropy_lower (Φ : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (hΦ : ∀ A : Matrix n n ℂ, A.PosSemidef → 0 ≤ Φ A)
    (hmass : Φ 1 ≤ 1) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    -Φ (effectEntropy A) ≤ Real.negMulLog (Φ A) := by
  let U : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let w : n → ℝ := fun i => Φ (spectralLinear U (Pi.single i 1))
  have hw : ∀ i, 0 ≤ w i := fun i => hΦ _ (spectralLinear_single_pos U i)
  have hU : U*Uᴴ=1 := Unitary.mul_star_self_of_mem hA.isHermitian.eigenvectorUnitary.property
  have hone : ∑ i, w i = Φ 1 := by
    rw [← spectralLinear_one U hU, spectralLinear_sum]
    simp only [map_sum, map_smul, smul_eq_mul, one_mul, w]
  have heval (f : ℝ → ℝ) : Φ (cfc f A) = ∑ i, w i*f (hA.isHermitian.eigenvalues i) := by
    rw [cfc_eq_spectralLinear hA.isHermitian, spectralLinear_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hid : Φ A = ∑ i, w i*hA.isHermitian.eigenvalues i := by
    have h := heval id
    erw [cfc_id' ℝ A hA.isHermitian] at h
    exact h
  have hh := ScalarEntropy.negMulLog_subprob w hA.isHermitian.eigenvalues hw
    (hone.trans_le hmass) hA.eigenvalues_nonneg
  rw [← hid] at hh
  rw [effectEntropy, heval]
  convert hh using 1
  simp only [Real.negMulLog_def, mul_neg, neg_mul, Finset.sum_neg_distrib]

variable {m : Type u_m} [Fintype m] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
lemma prob_smul_left (C : Matrix m n ℂ) (r : ℝ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (r • A) B = r*prob C A B := by
  simp [prob, eval_eq_trace, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul]
omit [DecidableEq n] [DecidableEq m] in
lemma prob_smul_right (C : Matrix m n ℂ) (r : ℝ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C A (r • B) = r*prob C A B := by
  simp [prob, eval_eq_trace, Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul]

def probLeft (C : Matrix m n ℂ) (B : Matrix n n ℂ) : Matrix m m ℂ →ₗ[ℝ] ℝ where
  toFun A := prob C A B
  map_add' A A' := prob_add_left C A A' B
  map_smul' r A := prob_smul_left C r A B

def probRight (C : Matrix m n ℂ) (A : Matrix m m ℂ) : Matrix n n ℂ →ₗ[ℝ] ℝ where
  toFun B := prob C A B
  map_add' B B' := prob_add_right C A B B'
  map_smul' r B := prob_smul_right C r A B

omit [DecidableEq n] [DecidableEq m] in
lemma prob_mono_left (C : Matrix m n ℂ) {A A' : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hB : B.PosSemidef) (hA : A ≤ A') : prob C A B ≤ prob C A' B := by
  have h := prob_nonneg (C := C) (show (A'-A).PosSemidef from Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hA)) hB
  rw [prob_sub_left] at h
  linarith
omit [DecidableEq n] [DecidableEq m] in
lemma prob_mono_right (C : Matrix m n ℂ) {A : Matrix m m ℂ} {B B' : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B ≤ B') : prob C A B ≤ prob C A B' := by
  have h := prob_nonneg (C := C) hA (show (B'-B).PosSemidef from Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hB))
  rw [prob_sub_right] at h
  linarith

lemma prob_entropy_left_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hB1 : B ≤ 1) :
    -prob C (effectEntropy A) B ≤ Real.negMulLog (prob C A B) := by
  apply functional_entropy_lower (probLeft C B) (fun T hT => prob_nonneg hT hB) _ hA
  exact ((prob_mono_right C Matrix.PosSemidef.one hB1).trans_eq (prob_one C)).trans hC

lemma prob_entropy_right_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hA1 : A ≤ 1) (hB : B.PosSemidef) :
    -prob C A (effectEntropy B) ≤ Real.negMulLog (prob C A B) := by
  apply functional_entropy_lower (probRight C A) (fun T hT => prob_nonneg hA hT) _ hB
  exact ((prob_mono_left C Matrix.PosSemidef.one hA1).trans_eq (prob_one C)).trans hC

end OperatorEntropy
end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [DecidableEq X] [DecidableEq Y] [AddCommMonoid E] [Module ℝ E]

abbrev Profile (I : Type u_I) (X : Type u_X) (Y : Type u_Y) := I → X × Y

def updateLeft (z : Profile I X Y) (i : I) (x : X) : Profile I X Y :=
  Function.update z i (x,(z i).2)
def updateRight (z : Profile I X Y) (i : I) (y : Y) : Profile I X Y :=
  Function.update z i ((z i).1,y)

def left (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E)
    (z : Profile I X Y) : E :=
  (μ.givenSecond x₀ (z i).2).avg (fun x => f (updateLeft z i x))
def right (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E)
    (z : Profile I X Y) : E :=
  (μ.givenFirst y₀ (z i).1).avg (fun y => f (updateRight z i y))

def IgnoresLeft (f : Profile I X Y → E) (i : I) : Prop :=
  ∀ z x, f (updateLeft z i x) = f z
def IgnoresRight (f : Profile I X Y → E) (i : I) : Prop :=
  ∀ z y, f (updateRight z i y) = f z

omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_self (z : Profile I X Y) (i : I) : updateLeft z i (z i).1 = z := by
  simp [updateLeft]
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateRight_self (z : Profile I X Y) (i : I) : updateRight z i (z i).2 = z := by
  simp [updateRight]
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_same (z : Profile I X Y) (i : I) (x x' : X) :
    updateLeft (updateLeft z i x) i x' = updateLeft z i x' := by
  simp [updateLeft]
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateRight_same (z : Profile I X Y) (i : I) (y y' : Y) :
    updateRight (updateRight z i y) i y' = updateRight z i y' := by
  simp [updateRight]
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_comm (z : Profile I X Y) {i j : I} (hij : i ≠ j) (x x' : X) :
    updateLeft (updateLeft z i x) j x' = updateLeft (updateLeft z j x') i x := by
  simp only [updateLeft, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateRight_comm (z : Profile I X Y) {i j : I} (hij : i ≠ j) (y y' : Y) :
    updateRight (updateRight z i y) j y' = updateRight (updateRight z j y') i y := by
  simp only [updateRight, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_right_comm (z : Profile I X Y) (i j : I) (x : X) (y : Y) :
    updateLeft (updateRight z j y) i x = updateRight (updateLeft z i x) j y := by
  by_cases hij : i = j
  · subst j; simp [updateLeft, updateRight]
  · simp only [updateLeft, updateRight, Function.update_of_ne hij,
      Function.update_of_ne (Ne.symm hij)]
    exact Function.update_comm (Ne.symm hij) _ _ z

omit [Fintype I] [DecidableEq Y] in
lemma left_ignoresLeft (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E) :
    IgnoresLeft (μ.left x₀ i f) i := by
  intro z x
  simp only [left, updateLeft, Function.update_self]
  congr 1
  funext x'
  simp [Function.update_idem]
omit [Fintype I] [DecidableEq X] in
lemma right_ignoresRight (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E) :
    IgnoresRight (μ.right y₀ i f) i := by
  intro z y
  simp only [right, updateRight, Function.update_self]
  congr 1
  funext y'
  simp [Function.update_idem]

omit [Fintype I] [DecidableEq Y] in
lemma left_ignoresLeft_other (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresLeft f j) : IgnoresLeft (μ.left x₀ i f) j := by
  intro z x
  have hi : updateLeft z j x i = z i := Function.update_of_ne hij _ _
  simp only [left, hi]
  congr 1
  funext u
  rw [updateLeft_comm z (Ne.symm hij), hf _ _]
omit [Fintype I] [DecidableEq Y] in
lemma left_ignoresRight_other (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresRight f j) : IgnoresRight (μ.left x₀ i f) j := by
  intro z y
  have hi : updateRight z j y i = z i := Function.update_of_ne hij _ _
  simp only [left, hi]
  congr 1
  funext u
  rw [updateLeft_right_comm, hf _ _]
omit [Fintype I] [DecidableEq X] in
lemma right_ignoresRight_other (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresRight f j) : IgnoresRight (μ.right y₀ i f) j := by
  intro z y
  have hi : updateRight z j y i = z i := Function.update_of_ne hij _ _
  simp only [right, hi]
  congr 1
  funext u
  rw [updateRight_comm z (Ne.symm hij), hf _ _]
omit [Fintype I] [DecidableEq X] in
lemma right_ignoresLeft_other (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresLeft f j) : IgnoresLeft (μ.right y₀ i f) j := by
  intro z x
  have hi : updateLeft z j x i = z i := Function.update_of_ne hij _ _
  simp only [right, hi]
  congr 1
  funext u
  rw [← updateLeft_right_comm, hf _ _]

omit [Fintype I] [DecidableEq Y] in
lemma left_of_ignores (μ : Law (X×Y)) (x₀ : X) (i : I)
    {f : Profile I X Y → E} (hf : IgnoresLeft f i) : μ.left x₀ i f = f := by
  funext z
  change (μ.givenSecond x₀ (z i).2).avg (fun x => f (updateLeft z i x)) = f z
  simp only [hf z, avg_const]
omit [Fintype I] [DecidableEq X] in
lemma right_of_ignores (μ : Law (X×Y)) (y₀ : Y) (i : I)
    {f : Profile I X Y → E} (hf : IgnoresRight f i) : μ.right y₀ i f = f := by
  funext z
  change (μ.givenFirst y₀ (z i).1).avg (fun y => f (updateRight z i y)) = f z
  simp only [hf z, avg_const]

omit [DecidableEq Y] in
lemma pair_avg_left (μ : Law (X×Y)) (x₀ : X) (f : X×Y → E) :
    μ.avg (fun z => (μ.givenSecond x₀ z.2).avg (fun x => f (x,z.2))) = μ.avg f := by
  rw [disintegrate_second μ x₀, disintegrate_second μ x₀ f]
  simp only [avg_const]
omit [DecidableEq X] in
lemma pair_avg_right (μ : Law (X×Y)) (y₀ : Y) (f : X×Y → E) :
    μ.avg (fun z => (μ.givenFirst y₀ z.1).avg (fun y => f (z.1,y))) = μ.avg f := by
  rw [disintegrate_first μ y₀, disintegrate_first μ y₀ f]
  simp only [avg_const]

omit [DecidableEq Y] in
lemma pi_avg_left (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E) :
    (pi (fun _ : I => μ)).avg (μ.left x₀ i f) = (pi (fun _ : I => μ)).avg f := by
  rw [pi_avg_split _ i, pi_avg_split _ i f]
  rw [avg_comm, avg_comm μ]
  congr 1
  funext r
  change μ.avg (fun z => (μ.givenSecond x₀ _).avg _) = _
  have he (z : X×Y) (x : X) :
      updateLeft ((Equiv.funSplitAt i (X×Y)).symm (z,r)) i x =
        (Equiv.funSplitAt i (X×Y)).symm ((x,z.2),r) := by
    simpa only [updateLeft, Equiv.funSplitAt_symm_apply, dite_eq_left] using
      update_split i r z (x,z.2)
  simp_rw [he]
  simpa only [Equiv.funSplitAt_symm_apply, dite_eq_left] using
    (pair_avg_left μ x₀ (fun z => f ((Equiv.funSplitAt i (X×Y)).symm (z,r))))
omit [DecidableEq X] in
lemma pi_avg_right (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E) :
    (pi (fun _ : I => μ)).avg (μ.right y₀ i f) = (pi (fun _ : I => μ)).avg f := by
  rw [pi_avg_split _ i, pi_avg_split _ i f]
  rw [avg_comm, avg_comm μ]
  congr 1
  funext r
  change μ.avg (fun z => (μ.givenFirst y₀ _).avg _) = _
  have he (z : X×Y) (y : Y) :
      updateRight ((Equiv.funSplitAt i (X×Y)).symm (z,r)) i y =
        (Equiv.funSplitAt i (X×Y)).symm ((z.1,y),r) := by
    simpa only [updateRight, Equiv.funSplitAt_symm_apply, dite_eq_left] using
      update_split i r z (z.1,y)
  simp_rw [he]
  simpa only [Equiv.funSplitAt_symm_apply, dite_eq_left] using
    (pair_avg_right μ y₀ (fun z => f ((Equiv.funSplitAt i (X×Y)).symm (z,r))))

section Linear
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
omit [Fintype I] [DecidableEq Y] in
lemma left_linear (μ : Law (X×Y)) (x₀ : X) (i : I)
    (f : Profile I X Y → E) (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.left x₀ i f z) = μ.left x₀ i (fun q => L (f q)) z := avg_linear _ _ _
omit [Fintype I] [DecidableEq X] in
lemma right_linear (μ : Law (X×Y)) (y₀ : Y) (i : I)
    (f : Profile I X Y → E) (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.right y₀ i f z) = μ.right y₀ i (fun q => L (f q)) z := avg_linear _ _ _

omit [DecidableEq Y] in
lemma pi_left_pairing (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresLeft L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.left x₀ i f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  have he : (fun z => L z (μ.left x₀ i f z)) =
      μ.left x₀ i (fun z => L z (f z)) := by
    funext z
    rw [left_linear]
    unfold left
    congr 1
    funext x
    simp only [hL z x]
  rw [he, pi_avg_left]

omit [DecidableEq X] in
lemma pi_right_pairing (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresRight L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.right y₀ i f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  have he : (fun z => L z (μ.right y₀ i f z)) =
      μ.right y₀ i (fun z => L z (f z)) := by
    funext z
    rw [right_linear]
    unfold right
    congr 1
    funext y
    simp only [hL z y]
  rw [he, pi_avg_right]
end Linear

section Folds

def lefts (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : Profile I X Y → E) :
    Profile I X Y → E := l.foldr (μ.left x₀) f

def rights (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : Profile I X Y → E) :
    Profile I X Y → E := l.foldr (μ.right y₀) f

omit [Fintype I] [DecidableEq Y] in
lemma lefts_ignoresLeft_mem (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (f : Profile I X Y → E) {i : I} (hi : i ∈ l) : IgnoresLeft (μ.lefts x₀ l f) i := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    by_cases hj : j=i
    · subst j; exact left_ignoresLeft μ x₀ i _
    · exact left_ignoresLeft_other μ x₀ hj (ih ((List.mem_cons.mp hi).resolve_left (Ne.symm hj)))

omit [Fintype I] [DecidableEq X] in
lemma rights_ignoresRight_mem (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (f : Profile I X Y → E) {i : I} (hi : i ∈ l) : IgnoresRight (μ.rights y₀ l f) i := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    by_cases hj : j=i
    · subst j; exact right_ignoresRight μ y₀ i _
    · exact right_ignoresRight_other μ y₀ hj (ih ((List.mem_cons.mp hi).resolve_left (Ne.symm hj)))

omit [Fintype I] [DecidableEq Y] in
lemma lefts_ignoresRight_notMem (μ : Law (X×Y)) (x₀ : X) (l : List I)
    {f : Profile I X Y → E} {i : I} (hi : i ∉ l) (hf : IgnoresRight f i) :
    IgnoresRight (μ.lefts x₀ l f) i := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    have h : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    exact left_ignoresRight_other μ x₀ (Ne.symm h.1) (ih h.2)

omit [Fintype I] [DecidableEq X] in
lemma rights_ignoresLeft_notMem (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    {f : Profile I X Y → E} {i : I} (hi : i ∉ l) (hf : IgnoresLeft f i) :
    IgnoresLeft (μ.rights y₀ l f) i := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    have h : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    exact right_ignoresLeft_other μ y₀ (Ne.symm h.1) (ih h.2)

variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
omit [DecidableEq Y] in
lemma pi_lefts_pairing (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ i ∈ l, IgnoresLeft L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.lefts x₀ l f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (pi _).avg (fun z => L z (μ.left x₀ i (μ.lefts x₀ l f) z)) = _
    rw [pi_left_pairing μ x₀ i _ L (hL i (List.mem_cons_self))]
    exact ih (fun j hj => hL j (List.mem_cons_of_mem i hj))

omit [DecidableEq X] in
lemma pi_rights_pairing (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ i ∈ l, IgnoresRight L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.rights y₀ l f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (pi _).avg (fun z => L z (μ.right y₀ i (μ.rights y₀ l f) z)) = _
    rw [pi_right_pairing μ y₀ i _ L (hL i (List.mem_cons_self))]
    exact ih (fun j hj => hL j (List.mem_cons_of_mem i hj))
end Folds

section FixedCoordinate
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_update (z : Profile I X Y) {i j : I} (hij : i ≠ j)
    (q : X×Y) (x : X) :
    updateLeft (Function.update z i q) j x = Function.update (updateLeft z j x) i q := by
  simp only [updateLeft, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateRight_update (z : Profile I X Y) {i j : I} (hij : i ≠ j)
    (q : X×Y) (y : Y) :
    updateRight (Function.update z i q) j y = Function.update (updateRight z j y) i q := by
  simp only [updateRight, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z

omit [Fintype I] [DecidableEq Y] in
lemma left_update (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    (f : Profile I X Y → E) (z : Profile I X Y) (q : X×Y) :
    μ.left x₀ j f (Function.update z i q) =
      μ.left x₀ j (fun r => f (Function.update r i q)) z := by
  simp only [left, Function.update_of_ne (Ne.symm hij), updateLeft_update _ hij]
omit [Fintype I] [DecidableEq X] in
lemma right_update (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    (f : Profile I X Y → E) (z : Profile I X Y) (q : X×Y) :
    μ.right y₀ j f (Function.update z i q) =
      μ.right y₀ j (fun r => f (Function.update r i q)) z := by
  simp only [right, Function.update_of_ne (Ne.symm hij), updateRight_update _ hij]

variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
omit [DecidableEq Y] in
lemma pi_fixed_left_pairing (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresLeft L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.left x₀ j f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  simp_rw [left_update μ x₀ hij]
  apply pi_left_pairing
  intro z x
  dsimp only
  rw [← updateLeft_update _ hij, hL]
omit [DecidableEq X] in
lemma pi_fixed_right_pairing (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresRight L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.right y₀ j f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  simp_rw [right_update μ y₀ hij]
  apply pi_right_pairing
  intro z y
  dsimp only
  rw [← updateRight_update _ hij, hL]

omit [DecidableEq Y] in
lemma pi_fixed_lefts_pairing (μ : Law (X×Y)) (x₀ : X) (l : List I) {i : I} (hi : i ∉ l)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ j ∈ l, IgnoresLeft L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.lefts x₀ l f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hn : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    change (pi _).avg (fun z => L (Function.update z i q)
      (μ.left x₀ j (μ.lefts x₀ l f) (Function.update z i q))) = _
    rw [pi_fixed_left_pairing μ x₀ hn.1 q _ L (hL j List.mem_cons_self)]
    exact ih hn.2 (fun t ht => hL t (List.mem_cons_of_mem j ht))
omit [DecidableEq X] in
lemma pi_fixed_rights_pairing (μ : Law (X×Y)) (y₀ : Y) (l : List I) {i : I} (hi : i ∉ l)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ j ∈ l, IgnoresRight L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.rights y₀ l f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hn : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    change (pi _).avg (fun z => L (Function.update z i q)
      (μ.right y₀ j (μ.rights y₀ l f) (Function.update z i q))) = _
    rw [pi_fixed_right_pairing μ y₀ hn.1 q _ L (hL j List.mem_cons_self)]
    exact ih hn.2 (fun t ht => hL t (List.mem_cons_of_mem j ht))
end FixedCoordinate

section FoldLinear
variable {R : Type u_R} {F : Type u_F} [Fintype R] [AddCommMonoid F] [Module ℝ F]
omit [Fintype I] [DecidableEq Y] in
lemma lefts_linear (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : Profile I X Y → E)
    (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.lefts x₀ l f z) = μ.lefts x₀ l (fun q => L (f q)) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change L ((μ.givenSecond x₀ (z i).2).avg _) = _
    rw [avg_linear]
    change (μ.givenSecond x₀ (z i).2).avg (fun x => L (μ.lefts x₀ l f (updateLeft z i x))) =
      (μ.givenSecond x₀ (z i).2).avg (fun x => μ.lefts x₀ l (fun q => L (f q)) (updateLeft z i x))
    simp only [ih]
omit [Fintype I] [DecidableEq X] in
lemma rights_linear (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : Profile I X Y → E)
    (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.rights y₀ l f z) = μ.rights y₀ l (fun q => L (f q)) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change L ((μ.givenFirst y₀ (z i).1).avg _) = _
    rw [avg_linear]
    change (μ.givenFirst y₀ (z i).1).avg (fun y => L (μ.rights y₀ l f (updateRight z i y))) =
      (μ.givenFirst y₀ (z i).1).avg (fun y => μ.rights y₀ l (fun q => L (f q)) (updateRight z i y))
    simp only [ih]
omit [Fintype I] [DecidableEq Y] in
lemma lefts_sum (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : R → Profile I X Y → E)
    (z : Profile I X Y) :
    μ.lefts x₀ l (fun q => ∑ r, f r q) z = ∑ r, μ.lefts x₀ l (f r) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change (μ.givenSecond x₀ (z i).2).avg (fun x => μ.lefts x₀ l (fun q => ∑ r, f r q) (updateLeft z i x)) =
      ∑ r, (μ.givenSecond x₀ (z i).2).avg (fun x => μ.lefts x₀ l (f r) (updateLeft z i x))
    simp only [ih]
    exact avg_sum _ _
omit [Fintype I] [DecidableEq X] in
lemma rights_sum (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : R → Profile I X Y → E)
    (z : Profile I X Y) :
    μ.rights y₀ l (fun q => ∑ r, f r q) z = ∑ r, μ.rights y₀ l (f r) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change (μ.givenFirst y₀ (z i).1).avg (fun y => μ.rights y₀ l (fun q => ∑ r, f r q) (updateRight z i y)) =
      ∑ r, (μ.givenFirst y₀ (z i).1).avg (fun y => μ.rights y₀ l (f r) (updateRight z i y))
    simp only [ih]
    exact avg_sum _ _
end FoldLinear

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability

namespace FiniteProbability.Law
variable {R : Type u_R} {n : Type u_n} [Fintype R] [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n] in
lemma avg_posSemidef (p : Law R) (A : R → Matrix n n ℂ) (hA : ∀ r, (A r).PosSemidef) :
    (p.avg A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro r _
  exact (hA r).smul (p.nonneg r)
lemma avg_matrix_mono (p : Law R) {A B : R → Matrix n n ℂ} (h : ∀ r, A r ≤ B r) :
    p.avg A ≤ p.avg B := by
  unfold avg
  exact Finset.sum_le_sum (fun r _ => smul_le_smul_of_nonneg_left (h r) (p.nonneg r))
lemma avg_matrix_le (p : Law R) {A : R → Matrix n n ℂ} {B : Matrix n n ℂ}
    (h : ∀ r, A r ≤ B) : p.avg A ≤ B := by
  simpa only [avg_const] using p.avg_matrix_mono h

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq I]
omit [DecidableEq Y] [Fintype n] [DecidableEq n] in
lemma lefts_posSemidef (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) (hf : ∀ z, (f z).PosSemidef) :
    ∀ z, (μ.lefts x₀ l f z).PosSemidef := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_posSemidef _ _ (fun _ => ih _)
omit [DecidableEq X] [Fintype n] [DecidableEq n] in
lemma rights_posSemidef (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) (hf : ∀ z, (f z).PosSemidef) :
    ∀ z, (μ.rights y₀ l f z).PosSemidef := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_posSemidef _ _ (fun _ => ih _)
omit [DecidableEq Y] in
lemma lefts_le (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) {B : Matrix n n ℂ} (hf : ∀ z, f z ≤ B) :
    ∀ z, μ.lefts x₀ l f z ≤ B := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_matrix_le _ (fun _ => ih _)
omit [DecidableEq X] in
lemma rights_le (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) {B : Matrix n n ℂ} (hf : ∀ z, f z ≤ B) :
    ∀ z, μ.rights y₀ l f z ≤ B := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_matrix_le _ (fun _ => ih _)
end FiniteProbability.Law

namespace QuantumSampling.POVM
variable {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} [Fintype n] [DecidableEq n] [Fintype A] [Fintype B] [Fintype R]
lemma le_one (P : POVM n A) (a : A) : P.effect a ≤ 1 := by
  rw [← P.total]
  exact Finset.single_le_sum (fun b _ => (P.pos b).nonneg) (Finset.mem_univ a)

def coarsen (P : POVM n A) (f : A → B) : POVM n B := by
  classical
  exact {
    effect b := ∑ a with f a=b, P.effect a
    pos b := Matrix.posSemidef_sum _ (fun a _ => P.pos a)
    total := by simp only [Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (f a)), P.total] }

lemma coarsen_sum (P : POVM n A) (f : A → B) (g : B → Matrix n n ℂ →ₗ[ℝ] ℝ) :
    (∑ b, g b ((P.coarsen f).effect b)) = ∑ a, g (f a) (P.effect a) := by
  classical
  simp only [coarsen, map_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

def average (p : Law R) (P : R → POVM n A) : POVM n A where
  effect a := p.avg (fun r => (P r).effect a)
  pos a := p.avg_posSemidef _ (fun r => (P r).pos a)
  total := by
    simp only [Law.avg]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, (P _).total]
    exact p.avg_const 1
end QuantumSampling.POVM

namespace OperatorEntropy
variable {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
lemma potential_left_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hH : ∀ r, (H r).PosSemidef) (hH1 : ∀ r, H r ≤ 1)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ r, w r ≤ d) (hp : 0 < p)
    (hm : ∑ r, w r*prob C (F r) (H r) = p) :
    -p*Real.log (d/p) ≤ ∑ r, w r * prob C (effectEntropy (F r)) (H r) := by
  have h := ScalarEntropy.weighted_negMulLog_le w (fun r => prob C (F r) (H r)) hw
    (fun r => prob_nonneg (hF r) (hH r)) hd hs hp hm
  have h' : -(∑ r, w r*prob C (effectEntropy (F r)) (H r)) ≤
      ∑ r, w r*Real.negMulLog (prob C (F r) (H r)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun r _ => by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left
        (prob_entropy_left_lower C hC (hF r) (hH r) (hH1 r)) (hw r))
  linarith
lemma potential_right_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hF1 : ∀ r, F r ≤ 1) (hH : ∀ r, (H r).PosSemidef)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ r, w r ≤ d) (hp : 0 < p)
    (hm : ∑ r, w r*prob C (F r) (H r) = p) :
    -p*Real.log (d/p) ≤ ∑ r, w r * prob C (F r) (effectEntropy (H r)) := by
  have h := ScalarEntropy.weighted_negMulLog_le w (fun r => prob C (F r) (H r)) hw
    (fun r => prob_nonneg (hF r) (hH r)) hd hs hp hm
  have h' : -(∑ r, w r*prob C (F r) (effectEntropy (H r))) ≤
      ∑ r, w r*Real.negMulLog (prob C (F r) (H r)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun r _ => by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left
        (prob_entropy_right_lower C hC (hF r) (hF1 r) (hH r)) (hw r))
  linarith
omit [DecidableEq n] in
lemma potential_left_nonpos (C : Matrix m n ℂ)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hF1 : ∀ r, F r ≤ 1) (hH : ∀ r, (H r).PosSemidef) :
    (∑ r, w r * prob C (effectEntropy (F r)) (H r)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro r _
  apply mul_nonpos_of_nonneg_of_nonpos (hw r)
  simpa only [prob, eval_eq_trace, Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero,
    Complex.zero_re] using prob_mono_left C (hH r) (effectEntropy_nonpos (hF r) (hF1 r))
omit [DecidableEq m] in
lemma potential_right_nonpos (C : Matrix m n ℂ)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hH : ∀ r, (H r).PosSemidef) (hH1 : ∀ r, H r ≤ 1) :
    (∑ r, w r * prob C (F r) (effectEntropy (H r))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro r _
  apply mul_nonpos_of_nonneg_of_nonpos (hw r)
  simpa only [prob, eval_eq_trace, Matrix.transpose_zero, Matrix.mul_zero, Matrix.trace_zero,
    Complex.zero_re] using prob_mono_right C (hF r) (effectEntropy_nonpos (hH r) (hH1 r))
end OperatorEntropy

namespace Resolvent
variable {J : Type u_J} {n : Type u_n} [Fintype J] [Nonempty J] [DecidableEq J] [Fintype n] [DecidableEq n]

def effectIndex (A : J → Matrix n n ℂ) (T : Matrix n n ℂ) : J :=
  if h : T ∈ Set.range A then Classical.choose h else Classical.choice inferInstance

def commonMap (A : J → Matrix n n ℂ) (T : Matrix n n ℂ) : Matrix (J×n) n ℂ :=
  finitePurification A (effectIndex A T)

omit [DecidableEq J] [DecidableEq n] in
lemma effectIndex_eq (A : J → Matrix n n ℂ) {T : Matrix n n ℂ} (hT : T ∈ Set.range A) :
    A (effectIndex A T) = T := by
  rw [effectIndex, dif_pos hT]
  exact Classical.choose_spec hT
lemma commonMap_gram (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef)
    {T : Matrix n n ℂ} (hT : T ∈ Set.range A) :
    (commonMap A T)ᴴ*commonMap A T = T := by
  rw [commonMap, finitePurification_self A hA, effectIndex_eq A hT]

lemma commonMap_jensen {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (p : Law R) (F : R → Matrix n n ℂ) (hF : ∀ r, F r ∈ Set.range A)
    (hmean : p.avg F ∈ Set.range A) :
    p.avg (fun r => (commonMap A (F r)-commonMap A (p.avg F))ᴴ *
      (commonMap A (F r)-commonMap A (p.avg F))) ≤
      p.avg (fun r => effectEntropy (F r)) - effectEntropy (p.avg F) := by
  have h := finitePurification_jensen A hA hA1 (fun r => effectIndex A (F r)) p.weight
    (effectIndex A (p.avg F)) p.nonneg p.total (by
      simp only [effectIndex_eq A (hF _), effectIndex_eq A hmean]; rfl)
  simp only [effectIndex_eq A (hF _), effectIndex_eq A hmean] at h
  exact h

variable {m : Type u_m} {K : Type u_K} [Fintype m] [DecidableEq m] [Fintype K] [DecidableEq K]
omit [DecidableEq m] in
lemma commonMap_error_left {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (p : Law R) (F : R → Matrix n n ℂ) (hF : ∀ r, F r ∈ Set.range A)
    (hmean : p.avg F ∈ Set.range A) (C : Matrix n m ℂ) (L : Matrix K m ℂ) :
    p.avg (fun r => hsSq ((commonMap A (F r)-commonMap A (p.avg F))*C*Lᵀ)) ≤
      p.avg (fun r => prob C (effectEntropy (F r)) (Lᴴ*L)) -
        prob C (effectEntropy (p.avg F)) (Lᴴ*L) := by
  have h := prob_mono_left C (Matrix.posSemidef_conjTranspose_mul_self L)
    (commonMap_jensen A hA hA1 p F hF hmean)
  rw [prob_sub_left] at h
  have he (T : R → Matrix n n ℂ) : prob C (p.avg T) (Lᴴ*L) =
      p.avg (fun r => prob C (T r) (Lᴴ*L)) := p.avg_linear T (probLeft C (Lᴴ*L))
  rw [he, he] at h
  convert h using 1
  apply congrArg p.avg
  funext r
  exact (prob_gram C _ L).symm
omit [DecidableEq m] in
lemma commonMap_error_right {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (p : Law R) (F : R → Matrix n n ℂ) (hF : ∀ r, F r ∈ Set.range A)
    (hmean : p.avg F ∈ Set.range A) (C : Matrix m n ℂ) (L : Matrix K m ℂ) :
    p.avg (fun r => hsSq (L*C*(commonMap A (F r)-commonMap A (p.avg F))ᵀ)) ≤
      p.avg (fun r => prob C (Lᴴ*L) (effectEntropy (F r))) -
        prob C (Lᴴ*L) (effectEntropy (p.avg F)) := by
  have h := prob_mono_right C (Matrix.posSemidef_conjTranspose_mul_self L)
    (commonMap_jensen A hA hA1 p F hF hmean)
  rw [prob_sub_right] at h
  have he (T : R → Matrix n n ℂ) : prob C (Lᴴ*L) (p.avg T) =
      p.avg (fun r => prob C (Lᴴ*L) (T r)) := p.avg_linear T (probRight C (Lᴴ*L))
  rw [he, he] at h
  convert h using 1
  apply congrArg p.avg
  funext r
  exact (prob_gram C L _).symm
end Resolvent

end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} {J : Type u_J} {K : Type u_K} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype J] [DecidableEq J] [Nonempty J] [Fintype K] [DecidableEq K] [Nonempty K]

lemma step_left (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (i : I)
    (C : Matrix m n ℂ) (A : J → Matrix m m ℂ) (B : K → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1) (hB : ∀ j, (B j).PosSemidef)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ z, F z ∈ Set.range A) (hF0 : ∀ z, μ.left x₀ i F z ∈ Set.range A)
    (hH : ∀ z, H z ∈ Set.range B) (hFi : IgnoresRight F i) (hHi : IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθ : ∀ z, 0 ≤ θ z)
    (hθL : IgnoresLeft θ i) (hθR : IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * hsSq
      ((commonMap A (F z) - commonMap A (μ.left x₀ i F z))*C*(commonMap B (H z))ᵀ)) ≤
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (effectEntropy (F z)) (μ.right y₀ i H z)) -
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (effectEntropy (μ.left x₀ i F z)) (H z)) := by
  let ρ := pi (fun _ : I => μ)
  let T := μ.left x₀ i F
  let e : Profile I X Y → ℝ := fun z => θ z * hsSq
    ((commonMap A (F z)-commonMap A (T z))*C*(commonMap B (H z))ᵀ)
  have hTi : IgnoresLeft T i := left_ignoresLeft μ x₀ i F
  have hstep (z : Profile I X Y) : μ.left x₀ i e z ≤
      θ z * (prob C (μ.left x₀ i (fun z => effectEntropy (F z)) z) (H z) -
        prob C (effectEntropy (T z)) (H z)) := by
    have h := commonMap_error_left A hA hA1 (μ.givenSecond x₀ (z i).2)
      (fun x => F (updateLeft z i x)) (fun x => hF _) (hF0 z) C (commonMap B (H z))
    rw [commonMap_gram B hB (hH z)] at h
    have hl : μ.left x₀ i e z = θ z *
        (μ.givenSecond x₀ (z i).2).avg (fun x => hsSq
          ((commonMap A (F (updateLeft z i x))-commonMap A (T z))*C*(commonMap B (H z))ᵀ)) := by
      simp only [left, e, hθL z, hTi z, hHi z, Law.avg, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hl]
    apply mul_le_mul_of_nonneg_left _ (hθ z)
    have heq := (μ.givenSecond x₀ (z i).2).avg_linear
      (fun x => effectEntropy (F (updateLeft z i x))) (probLeft C (H z))
    change prob C (μ.left x₀ i (fun z => effectEntropy (F z)) z) (H z) = _ at heq
    rw [heq]
    exact h
  have havg := ρ.avg_mono hstep
  have hPairL : ρ.avg (fun z => θ z * prob C (μ.left x₀ i (fun z => effectEntropy (F z)) z) (H z)) =
      ρ.avg (fun z => θ z * prob C (effectEntropy (F z)) (H z)) := by
    apply pi_left_pairing μ x₀ i (fun z => effectEntropy (F z))
      (fun z => θ z • probLeft C (H z))
    intro z x
    simp only [hθL z, hHi z]
  have hPairR : ρ.avg (fun z => θ z * prob C (effectEntropy (F z)) (μ.right y₀ i H z)) =
      ρ.avg (fun z => θ z * prob C (effectEntropy (F z)) (H z)) := by
    apply pi_right_pairing μ y₀ i H (fun z => θ z • probRight C (effectEntropy (F z)))
    intro z y
    simp only [hθR z, hFi z]
  have he : ρ.avg (μ.left x₀ i e) = ρ.avg e := pi_avg_left μ x₀ i e
  rw [he] at havg
  have hr : ρ.avg (fun z => θ z * (prob C (μ.left x₀ i (fun z => effectEntropy (F z)) z) (H z) -
        prob C (effectEntropy (T z)) (H z))) =
      ρ.avg (fun z => θ z*prob C (effectEntropy (F z)) (μ.right y₀ i H z)) -
      ρ.avg (fun z => θ z*prob C (effectEntropy (T z)) (H z)) := by
    simp only [mul_sub, Law.avg_sub]
    rw [hPairL, hPairR]
  exact havg.trans_eq hr

lemma step_right (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (i : I)
    (C : Matrix m n ℂ) (A : J → Matrix m m ℂ) (B : K → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ j, (B j).PosSemidef) (hB1 : ∀ j, B j ≤ 1)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ z, F z ∈ Set.range A) (hH : ∀ z, H z ∈ Set.range B)
    (hH1 : ∀ z, μ.right y₀ i H z ∈ Set.range B)
    (hFi : IgnoresRight F i) (hHi : IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθ : ∀ z, 0 ≤ θ z)
    (hθL : IgnoresLeft θ i) (hθR : IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * hsSq
      (commonMap A (F z)*C*(commonMap B (H z) - commonMap B (μ.right y₀ i H z))ᵀ)) ≤
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (μ.left x₀ i F z) (effectEntropy (H z))) -
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (effectEntropy (μ.right y₀ i H z))) := by
  let ρ := pi (fun _ : I => μ)
  let T := μ.right y₀ i H
  let e : Profile I X Y → ℝ := fun z => θ z * hsSq
    (commonMap A (F z)*C*(commonMap B (H z)-commonMap B (T z))ᵀ)
  have hTi : IgnoresRight T i := right_ignoresRight μ y₀ i H
  have hstep (z : Profile I X Y) : μ.right y₀ i e z ≤
      θ z * (prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z) -
        prob C (F z) (effectEntropy (T z))) := by
    have h := commonMap_error_right B hB hB1 (μ.givenFirst y₀ (z i).1)
      (fun y => H (updateRight z i y)) (fun y => hH _) (hH1 z) C (commonMap A (F z))
    rw [commonMap_gram A hA (hF z)] at h
    have hl : μ.right y₀ i e z = θ z *
        (μ.givenFirst y₀ (z i).1).avg (fun y => hsSq
          (commonMap A (F z)*C*(commonMap B (H (updateRight z i y))-commonMap B (T z))ᵀ)) := by
      simp only [right, e, hθR z, hTi z, hFi z, Law.avg, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hl]
    apply mul_le_mul_of_nonneg_left _ (hθ z)
    have heq := (μ.givenFirst y₀ (z i).1).avg_linear
      (fun y => effectEntropy (H (updateRight z i y))) (probRight C (F z))
    change prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z) = _ at heq
    rw [heq]
    exact h
  have havg := ρ.avg_mono hstep
  have hPairR : ρ.avg (fun z => θ z * prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z)) =
      ρ.avg (fun z => θ z * prob C (F z) (effectEntropy (H z))) := by
    apply pi_right_pairing μ y₀ i (fun z => effectEntropy (H z))
      (fun z => θ z • probRight C (F z))
    intro z y
    simp only [hθR z, hFi z]
  have hPairL : ρ.avg (fun z => θ z * prob C (μ.left x₀ i F z) (effectEntropy (H z))) =
      ρ.avg (fun z => θ z * prob C (F z) (effectEntropy (H z))) := by
    apply pi_left_pairing μ x₀ i F (fun z => θ z • probLeft C (effectEntropy (H z)))
    intro z x
    simp only [hθL z, hHi z]
  have he : ρ.avg (μ.right y₀ i e) = ρ.avg e := pi_avg_right μ y₀ i e
  rw [he] at havg
  have hr : ρ.avg (fun z => θ z * (prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z) -
        prob C (F z) (effectEntropy (T z)))) =
      ρ.avg (fun z => θ z*prob C (μ.left x₀ i F z) (effectEntropy (H z))) -
      ρ.avg (fun z => θ z*prob C (F z) (effectEntropy (T z))) := by
    simp only [mul_sub, Law.avg_sub]
    rw [hPairR, hPairL]
  exact havg.trans_eq hr
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [Fintype n]

lemma mixed_pairing (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l r : List I)
    (hlr : ∀ i ∈ l, i ∉ r) (C : Matrix m n ℂ)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ i ∈ r, IgnoresRight F i) (hH : ∀ i ∈ l, IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθL : ∀ i ∈ l, IgnoresLeft θ i) (hθR : ∀ i ∈ r, IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (μ.lefts x₀ l F z) (μ.rights y₀ r H z)) =
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (H z)) := by
  calc
    _ = (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (μ.rights y₀ r H z)) := by
      apply pi_lefts_pairing μ x₀ l F (fun z => θ z • probLeft C (μ.rights y₀ r H z))
      intro i hi z x
      simp only [hθL i hi z, rights_ignoresLeft_notMem μ y₀ r (hlr i hi) (hH i hi) z]
    _ = _ := by
      apply pi_rights_pairing μ y₀ r H (fun z => θ z • probRight C (F z))
      intro i hi z y
      simp only [hθR i hi z, hF i hi z]

lemma fixed_mixed_pairing (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l r : List I)
    (hlr : ∀ i ∈ l, i ∉ r) (C : Matrix m n ℂ)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ i ∈ r, IgnoresRight F i) (hH : ∀ i ∈ l, IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθL : ∀ i ∈ l, IgnoresLeft θ i) (hθR : ∀ i ∈ r, IgnoresRight θ i)
    (i : I) (hiL : i ∉ l) (hiR : i ∉ r) (q : X×Y) :
    (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) * prob C
      (μ.lefts x₀ l F (Function.update z i q)) (μ.rights y₀ r H (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) *
      prob C (F (Function.update z i q)) (H (Function.update z i q))) := by
  calc
    _ = (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) *
        prob C (F (Function.update z i q)) (μ.rights y₀ r H (Function.update z i q))) := by
      apply pi_fixed_lefts_pairing μ x₀ l hiL q F (fun z => θ z • probLeft C (μ.rights y₀ r H z))
      intro j hj z x
      simp only [hθL j hj z, rights_ignoresLeft_notMem μ y₀ r (hlr j hj) (hH j hj) z]
    _ = _ := by
      apply pi_fixed_rights_pairing μ y₀ r hiR q H (fun z => θ z • probRight C (F z))
      intro j hj z y
      simp only [hθR j hj z, hF j hj z]
end ThresholdParallelRepetition.MixedExposure

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law

lemma list_suffix_prefix_disjoint {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ) :
    ∀ i ∈ l.drop j, i ∉ (l.take j).reverse := by
  have h : (l.take j ++ l.drop j).Nodup := by simpa using hN
  have hd := (List.nodup_append.mp h).2.2
  intro i hi hi'
  exact hd i (List.mem_reverse.mp hi') i hi rfl

lemma list_fresh_not_suffix {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ)
    (hj : j < l.length) : l[j] ∉ l.drop (j+1) := by
  have h : (l.drop j).Nodup := hN.drop
  rw [List.drop_eq_getElem_cons hj] at h
  exact (List.nodup_cons.mp h).1

lemma list_fresh_not_prefix {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ)
    (hj : j < l.length) : l[j] ∉ (l.take j).reverse := by
  apply list_suffix_prefix_disjoint l hN j l[j]
  rw [List.drop_eq_getElem_cons hj]
  exact List.mem_cons_self

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

variable {E : Type u_E} [AddCommMonoid E] [Module ℝ E]
def chainLeft (μ : Law (X×Y)) (x₀ : X) (l : List I) (F : R → Profile I X Y → E)
    (j : ℕ) (r : R) : Profile I X Y → E := μ.lefts x₀ (l.drop j) (F r)
def chainRight (μ : Law (X×Y)) (y₀ : Y) (l : List I) (H : R → Profile I X Y → E)
    (j : ℕ) (r : R) : Profile I X Y → E := μ.rights y₀ (l.take j).reverse (H r)

omit [Fintype I] [DecidableEq Y] [Fintype R] in
lemma chainLeft_step (μ : Law (X×Y)) (x₀ : X) (l : List I) (F : R → Profile I X Y → E)
    (j : ℕ) (hj : j < l.length) (r : R) :
    chainLeft μ x₀ l F j r = μ.left x₀ l[j] (chainLeft μ x₀ l F (j+1) r) := by
  unfold chainLeft
  rw [List.drop_eq_getElem_cons hj]
  rfl
omit [Fintype I] [DecidableEq X] [Fintype R] in
lemma chainRight_step (μ : Law (X×Y)) (y₀ : Y) (l : List I) (H : R → Profile I X Y → E)
    (j : ℕ) (hj : j < l.length) (r : R) :
    chainRight μ y₀ l H (j+1) r = μ.right y₀ l[j] (chainRight μ y₀ l H j r) := by
  unfold chainRight
  rw [List.take_succ_eq_append_getElem hj, List.reverse_append]
  rfl

omit [Fintype I] [DecidableEq Y] [Fintype R] in
lemma chainLeft_next_local (μ : Law (X×Y)) (x₀ : X) (l : List I) (hN : l.Nodup)
    (F : R → Profile I X Y → E) (hF : ∀ r i, IgnoresRight (F r) i)
    (j : ℕ) (hj : j < l.length) (r : R) :
    IgnoresRight (chainLeft μ x₀ l F (j+1) r) l[j] :=
  lefts_ignoresRight_notMem μ x₀ _ (list_fresh_not_suffix l hN j hj) (hF r _)
omit [Fintype I] [DecidableEq X] [Fintype R] in
lemma chainRight_prev_local (μ : Law (X×Y)) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (H : R → Profile I X Y → E) (hH : ∀ r i, IgnoresLeft (H r) i)
    (j : ℕ) (hj : j < l.length) (r : R) :
    IgnoresLeft (chainRight μ y₀ l H j r) l[j] :=
  rights_ignoresLeft_notMem μ y₀ _ (list_fresh_not_prefix l hN j hj) (hH r _)

omit [DecidableEq m] [DecidableEq n] in
lemma chain_mass (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r i, IgnoresRight (F r) i) (hH : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    (j : ℕ) :
    (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (chainLeft μ x₀ l F j r z) (chainRight μ y₀ l H j r z))) =
    ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * prob C (F r z) (H r z)) := by
  apply Finset.sum_congr rfl
  intro r _
  apply mixed_pairing μ x₀ y₀ _ _ (list_suffix_prefix_disjoint l hN j) C (F r) (H r)
    (fun i _ => hF r i) (fun i _ => hH r i) (θ r)
  · exact fun i hi => hθL r i (List.mem_of_mem_drop hi)
  · exact fun i hi => hθR r i (List.mem_of_mem_take (List.mem_reverse.mp hi))
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {R : Type u_R} {Z : Type u_Z} {m : Type u_m} {n : Type u_n} [Fintype R] [Nonempty R] [Fintype Z]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [Nonempty R] in
lemma tested_weight_sum_le (ρ : Law Z) (θ : R → Z → ℝ) (hθ1 : ∀ r z, θ r z ≤ 1) :
    (∑ t : R×Z, ρ.weight t.2 * θ t.1 t.2) ≤ Fintype.card R := by
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _r : R, ∑ z, ρ.weight z := by
      apply Finset.sum_le_sum; intro r _
      exact Finset.sum_le_sum (fun z _ => by nlinarith [ρ.nonneg z, hθ1 r z])
    _ = _ := by simp only [ρ.total, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma averaged_potential_left_bounds (ρ : Law Z) (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (θ : R → Z → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (F : R → Z → Matrix m m ℂ) (H : R → Z → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    {p : ℝ} (hp : 0 < p) (hm : (∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (H r z))) = p) :
    -p*Real.log ((Fintype.card R : ℝ)/p) ≤
      ∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (F r z)) (H r z)) ∧
    (∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (F r z)) (H r z))) ≤ 0 := by
  have hmass : ∑ t : R×Z, (ρ.weight t.2*θ t.1 t.2)*prob C (F t.1 t.2) (H t.1 t.2) = p := by
    simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using hm
  have h0 := potential_left_lower C hC (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hH _ _) (fun t => hH1 _ _)
    (Nat.cast_pos.mpr (Fintype.card_pos)) (tested_weight_sum_le ρ θ hθ1) hp hmass
  have h1 := potential_left_nonpos C (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hF1 _ _) (fun t => hH _ _)
  simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using And.intro h0 h1

lemma averaged_potential_right_bounds (ρ : Law Z) (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (θ : R → Z → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (F : R → Z → Matrix m m ℂ) (H : R → Z → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    {p : ℝ} (hp : 0 < p) (hm : (∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (H r z))) = p) :
    -p*Real.log ((Fintype.card R : ℝ)/p) ≤
      ∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (effectEntropy (H r z))) ∧
    (∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (effectEntropy (H r z)))) ≤ 0 := by
  have hmass : ∑ t : R×Z, (ρ.weight t.2*θ t.1 t.2)*prob C (F t.1 t.2) (H t.1 t.2) = p := by
    simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using hm
  have h0 := potential_right_lower C hC (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hF1 _ _) (fun t => hH _ _)
    (Nat.cast_pos.mpr (Fintype.card_pos)) (tested_weight_sum_le ρ θ hθ1) hp hmass
  have h1 := potential_right_nonpos C (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hH _ _) (fun t => hH1 _ _)
  simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using And.intro h0 h1

lemma fin_telescope_bound {N : ℕ} (U : ℕ → ℝ) (e : Fin N → ℝ) (L : ℝ)
    (hstep : ∀ i, e i ≤ U (i+1)-U i) (h0 : -L ≤ U 0) (hN : U N ≤ 0) :
    ∑ i, e i ≤ L := by
  calc
    _ ≤ ∑ i : Fin N, (U (i+1)-U i) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = U N-U 0 := by rw [Fin.sum_univ_eq_sum_range (fun i => U (i+1)-U i), Finset.sum_range_sub]
    _ ≤ L := by linarith

lemma fin_telescope_bound_rev {N : ℕ} (U : ℕ → ℝ) (e : Fin N → ℝ) (L : ℝ)
    (hstep : ∀ i, e i ≤ U i-U (i+1)) (h0 : U 0 ≤ 0) (hN : -L ≤ U N) :
    ∑ i, e i ≤ L := by
  calc
    _ ≤ ∑ i : Fin N, (U i-U (i+1)) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = U 0-U N := by rw [Fin.sum_univ_eq_sum_range (fun i => U i-U (i+1)), Finset.sum_range_sub']
    _ ≤ L := by linarith
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

abbrev ExposureIndex (l : List I) := Fin (l.length+1) × R × Profile I X Y

def chainLeftFamily (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (F : R → Profile I X Y → Matrix m m ℂ) :
    ExposureIndex (R := R) (X := X) (Y := Y) l → Matrix m m ℂ :=
  fun t => chainLeft μ x₀ l F t.1 t.2.1 t.2.2

def chainRightFamily (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (H : R → Profile I X Y → Matrix n n ℂ) :
    ExposureIndex (R := R) (X := X) (Y := Y) l → Matrix n n ℂ :=
  fun t => chainRight μ y₀ l H t.1 t.2.1 t.2.2

lemma chain_error_bounds (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    (hFlocal : ∀ r i, IgnoresRight (F r) i) (hHlocal : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    {p : ℝ} (hp : 0 < p)
    (hm : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * prob C (F r z) (H r z))) = p) :
    let A := chainLeftFamily μ x₀ l F
    let B := chainRightFamily μ y₀ l H
    (∑ j : Fin l.length, ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
      ((commonMap A (chainLeft μ x₀ l F (j+1) r z)-commonMap A (chainLeft μ x₀ l F j r z))*C*
        (commonMap B (chainRight μ y₀ l H j r z))ᵀ))) ≤ p*Real.log ((Fintype.card R : ℝ)/p) ∧
    (∑ j : Fin l.length, ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
      (commonMap A (chainLeft μ x₀ l F (j+1) r z)*C*
        (commonMap B (chainRight μ y₀ l H j r z)-commonMap B (chainRight μ y₀ l H (j+1) r z))ᵀ))) ≤
      p*Real.log ((Fintype.card R : ℝ)/p) := by
  let ρ := pi (fun _ : I => μ)
  let A := chainLeftFamily μ x₀ l F
  let B := chainRightFamily μ y₀ l H
  let f := chainLeft μ x₀ l F
  let h := chainRight μ y₀ l H
  have hfpos : ∀ j r z, (f j r z).PosSemidef :=
    fun j r => lefts_posSemidef μ x₀ _ _ (hF r)
  have hf1 : ∀ j r z, f j r z ≤ 1 := fun j r => lefts_le μ x₀ _ _ (hF1 r)
  have hhpos : ∀ j r z, (h j r z).PosSemidef :=
    fun j r => rights_posSemidef μ y₀ _ _ (hH r)
  have hh1 : ∀ j r z, h j r z ≤ 1 := fun j r => rights_le μ y₀ _ _ (hH1 r)
  have hA : ∀ t, (A t).PosSemidef := fun t => hfpos _ _ _
  have hA1 : ∀ t, A t ≤ 1 := fun t => hf1 _ _ _
  have hB : ∀ t, (B t).PosSemidef := fun t => hhpos _ _ _
  have hB1 : ∀ t, B t ≤ 1 := fun t => hh1 _ _ _
  have hfRange : ∀ j, j ≤ l.length → ∀ r z, f j r z ∈ Set.range A := by
    intro j hj r z
    exact ⟨(⟨j, by omega⟩, r, z), rfl⟩
  have hhRange : ∀ j, j ≤ l.length → ∀ r z, h j r z ∈ Set.range B := by
    intro j hj r z
    exact ⟨(⟨j, by omega⟩, r, z), rfl⟩
  let U : ℕ → ℝ := fun j => ∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (f j r z)) (h j r z))
  let Z : ℕ → ℝ := fun j => ∑ r, ρ.avg (fun z => θ r z*prob C (f j r z) (effectEntropy (h j r z)))
  have hmass (j : ℕ) : (∑ r, ρ.avg (fun z => θ r z*prob C (f j r z) (h j r z))) = p :=
    (chain_mass μ x₀ y₀ l hN C F H hFlocal hHlocal θ hθL hθR j).trans hm
  have hU (j : ℕ) : -p*Real.log ((Fintype.card R : ℝ)/p) ≤ U j ∧ U j ≤ 0 :=
    averaged_potential_left_bounds ρ C hC θ hθ hθ1 (f j) (h j)
      (hfpos j) (hf1 j) (hhpos j) (hh1 j) hp (hmass j)
  have hZ (j : ℕ) : -p*Real.log ((Fintype.card R : ℝ)/p) ≤ Z j ∧ Z j ≤ 0 :=
    averaged_potential_right_bounds ρ C hC θ hθ hθ1 (f j) (h j)
      (hfpos j) (hf1 j) (hhpos j) (hh1 j) hp (hmass j)
  constructor
  · apply fin_telescope_bound U _ (p*Real.log ((Fintype.card R : ℝ)/p)) _ (by simpa only [neg_mul] using (hU 0).1) (hU _).2
    intro j
    have hs (r : R) := step_left μ x₀ y₀ l[j.val] C A B hA hA1 hB
      (f (j+1) r) (h j r) (hfRange _ (by omega) r)
      (by rw [← chainLeft_step μ x₀ l F j j.isLt]; exact hfRange _ (by omega) r)
      (hhRange _ (by omega) r)
      (chainLeft_next_local μ x₀ l hN F hFlocal j j.isLt r)
      (chainRight_prev_local μ y₀ l hN H hHlocal j j.isLt r)
      (θ r) (hθ r) (hθL r _ (List.getElem_mem j.isLt)) (hθR r _ (List.getElem_mem j.isLt))
    change _ ≤ (∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (f (j+1) r z)) (h (j+1) r z))) -
      ∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (f j r z)) (h j r z))
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro r _
    have heL : μ.left x₀ l[j.val] (f (j+1) r) = f j r :=
      (chainLeft_step μ x₀ l F j j.isLt r).symm
    have heR : μ.right y₀ l[j.val] (h j r) = h (j+1) r :=
      (chainRight_step μ y₀ l H j j.isLt r).symm
    have hh := hs r
    rw [heL, heR] at hh
    exact hh
  · apply fin_telescope_bound_rev Z _ (p*Real.log ((Fintype.card R : ℝ)/p)) _ (hZ 0).2 (by simpa only [neg_mul] using (hZ _).1)
    intro j
    have hs (r : R) := step_right μ x₀ y₀ l[j.val] C A B hA hB hB1
      (f (j+1) r) (h j r) (hfRange _ (by omega) r) (hhRange _ (by omega) r)
      (by rw [← chainRight_step μ y₀ l H j j.isLt]; exact hhRange _ (by omega) r)
      (chainLeft_next_local μ x₀ l hN F hFlocal j j.isLt r)
      (chainRight_prev_local μ y₀ l hN H hHlocal j j.isLt r)
      (θ r) (hθ r) (hθL r _ (List.getElem_mem j.isLt)) (hθR r _ (List.getElem_mem j.isLt))
    change _ ≤ (∑ r, ρ.avg (fun z => θ r z*prob C (f j r z) (effectEntropy (h j r z)))) -
      ∑ r, ρ.avg (fun z => θ r z*prob C (f (j+1) r z) (effectEntropy (h (j+1) r z)))
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro r _
    have heL : μ.left x₀ l[j.val] (f (j+1) r) = f j r :=
      (chainLeft_step μ x₀ l F j j.isLt r).symm
    have heR : μ.right y₀ l[j.val] (h j r) = h (j+1) r :=
      (chainRight_step μ y₀ l H j j.isLt r).symm
    have hh := hs r
    rw [heL, heR] at hh
    exact hh
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq X] [DecidableEq Y]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def massAt (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (q : X×Y) : ℝ :=
  (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
    prob C (F r (Function.update z i q)) (H r (Function.update z i q)))

omit [Fintype n] [Fintype I] [Fintype R] [DecidableEq X] [DecidableEq n] [DecidableEq m] in
lemma right_update_eq (μ : Law (X×Y)) (y₀ : Y) (i : I)
    (H : Profile I X Y → Matrix n n ℂ) (z : Profile I X Y) (q : X×Y) :
    μ.right y₀ i H (Function.update z i q) =
      (μ.givenFirst y₀ q.1).avg (fun y => H (Function.update z i (q.1,y))) := by
  simp only [right, Function.update_self, updateRight, Function.update_idem]
omit [Fintype m] [Fintype I] [Fintype R] [DecidableEq Y] [DecidableEq n] [DecidableEq m] in
lemma left_update_eq (μ : Law (X×Y)) (x₀ : X) (i : I)
    (F : Profile I X Y → Matrix m m ℂ) (z : Profile I X Y) (q : X×Y) :
    μ.left x₀ i F (Function.update z i q) =
      (μ.givenSecond x₀ q.2).avg (fun x => F (Function.update z i (x,q.2))) := by
  simp only [left, Function.update_self, updateLeft, Function.update_idem]

omit [DecidableEq X] [DecidableEq m] [DecidableEq n] in
lemma massAt_right (μ : Law (X×Y)) (y₀ : Y) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (hF : ∀ r, IgnoresRight (F r) i) (q : X×Y) :
    massAt μ θ p i C F (fun r => μ.right y₀ i (H r)) q =
      (μ.givenFirst y₀ q.1).avg (fun y => massAt μ θ p i C F H (q.1,y)) := by
  unfold massAt
  rw [show (fun y => (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y))))) =
        (fun y => (1/p) • ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y))))) from rfl,
    avg_smul, avg_sum]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [avg_comm]
  congr 1; funext z
  rw [show (fun y => θ r z*prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y)))) =
      (fun y => θ r z • prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y)))) from rfl,
    avg_smul]
  dsimp only
  rw [right_update_eq]
  congr 1
  have he (y : Y) : F r (Function.update z i (q.1,y)) = F r (Function.update z i q) := by
    simpa only [updateRight, Function.update_self, Function.update_idem] using hF r (Function.update z i q) y
  simp_rw [he]
  exact (μ.givenFirst y₀ q.1).avg_linear _ (probRight C (F r (Function.update z i q)))

omit [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
lemma massAt_left (μ : Law (X×Y)) (x₀ : X) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (hH : ∀ r, IgnoresLeft (H r) i) (q : X×Y) :
    massAt μ θ p i C (fun r => μ.left x₀ i (F r)) H q =
      (μ.givenSecond x₀ q.2).avg (fun x => massAt μ θ p i C F H (x,q.2)) := by
  unfold massAt
  rw [show (fun x => (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2))))) =
        (fun x => (1/p) • ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2))))) from rfl,
    avg_smul, avg_sum]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [avg_comm]
  congr 1; funext z
  rw [show (fun x => θ r z*prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2)))) =
      (fun x => θ r z • prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2)))) from rfl,
    avg_smul]
  dsimp only
  rw [left_update_eq]
  congr 1
  have he (x : X) : H r (Function.update z i (x,q.2)) = H r (Function.update z i q) := by
    simpa only [updateLeft, Function.update_self, Function.update_idem] using hH r (Function.update z i q) x
  simp_rw [he]
  exact (μ.givenSecond x₀ q.2).avg_linear _ (probLeft C (H r (Function.update z i q)))
end ThresholdParallelRepetition.MixedExposure

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
section Blocks
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
lemma trace_blockDiagonal (C : R → Matrix m m ℂ) :
    Matrix.trace (Matrix.blockDiagonal C) = ∑ r, Matrix.trace (C r) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.blockDiagonal_apply_eq]
  exact Finset.sum_comm

lemma hsSq_blockDiagonal (C : R → Matrix m n ℂ) :
    hsSq (Matrix.blockDiagonal C) = ∑ r, hsSq (C r) := by
  simp only [hsSq_eq_trace, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    trace_blockDiagonal, Complex.re_sum]

lemma prob_blockDiagonal (C : R → Matrix m n ℂ) (A : R → Matrix m m ℂ)
    (B : R → Matrix n n ℂ) :
    prob (Matrix.blockDiagonal C) (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      ∑ r, prob (C r) (A r) (B r) := by
  simp only [prob, eval_eq_trace, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    Matrix.blockDiagonal_transpose, trace_blockDiagonal, Complex.re_sum]

variable [DecidableEq m]
lemma posSemidef_blockDiagonal (A : R → Matrix m m ℂ) (hA : ∀ r, (A r).PosSemidef) :
    (Matrix.blockDiagonal A).PosSemidef := by
  let B := Matrix.blockDiagonal (fun r => CFC.sqrt (A r))
  have he : Bᴴ*B = Matrix.blockDiagonal A := by
    simp only [B, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext r
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A r))).isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ (hA r).nonneg]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self B

variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq n]
def POVM.blocks (P : R → POVM m A) : POVM (m×R) A where
  effect a := Matrix.blockDiagonal (fun r => (P r).effect a)
  pos a := posSemidef_blockDiagonal _ (fun r => (P r).pos a)
  total := by
    change (∑ a, (Matrix.blockDiagonalAddMonoidHom m m R ℂ) (fun r => (P r).effect a)) = _
    rw [← map_sum]
    have he : (∑ a, fun r => (P r).effect a) = 1 := by
      funext r; simpa only [Finset.sum_apply, Pi.one_apply] using (P r).total
    rw [he]
    exact Matrix.blockDiagonal_one

lemma payoff_blockDiagonal (C : R → Matrix m n ℂ) (P : R → POVM m A) (Q : R → POVM n B)
    (V : A → B → Bool) :
    payoff (Matrix.blockDiagonal C) (POVM.blocks P) (POVM.blocks Q) V =
      ∑ r, payoff (C r) (P r) (Q r) V := by
  simp only [payoff, POVM.blocks, prob_blockDiagonal]
  calc
    _ = ∑ a, ∑ b, ∑ r, if V a b then prob (C r) ((P r).effect a) ((Q r).effect b) else 0 := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      split <;> simp_all
    _ = _ := by
      conv_rhs =>
        rw [Finset.sum_comm]
        arg 2
        ext a
        rw [Finset.sum_comm]
end Blocks

section Normalization
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
lemma hsSq_eq_zero_iff (C : Matrix m n ℂ) : hsSq C = 0 ↔ C = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [norm_eq_sqrt_hsSq, h, Real.sqrt_zero]
  · rintro rfl; exact hsSq_zero

def unitize (C D : Matrix m n ℂ) : Matrix m n ℂ :=
  if hsSq C = 0 then D else (Real.sqrt (hsSq C))⁻¹ • C

lemma hsSq_unitize (C D : Matrix m n ℂ) (hD : hsSq D = 1) : hsSq (unitize C D) = 1 := by
  unfold unitize
  split_ifs with h
  · exact hD
  · rw [hsSq_smul, inv_pow, Real.sq_sqrt (hsSq_nonneg C)]
    exact inv_mul_cancel₀ h

lemma unitize_distance (C D : Matrix m n ℂ) (hD : hsSq D = 1) :
    hsSq (C-unitize C D) = (Real.sqrt (hsSq C)-1)^2 := by
  unfold unitize
  split_ifs with h
  · have hz := (hsSq_eq_zero_iff C).mp h
    simp only [hz, hsSq_zero, Real.sqrt_zero, zero_sub, hsSq_neg, hD]
    norm_num
  · have hs : Real.sqrt (hsSq C) ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne (hsSq_nonneg C) (Ne.symm h))).ne'
    have he : C - (Real.sqrt (hsSq C))⁻¹ • C = (1-(Real.sqrt (hsSq C))⁻¹) • C := by
      rw [sub_smul, one_smul]
    rw [he, hsSq_smul]
    calc
      _ = (1-(Real.sqrt (hsSq C))⁻¹)^2 * (Real.sqrt (hsSq C))^2 := by rw [Real.sq_sqrt (hsSq_nonneg C)]
      _ = _ := by field_simp

lemma hsSq_difference_unbounded (C D : Matrix m n ℂ) (hD : hsSq D ≤ 1) :
    hsSq C - hsSq D ≤ 2*Real.sqrt (hsSq (C-D)) + hsSq (C-D) := by
  have ht : ‖C‖ ≤ ‖D‖ + ‖C-D‖ := by
    simpa only [norm_sub_rev] using norm_le_insert D C
  have hd := hsSq_le_one_norm hD
  have hc0 := norm_nonneg C
  have hd0 := norm_nonneg D
  have he0 := norm_nonneg (C-D)
  have ht2 := sq_le_sq₀ hc0 (add_nonneg hd0 he0) |>.2 ht
  simp only [norm_eq_sqrt_hsSq] at ht2 hd hd0 he0
  have hmul := mul_le_mul_of_nonneg_right hd he0
  rw [Real.sq_sqrt (hsSq_nonneg C)] at ht2
  nlinarith [Real.sq_sqrt (hsSq_nonneg D), Real.sq_sqrt (hsSq_nonneg (C-D))]
end Normalization

section Payoff
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A] [Fintype B]
lemma payoff_difference_unbounded (C D : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) (hD : hsSq D ≤ 1) :
    payoff C P Q V - payoff D P Q V ≤ 2*Real.sqrt (hsSq (C-D)) + hsSq (C-D) := by
  have hsd := (hsSq_mul_contraction (winSqrt_contraction P Q V) (flat D)).trans
    (le_trans (le_of_eq (hsSq_flat D)) hD)
  rw [payoff_eq_hsSq, payoff_eq_hsSq]
  refine (hsSq_difference_unbounded _ _ hsd).trans ?_
  have he : hsSq (CFC.sqrt (winEffect P Q V)*flat C-CFC.sqrt (winEffect P Q V)*flat D) ≤ hsSq (C-D) := by
    rw [← Matrix.mul_sub, ← flat_sub]
    exact (hsSq_mul_contraction (winSqrt_contraction P Q V) _).trans_eq (hsSq_flat _)
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (by norm_num)) he
end Payoff
end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma posSemidef_fromBlocks_diag {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  let T := Matrix.fromBlocks (CFC.sqrt A) (0 : Matrix m n ℂ) 0 (CFC.sqrt B)
  have he : Tᴴ*T = Matrix.fromBlocks A 0 0 B := by
    simp only [T, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq,
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ hA.nonneg, CFC.sqrt_mul_sqrt_self _ hB.nonneg]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self T

def squareState (C : Matrix m n ℂ) : Matrix (m⊕n) (m⊕n) ℂ := Matrix.fromBlocks 0 C 0 0

omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_squareState (C : Matrix m n ℂ) : hsSq (squareState C) = hsSq C := by
  simp only [squareState, hsSq_blocks, hsSq_zero, zero_add, add_zero]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma squareState_sub (C D : Matrix m n ℂ) : squareState (C-D) = squareState C-squareState D := by
  simp only [squareState, fromBlocks_sub, sub_self]

variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B]
def POVM.sum (P : POVM m A) (Q : POVM n A) : POVM (m⊕n) A where
  effect a := Matrix.fromBlocks (P.effect a) 0 0 (Q.effect a)
  pos a := posSemidef_fromBlocks_diag (P.pos a) (Q.pos a)
  total := by
    have he : (∑ a, Matrix.fromBlocks (P.effect a) (0 : Matrix m n ℂ) 0 (Q.effect a)) =
        Matrix.fromBlocks (∑ a, P.effect a) 0 0 (∑ a, Q.effect a) := by
      ext i j
      cases i <;> cases j <;> simp [Matrix.sum_apply]
    rw [he, P.total, Q.total, Matrix.fromBlocks_one]

omit [DecidableEq m] [DecidableEq n] in
lemma prob_squareState (C : Matrix m n ℂ) (A₁ : Matrix m m ℂ) (A₂ : Matrix n n ℂ)
    (B₁ : Matrix m m ℂ) (B₂ : Matrix n n ℂ) :
    prob (squareState C) (Matrix.fromBlocks A₁ 0 0 A₂) (Matrix.fromBlocks B₁ 0 0 B₂) =
      prob C A₁ B₂ := by
  simp only [prob, eval_eq_trace, squareState, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_transpose, Matrix.conjTranspose_zero, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Finset.sum_const_zero, zero_add]

lemma payoff_squareState (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (a₀ : A) (b₀ : B) (V : A → B → Bool) :
    payoff (squareState C) (P.sum (POVM.default a₀)) ((POVM.default b₀).sum Q) V = payoff C P Q V := by
  simp only [payoff, POVM.sum, prob_squareState]
end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law
section Stack
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
def weightedBlock (w : R → ℝ) (C : R → Matrix m n ℂ) : Matrix (m×R) (n×R) ℂ :=
  Matrix.blockDiagonal (fun r => Real.sqrt (w r) • C r)
lemma hsSq_weightedBlock (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C : R → Matrix m n ℂ) :
    hsSq (weightedBlock w C) = ∑ r, w r*hsSq (C r) := by
  simp only [weightedBlock, hsSq_blockDiagonal, hsSq_smul, Real.sq_sqrt (hw _)]
omit [Fintype m] [Fintype n] [Fintype R] in
lemma weightedBlock_sub (w : R → ℝ) (C D : R → Matrix m n ℂ) :
    weightedBlock w (fun r => C r-D r) = weightedBlock w C-weightedBlock w D := by
  simp only [weightedBlock, smul_sub]
  exact Matrix.blockDiagonal_sub _ _
lemma hsSq_weightedBlock_sub (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C D : R → Matrix m n ℂ) :
    hsSq (weightedBlock w C-weightedBlock w D) = ∑ r, w r*hsSq (C r-D r) := by
  rw [← weightedBlock_sub, hsSq_weightedBlock w hw]
variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq m] [DecidableEq n]
lemma payoff_weightedBlock (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C : R → Matrix m n ℂ)
    (P : R → POVM m A) (Q : R → POVM n B) (V : A → B → Bool) :
    payoff (weightedBlock w C) (POVM.blocks P) (POVM.blocks Q) V =
      ∑ r, w r*payoff (C r) (P r) (Q r) V := by
  simp only [weightedBlock, payoff_blockDiagonal, payoff_smul, Real.sq_sqrt (hw _)]
end Stack

lemma correlated_sampling_value_rect {m n : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (M : Fin (x+1) → Matrix m n ℂ) (N : Fin (y+1) → Matrix m n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) := by
  have hh := correlated_sampling_value G (fun x => squareState (M x)) (fun y => squareState (N y))
    (fun x => (hsSq_squareState _).trans (hM x)) (fun y => (hsSq_squareState _).trans (hN y))
    (fun x => (P x).sum (POVM.default 0)) (fun y => (POVM.default 0).sum (Q y)) hε hε1
  simpa only [payoff_squareState, ← squareState_sub, hsSq_squareState] using hh

lemma avg_payoff_difference_unbounded {Z : Type u_Z} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype Z] [Fintype m] [Fintype n]
    [Fintype A] [Fintype B] [DecidableEq m] [DecidableEq n]
    (μ : Law Z) (C D : Z → Matrix m n ℂ) (hD : ∀ z, hsSq (D z) ≤ 1)
    (P : Z → POVM m A) (Q : Z → POVM n B) (V : Z → A → B → Bool) :
    μ.avg (fun z => payoff (C z) (P z) (Q z) (V z)) -
      μ.avg (fun z => payoff (D z) (P z) (Q z) (V z)) ≤
      2*Real.sqrt (μ.avg (fun z => hsSq (C z-D z))) + μ.avg (fun z => hsSq (C z-D z)) := by
  rw [← avg_sub]
  have he := μ.avg_mono (fun z => payoff_difference_unbounded (C z) (D z) (P z) (Q z) (V z) (hD z))
  apply he.trans
  rw [avg_add]
  apply add_le_add _ (le_refl _)
  rw [show (fun z => 2*Real.sqrt (hsSq (C z-D z))) = (fun z => (2:ℝ) • Real.sqrt (hsSq (C z-D z))) from rfl,
    avg_smul]
  exact mul_le_mul_of_nonneg_left (weighted_sqrt_le _ _ μ.nonneg (fun z => hsSq_nonneg _) μ.total) (by norm_num)
end ThresholdParallelRepetition.QuantumSampling

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [DecidableEq I]
lemma ignoresRight_update {f : Profile I X Y → E} {i : I} (hf : IgnoresRight f i)
    (z : Profile I X Y) (x : X) (y y' : Y) :
    f (Function.update z i (x,y)) = f (Function.update z i (x,y')) := by
  simpa [updateRight] using hf (Function.update z i (x,y')) y
lemma ignoresLeft_update {f : Profile I X Y → E} {i : I} (hf : IgnoresLeft f i)
    (z : Profile I X Y) (x x' : X) (y : Y) :
    f (Function.update z i (x,y)) = f (Function.update z i (x',y)) := by
  simpa [updateLeft] using hf (Function.update z i (x',y)) x
lemma ignores_update {f : Profile I X Y → E} {i : I} (hL : IgnoresLeft f i) (hR : IgnoresRight f i)
    (z : Profile I X Y) (q : X×Y) : f (Function.update z i q) = f z := by
  obtain ⟨x,y⟩ := q
  rw [ignoresRight_update hR z x y (z i).2]
  exact hL z x
end ThresholdParallelRepetition.FiniteProbability.Law
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [DecidableEq X] [DecidableEq Y]
omit [DecidableEq R] [DecidableEq X] [DecidableEq Y] in
lemma fresh_avg_weighted (μ : Law (X×Y)) (i : I) (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r, IgnoresLeft (θ r) i) (hθR : ∀ r, IgnoresRight (θ r) i)
    (g : R → Profile I X Y → ℝ) :
    μ.avg (fun q => ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*g r (Function.update z i q))) =
      ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*g r z) := by
  rw [avg_sum]
  apply Finset.sum_congr rfl; intro r _
  have he : (fun q => (pi (fun _ : I => μ)).avg (fun z => θ r z*g r (Function.update z i q))) =
      (fun q => (pi (fun _ : I => μ)).avg (fun z => θ r (Function.update z i q)*g r (Function.update z i q))) := by
    funext q
    congr 1
    funext z
    rw [ignores_update (hθL r) (hθR r)]
  rw [he, avg_comm]
  exact pi_avg_update _ i (fun z => θ r z*g r z)

variable {m : Type u_m} {n : Type u_n} {u : Type u_u} {v : Type u_v} [Fintype m] [Fintype n] [Fintype u] [Fintype v]
def stateAt (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    Matrix (u×(R×Profile I X Y)) (v×(R×Profile I X Y)) ℂ :=
  weightedBlock (fun t : R×Profile I X Y => (pi (fun _ : I => μ)).weight t.2 * θ t.1 t.2 / p)
    (fun t => U t.1 (Function.update t.2 i q)*C*(V t.1 (Function.update t.2 i q))ᵀ)

lemma stateAt_norm (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q) = (1/p)*∑ r, (pi (fun _ : I => μ)).avg
      (fun z => θ r z * hsSq (U r (Function.update z i q)*C*(V r (Function.update z i q))ᵀ)) := by
  rw [stateAt, hsSq_weightedBlock _ (fun t => div_nonneg (mul_nonneg ((pi _).nonneg _) (hθ _ _)) hp.le),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  simp only [avg, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  ring

lemma stateAt_distance_left (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U U' : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q-stateAt μ θ p i C U' V q) =
      (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
        ((U r (Function.update z i q)-U' r (Function.update z i q))*C*(V r (Function.update z i q))ᵀ)) := by
  simp only [stateAt]
  rw [hsSq_weightedBlock_sub _ (fun t => div_nonneg (mul_nonneg ((pi _).nonneg _) (hθ _ _)) hp.le),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  simp only [avg, smul_eq_mul, Finset.mul_sum, Matrix.sub_mul]
  apply Finset.sum_congr rfl; intro z _
  ring

lemma stateAt_distance_right (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V V' : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q-stateAt μ θ p i C U V' q) =
      (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
        (U r (Function.update z i q)*C*(V r (Function.update z i q)-V' r (Function.update z i q))ᵀ)) := by
  simp only [stateAt]
  rw [hsSq_weightedBlock_sub _ (fun t => div_nonneg (mul_nonneg ((pi _).nonneg _) (hθ _ _)) hp.le),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  simp only [avg, smul_eq_mul, Finset.mul_sum, Matrix.transpose_sub, Matrix.mul_sub]
  apply Finset.sum_congr rfl; intro z _
  ring
omit [Fintype R] [Fintype u] [Fintype v] in
lemma stateAt_right_local (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ)
    (hU : ∀ r, IgnoresRight (U r) i) (hV : ∀ r, IgnoresRight (V r) i)
    (x : X) (y y' : Y) : stateAt μ θ p i C U V (x,y) = stateAt μ θ p i C U V (x,y') := by
  unfold stateAt
  congr 1
  funext t
  rw [ignoresRight_update (hU t.1) t.2 x y y', ignoresRight_update (hV t.1) t.2 x y y']

omit [Fintype R] [Fintype u] [Fintype v] in
lemma stateAt_left_local (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ)
    (hU : ∀ r, IgnoresLeft (U r) i) (hV : ∀ r, IgnoresLeft (V r) i)
    (x x' : X) (y : Y) : stateAt μ θ p i C U V (x,y) = stateAt μ θ p i C U V (x',y) := by
  unfold stateAt
  congr 1
  funext t
  rw [ignoresLeft_update (hU t.1) t.2 x x' y, ignoresLeft_update (hV t.1) t.2 x x' y]

variable [DecidableEq m] [DecidableEq n] [DecidableEq u] [DecidableEq v]
omit [DecidableEq m] [DecidableEq n] in
lemma stateAt_norm_gram (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hU : ∀ r z, (U r z)ᴴ*U r z=F r z) (hV : ∀ r z, (V r z)ᴴ*V r z=H r z) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q) = (1/p)*∑ r, (pi (fun _ : I => μ)).avg
      (fun z => θ r z*prob C (F r (Function.update z i q)) (H r (Function.update z i q))) := by
  rw [stateAt_norm μ θ hθ hp]
  simp only [← prob_gram, hU, hV]
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
lemma chain_fixed_mass (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r i, IgnoresRight (F r) i) (hH : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    (p : ℝ) (j : Fin l.length) (q : X×Y) :
    massAt μ θ p l[j.val] C (chainLeft μ x₀ l F (j+1)) (chainRight μ y₀ l H j) q =
      massAt μ θ p l[j.val] C F H q := by
  unfold massAt
  congr 1
  apply Finset.sum_congr rfl; intro r _
  have hθi (z : Profile I X Y) : θ r (Function.update z l[j.val] q) = θ r z :=
    ignores_update (hθL r _ (List.getElem_mem j.isLt)) (hθR r _ (List.getElem_mem j.isLt)) z q
  have he (G : Profile I X Y → ℝ) :
      (pi (fun _ : I => μ)).avg (fun z => θ r z*G (Function.update z l[j.val] q)) =
      (pi (fun _ : I => μ)).avg (fun z => θ r (Function.update z l[j.val] q)*G (Function.update z l[j.val] q)) := by
    simp only [hθi]
  rw [he (fun z => prob C (chainLeft μ x₀ l F (j+1) r z) (chainRight μ y₀ l H j r z)),
    he (fun z => prob C (F r z) (H r z))]
  apply fixed_mixed_pairing μ x₀ y₀ _ _ _ C (F r) (H r)
    (fun i _ => hF r i) (fun i _ => hH r i) (θ r)
    (fun i hi => hθL r i (List.mem_of_mem_drop hi))
    (fun i hi => hθR r i (List.mem_of_mem_take (List.mem_reverse.mp hi)))
    l[j.val] (list_fresh_not_suffix l hN j j.isLt) (list_fresh_not_prefix l hN j j.isLt) q
  intro i hi
  exact list_suffix_prefix_disjoint l hN j i (List.drop_subset_drop_left l (Nat.le_succ j) hi)

def eventDensity (θ : R → Profile I X Y → ℝ) (p : ℝ) (C : Matrix m n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (z : Profile I X Y) : ℝ := (1/p)*∑ r, θ r z*prob C (F r z) (H r z)

omit [DecidableEq X] [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
lemma massAt_eq_coordDensity (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (i : I)
    (hθL : ∀ r, IgnoresLeft (θ r) i) (hθR : ∀ r, IgnoresRight (θ r) i) (q : X×Y) :
    massAt μ θ p i C F H q = coordDensity (fun _ : I => μ) (eventDensity θ p C F H) i q := by
  unfold massAt coordDensity eventDensity
  simp only [ignores_update (hθL _) (hθR _)]
  rw [show (fun z => (1/p)*∑ r, θ r z*prob C (F r (Function.update z i q)) (H r (Function.update z i q))) =
    (fun z => (1/p) • ∑ r, θ r z*prob C (F r (Function.update z i q)) (H r (Function.update z i q))) from rfl,
    avg_smul, avg_sum]
  rfl

omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] [DecidableEq I] [DecidableEq m] [DecidableEq n] in
lemma eventDensity_nonneg (θ : R → Profile I X Y → ℝ) (hθ : ∀ r z, 0 ≤ θ r z)
    {p : ℝ} (hp : 0 < p) (C : Matrix m n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hH : ∀ r z, (H r z).PosSemidef) (z : Profile I X Y) :
    0 ≤ eventDensity θ p C F H z :=
  mul_nonneg (div_nonneg zero_le_one hp.le)
    (Finset.sum_nonneg (fun r _ => mul_nonneg (hθ r z) (prob_nonneg (hF r z) (hH r z))))

omit [DecidableEq X] [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
lemma eventDensity_total (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    {p : ℝ} (hp : 0 < p) (C : Matrix m n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hm : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*prob C (F r z) (H r z))) = p) :
    (pi (fun _ : I => μ)).avg (eventDensity θ p C F H) = 1 := by
  change (pi (fun _ : I => μ)).avg (fun z => (1/p) • ∑ r, θ r z*prob C (F r z) (H r z)) = 1
  rw [avg_smul, avg_sum, hm, smul_eq_mul, one_div, inv_mul_cancel₀ hp.ne']
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law ScalarEntropy
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def basisState (i : m) (j : n) : Matrix m n ℂ := fun a b => if a=i ∧ b=j then 1 else 0
lemma hsSq_basisState (i : m) (j : n) : hsSq (basisState i j) = 1 := by
  have he : basisState i j = fun a b => if a=i then (if b=j then 1 else 0) else 0 := by
    ext a b
    by_cases h : a=i <;> simp [basisState, h]
  rw [he]
  simp [hsSq, apply_ite]

omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_triangle (C D E : Matrix m n ℂ) : hsSq (C-E) ≤ 2*(hsSq (C-D)+hsSq (D-E)) := by
  have h := hsSq_add_le (C-D) (D-E)
  simpa only [sub_add_sub_cancel] using h

omit [DecidableEq m] [DecidableEq n] in
lemma avg_unitize_triangle {Z : Type u_Z} [Fintype Z] (μ : Law Z)
    (C D : Z → Matrix m n ℂ) (E : Matrix m n ℂ) :
    μ.avg (fun z => hsSq (C z-unitize (D z) E)) ≤
      2*(μ.avg (fun z => hsSq (C z-D z))+μ.avg (fun z => hsSq (D z-unitize (D z) E))) := by
  have h := μ.avg_mono (fun z => hsSq_triangle (C z) (D z) (unitize (D z) E))
  apply h.trans_eq
  change μ.avg (fun z => (2:ℝ) • (hsSq (C z-D z)+hsSq (D z-unitize (D z) E))) = _
  rw [avg_smul, avg_add]
  rfl

variable {X : Type u_X} {Y : Type u_Y} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
omit [DecidableEq m] [DecidableEq n] [DecidableEq X] in
lemma first_unitize_cost (μ : Law (X×Y)) (y₀ : Y) (f : X×Y → ℝ)
    (hf : ∀ z, 0 ≤ f z) (ht : μ.avg f = 1) (M : X → Matrix m n ℂ)
    (hM : ∀ x, hsSq (M x) = (μ.givenFirst y₀ x).avg (fun y => f (x,y)))
    (E : Matrix m n ℂ) (hE : hsSq E = 1) :
    μ.avg (fun z => hsSq (M z.1-unitize (M z.1) E)) ≤ μ.avg (fun z => f z*Real.log (f z)) := by
  rw [disintegrate_first μ y₀]
  simp only [avg_const, unitize_distance _ _ hE, hM]
  have hmean : μ.first.avg (fun x => (μ.givenFirst y₀ x).avg (fun y => f (x,y))) = 1 := by
    rw [← disintegrate_first]; exact ht
  exact (avg_hellinger_le_entropy μ.first _ (fun x => (μ.givenFirst y₀ x).avg_nonneg (fun y => hf (x,y))) hmean).trans
    (first_density_entropy_le μ y₀ f hf)

omit [DecidableEq m] [DecidableEq n] [DecidableEq Y] in
lemma second_unitize_cost (μ : Law (X×Y)) (x₀ : X) (f : X×Y → ℝ)
    (hf : ∀ z, 0 ≤ f z) (ht : μ.avg f = 1) (N : Y → Matrix m n ℂ)
    (hN : ∀ y, hsSq (N y) = (μ.givenSecond x₀ y).avg (fun x => f (x,y)))
    (E : Matrix m n ℂ) (hE : hsSq E = 1) :
    μ.avg (fun z => hsSq (N z.2-unitize (N z.2) E)) ≤ μ.avg (fun z => f z*Real.log (f z)) := by
  rw [disintegrate_second μ x₀]
  simp only [avg_const, unitize_distance _ _ hE, hN]
  have hmean : μ.second.avg (fun y => (μ.givenSecond x₀ y).avg (fun x => f (x,y))) = 1 := by
    rw [← disintegrate_second]; exact ht
  exact (avg_hellinger_le_entropy μ.second _ (fun y => (μ.givenSecond x₀ y).avg_nonneg (fun x => hf (x,y))) hmean).trans
    (second_density_entropy_le μ x₀ f hf)
end ThresholdParallelRepetition.QuantumSampling

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable (X : Type u_X) (Y : Type u_Y) (I : Type u_I) (R : Type u_R) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

structure EventSystem where
  μ : Law (X×Y)
  x₀ : X
  y₀ : Y
  l : List I
  nodup : l.Nodup
  C : Matrix m n ℂ
  hC : hsSq C = 1
  F : R → Profile I X Y → Matrix m m ℂ
  H : R → Profile I X Y → Matrix n n ℂ
  hF : ∀ r z, (F r z).PosSemidef
  hF1 : ∀ r z, F r z ≤ 1
  hH : ∀ r z, (H r z).PosSemidef
  hH1 : ∀ r z, H r z ≤ 1
  localF : ∀ r i, IgnoresRight (F r) i
  localH : ∀ r i, IgnoresLeft (H r) i
  θ : R → Profile I X Y → ℝ
  hθ : ∀ r z, 0 ≤ θ r z
  hθ1 : ∀ r z, θ r z ≤ 1
  localθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i
  localθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i
  event_le_one : ∀ z, (∑ r, θ r z*prob C (F r z) (H r z)) ≤ 1
  p : ℝ
  hp : 0 < p
  mass : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*prob C (F r z) (H r z))) = p

variable {X Y I R m n} [Nonempty X] [Nonempty Y] [Nonempty R]
namespace EventSystem
variable (S : EventSystem X Y I R m n)
abbrev J := ExposureIndex (R := R) (X := X) (Y := Y) S.l
abbrev f := chainLeft S.μ S.x₀ S.l S.F
abbrev h := chainRight S.μ S.y₀ S.l S.H
abbrev A := chainLeftFamily S.μ S.x₀ S.l S.F
abbrev B := chainRightFamily S.μ S.y₀ S.l S.H

def U (j : ℕ) (r : R) (z : Profile I X Y) : Matrix (S.J×m) m ℂ := commonMap S.A (S.f j r z)
def V (j : ℕ) (r : R) (z : Profile I X Y) : Matrix (S.J×n) n ℂ := commonMap S.B (S.h j r z)

omit [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma f_pos (j : ℕ) (r : R) (z : Profile I X Y) : (S.f j r z).PosSemidef :=
  lefts_posSemidef S.μ S.x₀ _ _ (S.hF r) z
omit [DecidableEq X] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma h_pos (j : ℕ) (r : R) (z : Profile I X Y) : (S.h j r z).PosSemidef :=
  rights_posSemidef S.μ S.y₀ _ _ (S.hH r) z
lemma U_gram {j : ℕ} (hj : j ≤ S.l.length) (r : R) (z : Profile I X Y) :
    (S.U j r z)ᴴ*S.U j r z = S.f j r z :=
  commonMap_gram S.A (fun t => S.f_pos _ _ _) ⟨(⟨j, by omega⟩,r,z),rfl⟩
lemma V_gram {j : ℕ} (hj : j ≤ S.l.length) (r : R) (z : Profile I X Y) :
    (S.V j r z)ᴴ*S.V j r z = S.h j r z :=
  commonMap_gram S.B (fun t => S.h_pos _ _ _) ⟨(⟨j, by omega⟩,r,z),rfl⟩

def D (j : Fin S.l.length) : X×Y → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V j)
def rawA (j : Fin S.l.length) : X → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  fun x => stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V (j+1)) (x,S.y₀)
def rawB (j : Fin S.l.length) : Y → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  fun y => stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U j) (S.V j) (S.x₀,y)

lemma rawA_eq (j : Fin S.l.length) (q : X×Y) : S.rawA j q.1 =
    stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V (j+1)) q := by
  apply stateAt_right_local
  · intro r z y
    exact congrArg (commonMap S.A) (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt r z y)
  · intro r z y
    apply congrArg (commonMap S.B)
    rw [h, chainRight_step S.μ S.y₀ S.l S.H j j.isLt r]
    exact right_ignoresRight S.μ S.y₀ _ _ z y
lemma rawB_eq (j : Fin S.l.length) (q : X×Y) : S.rawB j q.2 =
    stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U j) (S.V j) q := by
  apply stateAt_left_local
  · intro r z x
    apply congrArg (commonMap S.A)
    rw [f, chainLeft_step S.μ S.x₀ S.l S.F j j.isLt r]
    exact left_ignoresLeft S.μ S.x₀ _ _ z x
  · intro r z x
    exact congrArg (commonMap S.B) (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt r z x)

def density : Profile I X Y → ℝ := eventDensity S.θ S.p S.C S.F S.H
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_nonneg : ∀ z, 0 ≤ S.density z := eventDensity_nonneg S.θ S.hθ S.hp S.C S.F S.H S.hF S.hH
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_total : (pi (fun _ : I => S.μ)).avg S.density = 1 :=
  eventDensity_total S.μ S.θ S.hp S.C S.F S.H S.mass
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_le (z : Profile I X Y) : S.density z ≤ 1/S.p := by
  exact (mul_le_mul_of_nonneg_left (S.event_le_one z) (div_nonneg zero_le_one S.hp.le)).trans_eq (mul_one _)

lemma D_norm (j : Fin S.l.length) (q : X×Y) : hsSq (S.D j q) = coordDensity (fun _ : I => S.μ) S.density S.l[j.val] q := by
  rw [D, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  change massAt S.μ S.θ S.p S.l[j.val] S.C (S.f (j+1)) (S.h j) q = _
  rw [chain_fixed_mass S.μ S.x₀ S.y₀ S.l S.nodup S.C S.F S.H S.localF S.localH S.θ S.localθL S.localθR]
  exact massAt_eq_coordDensity S.μ S.θ S.p S.C S.F S.H _
    (fun r => S.localθL r _ (List.getElem_mem j.isLt)) (fun r => S.localθR r _ (List.getElem_mem j.isLt)) q

lemma rawA_norm (j : Fin S.l.length) (x : X) : hsSq (S.rawA j x) =
    (S.μ.givenFirst S.y₀ x).avg (fun y => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] (x,y)) := by
  rw [rawA, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h (j+1))
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  change massAt S.μ S.θ S.p S.l[j.val] S.C (S.f (j+1)) (S.h (j+1)) (x,S.y₀) = _
  have he : S.h (j+1) = fun r => S.μ.right S.y₀ S.l[j.val] (S.h j r) := by
    funext r; exact chainRight_step S.μ S.y₀ S.l S.H j j.isLt r
  rw [he, massAt_right S.μ S.y₀ S.θ S.p _ S.C _ _
    (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt)]
  congr 1; funext y
  rw [← S.D_norm j (x,y), D, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  rfl
lemma rawB_norm (j : Fin S.l.length) (y : Y) : hsSq (S.rawB j y) =
    (S.μ.givenSecond S.x₀ y).avg (fun x => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] (x,y)) := by
  rw [rawB, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f j) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  change massAt S.μ S.θ S.p S.l[j.val] S.C (S.f j) (S.h j) (S.x₀,y) = _
  have he : S.f j = fun r => S.μ.left S.x₀ S.l[j.val] (S.f (j+1) r) := by
    funext r; exact chainLeft_step S.μ S.x₀ S.l S.F j j.isLt r
  rw [he, massAt_left S.μ S.x₀ S.θ S.p _ S.C _ _
    (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt)]
  congr 1; funext x
  rw [← S.D_norm j (x,y), D, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  rfl
end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law MeasurementTransport
namespace QuantumSampling.POVM
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]
def transport (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ*F) (a₀ : A) : POVM m A where
  effect := transportedEffect F G a₀
  pos := transportedEffect_pos F G hG a₀
  total := transportedEffect_sum F G hGT a₀
lemma transport_pullback (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ*F) (a₀ a : A) :
    Fᴴ*(transport F G hG hGT a₀).effect a*F = G a :=
  transportedEffect_pullback F G hG hGT a₀ a
end QuantumSampling.POVM
namespace MixedExposure
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

structure Refinement (S : EventSystem X Y I R m n) (A : Type u_A) (B : Type u_B) [Fintype A] [Fintype B] where
  left : I → R → Profile I X Y → A → Matrix m m ℂ
  right : I → R → Profile I X Y → B → Matrix n n ℂ
  left_pos : ∀ i r z a, (left i r z a).PosSemidef
  right_pos : ∀ i r z b, (right i r z b).PosSemidef
  left_total : ∀ i r z, ∑ a, left i r z a = S.F r z
  right_total : ∀ i r z, ∑ b, right i r z b = S.H r z
  left_local : ∀ i r a j, IgnoresRight (fun z => left i r z a) j
  right_local : ∀ i r b j, IgnoresLeft (fun z => right i r z b) j
namespace Refinement
variable {S : EventSystem X Y I R m n} (T : Refinement S A B)
def leftFine (j : Fin S.l.length) (r : R) (z : Profile I X Y) (a : A) : Matrix m m ℂ :=
  S.μ.lefts S.x₀ (S.l.drop (j+1)) (fun z => T.left S.l[j.val] r z a) z
def rightFine (j : Fin S.l.length) (r : R) (z : Profile I X Y) (b : B) : Matrix n n ℂ :=
  S.μ.rights S.y₀ (S.l.take j).reverse (fun z => T.right S.l[j.val] r z b) z
omit [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma leftFine_pos (j : Fin S.l.length) (r : R) (z : Profile I X Y) (a : A) : (T.leftFine j r z a).PosSemidef :=
  lefts_posSemidef S.μ S.x₀ _ _ (fun z => T.left_pos _ r z a) z
omit [DecidableEq X] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma rightFine_pos (j : Fin S.l.length) (r : R) (z : Profile I X Y) (b : B) : (T.rightFine j r z b).PosSemidef :=
  rights_posSemidef S.μ S.y₀ _ _ (fun z => T.right_pos _ r z b) z
omit [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma leftFine_total (j : Fin S.l.length) (r : R) (z : Profile I X Y) :
    ∑ a, T.leftFine j r z a = S.f (j+1) r z := by
  simp only [leftFine]
  rw [← lefts_sum]
  simp only [T.left_total]
  rfl
omit [DecidableEq X] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma rightFine_total (j : Fin S.l.length) (r : R) (z : Profile I X Y) :
    ∑ b, T.rightFine j r z b = S.h j r z := by
  simp only [rightFine]
  rw [← rights_sum]
  simp only [T.right_total]
  rfl
omit [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma leftFine_local (j : Fin S.l.length) (r : R) (a : A) : IgnoresRight (fun z => T.leftFine j r z a) S.l[j.val] :=
  lefts_ignoresRight_notMem S.μ S.x₀ _ (list_fresh_not_suffix S.l S.nodup j j.isLt) (T.left_local _ r a _)
omit [DecidableEq X] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma rightFine_local (j : Fin S.l.length) (r : R) (b : B) : IgnoresLeft (fun z => T.rightFine j r z b) S.l[j.val] :=
  rights_ignoresLeft_notMem S.μ S.y₀ _ (list_fresh_not_prefix S.l S.nodup j j.isLt) (T.right_local _ r b _)

def leftPOVM (a₀ : A) (j : Fin S.l.length) (r : R) (z : Profile I X Y) : POVM (S.J×m) A :=
  POVM.transport (S.U (j+1) r z) (T.leftFine j r z) (T.leftFine_pos j r z)
    ((T.leftFine_total j r z).trans (S.U_gram (by omega) r z).symm) a₀
def rightPOVM (b₀ : B) (j : Fin S.l.length) (r : R) (z : Profile I X Y) : POVM (S.J×n) B :=
  POVM.transport (S.V j r z) (T.rightFine j r z) (T.rightFine_pos j r z)
    ((T.rightFine_total j r z).trans (S.V_gram (by omega) r z).symm) b₀

omit [DecidableEq B] in
lemma leftPOVM_local (a₀ : A) (j : Fin S.l.length) (r : R) : IgnoresRight (T.leftPOVM a₀ j r) S.l[j.val] := by
  intro z y
  have hU : S.U (j+1) r (updateRight z S.l[j.val] y) = S.U (j+1) r z :=
    congrArg (commonMap S.A) (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt r z y)
  have hF : T.leftFine j r (updateRight z S.l[j.val] y) = T.leftFine j r z := by
    funext a; exact T.leftFine_local j r a z y
  simp only [leftPOVM, hU, hF]
omit [DecidableEq A] in
lemma rightPOVM_local (b₀ : B) (j : Fin S.l.length) (r : R) : IgnoresLeft (T.rightPOVM b₀ j r) S.l[j.val] := by
  intro z x
  have hV : S.V j r (updateLeft z S.l[j.val] x) = S.V j r z :=
    congrArg (commonMap S.B) (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt r z x)
  have hH : T.rightFine j r (updateLeft z S.l[j.val] x) = T.rightFine j r z := by
    funext b; exact T.rightFine_local j r b z x
  simp only [rightPOVM, hV, hH]

instance coherentDecEq (l : List I) : DecidableEq (((ExposureIndex (R := R) (X := X) (Y := Y) l)×m)×(R×Profile I X Y)) :=
  @instDecidableEqProd _ _ (inferInstance : DecidableEq ((ExposureIndex (R := R) (X := X) (Y := Y) l)×m))
    (inferInstance : DecidableEq (R×Profile I X Y))

def P (a₀ : A) (j : Fin S.l.length) (x : X) : POVM ((S.J×m)×(R×Profile I X Y)) A := by
  classical
  exact POVM.blocks (fun t : R×Profile I X Y => T.leftPOVM a₀ j t.1 (Function.update t.2 S.l[j.val] (x,S.y₀)))
def Q (b₀ : B) (j : Fin S.l.length) (y : Y) : POVM ((S.J×n)×(R×Profile I X Y)) B := by
  classical
  exact POVM.blocks (fun t : R×Profile I X Y => T.rightPOVM b₀ j t.1 (Function.update t.2 S.l[j.val] (S.x₀,y)))

omit [DecidableEq B] in
lemma P_effect (a₀ : A) (j : Fin S.l.length) (q : X×Y) (a : A) :
    (T.P a₀ j q.1).effect a =
      Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.leftPOVM a₀ j t.1 (Function.update t.2 S.l[j.val] q)).effect a) := by
  change Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.leftPOVM a₀ j t.1 (Function.update t.2 S.l[j.val] (q.1,S.y₀))).effect a) = _
  apply congrArg Matrix.blockDiagonal
  funext t
  rw [ignoresRight_update (T.leftPOVM_local a₀ j t.1) t.2 q.1 S.y₀ q.2]
omit [DecidableEq A] in
lemma Q_effect (b₀ : B) (j : Fin S.l.length) (q : X×Y) (b : B) :
    (T.Q b₀ j q.2).effect b =
      Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.rightPOVM b₀ j t.1 (Function.update t.2 S.l[j.val] q)).effect b) := by
  change Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.rightPOVM b₀ j t.1 (Function.update t.2 S.l[j.val] (S.x₀,q.2))).effect b) = _
  apply congrArg Matrix.blockDiagonal
  funext t
  rw [ignoresLeft_update (T.rightPOVM_local b₀ j t.1) t.2 S.x₀ q.1 q.2]

lemma transported_prob (a₀ : A) (b₀ : B) (j : Fin S.l.length) (r : R) (z : Profile I X Y) (a : A) (b : B) :
    prob (S.U (j+1) r z*S.C*(S.V j r z)ᵀ) ((T.leftPOVM a₀ j r z).effect a) ((T.rightPOVM b₀ j r z).effect b) =
      prob S.C (T.leftFine j r z a) (T.rightFine j r z b) := by
  rw [← prob_pullback]
  simp only [leftPOVM, rightPOVM, POVM.transport_pullback]
end Refinement
end MixedExposure
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law MeasurementTransport
namespace QuantumSampling
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
lemma prob_weightedBlock (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C : R → Matrix m n ℂ)
    (P : R → Matrix m m ℂ) (Q : R → Matrix n n ℂ) :
    prob (weightedBlock w C) (Matrix.blockDiagonal P) (Matrix.blockDiagonal Q) = ∑ r, w r*prob (C r) (P r) (Q r) := by
  simp only [weightedBlock, prob_blockDiagonal, prob_smul, Real.sq_sqrt (hw _)]
end QuantumSampling
namespace MixedExposure
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
namespace Refinement
variable {S : EventSystem X Y I R m n} (T : Refinement S A B)

lemma prob_D (a₀ : A) (b₀ : B) (j : Fin S.l.length) (q : X×Y) (a : A) (b : B) :
    prob (S.D j q) ((T.P a₀ j q.1).effect a) ((T.Q b₀ j q.2).effect b) =
      massAt S.μ S.θ S.p S.l[j.val] S.C (fun r z => T.left S.l[j.val] r z a) (fun r z => T.right S.l[j.val] r z b) q := by
  rw [T.P_effect a₀ j q a, T.Q_effect b₀ j q b]
  simp only [EventSystem.D, stateAt]
  rw [prob_weightedBlock (fun t : R×Profile I X Y => (pi (fun _ : I => S.μ)).weight t.2*S.θ t.1 t.2/S.p)
    (fun t => div_nonneg (mul_nonneg ((pi (fun _ : I => S.μ)).nonneg t.2) (S.hθ t.1 t.2)) S.hp.le)]
  simp only [T.transported_prob, Fintype.sum_prod_type]
  have he : (∑ r, ∑ z, (pi (fun _ : I => S.μ)).weight z*S.θ r z/S.p *
      prob S.C (T.leftFine j r (Function.update z S.l[j.val] q) a) (T.rightFine j r (Function.update z S.l[j.val] q) b)) =
      massAt S.μ S.θ S.p S.l[j.val] S.C
        (chainLeft S.μ S.x₀ S.l (fun r z => T.left S.l[j.val] r z a) (j+1))
        (chainRight S.μ S.y₀ S.l (fun r z => T.right S.l[j.val] r z b) j) q := by
    unfold massAt
    simp only [avg, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro z _
    change _ = (1/S.p)*((pi (fun _ : I => S.μ)).weight z*(_*_))
    simp only [leftFine, rightFine, chainLeft, chainRight]
    ring
  rw [he]
  exact chain_fixed_mass S.μ S.x₀ S.y₀ S.l S.nodup S.C _ _
    (fun r i => T.left_local _ r a i) (fun r i => T.right_local _ r b i)
    S.θ S.localθL S.localθR S.p j q

def score (i : I) (V : X → Y → A → B → Bool) : ℝ :=
  (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
    ∑ a, ∑ b, if V (z i).1 (z i).2 a b then prob S.C (T.left i r z a) (T.right i r z b) else 0)

omit [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] in
lemma avg_if_massAt (i : I) (hi : i ∈ S.l) (V : X×Y → Bool)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ) :
    S.μ.avg (fun q => if V q then massAt S.μ S.θ S.p i S.C F H q else 0) =
      (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
        (if V (z i) then prob S.C (F r z) (H r z) else 0)) := by
  have he : (fun q => if V q then massAt S.μ S.θ S.p i S.C F H q else 0) =
      (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
        (if V ((Function.update z i q) i) then prob S.C (F r (Function.update z i q)) (H r (Function.update z i q)) else 0))) := by
    funext q
    simp only [Function.update_self]
    split <;> simp_all [massAt, avg, smul_eq_mul]
  rw [he, avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ i S.θ
    (fun r => S.localθL r i hi) (fun r => S.localθR r i hi)
    (fun r z => if V (z i) then prob S.C (F r z) (H r z) else 0)

lemma payoff_D_eq_score (a₀ : A) (b₀ : B) (j : Fin S.l.length) (V : X → Y → A → B → Bool) :
    S.μ.avg (fun q => payoff (S.D j q) (T.P a₀ j q.1) (T.Q b₀ j q.2) (V q.1 q.2)) = T.score S.l[j.val] V := by
  simp only [payoff, T.prob_D, avg_sum]
  simp only [avg_if_massAt (S := S) S.l[j.val] (List.getElem_mem j.isLt)]
  unfold score
  simp only [Finset.mul_sum, avg_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Refinement
end MixedExposure
end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {I : Type u_I} {Z : Type u_Z} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]
omit [DecidableEq Z] in
lemma coord_entropy_nonneg (q : I → Law Z) (f : (I → Z) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : I) :
    0 ≤ (q i).avg (fun z => coordDensity q f i z*Real.log (coordDensity q f i z)) := by
  rw [← kl_tilt (q i) _ (coordDensity_nonneg q f hf i) (coordDensity_total q f ht i)]
  exact kl_nonneg _ _ (tilt_supports _ _ _ _)

lemma list_coord_entropy_sum_le (q : I → Law Z) (f : (I → Z) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (l : List I) (hN : l.Nodup) :
    (∑ j : Fin l.length, (q l[j.val]).avg (fun z => coordDensity q f l[j.val] z*Real.log (coordDensity q f l[j.val] z))) ≤
      (pi q).avg (fun z => f z*Real.log (f z)) := by
  let g : I → ℝ := fun i => (q i).avg (fun z => coordDensity q f i z*Real.log (coordDensity q f i z))
  have hi : Function.Injective (fun j : Fin l.length => l[j.val]) := by
    intro i j h
    apply hN.get_inj_iff.mp
    simpa only [List.get_eq_getElem] using h
  have hs : (∑ j : Fin l.length, g l[j.val]) ≤ ∑ i, g i := by
    rw [← Finset.sum_image (f := g) (s := Finset.univ) (Set.injOn_of_injective hi)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => coord_entropy_nonneg q f hf ht i)
  exact hs.trans (coord_entropy_sum_le q f hf ht)
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
namespace EventSystem
variable (S : EventSystem X Y I R m n)

lemma rawA_error_eq (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1)) =
    (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      (S.U (j+1) r z*S.C*(S.V j r z-S.V (j+1) r z)ᵀ)) := by
  simp only [S.rawA_eq, D, stateAt_distance_right S.μ S.θ S.hθ S.hp]
  change S.μ.avg (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      (S.U (j+1) r (Function.update z S.l[j.val] q)*S.C*
        (S.V j r (Function.update z S.l[j.val] q)-S.V (j+1) r (Function.update z S.l[j.val] q))ᵀ))) = _
  rw [avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ _ S.θ
    (fun r => S.localθL r _ (List.getElem_mem j.isLt)) (fun r => S.localθR r _ (List.getElem_mem j.isLt))
    (fun r z => hsSq (S.U (j+1) r z*S.C*(S.V j r z-S.V (j+1) r z)ᵀ))
lemma rawB_error_eq (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.D j q-S.rawB j q.2)) =
    (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      ((S.U (j+1) r z-S.U j r z)*S.C*(S.V j r z)ᵀ)) := by
  simp only [S.rawB_eq, D, stateAt_distance_left S.μ S.θ S.hθ S.hp]
  change S.μ.avg (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      ((S.U (j+1) r (Function.update z S.l[j.val] q)-S.U j r (Function.update z S.l[j.val] q))*S.C*
        (S.V j r (Function.update z S.l[j.val] q))ᵀ))) = _
  rw [avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ _ S.θ
    (fun r => S.localθL r _ (List.getElem_mem j.isLt)) (fun r => S.localθR r _ (List.getElem_mem j.isLt))
    (fun r z => hsSq ((S.U (j+1) r z-S.U j r z)*S.C*(S.V j r z)ᵀ))

lemma raw_error_bounds :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1))) ≤ Real.log ((Fintype.card R : ℝ)/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawB j q.2))) ≤ Real.log ((Fintype.card R : ℝ)/S.p) := by
  have hh := chain_error_bounds S.μ S.x₀ S.y₀ S.l S.nodup S.C S.hC.le S.F S.H
    S.hF S.hF1 S.hH S.hH1 S.localF S.localH S.θ S.hθ S.hθ1 S.localθL S.localθR S.hp S.mass
  dsimp only at hh
  simp only [S.rawA_error_eq, S.rawB_error_eq, ← Finset.mul_sum]
  constructor
  · have h := mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ 1/S.p from div_nonneg zero_le_one S.hp.le)
    simpa only [U, V, ← mul_assoc, one_div, inv_mul_cancel₀ S.hp.ne', one_mul] using h
  · have h := mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ 1/S.p from div_nonneg zero_le_one S.hp.le)
    simpa only [U, V, ← mul_assoc, one_div, inv_mul_cancel₀ S.hp.ne', one_mul] using h

def M (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ) (x : X) :=
  unitize (S.rawA j x) E
def N (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ) (y : Y) :=
  unitize (S.rawB j y) E
lemma M_unit (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) (x : X) : hsSq (S.M j E x) = 1 := hsSq_unitize _ _ hE
lemma N_unit (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) (y : Y) : hsSq (S.N j E y) = 1 := hsSq_unitize _ _ hE

lemma norm_cost_bounds (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawA j q.1-S.M j E q.1))) ≤ Real.log (1/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawB j q.2-S.N j E q.2))) ≤ Real.log (1/S.p) := by
  have he := list_coord_entropy_sum_le (fun _ : I => S.μ) S.density S.density_nonneg S.density_total S.l S.nodup
  have hlog := kl_tilt_le (pi (fun _ : I => S.μ)) S.density S.density_nonneg S.density_total
    (one_div_pos.mpr S.hp) S.density_le
  rw [kl_tilt] at hlog
  have hb := he.trans hlog
  have hA (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.rawA j q.1-S.M j E q.1)) ≤
      S.μ.avg (fun z => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z *
        Real.log (coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z)) := by
    exact first_unitize_cost S.μ S.y₀
      (coordDensity (fun _ : I => S.μ) S.density S.l[j.val])
      (coordDensity_nonneg _ _ S.density_nonneg S.l[j.val])
      (coordDensity_total _ _ S.density_total S.l[j.val]) (S.rawA j) (S.rawA_norm j) E hE
  have hB (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.rawB j q.2-S.N j E q.2)) ≤
      S.μ.avg (fun z => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z *
        Real.log (coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z)) := by
    exact second_unitize_cost S.μ S.x₀
      (coordDensity (fun _ : I => S.μ) S.density S.l[j.val])
      (coordDensity_nonneg _ _ S.density_nonneg S.l[j.val])
      (coordDensity_total _ _ S.density_total S.l[j.val]) (S.rawB j) (S.rawB_norm j) E hE
  exact ⟨(Finset.sum_le_sum fun j _ => hA j).trans hb, (Finset.sum_le_sum fun j _ => hB j).trans hb⟩

lemma normalized_error_bounds (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.M j E q.1))) ≤ 4*Real.log ((Fintype.card R : ℝ)/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.N j E q.2))) ≤ 4*Real.log ((Fintype.card R : ℝ)/S.p) := by
  have hcard : (1:ℝ) ≤ Fintype.card R := by exact_mod_cast Fintype.card_pos (α := R)
  have hl : Real.log (1/S.p) ≤ Real.log ((Fintype.card R : ℝ)/S.p) :=
    Real.log_le_log (one_div_pos.mpr S.hp) (div_le_div_of_nonneg_right hcard S.hp.le)
  have ha := S.raw_error_bounds
  have hb := S.norm_cost_bounds E hE
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      avg_unitize_triangle S.μ (S.D j) (fun q => S.rawA j q.1) E)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    change (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.M j E q.1))) ≤
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1)))+
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawA j q.1-S.M j E q.1))) at hh
    linarith
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      avg_unitize_triangle S.μ (S.D j) (fun q => S.rawB j q.2) E)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    change (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.N j E q.2))) ≤
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawB j q.2)))+
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawB j q.2-S.N j E q.2))) at hh
    linarith
end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

def Game.questionLaw {x y a b : ℕ} (G : Game x y a b) : Law (Fin (x+1)×Fin (y+1)) :=
  ⟨G.questionProb, G.questionProb_nonneg, G.questionProb_sum⟩

namespace QuantumSampling
lemma rounding_value_rect {m n : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (D : Fin (x+1)×Fin (y+1) → Matrix m n ℂ)
    (M : Fin (x+1) → Matrix m n ℂ) (N : Fin (y+1) → Matrix m n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {eA eB : ℝ}
    (hA : G.questionLaw.avg (fun z => hsSq (D z-M z.1)) ≤ eA)
    (hB : G.questionLaw.avg (fun z => hsSq (D z-N z.2)) ≤ eB)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    G.questionLaw.avg (fun z => payoff (D z) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤
      entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (4*(eA+eB))) +
        2*Real.sqrt eA+eA := by
  have hη : G.questionLaw.avg (fun z => hsSq (M z.1-N z.2)) ≤ 2*(eA+eB) := by
    have he := G.questionLaw.avg_mono (fun z => hsSq_triangle (M z.1) (D z) (N z.2))
    have heq : G.questionLaw.avg (fun z => 2*(hsSq (M z.1-D z)+hsSq (D z-N z.2))) =
        2*(G.questionLaw.avg (fun z => hsSq (D z-M z.1))+G.questionLaw.avg (fun z => hsSq (D z-N z.2))) := by
      simp only [hsSq_sub_comm (M _), show (fun z => 2*(hsSq (D z-M z.1)+hsSq (D z-N z.2))) =
        (fun z => (2:ℝ) • (hsSq (D z-M z.1)+hsSq (D z-N z.2))) from rfl, avg_smul, avg_add, smul_eq_mul]
    rw [heq] at he
    linarith
  have hround := correlated_sampling_value_rect G M N hM hN P Q hε hε1
  change G.questionLaw.avg (fun z => payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤
    entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*G.questionLaw.avg (fun z => hsSq (M z.1-N z.2)))) at hround
  have hloss := avg_payoff_difference_unbounded G.questionLaw D (fun z => M z.1)
    (fun z => (hM z.1).le) (fun z => P z.1) (fun z => Q z.2) (fun z => G.accepts z.1 z.2)
  have hsA := Real.sqrt_le_sqrt hA
  have hsη : Real.sqrt (2*G.questionLaw.avg (fun z => hsSq (M z.1-N z.2))) ≤
      Real.sqrt (4*(eA+eB)) := Real.sqrt_le_sqrt (by linarith)
  have hsamp : Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*G.questionLaw.avg (fun z => hsSq (M z.1-N z.2)))) ≤
      Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (4*(eA+eB))) := by
    apply Real.sqrt_le_sqrt
    linarith [mul_le_mul_of_nonneg_left hsη (show (0:ℝ) ≤ 12/ε from div_nonneg (by norm_num) hε.le)]
  linarith

lemma rounding_value_modes {m n R : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n] [Fintype R] [DecidableEq R] [Nonempty R]
    {x y a b : ℕ} (G : Game x y a b) (ρ : Law R)
    (D : R → Fin (x+1)×Fin (y+1) → Matrix m n ℂ)
    (M : R → Fin (x+1) → Matrix m n ℂ) (N : R → Fin (y+1) → Matrix m n ℂ)
    (hM : ∀ r x, hsSq (M r x) = 1) (hN : ∀ r y, hsSq (N r y) = 1)
    (P : R → Fin (x+1) → POVM m (Fin (a+1))) (Q : R → Fin (y+1) → POVM n (Fin (b+1)))
    {eA eB : ℝ}
    (hA : ρ.avg (fun r => G.questionLaw.avg (fun z => hsSq (D r z-M r z.1))) ≤ eA)
    (hB : ρ.avg (fun r => G.questionLaw.avg (fun z => hsSq (D r z-N r z.2))) ≤ eB)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ρ.avg (fun r => G.questionLaw.avg (fun z => payoff (D r z) (P r z.1) (Q r z.2) (G.accepts z.1 z.2))) ≤
      entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (4*(eA+eB))) +
        2*Real.sqrt eA+eA := by
  let D' := fun z => weightedBlock ρ.weight (fun r => D r z)
  let M' := fun x => weightedBlock ρ.weight (fun r => M r x)
  let N' := fun y => weightedBlock ρ.weight (fun r => N r y)
  have hm : ∀ x, hsSq (M' x) = 1 := by
    intro x
    simp only [M', hsSq_weightedBlock _ ρ.nonneg, hM, mul_one, ρ.total]
  have hn : ∀ y, hsSq (N' y) = 1 := by
    intro y
    simp only [N', hsSq_weightedBlock _ ρ.nonneg, hN, mul_one, ρ.total]
  have ha : G.questionLaw.avg (fun z => hsSq (D' z-M' z.1)) ≤ eA := by
    simp only [D', M', hsSq_weightedBlock_sub _ ρ.nonneg]
    change G.questionLaw.avg (fun z => ρ.avg (fun r => hsSq (D r z-M r z.1))) ≤ _
    rw [avg_comm]; exact hA
  have hb : G.questionLaw.avg (fun z => hsSq (D' z-N' z.2)) ≤ eB := by
    simp only [D', N', hsSq_weightedBlock_sub _ ρ.nonneg]
    change G.questionLaw.avg (fun z => ρ.avg (fun r => hsSq (D r z-N r z.2))) ≤ _
    rw [avg_comm]; exact hB
  have hh := rounding_value_rect G D' M' N' hm hn
    (fun x => POVM.blocks (fun r => P r x)) (fun y => POVM.blocks (fun r => Q r y)) ha hb hε hε1
  simp only [D', payoff_weightedBlock _ ρ.nonneg] at hh
  change G.questionLaw.avg (fun z => ρ.avg (fun r => payoff (D r z) (P r z.1) (Q r z.2) (G.accepts z.1 z.2))) ≤ _ at hh
  rw [avg_comm] at hh
  exact hh
end QuantumSampling
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {R : Type u_R} [Fintype R] [Nonempty R]
def uniform : Law R where
  weight _ := 1/(Fintype.card R : ℝ)
  nonneg _ := by positivity
  total := by simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
lemma uniform_avg (f : R → ℝ) : (uniform (R := R)).avg f = (1/(Fintype.card R : ℝ))*∑ r, f r := by
  simp only [uniform, avg, smul_eq_mul, Finset.mul_sum]
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
namespace ThresholdParallelRepetition
lemma rounding_loss_small {δ τ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (_hτ : 0 ≤ τ)
    (hsmall : τ ≤ δ^8/(2:ℝ)^80) :
    4*Real.sqrt (2*(δ^2/1024)^2+(12/(δ^2/1024))*Real.sqrt (32*τ)) +
      2*Real.sqrt (4*τ)+4*τ ≤ δ/4 := by
  have hδ2 : 0 < δ^2 := sq_pos_of_pos hδ
  have h24 : δ^4 ≤ δ^2 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h48 : δ^8 ≤ δ^4 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have hs32 : Real.sqrt (32*τ) ≤ δ^4/(2:ℝ)^36 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hterm : (12/(δ^2/1024))*Real.sqrt (32*τ) ≤ δ^2/2048 := by
    have hmul := mul_le_mul_of_nonneg_left hs32 (show 0 ≤ 12/(δ^2/1024) by positivity)
    have he : (12/(δ^2/1024))*(δ^4/(2:ℝ)^36) = (3/(2:ℝ)^24)*δ^2 := by
      field_simp; ring
    rw [he] at hmul
    nlinarith
  have hinner : 2*(δ^2/1024)^2+(12/(δ^2/1024))*Real.sqrt (32*τ) ≤ δ^2/1024 := by
    nlinarith
  have hsout : Real.sqrt (2*(δ^2/1024)^2+(12/(δ^2/1024))*Real.sqrt (32*τ)) ≤ δ/32 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hs4 : Real.sqrt (4*τ) ≤ δ/64 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have ht4 : 4*τ ≤ δ/32 := by nlinarith
  linarith
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {I R m n : Type} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (S : EventSystem (Fin (x+1)) (Fin (y+1)) I R m n)
  (hμ : S.μ = G.questionLaw)
  (T : Refinement S (Fin (a+1)) (Fin (b+1)))

include hμ
lemma conditional_rounding_bound (hl : 0 < S.l.length) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1/(S.l.length : ℝ))*∑ j : Fin S.l.length, T.score S.l[j.val] G.accepts ≤
      entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (32*(Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)))) +
        2*Real.sqrt (4*(Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)))+
          4*(Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)) := by
  have : Nonempty (Fin S.l.length) := ⟨⟨0,hl⟩⟩
  let E : Matrix ((S.J×m)×(R×Profile I (Fin (x+1)) (Fin (y+1))))
      ((S.J×n)×(R×Profile I (Fin (x+1)) (Fin (y+1)))) ℂ :=
    basisState (Classical.arbitrary _) (Classical.arbitrary _)
  have hE : hsSq E = 1 := hsSq_basisState _ _
  let τ := Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)
  have hb := S.normalized_error_bounds E hE
  have hA : (uniform (R := Fin S.l.length)).avg (fun j => G.questionLaw.avg
      (fun q => hsSq (S.D j q-S.M j E q.1))) ≤ 4*τ := by
    rw [← hμ, uniform_avg, Fintype.card_fin]
    have hh := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ 1/(S.l.length : ℝ) by positivity)
    exact hh.trans_eq (by dsimp only [τ]; ring)
  have hB : (uniform (R := Fin S.l.length)).avg (fun j => G.questionLaw.avg
      (fun q => hsSq (S.D j q-S.N j E q.2))) ≤ 4*τ := by
    rw [← hμ, uniform_avg, Fintype.card_fin]
    have hh := mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ 1/(S.l.length : ℝ) by positivity)
    exact hh.trans_eq (by dsimp only [τ]; ring)
  have hr := rounding_value_modes G uniform S.D (fun j => S.M j E) (fun j => S.N j E)
    (fun j => S.M_unit j E hE) (fun j => S.N_unit j E hE) (T.P 0) (T.Q 0) hA hB hε hε1
  rw [← hμ] at hr
  simp only [T.payoff_D_eq_score, uniform_avg, Fintype.card_fin] at hr
  have he : 4*(4*τ+4*τ)=32*τ := by ring
  simpa only [he, τ] using hr

lemma conditional_rounding_small (hl : 0 < S.l.length) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (1/(S.l.length : ℝ))*∑ j : Fin S.l.length, T.score S.l[j.val] G.accepts ≤ entangledValue G+δ/4 := by
  have hn : 0 ≤ Real.log ((Fintype.card R : ℝ)/S.p) := by
    have he := S.raw_error_bounds.1
    have hz : 0 ≤ ∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1)) :=
      Finset.sum_nonneg (fun j _ => S.μ.avg_nonneg (fun q => hsSq_nonneg _))
    exact hz.trans he
  have ht : 0 ≤ Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ) := div_nonneg hn (Nat.cast_nonneg _)
  have he0 : 0 < δ^2/1024 := by positivity
  have he1 : δ^2/1024 ≤ 1 := by nlinarith
  have hh := conditional_rounding_bound G S hμ T hl he0 he1
  have hnum := rounding_loss_small hδ hδ1 ht hsmall
  linarith
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law OperatorEntropy
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} {T : Type u_T} {U : Type u_U} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [Fintype B] [Fintype R] [Fintype T] [Fintype U]

lemma coarsen_prob_sum (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (f : A → R) (g : B → T) (w : R → T → ℝ) :
    (∑ r, ∑ t, w r t * prob C ((P.coarsen f).effect r) ((Q.coarsen g).effect t)) =
      ∑ a, ∑ b, w (f a) (g b) * prob C (P.effect a) (Q.effect b) := by
  classical
  have hR (r : R) : (∑ t, w r t * prob C ((P.coarsen f).effect r) ((Q.coarsen g).effect t)) =
      ∑ b, w r (g b)*prob C ((P.coarsen f).effect r) (Q.effect b) :=
    Q.coarsen_sum g (fun t => w r t • probRight C ((P.coarsen f).effect r))
  simp only [hR]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b, ∑ a, w (f a) (g b)*prob C (P.effect a) (Q.effect b) := by
      apply Finset.sum_congr rfl; intro b _
      exact P.coarsen_sum f (fun r => w r (g b) • probLeft C (Q.effect b))
    _ = _ := Finset.sum_comm

lemma POVM.coarsen_slice (P : POVM m A) (f : A → R) (g : A → T) (r : R) :
    (∑ t, (P.coarsen (fun a => (f a,g a))).effect (r,t)) = (P.coarsen f).effect r := by
  classical
  simp only [POVM.coarsen, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simp only [Prod.mk.injEq]
  by_cases hr : f a = r
  · simp [hr]
  · simp [hr]

lemma prob_POVM_total (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) :
    (∑ a, ∑ b, prob C (P.effect a) (Q.effect b)) = hsSq C := by
  simp only [← prob_sum_right, ← prob_sum_left, P.total, Q.total, prob_one]

def outcomeLaw (C : Matrix m n ℂ) (hC : hsSq C = 1) (P : POVM m A) (Q : POVM n B) : Law (A×B) where
  weight z := prob C (P.effect z.1) (Q.effect z.2)
  nonneg z := prob_nonneg (P.pos z.1) (Q.pos z.2)
  total := by rw [Fintype.sum_prod_type, prob_POVM_total, hC]

lemma outcomeLaw_avg (C : Matrix m n ℂ) (hC : hsSq C = 1) (P : POVM m A) (Q : POVM n B) (f : A×B → ℝ) :
    (outcomeLaw C hC P Q).avg f = ∑ a, ∑ b, prob C (P.effect a) (Q.effect b)*f (a,b) := by
  simp only [avg, outcomeLaw, smul_eq_mul, Fintype.sum_prod_type]
end ThresholdParallelRepetition.QuantumSampling

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

structure RepeatedModel (X : Type u_X) (Y : Type u_Y) (A : Type u_A) (B : Type u_B) (I : Type u_I) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] where
  μ : Law (X×Y)
  C : Matrix m n ℂ
  hC : hsSq C = 1
  P : (I → X) → POVM m (I → A)
  Q : (I → Y) → POVM n (I → B)
  V : X → Y → A → B → Bool

namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (M : RepeatedModel X Y A B I m n)
abbrev Result := Profile I X Y × ((I→A)×(I→B))
def answers (z : Profile I X Y) : Law ((I→A)×(I→B)) :=
  outcomeLaw M.C M.hC (M.P (fun i => (z i).1)) (M.Q (fun i => (z i).2))
def joint : Law (Result (X := X) (Y := Y) (A := A) (B := B) (I := I)) where
  weight t := (pi (fun _ : I => M.μ)).weight t.1 * (M.answers t.1).weight t.2
  nonneg t := mul_nonneg ((pi _).nonneg t.1) ((M.answers t.1).nonneg t.2)
  total := by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (M.answers _).total, mul_one, (pi _).total]
lemma joint_avg (f : Result (X := X) (Y := Y) (A := A) (B := B) (I := I) → ℝ) :
    M.joint.avg f = (pi (fun _ : I => M.μ)).avg (fun z => (M.answers z).avg (fun w => f (z,w))) := by
  simp only [avg, joint, smul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
def winsAt (t : Result (X := X) (Y := Y) (A := A) (B := B) (I := I)) (i : I) : Bool :=
  M.V (t.1 i).1 (t.1 i).2 (t.2.1 i) (t.2.2 i)
def indicator (c : Finset I) (t : Result (X := X) (Y := Y) (A := A) (B := B) (I := I)) : ℝ :=
  if ∀ i ∈ c, M.winsAt t i then 1 else 0
def mass (c : Finset I) : ℝ := M.joint.avg (M.indicator c)
lemma indicator_nonneg (c : Finset I) (t) : 0 ≤ M.indicator c t := by
  unfold indicator; split_ifs <;> norm_num
lemma indicator_le_one (c : Finset I) (t) : M.indicator c t ≤ 1 := by
  unfold indicator; split_ifs <;> norm_num
lemma mass_nonneg (c : Finset I) : 0 ≤ M.mass c := M.joint.avg_nonneg (M.indicator_nonneg c)
lemma mass_le_one (c : Finset I) : M.mass c ≤ 1 := M.joint.avg_le_const (M.indicator_le_one c)
lemma mass_empty : M.mass ∅ = 1 := by
  have he : M.indicator ∅ = fun _ => (1:ℝ) := by funext t; simp [indicator]
  rw [mass, he, avg_const]
lemma indicator_insert (c : Finset I) (i : I) (t) :
    M.indicator (insert i c) t = M.indicator c t * (if M.winsAt t i then 1 else 0) := by
  simp only [indicator, Finset.forall_mem_insert]
  split_ifs <;> simp_all
lemma mass_insert_le (c : Finset I) (i : I) : M.mass (insert i c) ≤ M.mass c := by
  apply M.joint.avg_mono
  intro t
  rw [indicator_insert]
  split_ifs <;> simp [M.indicator_nonneg]

abbrev Records (c : Finset I) := (c → A)×(c → B)
def restrictA (c : Finset I) (a : I→A) : c → A := fun i => a i
def restrictB (c : Finset I) (b : I→B) : c → B := fun i => b i
def mask (c : Finset I) (r : Records (A := A) (B := B) c) (z : Profile I X Y) : ℝ :=
  if ∀ i : c, M.V (z i).1 (z i).2 (r.1 i) (r.2 i) then 1 else 0
def coarseA (c : Finset I) (z : Profile I X Y) : POVM m (c → A) :=
  (M.P (fun i => (z i).1)).coarsen (restrictA c)
def coarseB (c : Finset I) (z : Profile I X Y) : POVM n (c → B) :=
  (M.Q (fun i => (z i).2)).coarsen (restrictB c)
lemma mask_restrict (c : Finset I) (z : Profile I X Y) (a : I→A) (b : I→B) :
    M.mask c (restrictA c a,restrictB c b) z = M.indicator c (z,a,b) := by
  simp only [mask, indicator, winsAt, restrictA, restrictB]
  congr 1
  exact propext Subtype.forall
lemma coarse_event (c : Finset I) (z : Profile I X Y) :
    (∑ r : Records (A := A) (B := B) c, M.mask c r z * prob M.C ((M.coarseA c z).effect r.1) ((M.coarseB c z).effect r.2)) =
      (M.answers z).avg (fun w => M.indicator c (z,w)) := by
  rw [Fintype.sum_prod_type, coarseA, coarseB, coarsen_prob_sum]
  simp only [mask_restrict, answers, outcomeLaw_avg, mul_comm]
lemma mask_nonneg (c : Finset I) (r) (z) : 0 ≤ M.mask c r z := by
  unfold mask; split_ifs <;> norm_num
lemma mask_le_one (c : Finset I) (r) (z) : M.mask c r z ≤ 1 := by
  unfold mask; split_ifs <;> norm_num
lemma coarse_event_le_one (c : Finset I) (z : Profile I X Y) :
    (∑ r : Records (A := A) (B := B) c, M.mask c r z * prob M.C ((M.coarseA c z).effect r.1) ((M.coarseB c z).effect r.2)) ≤ 1 := by
  rw [M.coarse_event]
  exact (M.answers z).avg_le_const (fun w => M.indicator_le_one c (z,w))
lemma mass_coarse (c : Finset I) :
    (∑ r : Records (A := A) (B := B) c, (pi (fun _ : I => M.μ)).avg (fun z => M.mask c r z *
      prob M.C ((M.coarseA c z).effect r.1) ((M.coarseB c z).effect r.2))) = M.mass c := by
  rw [← avg_sum]
  simp only [M.coarse_event]
  exact (M.joint_avg _).symm
end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace FiniteProbability.Law
variable {I : Type u_I} {X : Type u_X} {Y : Type u_Y} [DecidableEq I]
lemma firsts_updateRight (z : Profile I X Y) (i : I) (y : Y) :
    (fun j => (updateRight z i y j).1) = fun j => (z j).1 := by
  funext j
  by_cases h : j=i
  · subst j; simp [updateRight]
  · simp [updateRight, Function.update_of_ne h]
lemma seconds_updateLeft (z : Profile I X Y) (i : I) (x : X) :
    (fun j => (updateLeft z i x j).2) = fun j => (z j).2 := by
  funext j
  by_cases h : j=i
  · subst j; simp [updateLeft]
  · simp [updateLeft, Function.update_of_ne h]
end FiniteProbability.Law
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma coarseA_local (c : Finset I) (r : c→A) (i : I) : IgnoresRight (fun z => (M.coarseA c z).effect r) i := by
  intro z y
  simp only [coarseA, firsts_updateRight]
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma coarseB_local (c : Finset I) (r : c→B) (i : I) : IgnoresLeft (fun z => (M.coarseB c z).effect r) i := by
  intro z x
  simp only [coarseB, seconds_updateLeft]
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma mask_congr (c : Finset I) (r : Records (A := A) (B := B) c) {z z' : Profile I X Y}
    (hz : ∀ i ∈ c, z i = z' i) : M.mask c r z = M.mask c r z' := by
  simp only [mask]
  congr 1
  apply propext
  exact forall_congr' (fun i => by rw [hz i i.property])
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma mask_local_left (c : Finset I) (r : Records (A := A) (B := B) c) (i : I) (hi : i ∉ c) : IgnoresLeft (M.mask c r) i := by
  intro z x
  apply M.mask_congr
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma mask_local_right (c : Finset I) (r : Records (A := A) (B := B) c) (i : I) (hi : i ∉ c) : IgnoresRight (M.mask c r) i := by
  intro z y
  apply M.mask_congr
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _

def exposure (c : Finset I) (hp : 0 < M.mass c) : EventSystem X Y I (Records (A := A) (B := B) c) m n where
  μ := M.μ
  x₀ := Classical.arbitrary X
  y₀ := Classical.arbitrary Y
  l := cᶜ.toList
  nodup := cᶜ.nodup_toList
  C := M.C
  hC := M.hC
  F r z := (M.coarseA c z).effect r.1
  H r z := (M.coarseB c z).effect r.2
  hF r z := (M.coarseA c z).pos r.1
  hF1 r z := (M.coarseA c z).le_one r.1
  hH r z := (M.coarseB c z).pos r.2
  hH1 r z := (M.coarseB c z).le_one r.2
  localF r i := M.coarseA_local c r.1 i
  localH r i := M.coarseB_local c r.2 i
  θ := M.mask c
  hθ := M.mask_nonneg c
  hθ1 := M.mask_le_one c
  localθL r i hi := M.mask_local_left c r i (by simpa only [Finset.mem_toList, Finset.mem_compl] using hi)
  localθR r i hi := M.mask_local_right c r i (by simpa only [Finset.mem_toList, Finset.mem_compl] using hi)
  event_le_one := M.coarse_event_le_one c
  p := M.mass c
  hp := hp
  mass := M.mass_coarse c

def fineA (c : Finset I) (i : I) (z : Profile I X Y) : POVM m ((c→A)×A) :=
  (M.P (fun j => (z j).1)).coarsen (fun a => (restrictA c a,a i))
def fineB (c : Finset I) (i : I) (z : Profile I X Y) : POVM n ((c→B)×B) :=
  (M.Q (fun j => (z j).2)).coarsen (fun b => (restrictB c b,b i))

def refinement (c : Finset I) (hp : 0 < M.mass c) : Refinement (M.exposure c hp) A B where
  left i r z a := (M.fineA c i z).effect (r.1,a)
  right i r z b := (M.fineB c i z).effect (r.2,b)
  left_pos i r z a := (M.fineA c i z).pos (r.1,a)
  right_pos i r z b := (M.fineB c i z).pos (r.2,b)
  left_total i r z := POVM.coarsen_slice _ (restrictA c) (fun a => a i) r.1
  right_total i r z := POVM.coarsen_slice _ (restrictB c) (fun b => b i) r.2
  left_local i r a j := by intro z y; simp only [fineA, firsts_updateRight]
  right_local i r b j := by intro z x; simp only [fineB, seconds_updateLeft]
end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma fine_event (c : Finset I) (i : I) (z : Profile I X Y) :
    (∑ r : Records (A := A) (B := B) c, M.mask c r z *
      ∑ a, ∑ b, if M.V (z i).1 (z i).2 a b then
        prob M.C ((M.fineA c i z).effect (r.1,a)) ((M.fineB c i z).effect (r.2,b)) else 0) =
      (M.answers z).avg (fun w => M.indicator (insert i c) (z,w)) := by
  have hh := coarsen_prob_sum M.C (M.P (fun j => (z j).1)) (M.Q (fun j => (z j).2))
    (fun a => (restrictA c a,a i)) (fun b => (restrictB c b,b i))
    (fun ra rb => M.mask c (ra.1,rb.1) z * (if M.V (z i).1 (z i).2 ra.2 rb.2 then (1:ℝ) else 0))
  simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul] at hh
  simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]
  conv_lhs => arg 2; ext ra; rw [Finset.sum_comm]
  rw [show (∑ ra, ∑ a, ∑ rb, ∑ b, if M.V (z i).1 (z i).2 a b then
      M.mask c (ra,rb) z * prob M.C ((M.fineA c i z).effect (ra,a)) ((M.fineB c i z).effect (rb,b)) else 0) =
      ∑ a, ∑ b, if M.V (z i).1 (z i).2 (a i) (b i) then
        M.mask c (restrictA c a,restrictB c b) z * prob M.C ((M.P (fun j => (z j).1)).effect a) ((M.Q (fun j => (z j).2)).effect b) else 0 from hh]
  simp only [answers, outcomeLaw_avg, M.indicator_insert, M.mask_restrict, winsAt]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  split_ifs with h <;> simp [h, mul_comm]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B] in
lemma score_eq_mass_ratio (c : Finset I) (hp : 0 < M.mass c) (i : I) :
    (M.refinement c hp).score i M.V = M.mass (insert i c)/M.mass c := by
  unfold Refinement.score
  change (1/M.mass c)*∑ r : Records (A := A) (B := B) c,
    (pi (fun _ : I => M.μ)).avg (fun z => M.mask c r z *
      ∑ a, ∑ b, if M.V (z i).1 (z i).2 a b then
        prob M.C ((M.fineA c i z).effect (r.1,a)) ((M.fineB c i z).effect (r.2,b)) else 0) = _
  rw [← avg_sum]
  simp only [M.fine_event]
  rw [← M.joint_avg]
  change (1/M.mass c)*M.mass (insert i c) = _
  ring

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
omit [Fintype I] in
lemma card_records (c : Finset I) : Fintype.card (Records (A := A) (B := B) c) = (Fintype.card A*Fintype.card B)^c.card := by
  simp only [Records, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, mul_pow]

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Tests
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)
def event (c : Finset I) (ω : Ω) : ℝ := if ∀ i ∈ c, win ω i then 1 else 0
def mass (c : Finset I) : ℝ := ρ.avg (event win c)
def rate (ω : Ω) : ℝ := (uniform (R := I)).avg (fun i => if win ω i then 1 else 0)
def moment (c : Finset I) (t : ℕ) : ℝ := ρ.avg (fun ω => event win c ω*(rate win ω)^t)

omit [Nonempty I] [Fintype Ω] in
lemma event_nonneg (c : Finset I) (ω : Ω) : 0 ≤ event win c ω := by unfold event; split_ifs <;> norm_num
omit [Nonempty I] [Fintype Ω] in
lemma event_le_one (c : Finset I) (ω : Ω) : event win c ω ≤ 1 := by unfold event; split_ifs <;> norm_num
omit [Nonempty I] in
lemma mass_nonneg (c : Finset I) : 0 ≤ mass ρ win c := ρ.avg_nonneg (event_nonneg win c)
omit [Nonempty I] in
lemma mass_le_one (c : Finset I) : mass ρ win c ≤ 1 := ρ.avg_le_const (event_le_one win c)
omit [DecidableEq I] [Fintype Ω] in
lemma rate_nonneg (ω : Ω) : 0 ≤ rate win ω := by
  apply avg_nonneg; intro i; split_ifs <;> norm_num
omit [DecidableEq I] [Fintype Ω] in
lemma rate_le_one (ω : Ω) : rate win ω ≤ 1 := by
  apply avg_le_const; intro i; split_ifs <;> norm_num
omit [Nonempty I] [Fintype Ω] in
lemma event_empty (ω : Ω) : event win ∅ ω = 1 := by simp [event]
omit [Nonempty I] in
lemma mass_empty : mass ρ win ∅ = 1 := by
  unfold mass
  conv_lhs => arg 2; ext ω; rw [event_empty]
  exact avg_const _ 1
omit [Nonempty I] [Fintype Ω] in
lemma event_insert (c : Finset I) (i : I) (ω : Ω) :
    event win (insert i c) ω = event win c ω*(if win ω i then 1 else 0) := by
  simp only [event, Finset.forall_mem_insert]
  split_ifs <;> simp_all
omit [Fintype Ω] in
lemma avg_event_insert (c : Finset I) (ω : Ω) :
    (uniform (R := I)).avg (fun i => event win (insert i c) ω) = event win c ω*rate win ω := by
  simp only [event_insert]
  change (uniform (R := I)).avg (fun i => event win c ω • (if win ω i then (1:ℝ) else 0)) = _
  rw [avg_smul]; rfl
lemma moment_zero (c : Finset I) : moment ρ win c 0 = mass ρ win c := by simp only [moment, pow_zero, mul_one, mass]
lemma moment_step (c : Finset I) (t : ℕ) :
    moment ρ win c (t+1) = (uniform (R := I)).avg (fun i => moment ρ win (insert i c) t) := by
  unfold moment
  rw [avg_comm]
  apply congrArg ρ.avg
  funext ω
  have he : (fun i => event win (insert i c) ω * rate win ω^t) =
      (fun i => (rate win ω^t) • event win (insert i c) ω) := by funext i; simp only [smul_eq_mul, mul_comm]
  rw [he, avg_smul, avg_event_insert, pow_succ]
  change _ = _*_
  ring

lemma moment_upper {r e : ℝ} (hr : 0 ≤ r) (_he : 0 ≤ e) (T : ℕ)
    (hstep : ∀ c : Finset I, c.card < T →
      (uniform (R := I)).avg (fun i => mass ρ win (insert i c)) ≤ r*mass ρ win c+e) :
    ∀ t : ℕ, ∀ c : Finset I, c.card+t ≤ T →
      moment ρ win c t ≤ r^t*mass ρ win c + e*∑ s ∈ Finset.range t, r^s := by
  intro t
  induction t with
  | zero => intro c hc; simp only [moment_zero, pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]; exact le_rfl
  | succ t ih =>
    intro c hc
    rw [moment_step]
    have hbound := (uniform (R := I)).avg_mono (fun i => ih (insert i c) (by
      have hi := Finset.card_insert_le i c
      omega))
    have heq : (uniform (R := I)).avg (fun i => r^t*mass ρ win (insert i c)+e*∑ s ∈ Finset.range t, r^s) =
        r^t*(uniform (R := I)).avg (fun i => mass ρ win (insert i c))+e*∑ s ∈ Finset.range t, r^s := by
      rw [avg_add, avg_const]
      change (uniform (R := I)).avg (fun i => (r^t) • mass ρ win (insert i c)) + _ = _
      rw [avg_smul]; rfl
    rw [heq] at hbound
    have hs := mul_le_mul_of_nonneg_left (hstep c (by omega)) (pow_nonneg hr t)
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

lemma threshold_moment_lower {q : ℝ} (hq : 0 ≤ q) (t : ℕ) :
    (ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0))*q^t ≤ moment ρ win ∅ t := by
  have he : (ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0))*q^t =
      ρ.avg (fun ω => if q ≤ rate win ω then q^t else 0) := by
    rw [mul_comm]
    change (q^t) • ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0) = _
    rw [← avg_smul]
    congr 1; funext ω; split_ifs <;> simp
  rw [he]
  apply ρ.avg_mono
  intro ω
  simp only [event_empty, one_mul]
  split_ifs with h
  · exact pow_le_pow_left₀ hq h _
  · exact pow_nonneg (rate_nonneg win ω) _
end Tests
end ThresholdParallelRepetition.FiniteProbability

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure

lemma sum_fin_get_toList {I : Type u_I} [DecidableEq I] (c : Finset I) (f : I → ℝ) :
    (∑ j : Fin c.toList.length, f c.toList[j.val]) = ∑ i ∈ c, f i := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map, Finset.sum_map_toList]

namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

omit [Nonempty I] in
lemma fresh_sum_bound (c : Finset I) (hp : 0 < M.mass c) (hc : c.card < Fintype.card I)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
      ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (∑ i ∈ cᶜ, M.mass (insert i c)) ≤
      (entangledValue G+δ/4)*M.mass c*((Fintype.card I-c.card : ℕ) : ℝ) := by
  have hl : 0 < (M.exposure c hp).l.length := by
    change 0 < cᶜ.toList.length
    simp only [Finset.length_toList, Finset.card_compl]
    omega
  have hs : Real.log ((Fintype.card (Records (A := Fin (a+1)) (B := Fin (b+1)) c) : ℝ)/(M.exposure c hp).p)/
      ((M.exposure c hp).l.length : ℝ) ≤ δ^8/(2:ℝ)^80 := by
    simpa only [exposure, card_records, Fintype.card_fin, Nat.cast_pow, Finset.length_toList, Finset.card_compl] using hsmall
  have hh := conditional_rounding_small G (M.exposure c hp) hμ (M.refinement c hp) hl hδ hδ1 hs
  rw [← hV] at hh
  simp only [M.score_eq_mass_ratio] at hh
  change (1/(cᶜ.toList.length : ℝ))*∑ j : Fin cᶜ.toList.length,
    M.mass (insert cᶜ.toList[j.val] c)/M.mass c ≤ _ at hh
  rw [sum_fin_get_toList cᶜ (fun i => M.mass (insert i c)/M.mass c), ← Finset.sum_div, Finset.length_toList, Finset.card_compl] at hh
  have hn : 0 < ((Fintype.card I-c.card : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hc
  rw [one_div, inv_mul_eq_div] at hh
  have hm := (div_le_iff₀ hp).mp ((div_le_iff₀ hn).mp hh)
  nlinarith

lemma good_event_step (c : Finset I) (hp : 0 < M.mass c) (hc : c.card < Fintype.card I)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : (c.card : ℝ) ≤ δ*(Fintype.card I : ℝ)/4)
    (hsmall : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
      ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (uniform (R := I)).avg (fun i => M.mass (insert i c)) ≤ (entangledValue G+δ/2)*M.mass c := by
  have hf := M.fresh_sum_bound G hμ hV c hp hc hδ hδ1 hsmall
  have hcBound : (∑ i ∈ c, M.mass (insert i c)) ≤ (c.card : ℝ)*M.mass c := by
    calc
      _ ≤ ∑ _i ∈ c, M.mass c := Finset.sum_le_sum (fun i _ => M.mass_insert_le c i)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hv : 0 ≤ entangledValue G+δ/4 := by linarith [entangledValue_nonneg G]
  have hcard : ((Fintype.card I-c.card : ℕ) : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Nat.sub_le (Fintype.card I) c.card
  have hsum := add_le_add hcBound (hf.trans (mul_le_mul_of_nonneg_left hcard (mul_nonneg hv hp.le)))
  rw [Finset.sum_add_sum_compl] at hsum
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [uniform_avg, one_div, inv_mul_eq_div]
  apply (div_le_iff₀ hn).mpr
  have hsz := mul_le_mul_of_nonneg_right hsize hp.le
  nlinarith

omit hμ hV [Nonempty m] [Nonempty n] in
lemma mean_eq_first_test : M.joint.avg (Tests.rate M.winsAt) =
    (uniform (R := I)).avg (fun i => M.mass (insert i ∅)) := by
  unfold Tests.rate
  rw [avg_comm]
  congr 1
  funext i
  unfold mass
  congr 1
  funext ω
  simp [indicator]

lemma unconditional_rate_le_value : M.joint.avg (Tests.rate M.winsAt) ≤ entangledValue G := by
  rw [M.mean_eq_first_test]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < min ε 1 := lt_min hε zero_lt_one
  have hδ1 : min ε 1 ≤ 1 := min_le_right _ _
  have hh := M.good_event_step G hμ hV ∅ (by rw [M.mass_empty]; norm_num)
    (by simpa using Fintype.card_pos (α := I)) hδ hδ1 (by simp; positivity) (by
      simp only [Finset.card_empty, pow_zero, M.mass_empty, div_one, Real.log_one, zero_div]
      positivity)
  rw [M.mass_empty, mul_one] at hh
  have hε' := min_le_left ε 1
  linarith

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
namespace ThresholdParallelRepetition

lemma testing_parameters_good {δ k d p : ℝ} {c : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < k) (hd : 1 ≤ d)
    (hc : (c : ℝ) ≤ δ^9*k/((2:ℝ)^90*(1+Real.log d)))
    (hp : Real.exp (-(δ^8*k/(2:ℝ)^83)) ≤ p) :
    (c : ℝ) ≤ δ*k/4 ∧ (c : ℝ) < k ∧
      Real.log (d^c/p)/(k-(c : ℝ)) ≤ δ^8/(2:ℝ)^80 := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hlog : 0 ≤ Real.log d := Real.log_nonneg hd
  have hD : 0 < (2:ℝ)^90*(1+Real.log d) := by positivity
  have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg c
  have hc' := (le_div_iff₀ hD).mp hc
  have h9 : δ^9 ≤ δ := by simpa using pow_le_pow_of_le_one hδ.le hδ1 (show 1 ≤ 9 by omega)
  have h98 : δ^9 ≤ δ^8 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h9k := mul_le_mul_of_nonneg_right h9 hk.le
  have h98k := mul_le_mul_of_nonneg_right h98 hk.le
  have hcd : (c : ℝ)*(2:ℝ)^90 ≤ δ^9*k := by
    nlinarith [mul_nonneg hc0 hlog]
  have hsize : (c : ℝ) ≤ δ*k/4 := by nlinarith
  have hhalf : (c : ℝ) ≤ k/2 := by nlinarith
  have hck : (c : ℝ) < k := by linarith
  have hp0 : 0 < p := (Real.exp_pos _).trans_le hp
  have hlp := Real.log_le_log (Real.exp_pos _) hp
  rw [Real.log_exp] at hlp
  have hlc : Real.log (d^c/p) ≤ δ^8*k/(2:ℝ)^82 := by
    rw [Real.log_div (pow_ne_zero _ hd0.ne') hp0.ne', Real.log_pow]
    have hclog : (c : ℝ)*Real.log d ≤ δ^8*k/(2:ℝ)^90 := by
      nlinarith
    nlinarith [mul_nonneg (pow_nonneg hδ.le 8) hk.le]
  refine ⟨hsize, hck, ?_⟩
  apply (div_le_iff₀ (sub_pos.mpr hck)).mpr
  have hz : 0 ≤ δ^8 := pow_nonneg hδ.le 8
  have hh := mul_le_mul_of_nonneg_left hhalf hz
  nlinarith

end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Tests
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)

def threshold (s : ℝ) : ℝ := ρ.avg (fun ω => if s ≤ rate win ω then (1:ℝ) else 0)
omit [DecidableEq I] in
lemma threshold_nonneg (s : ℝ) : 0 ≤ threshold ρ win s := by
  apply avg_nonneg; intro ω; split_ifs <;> norm_num
omit [DecidableEq I] in
lemma threshold_le_one (s : ℝ) : threshold ρ win s ≤ 1 := by
  apply avg_le_const; intro ω; split_ifs <;> norm_num

omit [DecidableEq I] in
lemma threshold_markov {s : ℝ} (_hs : 0 ≤ s) : threshold ρ win s*s ≤ ρ.avg (rate win) := by
  change ρ.avg (fun ω => if s ≤ rate win ω then (1:ℝ) else 0)*s ≤ _
  rw [mul_comm]
  change s • ρ.avg (fun ω => if s ≤ rate win ω then (1:ℝ) else 0) ≤ _
  rw [← avg_smul]
  apply ρ.avg_mono
  intro ω
  change s*(if s ≤ rate win ω then 1 else 0) ≤ rate win ω
  split_ifs with h
  · simpa using h
  · simpa using rate_nonneg win ω

omit [DecidableEq I] in
lemma threshold_mean_bound {v δ : ℝ} (hδ : 0 < δ) (hs : v+δ ≤ 1)
    (hmean : ρ.avg (rate win) ≤ v) : threshold ρ win (v+δ) ≤ Real.exp (-δ) := by
  have hmean0 : 0 ≤ ρ.avg (rate win) := ρ.avg_nonneg (rate_nonneg win)
  have hv : 0 ≤ v := hmean0.trans hmean
  have hm := (threshold_markov ρ win (show 0 ≤ v+δ by linarith)).trans hmean
  have hq := threshold_le_one ρ win (v+δ)
  have hmul := mul_nonneg (show 0 ≤ 1-(v+δ) by linarith) (show 0 ≤ 1-threshold ρ win (v+δ) by linarith)
  have he := Real.add_one_le_exp (-δ)
  nlinarith

lemma geometric_bound {v δ : ℝ} (hv : 0 ≤ v) (hδ : 0 < δ) (hs : v+δ ≤ 1) (T : ℕ) :
    (∑ s ∈ Finset.range T, (v+δ/2)^s) ≤ 2/δ := by
  have hr : 0 ≤ v+δ/2 := by linarith
  have hsum : 0 ≤ ∑ s ∈ Finset.range T, (v+δ/2)^s := Finset.sum_nonneg (fun s _ => pow_nonneg hr s)
  have hg := geom_sum_mul_neg (v+δ/2) T
  have hm := mul_le_mul_of_nonneg_left (show δ/2 ≤ 1-(v+δ/2) by linarith) hsum
  apply (le_div_iff₀ hδ).mpr
  nlinarith [pow_nonneg hr T]

lemma threshold_power_bound {v δ e : ℝ} (hv : 0 ≤ v) (hδ : 0 < δ) (hs : v+δ ≤ 1)
    (he : 0 ≤ e) (T : ℕ)
    (hstep : ∀ c : Finset I, c.card < T →
      (uniform (R := I)).avg (fun i => mass ρ win (insert i c)) ≤ (v+δ/2)*mass ρ win c+e) :
    threshold ρ win (v+δ)*(v+δ)^T ≤ (v+δ/2)^T+e*(2/δ) := by
  have hlo := threshold_moment_lower ρ win (show 0 ≤ v+δ by linarith) T
  have hhi := moment_upper ρ win (show 0 ≤ v+δ/2 by linarith) he T hstep T ∅ (by simp)
  rw [mass_empty, mul_one] at hhi
  have hg := mul_le_mul_of_nonneg_left (geometric_bound hv hδ hs T) he
  exact hlo.trans (hhi.trans (by linarith))

end ThresholdParallelRepetition.FiniteProbability.Tests

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

lemma all_event_step {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (T : ℕ)
    (hT : (T : ℝ) ≤ δ^9*(Fintype.card I : ℝ)/((2:ℝ)^90*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))))
    (c : Finset I) (hc : c.card < T) :
    (uniform (R := I)).avg (fun i => M.mass (insert i c)) ≤
      (entangledValue G+δ/2)*M.mass c+Real.exp (-(δ^8*(Fintype.card I : ℝ)/(2:ℝ)^83)) := by
  have hk : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : (1:ℝ) ≤ (((a+1)*(b+1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))
  have hc' : (c.card : ℝ) ≤ δ^9*(Fintype.card I : ℝ)/((2:ℝ)^90*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))) :=
    (show (c.card : ℝ) ≤ T by exact_mod_cast hc.le).trans hT
  by_cases hp : Real.exp (-(δ^8*(Fintype.card I : ℝ)/(2:ℝ)^83)) ≤ M.mass c
  · have hp0 := (Real.exp_pos _).trans_le hp
    obtain ⟨hsize, hcard, hsmall⟩ := testing_parameters_good hδ hδ1 hk hd hc' hp
    have hcNat : c.card < Fintype.card I := by exact_mod_cast hcard
    have hs : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
        ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80 := by
      simpa only [Nat.cast_sub hcNat.le] using hsmall
    exact (M.good_event_step G hμ hV c hp0 hcNat hδ hδ1 hsize hs).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hh := (uniform (R := I)).avg_le_const (fun i => M.mass_insert_le c i)
    have hv : 0 ≤ entangledValue G+δ/2 := by linarith [entangledValue_nonneg G]
    have hm := mul_nonneg hv (M.mass_nonneg c)
    linarith

lemma threshold_power_bound {δ : ℝ} (hδ : 0 < δ) (hs : entangledValue G+δ ≤ 1) (T : ℕ)
    (hT : (T : ℝ) ≤ δ^9*(Fintype.card I : ℝ)/((2:ℝ)^90*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ)))) :
    Tests.threshold M.joint M.winsAt (entangledValue G+δ)*(entangledValue G+δ)^T ≤
      (entangledValue G+δ/2)^T+Real.exp (-(δ^8*(Fintype.card I : ℝ)/(2:ℝ)^83))*(2/δ) := by
  have hv := entangledValue_nonneg G
  have hδ1 : δ ≤ 1 := by linarith
  exact Tests.threshold_power_bound M.joint M.winsAt hv hδ hs (Real.exp_pos _).le T
    (fun c hc => M.all_event_step G hμ hV hδ hδ1 T hT c hc)

lemma threshold_mean_bound {δ : ℝ} (hδ : 0 < δ) (hs : entangledValue G+δ ≤ 1) :
    Tests.threshold M.joint M.winsAt (entangledValue G+δ) ≤ Real.exp (-δ) :=
  Tests.threshold_mean_bound M.joint M.winsAt hδ hs (M.unconditional_rate_le_value G hμ hV)

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace ThresholdParallelRepetition

lemma power_ratio_bound {v δ : ℝ} (hv : 0 ≤ v) (hδ : 0 < δ) (hs : v+δ ≤ 1) (T : ℕ) :
    (v+δ/2)^T/(v+δ)^T ≤ Real.exp (-(δ*(T : ℝ)/2)) := by
  have hs0 : 0 < v+δ := by linarith
  have hr0 : 0 ≤ (v+δ/2)/(v+δ) := div_nonneg (by linarith) hs0.le
  have hr : (v+δ/2)/(v+δ) ≤ Real.exp (-δ/2) := by
    have he := Real.add_one_le_exp (-δ/2)
    have hratio : (v+δ/2)/(v+δ) ≤ 1-δ/2 := by
      apply (div_le_iff₀ hs0).mpr
      nlinarith
    linarith
  rw [← div_pow]
  have hh := pow_le_pow_left₀ hr0 hr T
  rw [← Real.exp_nat_mul] at hh
  exact hh.trans_eq (by congr 1; ring)

lemma inverse_power_bound {s δ : ℝ} (hδ : 0 < δ) (hs : δ ≤ s) (T : ℕ) :
    1/s^T ≤ Real.exp ((T : ℝ)/δ) := by
  have hs0 : 0 < s := hδ.trans_le hs
  have hh := Real.log_le_sub_one_of_pos (one_div_pos.mpr hδ)
  rw [one_div, Real.log_inv] at hh
  have hlog := Real.log_le_log hδ hs
  have hl : -Real.log s ≤ 1/δ := by simpa only [one_div] using (show -Real.log s ≤ δ⁻¹ by linarith)
  have hpow := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg T : (0:ℝ) ≤ T)
  have he : 1/s^T = Real.exp (-(T : ℝ)*Real.log s) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hs0, one_div]
  rw [he]
  apply Real.exp_le_exp.mpr
  simpa only [mul_neg, neg_mul, div_eq_mul_inv, one_mul] using hpow

end ThresholdParallelRepetition

end

noncomputable section
namespace ThresholdParallelRepetition

lemma analytic_threshold_bound {v δ θ R E q : ℝ}
    (hv : 0 ≤ v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : v+δ ≤ 1)
    (hθ : 2 ≤ θ) (hδθ : 8 ≤ δ*θ)
    (hθR : θ/δ ≤ R/4) (hR : 2/δ ≤ R/4) (hE : E ≤ δ*θ/8)
    (hq : q*(v+δ)^(⌊θ⌋₊) ≤ (v+δ/2)^(⌊θ⌋₊)+Real.exp (-R)*(2/δ)) :
    q ≤ Real.exp (-E) := by
  let T := ⌊θ⌋₊
  let L := δ*θ/4
  have hθ0 : 0 ≤ θ := by linarith
  have hT : (T : ℝ) ≤ θ := Nat.floor_le hθ0
  have hT' : θ/2 ≤ (T : ℝ) := by
    have hh := Nat.lt_floor_add_one θ
    dsimp [T]; linarith
  have hs0 : 0 < v+δ := by linarith
  have hp0 : 0 < (v+δ)^T := pow_pos hs0 _
  have hq' : q ≤ (v+δ/2)^T/(v+δ)^T + Real.exp (-R)*(2/δ)/(v+δ)^T := by
    rw [← add_div]
    exact (le_div_iff₀ hp0).mpr hq
  have hfirst : (v+δ/2)^T/(v+δ)^T ≤ Real.exp (-L) := by
    apply (power_ratio_bound hv hδ hs T).trans
    apply Real.exp_le_exp.mpr
    dsimp [L]
    nlinarith
  have hTδ : (T : ℝ)/δ ≤ R/4 := (div_le_div_of_nonneg_right hT hδ.le).trans hθR
  have hfac : 2/δ ≤ Real.exp (2/δ) := by linarith [Real.add_one_le_exp (2/δ)]
  have hbad : Real.exp (-R)*(2/δ)/(v+δ)^T ≤ Real.exp (-R/2) := by
    calc
      Real.exp (-R)*(2/δ)/(v+δ)^T = Real.exp (-R)*(2/δ)*(1/(v+δ)^T) := by ring
      _ ≤ Real.exp (-R)*Real.exp (2/δ)*Real.exp ((T : ℝ)/δ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hfac (Real.exp_pos _).le
        · exact inverse_power_bound hδ (by linarith) T
        · positivity
        · positivity
      _ = Real.exp (-R+2/δ+(T : ℝ)/δ) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-R/2) := Real.exp_le_exp.mpr (by linarith)
  have hδ2 : δ*δ ≤ 1 := by nlinarith
  have hL : L ≤ R/2 := by
    have hh : δ*θ ≤ θ/δ := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith [mul_le_mul_of_nonneg_right hδ2 hθ0]
    have hR0 : 0 < R := by have := div_pos (show (0:ℝ)<2 by norm_num) hδ; linarith
    dsimp [L]; linarith
  have hqL : q ≤ 2*Real.exp (-L) := by
    have hb : Real.exp (-R)*(2/δ)/(v+δ)^T ≤ Real.exp (-L) :=
      hbad.trans (Real.exp_le_exp.mpr (by linarith))
    linarith
  have htwo : 2 ≤ Real.exp (L/2) := by
    have hh := Real.add_one_le_exp (L/2)
    dsimp [L] at *
    linarith
  calc
    q ≤ 2*Real.exp (-L) := hqL
    _ ≤ Real.exp (L/2)*Real.exp (-L) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-L/2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-E) := by apply Real.exp_le_exp.mpr; dsimp [L]; linarith

lemma large_rate_parameters {δ k D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 0 < k) (hD : 1 ≤ D) (hbig : (2:ℝ)^100*D ≤ δ^12*k) :
    2 ≤ δ^9*k/((2:ℝ)^90*D) ∧
    8 ≤ δ*(δ^9*k/((2:ℝ)^90*D)) ∧
    (δ^9*k/((2:ℝ)^90*D))/δ ≤ (δ^8*k/(2:ℝ)^83)/4 ∧
    2/δ ≤ (δ^8*k/(2:ℝ)^83)/4 ∧
    δ^13*k/((2:ℝ)^101*D) ≤ δ*(δ^9*k/((2:ℝ)^90*D))/8 := by
  have hD0 : 0 < D := by linarith
  have hden : 0 < (2:ℝ)^90*D := by positivity
  have h129 : δ^12 ≤ δ^9 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h1210 : δ^12 ≤ δ^10 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h1310 : δ^13 ≤ δ^10 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h129k := mul_le_mul_of_nonneg_right h129 hk.le
  have h1210k := mul_le_mul_of_nonneg_right h1210 hk.le
  have h1310k := mul_le_mul_of_nonneg_right h1310 hk.le
  have h8k : 0 ≤ δ^8*k := by positivity
  have h10k : 0 ≤ δ^10*k := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hδ).mpr
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hD h8k
    nlinarith
  · apply (div_le_iff₀ hδ).mpr
    nlinarith
  · rw [← mul_div_assoc, div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < (2:ℝ)^101*D) (by positivity : 0 < (2:ℝ)^90*D*8)).mpr
    have hh := mul_le_mul_of_nonneg_right h1310k hD0.le
    nlinarith [mul_nonneg h10k hD0.le]

end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

lemma threshold_exp_bound {δ : ℝ} (hδ : 0 < δ) (hs : entangledValue G+δ ≤ 1) :
    Tests.threshold M.joint M.winsAt (entangledValue G+δ) ≤
      Real.exp (-(δ^13*(Fintype.card I : ℝ)/((2:ℝ)^101*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))))) := by
  let D : ℝ := 1+Real.log (((a+1)*(b+1) : ℕ) : ℝ)
  let k : ℝ := Fintype.card I
  let θ : ℝ := δ^9*k/((2:ℝ)^90*D)
  let R : ℝ := δ^8*k/(2:ℝ)^83
  let E : ℝ := δ^13*k/((2:ℝ)^101*D)
  have hd : (1:ℝ) ≤ (((a+1)*(b+1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))
  have hD : 1 ≤ D := by dsimp [D]; linarith [Real.log_nonneg hd]
  have hD0 : 0 < D := by linarith
  have hk : 0 < k := by dsimp [k]; exact_mod_cast Fintype.card_pos (α := I)
  have hv := entangledValue_nonneg G
  have hδ1 : δ ≤ 1 := by linarith
  change _ ≤ Real.exp (-E)
  by_cases hsmall : δ^12*k ≤ (2:ℝ)^100*D
  · apply (M.threshold_mean_bound G hμ hV hδ hs).trans
    apply Real.exp_le_exp.mpr
    suffices E ≤ δ by linarith
    dsimp [E]
    apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^101*D)).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall hδ.le
    nlinarith [mul_nonneg hδ.le hD0.le]
  · obtain ⟨hθ,hδθ,hθR,hR,hE⟩ := large_rate_parameters hδ hδ1 hk hD (le_of_not_ge hsmall)
    have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
    have htest := M.threshold_power_bound G hμ hV hδ hs ⌊θ⌋₊ (Nat.floor_le hθ0)
    exact analytic_threshold_bound hv hδ hδ1 hs hθ hδθ hθR hR hE htest

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law
namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]
def coeff (S : Strategy X Y A B) : Matrix (Fin (S.dimA+1)) (Fin (S.dimB+1)) ℂ := fun i j => S.state (i,j)
lemma coeff_unit (S : Strategy X Y A B) : hsSq S.coeff = 1 := by
  simpa only [hsSq, coeff, Fintype.sum_prod_type] using S.state_unit
lemma born_eq_prob (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b = prob S.coeff (S.alice x a) (S.bob y b) := by
  rw [S.born_eq_quadratic]
  rfl

def repetitionModel {x y a b k : ℕ} (S : RepeatedStrategy x y a b k) (G : Game x y a b) :
    RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) (Fin k)
      (Fin (S.dimA+1)) (Fin (S.dimB+1)) where
  μ := G.questionLaw
  C := S.coeff
  hC := S.coeff_unit
  P xs := ⟨S.alice xs, S.alice_pos xs, S.alice_total xs⟩
  Q ys := ⟨S.bob ys, S.bob_pos ys, S.bob_total ys⟩
  V := G.accepts
end Strategy

lemma sum_profiles {I : Type u_I} {X : Type u_X} {Y : Type u_Y} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]
    (f : (I→X×Y) → ℝ) :
    (∑ z, f z) = ∑ xs : I → X, ∑ ys : I → Y, f (fun i => (xs i,ys i)) := by
  let e : (I→X×Y) ≃ (I→X)×(I→Y) := {
    toFun := fun z => (fun i => (z i).1, fun i => (z i).2)
    invFun := fun t i => (t.1 i,t.2 i)
    left_inv := fun z => by funext i; exact Prod.eta _
    right_inv := fun t => by rcases t with ⟨xs,ys⟩; rfl }
  calc
    (∑ z, f z) = ∑ t : (I→X)×(I→Y), f (e.symm t) := (e.symm.sum_comp f).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

namespace Strategy
variable {x y a b k : ℕ} (S : RepeatedStrategy x y a b k) (G : Game x y a b)
lemma rate_eq_wins [Nonempty (Fin k)] (z : Profile (Fin k) (Fin (x+1)) (Fin (y+1)))
    (as : Fin k → Fin (a+1)) (bs : Fin k → Fin (b+1)) :
    Tests.rate (S.repetitionModel G).winsAt (z,as,bs) =
      (wins G (fun i => (z i).1) (fun i => (z i).2) as bs : ℝ)/(k : ℝ) := by
  rw [Tests.rate, uniform_avg, Fintype.card_fin, one_div, inv_mul_eq_div]
  congr 1
  unfold wins
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl; intro i _
  change (if G.accepts (z i).1 (z i).2 (as i) (bs i) then (1:ℝ) else 0) = _
  split_ifs <;> norm_num

lemma threshold_eq_model [Nonempty (Fin k)] (hk : 0 < k) (δ : ℝ) :
    thresholdProbability G δ S =
      Tests.threshold (S.repetitionModel G).joint
        (S.repetitionModel G).winsAt (entangledValue G+δ) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  symm
  unfold Tests.threshold
  rw [RepeatedModel.joint_avg]
  simp only [S.rate_eq_wins G, le_div_iff₀ hk', ← Nat.ceil_le]
  simp only [avg, pi, RepeatedModel.answers, outcomeLaw, Strategy.repetitionModel,
    smul_eq_mul, Fintype.sum_prod_type]
  rw [sum_profiles]
  unfold thresholdProbability
  apply Finset.sum_congr rfl; intro xs _
  apply Finset.sum_congr rfl; intro ys _
  congr 1
  apply Finset.sum_congr rfl; intro as _
  apply Finset.sum_congr rfl; intro bs _
  rw [S.born_eq_prob]
  split_ifs <;> simp
end Strategy
end ThresholdParallelRepetition

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder
namespace ThresholdParallelRepetition

theorem threshold_parallel_repetition_oai :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (x y a b : ℕ) (G : Game x y a b), entangledValue G < 1 →
      ∀ (δ : ℝ), 0 < δ → δ < 1 - entangledValue G →
      ∀ (k : ℕ), 1 ≤ k →
        (∀ S : RepeatedStrategy x y a b k,
          thresholdProbability G δ S ≤
            Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k)) ∧
        thresholdValue (k := k) G δ ≤
          Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k) := by
  refine ⟨((2:ℝ)^101)⁻¹, by positivity, ?_⟩
  intro x y a b G _ δ hδ hδv k hk
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hs : entangledValue G+δ ≤ 1 := by linarith
  have hstrategy : ∀ S : RepeatedStrategy x y a b k,
      thresholdProbability G δ S ≤
        Real.exp (-((2:ℝ)^101)⁻¹ * δ^13 / (1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))*k) := by
    intro S
    rw [S.threshold_eq_model G (by omega) δ]
    have hh := (S.repetitionModel G).threshold_exp_bound G rfl rfl hδ hs
    simp only [Fintype.card_fin] at hh
    refine hh.trans_eq ?_
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨hstrategy, ?_⟩
  unfold thresholdValue
  apply csSup_le
  · let S : RepeatedStrategy x y a b k := Strategy.deterministic (fun _ => 0) (fun _ => 0)
    exact ⟨_, Set.mem_range_self S⟩
  · rintro _ ⟨S,rfl⟩
    exact hstrategy S

end ThresholdParallelRepetition

end

end OAI
end
end

theorem solution : type_of% @OAI.ThresholdParallelRepetition.threshold_parallel_repetition_oai := @OAI.ThresholdParallelRepetition.threshold_parallel_repetition_oai
