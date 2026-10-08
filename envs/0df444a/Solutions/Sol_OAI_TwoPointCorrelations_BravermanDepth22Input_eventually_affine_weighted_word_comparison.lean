-- Prove2me | solution 1 for OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_affine_weighted_word_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:23:39.238428+00:00
-- url     : https://prove2.me/submissions/abc4f96b-7e78-47c3-a828-cae12b1420a5

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueCounts
namespace OAI

/-!
# Residue counts on arbitrary finite consecutive intervals

An interval is represented by its starting residue `A` and its length `N`.
Thus this includes arbitrary translates, including intervals starting at
negative integers. We prove the exact quotient-and-remainder count, the
one-count discrepancy, and the total-variation estimate used by the finite
residue comparison in the manuscript.
-/

namespace TwoPointCorrelations

open _root_.Finset


lemma residueCount_add {D : ℕ} [NeZero D] (A : ZMod D) (M N : ℕ) (r : ZMod D) :
    residueCount A (M + N) r = residueCount A M r + residueCount (A + (M : ZMod D)) N r := by
  unfold residueCount
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.cast_add, add_assoc]

lemma residueCount_period {D : ℕ} [NeZero D] (A r : ZMod D) :
    residueCount A D r = 1 := by
  unfold residueCount
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin D ≃ ZMod D :=
    { toFun := fun i => (i.val : ZMod D)
      invFun := fun z => ⟨z.val, z.val_lt⟩
      left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := fun z => ZMod.natCast_zmod_val z }
  change (∑ i : Fin D, (fun z : ZMod D => if A + z = r then (1 : ℕ) else 0) (e i)) = 1
  rw [e.sum_comp (fun z : ZMod D => if A + z = r then (1 : ℕ) else 0)]
  have htest (j : ZMod D) : A + j = r ↔ j = r - A := by
    constructor
    · intro h
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using h
    · intro h
      rw [h]
      ring
  simp_rw [htest]
  simp

lemma residueCount_multiple {D : ℕ} [NeZero D] (A r : ZMod D) (k : ℕ) :
    residueCount A (D * k) r = k := by
  induction k with
  | zero => simp [residueCount]
  | succ k ih =>
      rw [Nat.mul_succ, residueCount_add, ih, residueCount_period]

lemma residueCount_short {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ)
    (hN : N ≤ D) : residueCount A N r = if (r - A).val < N then 1 else 0 := by
  unfold residueCount
  have htest (j : ℕ) (hj : j ∈ Finset.range N) :
      A + (j : ZMod D) = r ↔ j = (r - A).val := by
    have hjD : j < D := (Finset.mem_range.mp hj).trans_le hN
    constructor
    · intro h
      have heq : (j : ZMod D) = r - A := by
        apply eq_sub_iff_add_eq.mpr
        simpa [add_comm] using h
      have hv := congrArg ZMod.val heq
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hjD] using hv
    · intro h
      rw [h, ZMod.natCast_zmod_val]
      ring
  calc
    (∑ j ∈ Finset.range N, if A + (j : ZMod D) = r then 1 else 0) =
        ∑ j ∈ Finset.range N, if j = (r - A).val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [htest j hj]
    _ = if (r - A).val < N then 1 else 0 := by simp

/-- Exact residue count on an arbitrary translated interval. -/
theorem residueCount_exact {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ) :
    residueCount A N r = N / D + if (r - A).val < N % D then 1 else 0 := by
  have hsplit := residueCount_add A (D * (N / D)) (N % D) r
  have hN : D * (N / D) + N % D = N := Nat.div_add_mod N D
  rw [hN, residueCount_multiple] at hsplit
  simpa only [Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    residueCount_short A r (N % D) (Nat.le_of_lt (Nat.mod_lt N (NeZero.pos D)))] using hsplit

/-- The count differs from interval length divided by modulus by at most one. -/
theorem residueCount_discrepancy {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ) :
    |(residueCount A N r : ℝ) - (N : ℝ) / D| ≤ 1 := by
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hrem₀ : (0 : ℝ) ≤ ((N % D : ℕ) : ℝ) := by positivity
  have hrem₁ : ((N % D : ℕ) : ℝ) < D := by exact_mod_cast Nat.mod_lt N (NeZero.pos D)
  have hdiv₀ : (0 : ℝ) ≤ ((N % D : ℕ) : ℝ) / D := div_nonneg hrem₀ hD.le
  have hdiv₁ : ((N % D : ℕ) : ℝ) / D < 1 := (div_lt_one hD).mpr hrem₁
  have hquot : (N : ℝ) / D = (N / D : ℕ) + ((N % D : ℕ) : ℝ) / D := by
    have hN : (N : ℝ) = (D : ℝ) * (N / D : ℕ) + (N % D : ℕ) := by
      exact_mod_cast (Nat.div_add_mod N D).symm
    apply (div_eq_iff hD.ne').mpr
    field_simp
    nlinarith [hN]
  rw [residueCount_exact, Nat.cast_add, hquot]
  split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero] <;> rw [abs_le] <;>
    constructor <;> linarith




lemma residueProbability_discrepancy {D : ℕ} [NeZero D] (A r : ZMod D)
    (N : ℕ) (hN : 0 < N) : |residueProbability A N r - 1 / (D : ℝ)| ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne D
  have heq : residueProbability A N r - 1 / (D : ℝ) =
      ((residueCount A N r : ℝ) - (N : ℝ) / D) / N := by
    unfold residueProbability
    field_simp
  rw [heq, abs_div, abs_of_pos hN']
  exact div_le_div_of_nonneg_right (residueCount_discrepancy A r N) hN'.le


/-- The stronger `D/(2N)` bound implies the `D/N` estimate used in the paper. -/
theorem residueTotalVariation_le {D : ℕ} [NeZero D] (A : ZMod D)
    (N : ℕ) (hN : 0 < N) : residueTotalVariation A N ≤ (D : ℝ) / (2 * N) := by
  unfold residueTotalVariation
  have hsum : (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) ≤
      (D : ℝ) / N := by
    calc
      (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) ≤
          ∑ _r : ZMod D, 1 / (N : ℝ) :=
        Finset.sum_le_sum (fun r _ => residueProbability_discrepancy A r N hN)
      _ = (D : ℝ) / N := by simp [ZMod.card, nsmul_eq_mul, div_eq_mul_inv]
  have := div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)
  convert (preTransparency := .instances) this using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CRTComparison
namespace OAI

/-!
# Finite CRT marginals and contraction under independent randomization

A selected finite set of pairwise coprime residue coordinates has the law
of one residue modulo their product. The exact interval count from
`ResidueCounts` gives total variation at most `D / (2N)`. Applying any
finite stochastic kernel preserves this bound; in particular one may add
independent finite randomness and project to any selected encoded bits.
These are the finite arithmetic and data-processing steps in `q:crt-bits`.
-/

open _root_.Finset

namespace TwoPointCorrelations






/-- A bounded observable has expectation difference at most twice TV. -/
lemma finite_observable_difference {α : Type*} [Fintype α]
    (f g u : α → ℝ) (hu : ∀ x, |u x| ≤ 1) :
    |(∑ x, f x * u x) - ∑ x, g x * u x| ≤ 2 * finiteTotalVariation f g := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, (f x * u x - g x * u x)| = |∑ x, (f x - g x) * u x| := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, |(f x - g x) * u x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |f x - g x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hu x)
    _ = 2 * finiteTotalVariation f g := by unfold finiteTotalVariation; ring








/-- This CRT-transported mass is the actual empirical joint residue law. -/
lemma crtJointProbability_eq_count {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (r : ∀ i, ZMod (s i)) :
    crtJointProbability s hcop A N r =
      (∑ j ∈ Finset.range N,
        if ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))) = r
          then (1 : ℝ) else 0) / N := by
  unfold crtJointProbability residueProbability residueCount
  rw [Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have heq : A + (j : ZMod (∏ i, s i)) = (ZMod.prodEquivPi s hcop).symm r ↔
      ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))) = r :=
    (ZMod.prodEquivPi s hcop).toEquiv.eq_symm_apply
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, heq]




lemma crtJointProbability_totalVariation {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) :
    finiteTotalVariation (crtJointProbability s hcop A N) (crtUniform s) =
      residueTotalVariation A N := by
  unfold finiteTotalVariation crtJointProbability crtUniform residueTotalVariation
  congr 1
  exact (ZMod.prodEquivPi s hcop).symm.toEquiv.sum_comp
    (fun z => |residueProbability A N z - 1 / (∏ i, s i : ℕ)|)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]

lemma uniformAverage_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : uniformAverage (fun x => f (e x)) = uniformAverage f := by
  unfold uniformAverage
  rw [e.sum_comp, Fintype.card_congr e]

lemma uniformAverage_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformAverage (fun x : α × β => f x.1 x.2) =
      uniformAverage (fun x => uniformAverage (f x)) := by
  unfold uniformAverage
  rw [Fintype.sum_prod_type', Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div]
  rw [div_div]
  congr 1
  ring

/-- A uniform independent family restricted to selected coordinates remains
uniform; coordinates outside the selection integrate out exactly. -/
lemma uniformAverage_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)] (S : Finset ι)
    (f : (∀ i : S, β i) → ℝ) :
    uniformAverage (fun x : ∀ i, β i => f (fun i : S => x i)) = uniformAverage f := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) β
  calc
    _ = uniformAverage (fun x : (∀ i : S, β i) × (∀ i : {i // i ∉ S}, β i) => f x.1) :=
      uniformAverage_equiv e (fun x => f x.1)
    _ = uniformAverage f := by
      rw [uniformAverage_prod (fun (x : ∀ i : S, β i)
        (_y : ∀ i : {i // i ∉ S}, β i) => f x)]
      simp only [uniformAverage_const]

lemma abs_uniformAverage_le_one {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : |uniformAverage f| ≤ 1 := by
  unfold uniformAverage
  rw [abs_div, show |(Fintype.card α : ℝ)| = (Fintype.card α : ℝ) from
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    |∑ x, f x| / (Fintype.card α : ℝ) ≤
        (∑ x, |f x|) / (Fintype.card α : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ (∑ _x : α, (1 : ℝ)) / (Fintype.card α : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hf x)) (Nat.cast_nonneg _)
    _ ≤ 1 := by simp [div_self_le_one]

/-- Grouping an interval average by its actual CRT residue vector. -/
lemma crtJointProbability_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (F : (∀ i, ZMod (s i)) → ℝ) :
    (∑ r, crtJointProbability s hcop A N r * F r) =
      uniformAverage (fun j : Fin N =>
        F (ZMod.prodEquivPi s hcop (A + (j.val : ZMod (∏ i, s i))))) := by
  simp_rw [crtJointProbability_eq_count, div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold uniformAverage
  rw [Fintype.card_fin]
  congr 1
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => F (ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))))) N).symm

lemma crtUniform_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] (F : (∀ i, ZMod (s i)) → ℝ) :
    (∑ r, crtUniform s r * F r) = uniformAverage F := by
  unfold crtUniform uniformAverage
  rw [← Finset.mul_sum]
  simp only [Fintype.card_pi, ZMod.card, Nat.cast_prod]
  ring

/-- Uniform translated interval averages of any bounded observable of the
selected residue coordinates differ from the product law by at most `D/N`. -/
theorem crt_observable_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (hN : 0 < N)
    (F : (∀ i, ZMod (s i)) → ℝ) (hF : ∀ r, |F r| ≤ 1) :
    |uniformAverage (fun j : Fin N =>
        F (ZMod.prodEquivPi s hcop (A + (j.val : ZMod (∏ i, s i))))) -
      uniformAverage F| ≤ (∏ i, s i : ℕ) / (N : ℝ) := by
  have h := finite_observable_difference (crtJointProbability s hcop A N) (crtUniform s) F hF
  rw [crtJointProbability_expectation, crtUniform_expectation] at h
  calc
    _ ≤ 2 * finiteTotalVariation (crtJointProbability s hcop A N) (crtUniform s) := h
    _ = 2 * residueTotalVariation A N := by rw [crtJointProbability_totalVariation]
    _ ≤ 2 * ((∏ i, s i : ℕ) / (2 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (residueTotalVariation_le A N hN) (by norm_num)
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.AffineResidueAverage
namespace OAI

/-! Freeze a progression class and change every prime residue by the
same invertible affine map. This preserves the precise uniform model. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

lemma uniformAverage_residue_affine {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (a l : ℕ) (hl : ∀ i, l.Coprime (s i)) (F : (∀ i, ZMod (s i)) → ℝ) :
    uniformAverage (fun z : ∀ i, ZMod (s i) =>
      F (fun i => (a : ZMod (s i)) + (l : ZMod (s i)) * z i)) =
      uniformAverage F := by
  let e : (∀ i, ZMod (s i)) ≃ (∀ i, ZMod (s i)) := Equiv.piCongrRight fun i =>
    (Units.mulLeft (ZMod.unitOfCoprime l (hl i))).trans (Equiv.addLeft (a : ZMod (s i)))
  have he (z : ∀ i, ZMod (s i)) : e z =
      fun i => (a : ZMod (s i)) + (l : ZMod (s i)) * z i := by
    funext i
    change (a : ZMod (s i)) + (ZMod.unitOfCoprime l (hl i) : ZMod (s i)) * z i = _
    rw [ZMod.coe_unitOfCoprime]
  simpa only [he] using uniformAverage_equiv e F

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection
namespace OAI

/-!
# Correcting an almost independent Boolean density

This is the finite Fourier correction used in the proof of the manuscript's
finite-residue comparison (`q:finite-law`, `q:fourier-correction-tv`). The
construction removes the chosen nonconstant Walsh coefficients and adds the
constant `a` before normalization, retaining pointwise nonnegativity.
-/

namespace TwoPointCorrelations

open _root_.Finset




lemma cubeAverage_sub {n : ℕ} (f g : BooleanCube n → ℝ) :
    cubeAverage (fun x => f x - g x) = cubeAverage f - cubeAverage g := by
  simp [cubeAverage, Finset.sum_sub_distrib, sub_div]



lemma cubeAverage_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → BooleanCube n → ℝ) :
    cubeAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeAverage (f i) := by
  simp only [cubeAverage, Finset.sum_div]
  rw [Finset.sum_comm]

lemma cubeAverage_mono {n : ℕ} {f g : BooleanCube n → ℝ}
    (h : ∀ x, f x ≤ g x) : cubeAverage f ≤ cubeAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)


@[simp] lemma booleanSign_not (b : Bool) : booleanSign (!b) = -booleanSign b := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma booleanSign_sq (b : Bool) : booleanSign b * booleanSign b = 1 := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma abs_booleanSign (b : Bool) : |booleanSign b| = 1 := by
  cases b <;> norm_num [booleanSign]



@[simp] lemma abs_walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    |walsh S x| = 1 := by
  simp [walsh, Finset.abs_prod]

@[simp] lemma walsh_mul_self {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh S x = 1 := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  simp


lemma walsh_flipBit {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (x : BooleanCube n) :
    walsh S (flipBit i x) = if i ∈ S then -walsh S x else walsh S x := by
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hrest : (∏ j ∈ S.erase i, booleanSign ((flipBit i x) j)) =
        ∏ j ∈ S.erase i, booleanSign (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [flipBit, Function.update_of_ne (mem_erase.mp hj).1]
    unfold walsh
    rw [← Finset.prod_erase_mul _ _ hi, hrest,
      ← Finset.prod_erase_mul _ (fun j => booleanSign (x j)) hi]
    simp [flipBit]
  · rw [if_neg hi]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    simp [flipBit, Function.update_of_ne hji]

lemma cubeAverage_eq_zero_of_flip {n : ℕ} (f : BooleanCube n → ℝ) (i : Fin n)
    (hf : ∀ x, f (flipBit i x) = -f x) : cubeAverage f = 0 := by
  have hsum : (∑ x, f (flipBit i x)) = ∑ x, f x :=
    (flipBit i).sum_comp f
  simp_rw [hf] at hsum
  rw [Finset.sum_neg_distrib] at hsum
  have hz : (∑ x, f x) = 0 := by linarith
  simp [cubeAverage, hz]

lemma cubeAverage_walsh {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) :
    cubeAverage (walsh S) = 0 := by
  obtain ⟨i, hi⟩ := hS
  apply cubeAverage_eq_zero_of_flip _ i
  intro x
  simp [walsh_flipBit, hi]

lemma cubeAverage_walsh_mul {n : ℕ} (S T : Finset (Fin n)) :
    cubeAverage (fun x => walsh S x * walsh T x) = if S = T then 1 else 0 := by
  classical
  by_cases hST : S = T
  · subst T; simp
  · rw [if_neg hST]
    have hex : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      simpa only [Finset.ext_iff, not_forall] using hST
    obtain ⟨i, hi⟩ := hex
    apply cubeAverage_eq_zero_of_flip _ i
    intro x
    by_cases hSi : i ∈ S
    · have hTi : i ∉ T := fun h => hi ⟨fun _ => h, fun _ => hSi⟩
      simp [walsh_flipBit, hSi, hTi]
    · have hTi : i ∈ T := by
        by_contra hnot
        apply hi
        simp [hSi, hnot]
      simp [walsh_flipBit, hSi, hTi]





lemma cubeAverage_lowWalshCorrection {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) :
    cubeAverage (lowWalshCorrection f t) = 0 := by
  change cubeAverage (fun x => ∑ S ∈ lowWalshSets n t, walshCoefficient f S * walsh S x) = 0
  rw [cubeAverage_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [cubeAverage_mul_const, cubeAverage_walsh (mem_filter.mp hS).2.1, mul_zero]

lemma lowWalshCorrection_abs_le {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (x : BooleanCube n) : |lowWalshCorrection f t x| ≤ lowWalshMass f t := by
  unfold lowWalshCorrection lowWalshMass
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  simp

lemma lowWalshCorrection_coefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (S : Finset (Fin n)) (hS : S ∈ lowWalshSets n t) :
    cubeAverage (fun x => lowWalshCorrection f t x * walsh S x) = walshCoefficient f S := by
  simp only [lowWalshCorrection, Finset.sum_mul]
  rw [cubeAverage_sum]
  simp_rw [mul_assoc, cubeAverage_mul_const, cubeAverage_walsh_mul]
  simp [hS]


lemma correctedCubeDensity_nonneg {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) (a : ℝ)
    (hf : ∀ x, 0 ≤ f x) (ha : 0 ≤ a) (hmass : lowWalshMass f t ≤ a) :
    ∀ x, 0 ≤ correctedCubeDensity f t a x := by
  intro x
  apply div_nonneg _ (by linarith)
  have hH := (le_abs_self (lowWalshCorrection f t x)).trans
    ((lowWalshCorrection_abs_le f t x).trans hmass)
  linarith [hf x]

lemma cubeAverage_correctedCubeDensity {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (hf : cubeAverage f = 1) (ha : 0 ≤ a) :
    cubeAverage (correctedCubeDensity f t a) = 1 := by
  have hden : 1 + a ≠ 0 := by linarith
  unfold correctedCubeDensity
  simp only [div_eq_mul_inv]
  simp_rw [mul_comm _ (1 + a)⁻¹]
  rw [cubeAverage_mul_const, cubeAverage_add, cubeAverage_sub,
    hf, cubeAverage_lowWalshCorrection, cubeAverage_const]
  field_simp
  ring

lemma correctedCubeDensity_coefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (S : Finset (Fin n)) (hS : S ∈ lowWalshSets n t) :
    walshCoefficient (correctedCubeDensity f t a) S = 0 := by
  unfold walshCoefficient correctedCubeDensity
  have heq : (fun x => (f x - lowWalshCorrection f t x + a) / (1 + a) * walsh S x) =
      fun x => (1 + a)⁻¹ *
        ((f x * walsh S x - lowWalshCorrection f t x * walsh S x) + a * walsh S x) := by
    funext x
    ring
  rw [heq, cubeAverage_mul_const, cubeAverage_add, cubeAverage_sub,
    lowWalshCorrection_coefficient f t S hS, cubeAverage_mul_const,
    cubeAverage_walsh (mem_filter.mp hS).2.1]
  change (1 + a)⁻¹ * (walshCoefficient f S - walshCoefficient f S + a * 0) = 0
  ring

/-- Total variation from the initial density is at most `3a/2`. -/
theorem correctedCubeDensity_totalVariation_le {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (hf : ∀ x, 0 ≤ f x) (hmean : cubeAverage f = 1)
    (ha : 0 ≤ a) (hmass : lowWalshMass f t ≤ a) :
    cubeAverage (fun x => |correctedCubeDensity f t a x - f x|) / 2 ≤ 3 * a / 2 := by
  have hden : 0 < 1 + a := by linarith
  have hpoint (x : BooleanCube n) :
      |correctedCubeDensity f t a x - f x| ≤ a * (2 + f x) := by
    have hdiff : correctedCubeDensity f t a x - f x =
        (-lowWalshCorrection f t x + a * (1 - f x)) / (1 + a) := by
      unfold correctedCubeDensity
      field_simp
      ring
    rw [hdiff, abs_div, abs_of_pos hden]
    apply (div_le_self (abs_nonneg _) (by linarith : 1 ≤ 1 + a)).trans
    have hH := (lowWalshCorrection_abs_le f t x).trans hmass
    have hF : |1 - f x| ≤ 1 + f x := by
      rw [abs_le]
      constructor <;> linarith [hf x]
    calc
      |-lowWalshCorrection f t x + a * (1 - f x)| ≤
          |lowWalshCorrection f t x| + a * |1 - f x| := by
        simpa [abs_mul, abs_of_nonneg ha] using
          abs_add_le (-lowWalshCorrection f t x) (a * (1 - f x))
      _ ≤ a + a * (1 + f x) := add_le_add hH (mul_le_mul_of_nonneg_left hF ha)
      _ = a * (2 + f x) := by ring
  have hav := cubeAverage_mono hpoint
  rw [cubeAverage_mul_const, cubeAverage_add, cubeAverage_const, hmean] at hav
  linarith


/-- Finite Walsh inversion of a cylinder indicator. -/
lemma cubePattern_walsh_expansion {n : ℕ} (S : Finset (Fin n))
    (z x : BooleanCube n) :
    (2 : ℝ) ^ S.card * cubePattern S z x =
      ∑ T ∈ S.powerset, walsh T z * walsh T x := by
  have hcoord (i : Fin n) : 1 + booleanSign (z i) * booleanSign (x i) =
      if x i = z i then (2 : ℝ) else 0 := by
    cases hx : x i <;> cases hz : z i <;> norm_num [booleanSign, hx, hz]
  have hprod : (∏ i ∈ S, (1 + booleanSign (z i) * booleanSign (x i))) =
      (2 : ℝ) ^ S.card * cubePattern S z x := by
    by_cases h : ∀ i ∈ S, x i = z i
    · calc
        (∏ i ∈ S, (1 + booleanSign (z i) * booleanSign (x i))) =
            ∏ _i ∈ S, (2 : ℝ) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [hcoord, if_pos (h i hi)]
        _ = (2 : ℝ) ^ S.card * cubePattern S z x := by
          rw [cubePattern, if_pos h]
          simp
    · have hex : ∃ i ∈ S, x i ≠ z i := by
        push Not at h
        exact h
      obtain ⟨i, hi, hneq⟩ := hex
      have hz : (∏ i ∈ S, (1 + booleanSign (z i) * booleanSign (x i))) = 0 := by
        apply Finset.prod_eq_zero hi
        rw [hcoord, if_neg hneq]
      simp [hz, cubePattern, h]
  rw [← hprod, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.prod_mul_distrib]
  rfl

/-- Vanishing of all nonconstant Walsh coefficients on a coordinate set makes
that marginal exactly uniform. -/
lemma cubeAverage_pattern_of_walsh {n : ℕ} (g : BooleanCube n → ℝ)
    (S : Finset (Fin n)) (z : BooleanCube n) (hmean : cubeAverage g = 1)
    (hcoeff : ∀ T ⊆ S, T.Nonempty → walshCoefficient g T = 0) :
    cubeAverage (fun x => g x * cubePattern S z x) = 1 / (2 : ℝ) ^ S.card := by
  have hsum : (∑ T ∈ S.powerset, walsh T z * walshCoefficient g T) = 1 := by
    rw [Finset.sum_eq_single ∅]
    · simpa [walshCoefficient] using hmean
    · intro T hT hne
      rw [hcoeff T (mem_powerset.mp hT) (Finset.nonempty_iff_ne_empty.mpr hne), mul_zero]
    · simp
  have hscale : (2 : ℝ) ^ S.card * cubeAverage (fun x => g x * cubePattern S z x) = 1 := by
    calc
      (2 : ℝ) ^ S.card * cubeAverage (fun x => g x * cubePattern S z x) =
          cubeAverage (fun x => (2 : ℝ) ^ S.card * (g x * cubePattern S z x)) :=
        (cubeAverage_mul_const _ _).symm
      _ = cubeAverage (fun x => ∑ T ∈ S.powerset,
          walsh T z * (g x * walsh T x)) := by
        congr 1
        funext x
        rw [mul_left_comm, cubePattern_walsh_expansion, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      _ = ∑ T ∈ S.powerset, walsh T z * walshCoefficient g T := by
        rw [cubeAverage_sum]
        apply Finset.sum_congr rfl
        intro T hT
        exact cubeAverage_mul_const _ _
      _ = 1 := hsum
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).mpr
  nlinarith only [hscale]


lemma correctedCubeDensity_tWiseUniform {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (hmean : cubeAverage f = 1) (ha : 0 ≤ a) :
    TWiseUniformDensity (correctedCubeDensity f t a) t := by
  intro S hS z
  apply cubeAverage_pattern_of_walsh _ S z (cubeAverage_correctedCubeDensity f t a hmean ha)
  intro T hTS hT
  apply correctedCubeDensity_coefficient
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ T,
    hT, (Finset.card_le_card hTS).trans hS⟩

/-- The complete finite correction used before applying Braverman's theorem. -/
theorem fourierCorrection {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) (a : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hmean : cubeAverage f = 1)
    (ha : 0 ≤ a) (hmass : lowWalshMass f t ≤ a) :
    (∀ x, 0 ≤ correctedCubeDensity f t a x) ∧
      cubeAverage (correctedCubeDensity f t a) = 1 ∧
      TWiseUniformDensity (correctedCubeDensity f t a) t ∧
      cubeAverage (fun x => |correctedCubeDensity f t a x - f x|) / 2 ≤ 3 * a / 2 :=
  ⟨correctedCubeDensity_nonneg f t a hf ha hmass,
    cubeAverage_correctedCubeDensity f t a hmean ha,
    correctedCubeDensity_tWiseUniform f t a hmean ha,
    correctedCubeDensity_totalVariation_le f t a hf hmean ha hmass⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SampleDensity
namespace OAI

/-! Exact densities on the Boolean cube induced by a finite sampling map. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma sampleDensity_nonneg {α : Type*} [Fintype α] {n : ℕ}
    (sample : α → BooleanCube n) (x : BooleanCube n) : 0 ≤ sampleDensity sample x := by
  unfold sampleDensity
  positivity

/-- Expectations against the induced density are exactly empirical averages. -/
lemma sampleDensity_expectation {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (sample : α → BooleanCube n) (F : BooleanCube n → ℝ) :
    cubeAverage (fun x => sampleDensity sample x * F x) =
      uniformAverage (fun a => F (sample a)) := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcube : (Fintype.card (BooleanCube n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ x : BooleanCube n,
      (∑ a, if sample a = x then (1 : ℝ) else 0) * F x) = ∑ a, F (sample a) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  unfold cubeAverage sampleDensity uniformAverage
  calc
    _ = ((Fintype.card (BooleanCube n) : ℝ) / Fintype.card α *
        (∑ x : BooleanCube n, (∑ a, if sample a = x then (1 : ℝ) else 0) * F x)) /
          Fintype.card (BooleanCube n) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [hsum]; field_simp

lemma sampleDensity_mean {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (sample : α → BooleanCube n) : cubeAverage (sampleDensity sample) = 1 := by
  simpa using sampleDensity_expectation sample (fun _ => 1)

lemma sampleDensity_walshCoefficient {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (sample : α → BooleanCube n) (S : Finset (Fin n)) :
    walshCoefficient (sampleDensity sample) S = uniformAverage (fun a => walsh S (sample a)) :=
  sampleDensity_expectation sample (walsh S)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.BitEncoding
namespace OAI

/-!
# Exact finite jitter encoding

For `Q = 2^B`, the integer code `⌊(r Q + j)/s⌋`, with `j` uniform in
`{0,…,Q-1}`, has exactly the distribution of the first `B` binary digits
of `(r + U)/s` for uniform `U` in `[0,1)`. This finite construction avoids
continuous auxiliary probability spaces. Jointly uniform residue and
jitter give a uniform code. Decoding can fail for at most `s` jitter values
at each fixed residue, giving the stronger bound `s/Q`.
-/

open _root_.Finset

namespace TwoPointCorrelations



lemma jitterCode_val {s Q : ℕ} (r : Fin s) (j : Fin Q) :
    (jitterCode r j).val = (j.val + Q * r.val) / s := rfl




/-- All jitter positions outside the first `s` positions decode correctly. -/
lemma jitterDecode_code {s Q : ℕ} (hs : 0 < s) (hQ : 0 < Q)
    (r : Fin s) (j : Fin Q) (hj : s ≤ j.val) :
    jitterDecode hs hQ (jitterCode r j) = r := by
  apply Fin.ext
  change s * (jitterCode r j).val / Q = r.val
  rw [jitterCode_val]
  have hmod := Nat.mod_lt (j.val + Q * r.val) hs
  have hsplit := Nat.mod_add_div (j.val + Q * r.val) s
  have hmod0 := Nat.zero_le ((j.val + Q * r.val) % s)
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · have hjQ := j.isLt
    nlinarith

/-- Conditional decoding error for every fixed residue, independent of the
law from which that residue was sampled. -/
theorem jitterDecode_error {s Q : ℕ} (hs : 0 < s) (hQ : 0 < Q) (r : Fin s) :
    (∑ j : Fin Q, if jitterDecode hs hQ (jitterCode r j) ≠ r then (1 : ℝ) else 0) /
        (Q : ℝ) ≤ (s : ℝ) / Q := by
  let E : Finset (Fin Q) := Finset.univ.filter
    (fun j => jitterDecode hs hQ (jitterCode r j) ≠ r)
  have hsmall (j : E) : j.val.val < s := by
    have he := (Finset.mem_filter.mp j.property).2
    by_contra h
    exact he (jitterDecode_code hs hQ r j.val (Nat.le_of_not_gt h))
  let emb : E → Fin s := fun j => ⟨j.val.val, hsmall j⟩
  have hinj : Function.Injective emb := by
    intro j k h
    apply Subtype.ext
    apply Fin.ext
    simpa only [emb] using congrArg (fun z : Fin s => z.val) h
  have hcard : E.card ≤ s := by
    simpa using Fintype.card_le_of_injective emb hinj
  have hsum : (∑ j : Fin Q,
      if jitterDecode hs hQ (jitterCode r j) ≠ r then (1 : ℝ) else 0) = (E.card : ℝ) := by
    exact Finset.sum_boole _ _
  rw [hsum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg Q)
  exact_mod_cast hcard




@[simp] lemma decode_jitterBits {s B : ℕ} (hs : 0 < s) (r : Fin s) (j : Fin (2 ^ B)) :
    decodeBits hs (jitterBits r j) = jitterDecode hs (by positivity) (jitterCode r j) := by
  simp [decodeBits, jitterBits]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.BitMarginals
namespace OAI

/-!
# Joint finite jitter and independent uniform bit blocks

The permutation underlying one-coordinate jitter acts independently in
every coordinate. This proves exact joint uniformity before selecting any
bits; together with CRT contraction it gives finite quantitative marginal
comparison, including arbitrary fixed non-squarefree moduli.
-/

namespace TwoPointCorrelations

open _root_.Finset




lemma jointJitterCode_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) (Q : ℕ) (F : (ι → Fin Q) → ℝ) :
    (∑ r : ∀ i, Fin (s i), ∑ j : ι → Fin Q, F (jointJitterCode r j)) =
      (∏ i, s i : ℕ) * ∑ k : ι → Fin Q, F k := by
  rw [← Fintype.sum_prod_type']
  change (∑ x : (∀ i, Fin (s i)) × (ι → Fin Q),
    (fun y : (ι → Fin Q) × (∀ i, Fin (s i)) => F y.1) (jointJitterPermutation s Q x)) = _
  rw [(jointJitterPermutation s Q).sum_comp
    (fun y : (ι → Fin Q) × (∀ i, Fin (s i)) => F y.1), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum]

/-- Exact uniformity of all code coordinates under uniform residues. -/
lemma jointJitterCode_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] {Q : ℕ} (hQ : 0 < Q) (k : ι → Fin Q) :
    (∑ r : ∀ i, Fin (s i), (1 / (∏ i, s i : ℕ)) *
      finiteRandomKernel (@jointJitterCode ι s Q) r k) =
        1 / (Fintype.card (ι → Fin Q) : ℝ) := by
  let : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hJ : (Fintype.card (ι → Fin Q) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hD : ((∏ i, s i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (∏ i, s i)
  unfold finiteRandomKernel
  rw [← Finset.mul_sum, ← Finset.sum_div]
  rw [jointJitterCode_sum s Q (fun z => if z = k then (1 : ℝ) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp


lemma crtJitterCode_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] {Q : ℕ} (hQ : 0 < Q) (k : ι → Fin Q) :
    kernelTransport (finiteRandomKernel (@crtJitterCode ι s _ Q)) (crtUniform s) k =
      1 / (Fintype.card (ι → Fin Q) : ℝ) := by
  let e : (∀ i, Fin (s i)) ≃ (∀ i, ZMod (s i)) :=
    Equiv.piCongrRight (fun i => (ZMod.finEquiv (s i)).toEquiv)
  calc
    _ = ∑ r : ∀ i, Fin (s i), (1 / (∏ i, s i : ℕ)) *
        finiteRandomKernel (@jointJitterCode ι s Q) r k := by
      unfold kernelTransport crtUniform
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      unfold finiteRandomKernel crtJitterCode
      simp [e]
    _ = _ := jointJitterCode_uniform s hQ k




lemma crtJitterBits_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] (B : ℕ) (x : ι → BooleanCube B) :
    kernelTransport (finiteRandomKernel (crtJitterBits s B)) (crtUniform s) x =
      1 / (Fintype.card (ι → BooleanCube B) : ℝ) := by
  have heq (r : ∀ i, ZMod (s i)) :
      finiteRandomKernel (crtJitterBits s B) r x =
        finiteRandomKernel (@crtJitterCode ι s _ (2 ^ B)) r ((jointBitEquiv ι B).symm x) := by
    unfold finiteRandomKernel
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have heq : crtJitterBits s B r j = x ↔
        crtJitterCode s r j = (jointBitEquiv ι B).symm x := by
      change jointBitEquiv ι B (crtJitterCode s r j) = x ↔ _
      exact (jointBitEquiv ι B).eq_symm_apply.symm
    simp only [heq]
  unfold kernelTransport
  simp_rw [heq]
  change kernelTransport (finiteRandomKernel (@crtJitterCode ι s _ (2 ^ B)))
    (crtUniform s) ((jointBitEquiv ι B).symm x) = _
  rw [crtJitterCode_uniform s (by positivity)]
  rw [Fintype.card_congr (jointBitEquiv ι B)]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitComparison
namespace OAI

/-!
# Bounded-independence circuit comparison after Fourier correction

The comparison uses the fixed-depth specialization of Mark Braverman,
*Polylogarithmic independence fools AC⁰ circuits*, J. ACM 57 (2010), Article 28,
Corollary 2 in the author's version. We use depth 22, with absolute constants
and natural logarithms. Circuits below have actual finite syntax: literals
and arbitrary finite-fan-in AND/OR gates. They are tree circuits, a subclass
of the circuits covered by Braverman's theorem. The size counts both input
occurrences and gates; the depth counts AND/OR levels.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace AC0Circuit




lemma size_pos {n : ℕ} (c : AC0Circuit n) : 0 < c.size := by
  cases c <;> simp [size]


lemma abs_centered_indicator {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) :
    |c.indicator x - 1 / 2| = (1 / 2 : ℝ) := by
  unfold indicator
  cases c.eval x <;> norm_num

end AC0Circuit


lemma abs_cubeAverage_le {n : ℕ} (f : BooleanCube n → ℝ) :
    |cubeAverage f| ≤ cubeAverage (fun x => |f x|) := by
  unfold cubeAverage
  rw [abs_div, show |(Fintype.card (BooleanCube n) : ℝ)| =
    (Fintype.card (BooleanCube n) : ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- For measures of equal total mass, an event difference is bounded by one
half of the mean absolute density difference. -/
lemma circuit_event_le_totalVariation {n : ℕ} (c : AC0Circuit n)
    (f g : BooleanCube n → ℝ) (hmass : cubeAverage f = cubeAverage g) :
    |cubeAverage (fun x => f x * c.indicator x) -
      cubeAverage (fun x => g x * c.indicator x)| ≤
        cubeAverage (fun x => |f x - g x|) / 2 := by
  have hzero : cubeAverage (fun x => f x - g x) = 0 := by
    rw [cubeAverage_sub, hmass, sub_self]
  have heq : cubeAverage (fun x => f x * c.indicator x) -
      cubeAverage (fun x => g x * c.indicator x) =
      cubeAverage (fun x => (f x - g x) * (c.indicator x - 1 / 2)) := by
    have hpoint : (fun x => (f x - g x) * (c.indicator x - 1 / 2)) =
        (fun x => (f x * c.indicator x - g x * c.indicator x) -
          (1 / 2 : ℝ) * (f x - g x)) := by
      funext x
      ring
    rw [hpoint, cubeAverage_sub, cubeAverage_sub, cubeAverage_mul_const, hzero]
    ring
  rw [heq]
  apply (abs_cubeAverage_le _).trans
  have hpoint : (fun x => |(f x - g x) * (c.indicator x - 1 / 2)|) =
      (fun x => (1 / 2 : ℝ) * |f x - g x|) := by
    funext x
    rw [abs_mul, c.abs_centered_indicator]
    ring
  rw [hpoint, cubeAverage_mul_const]
  exact le_of_eq (by ring)

/-- Fourier correction followed by Braverman's published theorem compares
the original density against uniform inputs, with the correction error
made explicit. -/
theorem BravermanDepth22Input.fourier_comparison (hBraverman : BravermanDepth22Input) :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (n : ℕ) (c : AC0Circuit n), c.depth ≤ 22 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∀ (f : BooleanCube n → ℝ) (a : ℝ),
          (∀ x, 0 ≤ f x) → cubeAverage f = 1 → 0 ≤ a → lowWalshMass f t ≤ a →
          |cubeAverage (fun x => f x * c.indicator x) - cubeAverage c.indicator| ≤
            3 * a / 2 + ε := by
  obtain ⟨K, C, hK, hC, hbound⟩ := hBraverman
  refine ⟨K, C, hK, hC, ?_⟩
  intro n c hdepth ε hε hεmax t ht f a hf hmean ha hmass
  let g := correctedCubeDensity f t a
  have hcorr := fourierCorrection f t a hf hmean ha hmass
  have hBrav := hbound n c hdepth ε hε hεmax t ht g hcorr.1 hcorr.2.1 hcorr.2.2.1
  have hTV := circuit_event_le_totalVariation c f g (hmean.trans hcorr.2.1.symm)
  have hTVbound : cubeAverage (fun x => |f x - g x|) / 2 ≤ 3 * a / 2 := by
    simpa only [abs_sub_comm] using hcorr.2.2.2
  calc
    |cubeAverage (fun x => f x * c.indicator x) - cubeAverage c.indicator| ≤
        |cubeAverage (fun x => f x * c.indicator x) -
          cubeAverage (fun x => g x * c.indicator x)| +
        |cubeAverage (fun x => g x * c.indicator x) - cubeAverage c.indicator| :=
      abs_sub_le _ _ _
    _ ≤ 3 * a / 2 + ε := add_le_add (hTV.trans hTVbound) hBrav

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FourierMass
namespace OAI

/-!
# Counting low-order Fourier coefficients

The number of nonempty coordinate sets of order at most `t` is at most
`(t+1)n^t`. Combining individual coefficient bounds with this count gives
the explicit error budget used by finite residue comparison.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma card_lowWalshSets_le {n : ℕ} (hn : 0 < n) (t : ℕ) :
    (lowWalshSets n t).card ≤ (t + 1) * n ^ t := by
  have hsub : lowWalshSets n t ⊆ (Finset.range (t + 1)).biUnion
      (fun k => (Finset.univ : Finset (Fin n)).powersetCard k) := by
    intro S hS
    have ht := (Finset.mem_filter.mp hS).2.2
    apply Finset.mem_biUnion.mpr
    refine ⟨S.card, Finset.mem_range.mpr (by omega), ?_⟩
    simp
  calc
    (lowWalshSets n t).card ≤ ((Finset.range (t + 1)).biUnion
        (fun k => (Finset.univ : Finset (Fin n)).powersetCard k)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (t + 1), ((Finset.univ : Finset (Fin n)).powersetCard k).card :=
      Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range (t + 1), n.choose k := by simp
    _ ≤ ∑ _k ∈ Finset.range (t + 1), n ^ t := by
      apply Finset.sum_le_sum
      intro k hk
      exact (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_right hn (by
        have := Finset.mem_range.mp hk
        omega))
    _ = (t + 1) * n ^ t := by simp

lemma lowWalshMass_le_of_coefficients {n : ℕ} (hn : 0 < n)
    (f : BooleanCube n → ℝ) (t : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hf : ∀ S ∈ lowWalshSets n t, |walshCoefficient f S| ≤ δ) :
    lowWalshMass f t ≤ δ * ((t + 1 : ℕ) : ℝ) * (n : ℝ) ^ t := by
  unfold lowWalshMass
  calc
    (∑ S ∈ lowWalshSets n t, |walshCoefficient f S|) ≤ ∑ _S ∈ lowWalshSets n t, δ :=
      Finset.sum_le_sum hf
    _ = δ * ((lowWalshSets n t).card : ℝ) := by simp [mul_comm]
    _ ≤ δ * (((t + 1) * n ^ t : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast card_lowWalshSets_le hn t) hδ
    _ = _ := by push_cast; ring

/-- The fixed-parameter finite-law consequence of Braverman's theorem:
only the individual low-order Fourier errors and the actual circuit size
and depth occur as hypotheses. -/
theorem BravermanDepth22Input.coefficient_comparison (hBraverman : BravermanDepth22Input) :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∀ (c : AC0Circuit n), c.depth ≤ 22 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∀ (f : BooleanCube n → ℝ) (δ a : ℝ),
          (∀ x, 0 ≤ f x) → cubeAverage f = 1 → 0 ≤ δ →
          (∀ S ∈ lowWalshSets n t, |walshCoefficient f S| ≤ δ) →
          δ * ((t + 1 : ℕ) : ℝ) * (n : ℝ) ^ t ≤ a →
          |cubeAverage (fun x => f x * c.indicator x) - cubeAverage c.indicator| ≤
            3 * a / 2 + ε := by
  obtain ⟨K, C, hK, hC, hbound⟩ := hBraverman.fourier_comparison
  refine ⟨K, C, hK, hC, ?_⟩
  intro n hn c hc ε hε hεmax t ht f δ a hf hmean hδ hcoeff ha
  have hmass := lowWalshMass_le_of_coefficients hn f t δ hδ hcoeff
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  exact hbound n c hc ε hε hεmax t ht f a hf hmean ha0 (hmass.trans ha)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedCoefficients
namespace OAI

/-!
# Low-order coefficients of the actual encoded interval law

A Walsh coefficient only uses the residue coordinates touched by its bits.
All other independent jitters integrate out. The remaining observable is
bounded by one, so CRT gives the product of its selected moduli divided by
the interval length as an explicit coefficient bound.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma finiteRandomKernel_expectation {α β J : Type*} [Fintype β] [DecidableEq β]
    [Fintype J] (F : α → J → β) (u : β → ℝ) (x : α) :
    (∑ y, finiteRandomKernel F x y * u y) = uniformAverage (fun j => u (F x j)) := by
  unfold finiteRandomKernel uniformAverage
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp

lemma kernelTransport_expectation {α β : Type*} [Fintype α] [Fintype β]
    (K : α → β → ℝ) (p : α → ℝ) (u : β → ℝ) :
    (∑ y, kernelTransport K p y * u y) = ∑ x, p x * ∑ y, K x y * u y := by
  unfold kernelTransport
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma crtJitterBits_uniformAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] (B : ℕ)
    (u : (ι → BooleanCube B) → ℝ) :
    uniformAverage (fun r : ∀ i, ZMod (s i) =>
      uniformAverage (fun j : ι → Fin (2 ^ B) => u (crtJitterBits s B r j))) =
        uniformAverage u := by
  rw [← crtUniform_expectation s]
  simp_rw [← finiteRandomKernel_expectation (crtJitterBits s B) u]
  rw [← kernelTransport_expectation]
  simp_rw [crtJitterBits_uniform]
  unfold uniformAverage
  rw [← Finset.mul_sum]
  ring


@[simp] lemma flattenBitBlocks_apply {m B : ℕ} (z : Fin m → BooleanCube B)
    (k : Fin (m * B)) : flattenBitBlocks m B z k = z k.divNat k.modNat := rfl


lemma card_bitSources_le {m B : ℕ} (S : Finset (Fin (m * B))) :
    (bitSources S).card ≤ S.card := Finset.card_image_le

lemma bitSource_mem {m B : ℕ} (S : Finset (Fin (m * B))) {k : Fin (m * B)} (hk : k ∈ S) :
    k.divNat ∈ bitSources S := Finset.mem_image_of_mem _ hk



lemma selectedWalsh_restrict {m B : ℕ} (S : Finset (Fin (m * B)))
    (z : Fin m → BooleanCube B) :
    selectedWalsh S (fun i : bitSources S => z i) = walsh S (flattenBitBlocks m B z) := by
  unfold selectedWalsh walsh
  apply Finset.prod_congr rfl
  intro k hk
  simp only [flattenBitBlocks_apply, extendBitBlocks, dif_pos (bitSource_mem S hk)]

lemma abs_selectedWalsh {m B : ℕ} (S : Finset (Fin (m * B)))
    (z : bitSources S → BooleanCube B) : |selectedWalsh S z| = 1 := abs_walsh _ _



lemma integerBitDensity_nonneg {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B a N : ℕ) (x : BooleanCube (m * B)) : 0 ≤ integerBitDensity s B a N x :=
  sampleDensity_nonneg _ x

lemma integerBitDensity_mean {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B a N : ℕ) (hN : 0 < N) : cubeAverage (integerBitDensity s B a N) = 1 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  exact sampleDensity_mean _


lemma abs_selectedWalshMean_le_one {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (S : Finset (Fin (m * B))) (r : ∀ i : bitSources S, ZMod (s i)) :
    |selectedWalshMean s S r| ≤ 1 := by
  apply abs_uniformAverage_le_one
  intro j
  exact (abs_selectedWalsh _ _).le

lemma crtJitterBits_restrict {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (C : Finset (Fin m)) (r : ∀ i, ZMod (s i)) (j : Fin m → Fin (2 ^ B)) :
    (fun i : C => crtJitterBits s B r j i) =
      crtJitterBits (fun i : C => s i) B (fun i : C => r i) (fun i : C => j i) := rfl

lemma selectedWalshMean_eq_full {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (S : Finset (Fin (m * B))) (r : ∀ i, ZMod (s i)) :
    selectedWalshMean s S (fun i : bitSources S => r i) =
      uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
        walsh S (flattenBitBlocks m B (crtJitterBits s B r j))) := by
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  rw [selectedWalshMean, ← uniformAverage_restrict (fun _ : Fin m => Fin (2 ^ B)) (bitSources S)]
  apply congrArg uniformAverage
  funext j
  rw [← crtJitterBits_restrict, selectedWalsh_restrict]

lemma selectedWalshMean_average_zero {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (S : Finset (Fin (m * B))) (hS : S.Nonempty) : uniformAverage (selectedWalshMean s S) = 0 := by
  rw [← uniformAverage_restrict (fun i : Fin m => ZMod (s i)) (bitSources S)]
  simp_rw [selectedWalshMean_eq_full]
  rw [crtJitterBits_uniformAverage s B (fun z => walsh S (flattenBitBlocks m B z))]
  have heq := uniformAverage_equiv (flattenBitBlocks m B) (walsh S)
  rw [heq]
  exact cubeAverage_walsh hS

/-- Each low-order coefficient is the actual selected-coordinate observable
along the integer interval. -/
lemma integerBitDensity_coefficient {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (a N : ℕ) (hN : 0 < N) (S : Finset (Fin (m * B))) :
    walshCoefficient (integerBitDensity s B a N) S =
      uniformAverage (fun j : Fin N =>
        selectedWalshMean s S (fun i : bitSources S => (a + j.val : ZMod (s i)))) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  rw [integerBitDensity, sampleDensity_walshCoefficient,
    uniformAverage_prod (fun (j : Fin N) (noise : Fin m → Fin (2 ^ B)) =>
      walsh S (integerBitSample s B a (j, noise)))]
  apply congrArg uniformAverage
  funext j
  change uniformAverage (fun noise : Fin m → Fin (2 ^ B) =>
      walsh S (flattenBitBlocks m B
        (crtJitterBits s B (fun i => (a + j.val : ZMod (s i))) noise))) = _
  exact (selectedWalshMean_eq_full s S (fun i => (a + j.val : ZMod (s i)))).symm

/-- The Fourier error for a set of bits is bounded by the product of the
moduli of the residue coordinates touched by those bits, divided by length. -/
theorem integerBitDensity_coefficient_bound {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (a N : ℕ) (hN : 0 < N) (S : Finset (Fin (m * B))) (hS : S.Nonempty) :
    |walshCoefficient (integerBitDensity s B a N) S| ≤
      (∏ i : bitSources S, s i : ℕ) / (N : ℝ) := by
  have hcopS : Pairwise (fun i j : bitSources S => (s i).Coprime (s j)) := by
    intro i j hij
    exact hcop (fun h => hij (Subtype.ext h))
  have h := crt_observable_difference (fun i : bitSources S => s i) hcopS
    (a : ZMod (∏ i : bitSources S, s i)) N hN (selectedWalshMean s S)
    (abs_selectedWalshMean_le_one s S)
  have hvec (j : Fin N) :
      ZMod.prodEquivPi (fun i : bitSources S => s i) hcopS
          ((a : ZMod (∏ i : bitSources S, s i)) + (j.val : ZMod (∏ i : bitSources S, s i))) =
        (fun i : bitSources S => (a + j.val : ZMod (s i))) := by
    funext i
    simp only [ZMod.prodEquivPi_apply, map_add, map_natCast]
  simp_rw [hvec, selectedWalshMean_average_zero s S hS, sub_zero] at h
  rw [integerBitDensity_coefficient s a N hN S]
  exact h

lemma selected_modulus_product_le {m B : ℕ} (s : Fin m → ℕ)
    (S : Finset (Fin (m * B))) (M : ℝ) (hM : 1 ≤ M)
    (hs : ∀ i, (s i : ℝ) ≤ M) (t : ℕ) (ht : S.card ≤ t) :
    ((∏ i : bitSources S, s i : ℕ) : ℝ) ≤ M ^ t := by
  calc
    ((∏ i : bitSources S, s i : ℕ) : ℝ) = ∏ i : bitSources S, (s i : ℝ) := by push_cast; rfl
    _ ≤ ∏ _i : bitSources S, M :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hs i)
    _ = M ^ (bitSources S).card := by simp
    _ ≤ M ^ t := pow_le_pow_right₀ hM ((card_bitSources_le S).trans ht)

lemma integerBitDensity_low_coefficients {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (a N : ℕ) (hN : 0 < N) (M : ℝ) (hM : 1 ≤ M) (hs : ∀ i, (s i : ℝ) ≤ M) (t : ℕ) :
    ∀ S ∈ lowWalshSets (m * B) t,
      |walshCoefficient (integerBitDensity s B a N) S| ≤ M ^ t / (N : ℝ) := by
  intro S hS
  have hdata := (Finset.mem_filter.mp hS).2
  exact (integerBitDensity_coefficient_bound s hcop a N hN S hdata.1).trans
    (div_le_div_of_nonneg_right (selected_modulus_product_le s S M hM hs t hdata.2)
      (Nat.cast_nonneg N))

/-- Finite-parameter encoded residue comparison derived from the published
Braverman input, with all Fourier errors discharged by the actual interval
sampling law. Only the final numerical error budget is left to choose. -/
theorem BravermanDepth22Input.encoded_interval_comparison (hBraverman : BravermanDepth22Input) :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (m B : ℕ), 0 < m * B →
      ∀ (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      Pairwise (fun i j => (s i).Coprime (s j)) →
      ∀ (c : AC0Circuit (m * B)), c.depth ≤ 22 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∀ (a N : ℕ), 0 < N → ∀ M A : ℝ, 1 ≤ M → (∀ i, (s i : ℝ) ≤ M) →
          (M ^ t / (N : ℝ)) * ((t + 1 : ℕ) : ℝ) * ((m * B : ℕ) : ℝ) ^ t ≤ A →
          |uniformAverage (fun x : Fin N × (Fin m → Fin (2 ^ B)) =>
              c.indicator (integerBitSample s B a x)) - cubeAverage c.indicator| ≤
            3 * A / 2 + ε := by
  obtain ⟨K, C, hK, hC, hbound⟩ := hBraverman.coefficient_comparison
  refine ⟨K, C, hK, hC, ?_⟩
  intro m B hn s _hpos hcop c hc ε hε hεmax t ht a N hN M A hM hs hA
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  have h := hbound (m * B) hn c hc ε hε hεmax t ht (integerBitDensity s B a N)
    (M ^ t / (N : ℝ)) A (integerBitDensity_nonneg s B a N)
    (integerBitDensity_mean s B a N hN) (by positivity)
    (integerBitDensity_low_coefficients s hcop a N hN M hM hs t) hA
  simpa only [integerBitDensity, sampleDensity_expectation] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitEncoding
namespace OAI

/-!
# Truth-table encoding and substitution for residue circuits

Any decoded residue equality is a Boolean function of its block of bits.
Its explicit disjunctive normal form has depth at most two and size at most
`1 + 2^B (1+B)`. Substituting such forms into the actual circuit syntax
increases depth by at most two and multiplies size by this bound.
-/

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset


lemma substitute_eval {n m : ℕ} (σ : Fin n → Bool → AC0Circuit m)
    (F : BooleanCube m → BooleanCube n)
    (hσ : ∀ i positive x, (σ i positive).eval x = if positive then F x i else !(F x i))
    (c : AC0Circuit n) (x : BooleanCube m) : (substitute σ c).eval x = c.eval (F x) := by
  induction c with
  | literal i positive => exact hσ i positive x
  | andGate children ih => simp only [substitute, eval, ih]
  | orGate children ih => simp only [substitute, eval, ih]

lemma substitute_depth {n m d : ℕ} (σ : Fin n → Bool → AC0Circuit m)
    (hσ : ∀ i positive, (σ i positive).depth ≤ d) (c : AC0Circuit n) :
    (substitute σ c).depth ≤ c.depth + d := by
  induction c with
  | literal i positive => simpa [substitute, depth] using hσ i positive
  | andGate children ih =>
      simp only [substitute, depth]
      have hs : (Finset.univ.sup fun i => (substitute σ (children i)).depth) ≤
          (Finset.univ.sup fun i => (children i).depth) + d := by
        apply Finset.sup_le
        intro i hi
        exact (ih i).trans (Nat.add_le_add_right (Finset.le_sup (f := fun i => (children i).depth) hi) d)
      omega
  | orGate children ih =>
      simp only [substitute, depth]
      have hs : (Finset.univ.sup fun i => (substitute σ (children i)).depth) ≤
          (Finset.univ.sup fun i => (children i).depth) + d := by
        apply Finset.sup_le
        intro i hi
        exact (ih i).trans (Nat.add_le_add_right (Finset.le_sup (f := fun i => (children i).depth) hi) d)
      omega

lemma substitute_size {n m K : ℕ} (σ : Fin n → Bool → AC0Circuit m)
    (hK : 1 ≤ K) (hσ : ∀ i positive, (σ i positive).size ≤ K) (c : AC0Circuit n) :
    (substitute σ c).size ≤ K * c.size := by
  induction c with
  | literal i positive => simpa [substitute, size] using hσ i positive
  | andGate children ih =>
      simp only [substitute, size]
      calc
        1 + ∑ i, (substitute σ (children i)).size ≤ K + ∑ i, K * (children i).size :=
          Nat.add_le_add hK (Finset.sum_le_sum (fun i _ => ih i))
        _ = K * (1 + ∑ i, (children i).size) := by rw [← Finset.mul_sum]; ring
  | orGate children ih =>
      simp only [substitute, size]
      calc
        1 + ∑ i, (substitute σ (children i)).size ≤ K + ∑ i, K * (children i).size :=
          Nat.add_le_add hK (Finset.sum_le_sum (fun i _ => ih i))
        _ = K * (1 + ∑ i, (children i).size) := by rw [← Finset.mul_sum]; ring



lemma literal_eval_true {n : ℕ} (i : Fin n) (positive : Bool) (x : BooleanCube n) :
    (.literal i positive : AC0Circuit n).eval x = true ↔ x i = positive := by
  cases h : x i <;> cases positive <;> simp [eval, h]

lemma assignmentTerm_eval_true {n B : ℕ} (v : Fin B → Fin n)
    (z : BooleanCube B) (x : BooleanCube n) :
    (assignmentTerm v z).eval x = true ↔ (fun i => x (v i)) = z := by
  change (decide (∀ i : Fin B, (.literal (v i) (z i) : AC0Circuit n).eval x = true) = true) ↔ _
  constructor
  · intro h
    funext i
    exact (literal_eval_true (v i) (z i) x).mp ((of_decide_eq_true h) i)
  · intro h
    apply decide_eq_true
    intro i
    exact (literal_eval_true (v i) (z i) x).mpr (congrFun h i)



lemma truthTable_eval {n B : ℕ} (v : Fin B → Fin n) (F : BooleanCube B → Bool)
    (x : BooleanCube n) : (truthTable v F).eval x = F (fun i => x (v i)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [truthTable, eval, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk⟩
    split_ifs at hk with hF
    · have heq := (assignmentTerm_eval_true v (binaryCellEquiv B k) x).mp hk
      rwa [heq]
    · simp only [falseCircuit_eval, Bool.false_eq_true] at hk
  · intro hF
    refine ⟨(binaryCellEquiv B).symm (fun i => x (v i)), ?_⟩
    simp only [Equiv.apply_symm_apply, hF, ite_true]
    exact (assignmentTerm_eval_true v _ x).mpr rfl

lemma assignmentTerm_depth {n B : ℕ} (v : Fin B → Fin n) (z : BooleanCube B) :
    (assignmentTerm v z).depth = 1 := by simp [assignmentTerm, depth]

lemma assignmentTerm_size {n B : ℕ} (v : Fin B → Fin n) (z : BooleanCube B) :
    (assignmentTerm v z).size = 1 + B := by simp [assignmentTerm, size]

lemma truthTable_depth {n B : ℕ} (v : Fin B → Fin n) (F : BooleanCube B → Bool) :
    (truthTable v F).depth ≤ 2 := by
  change 1 + (Finset.univ.sup fun k : Fin (2 ^ B) =>
    (if F (binaryCellEquiv B k) then assignmentTerm v (binaryCellEquiv B k)
      else falseCircuit n).depth) ≤ 2
  have hs : (Finset.univ.sup fun k : Fin (2 ^ B) =>
    (if F (binaryCellEquiv B k) then assignmentTerm v (binaryCellEquiv B k)
      else falseCircuit n).depth) ≤ 1 := by
    apply Finset.sup_le
    intro k _
    split_ifs <;> simp [assignmentTerm_depth, falseCircuit, depth]
  omega

lemma truthTable_size {n B : ℕ} (v : Fin B → Fin n) (F : BooleanCube B → Bool) :
    (truthTable v F).size ≤ 1 + 2 ^ B * (1 + B) := by
  change 1 + (∑ k : Fin (2 ^ B),
    (if F (binaryCellEquiv B k) then assignmentTerm v (binaryCellEquiv B k)
      else falseCircuit n).size) ≤ _
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _k : Fin (2 ^ B), (1 + B) := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs <;> simp [assignmentTerm_size, falseCircuit, size]
    _ = 2 ^ B * (1 + B) := by simp


lemma encodeInputs_eval {n m B : ℕ} (v : Fin n → Fin B → Fin m)
    (F : Fin n → BooleanCube B → Bool) (c : AC0Circuit n) (x : BooleanCube m) :
    (encodeInputs v F c).eval x = c.eval (fun i => F i (fun j => x (v i j))) := by
  apply substitute_eval
  intro i positive y
  exact truthTable_eval _ _ y

lemma encodeInputs_depth {n m B : ℕ} (v : Fin n → Fin B → Fin m)
    (F : Fin n → BooleanCube B → Bool) (c : AC0Circuit n) :
    (encodeInputs v F c).depth ≤ c.depth + 2 :=
  substitute_depth _ (fun _ _ => truthTable_depth _ _) c

lemma encodeInputs_size {n m B : ℕ} (v : Fin n → Fin B → Fin m)
    (F : Fin n → BooleanCube B → Bool) (c : AC0Circuit n) :
    (encodeInputs v F c).size ≤ (1 + 2 ^ B * (1 + B)) * c.size :=
  substitute_size _ (by omega) (fun _ _ => truthTable_size _ _) c

end TwoPointCorrelations.AC0Circuit

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DecoderComparison
namespace OAI

/-! Uniform decoding-error estimates for the finite jitter construction. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma uniformAverage_sum {α ι : Type*} [Fintype α] [Fintype ι] (f : ι → α → ℝ) :
    uniformAverage (fun x => ∑ i, f i x) = ∑ i, uniformAverage (f i) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

lemma abs_uniformAverage_sub_le {α : Type*} [Fintype α] (f g h : α → ℝ)
    (hfg : ∀ x, |f x - g x| ≤ h x) :
    |uniformAverage f - uniformAverage g| ≤ uniformAverage h := by
  unfold uniformAverage
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div,
    show |(Fintype.card α : ℝ)| = (Fintype.card α : ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => hfg x))

lemma uniformAverage_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)] (i : ι)
    (f : β i → ℝ) :
    uniformAverage (fun x : ∀ j, β j => f (x i)) = uniformAverage f := by
  let e := Equiv.piSplitAt i β
  calc
    _ = uniformAverage (fun x : β i × (∀ j : {j // j ≠ i}, β j) => f x.1) :=
      uniformAverage_equiv e (fun x => f x.1)
    _ = _ := by
      rw [uniformAverage_prod (fun (x : β i) (_y : ∀ j : {j // j ≠ i}, β j) => f x)]
      simp only [uniformAverage_const]


lemma decodedResidues_jitter {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (r : ∀ i, ZMod (s i)) (j : Fin m → Fin (2 ^ B)) (i : Fin m) :
    decodedResidues s B (crtJitterBits s B r j) i =
      ZMod.finEquiv (s i) (jitterDecode (NeZero.pos (s i)) (by positivity)
        (jitterCode ((ZMod.finEquiv (s i)).symm (r i)) (j i))) := by
  change ZMod.finEquiv (s i) (decodeBits (NeZero.pos (s i))
    (jitterBits ((ZMod.finEquiv (s i)).symm (r i)) (j i))) = _
  rw [decode_jitterBits]

lemma decoded_coordinate_error {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (r : ∀ i, ZMod (s i)) (i : Fin m) :
    uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      if decodedResidues s B (crtJitterBits s B r j) i ≠ r i then (1 : ℝ) else 0) ≤
        (s i : ℝ) / (2 ^ B : ℕ) := by
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  simp_rw [decodedResidues_jitter]
  rw [uniformAverage_coordinate (fun _ : Fin m => Fin (2 ^ B)) i
    (fun j => if ZMod.finEquiv (s i) (jitterDecode (NeZero.pos (s i)) (by positivity)
      (jitterCode ((ZMod.finEquiv (s i)).symm (r i)) j)) ≠ r i then (1 : ℝ) else 0)]
  have heq (j : Fin (2 ^ B)) :
      (ZMod.finEquiv (s i) (jitterDecode (NeZero.pos (s i)) (by positivity)
        (jitterCode ((ZMod.finEquiv (s i)).symm (r i)) j)) ≠ r i) ↔
      jitterDecode (NeZero.pos (s i)) (by positivity)
        (jitterCode ((ZMod.finEquiv (s i)).symm (r i)) j) ≠
          (ZMod.finEquiv (s i)).symm (r i) := by
    exact not_congr (ZMod.finEquiv (s i)).toEquiv.eq_symm_apply.symm
  simp_rw [heq]
  simpa only [uniformAverage, Fintype.card_fin] using
    jitterDecode_error (NeZero.pos (s i)) (by positivity) ((ZMod.finEquiv (s i)).symm (r i))


lemma eventIndicator_difference_le_coordinate_errors {m : ℕ} (s : Fin m → ℕ)
    (E : (∀ i, ZMod (s i)) → Bool) (r d : ∀ i, ZMod (s i)) :
    |eventIndicator E r - eventIndicator E d| ≤
      ∑ i : Fin m, if d i ≠ r i then (1 : ℝ) else 0 := by
  by_cases heq : d = r
  · subst d
    simp
  · have hex : ∃ i, d i ≠ r i := by
      by_contra h
      push Not at h
      exact heq (funext h)
    obtain ⟨i, hi⟩ := hex
    have hsum : (1 : ℝ) ≤ ∑ j : Fin m, if d j ≠ r j then (1 : ℝ) else 0 := by
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin m))) (a := i)
        (f := fun j => if d j ≠ r j then (1 : ℝ) else 0)
        (by intro j _; split_ifs <;> norm_num) (Finset.mem_univ i)
      change (if d i ≠ r i then (1 : ℝ) else 0) ≤ _ at h
      rw [if_pos hi] at h
      exact h
    have hdiff : |eventIndicator E r - eventIndicator E d| ≤ 1 := by
      cases hr : E r <;> cases hd : E d <;> norm_num [eventIndicator, hr, hd]
    exact hdiff.trans hsum

/-- Every event has decoding error at most the sum of the coordinate errors.
This statement imposes no circuit assumption; circuits enter only in the
comparison of the encoded distributions. -/
theorem decoder_event_error {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (E : (∀ i, ZMod (s i)) → Bool) (r : ∀ i, ZMod (s i)) :
    |eventIndicator E r - uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      eventIndicator E (decodedResidues s B (crtJitterBits s B r j)))| ≤
        ∑ i : Fin m, (s i : ℝ) / (2 ^ B : ℕ) := by
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  have h := abs_uniformAverage_sub_le
    (fun _j : Fin m → Fin (2 ^ B) => eventIndicator E r)
    (fun j => eventIndicator E (decodedResidues s B (crtJitterBits s B r j)))
    (fun j => ∑ i : Fin m,
      if decodedResidues s B (crtJitterBits s B r j) i ≠ r i then (1 : ℝ) else 0)
    (fun _ => eventIndicator_difference_le_coordinate_errors s E r _)
  rw [uniformAverage_const, uniformAverage_sum] at h
  exact h.trans (Finset.sum_le_sum (fun i _ => decoded_coordinate_error s r i))

/-- The same decoder bound holds after averaging over an arbitrary finite
law of origins represented as a uniformly sampled finite map. -/
theorem decoder_event_error_averaged {α : Type*} [Fintype α] [Nonempty α]
    {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (E : (∀ i, ZMod (s i)) → Bool) (r : α → ∀ i, ZMod (s i)) :
    |uniformAverage (fun x => eventIndicator E (r x)) -
      uniformAverage (fun x => uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
        eventIndicator E (decodedResidues s B (crtJitterBits s B (r x) j))))| ≤
      ∑ i : Fin m, (s i : ℝ) / (2 ^ B : ℕ) := by
  have h := abs_uniformAverage_sub_le
    (fun x => eventIndicator E (r x))
    (fun x => uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      eventIndicator E (decodedResidues s B (crtJitterBits s B (r x) j))))
    (fun _x : α => ∑ i : Fin m, (s i : ℝ) / (2 ^ B : ℕ))
    (fun x => decoder_event_error s E (r x))
  simpa only [uniformAverage_const] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteResidueComparison
namespace OAI

/-!
# Finite residue-circuit comparison

An original residue circuit has depth at most twenty. Each input tests one
residue coordinate, and is replaced by its explicit truth table on the
corresponding bit block. The encoded circuit therefore has depth at most
twenty-two. The empirical Fourier bound, the published Braverman input,
and the two decoding errors give a completely finite error estimate.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma abs_add_three (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le (a + b) c).trans (add_le_add (abs_add_le a b) (le_refl |c|))




lemma flattenBitBlocks_block {m B : ℕ} (z : Fin m → BooleanCube B) (i : Fin m) :
    (fun j => flattenBitBlocks m B z (finProdFinEquiv (i, j))) = z i := by
  funext j
  exact congrArg (fun p : Fin m × Fin B => z p.1 p.2)
    (finProdFinEquiv.symm_apply_apply (i, j))

lemma encodeResidueCircuit_eval {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n)
    (z : Fin m → BooleanCube B) :
    (encodeResidueCircuit s B coord test c).eval (flattenBitBlocks m B z) =
      residueCircuitEvent s coord test c (decodedResidues s B z) := by
  unfold encodeResidueCircuit
  rw [AC0Circuit.encodeInputs_eval]
  simp only [flattenBitBlocks_block]
  rfl

lemma encodeResidueCircuit_indicator {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n)
    (z : Fin m → BooleanCube B) :
    (encodeResidueCircuit s B coord test c).indicator (flattenBitBlocks m B z) =
      eventIndicator (residueCircuitEvent s coord test c) (decodedResidues s B z) := by
  simp only [AC0Circuit.indicator, eventIndicator, encodeResidueCircuit_eval]

lemma encodeResidueCircuit_depth {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) :
    (encodeResidueCircuit s B coord test c).depth ≤ c.depth + 2 :=
  AC0Circuit.encodeInputs_depth _ _ c

lemma encodeResidueCircuit_size {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) :
    (encodeResidueCircuit s B coord test c).size ≤ (1 + 2 ^ B * (1 + B)) * c.size :=
  AC0Circuit.encodeInputs_size _ _ c

lemma encodeResidueCircuit_interval_average {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) (a N : ℕ) :
    uniformAverage (fun x : Fin N × (Fin m → Fin (2 ^ B)) =>
      (encodeResidueCircuit s B coord test c).indicator (integerBitSample s B a x)) =
    uniformAverage (fun x : Fin N => uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      eventIndicator (residueCircuitEvent s coord test c)
        (decodedResidues s B (crtJitterBits s B (fun i => (a + x.val : ZMod (s i))) j)))) := by
  change uniformAverage (fun x : Fin N × (Fin m → Fin (2 ^ B)) =>
    (encodeResidueCircuit s B coord test c).indicator
      (flattenBitBlocks m B (crtJitterBits s B (fun i => (a + x.1.val : ZMod (s i))) x.2))) = _
  simp_rw [encodeResidueCircuit_indicator]
  exact uniformAverage_prod (fun (x : Fin N) (j : Fin m → Fin (2 ^ B)) =>
    eventIndicator (residueCircuitEvent s coord test c)
      (decodedResidues s B (crtJitterBits s B (fun i => (a + x.val : ZMod (s i))) j)))

lemma encodeResidueCircuit_uniform_average {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) :
    cubeAverage (encodeResidueCircuit s B coord test c).indicator =
    uniformAverage (fun r : ∀ i, ZMod (s i) =>
      uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
        eventIndicator (residueCircuitEvent s coord test c)
          (decodedResidues s B (crtJitterBits s B r j)))) := by
  calc
    _ = uniformAverage (fun z : Fin m → BooleanCube B =>
        (encodeResidueCircuit s B coord test c).indicator (flattenBitBlocks m B z)) :=
      (uniformAverage_equiv (flattenBitBlocks m B)
        (encodeResidueCircuit s B coord test c).indicator).symm
    _ = uniformAverage (fun r : ∀ i, ZMod (s i) =>
        uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
          (encodeResidueCircuit s B coord test c).indicator
            (flattenBitBlocks m B (crtJitterBits s B r j)))) :=
      (crtJitterBits_uniformAverage s B _).symm
    _ = _ := by simp_rw [encodeResidueCircuit_indicator]

/-- Comparison for the original depth-twenty residue circuit. The arithmetic
hypotheses are precisely positivity and pairwise coprimality of the moduli;
no squarefreeness or bound on their total product is used. The low-order
Fourier error and the decoding error are explicit finite quantities. -/
theorem BravermanDepth22Input.finite_residue_comparison (hBraverman : BravermanDepth22Input) :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (m B : ℕ), 0 < m * B →
      ∀ (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      Pairwise (fun i j => (s i).Coprime (s j)) →
      ∀ (n : ℕ) (coord : Fin n → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n), c.depth ≤ 20 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log
          (((encodeResidueCircuit s B coord test c).size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∀ (a N : ℕ), 0 < N → ∀ M A : ℝ, 1 ≤ M → (∀ i, (s i : ℝ) ≤ M) →
          (M ^ t / (N : ℝ)) * ((t + 1 : ℕ) : ℝ) * ((m * B : ℕ) : ℝ) ^ t ≤ A →
          |uniformAverage (fun x : Fin N =>
              eventIndicator (residueCircuitEvent s coord test c)
                (fun i => (a + x.val : ZMod (s i)))) -
            uniformAverage (eventIndicator (residueCircuitEvent s coord test c))| ≤
              2 * (∑ i : Fin m, (s i : ℝ) / (2 ^ B : ℕ)) + 3 * A / 2 + ε := by
  obtain ⟨K, C, hK, hC, hcompare⟩ := hBraverman.encoded_interval_comparison
  refine ⟨K, C, hK, hC, ?_⟩
  intro m B hn s _hpos hcop n coord test c hc ε hε hεmax t ht a N hN M A hM hs hA
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hdepth : (encodeResidueCircuit s B coord test c).depth ≤ 22 :=
    (encodeResidueCircuit_depth (B := B) s coord test c).trans (by omega)
  have hmiddle := hcompare m B hn s hcop (encodeResidueCircuit s B coord test c)
    hdepth ε hε hεmax t ht a N hN M A hM hs hA
  rw [encodeResidueCircuit_interval_average, encodeResidueCircuit_uniform_average] at hmiddle
  have hleft := decoder_event_error_averaged (B := B) s (residueCircuitEvent s coord test c)
    (fun x : Fin N => fun i => (a + x.val : ZMod (s i)))
  have hright := decoder_event_error_averaged (B := B) s (residueCircuitEvent s coord test c)
    (fun r : ∀ i, ZMod (s i) => r)
  let I := uniformAverage (fun x : Fin N =>
    eventIndicator (residueCircuitEvent s coord test c) (fun i => (a + x.val : ZMod (s i))))
  let J := uniformAverage (fun x : Fin N => uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
    eventIndicator (residueCircuitEvent s coord test c)
      (decodedResidues s B (crtJitterBits s B (fun i => (a + x.val : ZMod (s i))) j))))
  let U := uniformAverage (fun r : ∀ i, ZMod (s i) =>
    uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      eventIndicator (residueCircuitEvent s coord test c)
        (decodedResidues s B (crtJitterBits s B r j))))
  let V := uniformAverage (eventIndicator (residueCircuitEvent s coord test c))
  change |I - J| ≤ _ at hleft
  change |J - U| ≤ _ at hmiddle
  change |V - U| ≤ _ at hright
  change |I - V| ≤ _
  have htriangle : |I - V| ≤ |I - J| + |J - U| + |U - V| := by
    calc
      _ = |(I - J) + (J - U) + (U - V)| := by congr 1; ring
      _ ≤ _ := abs_add_three (I - J) (J - U) (U - V)
  rw [abs_sub_comm] at hright
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteLawParameters
namespace OAI

/-! Explicit large-scale choices for the finite residue comparison. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

/-- Fixed coefficients are absorbed by increasing a positive integer power. -/
lemma eventually_const_mul_pow_le (p q : ℕ) (hpq : p < q) (c : ℝ) :
    ∀ᶠ L : ℝ in atTop, c * L ^ p ≤ L ^ q := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop c] with L hL hc
  calc
    c * L ^ p ≤ L * L ^ p := mul_le_mul_of_nonneg_right hc (pow_nonneg (by linarith) _)
    _ = L ^ (p + 1) := by rw [pow_succ]; ring
    _ ≤ L ^ q := pow_le_pow_right₀ hL hpq

lemma ceil_pow_bounds {L : ℝ} (hL : 1 ≤ L) (k : ℕ) :
    L ^ k ≤ (⌈L ^ k⌉₊ : ℝ) ∧ (⌈L ^ k⌉₊ : ℝ) ≤ 2 * L ^ k := by
  have hp : 1 ≤ L ^ k := one_le_pow₀ hL
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity : 0 ≤ L ^ k)).le.trans (by linarith)⟩

/-- Truth-table substitution fits the manuscript's encoded size bound. -/
lemma eventually_encoded_size_bound :
    ∀ᶠ L : ℝ in atTop, ∀ B : ℕ, B = ⌈L ^ 15⌉₊ →
      ∀ S : ℝ, S ≤ Real.exp (L ^ 6) →
      (1 + (2 : ℝ) ^ B * (1 + B)) * S ≤ Real.exp (L ^ 17) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_const_mul_pow_le 15 17 (by norm_num) 7] with L hL hpow B hB S hS
  have hLp : 0 ≤ L := le_trans zero_le_one hL
  have hBbound : (B : ℝ) ≤ 2 * L ^ 15 := by simpa only [hB] using (ceil_pow_bounds hL 15).2
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowB : (2 : ℝ) ^ B ≤ Real.exp (B : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ B := pow_le_pow_left₀ (by norm_num) htwo B
      _ = Real.exp (B : ℝ) := by rw [← Real.exp_nat_mul]; simp
  have honeB : 1 + (B : ℝ) ≤ Real.exp (B : ℝ) := by
    simpa [add_comm] using Real.add_one_le_exp (B : ℝ)
  have hfac : 1 + (2 : ℝ) ^ B * (1 + B) ≤ Real.exp (1 + 2 * (B : ℝ)) := by
    calc
      _ ≤ 1 + Real.exp (B : ℝ) * Real.exp (B : ℝ) :=
        add_le_add (le_refl 1) (mul_le_mul hpowB honeB (by positivity) (by positivity))
      _ = 1 + Real.exp (2 * (B : ℝ)) := by rw [← Real.exp_add]; congr 2; ring
      _ ≤ 2 * Real.exp (2 * (B : ℝ)) := by
        have := Real.one_le_exp_iff.mpr (show 0 ≤ 2 * (B : ℝ) by positivity)
        linarith
      _ ≤ Real.exp 1 * Real.exp (2 * (B : ℝ)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hsmall : L ^ 6 ≤ L ^ 15 := pow_le_pow_right₀ hL (by norm_num)
  calc
    _ ≤ (1 + (2 : ℝ) ^ B * (1 + B)) * Real.exp (L ^ 6) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ Real.exp (1 + 2 * (B : ℝ)) * Real.exp (L ^ 6) :=
      mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
    _ = Real.exp (1 + 2 * (B : ℝ) + L ^ 6) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (7 * L ^ 15) := by
      apply Real.exp_le_exp.mpr
      have hp : 1 ≤ L ^ 15 := one_le_pow₀ hL
      nlinarith
    _ ≤ _ := Real.exp_le_exp.mpr hpow

/-- The number of bits is small even after adding the fixed-modulus block. -/
lemma eventually_bit_count_bound :
    ∀ᶠ L : ℝ in atTop, ∀ m B : ℕ, (m : ℝ) ≤ Real.exp L + 1 → B = ⌈L ^ 15⌉₊ →
      ((m * B : ℕ) : ℝ) ≤ Real.exp (2 * L) := by
  have h := (Real.isLittleO_pow_exp_atTop (n := 15)).bound (show 0 < (1 / 4 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop 1, h] with L hL hpow m B hm hB
  have hLp : 0 ≤ L := le_trans zero_le_one hL
  have hp : 0 ≤ L ^ 15 := pow_nonneg hLp _
  have h4 : 4 * L ^ 15 ≤ Real.exp L := by
    rw [Real.norm_eq_abs, abs_of_nonneg hp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hpow
    linarith
  have hm' : (m : ℝ) ≤ 2 * Real.exp L := by
    have := Real.one_le_exp_iff.mpr hLp
    linarith
  have hB' : (B : ℝ) ≤ 2 * L ^ 15 := by simpa only [hB] using (ceil_pow_bounds hL 15).2
  calc
    ((m * B : ℕ) : ℝ) = (m : ℝ) * (B : ℝ) := by push_cast; rfl
    _ ≤ (2 * Real.exp L) * (2 * L ^ 15) := mul_le_mul hm' hB' (by positivity) (by positivity)
    _ = Real.exp L * (4 * L ^ 15) := by ring
    _ ≤ Real.exp L * Real.exp L := mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Polynomially many independence coordinates suffice for Braverman's
logarithmic requirement at encoded size `exp (L^17)`. -/
lemma eventually_braverman_budget (K C : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ S : ℝ, 1 ≤ S → S ≤ Real.exp (L ^ 17) →
      (K : ℝ) * (Real.log (S / Real.exp (-(L ^ 11)))) ^ C ≤
        (⌈L ^ (17 * C + 1)⌉₊ : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_const_mul_pow_le (17 * C) (17 * C + 1) (by omega) ((K : ℝ) * 2 ^ C)]
    with L hL hpow S hS hlo
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hlog : Real.log (S / Real.exp (-(L ^ 11))) ≤ 2 * L ^ 17 := by
    rw [Real.log_div hSpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hl := Real.log_le_log hSpos hlo
    rw [Real.log_exp] at hl
    have hsmall : L ^ 11 ≤ L ^ 17 := pow_le_pow_right₀ hL (by norm_num)
    linarith
  have hlogpos : 0 ≤ Real.log (S / Real.exp (-(L ^ 11))) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have he : Real.exp (-(L ^ 11)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (pow_nonneg (le_trans zero_le_one hL) _))
    simpa using he.trans hS
  calc
    _ ≤ (K : ℝ) * (2 * L ^ 17) ^ C :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogpos hlog C) (Nat.cast_nonneg _)
    _ = ((K : ℝ) * 2 ^ C) * L ^ (17 * C) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ L ^ (17 * C + 1) := hpow
    _ ≤ _ := Nat.le_ceil _

/-- The actual low-order Fourier mass is exponentially small once the
interval exponent exceeds the independence exponent. -/
lemma eventually_fourier_budget (T A : ℕ) (hT : 10 ≤ T) (hA : T + 1 < A) :
    ∀ᶠ L : ℝ in atTop, ∀ t n N : ℕ, t = ⌈L ^ T⌉₊ →
      (n : ℝ) ≤ Real.exp (2 * L) → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ((Real.exp L) ^ t / (N : ℝ)) * ((t + 1 : ℕ) : ℝ) * (n : ℝ) ^ t ≤
        Real.exp (-(L ^ 11)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_const_mul_pow_le (T + 1) A hA 20] with L hL hpower t n N ht hn hN
  have hLp : 0 ≤ L := le_trans zero_le_one hL
  have htbound : (t : ℝ) ≤ 2 * L ^ T := by simpa only [ht] using (ceil_pow_bounds hL T).2
  have htp : 1 ≤ L ^ T := one_le_pow₀ hL
  have htadd : (t : ℝ) + 1 ≤ 3 * L ^ T := by linarith
  have hNt : 0 < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hN
  have htExp : ((t + 1 : ℕ) : ℝ) ≤ Real.exp ((t : ℝ) + 1) := by
    push_cast
    have h := Real.add_one_le_exp ((t : ℝ) + 1)
    linarith
  have hcalc : (((Real.exp L) ^ t / Real.exp (L ^ A / 2)) *
      Real.exp ((t : ℝ) + 1)) * (Real.exp (2 * L)) ^ t =
      Real.exp (3 * L * (t : ℝ) + ((t : ℝ) + 1) - L ^ A / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsmall : L ^ T ≤ L ^ (T + 1) := pow_le_pow_right₀ hL (by omega)
  have h11 : L ^ 11 ≤ L ^ (T + 1) := pow_le_pow_right₀ hL (by omega)
  have hterm : L * (t : ℝ) ≤ 2 * L ^ (T + 1) := by
    have h := mul_le_mul_of_nonneg_left htbound hLp
    rw [pow_succ]
    nlinarith
  calc
    _ ≤ (((Real.exp L) ^ t / Real.exp (L ^ A / 2)) *
        Real.exp ((t : ℝ) + 1)) * (Real.exp (2 * L)) ^ t := by
      gcongr
    _ = _ := hcalc
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      linarith

/-- Both decoder errors and the corrected-law errors fit inside the final
`exp (-L^10)` budget. -/
lemma eventually_total_comparison_error :
    ∀ᶠ L : ℝ in atTop, ∀ B : ℕ, B = ⌈L ^ 15⌉₊ → ∀ D : ℝ,
      D ≤ Real.exp (3 * L) →
      2 * D / (2 : ℝ) ^ B + 3 * Real.exp (-(L ^ 11)) / 2 +
        Real.exp (-(L ^ 11)) ≤ Real.exp (-(L ^ 10)) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop 4,
    eventually_const_mul_pow_le 11 15 (by norm_num) (6 / Real.log (2 : ℝ))]
    with L hL4 hpower B hB D hD
  have hL : 1 ≤ L := by linarith
  have hLp : 0 ≤ L := le_trans zero_le_one hL
  have hBbound : L ^ 15 ≤ (B : ℝ) := by simpa only [hB] using (ceil_pow_bounds hL 15).1
  have hdom : 6 * L ^ 11 ≤ L ^ 15 * Real.log (2 : ℝ) := by
    apply (div_le_iff₀ hlog).mp
    convert (preTransparency := .instances) hpower using 1; ring
  have hlogmax : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
    linarith
  have h11one : 1 ≤ L ^ 11 := one_le_pow₀ hL
  have hL11 : L ≤ L ^ 11 := by simpa using pow_le_pow_right₀ hL (show 1 ≤ (11 : ℕ) by norm_num)
  have hmul : L ^ 15 * Real.log (2 : ℝ) ≤ (B : ℝ) * Real.log (2 : ℝ) :=
    mul_le_mul_of_nonneg_right hBbound hlog.le
  have hdecodeExp : Real.log (2 : ℝ) + 3 * L - (B : ℝ) * Real.log (2 : ℝ) ≤ -(L ^ 11) := by
    linarith
  have hpowB : (2 : ℝ) ^ B = Real.exp ((B : ℝ) * Real.log (2 : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (show 0 < (2 : ℝ) by norm_num)]
  have hdecode : 2 * D / (2 : ℝ) ^ B ≤ Real.exp (-(L ^ 11)) := by
    calc
      _ ≤ 2 * Real.exp (3 * L) / (2 : ℝ) ^ B := by gcongr
      _ = Real.exp (Real.log (2 : ℝ) + 3 * L - (B : ℝ) * Real.log (2 : ℝ)) := by
        rw [hpowB, Real.exp_sub, Real.exp_add,
          Real.exp_log (show 0 < (2 : ℝ) by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr hdecodeExp
  have h10one : 1 ≤ L ^ 10 := one_le_pow₀ hL
  have h11grow : 4 * L ^ 10 ≤ L ^ 11 := by
    calc
      4 * L ^ 10 ≤ L * L ^ 10 := mul_le_mul_of_nonneg_right hL4 (pow_nonneg hLp 10)
      _ = L ^ 11 := by ring
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by
    linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (-(L ^ 11)) := by linarith [Real.exp_pos (-(L ^ 11))]
    _ ≤ Real.exp 3 * Real.exp (-(L ^ 11)) :=
      mul_le_mul_of_nonneg_right hfour (Real.exp_pos _).le
    _ = Real.exp (3 - L ^ 11) := by rw [← Real.exp_add]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- The coefficient mass allowed in scalar expansions consumes only one
power in the exponent of the finite-law error. -/
lemma eventually_scalar_error (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ 5) * Real.exp (-(L ^ 10)) ≤ Real.exp (-(L ^ 9)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_const_mul_pow_le 9 10 (by norm_num) (C + 1)] with L hL hpower
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsmall : L ^ 5 ≤ L ^ 9 := pow_le_pow_right₀ hL (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hsmall hC
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ScalarComparison
namespace OAI

/-! Signed scalar expansions preserve their coefficients through comparison. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma uniformAverage_mul_const {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformAverage (fun x => c * f x) = c * uniformAverage f := by
  unfold uniformAverage
  rw [← Finset.mul_sum]
  ring

/-- Each event is compared before absolute values are taken. The total error
is weighted by the absolute values of the original signed coefficients. -/
theorem scalar_average_comparison {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    (f : ι → α → ℝ) (g : ι → β → ℝ) (c error : ι → ℝ)
    (h : ∀ i, |uniformAverage (f i) - uniformAverage (g i)| ≤ error i) :
    |uniformAverage (fun x => ∑ i, c i * f i x) -
      uniformAverage (fun y => ∑ i, c i * g i y)| ≤ ∑ i, |c i| * error i := by
  simp_rw [uniformAverage_sum, uniformAverage_mul_const]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |c i * uniformAverage (f i) - c i * uniformAverage (g i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| * |uniformAverage (f i) - uniformAverage (g i)| := by
      simp_rw [← mul_sub, abs_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (abs_nonneg _))

/-- Uniform event error times total absolute coefficient mass. -/
theorem scalar_average_comparison_uniform {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    (f : ι → α → ℝ) (g : ι → β → ℝ) (c : ι → ℝ) (error : ℝ)
    (h : ∀ i, |uniformAverage (f i) - uniformAverage (g i)| ≤ error) :
    |uniformAverage (fun x => ∑ i, c i * f i x) -
      uniformAverage (fun y => ∑ i, c i * g i y)| ≤ (∑ i, |c i|) * error := by
  simpa only [Finset.sum_mul] using scalar_average_comparison f g c (fun _ => error) h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActiveStateExpansion
namespace OAI

/-! Exact active-prime states give small scalar expansions after the
degree truncation. All absent prime tests remain in each conjunction. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma mem_boundedActiveStates {n M : ℕ} {S : Finset (Fin n)} :
    S ∈ boundedActiveStates n M ↔ S.card ≤ M := by
  simp only [boundedActiveStates, mem_filter, mem_powerset, subset_univ, true_and]

lemma boundedActiveStates_card (n M : ℕ) :
    (boundedActiveStates n M).card ≤ (M + 1) * (n + 1) ^ M := by
  have he : boundedActiveStates n M =
      (range (M + 1)).biUnion (fun r => univ.powersetCard r) := by
    ext S
    simp only [mem_boundedActiveStates, mem_biUnion, mem_range, mem_powersetCard,
      subset_univ, true_and]
    constructor
    · intro hS
      exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨r, hr, he⟩
      omega
  rw [he]
  apply (card_biUnion_le).trans
  calc
    (∑ r ∈ range (M + 1), (univ.powersetCard r : Finset (Finset (Fin n))).card) =
        ∑ r ∈ range (M + 1), n.choose r := by
      simp only [card_powersetCard, card_univ, Fintype.card_fin]
    _ ≤ ∑ _r ∈ range (M + 1), (n + 1) ^ M := by
      apply sum_le_sum
      intro r hr
      exact (Nat.choose_le_pow n r).trans
        ((Nat.pow_le_pow_left (Nat.le_succ n) r).trans
          (Nat.pow_le_pow_right (by omega) (by simp only [mem_range] at hr; omega)))
    _ = _ := by simp


lemma activeStateCircuit_eval {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    (activeStateCircuit S).eval x = true ↔ activeState x = S := by
  simp only [activeStateCircuit, AC0Circuit.eval, decide_eq_true_eq]
  constructor
  · intro h
    ext i
    have hi := h i
    by_cases hs : i ∈ S <;> cases hx : x i <;>
      simp_all [activeState]
  · intro h i
    have hi : x i = true ↔ i ∈ S := by
      rw [← h]
      simp only [activeState, mem_filter, mem_univ, true_and]
    by_cases hs : i ∈ S <;> cases hx : x i <;>
      simp_all [activeState]

lemma activeStateCircuit_depth {n : ℕ} (S : Finset (Fin n)) :
    (activeStateCircuit S).depth ≤ 1 := by
  simp [activeStateCircuit, AC0Circuit.depth]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActiveStateBudget
namespace OAI

/-! The complete low-degree state family fits the scalar-comparison budget. -/

namespace TwoPointCorrelations

lemma active_state_family_cost (L : ℝ) (n M R : ℕ)
    (hL : 4800 ≤ L) (hn : (n : ℝ) ≤ Real.exp L)
    (hM : (M : ℝ) ≤ 400 * Real.log L) (hR : (R : ℝ) ≤ 4 * L) :
    (((M + 1) * (n + 1) ^ M : ℕ) : ℝ) ^ R ≤ Real.exp (L ^ 4) := by
  have hLp : 0 ≤ L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hexp : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hn' : (n : ℝ) + 1 ≤ Real.exp (2 * L) := by
    have he : Real.exp (2 * L) = Real.exp L * Real.exp L := by
      rw [show 2 * L = L + L by ring, Real.exp_add]
    rw [he]
    nlinarith
  have hM' : (M : ℝ) + 1 ≤ Real.exp (400 * Real.log L) := by
    linarith [Real.add_one_le_exp (400 * Real.log L)]
  have hbase : (((M + 1) * (n + 1) ^ M : ℕ) : ℝ) ≤
      Real.exp (1200 * L * Real.log L) := by
    push_cast
    calc
      _ ≤ Real.exp (400 * Real.log L) * (Real.exp (2 * L)) ^ M :=
        mul_le_mul hM' (pow_le_pow_left₀ (by positivity) hn' M) (by positivity) (by positivity)
      _ = Real.exp (400 * Real.log L + M * (2 * L)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right hM (show 0 ≤ 2 * L by positivity)
        have hl := mul_le_mul_of_nonneg_right (show 1 ≤ L by linarith) hlog
        nlinarith
  have hlogL : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc
    _ ≤ (Real.exp (1200 * L * Real.log L)) ^ R :=
      pow_le_pow_left₀ (by positivity) hbase R
    _ = Real.exp (R * (1200 * L * Real.log L)) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp (4800 * L ^ 3) := by
      apply Real.exp_le_exp.mpr
      have hr := mul_le_mul_of_nonneg_right hR
        (show 0 ≤ 1200 * L * Real.log L by positivity)
      have hl := mul_le_mul_of_nonneg_left hlogL (show 0 ≤ 4800 * L ^ 2 by positivity)
      nlinarith
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (show 0 ≤ L - 4800 by linarith) (pow_nonneg hLp 3)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActiveStateVectors
namespace OAI

/-! Simultaneous bounded active states at every vertex of a trace word.
Offsets may share residue coordinates; the circuit keeps this sharing explicit. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma activeStateVectorCircuit_eval {R n m : ℕ} (index : Fin R → Fin n → Fin m)
    (S : Fin R → Finset (Fin n)) (x : BooleanCube m) :
    (activeStateVectorCircuit index S).eval x = true ↔
      ∀ r, activeState (fun i => x (index r i)) = S r := by
  change (decide (∀ r, (activeStateCircuit (S r)).eval (fun i => x (index r i)) = true) = true) ↔ _
  simp only [decide_eq_true_eq, activeStateCircuit_eval]

lemma activeStateVectorCircuit_depth {R n m : ℕ} (index : Fin R → Fin n → Fin m)
    (S : Fin R → Finset (Fin n)) : (activeStateVectorCircuit index S).depth ≤ 2 := by
  change 1 + (univ.sup fun r : Fin R => (activeStateCircuit (S r)).depth) ≤ 2
  have hh : (univ.sup fun r : Fin R => (activeStateCircuit (S r)).depth) ≤ 1 :=
    Finset.sup_le (fun r _ => activeStateCircuit_depth (S r))
  omega

lemma activeStateVectorCircuit_size {R n m : ℕ} (index : Fin R → Fin n → Fin m)
    (S : Fin R → Finset (Fin n)) :
    (activeStateVectorCircuit index S).size = 1 + R * (1 + n) := by
  simp [activeStateVectorCircuit, AC0Circuit.size]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EventualResidueComparison
namespace OAI

/-! The explicit polynomial bit and independence budgets give the
finite-interval circuit comparison required in the graph application. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

theorem BravermanDepth22Input.eventually_residue_comparison (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (n : ℕ) (coord : Fin n → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n),
      c.depth ≤ 20 → (c.size : ℝ) ≤ Real.exp (L ^ 6) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N =>
          eventIndicator (residueCircuitEvent s coord test c)
            (fun i => (a + x.val : ZMod (s i)))) -
        uniformAverage (eventIndicator (residueCircuitEvent s coord test c))| ≤
          Real.exp (-(L ^ 10)) := by
  obtain ⟨K, C, hK, hC, hcompare⟩ := hBr.finite_residue_comparison
  let T := 17 * C + 1
  let A := T + 1002
  refine ⟨A, by omega, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_encoded_size_bound,
    eventually_bit_count_bound, eventually_braverman_budget K C,
    eventually_fourier_budget T A (by omega) (by omega),
    eventually_total_comparison_error] with L hL hsize hbits hbr hfourier herr
  intro m s _ hm hmexp hcop hs n coord test c hc hcsize a N hN
  let B := ⌈L ^ 15⌉₊
  let t := ⌈L ^ T⌉₊
  have hLone : 1 ≤ L := by linarith
  have hLp : 0 ≤ L := by linarith
  have hBone : 0 < B := by
    have hBbound := (ceil_pow_bounds hLone 15).1
    have hone : (1 : ℝ) ≤ L ^ 15 := one_le_pow₀ hLone
    have hBp : (0 : ℝ) < B := by dsimp only [B]; linarith
    exact_mod_cast hBp
  have hBsize0 : ((encodeResidueCircuit s B coord test c).size : ℝ) ≤
      (1 + (2 : ℝ) ^ B * (1 + B)) * c.size := by
    exact_mod_cast encodeResidueCircuit_size (B := B) s coord test c
  have hBsize : ((encodeResidueCircuit s B coord test c).size : ℝ) ≤ Real.exp (L ^ 17) :=
    hBsize0.trans (hsize B rfl c.size hcsize)
  have hBsizeone : (1 : ℝ) ≤ (encodeResidueCircuit s B coord test c).size := by
    exact_mod_cast (encodeResidueCircuit s B coord test c).size_pos
  have ht := hbr (encodeResidueCircuit s B coord test c).size hBsizeone hBsize
  have hnbits := hbits m B hmexp rfl
  have hfour := hfourier t (m * B) N rfl hnbits hN
  have hNpos : 0 < N := by
    have hNp : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
    exact_mod_cast hNp
  have heps : Real.exp (-(L ^ 11)) ≤ 1 / 2 := by
    have hone : (1 : ℝ) ≤ L ^ 11 := one_le_pow₀ hLone
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.exp_neg]
    exact (inv_anti₀ (by norm_num : (0 : ℝ) < 2)
      (he.trans (Real.exp_le_exp.mpr hone))).trans_eq (by norm_num)
  have hb := hcompare m B (Nat.mul_pos hm hBone) s hcop n coord test c hc
    (Real.exp (-(L ^ 11))) (Real.exp_pos _) heps t ht a N hNpos (Real.exp L)
    (Real.exp (-(L ^ 11))) (Real.one_le_exp hLp) hs hfour
  have hsum : (∑ i : Fin m, (s i : ℝ)) ≤ Real.exp (3 * L) := by
    have hbound : (∑ i : Fin m, (s i : ℝ)) ≤ m * Real.exp L := by
      calc
        _ ≤ ∑ _i : Fin m, Real.exp L := sum_le_sum (fun i _ => hs i)
        _ = _ := by simp
    have hE : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp hLp
    have hE2 : (2 : ℝ) ≤ Real.exp L := by
      linarith [Real.add_one_le_exp L]
    calc
      _ ≤ (Real.exp L + 1) * Real.exp L :=
        hbound.trans (mul_le_mul_of_nonneg_right hmexp (Real.exp_pos _).le)
      _ ≤ Real.exp L * Real.exp L * Real.exp L := by nlinarith
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  apply hb.trans
  simpa only [← sum_div, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc] using herr B rfl _ hsum

/-- Scalar expansions preserve their signed coefficients through the
finite-law comparison; only their total absolute mass enters the error. -/
theorem BravermanDepth22Input.eventually_scalar_residue_comparison
    (hBr : BravermanDepth22Input) (C : ℝ) (hC : 0 ≤ C) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (ι : Type) [Fintype ι] (n : ℕ) (coord : Fin n → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (c : ι → AC0Circuit n) (coeff : ι → ℝ),
      (∀ i, (c i).depth ≤ 20) → (∀ i, ((c i).size : ℝ) ≤ Real.exp (L ^ 6)) →
      (∑ i, |coeff i|) ≤ Real.exp (C * L ^ 5) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N => ∑ i, coeff i *
          eventIndicator (residueCircuitEvent s coord test (c i))
            (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage (fun r => ∑ i, coeff i *
          eventIndicator (residueCircuitEvent s coord test (c i)) r)| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hevent⟩ := hBr.eventually_residue_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hevent, eventually_scalar_error C hC] with L hevent herror
  intro m s _ hm hmexp hcop hs ι _ n coord test c coeff hc hsize hcoeff a N hN
  have hb := scalar_average_comparison_uniform
    (fun i (x : Fin N) => eventIndicator (residueCircuitEvent s coord test (c i))
      (fun j => (a + x.val : ZMod (s j))))
    (fun i r => eventIndicator (residueCircuitEvent s coord test (c i)) r)
    coeff (Real.exp (-(L ^ 10)))
    (fun i => hevent m s hm hmexp hcop hs n coord test (c i) (hc i) (hsize i) a N hN)
  exact hb.trans ((mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le).trans herror)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitBooleanOps
namespace OAI

/-! Relabel, complement and conjoin the residue circuits used in a
closed-word expansion without increasing their internal depth. -/

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset










lemma conjunction_eval {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) (x : BooleanCube n) :
    (conjunction c).eval x = true ↔ ∀ i, (c i).eval x = true := by
  simp only [conjunction, eval, decide_eq_true_eq]
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h ((Fintype.equivFin ι) i)
  · intro h i
    exact h _

lemma conjunction_depth {ι : Type*} [Fintype ι] {n d : ℕ}
    (c : ι → AC0Circuit n) (hc : ∀ i, (c i).depth ≤ d) :
    (conjunction c).depth ≤ d + 1 := by
  simp only [conjunction, depth]
  have hh : (univ.sup fun i : Fin (Fintype.card ι) =>
      (c ((Fintype.equivFin ι).symm i)).depth) ≤ d :=
    Finset.sup_le (fun i _ => hc _)
  omega

lemma conjunction_size {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : (conjunction c).size = 1 + ∑ i, (c i).size := by
  simp only [conjunction, size]
  congr 1
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => (c i).size)

end TwoPointCorrelations.AC0Circuit

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WeightedWordCircuit
namespace OAI

/-! Exact signed state expansion for a closed word. The padding states
are truncated; every centered-prime bit is retained. The remaining
predicate is a circuit, including all prohibited-vertex tests. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma weightedStateCircuit_eval {R n t m : ℕ}
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m)
    (x : BooleanCube m) :
    (weightedStateCircuit qindex pindex S bits c).eval x = true ↔
      (∀ r, activeState (fun i => x (qindex r i)) = S r) ∧
      (fun i => x (pindex i)) = bits ∧ c.eval x = true := by
  simp only [weightedStateCircuit, AC0Circuit.conjunction_eval, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    activeStateVectorCircuit_eval, AC0Circuit.assignmentTerm_eval_true]
  simp

lemma weightedStateCircuit_depth {R n t m : ℕ}
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m)
    (hc : c.depth ≤ 19) :
    (weightedStateCircuit qindex pindex S bits c).depth ≤ 20 := by
  apply AC0Circuit.conjunction_depth (d := 19)
  intro i
  fin_cases i
  · exact (activeStateVectorCircuit_depth qindex S).trans (by norm_num)
  · simp [AC0Circuit.assignmentTerm_depth]
  · exact hc

lemma weightedStateCircuit_size {R n t m : ℕ}
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m) :
    (weightedStateCircuit qindex pindex S bits c).size =
      3 + R * (1 + n) + t + c.size := by
  simp [weightedStateCircuit, AC0Circuit.conjunction_size, Fin.sum_univ_succ,
    activeStateVectorCircuit_size, AC0Circuit.assignmentTerm_size]
  omega

theorem weightedWord_scalar_expansion {R n t m : ℕ} (M : ℕ)
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ)
    (c : AC0Circuit m) (x : BooleanCube m) :
    (if (∀ r, (activeState (fun i => x (qindex r i))).card ≤ M) ∧ c.eval x = true
      then f (fun r => activeState (fun i => x (qindex r i))) (fun i => x (pindex i))
      else 0) =
    ∑ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      f (fun r => (b.1 r).val) b.2 *
        (weightedStateCircuit qindex pindex (fun r => (b.1 r).val) b.2 c).indicator x := by
  by_cases hx : (∀ r, (activeState (fun i => x (qindex r i))).card ≤ M) ∧ c.eval x = true
  · let b₀ : (Fin R → boundedActiveStates n M) × BooleanCube t :=
      (fun r => ⟨activeState (fun i => x (qindex r i)), mem_boundedActiveStates.mpr (hx.1 r)⟩,
        fun i => x (pindex i))
    rw [if_pos hx, sum_eq_single b₀]
    · have he := (weightedStateCircuit_eval qindex pindex
        (fun r => (b₀.1 r).val) b₀.2 c x).mpr ⟨fun _ => rfl, rfl, hx.2⟩
      simp only [AC0Circuit.indicator, he, ite_true, mul_one]
      rfl
    · intro b _ hb
      have he : (weightedStateCircuit qindex pindex
          (fun r => (b.1 r).val) b.2 c).eval x ≠ true := by
        intro he
        obtain ⟨hS, hp, _⟩ := (weightedStateCircuit_eval qindex pindex _ _ c x).mp he
        apply hb
        apply Prod.ext
        · funext r
          exact Subtype.ext (hS r).symm
        · exact hp.symm
      simp [AC0Circuit.indicator, he]
    · simp
  · rw [if_neg hx]
    symm
    apply sum_eq_zero
    intro b _
    have he : (weightedStateCircuit qindex pindex
        (fun r => (b.1 r).val) b.2 c).eval x ≠ true := by
      intro he
      obtain ⟨hS, _, hc⟩ := (weightedStateCircuit_eval qindex pindex _ _ c x).mp he
      apply hx
      refine ⟨?_, hc⟩
      intro r
      rw [hS r]
      exact mem_boundedActiveStates.mp (b.1 r).property
    simp [AC0Circuit.indicator, he]

lemma weightedWord_coefficient_mass {R n t M : ℕ}
    (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      |f (fun r => (b.1 r).val) b.2| ≤ C) :
    (∑ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      |f (fun r => (b.1 r).val) b.2|) ≤
        (((M + 1) * (n + 1) ^ M : ℕ) : ℝ) ^ R * (2 : ℝ) ^ t * C := by
  calc
    _ ≤ ∑ _b : (Fin R → boundedActiveStates n M) × BooleanCube t, C :=
      sum_le_sum (fun b _ => hf b)
    _ = ((boundedActiveStates n M).card : ℝ) ^ R * (2 : ℝ) ^ t * C := by
      simp [BooleanCube, Fintype.card_prod, Nat.cast_mul, Nat.cast_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast boundedActiveStates_card n M) R)
        (by positivity)) hC

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WeightedWordBudget
namespace OAI

/-! Size and coefficient budgets for the actual finite-word expansion. -/

namespace TwoPointCorrelations

lemma weightedWord_coefficient_budget {R n t M : ℕ} (L : ℝ)
    (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ)
    (hL : 4800 ≤ L) (hn : (n : ℝ) ≤ Real.exp L)
    (hM : (M : ℝ) ≤ 400 * Real.log L) (hR : (R : ℝ) ≤ 4 * L)
    (ht : (t : ℝ) ≤ L ^ 2)
    (hf : ∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      |f (fun r => (b.1 r).val) b.2| ≤ Real.exp (L ^ 4)) :
    (∑ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      |f (fun r => (b.1 r).val) b.2|) ≤ Real.exp (L ^ 5) := by
  have hLp : 0 ≤ L := by linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ht' : (2 : ℝ) ^ t ≤ Real.exp (L ^ 2) := by
    calc
      _ ≤ (Real.exp 1) ^ t := pow_le_pow_left₀ (by norm_num) htwo t
      _ = Real.exp (t : ℝ) := by rw [← Real.exp_nat_mul]; simp
      _ ≤ _ := Real.exp_le_exp.mpr ht
  apply (weightedWord_coefficient_mass f (Real.exp (L ^ 4)) (Real.exp_pos _).le hf).trans
  calc
    _ ≤ Real.exp (L ^ 4) * Real.exp (L ^ 2) * Real.exp (L ^ 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (active_state_family_cost L n M R hL hn hM hR) ht'
          (by positivity) (by positivity)) (by positivity)
    _ = Real.exp (2 * L ^ 4 + L ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by norm_num)
      have h45 : 3 * L ^ 4 ≤ L ^ 5 := by
        calc
          _ ≤ L * L ^ 4 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hLp _)
          _ = _ := by ring
      linarith

lemma weightedStateCircuit_size_budget {R n t m : ℕ} (L : ℝ)
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m)
    (hL : 8 ≤ L) (hn : (n : ℝ) ≤ Real.exp L) (hR : (R : ℝ) ≤ 4 * L)
    (ht : (t : ℝ) ≤ L ^ 2) (hc : (c.size : ℝ) ≤ Real.exp (L ^ 3)) :
    ((weightedStateCircuit qindex pindex S bits c).size : ℝ) ≤ Real.exp (L ^ 6) := by
  rw [weightedStateCircuit_size]
  push_cast
  have hLp : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hEL : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hE1 : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp_iff.mpr hLp
  have hE8 : (8 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hR' : (R : ℝ) * (1 + n) ≤ Real.exp (3 * L) := by
    calc
      _ ≤ (4 * L) * (2 * Real.exp L) :=
        mul_le_mul hR (by linarith) (by positivity) (by positivity)
      _ ≤ 8 * (Real.exp L * Real.exp L) := by nlinarith [Real.exp_pos L]
      _ ≤ Real.exp L * (Real.exp L * Real.exp L) :=
        mul_le_mul_of_nonneg_right hE8 (by positivity)
      _ = Real.exp (3 * L) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hL3 : 3 * L ≤ L ^ 3 := by nlinarith
  have hE3 : Real.exp (3 * L) ≤ Real.exp (L ^ 3) := Real.exp_le_exp.mpr hL3
  have ht' : (t : ℝ) ≤ Real.exp (L ^ 3) := by
    calc
      _ ≤ L ^ 2 := ht
      _ ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
      _ ≤ Real.exp (L ^ 3) := by linarith [Real.add_one_le_exp (L ^ 3)]
  have hE4 : (4 : ℝ) ≤ Real.exp (L ^ 3) := by
    linarith [Real.add_one_le_exp (L ^ 3)]
  have h36 : 2 * L ^ 3 ≤ L ^ 6 := by
    have h3 : 2 ≤ L ^ 3 := by nlinarith
    nlinarith [sq_nonneg (L ^ 3 - 1)]
  calc
    _ ≤ 4 * Real.exp (L ^ 3) := by linarith [hR'.trans hE3]
    _ ≤ Real.exp (L ^ 3) * Real.exp (L ^ 3) :=
      mul_le_mul_of_nonneg_right hE4 (by positivity)
    _ = Real.exp (2 * L ^ 3) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr h36

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WeightedWordComparison
namespace OAI

/-! Finite-origin comparison for signed weighted words. All centered
prime bits, bounded padding states, and the surviving-site circuit are
expanded together, before taking any absolute values. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

theorem BravermanDepth22Input.eventually_weighted_word_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (R n t Ninput M : ℕ), (n : ℝ) ≤ Real.exp L →
      (M : ℝ) ≤ 400 * Real.log L → (R : ℝ) ≤ 4 * L → (t : ℝ) ≤ L ^ 2 →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (qindex : Fin R → Fin n → Fin Ninput) (pindex : Fin t → Fin Ninput)
        (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ) (c : AC0Circuit Ninput),
      (∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
        |f (fun r => (b.1 r).val) b.2| ≤ Real.exp (L ^ 4)) →
      c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
        then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
        else 0
      |uniformAverage (fun x : Fin N => F (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hscalar⟩ := hBr.eventually_scalar_residue_comparison 1 (by norm_num)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hscalar, eventually_ge_atTop (4800 : ℝ)] with L hscalar hL
  intro m s _ hm hmexp hcop hs R n t Ninput M hn hM hR ht coord test qindex pindex f c hf hc hsize a N hN
  let circuits := fun b : (Fin R → boundedActiveStates n M) × BooleanCube t =>
    weightedStateCircuit qindex pindex (fun r => (b.1 r).val) b.2 c
  let coeff := fun b : (Fin R → boundedActiveStates n M) × BooleanCube t =>
    f (fun r => (b.1 r).val) b.2
  have hb := hscalar m s hm hmexp hcop hs _ Ninput coord test circuits coeff
    (fun b => weightedStateCircuit_depth qindex pindex _ _ c hc)
    (fun b => weightedStateCircuit_size_budget L qindex pindex _ _ c (by linarith) hn hR ht hsize)
    (by simpa only [one_mul] using weightedWord_coefficient_budget L f hL hn hM hR ht hf)
    a N hN
  have hexpand (z : ∀ j, ZMod (s j)) :
      (if (∀ r, (activeState (fun i => residueCircuitInputs s coord test z (qindex r i))).card ≤ M) ∧
          c.eval (residueCircuitInputs s coord test z) = true
        then f (fun r => activeState (fun i => residueCircuitInputs s coord test z (qindex r i)))
          (fun i => residueCircuitInputs s coord test z (pindex i)) else 0) =
      ∑ b : (Fin R → boundedActiveStates n M) × BooleanCube t, coeff b *
        eventIndicator (residueCircuitEvent s coord test (circuits b)) z :=
    weightedWord_scalar_expansion M qindex pindex f c (residueCircuitInputs s coord test z)
  dsimp only
  simpa only [← hexpand] using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.AffineWeightedWordComparison
namespace OAI

/-! The existing signed word comparison on each fixed progression class.
All state, circuit and coefficient budgets remain unchanged. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

theorem BravermanDepth22Input.eventually_affine_weighted_word_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (R n t Ninput M : ℕ), (n : ℝ) ≤ Real.exp L →
      (M : ℝ) ≤ 400 * Real.log L → (R : ℝ) ≤ 4 * L → (t : ℝ) ≤ L ^ 2 →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (qindex : Fin R → Fin n → Fin Ninput) (pindex : Fin t → Fin Ninput)
        (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ) (c : AC0Circuit Ninput),
      (∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
        |f (fun r => (b.1 r).val) b.2| ≤ Real.exp (L ^ 4)) →
      c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ a l N : ℕ, (∀ i, l.Coprime (s i)) → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
        then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
        else 0
      |uniformAverage (fun x : Fin N => F (fun j => (a + l * x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hbase⟩ := hBr.eventually_weighted_word_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbase] with L hbase
  intro m s _ hm hmexp hcop hs R n t Ninput M hn hM hR ht coord test qindex pindex f c hf hc hsize a l N hl hN
  let affineTest := fun i (z : ZMod (s (coord i))) =>
    test i ((a : ZMod (s (coord i))) + (l : ZMod (s (coord i))) * z)
  let F := fun z : ∀ j, ZMod (s j) =>
    let bits := residueCircuitInputs s coord test z
    if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
    then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
    else 0
  let G := fun z : ∀ j, ZMod (s j) =>
    let bits := residueCircuitInputs s coord affineTest z
    if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
    then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
    else 0
  have hbits (z : ∀ j, ZMod (s j)) : residueCircuitInputs s coord affineTest z =
      residueCircuitInputs s coord test (fun j => (a : ZMod (s j)) + (l : ZMod (s j)) * z j) := rfl
  have hG (z : ∀ j, ZMod (s j)) : G z =
      F (fun j => (a : ZMod (s j)) + (l : ZMod (s j)) * z j) := by
    dsimp only [G, F]
    rw [hbits]
  have hb := hbase m s hm hmexp hcop hs R n t Ninput M hn hM hR ht
    coord affineTest qindex pindex f c hf hc hsize 0 N hN
  change |uniformAverage (fun x : Fin N => G (fun j => ((0 : ℕ) : ZMod (s j)) + x.val)) -
    uniformAverage G| ≤ Real.exp (-(L ^ 9)) at hb
  have hGfun : G = fun z => F (fun j => (a : ZMod (s j)) + (l : ZMod (s j)) * z j) := funext hG
  rw [hGfun] at hb
  rw [uniformAverage_residue_affine s a l hl F] at hb
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_zero, zero_add] using hb

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_affine_weighted_word_comparison := @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_affine_weighted_word_comparison
