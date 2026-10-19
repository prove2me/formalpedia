-- Prove2me | solution 1 for OAI.Erdos3.exists_manuscriptRelativePatchPower_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:02:03.000483+00:00
-- url     : https://prove2.me/submissions/5816b361-dd3e-4f79-a58e-4fd97f10e6a7

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B265
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_relativePatch_scalarBase_fin_power_s2
import Theorems.Thm_OAI_Erdos3_exists_preparedRelativePatchPowerPassage_s2
import Theorems.Thm_OAI_Erdos3_exists_prepared_polynomial_layer_exp_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem relativePatchDistinctWeights_eq_zero_iff {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : relativePatchDistinctWeights A = 0 ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have hm : A.weight i ∈ Finset.univ.image A.weight :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have he : Finset.univ.image A.weight = ∅ := Finset.card_eq_zero.mp h
    simp only [he, Finset.notMem_empty] at hm
  · rintro rfl
    simp [relativePatchDistinctWeights]

theorem RelativePatchSliceConclusion.mono {X : Type*} [Fintype X] {s : ℕ}
    {N : X → ℕ} {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound rankBound' : ℕ}
    {cost cost' : ℝ} (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hrank : rankBound ≤ rankBound') (hcost : cost ≤ cost') :
    RelativePatchSliceConclusion s N f target rankBound' cost' := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  have he : Real.exp (-cost') ≤ Real.exp (-cost) :=
    Real.exp_le_exp.mpr (neg_le_neg hcost)
  exact ⟨q, hq, S, d, A, fun i =>
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)).trans (hlength i),
    hd.trans hrank, hcomplexity.trans hcost, he.trans hscore⟩

end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

theorem eval_slice_substitute {I V : Type*} [AddCommGroup V] [Module ℝ V]
    {N : I → ℕ} {q : ℕ} (S : ResidueBoxSlice N q) (p : VectorPolynomial I ℝ V)
    (x : ∀ i, Fin (S.length i)) :
    eval (fun i => ((x i).val : ℝ)) (substitute S.polynomial p) =
      eval (fun i => ((S.point x i).val : ℝ)) p := by
  simp only [eval_substitute, ResidueBoxSlice.polynomial_eval]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} {N : X → ℕ} {q : ℕ}

theorem integerAffine_mem_integerBox [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) {x : X → ℤ} (hx : x ∈ integerBox S.length) :
    S.integerAffine x ∈ integerBox N := by
  have hx' := (mem_integerBox S.length x).mp hx
  apply (mem_integerBox N _).mpr
  intro i
  have hnat : (x i).toNat < S.length i := by
    have := hx' i
    omega
  have hin := S.inside i (x i).toNat hnat
  have hcast : (S.start i : ℤ) + (q : ℤ) * ((x i).toNat : ℤ) < (N i : ℤ) := by
    exact_mod_cast hin
  rw [Int.toNat_of_nonneg (hx' i).1] at hcast
  exact ⟨add_nonneg (Int.natCast_nonneg _) (mul_nonneg (Int.natCast_nonneg _) (hx' i).1),
    hcast⟩

theorem pullback_apFree [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) (hq : 0 < q) {f : (X → ℤ) → ℝ} {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {x | x ∈ integerBox S.length ∧ S.integerPullback f x ≠ 0} k := by
  intro a d hd
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hstep : (fun j => (q : ℤ) * d j) ≠ 0 := by
    intro he
    apply hd
    funext j
    exact (mul_eq_zero.mp (congrFun he j)).resolve_left hq0
  obtain ⟨i, hi⟩ := hfree (S.integerAffine a) (fun j => (q : ℤ) * d j) hstep
  refine ⟨i, ?_⟩
  rintro ⟨hx, hf⟩
  apply hi
  have he : S.integerAffine a + (i.val : ℤ) • (fun j => (q : ℤ) * d j) =
      S.integerAffine (a + (i.val : ℤ) • d) := by
    funext j
    simp only [integerAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact ⟨S.integerAffine_mem_integerBox hx, hf⟩

end ResidueBoxSlice

theorem relativePatchBoxScore_pullback {X : Type*} [Fintype X] [DecidableEq X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore S.length (S.integerPullback f) a A =
      relativePatchSliceScore S f a A := by
  classical
  symm
  unfold relativePatchSliceScore relativePatchBoxScore
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    exact (mem_integerBox S.length _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩)
  · intro t _
    simp only [ResidueBoxSlice.integerPullback, ResidueBoxSlice.integerAffine_finPoint,
      Int.cast_natCast]
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox S.length x).mp hx
    refine ⟨fun i => ⟨(x i).toNat, by have := hx' i; omega⟩, by simp only [Finset.mem_univ], ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hx' i).1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCoordinateEquiv
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem coordinateReindexedFunction_expect (e : X ≃ Y) (N : X → ℕ)
    (f : (X → ℤ) → ℝ) :
    (𝔼 y ∈ integerBox (coordinateReindexedSides e N), coordinateReindexedFunction e f y) =
      𝔼 x ∈ integerBox N, f x := by
  apply Finset.expect_bij (fun y _ x => y (e x))
  · intro y hy
    exact (coordinateReindexedSides_mem_integerBox e N y).mp hy
  · intro y _
    rfl
  · intro y _ z _ he
    funext j
    simpa only [e.apply_symm_apply] using congrFun he (e.symm j)
  · intro x hx
    refine ⟨fun j => x (e.symm j), ?_, ?_⟩
    · apply (coordinateReindexedSides_mem_integerBox e N _).mpr
      simpa only [e.symm_apply_apply] using hx
    · funext i
      simp only [e.symm_apply_apply]

theorem coordinateReindexedFunction_bounds (e : X ≃ Y) (N : X → ℕ)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ y ∈ integerBox (coordinateReindexedSides e N),
      coordinateReindexedFunction e f y ∈ Set.Icc (0 : ℝ) 1 := by
  intro y hy
  exact hf _ ((coordinateReindexedSides_mem_integerBox e N y).mp hy)

theorem coordinateReindexedFunction_apFree (e : X ≃ Y) (N : X → ℕ)
    (f : (X → ℤ) → ℝ) {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {y | y ∈ integerBox (coordinateReindexedSides e N) ∧
        coordinateReindexedFunction e f y ≠ 0} k := by
  intro a d hd
  have hd' : (fun x => d (e x)) ≠ 0 := by
    intro hzero
    apply hd
    funext j
    simpa only [e.apply_symm_apply, Pi.zero_apply] using congrFun hzero (e.symm j)
  obtain ⟨i, hi⟩ := hfree (fun x => a (e x)) (fun x => d (e x)) hd'
  refine ⟨i, ?_⟩
  rintro ⟨hbox, hnonzero⟩
  apply hi
  refine ⟨?_, ?_⟩
  · exact (coordinateReindexedSides_mem_integerBox e N _).mp hbox
  · exact hnonzero

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_unitInterval {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, relativeBoxInput N f x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x
  by_cases hx : x ∈ integerBox N
  · simpa only [relativeBoxInput_eq N f hx] using hf x hx
  · simp only [relativeBoxInput, if_neg hx, Set.mem_Icc]
    constructor <;> norm_num

theorem relativeBoxInput_progressionFree {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree {x | x ∈ integerBox N ∧ relativeBoxInput N f x ≠ 0} k := by
  convert hfree using 1
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by simpa only [relativeBoxInput_eq N f hx] using h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by simpa only [relativeBoxInput_eq N f hx] using h⟩

theorem relativePatchBoxScore_congr_input {X : Type*} [Fintype X] [DecidableEq X]
    {s d : ℕ} (N : X → ℕ) {f g : (X → ℤ) → ℝ}
    (hfg : ∀ x ∈ integerBox N, f x = g x) (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore N f target A = relativePatchBoxScore N g target A := by
  apply Finset.expect_congr rfl
  intro x hx
  rw [hfg x hx]

theorem relativePatchSliceScore_congr_input {X : Type*} [Fintype X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    {f g : (X → ℤ) → ℝ} (hfg : ∀ x ∈ integerBox N, f x = g x)
    (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchSliceScore S f target A = relativePatchSliceScore S g target A := by
  apply Finset.expect_congr rfl
  intro x _
  have hx : (fun i => ((S.point x i).val : ℤ)) ∈ integerBox N := by
    rw [mem_integerBox]
    intro i
    exact ⟨by positivity, by exact_mod_cast (S.point x i).isLt⟩
  rw [hfg _ hx]

theorem RelativePatchSliceConclusion.congr_input {X : Type*} [Fintype X]
    {s : ℕ} {N : X → ℕ} {f g : (X → ℤ) → ℝ}
    {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hfg : ∀ x ∈ integerBox N, f x = g x) :
    RelativePatchSliceConclusion s N g target rankBound cost := by
  obtain ⟨q, hq, S, d, A, hlength, hrank, hcost, hscore⟩ := h
  refine ⟨q, hq, S, d, A, hlength, hrank, hcost, ?_⟩
  rwa [relativePatchSliceScore_congr_input S hfg target A] at hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget
namespace OAI

section

namespace Erdos3

private theorem preparationCoordinateCap_real_bound {s m D : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hm : m ≤ s) (hD : (D : ℝ) ≤ p) :
    (preparationCoordinateCap m D (m * D) : ℝ) ≤
      p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1 := by
  have hT : (m : ℝ) * D ≤ (s : ℝ) * p :=
    mul_le_mul (Nat.cast_le.mpr hm) hD (Nat.cast_nonneg D) (Nat.cast_nonneg s)
  have hpowers : ((m : ℝ) * D + 1) ^ m ≤ ((s : ℝ) * p + 1) ^ s :=
    (pow_le_pow_left₀ (by positivity) (add_le_add hT le_rfl) m).trans
      (pow_le_pow_right₀ (by nlinarith [mul_nonneg (Nat.cast_nonneg s) hp]) hm)
  have hmul := mul_le_mul hD hpowers (by positivity : 0 ≤ ((m : ℝ) * D + 1) ^ m) hp
  simp only [preparationCoordinateCap, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
  linarith

theorem exists_preparation_input_power_budget (s e : ℕ) :
    ∃ a E : ℕ, 2 ≤ a ∧ 2 ≤ E ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ m D dim R : ℕ, m ≤ s → (D : ℝ) ≤ p → (dim : ℝ) ≤ p →
        (R : ℝ) ≤ Real.exp ((p + 2) ^ e) →
        let pPrep := (p + 2) ^ a
        let δ := Real.exp (-((p + 2) ^ e))
        let T := m * D
        let M := preparationCoordinateCap m D T
        0 ≤ pPrep ∧ (M : ℝ) ≤ pPrep ∧ (m : ℝ) ≤ pPrep ∧ (dim : ℝ) ≤ pPrep ∧
          (T : ℝ) + 1 ≤ pPrep ∧ 0 < δ ∧
          (δ / ((T : ℝ) * M + 1))⁻¹ ≤ Real.exp pPrep ∧
          (R : ℝ) ≤ Real.exp pPrep ∧
          (pPrep + 2) ^ (budgetDepthExponent 38 m + 7) ≤ (p + 2) ^ E := by
  let Mpoly : Polynomial ℕ :=
    Polynomial.X * (Polynomial.C s * Polynomial.X + 1) ^ s + Polynomial.X +
      Polynomial.C s * Polynomial.X + 1
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ e +
    (Polynomial.C s * Polynomial.X) * Mpoly + Mpoly +
      Polynomial.C s * Polynomial.X + Polynomial.X + Polynomial.C s + 2
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_fixed_power_budget Q
  let E := (a + 2) * (budgetDepthExponent 38 s + 7)
  refine ⟨a, E, ha, by dsimp [E]; nlinarith [preparationExponent_pos s], ?_⟩
  intro p hp m D dim R hm hD hdim hR
  dsimp only
  have hp0 : 0 ≤ p := by linarith
  let Mup := p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1
  let T := m * D
  let M := preparationCoordinateCap m D T
  let δ := Real.exp (-((p + 2) ^ e))
  let pPrep := (p + 2) ^ a
  have hMup : 0 ≤ Mup := by dsimp [Mup]; positivity
  have hTup : 0 ≤ (s : ℝ) * p := mul_nonneg (Nat.cast_nonneg s) hp0
  have hprod0 : 0 ≤ (s : ℝ) * p * Mup := mul_nonneg hTup hMup
  have hpow0 : 0 ≤ (p + 2) ^ e := by positivity
  have hbudget : (p + 2) ^ e + (s : ℝ) * p * Mup + Mup + (s : ℝ) * p + p + s + 2 ≤ pPrep := by
    simpa [Q, Mpoly, Mup, pPrep, Polynomial.eval₂_pow] using hbound p hp0
  have hM : (M : ℝ) ≤ Mup := preparationCoordinateCap_real_bound hp0 hm hD
  have hT : (T : ℝ) ≤ (s : ℝ) * p := by
    dsimp only [T]
    rw [Nat.cast_mul]
    exact mul_le_mul (Nat.cast_le.mpr hm) hD (Nat.cast_nonneg D) (Nat.cast_nonneg s)
  have hTM : (T : ℝ) * M ≤ (s : ℝ) * p * Mup :=
    mul_le_mul hT hM (Nat.cast_nonneg M) hTup
  have hpPrep : 0 ≤ pPrep := by dsimp [pPrep]; positivity
  have hApPrep : (p + 2) ^ e ≤ pPrep := by linarith
  have hshare : (δ / ((T : ℝ) * M + 1))⁻¹ ≤ Real.exp pPrep := by
    calc
      _ = ((T : ℝ) * M + 1) * Real.exp ((p + 2) ^ e) := by
        simp only [δ, div_eq_mul_inv, Real.exp_neg, mul_inv_rev, inv_inv]
      _ ≤ Real.exp ((T : ℝ) * M) * Real.exp ((p + 2) ^ e) :=
        mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_nonneg _)
      _ = Real.exp ((T : ℝ) * M + (p + 2) ^ e) := (Real.exp_add _ _).symm
      _ ≤ Real.exp pPrep := Real.exp_le_exp.mpr (by linarith)
  refine ⟨hpPrep, ?_, ?_, ?_, ?_, Real.exp_pos _, hshare,
    hR.trans (Real.exp_le_exp.mpr hApPrep), ?_⟩
  · exact hM.trans (by linarith)
  · have hmR : (m : ℝ) ≤ s := Nat.cast_le.mpr hm
    linarith
  · exact hdim.trans (by linarith)
  · linarith
  · have hdepth : budgetDepthExponent 38 m + 7 ≤ budgetDepthExponent 38 s + 7 :=
      Nat.add_le_add_right (preparationExponent_mono hm) 7
    exact (pow_le_pow_right₀ (by linarith : 1 ≤ pPrep + 2) hdepth).trans
      (shifted_power_budget_le hp0 a (budgetDepthExponent 38 s + 7))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedSourceSideBudget
namespace OAI

section

namespace Erdos3

theorem prepared_slice_length_fraction {cost N length : ℝ}
    (hloss : N ≤ Real.exp cost * length) :
    Real.exp (-cost) * N ≤ length := by
  calc
    _ ≤ Real.exp (-cost) * (Real.exp cost * length) :=
      mul_le_mul_of_nonneg_left hloss (Real.exp_nonneg _)
    _ = length := by rw [← mul_assoc, ← Real.exp_add]; simp

theorem prepared_source_cost_add_required {p required : ℝ} {c e : ℕ}
    (hp : 2 ≤ p) (hrequired : required ≤ (p + 2) ^ e) :
    (p + 2) ^ c + required ≤ (p + 2) ^ (max c e + 1) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hc : (p + 2) ^ c ≤ (p + 2) ^ max c e :=
    pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
  have he : (p + 2) ^ e ≤ (p + 2) ^ max c e :=
    pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
  rw [pow_succ]
  have hpow : 0 ≤ (p + 2) ^ max c e := by positivity
  nlinarith

theorem prepared_source_side_budget {p required N length : ℝ} {c e : ℕ}
    (hp : 2 ≤ p) (hrequired : required ≤ (p + 2) ^ e)
    (hlarge : Real.exp ((p + 2) ^ (max c e + 1)) ≤ N)
    (hloss : N ≤ Real.exp ((p + 2) ^ c) * length) :
    Real.exp required ≤ length ∧
      Real.exp (-((p + 2) ^ c)) * N ≤ length := by
  refine ⟨?_, prepared_slice_length_fraction hloss⟩
  apply le_of_mul_le_mul_left _ (Real.exp_pos ((p + 2) ^ c))
  calc
    Real.exp ((p + 2) ^ c) * Real.exp required =
        Real.exp ((p + 2) ^ c + required) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ (max c e + 1)) :=
      Real.exp_le_exp.mpr (prepared_source_cost_add_required hp hrequired)
    _ ≤ N := hlarge
    _ ≤ Real.exp ((p + 2) ^ c) * length := hloss

theorem prepared_source_side_budgets {X : Type*} {p required : ℝ} {c e : ℕ}
    (hp : 2 ≤ p) (hrequired : required ≤ (p + 2) ^ e)
    (N length : X → ℕ)
    (hlarge : ∀ i, Real.exp ((p + 2) ^ (max c e + 1)) ≤ N i)
    (hloss : ∀ i, (N i : ℝ) ≤ Real.exp ((p + 2) ^ c) * length i) :
    (∀ i, Real.exp required ≤ (length i : ℝ)) ∧
      (∀ i, Real.exp (-((p + 2) ^ c)) * N i ≤ (length i : ℝ)) := by
  have h i := prepared_source_side_budget hp hrequired (hlarge i) (hloss i)
  exact ⟨fun i => (h i).1, fun i => (h i).2⟩

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

theorem degreeLE_subtraction {I V : Type*} [AddCommGroup V] [Module ℝ V]
    {d : ℕ} {p q : VectorPolynomial I ℝ V}
    (hp : DegreeLE (fun _ => 1) d p) (hq : DegreeLE (fun _ => 1) d q) :
    DegreeLE (fun _ => 1) d (p - q) := by
  intro α hα
  simp only [map_sub, Finsupp.sub_apply, hp α hα, hq α hα, sub_self]

theorem integerCoordinates_degree {I J : Type*} [Fintype J] {d : ℕ}
    (ip : J → MvPolynomial I ℤ) (hip : ∀ j, (ip j).totalDegree ≤ d) :
    DegreeLE (fun _ => 1) d (integerCoordinates ip) := by
  classical
  intro α hα
  have hs : d < ∑ i ∈ α.support, α i := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_one] using hα
  rw [integerCoordinates, coefficients_ofCoordinates]
  apply Finset.sum_eq_zero
  intro j _
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_eq_zero_of_totalDegree_lt ((hip j).trans_lt hs)]
  simp

theorem integerCoordinates_eval {I J : Type*} [Fintype J]
    (ip : J → MvPolynomial I ℤ) (x : I → ℤ) :
    eval (fun i => (x i : ℝ)) (integerCoordinates ip) =
      fun j => (MvPolynomial.eval x (ip j) : ℝ) := by
  have he : eval₂ (fun i => (x i : ℝ)) (integerCoordinates ip) =
      eval (fun i => (x i : ℝ)) (integerCoordinates ip) := by
    simpa using (eval₂_algebraMap (S := ℝ) (fun i => (x i : ℝ)) (integerCoordinates ip))
  rw [← he, integerCoordinates, eval₂_ofCoordinates, Pi.basisFun_equivFun]
  funext j
  exact (MvPolynomial.map_eval (Int.castRingHom ℝ) x (ip j)).symm

end VectorPolynomial

namespace RankPreparationFamily

theorem polynomial_eval {I J : Type} [DecidableEq J] {s : ℕ}
    (L : RankPreparationFamily I J s) (x : I → ℝ) : eval x L.polynomial = L.value x := by
  simp only [polynomial, map_sum, eval_map]
  rfl

end RankPreparationFamily

theorem prepared_error_polynomial {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    {s q : ℕ} {δ : ℝ} {N : I → ℕ} (S : ResidueBoxSlice N q)
    (P : VectorPolynomial I ℝ (J → ℝ)) (hP : DegreeLE (fun _ => 1) s P)
    (L : RankPreparationFamily I J s)
    (hL : ∀ u, DegreeLE (fun _ => 1) (u.val + 1) (L u).poly)
    (ip : J → MvPolynomial I ℤ) (hip : ∀ j, (ip j).totalDegree ≤ s)
    (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ)
    (herr : ∀ x j, |err x j| ≤ δ)
    (hid : ∀ x j, eval (fun i => ((S.point x i).val : ℝ)) P j =
      L.value (fun i => ((x i).val : ℝ)) j +
      (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j) :
    ∃ E : VectorPolynomial I ℝ (J → ℝ), DegreeLE (fun _ => 1) s E ∧
      substitute S.polynomial P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E ∧
      ∀ (x : ∀ i, Fin (S.length i)) (j : J), |eval (fun i => ((x i).val : ℝ)) E j| ≤ δ := by
  let E := substitute S.polynomial P - L.polynomial - integerCoordinates ip - (1 ⊗ₜ[ℝ] c)
  have hE : DegreeLE (fun _ => 1) s E := by
    apply degreeLE_subtraction
    · apply degreeLE_subtraction
      · exact degreeLE_subtraction (degreeLE_substitute_affine S.polynomial S.polynomial_degree P hP)
          (L.polynomial_degree hL)
      · exact integerCoordinates_degree ip hip
    · exact degreeLE_tmul_totalDegree 1 c (by simp)
  refine ⟨E, hE, ?_, ?_⟩
  · dsimp [E]
    abel
  · intro x j
    have hint := integerCoordinates_eval ip (fun i => ((x i).val : ℤ))
    simp only [Int.cast_natCast] at hint
    have heval : eval (fun i => ((x i).val : ℝ)) E j = err x j := by
      dsimp only [E]
      rw [map_sub, map_sub, map_sub, eval_slice_substitute, RankPreparationFamily.polynomial_eval, hint]
      simp only [Pi.sub_apply, eval_tmul, map_one, one_smul]
      linarith [hid x j]
    rw [heval]
    exact herr x j

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

theorem normalizedOrigin_degree (i : Fin D) :
    L.normalizedOrigin i ∈ weightedSupportLE (fun _ : σ => 1) h :=
  polynomialMatrixAction_degree _ L.origin L.degree i

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchWeightDescent
namespace OAI

section

namespace Erdos3

theorem exists_monotone_lowest_weight_prefix {d : ℕ} (w : Fin d → ℕ)
    (hmono : Monotone w) (hd : 0 < d) :
    ∃ D : ℕ, 0 < D ∧ D ≤ d ∧
      (∀ i : Fin d, i.val < D → w i = w ⟨0, hd⟩) ∧
      (∀ i : Fin d, D ≤ i.val → w ⟨0, hd⟩ < w i) := by
  classical
  let above := fun D : ℕ => D ≤ d ∧ ∀ i : Fin d, D ≤ i.val → w ⟨0, hd⟩ < w i
  have hex : ∃ D, above D := ⟨d, le_rfl, fun i hi => False.elim (by omega)⟩
  let D := Nat.find hex
  have hD : above D := Nat.find_spec hex
  have hpos : 0 < D := by
    by_contra hn
    have hzero : D = 0 := by omega
    have hh := hD.2 ⟨0, hd⟩ (by omega)
    exact (lt_irrefl _) hh
  refine ⟨D, hpos, hD.1, ?_, hD.2⟩
  intro i hi
  apply le_antisymm
  · by_contra hn
    have hstrict : w ⟨0, hd⟩ < w i := by omega
    have hcut : above i.val := ⟨i.isLt.le, fun k hk =>
      hstrict.trans_le (hmono (show i ≤ k from hk))⟩
    have hminimal : D ≤ i.val := Nat.find_min' hex hcut
    omega
  · exact hmono (show (⟨0, hd⟩ : Fin d) ≤ i from Nat.zero_le _)

namespace PolynomialPatch

theorem castRank_weight_apply {X : Type*} {s d e : ℕ}
    (A : PolynomialPatch X s d) (h : d = e) (i : Fin e) :
    (A.castRank h).weight i = A.weight (i.cast h.symm) := by
  subst e
  rfl

theorem exists_lowestLayer_prefix {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) (hd : 0 < d) :
    ∃ (D j : ℕ) (hD : D ≤ d), 0 < D ∧ 1 ≤ j ∧ j ≤ s ∧
      (∀ i : Fin D,
        (A.castRank (Nat.add_sub_of_le hD).symm).weight (i.castAdd (d - D)) = j) ∧
      (∀ i : Fin (d - D),
        j < (A.castRank (Nat.add_sub_of_le hD).symm).weight (i.natAdd D)) ∧
      Nonempty ((A.castRank (Nat.add_sub_of_le hD).symm).LowestLayerModel (D := D) (E := d - D) j) := by
  obtain ⟨D, hDpos, hD, hfirst, hrest⟩ :=
    exists_monotone_lowest_weight_prefix A.weight A.weight_mono hd
  have hprefix (i : Fin D) :
      (A.castRank (Nat.add_sub_of_le hD).symm).weight (i.castAdd (d - D)) = A.weight ⟨0, hd⟩ := by
    rw [castRank_weight_apply]
    exact hfirst _ i.isLt
  refine ⟨D, A.weight ⟨0, hd⟩, hD, hDpos, A.weight_pos _, A.weight_le _, hprefix, ?_, ?_⟩
  · intro i
    rw [castRank_weight_apply]
    exact hrest _ (Nat.le_add_right D i.val)
  · exact nonempty_lowestLayerModel _ (Nat.zero_lt_of_lt (A.weight_pos _)) hprefix

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchFiniteCoordinateReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ}

theorem coordinateEquiv_value (A : PolynomialPatch X s d) (e : X ≃ Y) (y : Y → ℝ) :
    (A.coordinateEquiv e).value y = A.value (fun i => y (e i)) := by
  rw [coordinateEquiv, reparam_value]
  simp only [MvPolynomial.aeval_X]

end PolynomialPatch

theorem relativePatchBoxScore_coordinateEquiv
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {s d : ℕ} (e : X ≃ Y) (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore (coordinateReindexedSides e N) (coordinateReindexedFunction e f)
      target (A.coordinateEquiv e) = relativePatchBoxScore N f target A := by
  unfold relativePatchBoxScore
  simp only [PolynomialPatch.coordinateEquiv_value]
  exact coordinateReindexedFunction_expect e N
    (fun x => (f x - target) * A.value (fun i => (x i : ℝ)))

namespace ResidueBoxSlice

variable {X Y : Type*} {N : X → ℕ} {q : ℕ}

theorem coordinateReturn_score [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {s d : ℕ} (e : X ≃ Y) (S : ResidueBoxSlice (coordinateReindexedSides e N) q)
    (f : (X → ℤ) → ℝ) (target : ℝ) (A : PolynomialPatch Y s d) :
    relativePatchSliceScore (S.coordinateReturn e) f target (A.coordinateEquiv e.symm) =
      relativePatchSliceScore S (coordinateReindexedFunction e f) target A := by
  rw [← relativePatchBoxScore_pullback, ← relativePatchBoxScore_pullback]
  have h := relativePatchBoxScore_coordinateEquiv e.symm S.length
    (S.integerPullback (coordinateReindexedFunction e f)) target A
  convert h using 1
  congr 1
  funext x
  simp only [coordinateReindexedFunction, integerPullback, integerAffine,
    coordinateReturn, Equiv.symm_apply_apply]
  rfl

end ResidueBoxSlice

theorem RelativePatchSliceConclusion.coordinateReturn
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {s rankBound : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target cost : ℝ}
    (e : X ≃ Y)
    (h : RelativePatchSliceConclusion s (coordinateReindexedSides e N)
      (coordinateReindexedFunction e f) target rankBound cost) :
    RelativePatchSliceConclusion s N f target rankBound cost := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  refine ⟨q, hq, S.coordinateReturn e, d, A.coordinateEquiv e.symm, ?_,
    hd, hcomplexity, ?_⟩
  · intro i
    simpa only [coordinateReindexedSides, ResidueBoxSlice.coordinateReturn,
      Equiv.symm_apply_apply] using hlength (e i)
  · rwa [ResidueBoxSlice.coordinateReturn_score]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem RelativePatchFinInductionRule.to_general
    {s n₀ stage : ℕ} {τ : ℝ} {cutoff cost : ℝ → ℝ}
    (hfin : RelativePatchFinInductionRule s n₀ stage τ cutoff cost) :
    RelativePatchInductionRule s n₀ stage τ cutoff cost := by
  intro p a Λ d₀ hp ha haΛ hΛ habsolute X _ _ _ hX N hN f hf hfree d A hA hstage hscore
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  have hN' : ∀ i, Real.exp (cutoff p) ≤ (coordinateReindexedSides e N i : ℝ) :=
    fun i => hN (e.symm i)
  have hscore' : Real.exp (-p) ≤ relativePatchBoxScore (coordinateReindexedSides e N)
      (coordinateReindexedFunction e f) a (A.coordinateEquiv e) := by
    rwa [relativePatchBoxScore_coordinateEquiv]
  exact (hfin p a Λ d₀ hp ha haΛ hΛ habsolute (Fintype.card X) Fintype.card_pos hX
    (coordinateReindexedSides e N) hN' (coordinateReindexedFunction e f)
    (coordinateReindexedFunction_bounds e N f hf)
    (coordinateReindexedFunction_apFree e N f hfree)
    d (A.coordinateEquiv e) hA hstage hscore').coordinateReturn e

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchStageTransport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem relativePatchSliceScore_antitone {X : Type*} [Fintype X] {s d q : ℕ}
    {N : X → ℕ} (S : ResidueBoxSlice N q) (f : (X → ℤ) → ℝ)
    (A : PolynomialPatch X s d) {target target' : ℝ} (h : target' ≤ target) :
    relativePatchSliceScore S f target A ≤ relativePatchSliceScore S f target' A := by
  apply Finset.expect_le_expect
  intro x _
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left h _)
    (A.value_mem_Icc (fun i => ((x i).val : ℝ))).1

theorem RelativePatchSliceConclusion.target_mono {X : Type*} [Fintype X]
    {s : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target target' cost : ℝ} {D : ℕ}
    (h : RelativePatchSliceConclusion s N f target D cost) (htarget : target' ≤ target) :
    RelativePatchSliceConclusion s N f target' D cost := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  exact ⟨q, hq, S, d, A, hlength, hd, hcomplexity,
    hscore.trans (relativePatchSliceScore_antitone S f A htarget)⟩

theorem RelativePatchSliceConclusion.later_stage_target {X : Type*} [Fintype X]
    {s stage stage' D : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {τ Λ cost : ℝ}
    (h : RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage + 1) * Λ) D cost)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hΛ : 0 ≤ Λ) (hstage : stage ≤ stage') :
    RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage' + 1) * Λ) D cost := by
  apply h.target_mono
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (sub_nonneg.mpr hτ.2) (by linarith [hτ.1])
      (Nat.add_le_add_right hstage 1)) hΛ

end Erdos3

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

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedRoundedRank
namespace OAI

section

namespace Erdos3

theorem preparedRoundedRank_exp_le (p : ℝ) (e : ℕ) :
    Real.exp ((p + 2)^e) ≤ (preparedRoundedRank p e : ℝ) :=
  Nat.le_ceil _

theorem preparedRoundedRank_one_le (p : ℝ) (e : ℕ) :
    1 ≤ preparedRoundedRank p e := by
  have hpos := (Real.exp_pos ((p + 2)^e)).trans_le (preparedRoundedRank_exp_le p e)
  have : 0 < preparedRoundedRank p e := by exact_mod_cast hpos
  omega

theorem preparedRoundedRank_le_exp {p : ℝ} (hp : 2 ≤ p) (e : ℕ) :
    (preparedRoundedRank p e : ℝ) ≤ Real.exp ((p + 2)^(e + 1)) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hu : 1 ≤ (p + 2)^e := one_le_pow₀ hbase
  have hexp : 1 ≤ Real.exp ((p + 2)^e) := Real.one_le_exp_iff.mpr (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hnext : (p + 2)^e + 1 ≤ (p + 2)^(e + 1) := by
    rw [pow_succ]
    nlinarith
  calc
    _ ≤ Real.exp ((p + 2)^e) + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_nonneg ((p + 2)^e))).le
    _ ≤ Real.exp ((p + 2)^e) * 2 := by linarith
    _ ≤ Real.exp ((p + 2)^e) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
    _ = Real.exp ((p + 2)^e + 1) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hnext

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
namespace OAI

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct Classical

namespace PolynomialPatch.LowestLayerModel

variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {s D E j R : ℕ} {A : PolynomialPatch X s (D + E)}

omit [Fintype X] [DecidableEq X] in
theorem normalizedOrigin_vector_degree (F : A.LowestLayerModel (j + 1)) :
    DegreeLE (fun _ : X => 1) (j + 1)
      (VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) := by
  apply (degreeLE_iff_basis_coordinates (Pi.basisFun ℝ (Fin D)) _ _ _).mpr
  intro i
  simpa only [coordinate_ofCoordinates] using
    (mem_weightedSupportLE_iff _ _ _).mp (F.normalizedOrigin_degree i)

theorem exists_actual_prepared_slice (F : A.LowestLayerModel (j + 1))
    {p δ : ℝ} (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hδ : 0 < δ) (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (hM : (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ) ≤ p)
    (hj : ((j + 1 : ℕ) : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hT : (((j + 1) * D : ℕ) : ℝ) + 1 ≤ p)
    (hshare : (δ / ((((j + 1) * D : ℕ) : ℝ) *
      preparationCoordinateCap (j + 1) D ((j + 1) * D) + 1))⁻¹ ≤ Real.exp p)
    (hN : ∀ i, Real.exp ((p + 2) ^ (budgetDepthExponent 38 (j + 1) + 7)) ≤ N i) :
    let budget := (p + 2) ^ (budgetDepthExponent 38 (j + 1) + 7)
    ∃ (q : ℕ) (S : ResidueBoxSlice N q)
      (L : RankPreparationFamily X (Fin D) (j + 1))
      (ip : Fin D → MvPolynomial X ℤ) (c : Fin D → ℝ)
      (err : VectorPolynomial X ℝ (Fin D → ℝ)),
      0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp budget * S.length i) ∧
      (∑ u, (L u).rank) ≤ (j + 1) * D ∧
      L.Sized D ((j + 1) * D) ∧ L.PreparedHeights p R ∧
      (∀ u, Fintype.card (L u).Coord ≤ preparationCoordinateCap (j + 1) D ((j + 1) * D)) ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L u).space (L u).poly) ∧
      (∀ i, (ip i).totalDegree ≤ j + 1) ∧ DegreeLE (fun _ => 1) (j + 1) err ∧
      VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D))
        (F.reparam S.polynomial S.polynomial_weighted_support).normalizedOrigin =
          L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err ∧
      (∀ x ∈ integerBox S.length, ∀ i, |eval (fun k => (x k : ℝ)) err i| ≤ δ) ∧
      relativePatchBoxScore N f a A ≤
        relativePatchSliceScore S f a (A.reparam S.polynomial S.polynomial_weighted_support) := by
  classical
  have hdec : decX = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst decX
  let P := VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin
  have hP : DegreeLE (fun _ : X => 1) (j + 1) P := F.normalizedOrigin_vector_degree
  let score (x : ∀ i, Fin (N i)) :=
    (f (fun i => ((x i).val : ℤ)) - a) * A.value (fun i => ((x i).val : ℝ))
  obtain ⟨q, S, L, ip, c, e, hrank, hsize, hheight, hgood, hq, hqb, hlen,
      hscore, hip, he, hid⟩ :=
    exists_prepared_polynomial_layer_exp_s2 P hP hp hR hRp hδ N score
      (by simpa using hM) hj hX (by simpa using hT) (by simpa using hshare) hN
  have hdegree u := (hheight u).1
  obtain ⟨err, herrdeg, hidentity, herr⟩ :=
    prepared_error_polynomial S P hP L hdegree ip hip c e he hid
  refine ⟨q, S, L, ip, c, err, hq, hqb, hlen, ?_, ?_, hheight, ?_, hgood,
    hip, herrdeg, ?_, ?_, ?_⟩
  · simpa using hrank
  · simpa using hsize
  · intro u
    simpa using (preparationCoordinateCap_bounds hsize le_rfl u).1
  · have hn : (F.reparam S.polynomial S.polynomial_weighted_support).normalizedOrigin =
        fun i => MvPolynomial.aeval S.polynomial (F.normalizedOrigin i) :=
      funext (F.reparam_normalizedOrigin S.polynomial S.polynomial_weighted_support)
    rw [hn]
    simpa only [P, substitute_ofCoordinates] using hidentity
  · intro x hx i
    have hx' := (mem_integerBox S.length x).mp hx
    let u : ∀ k, Fin (S.length k) := fun k => ⟨(x k).toNat, by
      have := hx' k
      omega⟩
    have hu : (fun k => ((u k).val : ℝ)) = fun k => (x k : ℝ) := by
      funext k
      dsimp [u]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hx' k).1]
    rw [← hu]
    exact herr u i
  · have hparent : relativePatchBoxScore N f a A = 𝔼 x, score x := by
      symm
      unfold relativePatchBoxScore
      apply Finset.expect_bij (fun x _ i => ((x i).val : ℤ))
      · intro x _
        exact (mem_integerBox N _).mpr (fun i =>
          ⟨Int.natCast_nonneg _, by exact_mod_cast (x i).isLt⟩)
      · intro x _
        simp only [score, Int.cast_natCast]
      · intro x _ y _ h
        funext i
        apply Fin.ext
        exact_mod_cast congrFun h i
      · intro x hx
        have hx' := (mem_integerBox N x).mp hx
        refine ⟨fun i => ⟨(x i).toNat, by have := hx' i; omega⟩, Finset.mem_univ _, ?_⟩
        funext i
        exact Int.toNat_of_nonneg (hx' i).1
    rw [hparent]
    simpa only [score, relativePatchSliceScore, PolynomialPatch.reparam_value,
      ResidueBoxSlice.polynomial_eval, Int.cast_natCast] using hscore

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct

namespace PolynomialPatch.LowestLayerModel

theorem exists_uniform_prepared_slice (s errorPower : ℕ) :
    ∃ inputPower costPower : ℕ, 2 ≤ inputPower ∧ 2 ≤ costPower ∧
      ∀ (X : Type) [Fintype X] [DecidableEq X]
        (p : ℝ), 2 ≤ p →
      ∀ (D E j R : ℕ) (A : PolynomialPatch X s (D + E))
        (F : A.LowestLayerModel (j + 1)),
        j + 1 ≤ s → (D : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
        1 ≤ R → (R : ℝ) ≤ Real.exp ((p + 2) ^ errorPower) →
      ∀ (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ),
        (∀ i, Real.exp ((p + 2) ^ costPower) ≤ N i) →
      ∃ (q : ℕ) (S : ResidueBoxSlice N q)
        (L : RankPreparationFamily X (Fin D) (j + 1))
        (ip : Fin D → MvPolynomial X ℤ) (c : Fin D → ℝ)
        (err : VectorPolynomial X ℝ (Fin D → ℝ)),
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 2) ^ costPower) ∧
        (∀ i, 0 < S.length i ∧
          (N i : ℝ) ≤ Real.exp ((p + 2) ^ costPower) * S.length i) ∧
        (∑ u, (L u).rank) ≤ (j + 1) * D ∧
        L.Sized D ((j + 1) * D) ∧
        L.PreparedHeights ((p + 2) ^ inputPower) R ∧
        (∀ u, Fintype.card (L u).Coord ≤
          preparationCoordinateCap (j + 1) D ((j + 1) * D)) ∧
        (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ))
          R (L u).space (L u).poly) ∧
        (∀ i, (ip i).totalDegree ≤ j + 1) ∧
        DegreeLE (fun _ => 1) (j + 1) err ∧
        VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D))
          (F.reparam S.polynomial S.polynomial_weighted_support).normalizedOrigin =
            L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ errorPower))) ∧
        relativePatchBoxScore N f target A ≤
          relativePatchSliceScore S f target
            (A.reparam S.polynomial S.polynomial_weighted_support) := by
  obtain ⟨inputPower, costPower, hinputPower, hcostPower, hbudget⟩ :=
    exists_preparation_input_power_budget s errorPower
  refine ⟨inputPower, costPower, hinputPower, hcostPower, ?_⟩
  intro X _ _ p hp D E j R A F hj hD hX hR hRp N f target hN
  obtain ⟨hpPrep, hM, hjPrep, hXPrep, hT, hδ, hshare, hRPrep, hcost⟩ :=
    hbudget p hp (j + 1) D (Fintype.card X) R hj hD hX hRp
  have hexp := Real.exp_le_exp.mpr hcost
  obtain ⟨q, S, L, ip, c, err, hq, hqb, hlen, hrank, hsize, hheight,
      hcoord, hgood, hip, herrdeg, hid, herr, hscore⟩ :=
    F.exists_actual_prepared_slice hpPrep hR hRPrep hδ N f target
      hM hjPrep hXPrep hT hshare (fun i => hexp.trans (hN i))
  refine ⟨q, S, L, ip, c, err, hq, hqb.trans hexp, ?_, hrank, hsize,
    hheight, hcoord, hgood, hip, herrdeg, hid, herr, hscore⟩
  intro i
  exact ⟨(hlen i).1, (hlen i).2.trans
    (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _))⟩

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_lowest_weight_prepared_patch (s errorPower : ℕ) :
    ∃ inputPower costPower : ℕ, 2 ≤ inputPower ∧ 2 ≤ costPower ∧
      ∀ (X : Type) [Fintype X] [DecidableEq X] (p : ℝ), 2 ≤ p →
      ∀ (d R : ℕ) (A : PolynomialPatch X s d), 0 < d →
        relativePatchComplexity A ≤ p → (Fintype.card X : ℝ) ≤ p →
        1 ≤ R → (R : ℝ) ≤ Real.exp ((p + 2) ^ errorPower) →
      ∀ (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ),
        (∀ i, Real.exp ((p + 2) ^ costPower) ≤ (N i : ℝ)) →
      ∃ (D j : ℕ) (hD : D ≤ d), 0 < D ∧ j + 1 ≤ s ∧
      ∃ (q : ℕ) (S : ResidueBoxSlice N q),
      let A' := (A.castRank (Nat.add_sub_of_le hD).symm).reparam
        S.polynomial S.polynomial_weighted_support
      ∃ (F : A'.LowestLayerModel (D := D) (E := d - D) (j + 1))
        (L : RankPreparationFamily X (Fin D) (j + 1))
        (ip : Fin D → MvPolynomial X ℤ) (c : Fin D → ℝ)
        (err : VectorPolynomial X ℝ (Fin D → ℝ)),
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 2) ^ costPower) ∧
        (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp ((p + 2) ^ costPower) * S.length i) ∧
        (∀ i : Fin D, A'.weight (i.castAdd (d - D)) = j + 1) ∧
        (∀ i : Fin (d - D), j + 1 < A'.weight (i.natAdd D)) ∧
        A'.kernel.lip = A.kernel.lip ∧
        relativePatchComplexity A' = relativePatchComplexity A ∧
        relativePatchDistinctWeights A' = relativePatchDistinctWeights A ∧
        (∑ u, (L u).rank) ≤ (j + 1) * D ∧ (∑ u, (L u).rank) ≤ s * D ∧
        L.Sized D ((j + 1) * D) ∧ L.PreparedHeights ((p + 2) ^ inputPower) R ∧
        (∀ u, Fintype.card (L u).Coord ≤ preparationCoordinateCap (j + 1) D ((j + 1) * D)) ∧
        (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ))
          R (L u).space (L u).poly) ∧
        (∀ i, (ip i).totalDegree ≤ j + 1) ∧ DegreeLE (fun _ => 1) (j + 1) err ∧
        VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
          L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ errorPower))) ∧
        relativePatchBoxScore N f target A ≤ relativePatchSliceScore S f target A' ∧
        relativePatchBoxScore N f target A ≤
          relativePatchBoxScore S.length (S.integerPullback f) target A' := by
  obtain ⟨inputPower, costPower, hinputPower, hcostPower, hprepare⟩ :=
    PolynomialPatch.LowestLayerModel.exists_uniform_prepared_slice s errorPower
  refine ⟨inputPower, costPower, hinputPower, hcostPower, ?_⟩
  intro X _ _ p hp d R A hd hA hX hR hRp N f target hN
  obtain ⟨D, m, hD, hDpos, hmpos, hms, hfirst, hrest, hmodel⟩ :=
    A.exists_lowestLayer_prefix hd
  rcases m with _ | j
  · omega
  obtain ⟨F⟩ := hmodel
  let A₀ := A.castRank (Nat.add_sub_of_le hD).symm
  have hDp : (D : ℝ) ≤ p := (Nat.cast_le.mpr hD).trans
    ((relativePatchComplexity_rank_le A).trans hA)
  obtain ⟨q, S, L, ip, c, err, hq, hqb, hlen, hrank, hsize, hheight,
      hcoord, hgood, hip, herrdeg, hid, herr, hscore⟩ :=
    hprepare X p hp D (d - D) j R A₀ F hms hDp hX hR hRp N f target hN
  let A' := A₀.reparam S.polynomial S.polynomial_weighted_support
  have hscore' : relativePatchBoxScore N f target A ≤ relativePatchSliceScore S f target A' := by
    simpa only [A₀, relativePatchBoxScore, PolynomialPatch.castRank_value] using hscore
  refine ⟨D, j, hD, hDpos, hms, q, S,
    F.reparam S.polynomial S.polynomial_weighted_support,
    L, ip, c, err, hq, hqb, hlen, hfirst, hrest, ?_, ?_, ?_, hrank,
    hrank.trans (Nat.mul_le_mul_right D hms), hsize, hheight, hcoord,
    hgood, hip, herrdeg, hid, herr, hscore', ?_⟩
  · exact PolynomialPatch.castRank_kernel_lip A _
  · change ((D + (d - D) : ℕ) : ℝ) +
      Real.log (1 + ((A.castRank (Nat.add_sub_of_le hD).symm).kernel.lip : ℝ)) =
        relativePatchComplexity A
    rw [PolynomialPatch.castRank_kernel_lip, Nat.add_sub_of_le hD]
    rfl
  · exact relativePatchDistinctWeights_castRank A _
  · rwa [relativePatchBoxScore_pullback]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

theorem exists_lowest_weight_early_late_preparation
    (s requiredPower precisionPower : ℕ) :
    ∃ preparationPower costPower : ℕ,
      2 ≤ preparationPower ∧ 2 ≤ costPower ∧
      ∀ (X : Type) [Fintype X] [DecidableEq X] (p : ℝ), 2 ≤ p →
      ∀ (d : ℕ) (A : PolynomialPatch X s d), 0 < d →
        relativePatchComplexity A ≤ p → (Fintype.card X : ℝ) ≤ p →
      ∀ (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ),
        (∀ i, Real.exp ((p + 2) ^ (max costPower requiredPower + 1)) ≤ (N i : ℝ)) →
      let R := preparedRoundedRank p requiredPower
      ∃ (D j : ℕ) (hD : D ≤ d), 0 < D ∧ j + 1 ≤ s ∧
      ∃ (q : ℕ) (S : ResidueBoxSlice N q),
      let A' := (A.castRank (Nat.add_sub_of_le hD).symm).reparam
        S.polynomial S.polynomial_weighted_support
      ∃ (F : A'.LowestLayerModel (D := D) (E := d - D) (j + 1))
        (L : RankPreparationFamily X (Fin D) (j + 1))
        (ip : Fin D → MvPolynomial X ℤ) (c : Fin D → ℝ)
        (err : VectorPolynomial X ℝ (Fin D → ℝ)),
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 2) ^ costPower) ∧
        (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp ((p + 2) ^ costPower) * S.length i) ∧
        (∀ i : Fin D, A'.weight (i.castAdd (d - D)) = j + 1) ∧
        (∀ i : Fin (d - D), j + 1 < A'.weight (i.natAdd D)) ∧
        A'.kernel.lip = A.kernel.lip ∧
        relativePatchComplexity A' = relativePatchComplexity A ∧
        relativePatchDistinctWeights A' = relativePatchDistinctWeights A ∧
        (∑ u, (L u).rank) ≤ (j + 1) * D ∧ (∑ u, (L u).rank) ≤ s * D ∧
        L.Sized D ((j + 1) * D) ∧ L.PreparedHeights ((p + 2) ^ preparationPower) R ∧
        (∀ u, Fintype.card (L u).Coord ≤ preparationCoordinateCap (j + 1) D ((j + 1) * D)) ∧
        (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ))
          R (L u).space (L u).poly) ∧
        (∀ i, (ip i).totalDegree ≤ j + 1) ∧ DegreeLE (fun _ => 1) (j + 1) err ∧
        VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
          L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ (max (requiredPower + 1) precisionPower)))) ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ precisionPower))) ∧
        relativePatchBoxScore N f target A ≤ relativePatchSliceScore S f target A' ∧
        relativePatchBoxScore N f target A ≤
          relativePatchBoxScore S.length (S.integerPullback f) target A' ∧
        (∀ i, Real.exp ((p + 2) ^ requiredPower) ≤ (S.length i : ℝ)) ∧
        (∀ i, Real.exp (-((p + 2) ^ costPower)) * (N i : ℝ) ≤ (S.length i : ℝ)) ∧
        ∃ (b : ∀ u, Module.Basis (Fin (preparedSamplerTransverse L u)) ℝ
            (euclideanSubspace (L u).space)ᗮ)
          (_o : ∀ u, OrthonormalBasis (PreparedSamplerContinuous L u) ℝ
            (euclideanSubspace (L u).space))
          (bW : ∀ u, Module.Basis (PreparedSamplerContinuous L u) ℤ
            (latticeSection (standardEuclideanLattice (L u).Coord)
              (euclideanSubspace (L u).space))),
          (∀ u, Submodule.span ℤ (Set.range (b u)) =
            projectedIntegerLattice (euclideanSubspace (L u).space)) ∧
          (∀ u z, ‖normalizedOrthogonalChart (euclideanSubspace (L u).space) (b u) z‖ ≤
            Real.exp (allocatedUniformChartLog
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ)) * ‖z‖) ∧
          (∀ u z, ‖(normalizedOrthogonalChart (euclideanSubspace (L u).space) (b u)).symm z‖ ≤
            Real.exp (allocatedUniformChartLog
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ)) * ‖z‖) ∧
          (∀ u, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L u).space) (b u) ∧
            mixedDensityCovolumeRatio (euclideanSubspace (L u).space) (b u) ≤
              Real.exp (allocatedUniformChartLog
                (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ))) ∧
          (∀ u a, ‖(bW u a).val‖ ≤ Real.exp
            (((p + 2) ^ preparationPower +
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ) +
              (p + 2) ^ (requiredPower + 1) + 2) ^
                preparedIntegralBasisExponent (j + 1))) ∧
          (∀ u i, (basisAxisScale (b u) i : ℝ) ≤ Real.exp
            (((p + 2) ^ preparationPower +
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ) +
              (p + 2) ^ (requiredPower + 1) + 2) ^
                preparedIntegralBasisExponent (j + 1))) := by
  obtain ⟨preparationPower, costPower, hpreparationPower, hcostPower, hprepare⟩ :=
    exists_lowest_weight_prepared_patch s (max (requiredPower + 1) precisionPower)
  refine ⟨preparationPower, costPower, hpreparationPower, hcostPower, ?_⟩
  intro X _ _ p hp d A hd hA hX N f target hN
  let R := preparedRoundedRank p requiredPower
  have hNprep : ∀ i, Real.exp ((p + 2) ^ costPower) ≤ (N i : ℝ) := by
    intro i
    apply (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2)
      ((Nat.le_max_left costPower requiredPower).trans (Nat.le_succ _)))).trans (hN i)
  obtain ⟨D, j, hD, hDpos, hjs, q, S, F, L, ip, c, err,
      hq, hqb, hlen, hfirst, hrest, hLip, hComplexity, hCount, hrank, hsRank,
      hsize, hheight, hcoord, hgood, hip, herrdeg, hid, herr, hscore, hboxScore⟩ :=
    hprepare X p hp d R A hd hA hX (preparedRoundedRank_one_le p requiredPower)
      ((preparedRoundedRank_le_exp hp requiredPower).trans (Real.exp_le_exp.mpr
        (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (Nat.le_max_left _ _))))
      N f target hNprep
  have hprecision : ∀ x ∈ integerBox S.length, ∀ i,
      |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ precisionPower)) := by
    intro x hx i
    exact (herr x hx i).trans (Real.exp_le_exp.mpr (neg_le_neg
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (Nat.le_max_right _ _))))
  have hchildren := prepared_source_side_budgets hp (le_refl ((p + 2) ^ requiredPower))
    N S.length hN (fun i => (hlen i).2)
  refine ⟨D, j, hD, hDpos, hjs, q, S, F, L, ip, c, err,
    hq, hqb, hlen, hfirst, hrest, hLip, hComplexity, hCount, hrank, hsRank,
    hsize, hheight, hcoord, hgood, hip, herrdeg, hid, herr, hprecision, hscore, hboxScore,
    hchildren.1, hchildren.2, ?_⟩
  · let M := preparationCoordinateCap (j + 1) D ((j + 1) * D)
    let pLate := (p + 2) ^ preparationPower + (M : ℝ) + (p + 2) ^ (requiredPower + 1)
    have hprep0 : 0 ≤ (p + 2) ^ preparationPower := by positivity
    have hrank0 : 0 ≤ (p + 2) ^ (requiredPower + 1) := by positivity
    have hcap0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    apply hheight.exists_early_late_sampler_geometry L (pLate := pLate)
      hprep0 (preparedRoundedRank_one_le p requiredPower)
    · dsimp only [pLate]; linarith
    · apply (preparedRoundedRank_le_exp hp requiredPower).trans
      apply Real.exp_le_exp.mpr
      dsimp only [pLate]; linarith
    · exact hsize
    · exact le_rfl
    · dsimp only [pLate]; change (M : ℝ) ≤ _; linarith

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

theorem exists_relativePatchFinPositivePower_of_prepared
    {s n₀ stage : ℕ} {discount : ℝ}
    (hpassage : ∃ requiredPower precisionPower : ℕ,
      ∀ preparationPower : ℕ, 2 ≤ preparationPower →
        ∃ passagePower : ℕ, 2 ≤ passagePower ∧
          PreparedRelativePatchPowerPassage s n₀ stage discount
            requiredPower precisionPower preparationPower passagePower) :
    ∃ power : ℕ, 2 ≤ power ∧ RelativePatchFinPositivePowerRule s n₀ stage discount power := by
  obtain ⟨requiredPower, precisionPower, hpassage⟩ := hpassage
  obtain ⟨preparationPower, costPower, hprepPower, hcostPower, hprepare⟩ :=
    exists_lowest_weight_early_late_preparation s requiredPower precisionPower
  obtain ⟨passagePower, hpassagePower, hpass⟩ := hpassage preparationPower hprepPower
  let power := max (max costPower requiredPower + 1) (max costPower passagePower + 1)
  have hp1 : max costPower requiredPower + 1 ≤ power := Nat.le_max_left _ _
  have hp2 : max costPower passagePower + 1 ≤ power := Nat.le_max_right _ _
  refine ⟨power, by omega, ?_⟩
  intro p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hN f hf hfree d A hd hA hstage hscore
  have hbase : 1 ≤ p + 2 := by linarith
  let g := relativeBoxInput N f
  have hg : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 := relativeBoxInput_unitInterval N f (by simpa only [mem_integerBox] using hf)
  have hgfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ g x ≠ 0} (s + 2) := by
    simpa only [mem_integerBox] using
      relativeBoxInput_progressionFree N f (by simpa only [mem_integerBox] using hfree)
  have hgscore : Real.exp (-p) ≤ relativePatchBoxScore N g a A := by
    have heq : relativePatchBoxScore N g a A = relativePatchBoxScore N f a A := by
      apply relativePatchBoxScore_congr_input
      intro x hx
      exact relativeBoxInput_eq N f (by simpa only [mem_integerBox] using hx)
    exact hscore.trans_eq heq.symm
  have hNprep : ∀ i, Real.exp ((p + 2) ^ (max costPower requiredPower + 1)) ≤ (N i : ℝ) :=
    fun i => (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase hp1)).trans (hN i)
  obtain ⟨D, j, hD, hDpos, hjs, q, S, F, L, ip, c, err,
    hq, _hqb, hlen, _hfirst, hrest, _hLip, hcomplexity, hcount,
    hrank, _hsrank, hsize, hheight, hcoord, hgood, hip, herrdeg, hid,
    _herrStrong, herr, _hscoreSlice, hscoreBox, _hsourceSides, hfraction, _hgeometry⟩ :=
    hprepare (Fin nX) p hp d A hd hA (by simpa using hX) N g a hNprep
  have hNpass : ∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (S.length i : ℝ) :=
    (prepared_source_side_budgets hp (le_refl ((p + 2) ^ passagePower)) N S.length
      (fun i => (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase hp2)).trans (hN i))
      (fun i => (hlen i).2)).1
  have hout := hpass p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX S.length hNpass
    (S.integerPullback g) (fun x => hg (S.integerAffine x)) (S.pullback_apFree hq hgfree)
    D (d - D) (j + 1) hDpos (Nat.zero_lt_succ _) hjs _ F hrest
    (hcomplexity.le.trans hA) (hcount.le.trans hstage) (hgscore.trans hscoreBox)
    L hsize hheight hrank hcoord hgood ip c err hip herrdeg hid herr
  have hcomp := RelativePatchSliceConclusion.comp S hq
    (by positivity : 0 ≤ (p + 2) ^ costPower) hfraction hout
  have hsum : (p + 2) ^ costPower + (p + 2) ^ passagePower ≤ (p + 2) ^ power :=
    (prepared_source_cost_add_required hp (le_refl ((p + 2) ^ passagePower))).trans
      (pow_le_pow_right₀ hbase hp2)
  have hrankFinal : d₀ + s * (D + (d - D)) ≤ d₀ + s * d := by
    rw [Nat.add_sub_of_le hD]
  exact (hcomp.mono hrankFinal hsum).congr_input
    (fun x hx => relativeBoxInput_eq N f hx)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem RelativePatchFinPowerInductionRule.to_general
    {s n₀ stage power : ℕ} {discount : ℝ}
    (h : RelativePatchFinPowerInductionRule s n₀ stage discount power) :
    RelativePatchPowerInductionRule s n₀ stage discount power :=
  RelativePatchFinInductionRule.to_general h

theorem relativePatchFinPowerInductionRule_of_zero_and_positive
    {s n₀ stage basePower positivePower : ℕ} {discount : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hzero : RelativePatchFinPowerInductionRule s n₀ 0 discount basePower)
    (hpositive : RelativePatchFinPositivePowerRule s n₀ stage discount positivePower) :
    RelativePatchFinPowerInductionRule s n₀ (stage + 1) discount
      (max basePower positivePower) := by
  intro p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hN f hf hfree d A hA hstage hscore
  have hbase : 1 ≤ p + 2 := by linarith
  by_cases hd : d = 0
  · have hcost : (p + 2) ^ basePower ≤ (p + 2) ^ max basePower positivePower :=
      pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
    have hNzero : ∀ i, Real.exp ((p + 2) ^ basePower) ≤ (N i : ℝ) :=
      fun i => (Real.exp_le_exp.mpr hcost).trans (hN i)
    have hzeroWeights : relativePatchDistinctWeights A ≤ 0 :=
      ((relativePatchDistinctWeights_eq_zero_iff A).mpr hd).le
    have hout := hzero p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hNzero
      f hf hfree d A hA hzeroWeights hscore
    exact (hout.later_stage_target hdiscount
      (((Real.exp_pos (-p)).le.trans ha).trans haΛ)
      (Nat.zero_le (stage + 1))).mono le_rfl hcost
  · have hcost : (p + 2) ^ positivePower ≤ (p + 2) ^ max basePower positivePower :=
      pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
    have hNpositive : ∀ i, Real.exp ((p + 2) ^ positivePower) ≤ (N i : ℝ) :=
      fun i => (Real.exp_le_exp.mpr hcost).trans (hN i)
    exact (hpositive p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hNpositive
      f hf hfree d A (Nat.pos_of_ne_zero hd) hA hstage hscore).mono le_rfl hcost

theorem exists_relativePatchFinPowerInductionRule_of_positive_successors
    {s n₀ : ℕ} {discount : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchFinPowerInductionRule s n₀ 0 discount power)
    (hstep : ∀ stage : ℕ, stage < s → ∀ power : ℕ, 2 ≤ power →
      RelativePatchFinPowerInductionRule s n₀ stage discount power →
      ∃ nextPower : ℕ, 2 ≤ nextPower ∧
        RelativePatchFinPositivePowerRule s n₀ stage discount nextPower) :
    ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchFinPowerInductionRule s n₀ s discount power := by
  obtain ⟨basePower, hbasePower, hbase⟩ := hzero
  have hall : ∀ stage : ℕ, stage ≤ s → ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchFinPowerInductionRule s n₀ stage discount power := by
    intro stage
    induction stage with
    | zero =>
        intro _
        exact ⟨basePower, hbasePower, hbase⟩
    | succ stage ih =>
        intro hstage
        obtain ⟨power, hpower, hrule⟩ := ih (by omega)
        obtain ⟨nextPower, hnextPower, hpositive⟩ :=
          hstep stage (by omega) power hpower hrule
        exact ⟨max basePower nextPower, hbasePower.trans (Nat.le_max_left _ _),
          relativePatchFinPowerInductionRule_of_zero_and_positive hdiscount hbase hpositive⟩
  exact hall s le_rfl

theorem exists_relativePatchPowerInductionRule_of_fin_base_positive_successors
    {s n₀ : ℕ} {discount : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchFinPowerInductionRule s n₀ 0 discount power)
    (hstep : ∀ stage : ℕ, stage < s → ∀ power : ℕ, 2 ≤ power →
      RelativePatchPowerInductionRule s n₀ stage discount power →
      ∃ nextPower : ℕ, 2 ≤ nextPower ∧
        RelativePatchFinPositivePowerRule s n₀ stage discount nextPower) :
    ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchPowerInductionRule s n₀ s discount power := by
  obtain ⟨power, hpower, hrule⟩ :=
    exists_relativePatchFinPowerInductionRule_of_positive_successors hdiscount hzero
      (fun stage hstage power hpower hrule =>
        hstep stage hstage power hpower hrule.to_general)
  exact ⟨power, hpower, hrule.to_general⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Conclusions
namespace OAI

section

namespace Erdos3

theorem exists_manuscriptRelativePatchPower_s2_oai (s : ℕ) (hs : 1 ≤ s)
    (discount : ℝ) (hdiscount : 0 < discount) (hhalf : discount ≤ 1 / 2) :
    ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchPowerInductionRule s (VectorPolynomial.scalarNativeDimension s)
        s discount power := by
  have hone : discount ≤ 1 := by linarith only [hhalf]
  apply exists_relativePatchPowerInductionRule_of_fin_base_positive_successors
    ⟨hdiscount.le, hone⟩
  · exact VectorPolynomial.exists_relativePatch_scalarBase_fin_power_s2 s hdiscount hhalf
  · intro stage _hstage power hpower ih
    apply exists_relativePatchFinPositivePower_of_prepared
    exact exists_preparedRelativePatchPowerPassage_s2 s
      (VectorPolynomial.scalarNativeDimension s) stage power discount
      hs hpower hdiscount hone ih

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_manuscriptRelativePatchPower_s2_oai := @OAI.Erdos3.exists_manuscriptRelativePatchPower_s2_oai
