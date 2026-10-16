-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineSourceEarly_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-15T22:01:28.202991+00:00
-- url     : https://prove2.me/submissions/3c55c7f8-e9e7-4e96-b736-139f0989617e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedSourceEarlyPrefactor_le_exp

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy
namespace OAI

section

namespace Erdos3

theorem exp_neg_le_half_exp_neg {A B : ℝ} (hAB : B + 1 ≤ A) :
    Real.exp (-A) ≤ (1 / 2) * Real.exp (-B) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (-(B + 1)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 1 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-B) / 2 := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h2
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

theorem slicedSourceAccuracy_bounds {Q G E : ℝ} (hQ : 0 ≤ Q) (hG : 0 ≤ G) (hE : 0 ≤ E) :
    let εgrid := Real.exp (-(Q + E + 1))
    let εlong := Real.exp (-(G + E + 1))
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Q + E + 1) ∧
    0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ = Real.exp (G + E + 1) ∧
    ∀ C : ℝ, C ≤ Real.exp G → Real.exp Q * εgrid + εlong * C ≤ Real.exp (-E) := by
  intro εgrid εlong
  have hg : εgrid ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hQ, hE])
  have hl : εlong ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hG, hE])
  refine ⟨Real.exp_pos _, hg, ?_, Real.exp_pos _, hl, ?_, ?_⟩
  · simp only [εgrid, Real.exp_neg, inv_inv]
  · simp only [εlong, Real.exp_neg, inv_inv]
  · intro C hC
    have hhalf := exp_neg_le_half_exp_neg (A := E + 1) (B := E) le_rfl
    have hgrid : Real.exp Q * εgrid = Real.exp (-(E + 1)) := by
      dsimp [εgrid]
      rw [← Real.exp_add]
      congr 1
      ring
    have hlong : εlong * Real.exp G = Real.exp (-(E + 1)) := by
      dsimp [εlong]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Real.exp Q * εgrid + εlong * Real.exp G :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hC (Real.exp_nonneg _))
      _ = 2 * Real.exp (-(E + 1)) := by rw [hgrid, hlong]; ring
      _ ≤ Real.exp (-E) := by linarith only [hhalf]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSourceAccuracy
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

theorem affineSourceAccuracy_budget
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Dout Dgrid Prho Pbox Op E F C : ℝ}
    (hDout : 0 ≤ Dout) (hDgrid : 0 ≤ Dgrid) (hPrho : 0 ≤ Prho)
    (hPbox : 0 ≤ Pbox) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hout : (Fintype.card κ : ℝ) ≤ Dout) (hgrid : (Fintype.card ι : ℝ) ≤ Dgrid)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hC0 : 0 ≤ C) (hC : C ≤ Real.exp F) :
    let G := Dgrid * max Op 0
    let εgrid := Real.exp (-(Dout * Prho + (E + F) + 1))
    let εlong := Real.exp (-(G + (E + F) + 1))
    let Plong := Pbox + Prho + G + (E + F) + 2
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Dout * Prho + (E + F) + 1) ∧
      0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp Plong ∧
      0 ≤ Plong ∧ Pbox ≤ Plong ∧ (ρ : ℝ)⁻¹ ≤ Real.exp Plong ∧
      C * ((ρ⁻¹ ^ Fintype.card κ : ℝ≥0) * εgrid +
        εlong * ∏ _i : ι, Real.exp Op) ≤ Real.exp (-E) := by
  intro G εgrid εlong Plong
  have hG : 0 ≤ G := mul_nonneg hDgrid (le_max_right _ _)
  obtain ⟨hg0, hg1, hgi, hl0, hl1, hli, herr⟩ :=
    slicedSourceAccuracy_bounds (mul_nonneg hDout hPrho) hG (add_nonneg hE hF)
  have hPlong : G + (E + F) + 1 ≤ Plong := by dsimp [Plong]; linarith
  have hb : Pbox ≤ Plong := by dsimp [Plong]; linarith
  have hr : Prho ≤ Plong := by dsimp [Plong]; linarith
  have hcap : (ρ⁻¹ ^ Fintype.card κ : ℝ≥0) ≤ Real.exp (Dout * Prho) := by
    rw [NNReal.coe_pow, NNReal.coe_inv]
    calc
      _ ≤ (Real.exp Prho) ^ Fintype.card κ := pow_le_pow_left₀ (inv_nonneg.mpr ρ.coe_nonneg) hρ _
      _ = Real.exp (Fintype.card κ * Prho) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hout hPrho)
  have hprod : (∏ _i : ι, Real.exp Op) ≤ Real.exp G := by
    simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hgrid (le_max_right _ _))
  refine ⟨hg0, hg1, hgi, hl0, hl1, hli.trans_le (Real.exp_le_exp.mpr hPlong),
    hPbox.trans hb, hb, hρ.trans (Real.exp_le_exp.mpr hr), ?_⟩
  calc
    _ ≤ C * (Real.exp (Dout * Prho) * εgrid + εlong * ∏ _i : ι, Real.exp Op) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact add_le_add (mul_le_mul_of_nonneg_right hcap hg0.le) le_rfl
    _ ≤ C * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_left (herr _ hprod) hC0
    _ ≤ Real.exp F * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineSourceAccuracy
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_buffer_le_exp (rowSets : Fin m → Finset (Finset α)) :
    2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤
      Real.exp (((m : ℝ) + 2) * Fintype.card α + m + 4) := by
  let A : ℝ := ((m : ℝ) + 2) * Fintype.card α + 3
  have hT : 0 ≤ partitionedIdealRadius α m + 1 := by
    have := partitionedIdealRadius_nonneg α m
    positivity
  have hr : (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ 1 + m * idealSiteBoxRadius α m := by
    change 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1) ≤ _
    apply add_le_add_right
    calc
      _ ≤ ∑ _j : Fin m, idealSiteBoxRadius α m := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ hT
        exact_mod_cast (Finset.card_le_univ (rowSets j)).trans_eq (Fintype.card_finset (α := α))
      _ = _ := by simp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hone : 1 ≤ Real.exp A := Real.one_le_exp_iff.mpr hA
  calc
    _ ≤ 2 + m * (2 * idealSiteBoxRadius α m) := by nlinarith only [hr]
    _ ≤ 2 + m * Real.exp A := by
      gcongr
      exact idealSiteBoxRadius_buffer_le_exp α m
    _ ≤ ((m : ℝ) + 2) * Real.exp A := by nlinarith only [hone]
    _ ≤ Real.exp ((m : ℝ) + 1) * Real.exp A := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      simpa only [add_assoc, one_add_one_eq_two] using Real.add_one_le_exp ((m : ℝ) + 1)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [A]; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (E : Fin m → Type*) [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
variable (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
variable (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "outputs" => (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a)))

include hR hPnum hI hn hcoeff hRi hV in
omit [DecidableEq α] in
theorem allocatedAffineSourceEarly_error_budget
    {Mk period : ℕ} {Pk Pper Prho target Op : ℝ}
    (hPk : 0 ≤ Pk) (hPper : 0 ≤ Pper) (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target)
    (hMk : (Mk : ℝ) ≤ Real.exp Pk) (hperiod : (period : ℝ) ≤ Real.exp Pper)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho) :
    let F := (m * (2 : ℝ) ^ Fintype.card α) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * Pper)
    let Dout := (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ)
    let Dgrid := (Fintype.card (LayerSamplerAxis I n) : ℝ)
    let Pbox := ((m : ℝ) + 2) * Fintype.card α + m + 4
    let εgrid := Real.exp (-(Dout * Prho + (target + F) + 1))
    let Gcost := Dgrid * max Op 0
    let εlong := Real.exp (-(Gcost + (target + F) + 1))
    let Plong := Pbox + Prho + Gcost + (target + F) + 2
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Dout * Prho + (target + F) + 1) ∧
      0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp Plong ∧ 0 ≤ Plong ∧
      2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Plong ∧
      (ρ : ℝ)⁻¹ ≤ Real.exp Plong ∧
      ‖inverseNormalizer‖ *
        ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
          coefficientDeckPeriodCap rowTypes E period) *
        ((ρ⁻¹ ^ Fintype.card outputs : ℝ≥0) * εgrid +
          εlong * ∏ _a : {a // grid a}, Real.exp Op) ≤ Real.exp (-target) := by
  intro F Dout Dgrid Pbox εgrid Gcost εlong Plong
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hbox : 0 ≤ Pbox := by dsimp only [Pbox]; positivity
  have hout : (Fintype.card outputs : ℝ) ≤ Dout := by
    apply Nat.cast_le.mpr
    apply Fintype.card_le_of_injective (fun a : outputs =>
      (⟨a.1.val, a.2⟩ : Σ a : LayerSamplerAxis I n, rowTypes a.1))
    rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ heq
    cases heq
    rfl
  have hg : (Fintype.card {a // grid a} : ℝ) ≤ Dgrid := by
    change (Fintype.card {a // grid a} : ℝ) ≤ (Fintype.card (LayerSamplerAxis I n) : ℝ)
    exact_mod_cast Fintype.card_subtype_le grid
  have hc0 : 0 ≤ ‖inverseNormalizer‖ *
      ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
        coefficientDeckPeriodCap rowTypes E period) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (coefficientDeckPeriodCap_nonneg rowTypes E period))
  obtain ⟨hg0, hg1, hgi, hl0, hl1, hli, hp, hbp, hrp, herr⟩ :=
    affineSourceAccuracy_budget (ι := {a // grid a}) (κ := outputs)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hPrho hbox htarget hF hout hg ρ hρ hc0
      (allocatedSlicedSourceEarlyPrefactor_le_exp B U b S rowSets E hR hPnum hI hn hcoeff hRi hV hMk hperiod)
  exact ⟨hg0, hg1, hgi, hl0, hl1, hli, hp,
    (allocatedRowSlicedSiteRadius_buffer_le_exp rowSets).trans (Real.exp_le_exp.mpr hbp), hrp, herr⟩

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineSourceEarly_error_budget.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedAffineSourceEarly_error_budget.{u_1, u_2, u_3, u_4, u_5, u_6}
