-- Prove2me | solution 1 for OAI.QuantumTrace.gibbs_fock_spectral_regular
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:22:10.534422+00:00
-- url     : https://prove2.me/submissions/062cc044-ed7f-4715-80c1-4ffcd5de33bd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L1336-L1367
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.gibbs_fock_spectral_regular. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Theorems.Thm_OAI_QuantumTrace_exists_eigenbasis
import Theorems.Thm_OAI_QuantumTrace_gibbs_eigenvector_regular

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

omit [CompleteSpace E] [CompleteSpace F] in
theorem basisApprox_isCompactOperator (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (s : Finset ι) : IsCompactOperator (basisApprox b T s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [basisApprox] using (isCompactOperator_zero : IsCompactOperator (0 : E →L[ℂ] F))
  | @insert j s hj hs =>
    rw [basisApprox, Finset.sum_insert hj]
    apply IsCompactOperator.add _ hs
    rw [rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_rng (toSpanSingleton ℂ (T (b j)))).comp_clm (innerSL ℂ (b j))

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
theorem diagonalMap_norm_le (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    {C : ℝ} (hC : 0 ≤ C) (hab : ∀ i, ‖a i‖ ≤ C) : ‖diagonalMap a ha‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have h := lp.norm_mono (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (x := diagonalMap a ha x) (y := (C : ℂ) • x) (fun i => by
      simp only [diagonalMap_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hab i) (norm_nonneg _))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using h

theorem diagonalMap_injective (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (hn : ∀ i, a i ≠ 0) : Function.Injective (diagonalMap a ha) := by
  intro x y h
  ext i
  exact mul_left_cancel₀ (hn i) (congrArg (fun z : SequenceHilbert ι => z i) h)

end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

theorem diagonalMap_cut (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (s : Finset ι) :
    ∃ hb : ∃ C : ℝ, ∀ i, ‖(if i ∈ s then a i else 0 : ℂ)‖ ≤ C,
      diagonalMap (fun i => if i ∈ s then a i else 0) hb =
        basisApprox (sequenceBasis ι) (diagonalMap a ha) s := by
  classical
  have hb : ∃ C : ℝ, ∀ i, ‖(if i ∈ s then a i else 0 : ℂ)‖ ≤ C := by
    refine ⟨|ha.choose|, fun i => ?_⟩
    split_ifs
    · exact (ha.choose_spec i).trans (le_abs_self _)
    · simp only [norm_zero]; exact abs_nonneg _
  refine ⟨hb, ?_⟩
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro z
  have hz : lp.single (E := fun _ : ι => ℂ) 2 i z = z • sequenceBasis ι i := by
    simp only [sequenceBasis_apply, ← lp.single_smul, smul_eq_mul, mul_one]
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply, hz,
    map_smul, basisApprox_apply_basis]
  rw [sequenceBasis_apply, diagonalMap_single, diagonalMap_single]
  by_cases hi : i ∈ s
  · simp [hi]
  · simp [hi]

theorem diagonalMap_compact (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (hvan : ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ i, i ∉ s → ‖a i‖ ≤ ε) :
    IsCompactOperator (diagonalMap a ha) := by
  classical
  have hlim : Tendsto (fun s : Finset ι => basisApprox (sequenceBasis ι) (diagonalMap a ha) s)
      atTop (𝓝 (diagonalMap a ha)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨s, hs⟩ := hvan (ε/2) (by positivity)
    filter_upwards [eventually_ge_atTop s] with t ht
    obtain ⟨hb, he⟩ := diagonalMap_cut a ha t
    have hd : ∃ C : ℝ, ∀ i, ‖a i - (if i ∈ t then a i else 0 : ℂ)‖ ≤ C := by
      refine ⟨ε/2, fun i => ?_⟩
      by_cases hi : i ∈ t
      · simp only [ite_eq_left hi, sub_self, norm_zero]
        positivity
      · simpa [hi] using hs i (fun h => hi (ht h))
    have heq : diagonalMap a ha - diagonalMap (fun i => if i ∈ t then a i else 0) hb =
        diagonalMap (fun i => a i-(if i ∈ t then a i else 0)) hd := by
      ext x i
      simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, diagonalMap_apply]
      ring
    rw [dist_eq_norm, norm_sub_rev, ← he, heq]
    exact (diagonalMap_norm_le _ hd (C := ε/2) (by positivity) (by
      intro i
      by_cases hi : i ∈ t
      · simp only [ite_eq_left hi, sub_self, norm_zero]
        positivity
      · simpa [hi] using hs i (fun h => hi (ht h)))).trans_lt (by linarith)
  exact isCompactOperator_of_tendsto hlim
    (Eventually.of_forall (fun s => basisApprox_isCompactOperator _ _ s))

end

section
open Filter Topology
variable {ι : Type*}

theorem inversePower_injective (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    Function.Injective (inversePower s hs p) := by
  apply diagonalMap_injective
  intro i
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (by linarith [hs i])))

theorem gibbsInverse_positive (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    {k : ℝ} (hk : 0 < k) {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι}
    (hB : B.IsPositive) : (gibbsInverse s hs k B).IsPositive := by
  have hA := gibbsFactor_strictPositive s hs hk hB
  have hi : (Ring.inverse (gibbsFactor s hs k B)).IsPositive := by
    let A := gibbsFactor s hs k B
    have hp : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hA.nonneg
    apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
    intro x
    let y := Ring.inverse A x
    have hAy : A y = x := by
      exact congrArg (fun X : SequenceHilbert ι →L[ℂ] SequenceHilbert ι => X x)
        (Ring.mul_inverse_cancel A hA.isUnit)
    change ((inner ℂ y x).re : ℂ) = inner ℂ y x ∧ 0 ≤ (inner ℂ y x).re
    rw [← hAy]
    have hh := (ContinuousLinearMap.isPositive_iff_complex _).mp hp y
    have es : inner ℂ (A y) y = inner ℂ y (A y) := hp.isSymmetric y y
    change ((inner ℂ (A y) y).re : ℂ) = inner ℂ (A y) y ∧ 0 ≤ (inner ℂ (A y) y).re at hh
    rwa [es] at hh
  have h := hi.adjoint_conj (inversePower s hs 4)
  rw [inversePower_adjoint] at h
  exact h

theorem gibbsInverse_injective (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    {k : ℝ} (hk : 0 < k) {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι}
    (hB : B.IsPositive) : Function.Injective (gibbsInverse s hs k B) := by
  have hA := (gibbsFactor_strictPositive s hs hk hB).isUnit
  have hinv : Function.Injective (⇑(Ring.inverse (gibbsFactor s hs k B))) := by
    apply Function.LeftInverse.injective (g := gibbsFactor s hs k B)
    intro x
    exact congrArg (fun T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι => T x)
      (Ring.mul_inverse_cancel _ hA)
  exact (inversePower_injective s hs 4).comp (hinv.comp (inversePower_injective s hs 4))

theorem gibbsInverse_compact (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (k : ℝ)
    (B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι)
    (hcompact : IsCompactOperator (inversePower s hs 4)) :
    IsCompactOperator (gibbsInverse s hs k B) := by
  exact (hcompact.comp_clm (Ring.inverse (gibbsFactor s hs k B))).comp_clm (inversePower s hs 4)

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem exists_strictly_positive_eigenbasis {T : E →L[ℂ] E} (hc : IsCompactOperator T)
    (hp : T.IsPositive) (hi : Function.Injective T) :
    ∃ (J : Type v) (b : HilbertBasis J ℂ E) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ ∀ j, T (b j) = (p j : ℂ) • b j := by
  obtain ⟨J, b, e, he⟩ := exists_eigenbasis hc hp.isSymmetric
  have hie (j : J) : inner ℂ (b j) (T (b j)) = e j := by
    rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp
  have hr (j : J) : (e j).re ≥ 0 := by
    rw [← hie]
    exact hp.re_inner_nonneg_right _
  have hec (j : J) : ((e j).re : ℂ) = e j := by
    have h := hp.isSymmetric.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (he j), b.orthonormal.ne_zero j⟩)
    apply Complex.ext
    · rfl
    · have := congrArg Complex.im h
      simp only [Complex.conj_im] at this
      simpa using (show (0 : ℝ) = (e j).im by linarith)
  refine ⟨J, b, fun j => (e j).re, fun j => lt_of_le_of_ne (hr j) ?_, ?_⟩
  · intro hz
    have hz' : e j = 0 := by
      change 0 = (e j).re at hz
      rw [← hec, ← hz]; simp
    have ht : T (b j) = T 0 := by simp [he, hz']
    exact b.orthonormal.ne_zero j (hi ht)
  · intro j
    rw [hec, he]

end

section
open Filter Topology
variable {ι : Type*}

theorem real_exp_support (a b : ℝ) : Real.exp a*(1+b-a) ≤ Real.exp b := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b-a)) (Real.exp_nonneg a)
  rw [← Real.exp_add] at h
  convert h using 1 <;> congr 1 <;> ring

theorem heat_weight_le_diagonal (s : ι → ℝ) (_hs : ∀ i, 1 ≤ s i)
    {k u : ℝ} (hk : 0 < k) {ψ y : SequenceHilbert ι}
    (hψ : ‖ψ‖ = 1) (hy : ∀ i, y i = (s i^4 : ℝ)*ψ i)
    (he : k*‖y‖^2 ≤ u) :
    Real.exp (-u) ≤ ∑' i, Real.exp (-k*s i^8)*‖ψ i‖^2 := by
  have hw : HasSum (fun i => ‖ψ i‖^2) 1 := by
    simpa only [hψ, one_pow] using sequence_hasSum_norm_sq ψ
  have hwy : HasSum (fun i => s i^8*‖ψ i‖^2) (‖y‖^2) := by
    convert sequence_hasSum_norm_sq y using 1
    funext i
    rw [hy i, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  have hh : Summable (fun i => Real.exp (-k*s i^8)*‖ψ i‖^2) := by
    apply Summable.of_nonneg_of_le (fun i => by positivity) _ hw.summable
    intro i
    have hex : Real.exp (-k*s i^8) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (by positivity))
    nlinarith [sq_nonneg ‖ψ i‖, Real.exp_nonneg (-k*s i^8)]
  have hl : HasSum (fun i => Real.exp (-u)*((1+u)*‖ψ i‖^2-k*(s i^8*‖ψ i‖^2)))
      (Real.exp (-u)*((1+u)-k*‖y‖^2)) := by
    simpa only [mul_one] using ((hw.mul_left (1+u)).sub (hwy.mul_left k)).mul_left (Real.exp (-u))
  calc
    Real.exp (-u) ≤ Real.exp (-u)*((1+u)-k*‖y‖^2) := by
      nlinarith [Real.exp_pos (-u)]
    _ = ∑' i, Real.exp (-u)*((1+u)*‖ψ i‖^2-k*(s i^8*‖ψ i‖^2)) := hl.tsum_eq.symm
    _ ≤ _ := by
      apply hl.summable.tsum_le_tsum _ hh
      intro i
      have h := mul_le_mul_of_nonneg_right (real_exp_support (-u) (-k*s i^8)) (sq_nonneg ‖ψ i‖)
      convert h using 1; ring

theorem basis_coordinate_hasSum {κ : Type*} (b : HilbertBasis κ ℂ (SequenceHilbert ι)) (i : ι) :
    HasSum (fun j => ‖b j i‖^2) 1 := by
  have h := basis_hasSum_norm_sq b (sequenceBasis ι i)
  convert h using 1
  · funext j
    rw [← sequenceBasis_inner, norm_inner_symm]
  · simp only [(sequenceBasis ι).orthonormal.norm_eq_one, one_pow]

theorem heat_trace_bound {κ : Type*} (b : HilbertBasis κ ℂ (SequenceHilbert ι))
    (a : κ → ℝ) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (hds : Summable d)
    (ha : ∀ j, 0 ≤ a j)
    (hw : ∀ j, a j ≤ ∑' i, d i*‖b j i‖^2) :
    Summable a ∧ ∑' j, a j ≤ ∑' i, d i := by
  have hrow (j : κ) : Summable (fun i => d i*‖b j i‖^2) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (hd i) (sq_nonneg _)) _ hds
    intro i
    have hn : ‖b j i‖ ≤ 1 := by
      simpa only [b.orthonormal.norm_eq_one] using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (b j) i
    exact mul_le_of_le_one_right (hd i) (by nlinarith [norm_nonneg (b j i)])
  have hfin (F : Finset κ) : ∑ j ∈ F, a j ≤ ∑' i, d i := by
    calc
      ∑ j ∈ F, a j ≤ ∑ j ∈ F, ∑' i, d i*‖b j i‖^2 := Finset.sum_le_sum (fun j _ => hw j)
      _ = ∑' i, ∑ j ∈ F, d i*‖b j i‖^2 := (Summable.tsum_finsetSum (fun j _ => hrow j)).symm
      _ ≤ ∑' i, d i := by
        apply Summable.tsum_le_tsum _ _ hds
        · intro i
          rw [← Finset.mul_sum]
          apply mul_le_of_le_one_right (hd i)
          exact (basis_coordinate_hasSum b i).summable.sum_le_tsum F (fun _ _ => sq_nonneg _) |>.trans_eq (basis_coordinate_hasSum b i).tsum_eq
        · exact summable_sum (fun j _ => hrow j)
  have hs := summable_of_sum_le ha hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end

section
open Filter Topology

theorem rootNumberWeight_pow_eight {n : ℕ} (i : Fin n → ℕ) :
    rootNumberWeight i^8 = numberWeight i^4 := by
  rw [show (8 : ℕ) = 2*4 from rfl, pow_mul, rootNumberWeight, Real.sq_sqrt (by linarith [numberWeight_one_le i])]

theorem summable_exp_number (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun i : Fin n → ℕ => Real.exp (-t*(∑ j, (i j : ℝ)))) := by
  let w : ℕ → ℝ := fun m => Real.exp (-t*(m : ℝ))
  have hw : Summable w := by
    have hh : ‖Real.exp (-t)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      linarith
    apply (summable_geometric_of_norm_lt_one hh).congr
    intro m
    simpa only [w, mul_comm] using (Real.exp_nat_mul (-t) m).symm
  have hn : (∑' m, ENNReal.ofReal (w m)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => Real.exp_nonneg _) hw]
    exact ENNReal.ofReal_ne_top
  have he (i : Fin n → ℕ) :
      ENNReal.ofReal (Real.exp (-t*(∑ j, (i j : ℝ)))) = ∏ j, ENNReal.ofReal (w (i j)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _)]
    congr 1
    rw [← Real.exp_sum]
    congr 1
    exact Finset.mul_sum _ _ _
  have hf : (∑' i : Fin n → ℕ, ENNReal.ofReal (Real.exp (-t*(∑ j, (i j : ℝ))))) ≠ ⊤ := by
    simp_rw [he]
    rw [tsum_finite_product n (fun m => ENNReal.ofReal (w m))]
    exact ENNReal.pow_ne_top hn
  have hh := (ENNReal.hasSum_toReal hf).summable
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hh

theorem summable_exp_number_aux (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun i : Fin n → ℕ => Real.exp (-t*rootNumberWeight i^8)) := by
  apply Summable.of_nonneg_of_le (fun i => Real.exp_nonneg _) _ (summable_exp_number n ht)
  intro i
  apply Real.exp_le_exp.mpr
  rw [rootNumberWeight_pow_eight]
  have hw := numberWeight_one_le i
  have hh : numberWeight i ≤ numberWeight i^4 := le_self_pow₀ hw (by norm_num)
  have hsum : ∑ j, (i j : ℝ) ≤ numberWeight i^4 := by
    have hn : ∑ j, (i j : ℝ) = numberWeight i-1 := by simp [numberWeight]
    rw [hn]; linarith
  nlinarith

theorem inverseRootNumber_compact (n : ℕ) :
    IsCompactOperator (inversePower (rootNumberWeight (n := n)) rootNumberWeight_one_le 4) := by
  classical
  apply diagonalMap_compact
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (ε⁻¹)
  let F : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ => Finset.range (K+1))
  refine ⟨F, fun i hi => ?_⟩
  have hsum : (K+1 : ℝ) ≤ ∑ j, (i j : ℝ) := by
    simp only [F, Fintype.mem_piFinset, Finset.mem_range, not_forall] at hi
    obtain ⟨j, hj⟩ := hi
    have hh : K+1 ≤ i j := Nat.le_of_not_gt hj
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (i j)) (Finset.mem_univ j)
    exact_mod_cast hh.trans hs
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity [rootNumberWeight_one_le i]),
    rootNumberWeight_pow_four]
  have hw := numberWeight_one_le i
  have hn : (K : ℝ) ≤ numberWeight i := by unfold numberWeight; linarith
  have hh : ε⁻¹ ≤ numberWeight i^2 := by
    nlinarith [sq_nonneg (numberWeight i-1)]
  exact (inv_le_comm₀ (by nlinarith : 0 < numberWeight i^2) hε).mpr hh

theorem gibbs_fock_spectral_regular (n : ℕ) {k : ℝ} (hk : 0 < k)
    {B : SequenceHilbert (Fin n → ℕ) →L[ℂ] SequenceHilbert (Fin n → ℕ)} (hB : B.IsPositive) :
    ∃ (J : Type) (b : HilbertBasis J ℂ (SequenceHilbert (Fin n → ℕ))) (u : J → ℝ),
      (∀ j, 0 < u j) ∧
      (∀ j, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j) ∧
      (∀ j, ∃ y z : SequenceHilbert (Fin n → ℕ),
        (∀ i, y i = (rootNumberWeight i^4 : ℝ)*b j i) ∧
        (∀ i, z i = (rootNumberWeight i^7 : ℝ)*b j i) ∧
        ‖y‖^2 ≤ u j/k ∧ ‖z‖ ≤ k⁻¹*(u j+‖B‖*Real.sqrt (u j/k))) ∧
      (∀ t : ℝ, 0 < t → Summable (fun j => Real.exp (-t*u j))) := by
  obtain ⟨J, b, e, hep, he⟩ := exists_strictly_positive_eigenbasis
    (gibbsInverse_compact rootNumberWeight rootNumberWeight_one_le k B (inverseRootNumber_compact n))
    (gibbsInverse_positive rootNumberWeight rootNumberWeight_one_le hk hB)
    (gibbsInverse_injective rootNumberWeight rootNumberWeight_one_le hk hB)
  let u : J → ℝ := fun j => (e j)⁻¹
  have hup (j : J) : 0 < u j := inv_pos.mpr (hep j)
  have hue (j : J) : gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) =
      (((u j)⁻¹ : ℝ) : ℂ) • b j := by simpa only [u, inv_inv] using he j
  have hreg (j : J) := gibbs_eigenvector_regular rootNumberWeight rootNumberWeight_one_le hk
    (hup j) hB (b.orthonormal.norm_eq_one j) (hue j)
  refine ⟨J, b, u, hup, hue, hreg, ?_⟩
  intro t ht
  apply (heat_trace_bound b (fun j => Real.exp (-t*u j))
      (fun i => Real.exp (-(t*k)*rootNumberWeight i^8)) (fun _ => Real.exp_nonneg _)
      (summable_exp_number_aux n (mul_pos ht hk)) (fun _ => Real.exp_nonneg _) ?_).1
  intro j
  obtain ⟨y, z, hy, _, hnorm, _⟩ := hreg j
  have he' : (t*k)*‖y‖^2 ≤ t*u j := by
    have hh := (le_div_iff₀ hk).mp hnorm
    nlinarith
  simpa only [neg_mul] using heat_weight_le_diagonal rootNumberWeight rootNumberWeight_one_le (mul_pos ht hk)
    (b.orthonormal.norm_eq_one j) hy he'

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

end QuantumTrace

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology


theorem solution : type_of% @_root_.OAI.QuantumTrace.gibbs_fock_spectral_regular := @_root_.OAI.QuantumTrace.gibbs_fock_spectral_regular
