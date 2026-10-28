-- Prove2me | solution 1 for OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:50:48.091982+00:00
-- url     : https://prove2.me/submissions/f5b1be15-8dda-4bfc-9155-1905efd3aa1c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf005
import Definitions.Def_OAIQ15Sf009
import Definitions.Def_OAIQ15Sf011
import Theorems.Thm_OAI_KaplanskyConsequences_Regular_algebra_F2_simple
import Theorems.Thm_OAI_KaplanskyConsequences_Regular_tensor_two_isometries_of_small_tuple
import Theorems.Thm_OAI_KaplanskyConsequences_simple_stablyFinite_traceless_exists

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_Extraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace KaplanskyConsequences
open scoped ComplexOrder BigOperators
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

lemma positiveCone_convex : Convex ℝ (positiveCone A) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a • (x : A) + b • (y : A)
  exact add_nonneg (smul_nonneg ha hx) (smul_nonneg hb hy)

lemma one_mem_interior_positiveCone : (1 : selfAdjoint A) ∈ interior (positiveCone A) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨1, zero_lt_one, ?_⟩
  intro x hx
  have hn : ‖(x : A) - 1‖ ≤ 1 := by
    simpa only [dist_eq_norm, ← AddSubgroup.norm_coe, AddSubgroup.coe_sub, selfAdjoint.val_one] using (Metric.mem_ball.mp hx).le
  have hl := (show IsSelfAdjoint ((x : A) - 1) from x.property.sub (IsSelfAdjoint.one A)).neg_algebraMap_norm_le_self
  have hm : algebraMap ℝ A ‖(x : A) - 1‖ ≤ 1 := by
    rw [Algebra.algebraMap_eq_smul_one]
    simpa using smul_le_smul_of_nonneg_right hn (show (0 : A) ≤ 1 from zero_le_one)
  change 0 ≤ (x : A)
  have := le_trans (neg_le_neg hm) hl
  convert add_le_add_left this (1 : A) using 1 <;> abel

lemma trace_identity_of_square_swap (φ : A →ₗ[ℂ] ℂ)
    (hφ : ∀ x, φ (star x * x) = φ (x * star x)) (a b : A) :
    φ (a * b) = φ (b * a) := by
  have h₁ := hφ (a + star b)
  have h₂ := hφ (a + Complex.I • star b)
  simp only [star_add, star_star, add_mul, mul_add, map_add] at h₁
  simp only [star_add, star_smul, star_star, Complex.star_def, map_add,
    Complex.conj_I, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_add, map_smul, smul_eq_mul] at h₂
  have ha := hφ a
  have hb := hφ b
  linear_combination (norm := skip) -(h₁ + Complex.I * h₂ - (1 + Complex.I) * ha + (1 + Complex.I) * hb) / 2
  ring_nf
  simp only [Complex.I_sq, show Complex.I ^ 3 = -Complex.I by norm_num [pow_succ]]
  ring

lemma complexify_apply_selfAdjoint (g : (selfAdjoint A) →ₗ[ℝ] ℝ)
    (x : A) (hx : IsSelfAdjoint x) :
    complexify g x = (g ⟨x, hx⟩ : ℂ) := by
  have hI : selfAdjointPart ℝ (Complex.I • x) = 0 := by
    apply Subtype.ext
    simp [selfAdjointPart_apply_coe, star_smul, hx.star_eq]
  simp [complexify, Module.Dual.extendRCLike_apply, hx.selfAdjointPart_apply ℝ, hI]

lemma tracialState_of_selfAdjoint_functional
    (g : (selfAdjoint A) →ₗ[ℝ] ℝ) (hg1 : g 1 = 1)
    (hgpos : ∀ x : selfAdjoint A, 0 ≤ (x : A) → 0 ≤ g x)
    (hgspan : ∀ x ∈ commutatorSpan A, g x = 0) : Nonempty (TracialState A) := by
  let φ := complexify g
  have hφpos : ∀ x : A, 0 ≤ x → 0 ≤ φ x := by
    intro x hx
    rw [show φ x = (g ⟨x, IsSelfAdjoint.of_nonneg hx⟩ : ℂ) from
      complexify_apply_selfAdjoint g x (IsSelfAdjoint.of_nonneg hx)]
    exact_mod_cast hgpos ⟨x, IsSelfAdjoint.of_nonneg hx⟩ hx
  have hφswap : ∀ x : A, φ (star x * x) = φ (x * star x) := by
    intro x
    have hz := hgspan (selfCommutator x) (Submodule.subset_span ⟨x, rfl⟩)
    have heq := complexify_apply_selfAdjoint g (selfCommutator x) (selfCommutator x).property
    change φ (star x * x - x * star x) = (g (selfCommutator x) : ℂ) at heq
    rw [hz, Complex.ofReal_zero, map_sub, sub_eq_zero] at heq
    exact heq
  refine ⟨⟨PositiveLinearMap.mk₀ φ hφpos, ?_, ?_⟩⟩
  · change φ 1 = 1
    rw [show φ 1 = (g 1 : ℂ) from complexify_apply_selfAdjoint g 1 (IsSelfAdjoint.one A),
      hg1, Complex.ofReal_one]
  · exact trace_identity_of_square_swap φ hφswap

lemma nonpositive_functional_one_ne_zero
    (f : selfAdjoint A →L[ℝ] ℝ) (hfne : f ≠ 0)
    (hfpos : ∀ x : selfAdjoint A, 0 ≤ (x : A) → f x ≤ 0) : f 1 ≠ 0 := by
  intro hf1
  have hbound (x : selfAdjoint A) : 0 ≤ f x := by
    have hp : 0 ≤ ((‖(x : A)‖ • (1 : selfAdjoint A) - x : selfAdjoint A) : A) := by
      change 0 ≤ ‖(x : A)‖ • (1 : A) - (x : A)
      rw [← Algebra.algebraMap_eq_smul_one]
      exact sub_nonneg.mpr x.property.le_algebraMap_norm_self
    have hb := hfpos (‖(x : A)‖ • 1 - x) hp
    rw [map_sub, map_smul, hf1, smul_eq_mul, mul_zero, zero_sub] at hb
    exact neg_nonpos.mp hb
  apply hfne
  apply ContinuousLinearMap.ext
  intro x
  have hp := hbound x
  have hn := hbound (-x)
  rw [map_neg] at hn
  exact le_antisymm (neg_nonneg.mp hn) hp

lemma tracialState_of_disjoint
    (hdisj : Disjoint (interior (positiveCone A)) (commutatorSpan A : Set (selfAdjoint A))) :
    Nonempty (TracialState A) := by
  obtain ⟨f, u, hfne, hpos, hspan⟩ := geometric_hahn_banach_of_nonempty_interior
    (E := selfAdjoint A) (s := positiveCone A)
    (t := (commutatorSpan A : Set (selfAdjoint A)))
    (positiveCone_convex (A := A)) (commutatorSpan A).convex hdisj
    ⟨1, one_mem_interior_positiveCone (A := A)⟩ ⟨0, (commutatorSpan A).zero_mem⟩
  have hu₁ : 0 ≤ u := by
    simpa only [map_zero] using hpos 0 (show 0 ∈ positiveCone A from (by change (0 : A) ≤ 0; exact le_rfl))
  have hu₂ : u ≤ 0 := by simpa only [map_zero] using hspan 0 (commutatorSpan A).zero_mem
  have hu : u = 0 := le_antisymm hu₂ hu₁
  have hfpos : ∀ x : selfAdjoint A, 0 ≤ (x : A) → f x ≤ 0 := by
    intro x hx
    simpa only [hu] using hpos x hx
  have hfspan : ∀ x ∈ commutatorSpan A, f x = 0 := by
    intro x hx
    have hp := hspan x hx
    have hn := hspan (-x) ((commutatorSpan A).neg_mem hx)
    rw [hu] at hp
    rw [map_neg, hu] at hn
    exact le_antisymm (neg_nonneg.mp hn) hp
  have hf1le : f 1 ≤ 0 := hfpos 1 zero_le_one
  have hf1ne : f 1 ≠ 0 := nonpositive_functional_one_ne_zero f hfne hfpos
  have hf1 : f 1 < 0 := lt_of_le_of_ne hf1le hf1ne
  let g : (selfAdjoint A) →ₗ[ℝ] ℝ := (f 1)⁻¹ • f.toLinearMap
  apply tracialState_of_selfAdjoint_functional g
  · change (f 1)⁻¹ * f 1 = 1
    exact inv_mul_cancel₀ hf1ne
  · intro x hx
    change 0 ≤ (f 1)⁻¹ * f x
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr hf1.le) (hfpos x hx)
  · intro x hx
    change (f 1)⁻¹ * f x = 0
    rw [hfspan x hx, mul_zero]

lemma positive_commutator_of_no_trace (h : IsEmpty (TracialState A)) :
    ∃ x ∈ commutatorSpan A, x ∈ interior (positiveCone A) := by
  by_contra hn
  have hdisj : Disjoint (interior (positiveCone A)) (commutatorSpan A : Set (selfAdjoint A)) := by
    rw [Set.disjoint_left]
    intro x hx hs
    exact hn ⟨x, hs, hx⟩
  obtain ⟨τ⟩ := tracialState_of_disjoint hdisj
  exact h.false τ

lemma selfCommutator_star (x : A) : selfCommutator (star x) = -selfCommutator x := by
  apply Subtype.ext
  simp [selfCommutator, neg_sub]

lemma selfCommutator_smul (r : ℝ) (x : A) :
    selfCommutator (r • x) = (r * r) • selfCommutator x := by
  apply Subtype.ext
  simp only [selfCommutator, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, selfAdjoint.val_smul]
  rw [smul_sub]

lemma smul_selfCommutator (r : ℝ) (x : A) :
    ∃ y : A, selfCommutator y = r • selfCommutator x := by
  by_cases hr : 0 ≤ r
  · exact ⟨Real.sqrt r • x, by rw [selfCommutator_smul, Real.mul_self_sqrt hr]⟩
  · refine ⟨Real.sqrt (-r) • star x, ?_⟩
    rw [selfCommutator_smul, Real.mul_self_sqrt (by linarith), selfCommutator_star,
      neg_smul_neg]

lemma commutatorSpan_finite_representation {v : selfAdjoint A} (hv : v ∈ commutatorSpan A) :
    ∃ n : ℕ, ∃ x : Fin n → A, v = ∑ i, selfCommutator (x i) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, rfl⟩ := hv
    exact ⟨1, fun _ => x, by simp⟩
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | add v w hv hw hv' hw' =>
    obtain ⟨n, x, rfl⟩ := hv'
    obtain ⟨m, y, rfl⟩ := hw'
    refine ⟨n + m, Fin.addCases x y, ?_⟩
    simp [Fin.sum_univ_add]
  | smul r v hv hv' =>
    obtain ⟨n, x, rfl⟩ := hv'
    choose y hy using fun i => smul_selfCommutator r (x i)
    exact ⟨n, y, by simp only [hy, Finset.smul_sum]⟩

lemma strictly_positive_of_interior [Nontrivial A] {x : selfAdjoint A}
    (hx : x ∈ interior (positiveCone A)) :
    ∃ ε : ℝ, 0 < ε ∧ ε • (1 : A) ≤ (x : A) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨r, hr, hb⟩ := hx
  refine ⟨r / 2, by linarith, ?_⟩
  have hp := hb (show x - (r / 2) • 1 ∈ Metric.ball x r from ?_)
  · change 0 ≤ (x : A) - (r / 2) • (1 : A) at hp
    exact sub_nonneg.mp hp
  · rw [Metric.mem_ball, dist_eq_norm, ← AddSubgroup.norm_coe]
    simp only [AddSubgroup.coe_neg, selfAdjoint.val_smul, selfAdjoint.val_one,
      sub_sub_cancel_left, norm_neg, norm_smul, norm_one, mul_one,
      Real.norm_eq_abs, abs_of_pos (show 0 < r / 2 by linarith)]
    linarith

lemma strictly_positive_finite_selfCommutators [Nontrivial A]
    (h : IsEmpty (TracialState A)) :
    ∃ (n : ℕ) (x : Fin n → A) (ε : ℝ), 0 < ε ∧
      ε • (1 : A) ≤ ∑ i, (star (x i) * x i - x i * star (x i)) := by
  obtain ⟨v, hvspan, hvpos⟩ := positive_commutator_of_no_trace h
  obtain ⟨n, x, hv⟩ := commutatorSpan_finite_representation hvspan
  obtain ⟨ε, hε, hle⟩ := strictly_positive_of_interior hvpos
  refine ⟨n, x, ε, hε, ?_⟩
  convert hle using 1
  all_goals try with_reducible_and_instances rfl
  rw [hv]
  simp [selfCommutator]

lemma normalize_selfCommutators [Nontrivial A] {n : ℕ} (x : Fin n → A)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ε • (1 : A) ≤ ∑ i, (star (x i) * x i - x i * star (x i))) :
    ∃ y : Fin (n + 1) → A,
      (∑ i, star (y i) * y i = 1) ∧ ‖∑ i, y i * star (y i)‖ < 1 := by
  let a : A := ∑ i, star (x i) * x i
  let b : A := ∑ i, x i * star (x i)
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => star_mul_self_nonneg (x i)
  have hgap' : ε • (1 : A) ≤ a - b := by
    simpa only [a, b, Finset.sum_sub_distrib] using hgap
  let c : ℝ := ‖a‖ + ε + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hca : ‖a‖ ≤ c := by dsimp [c]; linarith
  have hcε : ε < c := by dsimp [c]; linarith [norm_nonneg a]
  have hpad : 0 ≤ c • (1 : A) - a := by
    apply sub_nonneg.mpr
    exact ha.isSelfAdjoint.le_algebraMap_norm_self.trans (by
      rw [Algebra.algebraMap_eq_smul_one]
      exact smul_le_smul_of_nonneg_right hca zero_le_one)
  let t := CFC.sqrt (c • (1 : A) - a)
  have htstar : star t = t := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have htt : t * t = c • (1 : A) - a := CFC.sqrt_mul_sqrt_self _ hpad
  let z : Fin (n + 1) → A := Fin.cons t x
  have hzcol : ∑ i, star (z i) * z i = c • (1 : A) := by
    simp only [z, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, htstar, htt]
    change c • (1 : A) - a + a = _
    exact sub_add_cancel _ _
  have hzrow : ∑ i, z i * star (z i) = c • (1 : A) - (a - b) := by
    simp only [z, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, htstar, htt]
    change c • (1 : A) - a + b = _
    abel
  let k : ℝ := Real.sqrt c⁻¹
  have hkk : k * k = c⁻¹ := Real.mul_self_sqrt (inv_nonneg.mpr hc.le)
  let y : Fin (n + 1) → A := fun i => k • z i
  have hycol : ∑ i, star (y i) * y i = c⁻¹ • ∑ i, star (z i) * z i := by
    simp only [y, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
      smul_smul, hkk, Finset.smul_sum]
  have hyrow : ∑ i, y i * star (y i) = c⁻¹ • ∑ i, z i * star (z i) := by
    simp only [y, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
      smul_smul, hkk, Finset.smul_sum]
  refine ⟨y, ?_, ?_⟩
  · rw [hycol, hzcol, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  · have hbound : ∑ i, y i * star (y i) ≤ (c⁻¹ * (c - ε)) • (1 : A) := by
      rw [hyrow, hzrow, ← smul_smul]
      apply smul_le_smul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      rw [sub_smul]
      exact sub_le_sub_left hgap' _
    have hnonneg : 0 ≤ c⁻¹ * (c - ε) := mul_nonneg (inv_nonneg.mpr hc.le) (sub_nonneg.mpr hcε.le)
    have hlt : c⁻¹ * (c - ε) < 1 := by
      rw [← div_eq_inv_mul]
      exact (div_lt_one hc).mpr (sub_lt_self c hε)
    have hnorm := CStarAlgebra.norm_le_norm_of_le_of_nonneg hbound
      (Finset.sum_nonneg fun i _ => mul_star_self_nonneg (y i))
    have hnorm' : ‖∑ i, y i * star (y i)‖ ≤ c⁻¹ * (c - ε) := by
      simpa only [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        using hnorm
    exact hnorm'.trans_lt hlt

theorem finite_trace_obstruction [Nontrivial A] (h : IsEmpty (TracialState A)) :
    ∃ n : ℕ, ∃ y : Fin n → A,
      (∑ i, star (y i) * y i = 1) ∧ ‖∑ i, y i * star (y i)‖ < 1 := by
  obtain ⟨n, x, ε, hε, hx⟩ := strictly_positive_finite_selfCommutators h
  obtain ⟨y, hy⟩ := normalize_selfCommutators x ε hε hx
  exact ⟨n + 1, y, hy⟩

end KaplanskyConsequences

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_CStarEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

universe u v w
open scoped ComplexOrder InnerProductSpace BigOperators WithCStarModule
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type u} [CStarAlgebra A] {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

lemma tuple_product_column (a : ι → A) (b : κ → A)
    (ha : ∑ i, star (a i)*a i = 1) (hb : ∑ j, star (b j)*b j = 1) :
    ∑ p : ι × κ, star (a p.1*b p.2)*(a p.1*b p.2) = 1 := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  calc
    _ = ∑ j, star (b j) * (∑ i, star (a i)*a i) * b j := by
      simp only [star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ = 1 := by simpa [ha] using hb

lemma tuple_product_row (a : ι → A) (b : κ → A) (c d : ℝ)
    (_hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha : ∑ i, a i*star (a i) ≤ c • (1:A))
    (hb : ∑ j, b j*star (b j) ≤ d • (1:A)) :
    ∑ p : ι × κ, (a p.1*b p.2)*star (a p.1*b p.2) ≤ (c*d) • (1:A) := by
  rw [Fintype.sum_prod_type]
  calc
    ∑ i, ∑ j, (a i*b j)*star (a i*b j) = ∑ i, a i*(∑ j, b j*star (b j))*star (a i) := by
      simp only [star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ ≤ ∑ i, a i*(d • (1:A))*star (a i) :=
      Finset.sum_le_sum fun i _ => star_right_conjugate_le_conjugate hb _
    _ = d • ∑ i, a i*star (a i) := by simp [Finset.smul_sum]
    _ ≤ d • (c • (1:A)) := smul_le_smul_of_nonneg_left ha hd
    _ = (c*d) • (1:A) := by rw [smul_smul,mul_comm]

lemma exists_small_row_tuple (a : ι → A) (c : ℝ) (hc : 0 ≤ c)
    (hcol : ∑ i, star (a i)*a i = 1) (hrow : ∑ i, a i*star (a i) ≤ c • (1:A))
    (k : ℕ) : ∃ (J : Type v) (_ : Fintype J) (b : J → A),
      (∑ j, star (b j)*b j = 1) ∧ (∑ j, b j*star (b j) ≤ c^k • (1:A)) := by
  induction k with
  | zero =>
    exact ⟨PUnit,inferInstance,fun _ => 1,by simp,by simp⟩
  | succ k ih =>
    rcases ih with ⟨J,hJ,b,hb1,hb2⟩
    let := hJ
    refine ⟨ι × J,inferInstance,fun p => a p.1*b p.2,tuple_product_column a b hcol hb1,?_⟩
    simpa only [pow_succ,mul_comm] using tuple_product_row a b c (c^k) hc (pow_nonneg hc _) hrow hb2


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped InnerProductSpace ComplexOrder BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2200] Complex.partialOrder
variable {G : Type*}

variable [Group G]

lemma delta_cyclic (T : Algebra G) (h : T.val (delta 1) = 0) : T = 0 := by
  have hd (g : G) : T.val (delta g) = 0 := by
    ext k
    rw [algebra_delta,h]; rfl
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change T.val x = 0
  have hs := (T.val.hasSum (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x))
  have hz (g : G) : T.val (lp.single 2 g (x g)) = 0 := by
    have he : lp.single 2 g (x g) = (x g) • delta g := by
      ext k
      by_cases hkg : k=g <;> simp [delta_apply,lp.single_apply,hkg]
    rw [he,map_smul,hd,smul_zero]
  simp only [hz] at hs
  exact hs.unique hasSum_zero

lemma coefficient_faithful (T : Algebra G) (h : coefficient (star T*T) = 0) : T=0 := by
  rw [coefficient_square] at h
  exact delta_cyclic T ((inner_self_eq_zero).mp h)


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_TracialStable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem stablyFinite_of_faithful_trace (τ : TracialState A)
    (hfaith : ∀ a : A, τ.functional (star a*a) = 0 → a=0) : StablyFinite A := by
  intro n hn v hv
  let tr (x : CStarMatrix (Fin n) (Fin n) A) := ∑ i, τ.functional (x i i)
  have hcyc (x y : CStarMatrix (Fin n) (Fin n) A) : tr (x*y) = tr (y*x) := by
    simp only [tr,CStarMatrix.mul_apply,map_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact τ.tracial _ _
  let q := v*star v
  have hq : q*q=q := by
    dsimp [q]
    calc
      v*star v*(v*star v) = v*(star v*v)*star v := by noncomm_ring
      _ = v*star v := by rw [hv,mul_one]
  let p := 1-q
  have hpstar : star p=p := by simp [p,q,star_mul]
  have hpp : star p*p=p := by
    rw [hpstar]
    change (1-q)*(1-q)=1-q
    calc
      _ = 1-q-q+q*q := by noncomm_ring
      _ = 1-q := by rw [hq]; abel
  have htr : tr p = 0 := by
    change ∑ i, τ.functional ((1-q) i i) = 0
    simp only [CStarMatrix.sub_apply,map_sub,Finset.sum_sub_distrib]
    change tr 1 - tr (v*star v) = 0
    rw [hcyc,hv,sub_self]
  have hz : ∑ i : Fin n, ∑ j : Fin n, τ.functional (star (p j i)*p j i) = 0 := by
    have he := hpp
    have ht := congrArg tr he
    simpa only [tr,CStarMatrix.mul_apply,CStarMatrix.star_apply,map_sum,htr] using ht.trans htr
  have hnon (i j : Fin n) : 0 ≤ τ.functional (star (p j i)*p j i) :=
    τ.functional.map_nonneg (star_mul_self_nonneg _)
  have hp : p=0 := by
    ext i j
    apply hfaith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnon i j))).mp hz j (Finset.mem_univ j)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnon j k)).mp hi i (Finset.mem_univ i)
  exact (sub_eq_zero.mp hp).symm


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedStable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace KaplanskyConsequences.Regular
variable {G : Type*} [Group G]

theorem algebra_stablyFinite : StablyFinite (Algebra G) :=
  stablyFinite_of_faithful_trace canonicalTrace coefficient_faithful

end KaplanskyConsequences.Regular
end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensor_two_isometries_of_row_contraction (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {ι : Type*} [Fintype ι] (a : ι → A) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∑ i, star (a i)*a i = 1) (hr : ∑ i, a i*star (a i) ≤ c • (1:A)) :
    ∃ s t : tensorAlgebra (G:=F2) ρ, star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ) < 1/10000) hc1
  obtain ⟨J,hJ,b,hb1,hb2⟩ := exists_small_row_tuple a c hc0 hc hr k
  let := hJ
  apply tensor_two_isometries_of_small_tuple ρ b hb1
  exact hb2.trans (smul_le_smul_of_nonneg_right hk.le (zero_le_one' A))


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_StateExists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
lemma positiveCone_closed : IsClosed (positiveCone A) :=
  isClosed_le continuous_const continuous_subtype_val

lemma neg_one_not_positiveCone : (-1 : selfAdjoint A) ∉ positiveCone A := by
  intro h
  have h' : (1:A) ≤ 0 := by
    have : -(1:A) ≥ 0 := h
    simpa only [neg_nonneg] using this
  exact one_ne_zero (le_antisymm h' zero_le_one)

lemma normalized_positive_functional_exists : ∃ f : A →ₚ[ℂ] ℂ, f 1=1 := by
  obtain ⟨f,u,hneg,hpos⟩ := geometric_hahn_banach_point_closed
    (positiveCone_convex (A:=A)) (positiveCone_closed (A:=A)) (neg_one_not_positiveCone (A:=A))
  have hu : u<0 := by simpa using hpos 0 (show 0 ∈ positiveCone A from (by change (0:A)≤0; exact le_rfl))
  have hfpos (x : selfAdjoint A) (hx : 0 ≤ (x:A)) : 0 ≤ f x := by
    by_contra hn
    have hn : f x < 0 := lt_of_not_ge hn
    let t : ℝ := (u-1)/(f x)
    have ht : 0 ≤ t := div_nonneg_of_nonpos (by linarith) hn.le
    have htX : t • x ∈ positiveCone A := smul_nonneg ht hx
    have hb := hpos (t • x) htX
    rw [map_smul,smul_eq_mul,show t*f x=u-1 from div_mul_cancel₀ _ hn.ne] at hb
    linarith
  have hf1 : 0<f 1 := by
    rw [map_neg] at hneg
    linarith
  let g : selfAdjoint A →ₗ[ℝ] ℝ := (f 1)⁻¹ • f.toLinearMap
  have hgpos (x : selfAdjoint A) (hx : 0 ≤ (x:A)) : 0 ≤ g x := by
    change 0 ≤ (f 1)⁻¹ * f x
    exact mul_nonneg (inv_nonneg.mpr hf1.le) (hfpos x hx)
  have hg1 : g 1=1 := inv_mul_cancel₀ hf1.ne'
  let φ := complexify g
  have hφpos (x : A) (hx : 0≤x) : 0≤φ x := by
    rw [show φ x = (g ⟨x,IsSelfAdjoint.of_nonneg hx⟩ : ℂ) from
      complexify_apply_selfAdjoint g x (IsSelfAdjoint.of_nonneg hx)]
    exact_mod_cast hgpos ⟨x,IsSelfAdjoint.of_nonneg hx⟩ hx
  refine ⟨PositiveLinearMap.mk₀ φ hφpos,?_⟩
  change φ 1=1
  rw [show φ 1 = (g 1:ℂ) from complexify_apply_selfAdjoint g 1 (IsSelfAdjoint.one A),hg1]
  rfl


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_SimpleRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder InnerProductSpace
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

lemma simple_hom_injective [Nontrivial B] (hA : CStarSimple A) (f : A →⋆ₐ[ℂ] B) :
    Function.Injective f := by
  rcases hA (homKernel f) with hzero | hwhole
  · intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    change f (a-b)=0
    rw [map_sub,hab,sub_self]
  · have h := hwhole 1
    change f 1=0 at h
    rw [map_one] at h
    exact (one_ne_zero h).elim

lemma gns_nontrivial (f : A →ₚ[ℂ] ℂ) (hf : f 1=1) : Nontrivial f.GNS := by
  apply nontrivial_of_ne ((f.toPreGNS 1 : f.PreGNS) : f.GNS) 0
  intro h
  have he := congrArg norm h
  rw [UniformSpace.Completion.norm_coe,norm_zero] at he
  have hs := f.preGNS_norm_sq (f.toPreGNS 1)
  apply (zero_ne_one : (0:ℂ)≠1)
  simpa only [he,Complex.ofReal_zero,zero_pow (by decide : 2≠0),f.ofPreGNS_toPreGNS,
    star_one,one_mul,hf] using hs

theorem simple_faithful_representation [Nontrivial A] (hA : CStarSimple A) :
    ∃ (H : Type u) (instH : NormedAddCommGroup H) (innerH : InnerProductSpace ℂ H),
      letI := instH
      letI := innerH
      ∃ (completeH : CompleteSpace H),
        letI := completeH
        ∃ ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H), Function.Injective ρ := by
  obtain ⟨f,hf⟩ := normalized_positive_functional_exists (A:=A)
  let : Nontrivial f.GNS := gns_nontrivial f hf
  exact ⟨f.GNS,inferInstance,inferInstance,inferInstance,f.gnsStarAlgHom,
    simple_hom_injective hA f.gnsStarAlgHom⟩


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_SimpleReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder BigOperators
open Kaplansky Regular
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem tensor_properlyInfinite_of_no_trace {A : Type*} [CStarAlgebra A] [Nontrivial A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hτ : IsEmpty (TracialState A)) :
    ProperlyInfinite (tensorAlgebra (G:=F2) ρ) := by
  obtain ⟨n,y,hcol,hrow⟩ := finite_trace_obstruction hτ
  apply tensor_two_isometries_of_row_contraction ρ y ‖∑ i, y i*star (y i)‖
    (norm_nonneg _) hrow hcol
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ => mul_star_self_nonneg (y i))).le_algebraMap_norm_self

theorem simple_stable_tensor_reduction
    (h : ∃ (M : Type) (inst : CStarAlgebra M),
      letI := inst
      Nontrivial M ∧ CStarSimple M ∧ StablyFinite M ∧ IsEmpty (TracialState M)) :
    SimpleStableTensorCounterexample := by
  obtain ⟨M,inst,hM,hs,hf,ht⟩ := h
  let := inst
  let := hM
  obtain ⟨H,instH,innerH,completeH,ρ,hρ⟩ := simple_faithful_representation hs
  let := instH
  let := innerH
  let := completeH
  refine ⟨algebra_F2_simple,algebra_stablyFinite (G:=F2),M,inst,hM,hs,hf,H,instH,
    innerH,completeH,ρ,hρ,tensor_properlyInfinite_of_no_trace ρ ht⟩


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_SimpleTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace KaplanskyConsequences

theorem simple_stable_tensor_counterexample_exists_oai : SimpleStableTensorCounterexample :=
  simple_stable_tensor_reduction simple_stablyFinite_traceless_exists

end KaplanskyConsequences
end
end

end OAI
end

theorem solution : type_of% @OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists_oai := @OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists_oai
