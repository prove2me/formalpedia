-- Prove2me | solution 1 for OAI.KaplanskyConsequences.separable_extraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:45:26.139381+00:00
-- url     : https://prove2.me/submissions/1e95b805-46ee-40b3-bea3-3a631731a399

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf005
import Definitions.Def_OAIQ15Sf010

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Products
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded C-star products and the generated separable unital algebra. -/

noncomputable section
open TopologicalSpace
open scoped Pointwise
namespace Kaplansky

/-- Countably many letters have only countably many finite multiplicative words. -/
theorem countable_monoid_closure {A : Type*} [Monoid A] {s : Set A}
    (hs : s.Countable) : (Submonoid.closure s : Set A).Countable := by
  let : Countable s := hs.to_subtype
  let : Countable (FreeMonoid s) := inferInstanceAs (Countable (List s))
  rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
  exact Set.countable_range _

variable {A : Type*} [CStarAlgebra A]

theorem generatedAlgebra_separable {s : Set A} (hs : s.Countable) :
    SeparableSpace (generatedAlgebra s) := by
  have hstar : (star s).Countable := by
    convert hs.image star using 1
    all_goals try with_reducible_and_instances rfl
    ext a
    simp
  have hw := countable_monoid_closure (hs.union hstar)
  have hspan := hw.isSeparable.span (R := ℂ)
  rw [← StarAlgebra.adjoin_eq_span] at hspan
  have hc := hspan.closure
  exact hc.separableSpace

instance finiteGeneratedAlgebra_separable {N : ℕ} (x : Fin N → A) :
    SeparableSpace (generatedAlgebra (Set.range x)) :=
  generatedAlgebra_separable (Set.countable_range x)

end Kaplansky

end

end OAI
end

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
open scoped BigOperators ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem no_tracialState_of_finite_obstruction {n : ℕ} (y : Fin n → A)
    (hcol : ∑ i, star (y i) * y i = 1)
    (hrow : ‖∑ i, y i * star (y i)‖ < 1) : IsEmpty (TracialState A) := by
  refine ⟨fun τ => ?_⟩
  have heq : τ.functional (∑ i, y i * star (y i)) = 1 := by
    calc
      τ.functional (∑ i, y i * star (y i)) =
          ∑ i, τ.functional (y i * star (y i)) := map_sum _ _ _
      _ = ∑ i, τ.functional (star (y i) * y i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact τ.tracial _ _
      _ = τ.functional (∑ i, star (y i) * y i) := (map_sum _ _ _).symm
      _ = 1 := by rw [hcol, τ.normalized]
  have hpos : 0 ≤ ∑ i, y i * star (y i) := by
    exact Finset.sum_nonneg fun i _ => mul_star_self_nonneg (y i)
  have hbound := τ.functional.norm_apply_le_of_nonneg _ hpos
  rw [heq, τ.normalized, norm_one, one_mul] at hbound
  exact (not_le_of_gt hrow) hbound

theorem stablyFinite_of_injective (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f)
    (hB : StablyFinite B) : StablyFinite A := by
  intro n hn v hv
  let F := CStarMatrix.mapₙₐ (n := Fin n) f.toNonUnitalStarAlgHom
  have hF1 : F 1 = 1 := by
    ext i j
    simp [F, CStarMatrix.mapₙₐ, CStarMatrix.mapₗ, CStarMatrix.map,
      CStarMatrix.one_apply]
    rfl
  have hFv : star (F v) * F v = 1 := by
    rw [← map_star, ← map_mul, hv, hF1]
  have hout := hB n hn (F v) hFv
  have hFinj : Function.Injective F := CStarMatrix.map_injective hf
  apply hFinj
  simpa only [map_mul, map_star, hF1] using hout

theorem finite_generated_extraction (hA : StablyFinite A) {n : ℕ} (y : Fin n → A)
    (hcol : ∑ i, star (y i) * y i = 1)
    (hrow : ‖∑ i, y i * star (y i)‖ < 1) :
    let C := Kaplansky.generatedAlgebra (Set.range y)
    TopologicalSpace.SeparableSpace C ∧ StablyFinite C ∧ IsEmpty (TracialState C) := by
  dsimp only
  let C := Kaplansky.generatedAlgebra (Set.range y)
  let z : Fin n → C := Kaplansky.generatedGenerator y
  refine ⟨inferInstance, stablyFinite_of_injective C.subtype Subtype.val_injective hA, ?_⟩
  apply no_tracialState_of_finite_obstruction z
  · apply Subtype.val_injective
    simpa [z, Kaplansky.generatedGenerator] using hcol
  · simpa [z, Kaplansky.generatedGenerator] using hrow

end KaplanskyConsequences

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

namespace KaplanskyConsequences

theorem separable_extraction_oai {A : Type} [CStarAlgebra A] [Nontrivial A]
    (hA : StablyFinite A) (hτ : IsEmpty (TracialState A)) :
    TraceFreeStablyFinite := by
  obtain ⟨n, y, hcol, hrow⟩ := finite_trace_obstruction hτ
  let C := Kaplansky.generatedAlgebra (Set.range y)
  obtain ⟨hs, hf, ht⟩ := finite_generated_extraction hA y hcol hrow
  exact ⟨C, inferInstance, inferInstance, hs, hf, ht⟩

end KaplanskyConsequences
end
end

end OAI
end

theorem solution : type_of% @OAI.KaplanskyConsequences.separable_extraction_oai := @OAI.KaplanskyConsequences.separable_extraction_oai
