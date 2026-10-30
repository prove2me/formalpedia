-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:54:52.855232+00:00
-- url     : https://prove2.me/submissions/bc384fd6-7925-4a6a-98e9-3f96c0f158f2

import Mathlib
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S063
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Cayley_hasMixing_of_smallWalsh

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared interfaces for sparse ternary parity checks

The definitions distinguish edge coordinates from graph vertices. Parallel
edges have different ports. All construction theorems built on these interfaces
must eventually discharge the local-distance and graph-mixing hypotheses.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

section Words

variable {C R : Type*} [Fintype C]

theorem weight_eq_sum (w : C → F3) :
    weight w = ∑ c, if w c ≠ 0 then 1 else 0 := by
  simp [weight, support, Finset.card_filter]

end Words

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeLogBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableHasDistance _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The reviewed log-size variant of the local code, using only integer bounds. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

theorem relative_of_log_distance {D B ell t : ℕ}
    (hB : 0 < B) (hell : 0 < ell)
    (Q : CheckMatrix (Fin t) (Fin D))
    (hQ : HasDistance Q (D / (100 * B * ell) + 1)) :
    HasRelativeDistance Q (1 / (100 * (B : ℝ) * (ell : ℝ))) := by
  intro v hv hv0
  have hd : 0 < 100 * B * ell := by positivity
  have hbound := Nat.lt_mul_div_succ D hd
  have hboundR : (D : ℝ) <
      (100 * (B : ℝ) * (ell : ℝ)) * ((D / (100 * B * ell) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hbound
  have hdR : 0 < 100 * (B : ℝ) * (ell : ℝ) := by positivity
  have hw := hQ v hv hv0
  simp only [Fintype.card_fin]
  calc
    1 / (100 * (B : ℝ) * (ell : ℝ)) * D =
        (D : ℝ) / (100 * (B : ℝ) * (ell : ℝ)) := by ring
    _ ≤ ((D / (100 * B * ell) + 1 : ℕ) : ℝ) :=
      (div_le_iff₀ hdR).mpr (by simpa only [mul_comm] using hboundR.le)
    _ ≤ (weight v : ℝ) := by exact_mod_cast hw

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableHasDistance _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem relative_fraction (m : ℕ) {B : ℕ} (hB : 0 < B) :
    (1 / (100 * (B : ℝ) * logSize m)) *
        (1 / (100 * (B : ℝ) * logSize m) - 1 / (gapDenom m B : ℝ)) =
      1 / (distanceDenom m B : ℝ) := by
  have hbr : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hlr : (logSize m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (logSize_pos m)
  simp only [gapDenom, distanceDenom, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ; ring

theorem distanceDenom_pos (m : ℕ) {B : ℕ} (hB : 0 < B) :
    0 < distanceDenom m B := by
  have := logSize_pos m
  unfold distanceDenom
  positivity

theorem relativeDistance_integer {C R : Type*} [Fintype C]
    {Q : CheckMatrix R C} {P : ℕ} (hP : 0 < P)
    (hQ : HasRelativeDistance Q (1 / (P : ℝ)))
    (w : C → F3) (hw : IsCodeword Q w) (hw0 : w ≠ 0) :
    Fintype.card C ≤ P * weight w := by
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  have hh := hQ w hw hw0
  have hh' : (Fintype.card C : ℝ) / (P : ℝ) ≤ (weight w : ℝ) := by
    convert hh using 1 <;> first | rfl | ring
  have hx := (div_le_iff₀ hp).mp hh'
  exact_mod_cast (show (Fintype.card C : ℝ) ≤ (P : ℝ) * (weight w : ℝ) by nlinarith)

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeTanner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableHasDistance _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

/-- The real inequality used after counting the active left and right
vertices. It has no graph or coding hypotheses hidden in its statement. -/
theorem tanner_scalar_bound {S u v D N δ ε : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hD : 0 < D) (hN : 0 < N)
    (hδ : 0 ≤ δ)
    (hleft : δ * D * u ≤ S) (hright : δ * D * v ≤ S)
    (hmix : S ≤ D * u * v / N + ε * D * Real.sqrt (u * v)) :
    N * D * δ * (δ - ε) ≤ S := by
  let t := Real.sqrt (u * v)
  have ht : 0 < t := Real.sqrt_pos.2 (mul_pos hu hv)
  have ht2 : t ^ 2 = u * v := Real.sq_sqrt (le_of_lt (mul_pos hu hv))
  have hδD : 0 ≤ δ * D := mul_nonneg hδ hD.le
  have hlocal : δ * D * t ≤ S := by
    rcases le_total u v with huv | hvu
    · have htv : t ≤ v := Real.sqrt_le_iff.mpr ⟨hv.le, by nlinarith⟩
      exact (mul_le_mul_of_nonneg_left htv hδD).trans hright
    · have htu : t ≤ u := Real.sqrt_le_iff.mpr ⟨hu.le, by nlinarith⟩
      exact (mul_le_mul_of_nonneg_left htu hδD).trans hleft
  have hmul : (δ - ε) * (D * t) ≤ (t / N) * (D * t) := by
    calc
      (δ - ε) * (D * t) = δ * D * t - ε * D * t := by ring
      _ ≤ D * u * v / N := by linarith
      _ = (t / N) * (D * t) := by rw [div_mul_eq_mul_div]; congr 1; nlinarith
  have hratio : δ - ε ≤ t / N := le_of_mul_le_mul_right hmul (mul_pos hD ht)
  have hsize : N * (δ - ε) ≤ t := by
    have := (le_div_iff₀ hN).mp hratio
    nlinarith
  calc
    N * D * δ * (δ - ε) = (δ * D) * (N * (δ - ε)) := by ring
    _ ≤ (δ * D) * t := mul_le_mul_of_nonneg_left hsize hδD
    _ ≤ S := hlocal

namespace PortGraph

variable {V P R : Type*} [Fintype V] [Fintype P]
    [DecidableEq V] [DecidableEq P]

omit [DecidableEq V] [DecidableEq P] in
theorem sum_left_weights (w : V × P → F3) :
    ∑ v, weight (leftWord w v) = weight w := by
  simp only [weight_eq_sum, leftWord]
  exact (Fintype.sum_prod_type (fun e : V × P => if w e ≠ 0 then (1 : ℕ) else 0)).symm

omit [DecidableEq V] [DecidableEq P] in
theorem sum_right_weights (G : PortGraph V P) (w : V × P → F3) :
    ∑ v, weight (G.rightWord w v) = weight w := by
  simp only [weight_eq_sum, rightWord]
  calc
    _ = ∑ e : V × P, if w (G.rotation.symm e) ≠ 0 then (1 : ℕ) else 0 :=
      (Fintype.sum_prod_type
        (fun e : V × P => if w (G.rotation.symm e) ≠ 0 then (1 : ℕ) else 0)).symm
    _ = _ := G.rotation.symm.sum_comp (fun e => if w e ≠ 0 then (1 : ℕ) else 0)

omit [DecidableEq V] [DecidableEq P] in
theorem leftActive_nonempty (w : V × P → F3) (hw : w ≠ 0) :
    (leftActive w).Nonempty := by
  obtain ⟨e, he⟩ := Function.ne_iff.mp hw
  refine ⟨e.1, (mem_leftActive w e.1).2 ?_⟩
  intro hz
  have := congrFun hz e.2
  exact he this

omit [DecidableEq V] [DecidableEq P] in
theorem rightActive_nonempty (G : PortGraph V P) (w : V × P → F3) (hw : w ≠ 0) :
    (G.rightActive w).Nonempty := by
  obtain ⟨e, he⟩ := Function.ne_iff.mp hw
  refine ⟨(G.rotation e).1, (mem_rightActive G w _).2 ?_⟩
  intro hz
  have hh := congrFun hz (G.rotation e).2
  simp only [rightWord, Prod.mk.eta, Equiv.symm_apply_apply, Pi.zero_apply] at hh
  exact he hh

omit [DecidableEq P] in
theorem support_subset_edgesBetween (G : PortGraph V P) (w : V × P → F3) :
    support w ⊆ G.edgesBetween (leftActive w) (G.rightActive w) := by
  intro e he
  have hw := (mem_support w e).mp he
  simp only [edgesBetween, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · apply (mem_leftActive w e.1).2
    intro hz
    exact hw (congrFun hz e.2)
  · apply (mem_rightActive G w (G.rotation e).1).2
    intro hz
    have hh := congrFun hz (G.rotation e).2
    simp only [rightWord, Prod.mk.eta, Equiv.symm_apply_apply, Pi.zero_apply] at hh
    exact hw hh

omit [DecidableEq P] in
theorem weight_le_edgeCount (G : PortGraph V P) (w : V × P → F3) :
    weight w ≤ G.edgeCount (leftActive w) (G.rightActive w) :=
  Finset.card_le_card (support_subset_edgesBetween G w)

omit [DecidableEq V] [DecidableEq P] in
theorem local_left_mass {Q : CheckMatrix R P} {δ : ℝ}
    (hQ : HasRelativeDistance Q δ) (w : V × P → F3)
    (hw : ∀ v, IsCodeword Q (leftWord w v)) :
    δ * Fintype.card P * (leftActive w).card ≤ (weight w : ℝ) := by
  calc
    δ * Fintype.card P * (leftActive w).card =
        ∑ _v ∈ leftActive w, δ * Fintype.card P := by simp [mul_comm]
    _ ≤ ∑ v ∈ leftActive w, (weight (leftWord w v) : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hQ _ (hw v) ((mem_leftActive w v).mp hv)
    _ ≤ ∑ v, (weight (leftWord w v) : ℝ) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.cast_nonneg _)
    _ = (weight w : ℝ) := by exact_mod_cast sum_left_weights w

omit [DecidableEq V] [DecidableEq P] in
theorem local_right_mass (G : PortGraph V P) {Q : CheckMatrix R P} {δ : ℝ}
    (hQ : HasRelativeDistance Q δ) (w : V × P → F3)
    (hw : ∀ v, IsCodeword Q (G.rightWord w v)) :
    δ * Fintype.card P * (G.rightActive w).card ≤ (weight w : ℝ) := by
  calc
    δ * Fintype.card P * (G.rightActive w).card =
        ∑ _v ∈ G.rightActive w, δ * Fintype.card P := by simp [mul_comm]
    _ ≤ ∑ v ∈ G.rightActive w, (weight (G.rightWord w v) : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hQ _ (hw v) ((mem_rightActive G w v).mp hv)
    _ ≤ ∑ v, (weight (G.rightWord w v) : ℝ) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.cast_nonneg _)
    _ = (weight w : ℝ) := by exact_mod_cast sum_right_weights G w

omit [DecidableEq P] in
/-- Global Tanner distance from only the explicit local distance and the
finite graph mixing inequality. -/
theorem tanner_distance (G : PortGraph V P) {Q : CheckMatrix R P} {δ ε : ℝ}
    (hV : 0 < Fintype.card V) (hP : 0 < Fintype.card P)
    (hδ : 0 ≤ δ) (hQ : HasRelativeDistance Q δ) (hG : G.HasMixing ε)
    (w : V × P → F3) (hw : G.IsTannerCodeword Q w) (hw0 : w ≠ 0) :
    (Fintype.card V : ℝ) * Fintype.card P * δ * (δ - ε) ≤ (weight w : ℝ) := by
  apply tanner_scalar_bound
      (u := ((leftActive w).card : ℝ))
      (v := ((G.rightActive w).card : ℝ))
      (D := (Fintype.card P : ℝ)) (N := (Fintype.card V : ℝ))
      (ε := ε)
  · exact_mod_cast Finset.card_pos.mpr (leftActive_nonempty w hw0)
  · exact_mod_cast Finset.card_pos.mpr (rightActive_nonempty G w hw0)
  · exact_mod_cast hP
  · exact_mod_cast hV
  · exact hδ
  · exact local_left_mass hQ w hw.1
  · exact local_right_mass G hQ w hw.2
  · have he : (weight w : ℝ) ≤
        (G.edgeCount (leftActive w) (G.rightActive w) : ℝ) := by
      exact_mod_cast weight_le_edgeCount G w
    exact he.trans (hG _ _)

end PortGraph

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableHasDistance _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode.PortGraph

open scoped BigOperators

variable {V P R : Type*} [Fintype V] [Fintype P]
    [DecidableEq V] [DecidableEq P]

omit [DecidableEq P] in
theorem isCodeword_matrix_iff (G : PortGraph V P) (Q : CheckMatrix R P)
    (w : V × P → F3) : IsCodeword (G.matrix Q) w ↔ G.IsTannerCodeword Q w := by
  constructor
  · intro hw
    constructor
    · intro v r
      simpa using hw (Sum.inl (v, r))
    · intro v r
      simpa using hw (Sum.inr (v, r))
  · rintro ⟨hleft, hright⟩ r
    rcases r with ⟨v, r⟩ | ⟨v, r⟩
    · exact (check_matrix_left G Q w v r).trans (hleft v r)
    · exact (check_matrix_right G Q w v r).trans (hright v r)

omit [DecidableEq P] in
theorem matrix_relativeDistance (G : PortGraph V P) {Q : CheckMatrix R P}
    {δ ε : ℝ} (hV : 0 < Fintype.card V) (hP : 0 < Fintype.card P)
    (hδ : 0 ≤ δ) (hQ : HasRelativeDistance Q δ) (hG : G.HasMixing ε) :
    HasRelativeDistance (G.matrix Q) (δ * (δ - ε)) := by
  intro w hw hw0
  have ht := G.tanner_distance hV hP hδ hQ hG w
    ((G.isCodeword_matrix_iff Q w).mp hw) hw0
  simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using ht

end SubexponentialSAT.SqrtLog.SparseCode.PortGraph

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeShorten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableHasDistance _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

variable {C E R : Type*} [Fintype C] [Fintype E]
    [DecidableEq C] [DecidableEq E]

omit [Fintype E] [DecidableEq C] in
theorem zeroExtend_eq_zero_of_not_mem (e : C ↪ E) (w : C → F3) (z : E)
    (hz : ∀ c, e c ≠ z) : zeroExtend e w z = 0 := by
  simp [zeroExtend, hz]

theorem support_zeroExtend (e : C ↪ E) (w : C → F3) :
    support (zeroExtend e w) = (support w).image e := by
  ext z
  by_cases hz : ∃ c, e c = z
  · obtain ⟨c, rfl⟩ := hz
    simp only [mem_support, zeroExtend_apply, Finset.mem_image]
    constructor
    · intro hw
      exact ⟨c, hw, rfl⟩
    · rintro ⟨a, ha, he⟩
      have hac : a = c := e.injective he
      simpa [hac] using ha
  · have he : ∀ c, e c ≠ z := by simpa only [not_exists] using hz
    simp only [mem_support, zeroExtend_eq_zero_of_not_mem e w z he, ne_eq,
      not_true_eq_false, Finset.mem_image]
    constructor
    · intro h
      exact h.elim
    · rintro ⟨c, _, hc⟩
      exact he c hc

@[simp] theorem weight_zeroExtend (e : C ↪ E) (w : C → F3) :
    weight (zeroExtend e w) = weight w := by
  simp only [weight, support_zeroExtend]
  exact Finset.card_image_of_injective _ e.injective

omit [Fintype E] in
theorem zeroExtend_ne_zero (e : C ↪ E) {w : C → F3} (hw : w ≠ 0) :
    zeroExtend e w ≠ 0 := by
  intro h
  apply hw
  funext c
  have := congrFun h (e c)
  simpa using this

omit [DecidableEq C] in
theorem check_zeroExtend (Q : CheckMatrix R E) (e : C ↪ E)
    (w : C → F3) (r : R) :
    check Q (zeroExtend e w) r = check (shorten Q e) w r := by
  simp only [check, zeroExtend, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [shorten, mul_ite]

omit [DecidableEq C] in
theorem isCodeword_shorten_iff (Q : CheckMatrix R E) (e : C ↪ E) (w : C → F3) :
    IsCodeword (shorten Q e) w ↔ IsCodeword Q (zeroExtend e w) := by
  simp only [IsCodeword, check_zeroExtend]

/-- Preserve the absolute lower bound, using the original column count.
Only the later arithmetic wrapper replaces it by the smaller count. -/
theorem relativeDistance_shorten_absolute (Q : CheckMatrix R E) (e : C ↪ E)
    {δ : ℝ} (hQ : HasRelativeDistance Q δ) (w : C → F3)
    (hw : IsCodeword (shorten Q e) w) (hw0 : w ≠ 0) :
    δ * Fintype.card E ≤ (weight w : ℝ) := by
  simpa using hQ _ ((isCodeword_shorten_iff Q e w).mp hw) (zeroExtend_ne_zero e hw0)

theorem relativeDistance_shorten (Q : CheckMatrix R E) (e : C ↪ E)
    {δ : ℝ} (hδ : 0 ≤ δ) (hQ : HasRelativeDistance Q δ) :
    HasRelativeDistance (shorten Q e) δ := by
  intro w hw hw0
  have hc : (Fintype.card C : ℝ) ≤ Fintype.card E := by
    exact_mod_cast Fintype.card_le_of_injective e e.injective
  exact (mul_le_mul_of_nonneg_left hc hδ).trans
    (relativeDistance_shorten_absolute Q e hQ w hw hw0)

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Existence and finite executable search for a small Walsh spectrum. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

theorem good_iff_smallWalsh {r D q : ℕ} (hq : 1 ≤ q) (s : Fin D → Cube r) :
    Good q s ↔ SmallWalsh s (1 / (q : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  constructor
  · intro h a ha
    have hi := h a ha
    have hr : (q : ℝ) * |(walshInt s a : ℝ)| ≤ (D : ℝ) := by exact_mod_cast hi
    rw [walshInt_cast] at hr
    simpa only [Fintype.card_fin, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      (le_div_iff₀ hqpos).mpr (show |walsh s a| * q ≤ (D : ℝ) by nlinarith)
  · intro h a ha
    have hr := h a ha
    simp only [Fintype.card_fin] at hr
    have hr' : |walsh s a| ≤ (D : ℝ) / q := by
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hr
    have hh := (le_div_iff₀ hqpos).mp hr'
    have hz : (q : ℝ) * |(walshInt s a : ℝ)| ≤ (D : ℝ) := by
      rw [walshInt_cast]
      nlinarith
    exact_mod_cast hz

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeSupplied
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The sparse-code assembly accepts any successful physical search output.
It does not require agreement with the semantic search enumeration order.
Physical serializers must emit the local incidence slots, rather than all
columns of these extensional matrices. -/
namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

theorem suppliedMatrix_distance {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (hs : WalshExistence.Good (gapDenom m B) s)
    (hQ : HasDistance Q (degree m B / (100 * B * logSize m) + 1)) :
    HasRelativeDistance (suppliedMatrix m B hm hB s Q)
      (1 / (distanceDenom m B : ℝ)) := by
  have hlocal := LocalCode.relative_of_log_distance hB (logSize_pos m) Q hQ
  have hwalsh := (WalshExistence.good_iff_smallWalsh (gapDenom_pos m hB) s).mp hs
  have hmix := Cayley.hasMixing_of_smallWalsh s (1 / (gapDenom m B : ℝ))
    (by positivity) hwalsh
  have hV : 0 < Fintype.card (Cayley.Cube (dimension m B)) := Fintype.card_pos
  have hP : 0 < Fintype.card (Fin (degree m B)) := by simpa using degree_pos hm hB
  have hglobal := (Cayley.graph s).matrix_relativeDistance hV hP
    (by positivity : (0 : ℝ) ≤ 1 / (100 * (B : ℝ) * logSize m)) hlocal hmix
  rw [relative_fraction m hB] at hglobal
  have hshort := relativeDistance_shorten _ (columnEmbedding m B hm hB)
    (by positivity : (0 : ℝ) ≤ 1 / (distanceDenom m B : ℝ)) hglobal
  intro w hw hw0
  apply hshort w _ hw0
  intro r
  obtain ⟨i,rfl⟩ := (rowEquiv m B).surjective r
  exact hw i

/-- The physical serializer may enumerate or reverse the rows in any order.
Coverage is sufficient; no agreement with rowEquiv's list order is assumed. -/
theorem supplied_kernel_bound_of_coverage_oai {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (hs : WalshExistence.Good (gapDenom m B) s)
    (hQ : HasDistance Q (degree m B / (100 * B * logSize m) + 1))
    (rs : List (Fin m → F3))
    (hcover : ∀ i, suppliedMatrix m B hm hB s Q i ∈ rs)
    (w : Fin m → F3) (hw : ∀ r ∈ rs, (∑ c, r c*w c)=0) (hw0 : w≠0) :
    m ≤ distanceDenom m B*weight w := by
  have hc : IsCodeword (suppliedMatrix m B hm hB s Q) w := fun i => hw _ (hcover i)
  simpa only [Fintype.card_fin] using relativeDistance_integer (distanceDenom_pos m hB)
    (suppliedMatrix_distance hm hB s Q hs hQ) w hc hw0

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage_oai
