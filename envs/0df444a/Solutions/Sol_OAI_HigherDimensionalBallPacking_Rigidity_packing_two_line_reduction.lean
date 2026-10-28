-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:07:21.046174+00:00
-- url     : https://prove2.me/submissions/f61e8936-53b8-4206-9b81-8a56a7c98e16

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp006
import Definitions.Def_OAIQ10Bp007

section
-- module Solutions.OAIQ10_BP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CompatibleStructures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

theorem standardForm_J_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) :
    0 < standardForm v (standardJ n v) := by
  rw [standardForm_J_self]
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hpos : 0 < Complex.normSq (v i) := Complex.normSq_pos.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
    (Finset.mem_univ i))

theorem compatible_standardJ (n : ℕ) : Compatible (standardJ n) :=
  ⟨standardJ_sq n, standardForm_J_J, fun _ hv => standardForm_J_pos hv⟩

theorem compatible_conjugateJ {n : ℕ} (e : Phase n ≃L[ℝ] Phase n)
    (he : ∀ v w, standardForm (e v) (e w) = standardForm v w) :
    Compatible (conjugateJ e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simp
  · intro v w
    simp only [conjugateJ_apply, he, standardForm_J_J]
    simpa using (he (e.symm v) (e.symm w)).symm
  · intro v hv
    have hv' : e.symm v ≠ 0 := by
      intro h
      apply hv
      simpa using congrArg e h
    have h := he (e.symm v) (standardJ n (e.symm v))
    rw [e.apply_symm_apply] at h
    change 0 < standardForm v (e (standardJ n (e.symm v)))
    rw [h]
    exact standardForm_J_pos hv'

theorem symplectic_linear_injective {n : ℕ} {A : End n}
    (hA : ∀ v w, standardForm (A v) (A w) = standardForm v w) :
    Injective A := by
  apply (injective_iff_map_eq_zero A).mpr
  intro v hv
  by_contra hne
  have hp := standardForm_J_pos hne
  have he := hA v (standardJ n v)
  rw [hv, show standardForm (0 : Phase n) (A (standardJ n v)) = 0 by
    simp [standardForm]] at he
  exact (ne_of_gt hp) he.symm

theorem symplectic_linear_invertible {n : ℕ} {A : End n}
    (hA : ∀ v w, standardForm (A v) (A w) = standardForm v w) : A.IsInvertible := by
  have hi := symplectic_linear_injective hA
  have hs := (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem symplecticOn_fderiv_invertible {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {x : Phase n} (hx : x ∈ U) :
    (fderiv ℝ f x).IsInvertible :=
  symplectic_linear_invertible (h.2.2.2 x hx)

theorem symplecticOn_injOn {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) : InjOn f U := by
  intro x hx y hy hxy
  exact congrArg Subtype.val (h.2.2.1.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)

theorem symplecticOn_open_image {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x,hx,rfl⟩
  have hs := h.2.1.contDiffAt (h.1.mem_nhds hx)
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h hx
  have hd : HasStrictFDerivAt f (e : End n) x := by
    rw [he]
    exact hs.hasStrictFDerivAt (by simp)
  have hi := Filter.image_mem_map (m := f) (h.1.mem_nhds hx)
  rwa [hd.map_nhds_eq_of_equiv] at hi

theorem symplecticOn_inverse_smooth {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) :
    ContDiffOn ℝ ∞ (invFunOn f U) (f '' U) := by
  rintro y ⟨x,hx,rfl⟩
  apply ContDiffAt.contDiffWithinAt
  have hs := h.2.1.contDiffAt (h.1.mem_nhds hx)
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h hx
  have hd : HasFDerivAt f (e : End n) x := by
    rw [he]
    exact hs.differentiableAt (by simp) |>.hasFDerivAt
  let q := hs.toOpenPartialHomeomorph f hd (by simp)
  have hqx : x ∈ q.source := hs.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hqy : f x ∈ q.target := hs.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have hqg : q.symm (f x) = x := q.left_inv hqx
  have hqs : ContDiffAt ℝ ∞ q.symm (f x) := hs.to_localInverse hd (by simp)
  have hUevent : ∀ᶠ z in 𝓝 (f x), q.symm z ∈ U :=
    hqs.continuousAt.eventually (h.1.mem_nhds (by rw [hqg]; exact hx))
  apply hqs.congr_of_eventuallyEq
  filter_upwards [q.open_target.mem_nhds hqy, hUevent] with z hz hUz
  have hj := (symplecticOn_injOn h).leftInvOn_invFunOn hUz
  have hqz : f (q.symm z) = z := q.right_inv hz
  rwa [hqz] at hj

@[simp] theorem imageJ_at_image {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {x : Phase n} (hx : x ∈ U) :
    imageJ U f (f x) = (fderiv ℝ f x).comp
      ((standardJ n).comp (fderiv ℝ f x).inverse) := by
  unfold imageJ
  rw [(symplecticOn_injOn h).leftInvOn_invFunOn hx]

theorem imageJ_compatible {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U) :
    Compatible (imageJ U f y) := by
  obtain ⟨x,hx,rfl⟩ := hy
  rw [imageJ_at_image h hx]
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h hx
  rw [←he]
  have heω : ∀ v w, standardForm (e v) (e w) = standardForm v w := by
    intro v w
    change standardForm ((e : End n) v) ((e : End n) w) = _
    rw [he]
    exact h.2.2.2 x hx v w
  convert compatible_conjugateJ e heω using 1
  all_goals try with_reducible_and_instances rfl
  simp [conjugateJ]

theorem imageJ_smooth {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) :
    ContDiffOn ℝ ∞ (imageJ U f) (f '' U) := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  have hg := (symplecticOn_inverse_smooth h).contDiffAt
    ((symplecticOn_open_image h).mem_nhds hy)
  have hx : invFunOn f U y ∈ U := invFunOn_mem hy
  have hf := h.2.1.contDiffAt (h.1.mem_nhds hx)
  have hD : ContDiffAt ℝ ∞ (fun z => fderiv ℝ f (invFunOn f U z)) y :=
    (hf.fderiv_right (by simp)).comp y hg
  have hI := (symplecticOn_fderiv_invertible h hx).contDiffAt_map_inverse.comp y hD
  exact hD.clm_comp (contDiffAt_const.clm_comp hI)

theorem symplecticOn_inverse_fderiv {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U) :
    fderiv ℝ (invFunOn f U) y = (fderiv ℝ f (invFunOn f U y)).inverse := by
  let g := invFunOn f U
  have hx : g y ∈ U := invFunOn_mem hy
  have hg := (symplecticOn_inverse_smooth h).contDiffAt
    ((symplecticOn_open_image h).mem_nhds hy)
  have hf := h.2.1.contDiffAt (h.1.mem_nhds hx)
  have hc : f ∘ g =ᶠ[𝓝 y] id := by
    filter_upwards [(symplecticOn_open_image h).mem_nhds hy] with z hz
    exact invFunOn_eq hz
  have hcomp : (fderiv ℝ f (g y)).comp (fderiv ℝ g y) = ContinuousLinearMap.id ℝ (Phase n) := by
    rw [←fderiv_comp y (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))]
    rw [hc.fderiv_eq, fderiv_id]
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h hx
  change fderiv ℝ g y = _
  rw [←he]
  rw [←he] at hcomp
  simp only [ContinuousLinearMap.inverse_equiv]
  apply ContinuousLinearMap.ext
  intro v
  apply e.injective
  have hv := congrArg (fun A : End n => A v) hcomp
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hv

theorem complex_differentiable_of_CR {n : ℕ} {u : ℂ → Phase n} {z : ℂ}
    (hu : DifferentiableAt ℝ u z)
    (hCR : ∀ w : ℂ, fderiv ℝ u z (Complex.I * w) = standardJ n (fderiv ℝ u z w)) :
    DifferentiableAt ℂ u z := by
  let A := fderiv ℝ u z
  let L : ℂ →L[ℂ] Phase n := (ContinuousLinearMap.id ℂ ℂ).smulRight (A 1)
  have hL : L.restrictScalars ℝ = A := by
    ext w i
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_one, mul_one]
        using (Complex.re_add_im w).symm
    have hI : A Complex.I = standardJ n (A 1) := by
      simpa only [mul_one] using hCR 1
    have hAw : A w = w.re • A 1 + w.im • standardJ n (A 1) := by
      conv_lhs => rw [hw]
      simp only [map_add, map_smul, hI]
    rw [hAw]
    change w * A 1 i = _
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, standardJ_apply]
    rw [←mul_assoc, ←add_mul]
    congr 1
    exact (Complex.re_add_im w).symm
  exact (hasFDerivAt_of_restrictScalars ℝ hu.hasFDerivAt hL).differentiableAt

theorem inverse_chart_holomorphic {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {u : ℂ → Phase n} {z : ℂ}
    (hu : PseudoHolomorphicAt (imageJ U f) u z) (hz : u z ∈ f '' U) :
    DifferentiableAt ℂ (invFunOn f U ∘ u) z := by
  let g := invFunOn f U
  have hg := ((symplecticOn_inverse_smooth h).contDiffAt
    ((symplecticOn_open_image h).mem_nhds hz)).differentiableAt (by simp)
  apply complex_differentiable_of_CR (hg.comp z hu.1)
  intro w
  rw [fderiv_comp z hg hu.1]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hu.2]
  rw [symplecticOn_inverse_fderiv h hz]
  change (fderiv ℝ f (g (u z))).inverse
    ((fderiv ℝ f (g (u z))) (standardJ n
      ((fderiv ℝ f (g (u z))).inverse (fderiv ℝ u z w)))) = _
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h (invFunOn_mem hz)
  rw [←he]
  simp

end Rigidity
end
end HigherDimensionalBallPacking

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem stdDot_symm {n : ℕ} (v w : Phase n) : stdDot n v w = stdDot n w v := by
  simp only [stdDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem stdDot_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v v := by
  rw [← standardForm_J_right]
  exact standardForm_J_pos hv

theorem stdDot_nonneg {n : ℕ} (v : Phase n) : 0 ≤ stdDot n v v := by
  by_cases hv : v = 0
  · subst v
    simp
  · exact (stdDot_pos hv).le

theorem standardForm_skew {n : ℕ} (v w : Phase n) :
    standardForm v w = -standardForm w v := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem compatible_metric_symm {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) : standardForm v (J w) = standardForm w (J v) := by
  calc
    standardForm v (J w) = standardForm (J v) (J (J w)) := (hJ.2.1 v (J w)).symm
    _ = -standardForm (J v) w := by rw [hJ.1, standardForm_neg_right]
    _ = standardForm w (J v) := by rw [standardForm_skew, neg_neg]

theorem compatible_of_sq_symmetric_positive {n : ℕ} {J : End n}
    (hJsq : ∀ v, J (J v) = -v)
    (hsym : ∀ v w, standardForm v (J w) = standardForm w (J v))
    (hpos : ∀ v, v ≠ 0 → 0 < standardForm v (J v)) : Compatible J := by
  refine ⟨hJsq, ?_, hpos⟩
  intro v w
  rw [hsym, hJsq, standardForm_neg_right, standardForm_skew, neg_neg]

theorem relativeOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) :
    stdDot n (relativeOperator J v) w = stdDot n v (relativeOperator J w) := by
  rw [stdDot_symm, stdDot_relativeOperator, stdDot_relativeOperator]
  exact compatible_metric_symm hJ w v

theorem relativeOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v (relativeOperator J v) := by
  rw [stdDot_relativeOperator]
  exact hJ.2.2 v hv

theorem cayleyP_invertible {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : (cayleyP J b a).IsInvertible := by
  have hi : Injective (cayleyP J b a) := by
    apply (injective_iff_map_eq_zero (cayleyP J b a)).mpr
    intro v hv
    by_contra hne
    have hp := stdDot_pos hne
    have hA := relativeOperator_positive hJ hne
    have he : stdDot n v (cayleyP J b a v) =
        b * stdDot n v (relativeOperator J v) + a * stdDot n v v := by
      simp only [cayleyP_apply, map_add, map_smul, smul_eq_mul]
    rw [hv] at he
    simp only [map_zero] at he
    have hn := mul_nonneg hb hA.le
    have hh := mul_pos ha hp
    linarith
  have hs := (LinearMap.injective_iff_surjective (f := (cayleyP J b a).toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (cayleyP J b a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem cayleyP_commute {n : ℕ} (J : End n) (a b : ℝ) (v : Phase n) :
    cayleyP J b a (cayleyP J a b v) = cayleyP J a b (cayleyP J b a v) := by
  simp only [cayleyP_apply, map_add, map_smul]
  module

theorem cayleyP_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v : Phase n) :
    cayleyP J a b (standardJ n (cayleyP J a b v)) =
      cayleyP J b a (standardJ n (cayleyP J b a v)) := by
  simp only [cayleyP_apply, map_add, map_smul, relativeOperator_J_relativeOperator hJ]
  module

theorem cayleyP_stdDot_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v w : Phase n) :
    stdDot n (cayleyP J b a v) (cayleyP J a b w) =
      stdDot n (cayleyP J a b v) (cayleyP J b a w) := by
  simp only [cayleyP_apply, map_add, map_smul,
    add_apply, smul_apply, smul_eq_mul]
  rw [relativeOperator_selfadjoint hJ v w]
  ring

theorem cayleyP_stdDot_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n (cayleyP J b a v) (cayleyP J a b v) := by
  have he : stdDot n (cayleyP J b a v) (cayleyP J a b v) =
      a * b * (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) +
      (a ^ 2 + b ^ 2) * stdDot n v (relativeOperator J v) := by
    simp only [cayleyP_apply, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul]
    rw [relativeOperator_selfadjoint hJ v v]
    ring
  rw [he]
  have hfirst : 0 ≤ a * b *
      (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) :=
    mul_nonneg (mul_nonneg ha.le hb) (add_nonneg (stdDot_nonneg _) (stdDot_nonneg _))
  have hcoeff : 0 < a ^ 2 + b ^ 2 := by nlinarith [sq_pos_of_pos ha, sq_nonneg b]
  exact add_pos_of_nonneg_of_pos hfirst (mul_pos hcoeff (relativeOperator_positive hJ hv))

theorem cayleyOperator_on_denominator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (cayleyP J b a v) = cayleyP J a b v := by
  obtain ⟨e,he⟩ := hQ
  simp only [cayleyOperator, ←he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

theorem denominator_cayleyOperator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyP J b a (cayleyOperator J a b v) = cayleyP J a b v := by
  change cayleyP J b a (cayleyP J a b ((cayleyP J b a).inverse v)) = _
  rw [cayleyP_commute]
  obtain ⟨e,he⟩ := hQ
  simp [←he]

theorem cayleyOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v w : Phase n) :
    stdDot n (cayleyOperator J a b v) w = stdDot n v (cayleyOperator J a b w) := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  obtain ⟨y,rfl⟩ := e.surjective w
  change stdDot n (cayleyOperator J a b ((e : End n) x)) ((e : End n) y) =
    stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) y))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩,
    cayleyOperator_on_denominator ⟨e,he⟩]
  exact (cayleyP_stdDot_identity hJ a b x y).symm

theorem cayleyOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n v (cayleyOperator J a b v) := by
  obtain ⟨e,he⟩ := cayleyP_invertible hJ ha hb
  obtain ⟨x,rfl⟩ := e.surjective v
  have hx : x ≠ 0 := by simpa using hv
  change 0 < stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) x))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_stdDot_positive hJ ha hb hx

theorem cayleyOperator_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (standardJ n (cayleyOperator J a b v)) = standardJ n v := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  apply e.injective
  change (e : End n) (cayleyOperator J a b (standardJ n (cayleyOperator J a b ((e : End n) x)))) =
    (e : End n) (standardJ n ((e : End n) x))
  rw [he, denominator_cayleyOperator ⟨e,he⟩, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_J_identity hJ a b x

theorem compatible_interpolateJ {n : ℕ} {J : End n} (hJ : Compatible J)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Compatible (interpolateJ J t) := by
  have ha : 0 < 1 + t := by linarith [ht.1]
  have hb : 0 ≤ 1 - t := by linarith [ht.2]
  have hQ := cayleyP_invertible hJ ha hb
  apply compatible_of_sq_symmetric_positive
  · intro v
    change standardJ n (cayleyOperator J (1+t) (1-t)
      (standardJ n (cayleyOperator J (1+t) (1-t) v))) = -v
    rw [cayleyOperator_J_identity hJ hQ, standardJ_sq]
  · intro v w
    change standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) w)) =
      standardForm w (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right, standardForm_J_right,
      ←cayleyOperator_selfadjoint hJ hQ, stdDot_symm]
  · intro v hv
    change 0 < standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right]
    exact cayleyOperator_positive hJ ha hb hv

@[simp] theorem interpolateJ_zero {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 0 = standardJ n := by
  have hQ := cayleyP_invertible hJ (a := 1) (b := 1) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+0) (1-0) ((e : End n) x)) = standardJ n ((e : End n) x)
  simp only [add_zero, sub_zero, he, cayleyOperator_on_denominator ⟨e,he⟩]

@[simp] theorem interpolateJ_one {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 1 = J := by
  have hQ := cayleyP_invertible hJ (a := 2) (b := 0) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+1) (1-1) ((e : End n) x)) = J ((e : End n) x)
  norm_num only [he, show (1:ℝ)+1=2 by norm_num, sub_self,
    cayleyOperator_on_denominator ⟨e,he⟩]
  simp

theorem contDiffAt_interpolateJ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {J : E → End n} {t : E → ℝ} {x : E}
    (hJs : ContDiffAt ℝ ∞ J x) (hts : ContDiffAt ℝ ∞ t x)
    (hJ : Compatible (J x)) (ht : t x ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y => interpolateJ (J y) (t y)) x := by
  have hA : ContDiffAt ℝ ∞ (fun y => relativeOperator (J y)) x :=
    (contDiffAt_const.clm_comp hJs).neg
  have ha : ContDiffAt ℝ ∞ (fun y => 1 + t y) x := contDiffAt_const.add hts
  have hb : ContDiffAt ℝ ∞ (fun y => 1 - t y) x := contDiffAt_const.sub hts
  have hP : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1+t y) (1-t y)) x :=
    (ha.smul hA).add (hb.smul contDiffAt_const)
  have hQ : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1-t y) (1+t y)) x :=
    (hb.smul hA).add (ha.smul contDiffAt_const)
  have hQi := cayleyP_invertible hJ (show 0 < 1 + t x by linarith [ht.1])
    (show 0 ≤ 1 - t x by linarith [ht.2])
  have hI : ContDiffAt ℝ ∞ (fun y => (cayleyP (J y) (1-t y) (1+t y)).inverse) x :=
    ContDiffAt.comp x (g := ContinuousLinearMap.inverse)
      (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := ∞) hQi) hQ
  exact contDiffAt_const.clm_comp (hP.clm_comp hI)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Adapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology Manifold
open Set Function Filter


theorem exists_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,E) hK.isClosed hKL (n := ⊤)
  have hs : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  exact ⟨χ,χ.contMDiff.contDiff,hL.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hLU,hχ1,hχrange⟩

theorem localizeJ_compatible {n : ℕ} {V : Set (Phase n)} {J : Phase n → End n}
    {χ : Phase n → ℝ} (hJ : ∀ x ∈ V, Compatible (J x))
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (x : Phase n) :
    Compatible (localizeJ V J χ x) := by
  classical
  by_cases hx : x ∈ V
  · simpa only [localizeJ, ite_eq_left hx] using compatible_interpolateJ (hJ x hx) (hχ x)
  · simpa only [localizeJ, ite_eq_right hx] using compatible_standardJ n

theorem localizeJ_eq_standard {n : ℕ} {V : Set (Phase n)} {J : Phase n → End n}
    {χ : Phase n → ℝ} (hJ : ∀ x ∈ V, Compatible (J x)) {x : Phase n}
    (hx : χ x = 0) : localizeJ V J χ x = standardJ n := by
  classical
  by_cases hV : x ∈ V
  · simp only [localizeJ, ite_eq_left hV, hx, interpolateJ_zero (hJ x hV)]
  · simp only [localizeJ, ite_eq_right hV]

theorem localizeJ_smooth {n : ℕ} {V : Set (Phase n)} (hV : IsOpen V)
    {J : Phase n → End n} (hJs : ContDiffOn ℝ ∞ J V)
    (hJ : ∀ x ∈ V, Compatible (J x)) {χ : Phase n → ℝ}
    (hχs : ContDiff ℝ ∞ χ) (hχV : tsupport χ ⊆ V)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) : ContDiff ℝ ∞ (localizeJ V J χ) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ V
  · apply (contDiffAt_interpolateJ (hJs.contDiffAt (hV.mem_nhds hx)) hχs.contDiffAt
      (hJ x hx) (hχ x)).congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hx] with y hy
    simp only [localizeJ, ite_eq_left hy]
  · have hn : x ∉ tsupport χ := fun h => hx (hχV h)
    apply (contDiffAt_const (c := standardJ n)).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    exact localizeJ_eq_standard hJ hy

theorem extend_two_compatible {n : ℕ} {K₀ K₁ V₀ V₁ W : Set (Phase n)}
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁) (hdis : Disjoint K₀ K₁)
    (hV₀ : IsOpen V₀) (hV₁ : IsOpen V₁) (hW : IsOpen W)
    (hKV₀ : K₀ ⊆ V₀) (hKV₁ : K₁ ⊆ V₁) (hKW₀ : K₀ ⊆ W) (hKW₁ : K₁ ⊆ W)
    {J₀ J₁ : Phase n → End n} (hJ₀s : ContDiffOn ℝ ∞ J₀ V₀)
    (hJ₁s : ContDiffOn ℝ ∞ J₁ V₁) (hJ₀ : ∀ x ∈ V₀, Compatible (J₀ x))
    (hJ₁ : ∀ x ∈ V₁, Compatible (J₁ x)) :
    ∃ J : Phase n → End n, ContDiff ℝ ∞ J ∧ (∀ x, Compatible (J x)) ∧
      (∀ᶠ x in 𝓝ˢ K₀, J x = J₀ x) ∧ (∀ᶠ x in 𝓝ˢ K₁, J x = J₁ x) ∧
      HasCompactSupport (fun x => J x - standardJ n) ∧
      tsupport (fun x => J x - standardJ n) ⊆ W := by
  obtain ⟨O₀,O₁,hO₀,hO₁,hKO₀,hKO₁,hOdis⟩ :=
    normal_separation hK₀.isClosed hK₁.isClosed hdis
  let A₀ := O₀ ∩ V₀ ∩ W
  let A₁ := O₁ ∩ V₁ ∩ W
  have hA₀ : IsOpen A₀ := (hO₀.inter hV₀).inter hW
  have hA₁ : IsOpen A₁ := (hO₁.inter hV₁).inter hW
  have hKA₀ : K₀ ⊆ A₀ := fun x hx => ⟨⟨hKO₀ hx,hKV₀ hx⟩,hKW₀ hx⟩
  have hKA₁ : K₁ ⊆ A₁ := fun x hx => ⟨⟨hKO₁ hx,hKV₁ hx⟩,hKW₁ hx⟩
  obtain ⟨χ₀,hχ₀s,hχ₀c,hχ₀A,hχ₀one,hχ₀I⟩ := exists_smooth_cutoff hK₀ hA₀ hKA₀
  obtain ⟨χ₁,hχ₁s,hχ₁c,hχ₁A,hχ₁one,hχ₁I⟩ := exists_smooth_cutoff hK₁ hA₁ hKA₁
  have hχdis : Disjoint (tsupport χ₀) (tsupport χ₁) :=
    hOdis.mono (fun _ hx => (hχ₀A hx).1.1) (fun _ hx => (hχ₁A hx).1.1)
  have hA₀V : A₀ ⊆ V₀ := fun _ hx => hx.1.2
  have hA₁V : A₁ ⊆ V₁ := fun _ hx => hx.1.2
  have hJ₀A : ∀ x ∈ A₀, Compatible (J₀ x) := fun _ hx => hJ₀ _ (hA₀V hx)
  have hJ₁A : ∀ x ∈ A₁, Compatible (J₁ x) := fun _ hx => hJ₁ _ (hA₁V hx)
  let L₀ := localizeJ A₀ J₀ χ₀
  let L₁ := localizeJ A₁ J₁ χ₁
  have hL₀s : ContDiff ℝ ∞ L₀ :=
    localizeJ_smooth hA₀ (hJ₀s.mono hA₀V) hJ₀A hχ₀s hχ₀A hχ₀I
  have hL₁s : ContDiff ℝ ∞ L₁ :=
    localizeJ_smooth hA₁ (hJ₁s.mono hA₁V) hJ₁A hχ₁s hχ₁A hχ₁I
  have hL₀ (x) : Compatible (L₀ x) := localizeJ_compatible hJ₀A hχ₀I x
  have hL₁ (x) : Compatible (L₁ x) := localizeJ_compatible hJ₁A hχ₁I x
  have hL₀out (x) (hx : x ∉ tsupport χ₀) : L₀ x = standardJ n :=
    localizeJ_eq_standard hJ₀A (image_eq_zero_of_notMem_tsupport hx)
  have hL₁out (x) (hx : x ∉ tsupport χ₁) : L₁ x = standardJ n :=
    localizeJ_eq_standard hJ₁A (image_eq_zero_of_notMem_tsupport hx)
  let J := fun x => L₀ x + L₁ x - standardJ n
  have hJs : ContDiff ℝ ∞ J := (hL₀s.add hL₁s).sub contDiff_const
  have hJ (x) : Compatible (J x) := by
    by_cases hx : x ∈ tsupport χ₀
    · have hx₁ : x ∉ tsupport χ₁ := fun hh => disjoint_left.mp hχdis hx hh
      simpa only [J,hL₁out x hx₁,add_sub_cancel_right] using hL₀ x
    · simpa only [J,hL₀out x hx,add_sub_cancel_left] using hL₁ x
  have hzero (x) (hx : x ∉ tsupport χ₀ ∪ tsupport χ₁) : J x - standardJ n = 0 := by
    have hx₀ : x ∉ tsupport χ₀ := fun hh => hx (Or.inl hh)
    have hx₁ : x ∉ tsupport χ₁ := fun hh => hx (Or.inr hh)
    simp only [J,hL₀out x hx₀,hL₁out x hx₁,add_sub_cancel_right,sub_self]
  have hsupport : tsupport (fun x => J x - standardJ n) ⊆ tsupport χ₀ ∪ tsupport χ₁ := by
    apply closure_minimal _ ((isClosed_tsupport χ₀).union (isClosed_tsupport χ₁))
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨J,hJs,hJ,?_,?_,(hχ₀c.union hχ₁c).of_isClosed_subset (isClosed_tsupport _) hsupport,
    fun x hx => ?_⟩
  · filter_upwards [hχ₀one] with x hx
    have hx₀ : x ∈ tsupport χ₀ := subset_tsupport χ₀ (by simp [mem_support,hx])
    have hx₁ : x ∉ tsupport χ₁ := fun hh => disjoint_left.mp hχdis hx₀ hh
    have hL : L₀ x = J₀ x := by
      classical
      simp only [L₀,localizeJ,ite_eq_left (hχ₀A hx₀),hx,
        interpolateJ_one (hJ₀A x (hχ₀A hx₀))]
    simp only [J,hL,hL₁out x hx₁,add_sub_cancel_right]
  · filter_upwards [hχ₁one] with x hx
    have hx₁ : x ∈ tsupport χ₁ := subset_tsupport χ₁ (by simp [mem_support,hx])
    have hx₀ : x ∉ tsupport χ₀ := fun hh => disjoint_left.mp hχdis hh hx₁
    have hL : L₁ x = J₁ x := by
      classical
      simp only [L₁,localizeJ,ite_eq_left (hχ₁A hx₁),hx,
        interpolateJ_one (hJ₁A x (hχ₁A hx₁))]
    simp only [J,hL₀out x hx₀,hL,add_sub_cancel_left]
  · rcases hsupport hx with h | h
    · exact (hχ₀A h).2
    · exact (hχ₁A h).2

theorem closedBall_isClosed (n : ℕ) (R : ℝ) : IsClosed (closedBall n R) :=
  isClosed_le (continuous_capacity n) continuous_const

theorem openBall_isOpen (n : ℕ) (R : ℝ) : IsOpen (openBall n R) :=
  isOpen_lt (continuous_capacity n) continuous_const

theorem closedBall_isCompact (n : ℕ) (R : ℝ) : IsCompact (closedBall n R) := by
  apply (isCompact_closedBall (0 : Phase n) (max R 0 + 1)).of_isClosed_subset
    (closedBall_isClosed n R)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ max R 0 + 1)).mpr
  intro j
  have hj : Complex.normSq (z j) ≤ ∑ k, Complex.normSq (z k) :=
    Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (z k)) (Finset.mem_univ j)
  have hj' := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
  have hq : 0 ≤ Complex.normSq (z j) := Complex.normSq_nonneg (z j)
  have hs : (∑ k, Complex.normSq (z k)) * Real.pi ≤ R := by
    simpa [closedBall, capacity, mul_comm] using hz
  have hb : Complex.normSq (z j) ≤ max R 0 := by
    nlinarith [Real.pi_gt_three, le_max_left R 0]
  rw [Complex.normSq_eq_norm_sq] at hb
  have hm := le_max_right R 0
  nlinarith [sq_nonneg (‖z j‖ - 1)]

theorem adapt_two_ball_images {n : ℕ} {a b R : ℝ}
    {U₀ U₁ : Set (Phase n)} {f₀ f₁ : Phase n → Phase n}
    (hsub₀ : closedBall n a ⊆ U₀) (hsub₁ : closedBall n b ⊆ U₁)
    (hf₀ : SymplecticOn U₀ f₀) (hf₁ : SymplecticOn U₁ f₁)
    (ht₀ : MapsTo f₀ (closedBall n a) (openBall n R))
    (ht₁ : MapsTo f₁ (closedBall n b) (openBall n R))
    (hdis : Disjoint (f₀ '' closedBall n a) (f₁ '' closedBall n b)) :
    ∃ J : Phase n → End n, ContDiff ℝ ∞ J ∧ (∀ x, Compatible (J x)) ∧
      (∀ᶠ x in 𝓝ˢ (f₀ '' closedBall n a), J x = imageJ U₀ f₀ x) ∧
      (∀ᶠ x in 𝓝ˢ (f₁ '' closedBall n b), J x = imageJ U₁ f₁ x) ∧
      HasCompactSupport (fun x => J x - standardJ n) ∧
      tsupport (fun x => J x - standardJ n) ⊆ openBall n R := by
  exact extend_two_compatible
    ((closedBall_isCompact n a).image_of_continuousOn (hf₀.2.1.continuousOn.mono hsub₀))
    ((closedBall_isCompact n b).image_of_continuousOn (hf₁.2.1.continuousOn.mono hsub₁))
    hdis (symplecticOn_open_image hf₀) (symplecticOn_open_image hf₁) (openBall_isOpen n R)
    (image_mono hsub₀) (image_mono hsub₁) (image_subset_iff.mpr ht₀) (image_subset_iff.mpr ht₁)
    (imageJ_smooth hf₀) (imageJ_smooth hf₁)
    (fun _ hx => imageJ_compatible hf₀ hx) (fun _ hx => imageJ_compatible hf₁ hx)

theorem packing_two_has_adapted_structure {n : ℕ} {a b R : ℝ}
    (hp : HasPacking n 2 R ![a,b]) :
    ∃ (U : Fin 2 → Set (Phase n)) (f : Fin 2 → Phase n → Phase n)
      (J : Phase n → End n),
      (∀ i, closedBall n (![a,b] i) ⊆ U i ∧ SymplecticOn (U i) (f i) ∧
        MapsTo (f i) (closedBall n (![a,b] i)) (openBall n R)) ∧
      (∀ i j, i ≠ j → Disjoint (f i '' closedBall n (![a,b] i))
        (f j '' closedBall n (![a,b] j))) ∧
      ContDiff ℝ ∞ J ∧ (∀ x, Compatible (J x)) ∧
      (∀ i, ∀ᶠ x in 𝓝ˢ (f i '' closedBall n (![a,b] i)), J x = imageJ (U i) (f i) x) ∧
      HasCompactSupport (fun x => J x - standardJ n) ∧
      tsupport (fun x => J x - standardJ n) ⊆ openBall n R := by
  obtain ⟨U,f,hf,hd⟩ := hp
  obtain ⟨J,hJs,hJ,hJ₀,hJ₁,hJc,hJsupp⟩ := adapt_two_ball_images
    (hf 0).1 (hf 1).1 (hf 0).2.1 (hf 1).2.1 (hf 0).2.2 (hf 1).2.2
    (hd 0 1 (by decide))
  refine ⟨U,f,J,hf,hd,hJs,hJ,?_,hJc,hJsupp⟩
  intro i
  fin_cases i
  · exact hJ₀
  · exact hJ₁


end

section
open scoped ContDiff Topology
open Set Function Filter

@[simp] theorem lineHomotopy_zero {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 0 x = standardJ n :=
  interpolateJ_zero (hJ x)

@[simp] theorem lineHomotopy_one {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 1 x = J x :=
  interpolateJ_one (hJ x)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem radialSwitch_smooth (σ τ : ℝ) : ContDiff ℝ ∞ (radialSwitch σ τ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem radialSwitch_nonneg (σ τ t : ℝ) : 0 ≤ radialSwitch σ τ t :=
  Real.smoothTransition.nonneg _

theorem radialSwitch_le_one (σ τ t : ℝ) : radialSwitch σ τ t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem radialSwitch_zero {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialSwitch σ τ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hστ).le

theorem radialSwitch_one {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    radialSwitch σ τ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr hστ)).mpr
  linarith

theorem radialOffset_hasDerivAt (σ τ t : ℝ) :
    HasDerivAt (radialOffset σ τ) (radialSwitch σ τ t) t := by
  have hc := (radialSwitch_smooth σ τ).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem radialOffset_smooth (σ τ : ℝ) : ContDiff ℝ ∞ (radialOffset σ τ) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (radialOffset_hasDerivAt σ τ t).differentiableAt,?_⟩
  have he : deriv (radialOffset σ τ) = radialSwitch σ τ :=
    funext (fun t => (radialOffset_hasDerivAt σ τ t).deriv)
  rw [he]
  exact radialSwitch_smooth σ τ

theorem radialOffset_zero {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialOffset σ τ t = 0 := by
  unfold radialOffset
  calc
    (∫ s in σ..t, radialSwitch σ τ s) = ∫ s in σ..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact radialSwitch_zero hστ ((uIcc_of_ge ht ▸ hs).2)
    _ = 0 := by simp

theorem radialOffset_nonneg {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    0 ≤ radialOffset σ τ t := by
  by_cases ht : t ≤ σ
  · rw [radialOffset_zero hστ ht]
  · exact intervalIntegral.integral_nonneg (le_of_not_ge ht)
      (fun s _ => radialSwitch_nonneg σ τ s)

theorem radialShift_pos {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1) :
    0 < radialShift σ τ := by
  have hn := radialOffset_nonneg hστ τ
  unfold radialShift
  linarith

theorem radialOffset_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    1 + radialOffset σ τ t = t + radialShift σ τ := by
  have hc := (radialSwitch_smooth σ τ).continuous
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) σ τ) (hc.intervalIntegrable τ t)
  have hI : (∫ s in τ..t, radialSwitch σ τ s) = t-τ := by
    calc
      _ = ∫ s in τ..t, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact radialSwitch_one hστ ((uIcc_of_le ht ▸ hs).1)
      _ = t-τ := by simp
  rw [hI] at he
  change radialOffset σ τ τ + (t-τ) = radialOffset σ τ t at he
  unfold radialShift
  linarith

theorem radialCoefficient_smooth {σ τ : ℝ} (hστ : σ < τ) :
    ContDiff ℝ ∞ (radialCoefficient σ τ) :=
  (contDiff_const.add (radialOffset_smooth σ τ)).inv
    (fun t => ne_of_gt (by linarith [radialOffset_nonneg hστ t]))

theorem radialCoefficient_hasDerivAt {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    HasDerivAt (radialCoefficient σ τ)
      (-radialSwitch σ τ t / (1 + radialOffset σ τ t)^2) t := by
  have hd : HasDerivAt (fun x : ℝ => 1 + radialOffset σ τ x) (radialSwitch σ τ t) t :=
    (radialOffset_hasDerivAt σ τ t).const_add 1
  exact hd.inv (ne_of_gt (by linarith [radialOffset_nonneg hστ t]))

theorem radialCoefficient_one {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialCoefficient σ τ t = 1 := by
  simp only [radialCoefficient,radialOffset_zero hστ ht,add_zero,inv_one]

theorem radialCoefficient_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    radialCoefficient σ τ t = (t + radialShift σ τ)⁻¹ := by
  rw [radialCoefficient,radialOffset_after hστ ht]

theorem radialMoment_derivative_pos {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1) (t : ℝ) :
    0 < (1 + radialOffset σ τ t - t * radialSwitch σ τ t) /
      (1 + radialOffset σ τ t)^2 := by
  apply div_pos _ (sq_pos_of_pos (by linarith [radialOffset_nonneg hστ t]))
  by_cases htσ : t ≤ σ
  · rw [radialOffset_zero hστ htσ,radialSwitch_zero hστ htσ]
    norm_num
  by_cases htτ : t ≤ τ
  · have ht1 : t < 1 := htτ.trans_lt hτ
    have hs0 := radialSwitch_nonneg σ τ t
    have hs1 := radialSwitch_le_one σ τ t
    have hφ := radialOffset_nonneg hστ t
    have hm : t * radialSwitch σ τ t < 1 := by
      by_cases ht0 : 0 ≤ t
      · exact (mul_le_mul_of_nonneg_left hs1 ht0).trans_lt (by simpa using ht1)
      · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht0) hs0).trans_lt zero_lt_one
    linarith
  · have htτ' : τ ≤ t := le_of_not_ge htτ
    rw [radialOffset_after hστ htτ',radialSwitch_one hστ htτ',mul_one]
    linarith [radialShift_pos hστ hτ]

theorem radialMoment_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    radialMoment σ τ t = t / (t + radialShift σ τ) := by
  rw [radialMoment, radialCoefficient_after hστ ht,div_eq_mul_inv]

theorem radialMoment_tendsto_one {σ τ : ℝ} (hστ : σ < τ) :
    Tendsto (radialMoment σ τ) atTop (𝓝 1) := by
  have ht : Tendsto (fun t : ℝ => t + radialShift σ τ) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_id
  have hc : Tendsto (fun t : ℝ => radialShift σ τ / (t + radialShift σ τ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
  have hl : Tendsto (fun t : ℝ => 1 - radialShift σ τ / (t + radialShift σ τ))
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hc
  apply hl.congr'
  filter_upwards [eventually_ge_atTop τ, eventually_gt_atTop (-radialShift σ τ)] with t htτ ht0
  rw [radialMoment_after hστ htτ]
  have hn : t + radialShift σ τ ≠ 0 := by linarith
  field_simp
  ring



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_RadialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem stdDot_standardForm_sq_le {n : ℕ} (z v : Phase n) :
    (stdDot n z v)^2 + (standardForm z v)^2 ≤ stdDot n z z * stdDot n v v := by
  let z' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 z
  let v' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  have hr : (inner ℂ z' v').re = stdDot n z v := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.re_sum, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add, stdDot_apply]
    apply Finset.sum_congr rfl
    intro i _
    change (v i).re * (z i).re + (v i).im * (z i).im = _
    ring
  have hi : (inner ℂ z' v').im = standardForm z v := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.im_sum, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, standardForm]
    apply Finset.sum_congr rfl
    intro i _
    change (v i).re * (-(z i).im) + (v i).im * (z i).re = _
    ring
  have hz : ‖z'‖^2 = stdDot n z z := by
    simp only [EuclideanSpace.norm_sq_eq, stdDot_apply, ←Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    rfl
  have hv : ‖v'‖^2 = stdDot n v v := by
    simp only [EuclideanSpace.norm_sq_eq, stdDot_apply, ←Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    rfl
  have hh := (sq_le_sq₀ (norm_nonneg (inner ℂ z' v'))
    (mul_nonneg (norm_nonneg z') (norm_nonneg v'))).mpr (norm_inner_le_norm z' v')
  rw [←Complex.normSq_eq_norm_sq, Complex.normSq_apply, hr, hi, mul_pow, hz, hv] at hh
  nlinarith only [hh]

theorem radialSlope_nonpos (σ τ t : ℝ) : radialSlope σ τ t ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (radialSwitch_nonneg σ τ t)) (sq_nonneg _)

theorem radialSlope_zero {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialSlope σ τ t = 0 := by simp [radialSlope, radialSwitch_zero hστ ht]

theorem radialMoment_derivative_eq {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    radialCoefficient σ τ t + t * radialSlope σ τ t =
      (1 + radialOffset σ τ t - t * radialSwitch σ τ t) / (1 + radialOffset σ τ t)^2 := by
  have hn : 1 + radialOffset σ τ t ≠ 0 :=
    ne_of_gt (by linarith [radialOffset_nonneg hστ t])
  unfold radialCoefficient radialSlope
  field_simp
  ring

theorem radialForm_standard {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) {x : Phase n}
    (hx : capacity x ≤ σ) (v w : Phase n) :
    radialForm σ τ x v w = standardForm v w := by
  simp only [radialForm, radialCoefficient_one hστ hx,radialSlope_zero hστ hx,
    one_mul,mul_zero,zero_mul,add_zero]

theorem radialForm_J_pos {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1)
    (x : Phase n) {v : Phase n} (hv : v ≠ 0) :
    0 < radialForm σ τ x v (standardJ n v) := by
  have hcs := stdDot_standardForm_sq_le x v
  have hs : Real.pi * radialSlope σ τ (capacity x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (radialSlope_nonpos _ _ _)
  have hm := mul_le_mul_of_nonpos_left hcs hs
  have hp := mul_pos (radialMoment_derivative_pos hστ hτ (capacity x)) (stdDot_pos hv)
  rw [←radialMoment_derivative_eq hστ] at hp
  simp only [radialForm, standardForm_J_right, stdDot_J_right]
  rw [capacity_eq_stdDot] at hp hm ⊢
  nlinarith only [hm,hp]

theorem radialForm_adapted_pos {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1)
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (houtside : ∀ x, σ < capacity x → J x = standardJ n) (x : Phase n)
    {v : Phase n} (hv : v ≠ 0) : 0 < radialForm σ τ x v (J x v) := by
  by_cases hx : capacity x ≤ σ
  · rw [radialForm_standard hστ hx]
    exact (hJ x).2.2 v hv
  · rw [houtside x (lt_of_not_ge hx)]
    exact radialForm_J_pos hστ hτ x hv

theorem capacity_smooth (n : ℕ) : ContDiff ℝ ∞ (@capacity n) := by
  have hd : ContDiff ℝ ∞ (fun x : Phase n => stdDot n x x) :=
    ((stdDot n).contDiff.comp contDiff_id).clm_apply contDiff_id
  have he : (@capacity n) = fun y => Real.pi * stdDot n y y := funext capacity_eq_stdDot
  rw [he]
  exact contDiff_const.mul hd

theorem capacity_hasFDerivAt {n : ℕ} (x : Phase n) :
    HasFDerivAt capacity ((2 * Real.pi) • stdDot n x) x := by
  have hd := ((stdDot n).hasFDerivAt).clm_apply (hasFDerivAt_id x)
  have hh := hd.const_mul Real.pi
  have he : Real.pi • ((stdDot n x).comp (ContinuousLinearMap.id ℝ (Phase n)) +
      (stdDot n).flip x) = (2 * Real.pi) • stdDot n x := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [stdDot_symm v x]
    ring
  simp only [id_eq] at hh
  rw [he] at hh
  have hefunc : (@capacity n) = fun y => Real.pi * stdDot n y y := funext capacity_eq_stdDot
  rw [hefunc]
  exact hh

theorem radialPrimitiveCLM_smooth {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) :
    ContDiff ℝ ∞ (@radialPrimitiveCLM n σ τ) :=
  (((radialCoefficient_smooth hστ).comp (capacity_smooth n)).div_const 2).smul
    (stdOmega n).contDiff

theorem radialPrimitiveCLM_derivative {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    (x v w : Phase n) :
    fderiv ℝ (radialPrimitiveCLM σ τ) x v w =
      (radialCoefficient σ τ (capacity x) / 2) * standardForm v w +
      Real.pi * radialSlope σ τ (capacity x) * stdDot n x v * standardForm x w := by
  have hg : HasFDerivAt (fun y : Phase n => radialCoefficient σ τ (capacity y) / 2)
      ((radialSlope σ τ (capacity x) / 2) • ((2 * Real.pi) • stdDot n x)) x := by
    have hc := ((radialCoefficient_hasDerivAt hστ (capacity x)).div_const 2).comp_hasFDerivAt x
      (capacity_hasFDerivAt x)
    exact hc
  have hd := hg.smul (stdOmega n).hasFDerivAt
  change HasFDerivAt (radialPrimitiveCLM σ τ) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, stdOmega_apply]
  ring

theorem radialPrimitive_smooth {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) :
    ContDiff ℝ ∞ (@radialPrimitive n σ τ) := by
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Phase n) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp (radialPrimitiveCLM_smooth hστ)

theorem radialForm_extDeriv {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (x v w : Phase n) :
    extDeriv (radialPrimitive σ τ) x ![v,w] = radialForm σ τ x v w := by
  rw [extDeriv_apply ((radialPrimitive_smooth hστ).differentiable (by simp) x)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => radialPrimitiveCLM σ τ y w) x v -
    fderiv ℝ (fun y => radialPrimitiveCLM σ τ y v) x w = _
  have he (a b : Phase n) :
      fderiv ℝ (fun y => radialPrimitiveCLM σ τ y a) x b =
        fderiv ℝ (radialPrimitiveCLM σ τ) x b a := by
    rw [fderiv_clm_apply ((radialPrimitiveCLM_smooth hστ).differentiable (by simp) x)
      (differentiableAt_const a)]
    simp
  rw [he w v,he v w]
  rw [radialPrimitiveCLM_derivative hστ, radialPrimitiveCLM_derivative hστ,
    standardForm_skew w v]
  unfold radialForm
  ring

theorem linear_asymptotic_norm_tendsto {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hv : v ≠ 0) (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    Tendsto (fun z => ‖u z‖) (cocompact ℂ) atTop := by
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖v‖ / 2 < ‖z⁻¹ • u z‖ :=
    (tendsto_order.mp hlim.norm).1 _ (by linarith)
  have hb : (fun z : ℂ => (‖v‖ / 2) * ‖z‖) ≤ᶠ[cocompact ℂ] fun z => ‖u z‖ := by
    filter_upwards [hev,(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hz0
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz0)
    rw [norm_smul,norm_inv,inv_mul_eq_div] at hz
    exact ((lt_div_iff₀ hn).mp hz).le
  exact tendsto_atTop_mono' _ hb
    (Tendsto.const_mul_atTop (by linarith : 0 < ‖v‖ / 2) tendsto_norm_cocompact_atTop)

theorem AffineLineCurve.tendsto_cocompact {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) :
    Tendsto u (cocompact ℂ) (cocompact (Phase n)) := by
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  rw [←Metric.cobounded_eq_cocompact (α := Phase n),←tendsto_norm_atTop_iff_cobounded]
  exact linear_asymptotic_norm_tendsto hv hlim

theorem AffineLineCurve.isProperMap {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) : IsProperMap u :=
  isProperMap_iff_tendsto_cocompact.mpr ⟨hu.1.continuous,hu.tendsto_cocompact⟩

theorem AffineLineCurve.holomorphic_at_infinity {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n)) :
    ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z := by
  filter_upwards [hu.tendsto_cocompact.eventually hJc.compl_mem_cocompact] with z hz
  have hJ : J (u z) = standardJ n :=
    sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => J x - standardJ n) hz)
  apply complex_differentiable_of_CR (hu.2.1 z).1
  intro w
  rw [(hu.2.1 z).2,hJ]

theorem infinityGerm_eventuallyEq {n : ℕ} (u : ℂ → Phase n) (v : Phase n)
    {w : ℂ} (hw : w ≠ 0) :
    infinityGerm u v =ᶠ[𝓝 w] fun z => z • u z⁻¹ := by
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hw] with z hz
  exact ite_eq_right hz

theorem infinityGerm_analyticAt {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z)
    (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    AnalyticAt ℂ (infinityGerm u v) 0 := by
  have hi : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  have ht : Tendsto (fun w : ℂ => w • u w⁻¹) (𝓝[≠] 0) (𝓝 v) := by
    simpa only [Function.comp_def,inv_inv] using hlim.comp hi
  have he : infinityGerm u v = Function.update (fun w : ℂ => w • u w⁻¹) 0 v := by
    classical
    funext w
    by_cases hw : w = 0
    · subst w; simp [infinityGerm]
    · simp [infinityGerm,hw]
  have hc : ContinuousAt (infinityGerm u v) 0 := by
    classical
    rw [he,continuousAt_update_same]
    exact ht
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  filter_upwards [hi.eventually hholo,self_mem_nhdsWithin] with w hw hw0
  have hn : w ≠ 0 := hw0
  have hd : DifferentiableAt ℂ (fun z : ℂ => z • u z⁻¹) w :=
    differentiableAt_id.smul (hw.comp w (differentiableAt_id.inv hn))
  exact hd.congr_of_eventuallyEq (infinityGerm_eventuallyEq u v hn)

theorem AffineLineCurve.analytic_at_infinity {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n)) :
    ∃ v : Phase n, v ≠ 0 ∧ AnalyticAt ℂ (infinityGerm u v) 0 ∧
      infinityGerm u v 0 = v := by
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  exact ⟨v,hv,infinityGerm_analyticAt (hu.holomorphic_at_infinity hJc) hlim,by simp [infinityGerm]⟩

end HigherDimensionalBallPacking.Rigidity

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem HasCompactSupport.comp_radiusSq {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z : Plane => g (radiusSq z)) := by
  obtain ⟨B,hB,hbound⟩ := hg.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro ((isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))).prod (isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))))
  intro z hz
  by_contra hg0
  have hb := hbound (radiusSq z) (subset_tsupport g hg0)
  have hq : 0 ≤ radiusSq z := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hq] at hb
  apply hz
  dsimp only [radiusSq] at hb
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]

theorem HasCompactSupport.comp_square {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun x : ℝ => g (x^2)) := by
  simpa only [radiusSq,zero_pow (by decide : (2:ℕ)≠0),add_zero] using
    HasCompactSupport.left_slice (HasCompactSupport.comp_radiusSq hg) 0

theorem integral_radial_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : (∫ z : Plane,2*deriv g (radiusSq z))= -2*Real.pi*g 0 := by
  let h : ℝ → ℝ := fun r => g (r^2)
  have hh : ContDiff ℝ ∞ h := hg.comp (contDiff_id.pow 2)
  have hhC : HasCompactSupport h := HasCompactSupport.comp_square hc
  have hd (r : ℝ) : deriv h r=2*r*deriv g (r^2) := by
    have H := (hg.differentiable (by simp) (r^2)).hasDerivAt.comp r ((hasDerivAt_id r).pow 2)
    change HasDerivAt h _ r at H
    rw [H.deriv]
    simp only [Nat.cast_ofNat,mul_one,id_eq]
    norm_num
    ring
  rw [← integral_comp_polarCoord_symm]
  have he : (fun p : Plane => p.1 • (2*deriv g (radiusSq (polarCoord.symm p))))=
      (fun p : Plane => deriv h p.1 * (1 : ℝ)) := by
    funext p
    rw [radiusSq_polar,hd]
    simp only [smul_eq_mul]
    ring
  rw [he,polarCoord_target,Measure.volume_eq_prod,setIntegral_prod_mul (deriv h) (fun _ : ℝ => (1 : ℝ)),
    HasCompactSupport.integral_Ioi_deriv_eq (hh.of_le (by simp)) hhC]
  simp only [h,zero_pow (by decide : (2:ℕ)≠0),integral_const,smul_eq_mul,
    Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0≤Real.pi-(-Real.pi))]
  ring

theorem radiusSq_hasFDerivAt (z : Plane) :
    HasFDerivAt radiusSq ((2:ℝ) • planarDot z) z := by
  have H := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2).add
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2)
  change HasFDerivAt radiusSq _ z at H
  apply H.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change (2 • z.1^(2-1))*v.1+(2 • z.2^(2-1))*v.2=2*(z.1*v.1+z.2*v.2)
  norm_num
  ring

theorem angularOneForm_contDiffAt {z : Plane} (hz : radiusSq z≠0) :
    ContDiffAt ℝ ∞ angularOneForm z :=
  (radiusSq_smooth.contDiffAt.inv hz).smul planarArea.contDiff.contDiffAt

theorem radialArea_curl {f : ℝ → ℝ} {point : Plane}
    (hf : DifferentiableAt ℝ f (radiusSq point)) :
    planarCurl (fun p : Plane => f (radiusSq p) • planarArea p) point=
      2*(f (radiusSq point)+radiusSq point*deriv f (radiusSq point)) := by
  have H := (hf.hasDerivAt.comp_hasFDerivAt point
    (radiusSq_hasFDerivAt point)).smul planarArea.hasFDerivAt
  change HasFDerivAt (fun p : Plane => f (radiusSq p) • planarArea p) _ point at H
  unfold planarCurl
  rw [H.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,planarArea_apply,planarDot_apply,
    Function.comp_apply]
  dsimp only [radiusSq]
  ring

theorem cutoffAngular_curl {g : ℝ → ℝ} {point : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq point)) (hz : radiusSq point≠0) :
    planarCurl (fun p : Plane => g (radiusSq p) • angularOneForm p) point=
      2*deriv g (radiusSq point) := by
  have hd := hg.hasDerivAt.div (hasDerivAt_id (radiusSq point)) hz
  change HasDerivAt (fun t => g t / t) _ (radiusSq point) at hd
  have he : (fun p : Plane => g (radiusSq p) • angularOneForm p)=
      fun p => (g (radiusSq p)/radiusSq p) • planarArea p := by
    funext p
    simp only [angularOneForm,smul_smul,div_eq_mul_inv]
  rw [he,radialArea_curl hd.differentiableAt,hd.deriv]
  simp only [id_eq]
  field_simp
  ring

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_PlanarResidueCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymplecticBallPacking.Hamiltonian
open Set Function MeasureTheory Filter
open scoped ContDiff Topology

theorem planarCurl_contDiff {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (planarCurl β) :=
  (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const).sub
    (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const)

theorem planarCurl_compact {β : Plane → Plane →L[ℝ] ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (planarCurl β) := by
  exact ((hβ.fderiv_apply (𝕜 := ℝ) (1,0)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (0,1)) rfl).sub
    ((hβ.fderiv_apply (𝕜 := ℝ) (0,1)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (1,0)) rfl)

theorem planarCurl_spatial_smul {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {z : Plane}
    (hf : DifferentiableAt ℝ f z) (hβ : DifferentiableAt ℝ β z) :
    planarCurl (fun y => f y • β y) z=cutoffWedge f β z+f z*planarCurl β z := by
  unfold planarCurl cutoffWedge
  have H := hf.hasFDerivAt.smul hβ.hasFDerivAt
  change HasFDerivAt (fun y => f y • β y) _ z at H
  rw [H.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  ring

theorem integral_cutoffWedge {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    (∫ z,cutoffWedge f β z)= -(∫ z,f z*planarCurl β z) := by
  have hp : ContDiff ℝ ∞ (fun z => f z • β z) := hf.smul hβ
  have hpc : HasCompactSupport (fun z => f z • β z) := hc.smul_right
  have hci : Integrable (planarCurl (fun z => f z • β z)) := (planarCurl_contDiff hp).continuous.integrable_of_hasCompactSupport (planarCurl_compact hpc)
  have hgi : Integrable (fun z => f z*planarCurl β z) := (hf.mul (planarCurl_contDiff hβ)).continuous.integrable_of_hasCompactSupport hc.mul_right
  have he : cutoffWedge f β=(fun z => planarCurl (fun y => f y • β y) z-f z*planarCurl β z) := by
    funext z
    rw [planarCurl_spatial_smul (hf.differentiable (by simp) z) (hβ.differentiable (by simp) z)]
    ring
  rw [he,integral_sub hci hgi,show (∫ z,planarCurl (fun y => f y • β y) z)=0 from compact_planar_stokes hp hpc,zero_sub]

theorem cutoffWedge_integrable {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    Integrable (cutoffWedge f β) := by
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) := (hf.fderiv_right (by simp)).clm_apply (contDiff_const (c := ((1:ℝ),(0:ℝ))))
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) := (hf.fderiv_right (by simp)).clm_apply (contDiff_const (c := ((0:ℝ),(1:ℝ))))
  exact ((h1.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (1,0)).mul_right).sub
    ((h2.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (0,1)).mul_right)

theorem radiusSq_pos {z : Plane} (hz : z≠0) : 0 < radiusSq z := by
  have hn := radiusSq_nonneg z
  by_contra hh
  have he : radiusSq z=0 := le_antisymm (le_of_not_gt hh) hn
  apply hz
  apply Prod.ext <;> change _=0 <;> dsimp only [radiusSq] at he <;>
    nlinarith [sq_nonneg z.1,sq_nonneg z.2]

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CurveArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

theorem realCurve_smooth {n : ℕ} {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (realCurve u) := hu.comp Complex.equivRealProdCLM.symm.contDiff

theorem realCurve_fderiv {n : ℕ} {u : ℂ → Phase n} {z : Plane}
    (hu : DifferentiableAt ℝ u (Complex.equivRealProdCLM.symm z)) (v : Plane) :
    fderiv ℝ (realCurve u) z v =
      fderiv ℝ u (Complex.equivRealProdCLM.symm z) (Complex.equivRealProdCLM.symm v) := by
  rw [realCurve, fderiv_comp z hu Complex.equivRealProdCLM.symm.differentiableAt]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv]

theorem realCurve_CR {n : ℕ} {J : Phase n → End n} {u : ℂ → Phase n} {z : Plane}
    (hu : PseudoHolomorphicAt J u (Complex.equivRealProdCLM.symm z)) :
    fderiv ℝ (realCurve u) z (0,1) =
      J (realCurve u z) (fderiv ℝ (realCurve u) z (1,0)) := by
  rw [realCurve_fderiv hu.1,realCurve_fderiv hu.1]
  simpa only [Complex.equivRealProdCLM_symm_apply, Complex.ofReal_zero, Complex.ofReal_one,
    zero_mul,one_mul,add_zero,zero_add,mul_one,realCurve,Function.comp_def] using hu.2 1


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem blowupMoment_smooth (σ τ : ℝ) : ContDiff ℝ ∞ (blowupMoment σ τ) :=
  contDiff_const.add (radialOffset_smooth σ τ)

theorem blowupMoment_hasDerivAt (σ τ t : ℝ) :
    HasDerivAt (blowupMoment σ τ) (radialSwitch σ τ t) t :=
  (radialOffset_hasDerivAt σ τ t).const_add _

theorem blowupMoment_before {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    blowupMoment σ τ t = blowupSize σ τ := by
  rw [blowupMoment,radialOffset_zero hστ ht,add_zero]

theorem blowupMoment_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    blowupMoment σ τ t = t := by
  have hh := radialOffset_after hστ ht
  unfold radialShift at hh
  unfold blowupMoment blowupSize
  linarith

theorem radialOffset_sub_id_antitone (σ τ : ℝ) :
    Antitone (fun t => radialOffset σ τ t - t) := by
  apply antitone_of_hasDerivAt_nonpos
    (fun t => (radialOffset_hasDerivAt σ τ t).sub (hasDerivAt_id t))
  intro t
  change radialSwitch σ τ t - 1 ≤ 0
  linarith [radialSwitch_le_one σ τ t]

theorem blowupMoment_ge_id {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    t ≤ blowupMoment σ τ t := by
  by_cases ht : τ ≤ t
  · rw [blowupMoment_after hστ ht]
  · have hh := radialOffset_sub_id_antitone σ τ (le_of_not_ge ht)
    unfold blowupMoment blowupSize
    linarith

theorem blowupSize_bounds {σ τ : ℝ} (hστ : σ < τ) :
    σ ≤ blowupSize σ τ ∧ blowupSize σ τ ≤ τ := by
  constructor
  · simpa only [blowupMoment_before hστ le_rfl] using blowupMoment_ge_id hστ σ
  · unfold blowupSize
    linarith [radialOffset_nonneg hστ τ]

theorem blowupCoefficient_smoothAt (σ τ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ContDiffAt ℝ ∞ (blowupCoefficient σ τ) t :=
  (blowupMoment_smooth σ τ).contDiffAt.div contDiffAt_id ht

theorem blowupCoefficient_hasDerivAt (σ τ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (blowupCoefficient σ τ) (blowupSlope σ τ t) t := by
  have h := (blowupMoment_hasDerivAt σ τ t).div (hasDerivAt_id t) ht
  simpa [blowupCoefficient,blowupSlope,mul_comm] using! h

theorem blowupCoefficient_before {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    blowupCoefficient σ τ t = blowupSize σ τ / t := by
  rw [blowupCoefficient,blowupMoment_before hστ ht]

theorem blowupCoefficient_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t)
    (ht0 : t ≠ 0) : blowupCoefficient σ τ t = 1 := by
  rw [blowupCoefficient,blowupMoment_after hστ ht,div_self ht0]

theorem blowupSlope_nonpos {σ τ t : ℝ} (hστ : σ < τ) (ht : 0 ≤ t) :
    blowupSlope σ τ t ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (radialSwitch_le_one σ τ t) ht
  have hq := blowupMoment_ge_id hστ t
  linarith

theorem blowup_radial_derivative {σ τ t : ℝ} (ht : t ≠ 0) :
    blowupCoefficient σ τ t + t * blowupSlope σ τ t = radialSwitch σ τ t := by
  unfold blowupCoefficient blowupSlope
  field_simp
  ring

theorem weightedTwoForm_J_nonneg {n : ℕ} {g dg : ℝ} (hdg : dg ≤ 0)
    (x v : Phase n) (hr : 0 ≤ g + capacity x * dg) :
    0 ≤ weightedTwoForm g dg x v (standardJ n v) := by
  have hcs := stdDot_standardForm_sq_le x v
  have hs : Real.pi * dg ≤ 0 := mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hdg
  have hm := mul_le_mul_of_nonpos_left hcs hs
  have hh := mul_nonneg hr (stdDot_nonneg v)
  simp only [weightedTwoForm,standardForm_J_right,stdDot_J_right]
  rw [capacity_eq_stdDot] at hh
  nlinarith only [hm,hh]

theorem blowupForm_J_nonneg {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {x : Phase n} (hx : 0 < capacity x) (v : Phase n) :
    0 ≤ weightedTwoForm (blowupCoefficient σ τ (capacity x))
      (blowupSlope σ τ (capacity x)) x v (standardJ n v) := by
  apply weightedTwoForm_J_nonneg (blowupSlope_nonpos hστ hx.le)
  rw [blowup_radial_derivative hx.ne']
  exact radialSwitch_nonneg σ τ _




theorem inverse_chart_analyticAt {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f)
    {J : Phase n → End n} {u : ℂ → Phase n} {z : ℂ}
    (hu : ∀ w, PseudoHolomorphicAt J u w) (hz : u z ∈ f '' U)
    (hJ : ∀ᶠ y in 𝓝 (u z), J y = imageJ U f y) :
    AnalyticAt ℂ (invFunOn f U ∘ u) z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hc := (hu z).1.continuousAt
  filter_upwards [hc.eventually hJ,
    hc.eventually ((symplecticOn_open_image hf).mem_nhds hz)] with w hJw hw
  apply inverse_chart_holomorphic hf _ hw
  refine ⟨(hu w).1,?_⟩
  intro v
  rw [(hu w).2, hJw]

theorem inverse_chart_zero_iff {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {y : Phase n} (hy : y ∈ f '' U) :
    invFunOn f U y = 0 ↔ y = f 0 := by
  constructor
  · intro he
    have hi := invFunOn_eq hy
    rw [he] at hi
    exact hi.symm
  · rintro rfl
    exact (symplecticOn_injOn hf).leftInvOn_invFunOn h0

theorem not_locally_constant_in_chart {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ∀ w, PseudoHolomorphicAt J u w)
    (hnc : ¬ ∀ w, u w = f 0)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y) (z : ℂ) :
    ¬ ∀ᶠ w in 𝓝 z, u w = f 0 := by
  let S : Set ℂ := {w | ∀ᶠ v in 𝓝 w, u v = f 0}
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun w => (hu w).1.continuousAt
  have hsub : S ⊆ {w | u w = f 0} := fun w hw => hw.self_of_nhds
  have hclosed : closure S ⊆ S := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact hwS
    have hew : u w = f 0 :=
      ((isClosed_eq hcont continuous_const).closure_subset_iff.mpr hsub) hw
    have haf : AnalyticAt ℂ (invFunOn f U ∘ u) w :=
      inverse_chart_analyticAt hf hu (hew ▸ mem_image_of_mem f h0) (hew ▸ hJ)
    have hcl : w ∈ closure ({v | u v = f 0} \ {w}) := by
      apply closure_mono _ hw
      intro v hv
      refine ⟨hsub hv,?_⟩
      intro hvw
      have : v = w := hvw
      subst v
      exact hwS hv
    have hfreq : ∃ᶠ v in 𝓝[≠] w, (invFunOn f U ∘ u) v = 0 := by
      apply (mem_closure_ne_iff_frequently_within.mp hcl).mono
      intro v hv
      change invFunOn f U (u v) = 0
      rw [hv]
      exact (symplecticOn_injOn hf).leftInvOn_invFunOn h0
    have hzero := haf.frequently_zero_iff_eventually_zero.mp hfreq
    have hfU : f '' U ∈ 𝓝 (u w) :=
      (symplecticOn_open_image hf).mem_nhds (hew ▸ mem_image_of_mem f h0)
    filter_upwards [hzero, (hcont.continuousAt.eventually hfU)] with v hv hvU
    exact (inverse_chart_zero_iff hf h0 hvU).mp hv
  have hclopen : IsClopen S := ⟨isClosed_of_closure_subset hclosed,
    isOpen_setOfPred_eventually_nhds⟩
  intro hz
  have hall : S = univ := hclopen.eq_univ ⟨z,hz⟩
  apply hnc
  intro w
  exact hsub (hall ▸ mem_univ w)

theorem isolated_chart_centre {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ∀ w, PseudoHolomorphicAt J u w) (hnc : ¬ ∀ w, u w = f 0)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y)
    {z : ℂ} (hz : u z = f 0) :
    ∀ᶠ w in 𝓝[≠] z, u w ≠ f 0 := by
  have haf := inverse_chart_analyticAt hf hu (hz ▸ mem_image_of_mem f h0) (hz ▸ hJ)
  have hzero : ¬ ∀ᶠ w in 𝓝 z, (invFunOn f U ∘ u) w = 0 := by
    intro he
    apply not_locally_constant_in_chart hf h0 hu hnc hJ z
    have hU := (hu z).1.continuousAt.eventually
      ((symplecticOn_open_image hf).mem_nhds (hz ▸ mem_image_of_mem f h0))
    filter_upwards [he,hU] with w hw hwU
    exact (inverse_chart_zero_iff hf h0 hwU).mp hw
  have he := haf.eventually_eq_zero_or_eventually_ne_zero.resolve_left hzero
  filter_upwards [he] with w hw
  intro heq
  apply hw
  change invFunOn f U (u w) = 0
  rw [heq]
  exact (symplecticOn_injOn hf).leftInvOn_invFunOn h0

theorem chart_centre_positive_order {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ∀ w, PseudoHolomorphicAt J u w) (hnc : ¬ ∀ w, u w = f 0)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y)
    {z : ℂ} (hz : u z = f 0) :
    ∃ (m : ℕ) (v : ℂ → Phase n), 0 < m ∧ AnalyticAt ℂ v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, (invFunOn f U ∘ u) w = (w-z)^m • v w := by
  have haf := inverse_chart_analyticAt hf hu (hz ▸ mem_image_of_mem f h0) (hz ▸ hJ)
  have hzero : ¬ ∀ᶠ w in 𝓝 z, (invFunOn f U ∘ u) w = 0 := by
    intro he
    apply not_locally_constant_in_chart hf h0 hu hnc hJ z
    have hU := (hu z).1.continuousAt.eventually
      ((symplecticOn_open_image hf).mem_nhds (hz ▸ mem_image_of_mem f h0))
    filter_upwards [he,hU] with w hw hwU
    exact (inverse_chart_zero_iff hf h0 hwU).mp hw
  obtain ⟨m,v,hv,hv0,he⟩ := haf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hzero
  refine ⟨m,v,?_,hv,hv0,he⟩
  by_contra hm
  have hm0 : m = 0 := by omega
  have he0 := he.self_of_nhds
  have hi : (invFunOn f U ∘ u) z = 0 := by
    change invFunOn f U (u z) = 0
    rw [hz]
    exact (symplecticOn_injOn hf).leftInvOn_invFunOn h0
  rw [hi,hm0,pow_zero,one_smul] at he0
  exact hv0 he0.symm

theorem AffineLineCurve.not_constant {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (y : Phase n) : ¬ ∀ z, u z = y := by
  intro hc
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have ht : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 0) := by
    simpa only [hc, zero_smul] using hi.smul_const y
  exact hv (tendsto_nhds_unique hlim ht)

theorem AffineLineCurve.finite_centre_fibre {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y) :
    Set.Finite {z | u z = f 0} := by
  have hc : IsCompact {z | u z = f 0} :=
    hu.isProperMap.isCompact_preimage isCompact_singleton
  apply hc.finite
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  have he := isolated_chart_centre hf h0 hu.2.1 (hu.not_constant _) hJ hz
  exact Filter.inf_principal_eq_bot.mpr he



open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)

theorem capacity_smul_complex {n : ℕ} (c : ℂ) (x : Phase n) :
    capacity (c • x) = Complex.normSq c * capacity x := by
  simp only [capacity,Pi.smul_apply,smul_eq_mul,Complex.normSq_mul,Finset.mul_sum]
  ring_nf

theorem standardForm_smul_complex_same {n : ℕ} (c : ℂ) (x v : Phase n) :
    standardForm (c • x) (c • v) = Complex.normSq c * standardForm x v := by
  simp only [standardForm,Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    Finset.mul_sum,Complex.normSq_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem standardForm_smul_complex_self {n : ℕ} (c d : ℂ) (x : Phase n) :
    standardForm (c • x) (d • x) = (star c * d).im * stdDot n x x := by
  simp only [standardForm,Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    stdDot_apply,Finset.mul_sum,Complex.star_def,Complex.conj_re,Complex.conj_im]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem capacity_pos {n : ℕ} {x : Phase n} (hx : x ≠ 0) : 0 < capacity x := by
  rw [capacity_eq_stdDot]
  exact mul_pos Real.pi_pos (stdDot_pos hx)

theorem normalizedPrimitive_smoothAt {n : ℕ} {x : Phase n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (@normalizedPrimitive n) x :=
  (contDiffAt_const.div (contDiffAt_const.mul (capacity_smooth n).contDiffAt)
    (mul_ne_zero (by norm_num) (capacity_pos hx).ne')).smul (stdOmega n).contDiff.contDiffAt

theorem normalizedPrimitive_smul {n : ℕ} {c : ℂ} (hc : c ≠ 0)
    {x : Phase n} (hx : x ≠ 0) (d : ℂ) (v : Phase n) :
    normalizedPrimitive (c • x) (d • x + c • v) =
      (c⁻¹ * d).im / (2 * Real.pi) + normalizedPrimitive x v := by
  rw [normalizedPrimitive_apply,←stdOmega_apply,map_add,stdOmega_apply,stdOmega_apply,
    standardForm_smul_complex_self,standardForm_smul_complex_same,
    capacity_smul_complex,normalizedPrimitive_apply,capacity_eq_stdDot]
  have hn : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  have hx' : stdDot n x x ≠ 0 := (stdDot_pos hx).ne'
  have he : (c⁻¹ * d).im = (star c * d).im / Complex.normSq c := by
    simp only [Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.star_def,
      Complex.conj_re,Complex.conj_im]
    ring
  rw [he]
  field_simp

theorem normalizedPrimitive_power {n : ℕ} {z : ℂ} (hz : z ≠ 0)
    {x : Phase n} (hx : x ≠ 0) (m : ℕ) (w : ℂ) (v : Phase n) :
    normalizedPrimitive (z^m • x) (((m:ℂ) * z^(m-1) * w) • x + z^m • v) =
      (m:ℝ) * (z⁻¹ * w).im / (2 * Real.pi) + normalizedPrimitive x v := by
  rw [normalizedPrimitive_smul (pow_ne_zero m hz) hx]
  congr 2
  by_cases hm : m = 0
  · simp [hm]
  · have he : (z^m)⁻¹ * ((m:ℂ) * z^(m-1) * w) = (m:ℂ) * (z⁻¹ * w) := by
      have hm' : m = (m-1)+1 := by omega
      conv_lhs => arg 1; rw [hm',pow_succ]
      field_simp
    rw [he]
    simp

theorem complex_winding_eq_angular {z : Plane} (_hz : z ≠ 0) (v : Plane) :
    ((Complex.equivRealProdCLM.symm z)⁻¹ * Complex.equivRealProdCLM.symm v).im =
      angularOneForm z v := by
  have hn : Complex.normSq (Complex.equivRealProdCLM.symm z) = radiusSq z := by
    simp [Complex.normSq_apply,Complex.equivRealProdCLM_symm_apply,radiusSq,pow_two]
  rw [angularOneForm,smul_apply,smul_eq_mul,planarArea_apply]
  simp only [Complex.mul_im,Complex.inv_re,Complex.inv_im,hn]
  simp only [Complex.equivRealProdCLM_symm_apply,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,zero_add]
  ring


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem weightedPrimitive_smoothAt {n : ℕ} {g : ℝ → ℝ} {x : Phase n}
    (hg : ContDiffAt ℝ ∞ g (capacity x)) :
    ContDiffAt ℝ ∞ (weightedPrimitive g) x :=
  ((hg.comp x (capacity_smooth n).contDiffAt).div_const 2).smul
    (stdOmega n).contDiff.contDiffAt

theorem weightedPrimitive_differentiableAt {n : ℕ} {g : ℝ → ℝ} {x : Phase n}
    (hg : DifferentiableAt ℝ g (capacity x)) :
    DifferentiableAt ℝ (weightedPrimitive g) x :=
  ((hg.div_const (2 : ℝ)).comp x (capacity_hasFDerivAt x).differentiableAt).fun_smul
    (stdOmega n).differentiableAt

theorem weightedPrimitive_derivative {n : ℕ} {g : ℝ → ℝ} {dg : ℝ} {x : Phase n}
    (hg : HasDerivAt g dg (capacity x)) (v w : Phase n) :
    fderiv ℝ (weightedPrimitive g) x v w =
      (g (capacity x) / 2) * standardForm v w +
      Real.pi * dg * stdDot n x v * standardForm x w := by
  have hd := ((hg.div_const 2).comp_hasFDerivAt x (capacity_hasFDerivAt x)).smul
    (stdOmega n).hasFDerivAt
  change HasFDerivAt (weightedPrimitive g) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,stdOmega_apply,Function.comp_def]
  ring

theorem weightedPrimitive_extDeriv {n : ℕ} {g : ℝ → ℝ} {dg : ℝ} {x : Phase n}
    (hg : HasDerivAt g dg (capacity x)) (v w : Phase n) :
    extDeriv (oneForm (weightedPrimitive g)) x ![v,w] = weightedTwoForm (g (capacity x)) dg x v w := by
  have hα := weightedPrimitive_differentiableAt hg.differentiableAt
  have hω : DifferentiableAt ℝ (oneForm (weightedPrimitive g)) x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Phase n) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x hα
  rw [extDeriv_apply hω,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => weightedPrimitive g y w) x v -
    fderiv ℝ (fun y => weightedPrimitive g y v) x w = _
  have he (a b : Phase n) :
      fderiv ℝ (fun y => weightedPrimitive g y a) x b =
        fderiv ℝ (weightedPrimitive g) x b a := by
    rw [fderiv_clm_apply hα (differentiableAt_const a)]
    simp
  rw [he w v,he v w,weightedPrimitive_derivative hg,weightedPrimitive_derivative hg,
    standardForm_skew w v]
  unfold weightedTwoForm
  ring

theorem blowupPrimitive_smoothAt {n : ℕ} (σ τ : ℝ) {x : Phase n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (@blowupPrimitive n σ τ) x :=
  weightedPrimitive_smoothAt (blowupCoefficient_smoothAt σ τ (capacity_pos hx).ne')

theorem blowupPrimitive_extDeriv {n : ℕ} (σ τ : ℝ) {x : Phase n} (hx : x ≠ 0)
    (v w : Phase n) :
    extDeriv (oneForm (blowupPrimitive σ τ)) x ![v,w] =
      weightedTwoForm (blowupCoefficient σ τ (capacity x))
        (blowupSlope σ τ (capacity x)) x v w :=
  weightedPrimitive_extDeriv (blowupCoefficient_hasDerivAt σ τ (capacity_pos hx).ne') v w

theorem blowupPrimitive_extDeriv_nonneg {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {x : Phase n} (hx : x ≠ 0) (v : Phase n) :
    0 ≤ extDeriv (oneForm (blowupPrimitive σ τ)) x ![v,standardJ n v] := by
  rw [blowupPrimitive_extDeriv σ τ hx]
  exact blowupForm_J_nonneg hστ (capacity_pos hx) v

theorem blowupPrimitive_before {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {x : Phase n} (hx : capacity x ≤ σ) :
    blowupPrimitive σ τ x = blowupSize σ τ • normalizedPrimitive x := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [blowupPrimitive,weightedPrimitive,smul_apply,smul_eq_mul,stdOmega_apply,
    blowupCoefficient_before hστ hx,normalizedPrimitive_apply]
  ring

theorem blowupPrimitive_after {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {x : Phase n} (hx : τ ≤ capacity x) (hx0 : x ≠ 0) :
    blowupPrimitive σ τ x = (1/2 : ℝ) • stdOmega n x := by
  simp only [blowupPrimitive,weightedPrimitive,
    blowupCoefficient_after hστ hx (capacity_pos hx0).ne']



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Correction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem stdPrimitive_smooth (n : ℕ) : ContDiff ℝ ∞ (@stdPrimitive n) :=
  (contDiff_const (c := (1/2 : ℝ))).smul (stdOmega n).contDiff

theorem inversePullback_smoothAt {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    {α : Phase n → Phase n →L[ℝ] ℝ}
    (hα : ContDiffAt ℝ ∞ α (invFunOn f U y)) :
    ContDiffAt ℝ ∞ (inversePullback U f α) y := by
  have hg := (symplecticOn_inverse_smooth hf).contDiffAt
    ((symplecticOn_open_image hf).mem_nhds hy)
  exact (hα.comp y hg).clm_comp (hg.fderiv_right (by simp))

theorem inverse_fderiv_preserves_form {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    (v w : Phase n) :
    standardForm (fderiv ℝ (invFunOn f U) y v) (fderiv ℝ (invFunOn f U) y w) =
      standardForm v w := by
  rw [symplecticOn_inverse_fderiv hf hy]
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible hf (invFunOn_mem hy)
  rw [←he,ContinuousLinearMap.inverse_equiv]
  have h := hf.2.2.2 _ (invFunOn_mem hy) (e.symm v) (e.symm w)
  rw [←he] at h
  simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using h.symm

theorem chartCorrection_eq_near {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    (σ τ : ℝ) :
    chartCorrection U f σ τ =ᶠ[𝓝 y]
      inversePullback U f (fun x => blowupPrimitive σ τ x - stdPrimitive x) := by
  filter_upwards [(symplecticOn_open_image hf).mem_nhds hy] with z hz
  simp only [chartCorrection, ite_eq_left hz]

theorem chartCorrection_zero_off {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} {σ τ : ℝ} (hτ : 0 < τ) (hστ : σ < τ)
    {y : Phase n} (hy : y ∉ f '' closedBall n τ) : chartCorrection U f σ τ y = 0 := by
  classical
  unfold chartCorrection
  split_ifs with h
  · have hcap : τ < capacity (invFunOn f U y) := by
      by_contra! hn
      exact hy ⟨invFunOn f U y,hn,invFunOn_eq h⟩
    have hne : invFunOn f U y ≠ 0 := by
      intro he
      simp only [he,capacity,Pi.zero_apply,Complex.normSq_zero,Finset.sum_const_zero,mul_zero] at hcap
      linarith
    simp only [inversePullback,blowupPrimitive_after hστ hcap.le hne,stdPrimitive,
      sub_self,ContinuousLinearMap.zero_comp]
  · rfl

theorem chartCorrection_support {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U) :
    tsupport (chartCorrection U f σ τ) ⊆ f '' closedBall n τ := by
  apply closure_minimal _ ((closedBall_isCompact n τ).image_of_continuousOn
    (hf.2.1.continuousOn.mono hsub)).isClosed
  intro y hy
  by_contra hn
  exact hy (chartCorrection_zero_off hτ hστ hn)

theorem chartCorrection_compact {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U) :
    HasCompactSupport (chartCorrection U f σ τ) :=
  ((closedBall_isCompact n τ).image_of_continuousOn
    (hf.2.1.continuousOn.mono hsub)).of_isClosed_subset (isClosed_tsupport _)
      (chartCorrection_support hf hτ hστ hsub)

theorem chartCorrection_zero_near {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U)
    {y : Phase n} (hy : y ∉ f '' closedBall n τ) :
    chartCorrection U f σ τ =ᶠ[𝓝 y] 0 := by
  have hK := ((closedBall_isCompact n τ).image_of_continuousOn
    (hf.2.1.continuousOn.mono hsub)).isClosed
  filter_upwards [hK.isOpen_compl.mem_nhds hy] with z hz
  exact chartCorrection_zero_off hτ hστ hz

theorem chartCorrection_smoothAt {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U)
    {y : Phase n} (hy : y ≠ f 0) :
    ContDiffAt ℝ ∞ (chartCorrection U f σ τ) y := by
  by_cases hU : y ∈ f '' U
  · apply ContDiffAt.congr_of_eventuallyEq _ (chartCorrection_eq_near hf hU σ τ)
    apply inversePullback_smoothAt hf hU
    apply ContDiffAt.sub _ (stdPrimitive_smooth n).contDiffAt
    apply blowupPrimitive_smoothAt
    intro he
    have hi := invFunOn_eq hU
    rw [he] at hi
    exact hy hi.symm
  · apply ContDiffAt.congr_of_eventuallyEq contDiffAt_const
    apply chartCorrection_zero_near hf hτ hστ hsub
    exact fun h => hU (image_mono hsub h)



open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)

theorem complex_power_fderiv_real (m : ℕ) (z w : ℂ) :
    fderiv ℝ (fun y : ℂ => y^m) z w = (m:ℂ) * z^(m-1) * w := by
  rw [((hasDerivAt_pow m z).hasFDerivAt.restrictScalars ℝ).fderiv]
  change w * ((m:ℂ) * z^(m-1)) = _
  ring

theorem power_curve_fderiv {n : ℕ} {h : ℂ → Phase n} {z : ℂ}
    (hh : DifferentiableAt ℝ h z) (m : ℕ) (w : ℂ) :
    fderiv ℝ (fun y : ℂ => y^m • h y) z w =
      ((m:ℂ) * z^(m-1) * w) • h z + z^m • fderiv ℝ h z w := by
  rw [fderiv_fun_smul (((hasDerivAt_pow m z).differentiableAt).restrictScalars ℝ) hh]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    complex_power_fderiv_real]
  module

theorem normalizedPrimitive_power_pullback {n : ℕ} {h : ℂ → Phase n} {z : Plane}
    (hh : DifferentiableAt ℝ h (Complex.equivRealProdCLM.symm z))
    (hh0 : h (Complex.equivRealProdCLM.symm z) ≠ 0) (hz : z ≠ 0) (m : ℕ) :
    planarPullback (realCurve (fun y : ℂ => y^m • h y)) normalizedPrimitive z =
      ((m:ℝ) / (2 * Real.pi)) • angularOneForm z +
        planarPullback (realCurve h) normalizedPrimitive z := by
  apply ContinuousLinearMap.ext
  intro w
  have hz' : Complex.equivRealProdCLM.symm z ≠ 0 := by
    intro he
    apply hz
    exact Complex.equivRealProdCLM.symm.injective (he.trans (map_zero _).symm)
  have hd : DifferentiableAt ℝ (fun y : ℂ => y^m • h y)
      (Complex.equivRealProdCLM.symm z) :=
    (((hasDerivAt_pow m _).differentiableAt).restrictScalars ℝ).fun_smul hh
  change normalizedPrimitive _ (fderiv ℝ (realCurve _) z w) =
    (m:ℝ) / (2*Real.pi) * angularOneForm z w +
      normalizedPrimitive _ (fderiv ℝ (realCurve _) z w)
  rw [realCurve_fderiv hd,realCurve_fderiv hh,power_curve_fderiv hh]
  change normalizedPrimitive ((Complex.equivRealProdCLM.symm z)^m • h _) _ = _
  rw [normalizedPrimitive_power hz' hh0,complex_winding_eq_angular hz]
  simp only [realCurve,Function.comp_def]
  ring

theorem normalizedPrimitive_branch_residue {n : ℕ} {v h : ℂ → Phase n} {m : ℕ}
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0)
    (he : v =ᶠ[𝓝 0] fun z : ℂ => z^m • h z) :
    ∀ᶠ z in 𝓝[≠] (0 : Plane),
      planarPullback (realCurve v) normalizedPrimitive z =
        ((m:ℝ) / (2 * Real.pi)) • angularOneForm z +
          planarPullback (realCurve h) normalizedPrimitive z := by
  have ht : Tendsto Complex.equivRealProdCLM.symm (𝓝 (0 : Plane)) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.equivRealProdCLM_symm_apply,Prod.fst_zero,Prod.snd_zero,
      Complex.ofReal_zero,zero_mul,zero_add] using
      (Complex.equivRealProdCLM.symm.continuous.tendsto (0 : Plane))
  have hreal : realCurve v =ᶠ[𝓝 (0 : Plane)] realCurve (fun z : ℂ => z^m • h z) := ht.eventually he
  have hn : ∀ᶠ w in 𝓝 (0 : ℂ), h w ≠ 0 :=
    hh.continuousAt.eventually (isClosed_singleton.isOpen_compl.mem_nhds hh0)
  have hd : ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℝ h w :=
    hh.eventually_analyticAt.mono fun _ hx => hx.differentiableAt.restrictScalars ℝ
  filter_upwards [((eventually_eventually_nhds.mpr hreal).filter_mono nhdsWithin_le_nhds),
    (ht.eventually hn).filter_mono nhdsWithin_le_nhds,
    (ht.eventually hd).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hez hdz hz0
  change realCurve v =ᶠ[𝓝 z] realCurve (fun w : ℂ => w^m • h w) at hz
  have hp : planarPullback (realCurve v) normalizedPrimitive z =
      planarPullback (realCurve (fun w : ℂ => w^m • h w)) normalizedPrimitive z := by
    unfold planarPullback
    rw [hz.self_of_nhds,hz.fderiv_eq]
  rw [hp]
  exact normalizedPrimitive_power_pullback hdz hez hz0 m


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)

theorem realCurve_smoothAt {n : ℕ} {u : ℂ → Phase n} {z : Plane}
    (hu : ContDiffAt ℝ ∞ u (Complex.equivRealProdCLM.symm z)) :
    ContDiffAt ℝ ∞ (realCurve u) z :=
  hu.comp z Complex.equivRealProdCLM.symm.contDiff.contDiffAt

theorem planarPullback_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ} {z : Plane}
    (hv : ContDiffAt ℝ ∞ v z) (hα : ContDiffAt ℝ ∞ α (v z)) :
    ContDiffAt ℝ ∞ (planarPullback v α) z :=
  (hα.comp z hv).clm_comp (hv.fderiv_right (by simp))

theorem normalizedPrimitive_remainder_smooth {n : ℕ} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0) :
    ContDiffAt ℝ ∞ (planarPullback (realCurve h) normalizedPrimitive) 0 := by
  apply planarPullback_smoothAt
  · apply realCurve_smoothAt
    simpa only [map_zero] using (hh.contDiffAt.restrict_scalars ℝ : ContDiffAt ℝ ∞ h 0)
  · apply normalizedPrimitive_smoothAt
    simpa using hh0

theorem blowup_branch_residue {n : ℕ} {v h : ℂ → Phase n} {m : ℕ}
    (hm : 0 < m) (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0)
    (he : v =ᶠ[𝓝 0] fun z : ℂ => z^m • h z)
    {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) :
    ∃ β : Plane → Plane →L[ℝ] ℝ, ContDiffAt ℝ ∞ β 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : Plane),
        planarPullback (realCurve v) (blowupPrimitive σ τ) z =
          ((blowupSize σ τ * (m:ℝ)) / (2 * Real.pi)) • angularOneForm z + β z := by
  let β : Plane → Plane →L[ℝ] ℝ :=
    fun z => blowupSize σ τ • planarPullback (realCurve h) normalizedPrimitive z
  refine ⟨β,?_,?_⟩
  · exact (contDiffAt_const (c := blowupSize σ τ)).smul
      (normalizedPrimitive_remainder_smooth hh hh0)
  have hv0 : v 0 = 0 := by
    have hh := he.self_of_nhds
    simpa only [zero_pow hm.ne',zero_smul] using hh
  have hvc : ContinuousAt v 0 :=
    (continuousAt_id.pow m |>.smul hh.continuousAt).congr_of_eventuallyEq he
  have hrvc : ContinuousAt (realCurve v) 0 := by
    unfold realCurve
    apply ContinuousAt.comp _ Complex.equivRealProdCLM.symm.continuous.continuousAt
    simpa only [map_zero] using hvc
  have hcap : capacity (realCurve v 0) < σ := by
    simpa [hv0,capacity] using hσ
  have hsmall : ∀ᶠ z in 𝓝 (0 : Plane), capacity (realCurve v z) < σ :=
    ((capacity_smooth n).continuous.continuousAt.comp hrvc).eventually
      (isOpen_Iio.mem_nhds hcap)
  filter_upwards [normalizedPrimitive_branch_residue hh hh0 he,
    hsmall.filter_mono nhdsWithin_le_nhds] with z hz hzsmall
  have hpb : planarPullback (realCurve v) (blowupPrimitive σ τ) z =
      blowupSize σ τ • planarPullback (realCurve v) normalizedPrimitive z := by
    unfold planarPullback
    rw [blowupPrimitive_before hστ hzsmall.le]
    rfl
  rw [hpb,hz,smul_add,smul_smul]
  change (blowupSize σ τ * ((m:ℝ)/(2*Real.pi))) • angularOneForm z + β z = _
  congr 2
  ring


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem oneForm_smoothAt {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : ContDiffAt ℝ ∞ α x) : ContDiffAt ℝ ∞ (oneForm α) x :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.contDiffAt.comp x hα

theorem oneForm_extDeriv_apply {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (v w : E) :
    extDeriv (oneForm α) x ![v,w] = fderiv ℝ α x v w - fderiv ℝ α x w v := by
  have hω : DifferentiableAt ℝ (oneForm α) x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x hα
  rw [extDeriv_apply hω,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => α y w) x v - fderiv ℝ (fun y => α y v) x w = _
  rw [fderiv_clm_apply hα (differentiableAt_const w),
    fderiv_clm_apply hα (differentiableAt_const v)]
  simp

theorem oneForm_extDeriv_sub {α β : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) (v w : E) :
    extDeriv (oneForm (fun y => α y - β y)) x ![v,w] =
      extDeriv (oneForm α) x ![v,w] - extDeriv (oneForm β) x ![v,w] := by
  rw [oneForm_extDeriv_apply (hα.fun_sub hβ),oneForm_extDeriv_apply hα,
    oneForm_extDeriv_apply hβ,fderiv_fun_sub hα hβ]
  simp only [sub_apply]
  ring

theorem oneForm_extDeriv_add {α β : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) (v w : E) :
    extDeriv (oneForm (fun y => α y + β y)) x ![v,w] =
      extDeriv (oneForm α) x ![v,w] + extDeriv (oneForm β) x ![v,w] := by
  rw [oneForm_extDeriv_apply (hα.fun_add hβ),oneForm_extDeriv_apply hα,
    oneForm_extDeriv_apply hβ,fderiv_fun_add hα hβ]
  simp only [add_apply]
  ring

theorem oneForm_extDeriv_congr {α β : E → E →L[ℝ] ℝ} {x : E}
    (he : α =ᶠ[𝓝 x] β) : extDeriv (oneForm α) x = extDeriv (oneForm β) x := by
  have he' : oneForm α =ᶠ[𝓝 x] oneForm β := he.fun_comp _
  simp only [extDeriv,he'.fderiv_eq]

theorem planarCurl_eq_extDeriv_at {α : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (hα : DifferentiableAt ℝ α z) :
    planarCurl α z = extDeriv (oneForm α) z ![(1,0),(0,1)] :=
  (oneForm_extDeriv_apply hα _ _).symm

theorem planarPullback_curlAt {v : Plane → E} {α : E → E →L[ℝ] ℝ} {z : Plane}
    (hv : ContDiffAt ℝ ∞ v z) (hα : ContDiffAt ℝ ∞ α (v z)) :
    planarCurl (planarPullback v α) z =
      extDeriv (oneForm α) (v z) ![fderiv ℝ v z (1,0),fderiv ℝ v z (0,1)] := by
  rw [planarCurl_eq_extDeriv_at ((planarPullback_smoothAt hv hα).differentiableAt (by simp))]
  have he : oneForm (planarPullback v α) = fun y =>
      (oneForm α (v y)).compContinuousLinearMap (fderiv ℝ v y) := by
    funext y
    ext w
    rfl
  rw [he,extDeriv_pullback ((oneForm_smoothAt hα).differentiableAt (by simp))
    hv (by
      norm_num [minSmoothness] <;> first | done | exact WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem inversePullback_extDeriv {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    {α : Phase n → Phase n →L[ℝ] ℝ}
    (hα : ContDiffAt ℝ ∞ α (invFunOn f U y)) (v w : Phase n) :
    extDeriv (oneForm (inversePullback U f α)) y ![v,w] =
      extDeriv (oneForm α) (invFunOn f U y)
        ![fderiv ℝ (invFunOn f U) y v,fderiv ℝ (invFunOn f U) y w] := by
  have he : oneForm (inversePullback U f α) = fun z =>
      (oneForm α (invFunOn f U z)).compContinuousLinearMap (fderiv ℝ (invFunOn f U) z) := by
    funext z
    ext w
    rfl
  rw [he,extDeriv_pullback ((oneForm_smoothAt hα).differentiableAt (by simp))
    ((symplecticOn_inverse_smooth hf).contDiffAt ((symplecticOn_open_image hf).mem_nhds hy)) (by
      norm_num [minSmoothness] <;> first | done | exact WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem stdPrimitive_extDeriv {n : ℕ} (x v w : Phase n) :
    extDeriv (oneForm stdPrimitive) x ![v,w] = standardForm v w := by
  have he : (@stdPrimitive n) = weightedPrimitive (fun _ => 1) := rfl
  rw [he,weightedPrimitive_extDeriv (hasDerivAt_const (capacity x) (1 : ℝ))]
  simp [weightedTwoForm]

theorem chartCorrection_extDeriv {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    {y : Phase n} (hy : y ∈ f '' U) (hy0 : y ≠ f 0) (v w : Phase n) :
    extDeriv (oneForm (chartCorrection U f σ τ)) y ![v,w] =
      extDeriv (oneForm (blowupPrimitive σ τ)) (invFunOn f U y)
        ![fderiv ℝ (invFunOn f U) y v,fderiv ℝ (invFunOn f U) y w] - standardForm v w := by
  have hx : invFunOn f U y ≠ 0 := by
    intro he
    have hi := invFunOn_eq hy
    rw [he] at hi
    exact hy0 hi.symm
  have hα := blowupPrimitive_smoothAt σ τ hx
  have hβ := (stdPrimitive_smooth n).contDiffAt (x := invFunOn f U y)
  rw [oneForm_extDeriv_congr (chartCorrection_eq_near hf hy σ τ),
    inversePullback_extDeriv hf hy (hα.sub hβ),
    oneForm_extDeriv_sub (hα.differentiableAt (by simp)) (hβ.differentiableAt (by simp)),
    stdPrimitive_extDeriv,inverse_fderiv_preserves_form hf hy]

theorem inverse_fderiv_intertwines {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    (v : Phase n) :
    fderiv ℝ (invFunOn f U) y (imageJ U f y v) =
      standardJ n (fderiv ℝ (invFunOn f U) y v) := by
  rw [symplecticOn_inverse_fderiv hf hy]
  unfold imageJ
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible hf (invFunOn_mem hy)
  rw [←he]
  simp


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem outerProfile_smooth (A : ℝ) : ContDiff ℝ ∞ (outerProfile A) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const A)))

theorem outerProfile_compact {A : ℝ} (hA : 0 < A) : HasCompactSupport (outerProfile A) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-2:ℝ)) (b := 2*A))
  intro t ht
  have ht' : t < -2 ∨ 2*A < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases ht' with ht' | ht'
  · simp only [outerProfile,Real.smoothTransition.zero_of_nonpos (by linarith : t+2 ≤ 0),zero_mul]
  · have h : 1 ≤ (t-A)/A := (le_div_iff₀ hA).mpr (by linarith)
    simp only [outerProfile,Real.smoothTransition.one_of_one_le h,sub_self,mul_zero]

theorem outerProfile_nonneg (A t : ℝ) : 0 ≤ outerProfile A t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem outerProfile_zero_value {A : ℝ} (hA : 0 < A) : outerProfile A 0 = 1 := by
  have h : (0-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le
  simp only [outerProfile,zero_add,Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ)≤2),
    Real.smoothTransition.zero_of_nonpos h,sub_zero,mul_one]

theorem outerProfile_deriv {A t : ℝ} (ht : 0 ≤ t) :
    deriv (outerProfile A) t = -(deriv Real.smoothTransition ((t-A)/A) / A) := by
  have he : outerProfile A =ᶠ[𝓝 t] fun s => 1 - Real.smoothTransition ((s-A)/A) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by linarith : (-1:ℝ) < t)] with s hs
    have hs' : -1 < s := hs
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ s + 2),one_mul]
  rw [he.deriv_eq]
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hh := (hs.differentiable (by simp) ((t-A)/A)).hasDerivAt.comp t
    (((hasDerivAt_id t).sub_const A).div_const A)
  have hd := hh.const_sub 1
  change HasDerivAt (fun s => 1 - Real.smoothTransition ((s-A)/A)) _ t at hd
  rw [hd.deriv]
  simp only [div_eq_mul_inv,one_mul]

theorem outerProfile_deriv_nonpos {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) :
    deriv (outerProfile A) t ≤ 0 := by
  rw [outerProfile_deriv ht]
  exact neg_nonpos.mpr (div_nonneg Real.smoothTransition.monotone.deriv_nonneg hA.le)

theorem outerProfile_deriv_zero_before {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (htA : t < A) :
    deriv (outerProfile A) t = 0 := by
  have he : outerProfile A =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (-1:ℝ) A from ⟨by linarith,htA⟩)] with s hs
    have hn : (s-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hs.2]) hA.le
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ s + 2),
      Real.smoothTransition.zero_of_nonpos hn,sub_zero,mul_one]
  rw [he.deriv_eq,deriv_const]

theorem cutoffWedge_radial_rotation {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) :
    cutoffWedge (fun y => g (radiusSq y)) β z =
      2 * deriv g (radiusSq z) * β z (planeRotation z) := by
  have hh := (hg.differentiable (by simp) (radiusSq z)).hasDerivAt.comp_hasFDerivAt z
    (radiusSq_hasFDerivAt z)
  change HasFDerivAt (fun y => g (radiusSq y)) _ z at hh
  have he : planeRotation z = (-z.2) • ((1,0) : Plane) + z.1 • (0,1) := by
    ext <;> simp [planeRotation]
  unfold cutoffWedge
  rw [hh.fderiv, he,map_add,map_smul,map_smul]
  simp only [smul_apply,smul_eq_mul,planarDot_apply]
  simp only [mul_one,mul_zero,add_zero,zero_add]
  ring

theorem nonneg_angular_limit_of_nonneg_curl {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcurl : ∀ z, 0 ≤ planarCurl β z) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) : 0 ≤ k := by
  by_contra! hk
  have he : ∀ᶠ z in cocompact Plane, β z (planeRotation z) ≤ k/2 :=
    (hlim.eventually (eventually_lt_nhds (by linarith : k < k/2))).mono fun _ h => h.le
  obtain ⟨K,hK,hKsub⟩ := mem_cocompact.mp he
  obtain ⟨B,hB,hbound⟩ := (hK.image radiusSq_smooth.continuous).isBounded.exists_pos_norm_le
  let A := B+1
  have hA : 0 < A := by dsimp [A]; linarith
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hgc : HasCompactSupport g := outerProfile_compact hA
  have hcomp : ∀ z : Plane,
      2 * deriv g (radiusSq z) * (k/2) ≤ cutoffWedge (fun y => g (radiusSq y)) β z := by
    intro z
    rw [cutoffWedge_radial_rotation hg]
    by_cases hd : deriv g (radiusSq z) = 0
    · simp [hd]
    have hzA : A ≤ radiusSq z := by
      by_contra! h
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) h)
    have hzK : z ∉ K := by
      intro h
      have hb := hbound (radiusSq z) ⟨z,h,rfl⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (radiusSq_nonneg z)] at hb
      dsimp [A] at hzA
      linarith
    exact mul_le_mul_of_nonpos_left (hKsub hzK)
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (outerProfile_deriv_nonpos hA (radiusSq_nonneg z)))
  have hdi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z) * (k/2)) :=
    ((((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv)).const_mul 2).mul_const (k/2)
  have hwi := cutoffWedge_integrable (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ
  have hle := integral_mono hdi hwi hcomp
  have hg0 : g 0 = 1 := outerProfile_zero_value hA
  rw [integral_mul_const,integral_radial_derivative hg hgc,hg0] at hle
  have hnonneg : 0 ≤ ∫ z : Plane, g (radiusSq z) * planarCurl β z :=
    integral_nonneg fun z => mul_nonneg (outerProfile_nonneg A _) (hcurl z)
  rw [integral_cutoffWedge (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ] at hle
  dsimp only [Function.comp_def] at hle
  have hpk := mul_neg_of_pos_of_neg Real.pi_pos hk
  nlinarith only [hle,hnonneg,hpk]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_AngularPoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem planarCurl_congr {α β : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (he : α =ᶠ[𝓝 z] β) : planarCurl α z = planarCurl β z := by
  simp only [planarCurl,he.fderiv_eq]

theorem planarCurl_sub {α β : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (hα : DifferentiableAt ℝ α z) (hβ : DifferentiableAt ℝ β z) :
    planarCurl (fun y => α y - β y) z = planarCurl α z - planarCurl β z := by
  simp only [planarCurl,fderiv_fun_sub hα hβ,sub_apply]
  ring

theorem planarCurl_const_smul (α : Plane → Plane →L[ℝ] ℝ) (c : ℝ) (z : Plane) :
    planarCurl (fun y => c • α y) z = c * planarCurl α z := by
  have he : fderiv ℝ (fun y => c • α y) z = c • fderiv ℝ α z :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := α) c) z
  simp only [planarCurl,he,smul_apply,smul_eq_mul]
  ring

theorem planarCurl_sum {ι : Type*} (P : Finset ι) {α : ι → Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (hα : ∀ i ∈ P, DifferentiableAt ℝ (α i) z) :
    planarCurl (fun y => ∑ i ∈ P, α i y) z = ∑ i ∈ P, planarCurl (α i) z := by
  rw [planarCurl,fderiv_fun_sum hα]
  simp only [sum_apply,planarCurl]
  simp only [Finset.sum_sub_distrib]

theorem planarCurl_translate {α : Plane → Plane →L[ℝ] ℝ} (p z : Plane)
    (hα : DifferentiableAt ℝ α (z-p)) :
    planarCurl (fun y => α (y-p)) z = planarCurl α (z-p) := by
  have hh := hα.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const p)
  change HasFDerivAt (fun y => α (y-p)) _ z at hh
  simp only [planarCurl,hh.fderiv,ContinuousLinearMap.comp_id]

theorem angularOneForm_curl {z : Plane} (hz : z ≠ 0) : planarCurl angularOneForm z = 0 := by
  have h := cutoffAngular_curl (point := z) (differentiableAt_const (1:ℝ)) (radiusSq_pos hz).ne'
  simpa only [one_smul,deriv_const,mul_zero] using h

theorem angularPole_smoothAt {p z : Plane} (hz : z ≠ p) : ContDiffAt ℝ ∞ (angularPole p) z :=
  (angularOneForm_contDiffAt (radiusSq_pos (sub_ne_zero.mpr hz)).ne').comp z
    (contDiffAt_id.sub contDiffAt_const)

theorem angularPole_curl {p z : Plane} (hz : z ≠ p) : planarCurl (angularPole p) z = 0 := by
  unfold angularPole
  rw [planarCurl_translate p z
    ((angularOneForm_contDiffAt (radiusSq_pos (sub_ne_zero.mpr hz)).ne').differentiableAt (by simp))]
  exact angularOneForm_curl (sub_ne_zero.mpr hz)

theorem angularOneForm_rotation {z : Plane} (hz : z ≠ 0) :
    angularOneForm z (planeRotation z) = 1 := by
  change (radiusSq z)⁻¹ * (z.1*z.1-z.2*(-z.2)) = 1
  have he : z.1*z.1-z.2*(-z.2) = radiusSq z := by unfold radiusSq; ring
  rw [he,inv_mul_cancel₀ (radiusSq_pos hz).ne']

theorem angularPole_tendsto_fixed (p v : Plane) :
    Tendsto (fun z => angularPole p z v) (cocompact Plane) (𝓝 0) := by
  have ht : Tendsto (fun z : Plane => Complex.equivRealProdCLM.symm (z-p))
      (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact.comp
      (Homeomorph.subRight p).isClosedEmbedding.tendsto_cocompact
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hl : Tendsto (fun z : Plane =>
      ((Complex.equivRealProdCLM.symm (z-p))⁻¹ * Complex.equivRealProdCLM.symm v).im)
      (cocompact Plane) (𝓝 0) := by
    simpa only [zero_mul,Complex.zero_im,Function.comp_def] using
      (Complex.continuous_im.continuousAt.tendsto.comp ((hi.comp ht).mul_const
        (Complex.equivRealProdCLM.symm v)))
  apply hl.congr'
  filter_upwards [(isCompact_singleton (x := p)).compl_mem_cocompact] with z hz
  have hz' : z ≠ p := hz
  exact complex_winding_eq_angular (sub_ne_zero.mpr hz') v

theorem angularPole_tendsto_rotation (p : Plane) :
    Tendsto (fun z => angularPole p z (planeRotation z)) (cocompact Plane) (𝓝 1) := by
  have hl : Tendsto (fun z => 1 + angularPole p z (planeRotation p)) (cocompact Plane) (𝓝 1) := by
    simpa using (angularPole_tendsto_fixed p (planeRotation p)).const_add 1
  apply hl.congr'
  filter_upwards [(isCompact_singleton (x := p)).compl_mem_cocompact] with z hz
  have hz' : z ≠ p := hz
  have he : planeRotation z = planeRotation (z-p) + planeRotation p := by
    ext <;> simp [planeRotation]
    ring
  rw [he,map_add]
  change 1 + angularOneForm (z-p) (planeRotation p) =
    angularOneForm (z-p) (planeRotation (z-p)) + angularOneForm (z-p) (planeRotation p)
  rw [angularOneForm_rotation (sub_ne_zero.mpr hz')]

theorem poleSum_smoothAt {P : Finset Plane} (c : Plane → ℝ) {z : Plane} (hz : z ∉ P) :
    ContDiffAt ℝ ∞ (poleSum P c) z := by
  apply ContDiffAt.sum
  intro p hp
  exact (contDiffAt_const (c := c p)).smul (angularPole_smoothAt (by rintro rfl; exact hz hp))

theorem poleSum_curl {P : Finset Plane} (c : Plane → ℝ) {z : Plane} (hz : z ∉ P) :
    planarCurl (poleSum P c) z = 0 := by
  unfold poleSum
  rw [planarCurl_sum P (α := fun p z => c p • angularPole p z) (fun p hp =>
    ((contDiffAt_const (c := c p)).smul (angularPole_smoothAt
      (by rintro rfl; exact hz hp))).differentiableAt (by simp))]
  apply Finset.sum_eq_zero
  intro p hp
  rw [planarCurl_const_smul,angularPole_curl (by rintro rfl; exact hz hp),mul_zero]

theorem poleSum_tendsto_rotation (P : Finset Plane) (c : Plane → ℝ) :
    Tendsto (fun z => poleSum P c z (planeRotation z)) (cocompact Plane) (𝓝 (∑ p ∈ P, c p)) := by
  have hl := tendsto_finsetSum P (fun p _ => (angularPole_tendsto_rotation p).const_mul (c p))
  simpa only [poleSum,sum_apply,smul_apply,smul_eq_mul,mul_one] using hl




theorem smooth_fill_finite (P : Finset Plane) (α : Plane → Plane →L[ℝ] ℝ)
    (hα : ∀ z, z ∉ P → ContDiffAt ℝ ∞ α z)
    (hlocal : ∀ p ∈ P, ∃ β : Plane → Plane →L[ℝ] ℝ,
      ContDiffAt ℝ ∞ β p ∧ α =ᶠ[𝓝[≠] p] β) :
    ∃ F : Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ F ∧ ∀ z, z ∉ P → F z = α z := by
  classical
  choose β hβs hβe using hlocal
  let F : Plane → Plane →L[ℝ] ℝ := fun z => if hz : z ∈ P then β z hz z else α z
  refine ⟨F,contDiff_iff_contDiffAt.mpr ?_,fun z hz => dite_eq_right hz⟩
  intro p
  by_cases hp : p ∈ P
  · have hP : ∀ᶠ z in 𝓝 p, z ∈ P → z = p := by
      have hn : p ∈ ((P.erase p : Finset Plane) : Set Plane)ᶜ := by simp
      filter_upwards [(P.erase p).finite_toSet.isClosed.isOpen_compl.mem_nhds hn] with z hz hzP
      by_contra hzp
      exact hz (Finset.mem_erase.mpr ⟨hzp,hzP⟩)
    have he : F =ᶠ[𝓝 p] β p hp := by
      filter_upwards [hP,eventually_nhdsWithin_iff.mp (hβe p hp)] with z hz hez
      by_cases hzp : z = p
      · subst z
        simp only [F,dite_eq_left hp]
      · have hzP : z ∉ P := fun h => hzp (hz h)
        simp only [F,dite_eq_right hzP]
        exact hez hzp
    exact (hβs p hp).congr_of_eventuallyEq he
  · have he : F =ᶠ[𝓝 p] α := by
      filter_upwards [P.finite_toSet.isClosed.isOpen_compl.mem_nhds hp] with z hz
      exact dite_eq_right hz
    exact (hα p hp).congr_of_eventuallyEq he

theorem finite_residues_le_infinity (P : Finset Plane) (c : Plane → ℝ)
    (α : Plane → Plane →L[ℝ] ℝ)
    (hα : ∀ z, z ∉ P → ContDiffAt ℝ ∞ α z)
    (hcurl : ∀ z, z ∉ P → 0 ≤ planarCurl α z)
    (hres : ∀ p ∈ P, ∃ β : Plane → Plane →L[ℝ] ℝ, ContDiffAt ℝ ∞ β p ∧
      α =ᶠ[𝓝[≠] p] fun z => c p • angularPole p z + β z)
    {k : ℝ} (hlim : Tendsto (fun z => α z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    (∑ p ∈ P, c p) ≤ k := by
  classical
  let γ : Plane → Plane →L[ℝ] ℝ := fun z => α z - poleSum P c z
  have hγs : ∀ z, z ∉ P → ContDiffAt ℝ ∞ γ z := fun z hz =>
    (hα z hz).sub (poleSum_smoothAt c hz)
  have hγlocal : ∀ p ∈ P, ∃ β : Plane → Plane →L[ℝ] ℝ,
      ContDiffAt ℝ ∞ β p ∧ γ =ᶠ[𝓝[≠] p] β := by
    intro p hp
    obtain ⟨β,hβs,hβe⟩ := hres p hp
    refine ⟨fun z => β z - poleSum (P.erase p) c z,
      hβs.sub (poleSum_smoothAt c (by simp)),?_⟩
    filter_upwards [hβe] with z hz
    have hsum : poleSum P c z = c p • angularPole p z + poleSum (P.erase p) c z :=
      (Finset.add_sum_erase P (fun q => c q • angularPole q z) hp).symm
    dsimp only [γ]
    rw [hz,hsum]
    abel
  obtain ⟨F,hFs,hFe⟩ := smooth_fill_finite P γ hγs hγlocal
  have hFnear (z : Plane) (hz : z ∉ P) : F =ᶠ[𝓝 z] γ := by
    filter_upwards [P.finite_toSet.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact hFe y hy
  have hFc : ∀ z, z ∉ P → 0 ≤ planarCurl F z := by
    intro z hz
    rw [planarCurl_congr (hFnear z hz)]
    change 0 ≤ planarCurl (fun y => α y - poleSum P c y) z
    rw [planarCurl_sub ((hα z hz).differentiableAt (by simp))
      ((poleSum_smoothAt c hz).differentiableAt (by simp)),poleSum_curl c hz,sub_zero]
    exact hcurl z hz
  have hFcAll : ∀ z, 0 ≤ planarCurl F z := by
    have hd : Dense ((P : Set Plane)ᶜ) := by
      convert dense_univ.sdiff_finset P using 1
      all_goals try with_reducible_and_instances rfl
      ext z
      simp only [mem_compl_iff,Set.mem_sdiff,mem_univ,true_and,Finset.mem_coe]
    have hc : IsClosed {z : Plane | 0 ≤ planarCurl F z} :=
      isClosed_le continuous_const (planarCurl_contDiff hFs).continuous
    have hs : closure ((P : Set Plane)ᶜ) ⊆ {z : Plane | 0 ≤ planarCurl F z} :=
      closure_minimal (fun z hz => hFc z hz) hc
    intro z
    apply hs
    rw [hd.closure_eq]
    exact mem_univ z
  have hFlim : Tendsto (fun z => F z (planeRotation z)) (cocompact Plane)
      (𝓝 (k - ∑ p ∈ P, c p)) := by
    apply (hlim.sub (poleSum_tendsto_rotation P c)).congr'
    filter_upwards [P.finite_toSet.isCompact.compl_mem_cocompact] with z hz
    rw [hFe z hz]
    rfl
  exact sub_nonneg.mp (nonneg_angular_limit_of_nonneg_curl hFs hFcAll hFlim)


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)

theorem realCurve_translate {n : ℕ} (v : ℂ → Phase n) (a : ℂ) :
    realCurve (fun z => v (z+a)) = fun z => realCurve v (z+Complex.equivRealProdCLM a) := by
  funext z
  simp only [realCurve,Function.comp_def,map_add,ContinuousLinearEquiv.symm_apply_apply]

theorem planarPullback_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Plane → E) (α : E → E →L[ℝ] ℝ) (a z : Plane) :
    planarPullback (fun y => v (y+a)) α z = planarPullback v α (z+a) := by
  simp only [planarPullback,fderiv_comp_add_right]

theorem tendsto_sub_punctured (p : Plane) :
    Tendsto (fun z : Plane => z-p) (𝓝[≠] p) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have ht : Tendsto (fun z : Plane => z-p) (𝓝 p) (𝓝 (p-p)) :=
      (continuous_id.sub continuous_const).continuousAt.tendsto
    simpa only [sub_self] using ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_ne_zero.mpr hz

theorem blowup_branch_residue_at {n : ℕ} {v h : ℂ → Phase n} {m : ℕ} {a : ℂ}
    (hm : 0 < m) (hh : AnalyticAt ℂ h a) (hh0 : h a ≠ 0)
    (he : v =ᶠ[𝓝 a] fun z : ℂ => (z-a)^m • h z)
    {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) :
    ∃ β : Plane → Plane →L[ℝ] ℝ, ContDiffAt ℝ ∞ β (Complex.equivRealProdCLM a) ∧
      ∀ᶠ z in 𝓝[≠] (Complex.equivRealProdCLM a),
        planarPullback (realCurve v) (blowupPrimitive σ τ) z =
          ((blowupSize σ τ * (m:ℝ)) / (2 * Real.pi)) • angularPole (Complex.equivRealProdCLM a) z + β z := by
  have ht : Tendsto (fun z : ℂ => z+a) (𝓝 0) (𝓝 a) := by
    have ht : Tendsto (fun z : ℂ => z+a) (𝓝 0) (𝓝 (0+a)) :=
      (continuous_id.add continuous_const).continuousAt.tendsto
    simpa only [zero_add] using ht
  have hh' : AnalyticAt ℂ (fun z : ℂ => h (z+a)) 0 := by
    have hh1 : AnalyticAt ℂ h (0+a) := by simpa only [zero_add] using hh
    exact hh1.comp (f := fun z : ℂ => z+a) (analyticAt_id.add analyticAt_const)
  have hh0' : (fun z : ℂ => h (z+a)) 0 ≠ 0 := by simpa using hh0
  have he' : (fun z : ℂ => v (z+a)) =ᶠ[𝓝 0] fun z : ℂ => z^m • h (z+a) := by
    filter_upwards [ht.eventually he] with z hz
    simpa only [add_sub_cancel_right] using hz
  obtain ⟨β,hβs,hβe⟩ := blowup_branch_residue hm hh' hh0' he' hσ hστ
  let p := Complex.equivRealProdCLM a
  refine ⟨fun z => β (z-p),?_,?_⟩
  · have hh : ContDiffAt ℝ ∞ β (p-p) := by simpa only [sub_self] using hβs
    have hs : ContDiffAt ℝ ∞ (fun z : Plane => z-p) p :=
      contDiffAt_id.sub contDiffAt_const
    exact hh.comp p (f := fun z : Plane => z-p) hs
  · filter_upwards [(tendsto_sub_punctured p).eventually hβe] with z hz
    rw [realCurve_translate,planarPullback_translate,sub_add_cancel] at hz
    exact hz


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

theorem correctedPrimitive_smoothAt {n : ℕ} {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    {y : Phase n} (hy : ∀ i, y ≠ f i 0) :
    ContDiffAt ℝ ∞ (correctedPrimitive S T U f σ τ) y :=
  ((radialPrimitiveCLM_smooth hST).contDiffAt.add
    (chartCorrection_smoothAt (hf 0) (hτ 0) (hστ 0) (hsub 0) (hy 0))).add
    (chartCorrection_smoothAt (hf 1) (hτ 1) (hστ 1) (hsub 1) (hy 1))

theorem chartCorrection_extDeriv_zero {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U)
    {y : Phase n} (hy : y ∉ f '' closedBall n τ) (v w : Phase n) :
    extDeriv (oneForm (chartCorrection U f σ τ)) y ![v,w] = 0 := by
  rw [oneForm_extDeriv_congr (chartCorrection_zero_near hf hτ hστ hsub hy)]
  change extDeriv (oneForm (fun _ : Phase n => (0 : Phase n →L[ℝ] ℝ))) y ![v,w] = 0
  rw [oneForm_extDeriv_apply (differentiableAt_const _)]
  simp

theorem correctedPrimitive_extDeriv {n : ℕ} {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    {y : Phase n} (hy : ∀ i, y ≠ f i 0) (v w : Phase n) :
    extDeriv (oneForm (correctedPrimitive S T U f σ τ)) y ![v,w] =
      radialForm S T y v w +
      extDeriv (oneForm (chartCorrection (U 0) (f 0) (σ 0) (τ 0))) y ![v,w] +
      extDeriv (oneForm (chartCorrection (U 1) (f 1) (σ 1) (τ 1))) y ![v,w] := by
  have hr := (radialPrimitiveCLM_smooth hST).differentiable (by simp) y
  have hc (i : Fin 2) :=
    (chartCorrection_smoothAt (hf i) (hτ i) (hστ i) (hsub i) (hy i)).differentiableAt (by simp)
  unfold correctedPrimitive
  rw [oneForm_extDeriv_add (hr.fun_add (hc 0)) (hc 1),
    oneForm_extDeriv_add hr (hc 0)]
  have he : oneForm (@radialPrimitiveCLM n S T) = radialPrimitive S T := rfl
  rw [he,radialForm_extDeriv hST]

theorem radialForm_adapted_nonneg {n : ℕ} {S T : ℝ} (hST : S < T) (hT : T < 1)
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n) (x v : Phase n) :
    0 ≤ radialForm S T x v (J x v) := by
  by_cases hv : v = 0
  · subst v
    simp [radialForm,standardForm,stdDot]
  · exact (radialForm_adapted_pos hST hT hJ hout x hv).le

theorem correctedPrimitive_extDeriv_nonneg {n : ℕ} {S T : ℝ}
    (hST : S < T) (hT : T < 1)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hdis : Disjoint (f 0 '' closedBall n (τ 0)) (f 1 '' closedBall n (τ 1)))
    (hcap : ∀ i, MapsTo (f i) (closedBall n (τ i)) (closedBall n S))
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n)
    (hJi : ∀ i, ∀ y ∈ f i '' closedBall n (τ i), J y = imageJ (U i) (f i) y)
    {y : Phase n} (hy : ∀ i, y ≠ f i 0) (v : Phase n) :
    0 ≤ extDeriv (oneForm (correctedPrimitive S T U f σ τ)) y ![v,J y v] := by
  rw [correctedPrimitive_extDeriv hST hf hτ hστ hsub hy]
  have hloc (i : Fin 2) (hi : y ∈ f i '' closedBall n (τ i)) :
      radialForm S T y v (J y v) +
        extDeriv (oneForm (chartCorrection (U i) (f i) (σ i) (τ i))) y ![v,J y v] ≥ 0 := by
    have hU : y ∈ f i '' U i := image_mono (hsub i) hi
    have hσy : y ∈ closedBall n S := by
      obtain ⟨x,hx,rfl⟩ := hi
      exact hcap i hx
    have hx : invFunOn (f i) (U i) y ≠ 0 := by
      intro he
      have hi := invFunOn_eq hU
      rw [he] at hi
      exact hy i hi.symm
    rw [radialForm_standard hST hσy,chartCorrection_extDeriv (hf i) hU (hy i),
      hJi i y hi,inverse_fderiv_intertwines (hf i) hU]
    have hn := blowupPrimitive_extDeriv_nonneg (hστ i) hx
      (fderiv ℝ (invFunOn (f i) (U i)) y v)
    linarith only [hn]
  by_cases h0 : y ∈ f 0 '' closedBall n (τ 0)
  · have h1 : y ∉ f 1 '' closedBall n (τ 1) := fun h => disjoint_left.mp hdis h0 h
    rw [chartCorrection_extDeriv_zero (hf 1) (hτ 1) (hστ 1) (hsub 1) h1,add_zero]
    exact hloc 0 h0
  · rw [chartCorrection_extDeriv_zero (hf 0) (hτ 0) (hστ 0) (hsub 0) h0,add_zero]
    by_cases h1 : y ∈ f 1 '' closedBall n (τ 1)
    · exact hloc 1 h1
    · rw [chartCorrection_extDeriv_zero (hf 1) (hτ 1) (hστ 1) (hsub 1) h1,add_zero]
      exact radialForm_adapted_nonneg hST hT hJ hout y v

theorem correctedCurve_curl_nonneg {n : ℕ} {S T : ℝ}
    (hST : S < T) (hT : T < 1)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hdis : Disjoint (f 0 '' closedBall n (τ 0)) (f 1 '' closedBall n (τ 1)))
    (hcap : ∀ i, MapsTo (f i) (closedBall n (τ i)) (closedBall n S))
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n)
    (hJi : ∀ i, ∀ y ∈ f i '' closedBall n (τ i), J y = imageJ (U i) (f i) y)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (hCR : ∀ z, PseudoHolomorphicAt J u z)
    {z : Plane} (hz : ∀ i, realCurve u z ≠ f i 0) :
    0 ≤ planarCurl (planarPullback (realCurve u) (correctedPrimitive S T U f σ τ)) z := by
  rw [planarPullback_curlAt (realCurve_smooth hu).contDiffAt
    (correctedPrimitive_smoothAt hST hf hτ hστ hsub hz),realCurve_CR (hCR _)]
  exact correctedPrimitive_extDeriv_nonneg hST hT hf hτ hστ hsub hdis hcap hJ hout hJi hz _


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)

theorem inversePullback_sub {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n)
    (α β : Phase n → Phase n →L[ℝ] ℝ) (y : Phase n) :
    inversePullback U f (fun x => α x - β x) y =
      inversePullback U f α y - inversePullback U f β y := by
  simp only [inversePullback,ContinuousLinearMap.sub_comp]

theorem correctedPrimitive_centre_remainder {n : ℕ} {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hne : f 0 0 ≠ f 1 0) (i : Fin 2) :
    ∃ γ : Phase n → Phase n →L[ℝ] ℝ, ContDiffAt ℝ ∞ γ (f i 0) ∧
      correctedPrimitive S T U f σ τ =ᶠ[𝓝 (f i 0)]
        fun y => inversePullback (U i) (f i) (blowupPrimitive (σ i) (τ i)) y + γ y := by
  have h0 (j : Fin 2) : (0 : Phase n) ∈ U j := hsub j (by simpa [closedBall,capacity] using (hτ j).le)
  have hmem (j : Fin 2) : f j 0 ∈ f j '' U j := mem_image_of_mem _ (h0 j)
  have hs (j : Fin 2) : ContDiffAt ℝ ∞ (inversePullback (U j) (f j) stdPrimitive) (f j 0) :=
    inversePullback_smoothAt (hf j) (hmem j) (stdPrimitive_smooth n).contDiffAt
  fin_cases i
  · refine ⟨fun y => radialPrimitiveCLM S T y + chartCorrection (U 1) (f 1) (σ 1) (τ 1) y -
        inversePullback (U 0) (f 0) stdPrimitive y,?_,?_⟩
    · exact ((radialPrimitiveCLM_smooth hST).contDiffAt.add
        (chartCorrection_smoothAt (hf 1) (hτ 1) (hστ 1) (hsub 1) hne)).sub (hs 0)
    · filter_upwards [chartCorrection_eq_near (hf 0) (hmem 0) (σ 0) (τ 0)] with y hy
      simp only [Fin.mk_zero,correctedPrimitive,hy,inversePullback_sub]
      ext w
      simp only [add_apply,sub_apply]
      ring
  · refine ⟨fun y => radialPrimitiveCLM S T y + chartCorrection (U 0) (f 0) (σ 0) (τ 0) y -
        inversePullback (U 1) (f 1) stdPrimitive y,?_,?_⟩
    · exact ((radialPrimitiveCLM_smooth hST).contDiffAt.add
        (chartCorrection_smoothAt (hf 0) (hτ 0) (hστ 0) (hsub 0) hne.symm)).sub (hs 1)
    · filter_upwards [chartCorrection_eq_near (hf 1) (hmem 1) (σ 1) (τ 1)] with y hy
      simp only [Fin.mk_one,correctedPrimitive,hy,inversePullback_sub]
      ext w
      simp only [add_apply,sub_apply]
      ring

theorem planarPullback_inverse {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f)
    {u : ℂ → Phase n} {z : Plane} (hu : DifferentiableAt ℝ (realCurve u) z)
    (hz : realCurve u z ∈ f '' U) (α : Phase n → Phase n →L[ℝ] ℝ) :
    planarPullback (realCurve u) (inversePullback U f α) z =
      planarPullback (realCurve (invFunOn f U ∘ u)) α z := by
  have hd := ((symplecticOn_inverse_smooth hf).contDiffAt
    ((symplecticOn_open_image hf).mem_nhds hz)).differentiableAt (by simp)
  have hc : realCurve (invFunOn f U ∘ u) = invFunOn f U ∘ realCurve u := rfl
  rw [hc]
  unfold planarPullback inversePullback
  rw [fderiv_comp z hd hu]
  rfl

theorem correctedPrimitive_centre_residue {n : ℕ} {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hσ : ∀ i, 0 < σ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hne : f 0 0 ≠ f 1 0)
    {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u)
    (hJ : ∀ i, ∀ᶠ y in 𝓝 (f i 0), J y = imageJ (U i) (f i) y)
    (i : Fin 2) {a : ℂ} (ha : u a = f i 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ β : Plane → Plane →L[ℝ] ℝ,
      ContDiffAt ℝ ∞ β (Complex.equivRealProdCLM a) ∧
      ∀ᶠ z in 𝓝[≠] (Complex.equivRealProdCLM a),
        planarPullback (realCurve u) (correctedPrimitive S T U f σ τ) z =
          ((blowupSize (σ i) (τ i) * (m:ℝ)) / (2 * Real.pi)) •
            angularPole (Complex.equivRealProdCLM a) z + β z := by
  have hτ (j : Fin 2) : 0 < τ j := (hσ j).trans (hστ j)
  have h0 (j : Fin 2) : (0 : Phase n) ∈ U j := hsub j (by simpa [closedBall,capacity] using (hτ j).le)
  obtain ⟨m,v,hm,hvs,hv0,hve⟩ := chart_centre_positive_order (hf i) (h0 i) hu.2.1
    (hu.not_constant _) (hJ i) ha
  obtain ⟨β,hβs,hβe⟩ := blowup_branch_residue_at hm hvs hv0 hve (hσ i) (hστ i)
  obtain ⟨γ,hγs,hγe⟩ := correctedPrimitive_centre_remainder hST hf hτ hστ hsub hne i
  let b := Complex.equivRealProdCLM a
  have hb : realCurve u b = f i 0 := by
    change u (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM a)) = f i 0
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ha
  have hus := realCurve_smooth hu.1
  have hpbγ : ContDiffAt ℝ ∞ (planarPullback (realCurve u) γ) b :=
    planarPullback_smoothAt hus.contDiffAt (hb.symm ▸ hγs)
  refine ⟨m,hm,fun z => β z + planarPullback (realCurve u) γ z,hβs.add hpbγ,?_⟩
  have hut : Tendsto (realCurve u) (𝓝 b) (𝓝 (f i 0)) := hb ▸ hus.continuous.tendsto b
  have him : ∀ᶠ z in 𝓝 b, realCurve u z ∈ f i '' U i := hut.eventually
    ((symplecticOn_open_image (hf i)).mem_nhds (mem_image_of_mem _ (h0 i)))
  filter_upwards [hβe,(hut.eventually hγe).filter_mono nhdsWithin_le_nhds,
    him.filter_mono nhdsWithin_le_nhds] with z hzz hγz hiz
  have he : planarPullback (realCurve u) (correctedPrimitive S T U f σ τ) z =
      planarPullback (realCurve u) (inversePullback (U i) (f i) (blowupPrimitive (σ i) (τ i))) z +
      planarPullback (realCurve u) γ z := by
    unfold planarPullback
    rw [hγz,ContinuousLinearMap.add_comp]
  rw [he,planarPullback_inverse (hf i) (hus.differentiable (by simp) z) hiz,hzz]
  abel


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)

theorem complex_inv_fderiv_real {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    fderiv ℝ (fun y : ℂ => y⁻¹) z w = -(z^2)⁻¹ * w := by
  rw [((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ).fderiv]
  change w * (-(z^2)⁻¹) = _
  ring

theorem infinity_curve_fderiv {n : ℕ} {h : ℂ → Phase n} {z : ℂ}
    (hz : z ≠ 0) (hh : DifferentiableAt ℝ h z⁻¹) (w : ℂ) :
    fderiv ℝ (fun y : ℂ => y • h y⁻¹) z w =
      w • h z⁻¹ + z • fderiv ℝ h z⁻¹ (-(z^2)⁻¹ * w) := by
  have hi : DifferentiableAt ℝ (fun y : ℂ => y⁻¹) z :=
    (hasDerivAt_inv hz).differentiableAt.restrictScalars ℝ
  have hid : DifferentiableAt ℝ (fun y : ℂ => y) z := differentiableAt_id
  have hcomp : DifferentiableAt ℝ (fun y : ℂ => h y⁻¹) z := hh.comp z hi
  rw [fderiv_fun_smul hid hcomp]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,fderiv_fun_id,
    ContinuousLinearMap.id_apply]
  have hder : HasFDerivAt (fun y : ℂ => h y⁻¹)
      ((fderiv ℝ h z⁻¹).comp (fderiv ℝ (fun y : ℂ => y⁻¹) z)) z :=
    hh.hasFDerivAt.comp z hi.hasFDerivAt
  rw [hder.fderiv,ContinuousLinearMap.comp_apply,complex_inv_fderiv_real hz]
  module

theorem normalizedPrimitive_infinity_curve {n : ℕ} {h : ℂ → Phase n} {z : ℂ}
    (hz : z ≠ 0) (hh : DifferentiableAt ℝ h z⁻¹) (hh0 : h z⁻¹ ≠ 0) :
    normalizedPrimitive (z • h z⁻¹) (fderiv ℝ (fun y : ℂ => y • h y⁻¹) z (Complex.I*z)) =
      1 / (2 * Real.pi) +
      normalizedPrimitive (h z⁻¹) (fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)) := by
  rw [infinity_curve_fderiv hz hh,normalizedPrimitive_smul hz hh0]
  have h1 : z⁻¹ * (Complex.I*z) = Complex.I := by field_simp
  have h2 : -(z^2)⁻¹ * (Complex.I*z) = -Complex.I*z⁻¹ := by field_simp
  rw [h1,h2,Complex.I_im]

theorem infinityGerm_curve_eventuallyEq {n : ℕ} (u : ℂ → Phase n) (v : Phase n) :
    u =ᶠ[cocompact ℂ] fun z : ℂ => z • infinityGerm u v z⁻¹ := by
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz' : z ≠ 0 := hz
  simp only [infinityGerm,inv_ne_zero hz',ite_false,inv_inv,smul_smul,
    mul_inv_cancel₀ hz',one_smul]

theorem normalizedPrimitive_infinity_limit {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hv : v ≠ 0) (hh : AnalyticAt ℂ (infinityGerm u v) 0) :
    Tendsto (fun z : ℂ => normalizedPrimitive (u z) (fderiv ℝ u z (Complex.I*z)))
      (cocompact ℂ) (𝓝 (1 / (2 * Real.pi))) := by
  let h := infinityGerm u v
  have hh0 : h 0 ≠ 0 := by simpa [h,infinityGerm] using hv
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hc : ContDiffAt ℝ ∞ h 0 := hh.contDiffAt.restrict_scalars ℝ
  have hdh : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹) (cocompact ℂ) (𝓝 (fderiv ℝ h 0)) :=
    (hc.fderiv_right (m := 0) (by simp)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hvec : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def,map_zero] using (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdh.prodMk_nhds harg)
  have hprim : Tendsto (fun z : ℂ => normalizedPrimitive (h z⁻¹))
      (cocompact ℂ) (𝓝 (normalizedPrimitive (h 0))) :=
    (normalizedPrimitive_smoothAt hh0).continuousAt.tendsto.comp (hc.continuousAt.tendsto.comp hi)
  have hl : Tendsto (fun z : ℂ => 1 / (2 * Real.pi) +
      normalizedPrimitive (h z⁻¹) (fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)))
      (cocompact ℂ) (𝓝 (1 / (2 * Real.pi))) := by
    simpa only [Function.comp_def,map_zero,add_zero] using ((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hprim.prodMk_nhds hvec)).const_add (1 / (2 * Real.pi))
  apply hl.congr'
  have he := infinityGerm_curve_eventuallyEq u v
  have hnear : ∀ᶠ z in cocompact ℂ, u =ᶠ[𝓝 z] fun y : ℂ => y • h y⁻¹ := by
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with y hy
    have hy' : y ≠ 0 := hy
    simp only [h,infinityGerm,inv_ne_zero hy',ite_false,inv_inv,smul_smul,
      mul_inv_cancel₀ hy',one_smul]
  have hn : ∀ᶠ w in 𝓝 (0:ℂ), h w ≠ 0 :=
    hc.continuousAt.eventually (isClosed_singleton.isOpen_compl.mem_nhds hh0)
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ h w :=
    hh.eventually_analyticAt.mono fun _ hx => hx.differentiableAt.restrictScalars ℝ
  filter_upwards [hnear,hi.eventually hn,hi.eventually hd,
    (isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hez hnz hdz hz
  rw [hez.self_of_nhds,hez.fderiv_eq]
  exact (normalizedPrimitive_infinity_curve hz hdz hnz).symm

theorem equivRealProd_rotation (z : Plane) :
    Complex.equivRealProdCLM.symm (planeRotation z) =
      Complex.I * Complex.equivRealProdCLM.symm z := by
  apply Complex.ext <;> simp [planeRotation,Complex.equivRealProdCLM_symm_apply]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CorrectedInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)

theorem radialPrimitiveCLM_eq_moment {n : ℕ} (S T : ℝ) {x : Phase n}
    (hx : x ≠ 0) :
    radialPrimitiveCLM S T x = radialMoment S T (capacity x) • normalizedPrimitive x := by
  unfold radialPrimitiveCLM normalizedPrimitive radialMoment
  rw [smul_smul]
  congr 1
  have hn := (capacity_pos hx).ne'
  field_simp

theorem capacity_tendsto_atTop (n : ℕ) :
    Tendsto (@capacity n) (cocompact (Phase n)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(closedBall_isCompact n b).compl_mem_cocompact] with x hx
  have hx' : ¬ capacity x ≤ b := hx
  exact (lt_of_not_ge hx').le

theorem AffineLineCurve.radial_infinity_limit {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {S T : ℝ} (hST : S < T) :
    Tendsto (fun z : Plane => planarPullback (realCurve u) (radialPrimitiveCLM S T) z
      (planeRotation z)) (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
  obtain ⟨v,hv,hh,_⟩ := hu.analytic_at_infinity hJc
  have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hul : Tendsto (realCurve u) (cocompact Plane) (cocompact (Phase n)) :=
    hu.tendsto_cocompact.comp hr
  have hn : Tendsto (fun z : Plane => planarPullback (realCurve u) normalizedPrimitive z
      (planeRotation z)) (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
    have ht := (normalizedPrimitive_infinity_limit hv hh).comp hr
    apply ht.congr
    intro z
    change normalizedPrimitive _ _ = normalizedPrimitive _ _
    have he := realCurve_fderiv (z := z) ((hu.1.differentiable (by simp)) _) (planeRotation z)
    rw [equivRealProd_rotation] at he
    exact congrArg (normalizedPrimitive (u (Complex.equivRealProdCLM.symm z))) he.symm
  have hm : Tendsto (fun z : Plane => radialMoment S T (capacity (realCurve u z)))
      (cocompact Plane) (𝓝 1) :=
    (radialMoment_tendsto_one hST).comp ((capacity_tendsto_atTop n).comp hul)
  have ht : Tendsto (fun z : Plane => radialMoment S T (capacity (realCurve u z)) *
      planarPullback (realCurve u) normalizedPrimitive z (planeRotation z))
      (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
    simpa only [one_mul] using hm.mul hn
  apply ht.congr'
  filter_upwards [hul.eventually (isCompact_singleton (x := (0 : Phase n))).compl_mem_cocompact] with z hz
  unfold planarPullback
  rw [radialPrimitiveCLM_eq_moment S T hz]
  rfl

theorem correctedPrimitive_eq_radial_at_infinity {n : ℕ} (S T : ℝ)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i) :
    correctedPrimitive S T U f σ τ =ᶠ[cocompact (Phase n)] radialPrimitiveCLM S T := by
  have hc (i : Fin 2) := chartCorrection_compact (hf i) (hτ i) (hστ i) (hsub i)
  filter_upwards [(hc 0).compl_mem_cocompact,(hc 1).compl_mem_cocompact] with y hy0 hy1
  have h0 := image_eq_zero_of_notMem_tsupport hy0
  have h1 := image_eq_zero_of_notMem_tsupport hy1
  simp only [correctedPrimitive,h0,h1,add_zero]

theorem AffineLineCurve.corrected_infinity_limit {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i) :
    Tendsto (fun z : Plane => planarPullback (realCurve u) (correctedPrimitive S T U f σ τ) z
      (planeRotation z)) (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
  apply (hu.radial_infinity_limit hJc hST).congr'
  have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hul : Tendsto (realCurve u) (cocompact Plane) (cocompact (Phase n)) :=
    hu.tendsto_cocompact.comp hr
  filter_upwards [hul.eventually (correctedPrimitive_eq_radial_at_infinity S T hf hτ hστ hsub)] with z hz
  unfold planarPullback
  rw [hz]


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

theorem AffineLineCurve.finite_real_centre_fibre {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y) :
    Set.Finite {z : Plane | realCurve u z = f 0} :=
  (hu.finite_centre_fibre hf h0 hJ).preimage Complex.equivRealProdCLM.symm.injective.injOn

theorem two_ball_line_area {n : ℕ} {S T : ℝ} (hST : S < T) (hT : T < 1)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hσ : ∀ i, 0 < σ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hdis : Disjoint (f 0 '' closedBall n (τ 0)) (f 1 '' closedBall n (τ 1)))
    (hcap : ∀ i, MapsTo (f i) (closedBall n (τ i)) (closedBall n S))
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n)
    (hJi : ∀ i, ∀ y ∈ f i '' closedBall n (τ i), J y = imageJ (U i) (f i) y)
    (hJnear : ∀ i, ∀ᶠ y in 𝓝 (f i 0), J y = imageJ (U i) (f i) y)
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {u : ℂ → Phase n} (hu : AffineLineCurve J (f 0 0) (f 1 0) u) :
    blowupSize (σ 0) (τ 0) + blowupSize (σ 1) (τ 1) ≤ 1 := by
  classical
  have hτ (i : Fin 2) : 0 < τ i := (hσ i).trans (hστ i)
  have hball0 (i : Fin 2) : (0 : Phase n) ∈ closedBall n (τ i) := by
    simpa [closedBall,capacity] using (hτ i).le
  have hne : f 0 0 ≠ f 1 0 := by
    intro he
    exact disjoint_left.mp hdis (mem_image_of_mem _ (hball0 0))
      (he.symm ▸ mem_image_of_mem (f 1) (hball0 1))
  have hfin (i : Fin 2) : Set.Finite {z : Plane | realCurve u z = f i 0} :=
    hu.finite_real_centre_fibre (hf i) (hsub i (hball0 i)) (hJnear i)
  let P := ((hfin 0).union (hfin 1)).toFinset
  have hP (z : Plane) : z ∈ P ↔ realCurve u z = f 0 0 ∨ realCurve u z = f 1 0 := by
    simp only [P,Set.Finite.mem_toFinset,Set.mem_union,Set.mem_ofPred_eq]
  let idx (z : Plane) : Fin 2 := if realCurve u z = f 0 0 then 0 else 1
  have hidx (z : Plane) (hz : z ∈ P) : realCurve u z = f (idx z) 0 := by
    unfold idx
    split_ifs with h
    · exact h
    · exact ((hP z).mp hz).resolve_left h
  let α := planarPullback (realCurve u) (correctedPrimitive S T U f σ τ)
  have hres (z : Plane) (hz : z ∈ P) : ∃ m : ℕ, 0 < m ∧
      ∃ β : Plane → Plane →L[ℝ] ℝ, ContDiffAt ℝ ∞ β z ∧
        α =ᶠ[𝓝[≠] z] fun w => ((blowupSize (σ (idx z)) (τ (idx z)) * (m:ℝ)) /
          (2 * Real.pi)) • angularPole z w + β w := by
    have hh := correctedPrimitive_centre_residue hST hf hσ hστ hsub hne hu hJnear
      (idx z) (a := Complex.equivRealProdCLM.symm z) (hidx z hz)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,α,Filter.EventuallyEq] using hh
  choose m hm β hβs hβe using hres
  let c (z : Plane) : ℝ := if hz : z ∈ P then
    blowupSize (σ (idx z)) (τ (idx z)) * (m z hz : ℝ) / (2 * Real.pi) else 0
  have hc (z : Plane) (hz : z ∈ P) :
      c z = blowupSize (σ (idx z)) (τ (idx z)) * (m z hz : ℝ) / (2 * Real.pi) := dite_eq_left hz
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hsize (i : Fin 2) : 0 < blowupSize (σ i) (τ i) :=
    (hσ i).trans_le (blowupSize_bounds (hστ i)).1
  have hcnon (z : Plane) : 0 ≤ c z := by
    by_cases hz : z ∈ P
    · rw [hc z hz]
      exact div_nonneg (mul_nonneg (hsize _).le (Nat.cast_nonneg _)) hpi.le
    · simp only [c,dite_eq_right hz,le_refl]
  have hclower (z : Plane) (hz : z ∈ P) :
      blowupSize (σ (idx z)) (τ (idx z)) / (2 * Real.pi) ≤ c z := by
    rw [hc z hz]
    apply div_le_div_of_nonneg_right _ hpi.le
    exact le_mul_of_one_le_right (hsize _).le (by exact_mod_cast (Nat.succ_le_iff.mpr (hm z hz)))
  have haway (z : Plane) (hz : z ∉ P) : ∀ i : Fin 2, realCurve u z ≠ f i 0 := by
    intro i
    fin_cases i
    · exact fun he => hz ((hP z).mpr (Or.inl he))
    · exact fun he => hz ((hP z).mpr (Or.inr he))
  have hsum : (∑ z ∈ P, c z) ≤ 1 / (2 * Real.pi) := by
    apply finite_residues_le_infinity P c α
    · intro z hz
      exact planarPullback_smoothAt (realCurve_smooth hu.1).contDiffAt
        (correctedPrimitive_smoothAt hST hf hτ hστ hsub (haway z hz))
    · intro z hz
      exact correctedCurve_curl_nonneg hST hT hf hτ hστ hsub hdis hcap hJ hout hJi
        hu.1 hu.2.1 (haway z hz)
    · intro z hz
      refine ⟨β z hz,hβs z hz,?_⟩
      rw [hc z hz]
      exact hβe z hz
    · exact hu.corrected_infinity_limit hJc hST hf hτ hστ hsub
  have hu0 : realCurve u 0 = f 0 0 := by simpa only [realCurve_zero] using hu.2.2.1
  have hu1 : realCurve u (1,0) = f 1 0 := by
    simpa only [realCurve,Function.comp_def,Complex.equivRealProdCLM_symm_apply,
      Complex.ofReal_one,Complex.ofReal_zero,zero_mul,add_zero] using hu.2.2.2.1
  have hp0 : (0 : Plane) ∈ P := (hP 0).mpr (Or.inl hu0)
  have hp1 : (1,0) ∈ P := (hP (1,0)).mpr (Or.inr hu1)
  have hi0 : idx 0 = 0 := ite_eq_left hu0
  have hi1 : idx (1,0) = 1 := ite_eq_right (by rw [hu1]; exact hne.symm)
  have hs01 : c 0 + c (1,0) ≤ ∑ z ∈ P, c z := by
    have hsubP : ({0,(1,0)} : Finset Plane) ⊆ P := by
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hp0
      · exact hp1
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsubP (fun z _ _ => hcnon z)
    have h01 : (0 : Plane) ≠ (1,0) := by
      intro he
      have hh := congrArg Prod.fst he
      norm_num at hh
    rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using h01),Finset.sum_singleton] at hs
    exact hs
  have hlow0 := hclower 0 hp0
  have hlow1 := hclower (1,0) hp1
  rw [hi0] at hlow0
  rw [hi1] at hlow1
  apply (div_le_div_iff_of_pos_right hpi).mp
  rw [add_div]
  linarith


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem two_ball_capacity_of_adapted_line {n : ℕ} {S T : ℝ} (hST : S < T) (hT : T < 1)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {r : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hr : ∀ i, 0 < r i)
    (hsub : ∀ i, closedBall n (r i) ⊆ U i)
    (hdis : Disjoint (f 0 '' closedBall n (r 0)) (f 1 '' closedBall n (r 1)))
    (hcap : ∀ i, MapsTo (f i) (closedBall n (r i)) (closedBall n S))
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n)
    (hJi : ∀ i, ∀ y ∈ f i '' closedBall n (r i), J y = imageJ (U i) (f i) y)
    (hJnear : ∀ i, ∀ᶠ y in 𝓝 (f i 0), J y = imageJ (U i) (f i) y)
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {u : ℂ → Phase n} (hu : AffineLineCurve J (f 0 0) (f 1 0) u) :
    r 0 + r 1 ≤ 1 := by
  by_contra! hlarge
  let δ := min (r 0) (min (r 1) (r 0 + r 1 - 1)) / 4
  have hδ : 0 < δ := div_pos (lt_min (hr 0) (lt_min (hr 1) (by linarith))) (by norm_num)
  have hδ0 : 4*δ ≤ r 0 := by
    dsimp [δ]
    linarith only [min_le_left (r 0) (min (r 1) (r 0+r 1-1))]
  have hδ1 : 4*δ ≤ r 1 := by
    have h := (min_le_right (r 0) (min (r 1) (r 0+r 1-1))).trans
      (min_le_left (r 1) (r 0+r 1-1))
    dsimp [δ]
    linarith only [h]
  have hδsum : 4*δ ≤ r 0+r 1-1 := by
    have h := (min_le_right (r 0) (min (r 1) (r 0+r 1-1))).trans
      (min_le_right (r 1) (r 0+r 1-1))
    dsimp [δ]
    linarith only [h]
  have hσ (i : Fin 2) : 0 < r i - δ := by
    fin_cases i <;> simp only [Fin.mk_zero,Fin.mk_one] <;> linarith
  have hστ (i : Fin 2) : r i - δ < r i := by linarith
  have harea := two_ball_line_area hST hT hf hσ hστ hsub hdis hcap hJ hout hJi hJnear hJc hu
  have h0 := (blowupSize_bounds (hστ 0)).1
  have h1 := (blowupSize_bounds (hστ 1)).1
  linarith




theorem packing_two_line_reduction_oai {n : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp : HasPacking n 2 1 ![a,b]) :
    ∃ (J : Phase n → End n) (p q : Phase n), ContDiff ℝ ∞ J ∧
      (∀ x, Compatible (J x)) ∧ HasCompactSupport (fun x => J x - standardJ n) ∧
      tsupport (fun x => J x - standardJ n) ⊆ openBall n 1 ∧ p ≠ q ∧
      ∀ u : ℂ → Phase n, AffineLineCurve J p q u → a+b ≤ 1 := by
  obtain ⟨U,f,J,hf,hd,hJs,hJ,hJn,hJc,hJsupp⟩ := packing_two_has_adapted_structure hp
  let r : Fin 2 → ℝ := ![a,b]
  have hr (i : Fin 2) : 0 < r i := by
    fin_cases i
    · exact ha
    · exact hb
  have h0 (i : Fin 2) : (0 : Phase n) ∈ closedBall n (r i) := by
    simpa [closedBall,capacity] using (hr i).le
  have hne : f 0 0 ≠ f 1 0 := by
    intro he
    exact disjoint_left.mp (hd 0 1 (by decide)) (mem_image_of_mem _ (h0 0))
      (he.symm ▸ mem_image_of_mem (f 1) (h0 1))
  refine ⟨J,f 0 0,f 1 0,hJs,hJ,hJc,hJsupp,hne,?_⟩
  intro u hu
  let K := tsupport (fun x => J x - standardJ n) ∪
    (f 0 '' closedBall n (r 0)) ∪ (f 1 '' closedBall n (r 1))
  have hKi (i : Fin 2) : IsCompact (f i '' closedBall n (r i)) :=
    (closedBall_isCompact n (r i)).image_of_continuousOn ((hf i).2.1.2.1.continuousOn.mono (hf i).1)
  have hK : IsCompact K := (hJc.union (hKi 0)).union (hKi 1)
  have hmemK (i : Fin 2) {x : Phase n} (hx : x ∈ closedBall n (r i)) : f i x ∈ K := by
    fin_cases i
    · exact Or.inl (Or.inr ⟨x,hx,rfl⟩)
    · exact Or.inr ⟨x,hx,rfl⟩
  have hKopen : K ⊆ openBall n 1 := by
    rintro y ((hy | hy) | hy)
    · exact hJsupp hy
    · obtain ⟨x,hx,rfl⟩ := hy
      exact (hf 0).2.2 hx
    · obtain ⟨x,hx,rfl⟩ := hy
      exact (hf 1).2.2 hx
  obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn ⟨f 0 0,hmemK 0 (h0 0)⟩
    (capacity_smooth n).continuous.continuousOn
  let S := capacity x
  let T := (S+1)/2
  have hS : S < 1 := hKopen hx
  have hST : S < T := by dsimp [T]; linarith
  have hT : T < 1 := by dsimp [T]; linarith
  have hcap (i : Fin 2) : MapsTo (f i) (closedBall n (r i)) (closedBall n S) := by
    intro y hy
    exact hmax (hmemK i hy)
  have hout (y : Phase n) (hy : S < capacity y) : J y = standardJ n := by
    have hn : y ∉ tsupport (fun z => J z - standardJ n) := by
      intro hyK
      exact (not_le_of_gt hy) (hmax (Or.inl (Or.inl hyK)))
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun z => J z - standardJ n) hn)
  have hJi (i : Fin 2) (y : Phase n) (hy : y ∈ f i '' closedBall n (r i)) :
      J y = imageJ (U i) (f i) y :=
    ((hJn i).filter_mono (nhds_le_nhdsSet hy)).self_of_nhds
  have hJnear (i : Fin 2) : ∀ᶠ y in 𝓝 (f i 0), J y = imageJ (U i) (f i) y :=
    (hJn i).filter_mono (nhds_le_nhdsSet (mem_image_of_mem _ (h0 i)))
  exact two_ball_capacity_of_adapted_line hST hT (fun i => (hf i).2.1) hr
    (fun i => (hf i).1) (hd 0 1 (by decide)) hcap hJ hout hJi hJnear hJc hu



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction_oai := @OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction_oai
