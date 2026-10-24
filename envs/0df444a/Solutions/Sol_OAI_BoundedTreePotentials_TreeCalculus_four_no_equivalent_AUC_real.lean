-- Prove2me | solution 1 for OAI.BoundedTreePotentials.TreeCalculus.four_no_equivalent_AUC_real
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T18:24:41.435655+00:00
-- url     : https://prove2.me/submissions/8d5f19ae-6627-4f17-950e-efe409a05675

import Mathlib
import Definitions.Def_BoundedTreePotentials
import Definitions.Def_OAIQWBTP000

section
-- module Solutions.OAIQW_BoundedTreePotentials.TestNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section TestNorms
open scoped Classical
variable {I : Type*}

/-- Symmetry identifies the signed-evaluation supremum with the absolute-pairing norm. -/

theorem testNorm_signed_sup (K : TestFamily I) (x : I →₀ ℝ) :
    testNorm K x = ⨆ f : K, finitePairing f.val x := by
  have hb : BddAbove (range fun f : K => finitePairing f.val x) :=
    ⟨testNorm K x, by rintro _ ⟨f, rfl⟩; exact (le_abs_self _).trans (finitePairing_le_testNorm K f x)⟩
  apply le_antisymm
  · apply ciSup_le
    intro f
    rw [abs_le]
    constructor
    · have hn := le_ciSup hb (⟨-f.val, K.neg_mem _ f.property⟩ : K)
      have he : finitePairing (-f.val) x = -finitePairing f.val x := by
        simp only [finitePairing_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      rw [he] at hn
      linarith
    · exact le_ciSup hb f
  · apply ciSup_le
    intro f
    exact (le_abs_self _).trans (finitePairing_le_testNorm K f x)

end TestNorms


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section TestCompletions
open scoped Classical
variable {I : Type*}

lemma norm_testVector_equiv (K : TestFamily I) (x : TestVector K) :
    ‖x‖ = testNorm K ((testVectorEquiv K) x) := rfl

lemma norm_test_single (K : TestFamily I) (i : I) :
    ‖(testVectorEquiv K).symm (Finsupp.single i 1)‖ = 1 := by
  apply le_antisymm
  · change testNorm K (Finsupp.single i 1) ≤ 1
    simpa using testNorm_le_l1 K (Finsupp.single i 1)
  · change 1 ≤ testNorm K (Finsupp.single i 1)
    simpa using coordinate_le_testNorm K (Finsupp.single i 1) i

lemma finiteTestFunctional_norm_le (K : TestFamily I) (f : K) : ‖finiteTestFunctional K f‖ ≤ 1 := by
  refine (finiteTestFunctional K f).opNorm_le_bound zero_le_one ?_
  intro x
  change |finitePairing f.val ((testVectorEquiv K) x)| ≤ 1 * testNorm K ((testVectorEquiv K) x)
  simpa only [one_mul] using finitePairing_le_testNorm K f ((testVectorEquiv K) x)

lemma completedTestFunctional_norm_le (K : TestFamily I) (f : K) :
    ‖completedTestFunctional K f‖ ≤ 1 := by
  have h := (finiteTestFunctional K f).opNorm_extend_le (N := 1)
    (e := UniformSpace.Completion.toComplL) UniformSpace.Completion.denseRange_coe
    (fun x => by simp)
  have h' : ‖completedTestFunctional K f‖ ≤ ‖finiteTestFunctional K f‖ := by
    simpa only [NNReal.coe_one, one_mul, completedTestFunctional] using h
  exact h'.trans (finiteTestFunctional_norm_le K f)

lemma completedTestFunctional_abs_le (K : TestFamily I) (f : K) (x : TestCompletion K) :
    |completedTestFunctional K f x| ≤ ‖x‖ := by
  simpa only [one_mul, Real.norm_eq_abs] using
    (completedTestFunctional K f).le_of_opNorm_le (completedTestFunctional_norm_le K f) x

/-- Extended tests really remain norming; this is established, not postulated
    as an extra hypothesis on the completion. -/
lemma exists_completed_test_near_norm (K : TestFamily I) (x : TestCompletion K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : K, ‖x‖ - ε < completedTestFunctional K f x := by
  obtain ⟨w, hw⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x
    (show 0 < ε / 3 by linarith)
  have hw' : ‖x - (w : TestCompletion K)‖ < ε / 3 := by simpa only [dist_eq_norm] using hw
  have hn : ‖x‖ - ‖w‖ < ε / 3 := by
    have h := norm_sub_norm_le x (w : TestCompletion K)
    rw [UniformSpace.Completion.norm_coe] at h
    exact h.trans_lt hw'
  have hu : testNorm K ((testVectorEquiv K) w) - ε / 3 <
      ⨆ f : K, finitePairing f.val ((testVectorEquiv K) w) := by
    rw [← testNorm_signed_sup K ((testVectorEquiv K) w)]
    linarith
  obtain ⟨f, hf⟩ := exists_lt_of_lt_ciSup hu
  refine ⟨f, ?_⟩
  have hd := completedTestFunctional_abs_le K f (x - (w : TestCompletion K))
  rw [map_sub, completedTestFunctional_coe] at hd
  have hl := (abs_le.mp hd).1
  change ‖w‖ - ε / 3 < finitePairing f.val w at hf
  linarith

theorem completed_tests_norming (K : TestFamily I) (x : TestCompletion K) :
    ‖x‖ = ⨆ f : K, completedTestFunctional K f x := by
  have hb : BddAbove (range fun f : K => completedTestFunctional K f x) :=
    ⟨‖x‖, by rintro _ ⟨f, rfl⟩; exact (le_abs_self _).trans (completedTestFunctional_abs_le K f x)⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hf⟩ := exists_completed_test_near_norm K x hε
    have := le_ciSup hb f
    linarith
  · apply ciSup_le
    intro f
    exact (le_abs_self _).trans (completedTestFunctional_abs_le K f x)

end TestCompletions


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.FiniteHeads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section CompletedHeads
open scoped Classical
variable {I : Type*}

@[simp] lemma norm_coordinateVector (K : TestFamily I) (i : I) :
    ‖coordinateVector K i‖ = 1 := by
  simp only [coordinateVector, UniformSpace.Completion.norm_coe, norm_test_single]

end CompletedHeads


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.WeakNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section WeakNullSequences
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeaklyNull.map {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {d : ℕ → E} (hd : WeaklyNull d) (L : E →L[ℝ] Y) : WeaklyNull (fun n => L (d n)) :=
  fun φ => hd (φ.comp L)

/-- Weak nullity really gives approximation in every closed finite-codimensional
    subspace; the finite-dimensional quotient step is proved explicitly. -/
lemma WeaklyNull.approximable {d : ℕ → E} (hd : WeaklyNull d) (F : ClosedFiniteCodim E)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ w : E, w ∈ F.space ∧ ‖d n - w‖ < ε := by
  let : IsClosed (F.space : Set E) := F.closed
  let : Module.Finite ℝ (E ⧸ F.space) := F.finiteCodim
  let e := (Module.finBasis ℝ (E ⧸ F.space)).equivFunL
  have hc : Tendsto (fun n => e (F.space.mkQL (d n))) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hd ((ContinuousLinearMap.proj i).comp (e.toContinuousLinearMap.comp F.space.mkQL))
  have hq : Tendsto (fun n => F.space.mkQL (d n)) atTop (𝓝 0) := by
    have h := (e.symm.continuous.tendsto 0).comp hc
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, map_zero] using h
  have hqn : Tendsto (fun n => ‖F.space.mkQL (d n)‖) atTop (𝓝 0) := by simpa using hq.norm
  have he := hqn.eventually_lt_const (show 0 < ε/2 by positivity)
  filter_upwards [he] with n hn
  obtain ⟨u, hu, hun⟩ := Submodule.Quotient.norm_mk_lt (F.space.mkQL (d n))
    (show 0 < ε/2 by positivity)
  refine ⟨d n - u, (Submodule.Quotient.eq F.space).mp hu.symm, ?_⟩
  have heq : d n - (d n - u) = u := by abel
  rw [heq]
  linarith

lemma hilbert_upper_eval_sq_sum {I : Type*} (v : I → E)
    (hv : ∀ (A : Finset I) (a : I → ℝ),
      ‖∑ n ∈ A, a n • v n‖ ≤ Real.sqrt (∑ n ∈ A, (a n)^2))
    (φ : E →L[ℝ] ℝ) (A : Finset I) :
    ∑ n ∈ A, φ (v n)^2 ≤ ‖φ‖^2 := by
  let S := ∑ n ∈ A, φ (v n)^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hscalar : φ (∑ n ∈ A, φ (v n) • v n) = S := by
    simp only [map_sum, map_smul, smul_eq_mul, S, pow_two]
  have hnorm := φ.le_opNorm (∑ n ∈ A, φ (v n) • v n)
  rw [hscalar, Real.norm_eq_abs, abs_of_nonneg hS] at hnorm
  have hprod : S ≤ ‖φ‖ * Real.sqrt S := hnorm.trans
    (mul_le_mul_of_nonneg_left (hv A (fun n => φ (v n))) (norm_nonneg φ))
  have hs : Real.sqrt S ≤ ‖φ‖ := by
    by_cases hzero : Real.sqrt S = 0
    · rw [hzero]; exact norm_nonneg _
    · have hpos : 0 < Real.sqrt S := lt_of_le_of_ne (Real.sqrt_nonneg S) (Ne.symm hzero)
      apply (mul_le_mul_iff_right₀ hpos).mp
      nlinarith [Real.sq_sqrt hS]
  nlinarith [Real.sq_sqrt hS, norm_nonneg φ, Real.sqrt_nonneg S]

lemma weaklyNull_of_hilbert_upper (v : ℕ → E)
    (hv : ∀ (A : Finset ℕ) (a : ℕ → ℝ),
      ‖∑ n ∈ A, a n • v n‖ ≤ Real.sqrt (∑ n ∈ A, (a n)^2)) : WeaklyNull v := by
  intro φ
  have hs : Summable (fun n => φ (v n)^2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) (hilbert_upper_eval_sq_sum v hv φ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := hs.tendsto_atTop_zero.sqrt
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using h

lemma oneSidedModulus_nonneg (t : ℝ) : (0 : EReal) ≤ oneSidedModulus E t := by
  apply le_iInf
  intro x
  obtain ⟨φ, hφ, hxφ⟩ := exists_dual_vector'' ℝ x.val
  apply le_iSup_of_le (functionalKernel φ)
  apply le_iInf
  intro y
  have hφy : φ y.val = 0 := y.property.1
  have h := φ.le_of_opNorm_le hφ (x.val + t • y.val)
  rw [map_add, map_smul, hφy, smul_zero, add_zero, hxφ, x.property] at h
  simp only [Real.ringHom_apply, Real.norm_eq_abs, abs_one, one_mul] at h
  exact EReal.coe_le_coe_iff.mpr (by linarith)

lemma oneSided_sphere_tail {t γ : ℝ} (hγ : (γ : EReal) < oneSidedModulus E t)
    (x : E) (hx : ‖x‖ = 1) :
    ∃ F : ClosedFiniteCodim E, ∀ y : E, y ∈ F.space → ‖y‖ = 1 →
      1 + γ ≤ ‖x + t • y‖ := by
  have hxlt := hγ.trans_le (iInf_le _ (⟨x, hx⟩ : {x : E // ‖x‖ = 1}))
  obtain ⟨F, hF⟩ := lt_iSup_iff.mp hxlt
  refine ⟨F, ?_⟩
  intro y hy hyn
  have hylt := hF.trans_le (iInf_le _ (⟨y, hy, hyn⟩ : {y : E // y ∈ F.space ∧ ‖y‖ = 1}))
  have hreal := EReal.coe_lt_coe_iff.mp hylt
  linarith

end WeakNullSequences

section AUCRayGrowth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_bound_extends_to_rays (x : E) (hx : ‖x‖ = 1) (F : Submodule ℝ E)
    {t γ : ℝ} (hγ : 0 ≤ γ)
    (hsphere : ∀ y : E, y ∈ F → ‖y‖ = 1 → 1 + γ ≤ ‖x + t • y‖)
    (y : E) (hy : y ∈ F) (hy1 : 1 ≤ ‖y‖) :
    1 + γ ≤ ‖x + t • y‖ := by
  let a := ‖y‖⁻¹
  have hyn : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy1
  have ha : 0 < a := inv_pos.mpr hyn
  have ha1 : a ≤ 1 := by
    simpa only [a, one_div] using ((div_le_one hyn).mpr hy1 : 1 / ‖y‖ ≤ 1)
  have hay : ‖a • y‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    exact inv_mul_cancel₀ (ne_of_gt hyn)
  have h := hsphere (a • y) (F.smul_mem a hy) hay
  have he : x + t • (a • y) = (1-a) • x + a • (x + t • y) := by module
  rw [he] at h
  have hn := norm_add_le ((1-a) • x) (a • (x + t • y))
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ha1),
    Real.norm_of_nonneg ha.le, hx, mul_one] at hn
  by_contra hh
  have hlong := lt_of_not_ge hh
  have hprod := mul_lt_mul_of_pos_left hlong ha
  have hγa : a * γ ≤ γ := mul_le_of_le_one_left hγ ha1
  nlinarith

lemma oneSided_wide_tail {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (hδ : (γ : EReal) < oneSidedModulus E t) (p : E) (hp : 0 < ‖p‖) :
    ∃ F : ClosedFiniteCodim E, ∀ w : E, w ∈ F.space → t * ‖p‖ ≤ ‖w‖ →
      (1 + γ) * ‖p‖ ≤ ‖p + w‖ := by
  let x := ‖p‖⁻¹ • p
  have hx : ‖x‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    exact inv_mul_cancel₀ (ne_of_gt hp)
  obtain ⟨F, hF⟩ := oneSided_sphere_tail hδ x hx
  refine ⟨F, ?_⟩
  intro w hw hwn
  let v := (t * ‖p‖)⁻¹ • w
  have hv : v ∈ F.space := F.space.smul_mem _ hw
  have hc : 0 < t * ‖p‖ := mul_pos ht hp
  have hvn : 1 ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hc).mpr (by simpa using hwn)
  have h := norm_bound_extends_to_rays x hx F.space hγ hF v hv hvn
  have hec : t * (t * ‖p‖)⁻¹ = ‖p‖⁻¹ := by
    field_simp
  have he : x + t • v = ‖p‖⁻¹ • (p + w) := by
    dsimp only [x, v]
    rw [smul_smul, hec, smul_add]
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), mul_comm, ← div_eq_mul_inv] at h
  exact (le_div_iff₀ hp).mp h

/-- One weakly-null child sequence gives a definite AUC increase. -/
lemma oneSided_growth {t γ c : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hc : 0 < c)
    (hδ : (γ : EReal) < oneSidedModulus E t) (p : E) (hp : 0 < ‖p‖)
    (htp : t * ‖p‖ ≤ c/2) (d : ℕ → E) (hd : WeaklyNull d)
    (hdn : ∀ n, c ≤ ‖d n‖) :
    ∃ n, ‖p‖ + γ * ‖p‖ / 2 ≤ ‖p + d n‖ := by
  obtain ⟨F, hF⟩ := oneSided_wide_tail ht hγ.le hδ p hp
  have hε : 0 < min (c/2) (γ * ‖p‖ / 2) := lt_min (by positivity) (by positivity)
  obtain ⟨n, w, hw, he⟩ := (hd.approximable F hε).exists
  have hec : ‖d n - w‖ < c/2 := he.trans_le (min_le_left _ _)
  have heγ : ‖d n - w‖ < γ * ‖p‖ / 2 := he.trans_le (min_le_right _ _)
  have hwn : t * ‖p‖ ≤ ‖w‖ := by
    have h := norm_sub_norm_le (d n) w
    have hd' := hdn n
    linarith
  have hfw := hF w hw hwn
  have hpert := norm_sub_norm_le (p + w) (p + d n)
  have heq : (p + w) - (p + d n) = w - d n := by abel
  rw [heq, norm_sub_rev] at hpert
  exact ⟨n, by linarith⟩

end AUCRayGrowth

section BoundedTrees
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_pos_real_lt_ereal {b : EReal} (hb : 0 < b) :
    ∃ γ : ℝ, 0 < γ ∧ (γ : EReal) < b := by
  cases b using EReal.rec with
  | bot => exact (not_lt_bot hb).elim
  | coe b =>
    have hb' : 0 < b := EReal.coe_lt_coe_iff.mp hb
    exact ⟨b/2, by positivity, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
  | top => exact ⟨1, zero_lt_one, EReal.coe_lt_top 1⟩

/-- The bounded-tree obstruction for arbitrary finite heights. Weak nullity is tested against the whole dual; iteration of the positive per-step gain gives the contradiction. -/


theorem bounded_tree_modulus_eq_zero
    (p : (h : ℕ) → Tree h → E) {m M c : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hc : 0 < c)
    (hbound : ∀ h, 1 ≤ h → ∀ s : Tree h, m ≤ ‖p h s‖ ∧ ‖p h s‖ ≤ M)
    (hweak : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => p h (child s hs n) - p h s))
    (hinc : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      c ≤ ‖p h (child s hs n) - p h s‖) :
    oneSidedModulus E (c / (2 * M)) = 0 := by
  apply le_antisymm ?_ (oneSidedModulus_nonneg _)
  by_contra hnot
  obtain ⟨γ, hγ, hγδ⟩ := exists_pos_real_lt_ereal (lt_of_not_ge hnot)
  have hM : 0 < M := hm.trans_le hmM
  have ht : 0 < c / (2 * M) := by positivity
  let a := γ * m / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (M / a)
  let H := n + 1
  have hH : 1 ≤ H := Nat.le_add_left 1 n
  have hlarge : M < m + (H : ℝ) * a := by
    have hn' : M < (n : ℝ) * a := (div_lt_iff₀ ha).mp hn
    simp only [H, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hpath : ∀ j : ℕ, j ≤ H → ∃ s : Tree H,
      s.val.length = j ∧ m + (j : ℝ) * a ≤ ‖p H s‖ := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨root H, rfl, by simpa using (hbound H hH (root H)).1⟩
    | succ j ih =>
      intro hj
      obtain ⟨s, hsl, hsn⟩ := ih (Nat.le_of_succ_le hj)
      have hs : s.val.length < H := by omega
      have hpb := hbound H hH s
      have hp : 0 < ‖p H s‖ := hm.trans_le hpb.1
      have htp : (c / (2 * M)) * ‖p H s‖ ≤ c/2 := by
        calc
          _ ≤ (c / (2 * M)) * M := mul_le_mul_of_nonneg_left hpb.2 ht.le
          _ = c/2 := by field_simp
      obtain ⟨i, hi⟩ := oneSided_growth ht hγ hc hγδ (p H s) hp htp
        (fun n => p H (child s hs n) - p H s) (hweak H hH s hs) (hinc H hH s hs)
      rw [add_sub_cancel] at hi
      refine ⟨child s hs i, by simp [hsl], ?_⟩
      have hgrowth : a ≤ γ * ‖p H s‖ / 2 := by
        dsimp [a]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpb.1 hγ.le) (by norm_num)
      rw [Nat.cast_succ]
      nlinarith
  obtain ⟨s, hs, hsn⟩ := hpath H le_rfl
  have hb := (hbound H hH s).2
  linarith

/-- Explicit equivalence constants are retained in the obstruction radius.
    Quantification over continuous linear copies is precisely quantification
    over equivalent norms via the identity linear equivalence. -/
theorem bounded_tree_renorming_obstruction
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (p : (h : ℕ) → Tree h → E) {m M c α β : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hc : 0 < c)
    (hbound : ∀ h, 1 ≤ h → ∀ s : Tree h, m ≤ ‖p h s‖ ∧ ‖p h s‖ ≤ M)
    (hweak : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => p h (child s hs n) - p h s))
    (hinc : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      c ≤ ‖p h (child s hs n) - p h s‖)
    (e : E ≃L[ℝ] Y) (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x : E, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖) :
    oneSidedModulus Y (α * c / (2 * β * M)) = 0 := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hM : 0 < M := hm.trans_le hmM
  have hb' : ∀ h, 1 ≤ h → ∀ s : Tree h,
      α * m ≤ ‖e (p h s)‖ ∧ ‖e (p h s)‖ ≤ β * M := by
    intro h hh s
    exact ⟨(mul_le_mul_of_nonneg_left (hbound h hh s).1 hα.le).trans (he _).1,
      (he _).2.trans (mul_le_mul_of_nonneg_left (hbound h hh s).2 hβ.le)⟩
  have hw' : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => e (p h (child s hs n)) - e (p h s)) := by
    intro h hh s hs
    have hw := (hweak h hh s hs).map e.toContinuousLinearMap
    change WeaklyNull (fun n => e (p h (child s hs n) - p h s)) at hw
    simpa only [map_sub] using hw
  have hi' : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      α*c ≤ ‖e (p h (child s hs n)) - e (p h s)‖ := by
    intro h hh s hs n
    rw [← map_sub]
    exact (mul_le_mul_of_nonneg_left (hinc h hh s hs n) hα.le).trans (he _).1
  have hmM' : α*m ≤ β*M := (mul_le_mul_of_nonneg_left hmM hα.le).trans
    (mul_le_mul_of_nonneg_right hαβ hM.le)
  simpa only [mul_assoc] using bounded_tree_modulus_eq_zero (fun h s => e (p h s))
    (mul_pos hα hm) hmM' (mul_pos hα hc) hb' hw' hi'

end BoundedTrees

end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.TreeObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace TreeCalculus
open scoped Classical

lemma finitePairing_nodeArray (r : Bool) (f : TreeCoordinate r → ℝ) (s : Node) :
    finitePairing f (nodeArray r s) = liftCoefficients r f s := by
  by_cases h : r = true ∨ s ≠ []
  · simp [nodeArray, h, finitePairing, liftCoefficients]
  · simp [nodeArray, h, liftCoefficients]

lemma finitePairing_pathArray (r : Bool) (f : TreeCoordinate r → ℝ) (s : Node) :
    finitePairing f (pathArray r s) = potential (liftCoefficients r f) s := by
  simp only [pathArray, map_list_sum, List.map_map, Function.comp_def,
    finitePairing_nodeArray, potential]

lemma pathArray_child (r : Bool) (s : Node) (n : ℕ) :
    pathArray r (s ++ [n]) = pathArray r s + nodeArray r (s ++ [n]) := by
  simp [pathArray, List.inits_append]

lemma pathArray_apply (r : Bool) (s : Node) (i : TreeCoordinate r) :
    pathArray r s i = if i.val <+: s then 1 else 0 := by
  rw [← finitePairing_single_test (pathArray r s) i, finitePairing_pathArray]
  trans potential (Pi.single i.val (1 : ℝ)) s
  · congr 1
    ext u
    by_cases hu : r = true ∨ u ≠ []
    · simp [liftCoefficients, hu, Pi.single_apply, Subtype.ext_iff]
    · have hn : u ≠ i.val := by rintro rfl; exact hu i.property
      simp [liftCoefficients, hu, hn]
  · exact potential_single i.val s

lemma testNorm_pathArray_le (r : Bool) (k : QuadraticKind) (s : Node) :
    testNorm (treeTestFamily r k) (pathArray r s) ≤ 1 := by
  apply ciSup_le
  intro f
  rw [finitePairing_pathArray]
  exact f.property.potential_bound s

lemma testNorm_pathArray (r : Bool) (k : QuadraticKind) (s : Node)
    (hs : r = true ∨ s ≠ []) : testNorm (treeTestFamily r k) (pathArray r s) = 1 := by
  apply le_antisymm (testNorm_pathArray_le r k s)
  have h := coordinate_le_testNorm (treeTestFamily r k) (pathArray r s) ⟨s,hs⟩
  simpa only [pathArray_apply, List.prefix_rfl, ite_true, abs_one] using h

lemma norm_treePath (r : Bool) (k : QuadraticKind) (s : Node) (hs : r = true ∨ s ≠ []) :
    ‖treePath r k s‖ = 1 := by
  simp only [treePath, UniformSpace.Completion.norm_coe, norm_testVector_equiv,
    LinearEquiv.apply_symm_apply]
  exact testNorm_pathArray r k s hs

lemma treePath_child_sub (r : Bool) (k : QuadraticKind) (s : Node) (n : ℕ) :
    treePath r k (s ++ [n]) - treePath r k s =
      coordinateVector (treeTestFamily r k) (childCoordinate r s n) := by
  simp only [treePath, pathArray_child, map_add, UniformSpace.Completion.coe_add,
    add_sub_cancel_left]
  simp only [nodeArray, show r = true ∨ s ++ [n] ≠ [] from Or.inr (by simp),
    dite_true, coordinateVector, childCoordinate]

lemma childNode_injective (s : Node) : Function.Injective (fun n : ℕ => s ++ [n]) := by
  intro n m h
  simpa using List.append_cancel_left h

lemma sibling_quadraticGroup (k : QuadraticKind) (s : Node) (A : Finset ℕ) :
    QuadraticGroup k (A.image (fun n => s ++ [n])) := by
  cases k with
  | sibling =>
    refine ⟨s, ?_⟩
    intro u hu
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨n, rfl⟩
  | antichain =>
    intro u hu v hv huv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
    constructor
    · intro hp
      apply huv
      exact hp.eq_of_length (by simp)
    · intro hp
      apply huv
      exact (hp.eq_of_length (by simp)).symm
  | global => trivial

lemma sibling_sq_sum_le {r : Bool} {k : QuadraticKind}
    (f : treeTestFamily r k) (s : Node) (A : Finset ℕ) :
    ∑ n ∈ A, f.val (childCoordinate r s n)^2 ≤ 1 := by
  have h := f.property.quadratic_budget (A.image (fun n => s ++ [n]))
    (sibling_quadraticGroup k s A)
  rw [Finset.sum_image (fun i hi j hj hij => childNode_injective s hij)] at h
  simpa only [← liftCoefficients_coord, childCoordinate] using h

lemma completedTestFunctional_vector {I : Type*} (K : TestFamily I) (f : K) (i : I) :
    completedTestFunctional K f (coordinateVector K i) = f.val i := by
  rw [coordinateVector, completedTestFunctional_coe]
  change finitePairing f.val (Finsupp.single i 1) = f.val i
  simp [finitePairing]

/-- Siblings have the asserted Hilbert upper estimate in each different model. -/
theorem sibling_hilbert_upper (r : Bool) (k : QuadraticKind) (s : Node)
    (A : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ n ∈ A, a n • coordinateVector (treeTestFamily r k) (childCoordinate r s n)‖ ≤
      Real.sqrt (∑ n ∈ A, (a n)^2) := by
  rw [completed_tests_norming]
  apply ciSup_le
  intro f
  simp only [map_sum, map_smul, completedTestFunctional_vector, smul_eq_mul]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq A a (fun n => f.val (childCoordinate r s n))
  have hf := sibling_sq_sum_le f s A
  have hS : 0 ≤ ∑ n ∈ A, (a n)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : (∑ n ∈ A, a n * f.val (childCoordinate r s n))^2 ≤ ∑ n ∈ A, (a n)^2 :=
    hc.trans ((mul_le_mul_of_nonneg_left hf hS).trans_eq (mul_one _))
  nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg (∑ n ∈ A, (a n)^2)]

lemma siblings_weaklyNull (r : Bool) (k : QuadraticKind) (s : Node) :
    WeaklyNull (fun n => coordinateVector (treeTestFamily r k) (childCoordinate r s n)) :=
  weaklyNull_of_hilbert_upper _ (sibling_hilbert_upper r k s)

lemma fourBoundedTree_norm (r : Bool) (k : QuadraticKind) (h : ℕ) (s : Tree h) :
    ‖fourBoundedTree r k h s‖ = 1 := by
  exact norm_treePath r k _ (Or.inr (by simp))

lemma fourBoundedTree_difference (r : Bool) (k : QuadraticKind) (h : ℕ)
    (s : Tree h) (hs : s.val.length < h) (n : ℕ) :
    fourBoundedTree r k h (child s hs n) - fourBoundedTree r k h s =
      coordinateVector (treeTestFamily r k) (childCoordinate r ([0] ++ s.val) n) := by
  change treePath r k ([0] ++ (s.val ++ [n])) - treePath r k ([0] ++ s.val) = _
  rw [← List.append_assoc]
  exact treePath_child_sub r k _ n

/-- Exact zero radius for every equivalent norm represented on a continuous-linearly-equivalent real normed space. -/

theorem four_renorming_obstruction (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖) :
    oneSidedModulus Y (α / (2 * β)) = 0 := by
  have hb : ∀ h, 1 ≤ h → ∀ s : Tree h,
      (1 : ℝ) ≤ ‖fourBoundedTree r k h s‖ ∧ ‖fourBoundedTree r k h s‖ ≤ 1 := by
    intro h hh s
    simp only [fourBoundedTree_norm, le_refl, and_self]
  have hw : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => fourBoundedTree r k h (child s hs n) - fourBoundedTree r k h s) := by
    intro h hh s hs
    simp only [fourBoundedTree_difference]
    exact siblings_weaklyNull r k _
  have hi : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      (1 : ℝ) ≤ ‖fourBoundedTree r k h (child s hs n) - fourBoundedTree r k h s‖ := by
    intro h hh s hs n
    simp only [fourBoundedTree_difference, norm_coordinateVector, le_refl]
  simpa only [mul_one] using bounded_tree_renorming_obstruction
    (fourBoundedTree r k) zero_lt_one le_rfl zero_lt_one hb hw hi e hα hαβ he

end TreeCalculus
section EquivalenceBounds
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma continuousEquiv_bounds (e : E ≃L[ℝ] Y) :
    ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ ∀ x, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖ := by
  let A := ‖e.symm.toContinuousLinearMap‖ + 1
  let B := ‖e.toContinuousLinearMap‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg e.toContinuousLinearMap]
  refine ⟨A⁻¹, B, inv_pos.mpr hA, (inv_le_one₀ hA).mpr hA1 |>.trans hB1, ?_⟩
  intro x
  constructor
  · have h := e.symm.toContinuousLinearMap.le_opNorm (e x)
    change ‖e.symm (e x)‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ at h
    rw [e.symm_apply_apply] at h
    have hu : ‖x‖ ≤ A * ‖e x‖ := by
      dsimp [A]
      nlinarith [norm_nonneg (e x)]
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hA), one_mul] using
      mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hA.le)
  · have h := e.toContinuousLinearMap.le_opNorm x
    change ‖e x‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x‖ at h
    dsimp [B]
    nlinarith [norm_nonneg x]

end EquivalenceBounds

namespace TreeCalculus

theorem four_no_equivalent_AUC (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) : ¬ IsAUC Y := by
  obtain ⟨α, β, hα, hαβ, he⟩ := continuousEquiv_bounds e
  have hβ : 0 < β := hα.trans_le hαβ
  intro hauc
  have hp := hauc (α/(2*β)) (by positivity)
  rw [four_renorming_obstruction r k e hα hαβ he] at hp
  exact lt_irrefl _ hp

end TreeCalculus

end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.RealModuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
/-- Coercion commutes with a bounded real infimum. -/

lemma ereal_coe_ciInf {I : Type*} [Nonempty I] (f : I → ℝ)
    (hf : BddBelow (Set.range f)) :
    ((⨅ i,f i : ℝ) : EReal) = ⨅ i,(f i : EReal) := by
  have hl : ((⨅ i,f i : ℝ) : EReal) ≤ ⨅ i,(f i : EReal) := by
    apply le_iInf
    intro i
    exact EReal.coe_le_coe_iff.mpr (ciInf_le hf i)
  have hb : (⨅ i,(f i : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl
  have ht : (⨅ i,(f i : EReal)) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (iInf_le (fun i => (f i : EReal)) (Classical.choice inferInstance))
  have he := EReal.coe_toReal ht hb
  apply le_antisymm hl
  rw [← he]
  apply EReal.coe_le_coe_iff.mpr
  apply le_ciInf
  intro i
  apply EReal.coe_le_coe_iff.mp
  rw [he]
  exact iInf_le _ i

lemma ereal_coe_ciSup {I : Type*} [Nonempty I] (f : I → ℝ)
    (hf : BddAbove (Set.range f)) :
    ((⨆ i,f i : ℝ) : EReal) = ⨆ i,(f i : EReal) := by
  have hu : (⨆ i,(f i : EReal)) ≤ ((⨆ i,f i : ℝ) : EReal) := by
    apply iSup_le
    intro i
    exact EReal.coe_le_coe_iff.mpr (le_ciSup hf i)
  have hb : (⨆ i,(f i : EReal)) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_iSup (fun i => (f i : EReal)) (Classical.choice inferInstance))
  have ht : (⨆ i,(f i : EReal)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hu
  have he := EReal.coe_toReal ht hb
  apply le_antisymm _ hu
  rw [← he]
  apply EReal.coe_le_coe_iff.mpr
  apply ciSup_le
  intro i
  apply EReal.coe_le_coe_iff.mp
  rw [he]
  exact le_iSup (fun i => (f i : EReal)) i

lemma ereal_coe_modulus_game {X F : Type*} {Y : F → Type*}
    [Nonempty X] [Nonempty F] [∀ f,Nonempty (Y f)]
    (v : X → (f : F) → Y f → ℝ) {a b : ℝ}
    (hl : ∀ x f y,a ≤ v x f y) (hu : ∀ x f,∃ y,v x f y ≤ b) :
    ((⨅ x,⨆ f,⨅ y,v x f y : ℝ) : EReal) =
      ⨅ x,⨆ f,⨅ y,(v x f y : EReal) := by
  have hb x f : BddBelow (Set.range (v x f)) := ⟨a,by rintro _ ⟨y,rfl⟩; exact hl x f y⟩
  have hlo x f : a ≤ ⨅ y,v x f y := le_ciInf (hl x f)
  have hup x f : (⨅ y,v x f y) ≤ b := by
    obtain ⟨y,hy⟩ := hu x f
    exact (ciInf_le (hb x f) y).trans hy
  have hsup x : BddAbove (Set.range (fun f => ⨅ y,v x f y)) :=
    ⟨b,by rintro _ ⟨f,rfl⟩; exact hup x f⟩
  have hmid x : a ≤ ⨆ f,⨅ y,v x f y :=
    (hlo x (Classical.choice inferInstance)).trans (le_ciSup (hsup x) _)
  rw [ereal_coe_ciInf _ ⟨a,by rintro _ ⟨x,rfl⟩; exact hmid x⟩]
  congr 1
  funext x
  rw [ereal_coe_ciSup _ (hsup x)]
  congr 1
  funext f
  exact ereal_coe_ciInf _ (hb x f)

section RealModuli
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ClosedFiniteCodim.unit_exists (hinf : ¬Module.Finite ℝ E)
    (F : ClosedFiniteCodim E) : ∃ y : E,y ∈ F.space ∧ ‖y‖=1 := by
  have hbot : F.space ≠ ⊥ := by
    intro h
    apply hinf
    let := F.finiteCodim
    exact Module.Finite.of_injective F.space.mkQ
      (LinearMap.ker_eq_bot.mp ((Submodule.ker_mkQ _).trans h))
  obtain ⟨v,hv,hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨‖v‖⁻¹ • v,F.space.smul_mem _ hv,?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvn)]

lemma unit_nonempty_of_infinite (hinf : ¬Module.Finite ℝ E) :
    Nonempty {x : E // ‖x‖=1} := by
  obtain ⟨x,_,hx⟩ := (Classical.choice (inferInstance : Nonempty (ClosedFiniteCodim E))).unit_exists E hinf
  exact ⟨⟨x,hx⟩⟩

lemma unit_perturbation_bound {x y : E} (hx : ‖x‖=1) (hy : ‖y‖=1) (t : ℝ) :
    ‖x+t • y‖ ≤ 1+|t| ∧ ‖x-t • y‖ ≤ 1+|t| := by
  constructor
  · simpa only [hx,hy,norm_smul,Real.norm_eq_abs,mul_one] using norm_add_le x (t • y)
  · simpa only [hx,hy,norm_smul,Real.norm_eq_abs,mul_one] using norm_sub_le x (t • y)

lemma oneSidedModulusReal_coe (hinf : ¬Module.Finite ℝ E) (t : ℝ) :
    (oneSidedModulusReal E t : EReal)=oneSidedModulus E t := by
  let := unit_nonempty_of_infinite E hinf
  have (F : ClosedFiniteCodim E) : Nonempty {y : E // y ∈ F.space ∧ ‖y‖=1} := by
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    exact ⟨⟨y,hy,hyn⟩⟩
  apply ereal_coe_modulus_game (a := -1) (b := |t|)
  · intro x F y
    linarith [norm_nonneg (x.val+t • y.val)]
  · intro x F
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    refine ⟨⟨y,hy,hyn⟩,?_⟩
    have hh := unit_perturbation_bound E x.property hyn t
    dsimp
    linarith [hh.1]

lemma isAUCReal_iff (hinf : ¬Module.Finite ℝ E) : IsAUCReal E ↔ IsAUC E := by
  unfold IsAUCReal IsAUC
  have hzero : (0 : EReal)=(0 : ℝ) := by norm_cast
  simp only [← oneSidedModulusReal_coe E hinf,hzero,EReal.coe_lt_coe_iff]

lemma oneSidedModulus_eq_top_of_finite [Module.Finite ℝ E] (t : ℝ) :
    oneSidedModulus E t=⊤ := by
  apply top_unique
  apply le_iInf
  intro x
  let F : ClosedFiniteCodim E := ⟨⊥,by simp,inferInstance⟩
  apply le_trans _ (le_iSup (fun F : ClosedFiniteCodim E =>
    ⨅ y : {y : E // y ∈ F.space ∧ ‖y‖=1},((‖x.val+t • y.val‖-1 : ℝ) : EReal)) F)
  have : IsEmpty {y : E // y ∈ F.space ∧ ‖y‖=1} := by
    constructor
    intro y
    have hy : y.val=0 := y.property.1
    simpa [hy] using y.property.2
  simp

lemma infiniteDimensional_of_not_isAUC (h : ¬IsAUC E) : ¬Module.Finite ℝ E := by
  intro hf
  let := hf
  apply h
  intro t ht
  rw [oneSidedModulus_eq_top_of_finite]
  exact EReal.coe_lt_top 0

lemma not_isAUCReal_of_not_isAUC (h : ¬IsAUC E) : ¬IsAUCReal E :=
  fun hh => h ((isAUCReal_iff E (infiniteDimensional_of_not_isAUC E h)).mp hh)

end RealModuli
end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.EndpointTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials

namespace TreeCalculus

theorem four_no_equivalent_AUC_real_oai (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (four_no_equivalent_AUC r k e)
end TreeCalculus

end BoundedTreePotentials


end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.BoundedTreePotentials.TreeCalculus.four_no_equivalent_AUC_real_oai.{u_1} := @OAI.BoundedTreePotentials.TreeCalculus.four_no_equivalent_AUC_real_oai.{u_1}
