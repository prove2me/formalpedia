-- Prove2me | solution 1 for OAI.SplitTangent.RationallyConnected.exists_submersive_familyAlternative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:38:08.182697+00:00
-- url     : https://prove2.me/submissions/e446b5b4-528f-48e0-9e5c-2f7da07bf64f

import Mathlib
import Definitions.Def_SplitTangentIntegrability
import Definitions.Def_OAIQWST002

section
-- module Solutions.OAIQW_SplitTangent.FormalBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Formal Boxes. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
universe u
open Set Filter Topology

section CurveImports

open Filter Topology Polynomial
namespace SplitTangent.ProjectiveLine



theorem finite_nonanalytic {f : ℂ → ℂ} (hf : Meromorphic f)
    (hInf : MeromorphicAtInfinity f) : {z : ℂ | ¬ AnalyticAt ℂ f z}.Finite := by
  have he : ∀ᶠ w in nhds 0, w ≠ 0 → AnalyticAt ℂ (fun z => f z⁻¹) w := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using
      hInf.eventually_analyticAt
  obtain ⟨r,hr,hrsub⟩ := Metric.eventually_nhds_iff.mp he
  have hlarge : ∀ z : ℂ, r⁻¹ < ‖z‖ → AnalyticAt ℂ f z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h; simp only [h, norm_zero] at hz
      exact (not_lt_of_ge (inv_nonneg.mpr hr.le)) hz
    have hinv : dist z⁻¹ 0 < r := by
      rw [dist_zero_right, norm_inv, inv_lt_comm₀ (norm_pos_iff.mpr hz0) hr]
      exact hz
    have ha := hrsub hinv (inv_ne_zero hz0)
    have hc := ha.comp (analyticAt_id.inv hz0)
    simpa only [Function.comp_def, inv_inv] using hc
  have hK := (isCompact_closedBall (0 : ℂ) r⁻¹).finite_sdiff_of_mem_codiscreteWithin
    ((hf.meromorphicOn (s := Metric.closedBall 0 r⁻¹)).analyticAt_mem_codiscreteWithin)
  apply hK.subset
  intro z hz
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using
    (not_lt.mp (fun h => hz (hlarge z h))), hz⟩

 

theorem exists_polynomial_denominator {f : ℂ → ℂ} (hf : Meromorphic f)
    (hInf : MeromorphicAtInfinity f) :
    ∃ q : ℂ[X], q ≠ 0 ∧ Differentiable ℂ (fun z => q.eval z * f z) := by
  classical
  let B := (finite_nonanalytic hf hInf).toFinset
  choose n hn using fun x => hf x
  let q : ℂ[X] := ∏ a ∈ B, (X - C a) ^ n a
  refine ⟨q, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun a ha => pow_ne_zero _ (X_sub_C_ne_zero a))
  · intro z
    by_cases hz : z ∈ B
    · have hfactor : q = (X - C z) ^ n z * ∏ a ∈ B.erase z, (X - C a) ^ n a := by
        exact (Finset.mul_prod_erase B _ hz).symm
      have han : AnalyticAt ℂ
          (fun t => (∏ a ∈ B.erase z, (X - C a) ^ n a).eval t * ((t-z)^n z * f t)) z :=
        (AnalyticOnNhd.eval_polynomial (∏ a ∈ B.erase z, (X - C a) ^ n a) z (mem_univ z)).mul
          (by simpa only [smul_eq_mul] using hn z)
      apply han.differentiableAt.congr_of_eventuallyEq
      filter_upwards with t
      simp only [hfactor, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      ring
    · have hz' : AnalyticAt ℂ f z := by simpa [B] using hz
      exact (by fun_prop : DifferentiableAt ℂ (fun t => q.eval t) z).mul hz'.differentiableAt

 

theorem polynomial_growth_atInfinity {f : ℂ → ℂ} (hInf : MeromorphicAtInfinity f) :
    ∃ (n : ℕ) (C R : ℝ), ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖^n := by
  obtain ⟨n,hn⟩ := hInf
  let h : ℂ → ℂ := fun w => w^n * f w⁻¹
  have hh : AnalyticAt ℂ h 0 := by simpa [h, smul_eq_mul] using hn
  have he : ∀ᶠ w in nhds 0, ‖h w‖ < ‖h 0‖ + 1 :=
    hh.continuousAt.norm.eventually_lt_const (by linarith)
  obtain ⟨r,hr,hrsub⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨n, ‖h 0‖+1, max 1 (r⁻¹+1), ?_⟩
  intro z hz
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hz)
  have hzlarge : r⁻¹ < ‖z‖ := by have := (le_max_right 1 (r⁻¹+1)).trans hz; linarith
  have hw : dist z⁻¹ 0 < r := by
    rw [dist_zero_right, norm_inv, inv_lt_comm₀ hzn hr]
    exact hzlarge
  have hb : ‖h z⁻¹‖ ≤ ‖h 0‖+1 := (hrsub hw).le
  have heq : ‖f z‖ = ‖z‖^n * ‖h z⁻¹‖ := by
    simp only [h, inv_inv, norm_mul, norm_pow, norm_inv]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hzn.ne', one_pow, one_mul]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg _) _)).trans_eq (mul_comm _ _)

 
theorem iteratedDeriv_zero_of_tail_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {n : ℕ} {C R₀ : ℝ} (hbound : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖^n)
    {k : ℕ} (hk : n < k) : iteratedDeriv k f 0 = 0 := by
  have hb : ∀ R : ℝ, max 1 R₀ ≤ R →
      ‖iteratedDeriv k f 0‖ ≤ (k.factorial : ℝ) * C / R^(k-n) := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) k hR0
      hf.diffContOnCl (fun z hz => by
        have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
        simpa only [hzR] using hbound z (hzR ▸ ((le_max_right _ _).trans hR)))
    convert h using 1
    rw [pow_sub₀ R hR0.ne' hk.le]
    field_simp
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto (show Tendsto (fun R : ℝ => (k.factorial : ℝ) * C / R^(k-n))
      atTop (nhds 0) from tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega)))
  exact (eventually_ge_atTop (max 1 R₀)).mono (fun R hR => hb R hR)

 

theorem exists_polynomial_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hInf : MeromorphicAtInfinity f) : ∃ p : ℂ[X], ∀ z, f z = p.eval z := by
  obtain ⟨n,C,R,hb⟩ := polynomial_growth_atInfinity hInf
  refine ⟨∑ k ∈ Finset.range (n+1), monomial k ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0), ?_⟩
  intro z
  rw [← Complex.taylorSeries_eq_of_entire' 0 z hf]
  rw [tsum_eq_sum (s := Finset.range (n+1)) (fun k hk => by
    have hnk : n < k := by simpa using hk
    rw [iteratedDeriv_zero_of_tail_growth hf hb hnk]
    simp)]
  simp [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

 
theorem meromorphicAt_polynomial_eval {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x)
    (p : ℂ[X]) : MeromorphicAt (fun z => p.eval (f z)) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add, Pi.add_apply] using hp.fun_add hq
  | monomial n a => simpa only [eval_monomial, Pi.mul_apply, Pi.pow_apply] using (MeromorphicAt.const a x).fun_mul (hf.fun_pow n)

 

theorem rationality {f : ℂ → ℂ} (hf : Meromorphic f)
    (hInf : MeromorphicAtInfinity f) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z * f z = p.eval z) ∧
      ∀ z, q.eval z ≠ 0 → f z = p.eval z / q.eval z := by
  obtain ⟨q,hq,hqf⟩ := exists_polynomial_denominator hf hInf
  have hqInf : MeromorphicAtInfinity (fun z => q.eval z * f z) := by
    exact (meromorphicAt_polynomial_eval (MeromorphicAt.id 0).inv q).mul hInf
  obtain ⟨p,hp⟩ := exists_polynomial_of_entire hqf hqInf
  refine ⟨p,q,hq,hp,?_⟩
  intro z hz
  exact (eq_div_iff hz).mpr (by simpa only [mul_comm] using hp z)

end SplitTangent.ProjectiveLine

namespace SplitTangent

 

theorem projectiveCoordinates_change {N : ℕ} (p : ProjectiveSpace N)
    (i j k : Fin (N+1)) (hk : p.rep k ≠ 0) :
    projectiveCoordinates i p j = projectiveCoordinates k p j / projectiveCoordinates k p i := by
  simp only [projectiveCoordinates, div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    (p.rep i)⁻¹ * p.rep j = ((p.rep k)⁻¹ * p.rep k) * ((p.rep i)⁻¹ * p.rep j) := by
      rw [inv_mul_cancel₀ hk, one_mul]
    _ = _ := by ring

 

theorem projective_ratio_meromorphic {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : ℂ → X.Carrier)
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (i j : Fin (e.N+1)) : Meromorphic (fun z => projectiveCoordinates i (e.map (g z)) j) := by
  intro z
  obtain ⟨k,hk⟩ : ∃ k, (e.map (g z)).rep k ≠ 0 := by
    by_contra h
    push Not at h
    exact (e.map (g z)).rep_nonzero (funext h)
  have ha : AnalyticAt ℂ (fun w => projectiveCoordinates k (e.map (g w))) z :=
    (((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp z
      hg.contMDiffAt).contDiffAt.analyticAt
  have hj : AnalyticAt ℂ (fun w => projectiveCoordinates k (e.map (g w)) j) z :=
    (ContinuousLinearMap.proj j : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp ha
  have hi : AnalyticAt ℂ (fun w => projectiveCoordinates k (e.map (g w)) i) z :=
    (ContinuousLinearMap.proj i : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp ha
  apply (hj.meromorphicAt.div hi.meromorphicAt).congr
  apply Filter.EventuallyEq.filter_mono _ nhdsWithin_le_nhds
  filter_upwards [hg.continuous.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)] with w hw
  exact (projectiveCoordinates_change (e.map (g w)) i j k hw).symm

 

theorem rationalCurve_ratio_meromorphicAtInfinity {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) (i j : Fin (e.N+1)) :
    ProjectiveLine.MeromorphicAtInfinity (fun z => projectiveCoordinates i (e.map (g.finite z)) j) := by
  apply (projective_ratio_meromorphic e g.infinity g.infinity_holomorphic i j 0).congr
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  rw [g.overlap z⁻¹ (inv_ne_zero hz0), inv_inv]

 

theorem rationalCurve_ratios_are_rational {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) (i j : Fin (e.N+1)) :
    ∃ p q : ℂ[X], q ≠ 0 ∧
      (∀ z, q.eval z * projectiveCoordinates i (e.map (g.finite z)) j = p.eval z) ∧
      ∀ z, q.eval z ≠ 0 → projectiveCoordinates i (e.map (g.finite z)) j = p.eval z / q.eval z :=
  ProjectiveLine.rationality
    (projective_ratio_meromorphic e g.finite g.finite_holomorphic i j)
    (rationalCurve_ratio_meromorphicAtInfinity e g i j)

namespace PolynomialTuple


theorem frequently_eval_ne_zero (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) :
    ∃ᶠ w in nhds z, p.eval w ≠ 0 := by
  by_contra h
  have he : ∀ᶠ w in nhds z, p.eval w = 0 := by simpa only [not_frequently, not_ne_iff] using h
  exact hp (p.eq_zero_of_infinite_isRoot (infinite_of_mem_nhds z he))

 

theorem common_denominator {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, ∃ p q : ℂ[X], q ≠ 0 ∧ ∀ z, q.eval z * f i z = p.eval z) :
    ∃ (P : ι → ℂ[X]) (Q : ℂ[X]), Q ≠ 0 ∧ ∀ i z, Q.eval z * f i z = (P i).eval z := by
  classical
  choose p q hq he using hf
  let Q : ℂ[X] := ∏ j, q j
  let P : ι → ℂ[X] := fun i => p i * ∏ j ∈ Finset.univ.erase i, q j
  refine ⟨P,Q,Finset.prod_ne_zero_iff.mpr (fun i _ => hq i),?_⟩
  intro i z
  have hQ : Q = q i * ∏ j ∈ Finset.univ.erase i, q j :=
    (Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)).symm
  simp only [P,hQ,Polynomial.eval_mul]
  rw [mul_assoc, mul_comm ((∏ j ∈ Finset.univ.erase i, q j).eval z), ← mul_assoc, he]

end PolynomialTuple

 

theorem rationalCurve_polynomial_presentation {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ P : Fin (e.N+1) → ℂ[X], Finset.univ.gcd P = 1 ∧
      ∀ (z : ℂ) (k j : Fin (e.N+1)), (e.map (g.finite z)).rep k ≠ 0 →
        (P j).eval z = projectiveCoordinates k (e.map (g.finite z)) j * (P k).eval z := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, (e.map (g.finite 0)).rep i ≠ 0 := by
    by_contra! h
    exact (e.map (g.finite 0)).rep_nonzero (funext h)
  obtain ⟨A,Q,hQ,hA⟩ := PolynomialTuple.common_denominator
    (fun j z => projectiveCoordinates i (e.map (g.finite z)) j)
    (fun j => by
      obtain ⟨p,q,hq,hpq,_⟩ := rationalCurve_ratios_are_rational e g i j
      exact ⟨p,q,hq,hpq⟩)
  have hAi : A i = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply infinite_of_mem_nhds (0 : ℂ)
    filter_upwards [g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds
      ((e.open_patch i).mem_nhds hi)] with z hz
    rw [← hA i z]
    simp only [projectiveCoordinates, inv_mul_cancel₀ hz, mul_one]
  let D := Finset.univ.gcd A
  have hD : D ≠ 0 := Finset.gcd_ne_zero_iff.mpr ⟨i,Finset.mem_univ i,hAi ▸ hQ⟩
  obtain ⟨P,hAP,hP⟩ := Finset.extract_gcd A (Finset.univ_nonempty)
  have hAP' : ∀ j, A j = D * P j := fun j => hAP j (Finset.mem_univ j)
  refine ⟨P,hP,?_⟩
  intro z k j hk
  have hnear : ∀ᶠ w in nhds z, (e.map (g.finite w)).rep k ≠ 0 :=
    g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)
  have hc : ContinuousAt (fun w => projectiveCoordinates k (e.map (g.finite w)) j) z :=
    (continuous_apply j).continuousAt.comp
      (((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp z
        g.finite_holomorphic.contMDiffAt).continuousAt
  apply tendsto_nhds_unique_of_frequently_eq
    (by fun_prop : ContinuousAt (fun w => (P j).eval w) z)
    (hc.mul (by fun_prop : ContinuousAt (fun w => (P k).eval w) z))
  apply ((PolynomialTuple.frequently_eval_ne_zero D hD z).and_eventually hnear).mono
  rintro w ⟨hw,hkw⟩
  have hAw : ∀ l, Q.eval w * projectiveCoordinates i (e.map (g.finite w)) l =
      D.eval w * (P l).eval w := by
    intro l
    rw [hA l w,hAP' l,Polynomial.eval_mul]
  have hiw : (e.map (g.finite w)).rep i ≠ 0 := by
    intro hzero
    obtain ⟨l,hl⟩ := PolynomialTuple.basepoint_free P hP w
    have he := hAw l
    simp only [projectiveCoordinates,hzero,inv_zero,zero_mul,mul_zero] at he
    exact hl ((mul_eq_zero.mp he.symm).resolve_left hw)
  have he : D.eval w * (P j).eval w =
      projectiveCoordinates k (e.map (g.finite w)) j * (D.eval w * (P k).eval w) := by
    rw [← hAw j,← hAw k]
    simp only [projectiveCoordinates]
    field_simp
  change (P j).eval w = projectiveCoordinates k (e.map (g.finite w)) j * (P k).eval w
  exact mul_left_cancel₀ hw (he.trans (by ring))

namespace PolynomialTuple

theorem primitive_of_basepoint_free {ι : Type*} [Fintype ι] (P : ι → ℂ[X])
    (hP : ∀ z : ℂ, ∃ i, (P i).eval z ≠ 0) : Finset.univ.gcd P = 1 := by
  classical
  rw [← Finset.normalize_gcd, normalize_eq_one]
  apply Polynomial.isUnit_iff_degree_eq_zero.mpr
  by_contra h
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root (Finset.univ.gcd P) h
  obtain ⟨i,hi⟩ := hP z
  exact hi (hz.dvd (Finset.gcd_dvd (Finset.mem_univ i)))

 
theorem reflect_transition (p : ℂ[X]) (d : ℕ) (hp : p.natDegree ≤ d)
    (z : ℂ) (hz : z ≠ 0) : (p.reflect d).eval z⁻¹ * z^d = p.eval z := by
  let := invertibleOfNonzero hz
  simpa only [invOf_eq_inv, Polynomial.eval₂_id] using
    Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z d p hp

 

theorem exists_primitive_reflection {ι : Type*} [Fintype ι] (P : ι → ℂ[X])
    (hP : Finset.univ.gcd P = 1) :
    ∃ d : ℕ, (∀ i, (P i).natDegree ≤ d) ∧
      Finset.univ.gcd (fun i => (P i).reflect d) = 1 := by
  classical
  let I := Finset.univ.filter (fun i => P i ≠ 0)
  have hI : I.Nonempty := by
    obtain ⟨i,hi⟩ := basepoint_free P hP 0
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,fun h => hi (h ▸ Polynomial.eval_zero)⟩⟩
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image I (fun j => (P j).natDegree) hI
  have hi0 := (Finset.mem_filter.mp hi).2
  have hbound : ∀ j, (P j).natDegree ≤ (P i).natDegree := by
    intro j
    by_cases hj : P j = 0
    · simp only [hj,Polynomial.natDegree_zero,Nat.zero_le]
    · exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
  refine ⟨(P i).natDegree,hbound,primitive_of_basepoint_free _ ?_⟩
  intro z
  by_cases hz : z = 0
  · refine ⟨i,?_⟩
    simpa only [hz,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_reflect,Polynomial.revAt_zero,
      Polynomial.coeff_natDegree] using (Polynomial.leadingCoeff_ne_zero.mpr hi0)
  · obtain ⟨j,hj⟩ := basepoint_free P hP z⁻¹
    refine ⟨j,?_⟩
    intro he
    have ht := reflect_transition (P j) (P i).natDegree (hbound j) z⁻¹ (inv_ne_zero hz)
    rw [inv_inv,he,zero_mul] at ht
    exact hj ht.symm

end PolynomialTuple

 

theorem rationalCurve_two_chart_polynomials {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (d : ℕ) (P Q : Fin (e.N+1) → ℂ[X]),
      Finset.univ.gcd P = 1 ∧ Finset.univ.gcd Q = 1 ∧
      (∀ i, (P i).natDegree ≤ d ∧ Q i = (P i).reflect d) ∧
      (∀ z k j, (e.map (g.finite z)).rep k ≠ 0 →
        (P j).eval z = projectiveCoordinates k (e.map (g.finite z)) j * (P k).eval z) ∧
      (∀ z k j, (e.map (g.infinity z)).rep k ≠ 0 →
        (Q j).eval z = projectiveCoordinates k (e.map (g.infinity z)) j * (Q k).eval z) ∧
      (∀ z, z ≠ 0 → ∀ i, (P i).eval z = z^d * (Q i).eval z⁻¹) := by
  obtain ⟨P,hP,hfinite⟩ := rationalCurve_polynomial_presentation e g
  obtain ⟨d,hd,hQ⟩ := PolynomialTuple.exists_primitive_reflection P hP
  let Q : Fin (e.N+1) → ℂ[X] := fun i => (P i).reflect d
  have htrans : ∀ z, z ≠ 0 → ∀ i, (P i).eval z = z^d * (Q i).eval z⁻¹ := by
    intro z hz i
    exact (PolynomialTuple.reflect_transition (P i) d (hd i) z hz).symm.trans (mul_comm _ _)
  refine ⟨d,P,Q,hP,hQ,fun i => ⟨hd i,rfl⟩,hfinite,?_,htrans⟩
  intro z k j hk
  have hnear : ∀ᶠ w in nhds z, (e.map (g.infinity w)).rep k ≠ 0 :=
    g.infinity_holomorphic.continuous.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)
  have hc : ContinuousAt (fun w => projectiveCoordinates k (e.map (g.infinity w)) j) z :=
    (continuous_apply j).continuousAt.comp
      (((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp z
        g.infinity_holomorphic.contMDiffAt).continuousAt
  apply tendsto_nhds_unique_of_frequently_eq
    (by fun_prop : ContinuousAt (fun w => (Q j).eval w) z)
    (hc.mul (by fun_prop : ContinuousAt (fun w => (Q k).eval w) z))
  have hfreq : ∃ᶠ w in nhds z, w ≠ (0 : ℂ) := by
    simpa only [Polynomial.eval_X] using
      PolynomialTuple.frequently_eval_ne_zero Polynomial.X Polynomial.X_ne_zero z
  apply (hfreq.and_eventually hnear).mono
  rintro w ⟨hw,hkw⟩
  change (Q j).eval w = projectiveCoordinates k (e.map (g.infinity w)) j * (Q k).eval w
  have ho := g.overlap w⁻¹ (inv_ne_zero hw)
  simp only [inv_inv] at ho
  have he := hfinite w⁻¹ k j (ho ▸ hkw)
  rw [ho,htrans w⁻¹ (inv_ne_zero hw) j,htrans w⁻¹ (inv_ne_zero hw) k,inv_inv] at he
  exact mul_left_cancel₀ (pow_ne_zero d (inv_ne_zero hw)) (he.trans (by ring))

end SplitTangent

end CurveImports

open Filter Topology

open Filter Topology

namespace SplitTangent.ProjectiveEmbedding
section
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)



theorem isClosed_cone [CompactSpace X.Carrier] :
    IsClosed {v : Fin (e.N+1) → ℂ | ∃ x, e.Incidence x v} := by
  have h := isClosedMap_snd_of_compactSpace _ e.isClosed_incidence
  convert h using 1
  ext v
  simp only [mem_image,mem_ofPred_eq,Prod.exists]
  aesop



theorem cone_local_equations [CompactSpace X.Carrier] {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) (hvX : ∃ x, e.Incidence x v) :
    ∃ D : (Fin (e.N+1) → ℂ) → (Fin (e.N+1) → ℂ), AnalyticAt ℂ D v ∧
      ∀ᶠ w in 𝓝 v, (∃ x, e.Incidence x w) ↔ D w = 0 := by
  obtain ⟨x,hx⟩ := hvX
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  have hvi : v i ≠ 0 := by
    intro hz
    apply hv
    ext j
    rw [(e.incidence_iff_coordinates hi).mp hx j,hz,zero_mul]
    rfl
  let c := chartAt (Model X) x
  let H := e.withinChart i x
  let n := e.normalize i
  have hcx : x ∈ c.source := mem_chart_source (Model X) x
  have hn : n v = H (c x) := by
    rw [e.incidence_iff_normalize hi hvi] at hx
    simpa [H,withinChart,c] using hx
  have hH : AnalyticAt ℂ H (c x) := e.withinChart_analytic i x hcx hi
  obtain ⟨r,hr,hr0,hri⟩ := AnalyticRetraction.exists_left_inverse hH
    (e.withinChart_immersion i x hcx hi)
  have hrn : AnalyticAt ℂ (r ∘ n) v := (hn ▸ hr).comp (e.normalize_analytic hvi)
  have hrn0 : r (n v) = c x := hn ▸ hr0
  have heq : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ (e.map y).rep i ≠ 0 ∧
      r (projectiveCoordinates i (e.map y)) = c y := by
    have hri' := (c.continuousAt hcx).eventually hri
    filter_upwards [c.open_source.mem_nhds hcx,(e.open_patch i).mem_nhds hi,hri'] with y hy hiy hry
    refine ⟨hy,hiy,?_⟩
    change r (projectiveCoordinates i (e.map (c.symm (c y)))) = c y at hry
    rwa [c.left_inv hy] at hry
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp heq
  have hloc := e.incidence_localizes hv hx hU hxU
  have hH' : AnalyticAt ℂ H ((r ∘ n) v) := by simpa only [Function.comp_apply,hrn0] using hH
  have hR : AnalyticAt ℂ (fun w => H (r (n w))) v := hH'.comp hrn
  let D := fun w => H (r (n w)) - n w
  refine ⟨D,hR.sub (e.normalize_analytic hvi),?_⟩
  have hc : ContinuousAt (fun w => c.symm (r (n w))) v := by
    apply (c.continuousAt_symm (c.map_source hcx)).comp_of_eq hrn.continuousAt
    exact hrn0
  have hx0 : c.symm (r (n v)) = x := by rw [hrn0,c.left_inv hcx]
  have hp : ∀ᶠ w in 𝓝 v, (e.map (c.symm (r (n w)))).rep i ≠ 0 :=
    hc.eventually (hx0 ▸ (e.open_patch i).mem_nhds hi)
  have hni : ∀ᶠ w in 𝓝 v, w i ≠ 0 := (continuous_apply i).continuousAt.eventually_ne hvi
  filter_upwards [hloc,hp,hni] with w hw hpw hiw
  change (∃ y, e.Incidence y w) ↔ H (r (n w)) - n w = 0
  rw [sub_eq_zero]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hcy,hiy,hry⟩ := hUsub (hw y hy)
    have hnw : n w = projectiveCoordinates i (e.map y) :=
      (e.incidence_iff_normalize hiy hiw).mp hy
    rw [hnw,hry]
    exact congrArg (projectiveCoordinates i ∘ e.map) (c.left_inv hcy)
  · intro h
    refine ⟨c.symm (r (n w)),(e.incidence_iff_normalize hpw hiw).mpr ?_⟩
    exact h.symm

theorem cone_local_equations_any [CompactSpace X.Carrier] {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) :
    ∃ D : (Fin (e.N+1) → ℂ) → (Fin (e.N+1) → ℂ), AnalyticAt ℂ D v ∧
      ∀ᶠ w in 𝓝 v, (∃ x, e.Incidence x w) ↔ D w = 0 := by
  by_cases h : ∃ x, e.Incidence x v
  · exact e.cone_local_equations hv h
  · refine ⟨fun _ => 1,analyticAt_const,?_⟩
    filter_upwards [e.isClosed_cone.isOpen_compl.mem_nhds h] with w hw
    constructor
    · exact fun hh => False.elim (hw hh)
    · intro hh
      exact False.elim (one_ne_zero (congrFun hh 0 : (1 : ℂ) = 0))

end

end SplitTangent.ProjectiveEmbedding

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.OpenManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open Manifold. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent
namespace OpenManifold
variable {d : ℕ} (U : Set (Fin d → ℂ)) (hU : IsOpen U) (hne : U.Nonempty)

lemma val_mfderiv_bijective (x : (manifold.{u} U hU hne).Carrier) :
    Function.Bijective (mfderiv (ModelWithCorners (manifold.{u} U hU hne))
      𝓘(ℂ, Fin d → ℂ) (fun y : (manifold.{u} U hU hne).Carrier => val U y) x) := by
  have H := (mdifferentiable_chart (I := ModelWithCorners (manifold.{u} U hU hne)) x).mfderiv_bijective
    (mem_chart_source (Model (manifold.{u} U hU hne)) x)
  exact H

end OpenManifold
end SplitTangent

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Families. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover
section

variable {R K F : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ R] [FiniteDimensional ℂ K] [FiniteDimensional ℂ F]

 

omit [FiniteDimensional ℂ F] in
lemma vertical_eq_zero_of_rank_le (A : R × K →L[ℂ] F) (p : F →L[ℂ] R)
    (hp : p.comp A = ContinuousLinearMap.fst ℂ R K)
    (hr : Module.finrank ℂ A.range ≤ Module.finrank ℂ R) (k : K) :
    A (0,k)=0 := by
  let q : A.range →ₗ[ℂ] R := p.toLinearMap.comp A.range.subtype
  have hq : Function.Surjective q := by
    intro r
    refine ⟨⟨A (r,0),⟨(r,0),rfl⟩⟩,?_⟩
    exact congrArg (fun B : R × K →L[ℂ] R => B (r,0)) hp
  have heq : Module.finrank ℂ A.range = Module.finrank ℂ R :=
    le_antisymm hr (LinearMap.finrank_le_finrank_of_surjective hq)
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hq
  have hh : q ⟨A (0,k),⟨(0,k),rfl⟩⟩ = q 0 := by
    simpa [q,ContinuousLinearMap.comp_apply] using congrArg (fun B : R × K →L[ℂ] R => B (0,k)) hp
  exact congrArg Subtype.val (hi hh)

 
omit [FiniteDimensional ℂ F] in
lemma finrank_range_comp_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ G]
    (a : E →L[ℂ] F) (b : G →L[ℂ] E) :
    Module.finrank ℂ (a.comp b).range ≤ Module.finrank ℂ a.range := by
  exact Submodule.finrank_mono (by
    rintro _ ⟨v,rfl⟩
    exact ⟨b v,rfl⟩)

 

lemma Patch.dimH_image_le (P : Patch F) :
    dimH P.image ≤ (2*P.dim : ℕ) := by
  have hh : dimH P.image ≤ dimH P.domain := by
    exact dimH_image_le_of_locally_lipschitzOn (fun x hx => by
      obtain ⟨C,s,hs,hC⟩ := (P.analytic x hx).contDiffAt (n := 1) |>.exists_lipschitzOnWith
      exact ⟨C,s,mem_nhdsWithin_of_mem_nhds hs,hC⟩)
  apply hh.trans
  apply (dimH_mono (subset_univ P.domain)).trans_eq
  rw [Real.dimH_univ_eq_finrank,finrank_real_of_complex,Module.finrank_fin_fun]

end

variable {E F R K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup R] [NormedSpace ℂ R]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [FiniteDimensional ℂ R] [FiniteDimensional ℂ K]

 
omit [FiniteDimensional ℂ F] in
lemma constant_vertical {H : R × K → F} {U : Set R} {V : Set K}
    (hU : IsOpen U) (hV : IsOpen V) (hVc : IsPreconnected V)
    (hH : AnalyticOnNhd ℂ H (U ×ˢ V)) (p : F →L[ℂ] R)
    (hp : ∀ z∈U ×ˢ V, p (H z)=z.1)
    (hr : ∀ z∈U ×ˢ V, Module.finrank ℂ (fderiv ℂ H z).range ≤ Module.finrank ℂ R)
    {r : R} (hrU : r∈U) {k l : K} (hk : k∈V) (hl : l∈V) :
    H (r,k)=H (r,l) := by
  have hd (v : K) (hv : v∈V) := (hH (r,v) ⟨hrU,hv⟩).differentiableAt
  have hcomp (v : K) (hv : v∈V) :
      HasFDerivAt (fun k => H (r,k))
        ((fderiv ℂ H (r,v)).comp (ContinuousLinearMap.inr ℂ R K)) v :=
    (hd v hv).hasFDerivAt.comp v
      ((hasFDerivAt_const r v).prodMk (hasFDerivAt_id v))
  have hz (v : K) (hv : v∈V) : fderiv ℂ (fun k => H (r,k)) v=0 := by
    rw [(hcomp v hv).fderiv]
    have he : (fun z => p (H z)) =ᶠ[𝓝 (r,v)] Prod.fst :=
      Filter.Eventually.mono ((hU.prod hV).mem_nhds (show (r,v)∈U ×ˢ V from ⟨hrU,hv⟩))
        (fun z hz => hp z hz)
    have heD : p.comp (fderiv ℂ H (r,v)) = ContinuousLinearMap.fst ℂ R K :=
      ((p.hasFDerivAt.comp (r,v) (hd v hv).hasFDerivAt).congr_of_eventuallyEq he.symm).unique
        hasFDerivAt_fst
    ext w
    exact vertical_eq_zero_of_rank_le _ p heD (hr (r,v) ⟨hrU,hv⟩) w
  exact hV.is_const_of_fderiv_eq_zero hVc
    (fun v hv => (hcomp v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => hz v hv) hk hl



end AnalyticZeroCover

open Filter Topology Set
open scoped ContDiff

open Filter Topology Set

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

open Filter Topology


open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology

open Set Filter Topology

open Filter Topology

open Filter Topology

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

 
lemma eventually_zero_of_all_derivatives {f : E → F} {x : E}
    (hf : AnalyticAt ℂ f x) (h : ∀ n, iteratedFDeriv ℂ n f x = 0) :
    f =ᶠ[𝓝 x] 0 := by
  obtain ⟨p,r,hp⟩ := hf
  filter_upwards [Metric.eball_mem_nhds x hp.r_pos] with y hy
  have hh := hp.hasSum_iteratedFDeriv (y := y-x) (by simpa only [Metric.mem_eball, edist_dist, dist_eq_norm, sub_zero] using hy)
  simp only [h, zero_apply, smul_zero, add_sub_cancel] at hh
  exact hh.unique (hasSum_zero)

lemma analyticAt_iterated {f : E → F} {x : E} (hf : AnalyticAt ℂ f x) (n : ℕ) :
    AnalyticAt ℂ (iteratedFDeriv ℂ n f) x :=
  (show AnalyticOnNhd ℂ f {x} from fun _ hy => mem_singleton_iff.mp hy ▸ hf).iteratedFDeriv n x
    (mem_singleton x)


lemma coeffDerivative_analytic {d n : ℕ} {f : Space d → ℂ} {x : Space d}
    (hf : AnalyticAt ℂ f x) (k : Fin n → Fin d) :
    AnalyticAt ℂ (coeffDerivative f n k) x := by
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Space d) ℂ
    (fun i => Pi.single (k i) 1)).analyticAt _).comp (analyticAt_iterated hf n)

lemma derivative_zero_of_coefficients {d n : ℕ} {f : Space d → ℂ} {x : Space d}
    (h : ∀ k : Fin n → Fin d, coeffDerivative f n k x = 0) :
    iteratedFDeriv ℂ n f x = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin n => Pi.basisFun ℂ (Fin d))
  intro k
  simpa only [coeffDerivative,Pi.basisFun_apply,ContinuousMultilinearMap.coe_coe,
    zero_apply] using h k

 

theorem exists_regular_derivative {d : ℕ} {f : Space d → ℂ} {x : Space d}
    (hf : AnalyticAt ℂ f x) (hx : f x=0) (hn : ¬ f =ᶠ[𝓝 x] 0) :
    ∃ (n : ℕ) (k : Fin n → Fin d), coeffDerivative f n k x=0 ∧
      fderiv ℂ (coeffDerivative f n k) x ≠ 0 := by
  classical
  have he : ∃ n, iteratedFDeriv ℂ n f x ≠ 0 := by
    by_contra! h
    exact hn (eventually_zero_of_all_derivatives hf h)
  let n := Nat.find he
  have hn0 : n ≠ 0 := by
    intro h
    have hh := Nat.find_spec he
    rw [show Nat.find he=0 from h] at hh
    apply hh
    ext v
    simp [iteratedFDeriv_zero_apply,hx]
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hm0 : iteratedFDeriv ℂ m f x=0 := by
    by_contra hc
    have := Nat.find_min' he hc
    dsimp [n] at hm
    omega
  have hm1 : iteratedFDeriv ℂ (m+1) f x≠0 := by
    have hh : iteratedFDeriv ℂ n f x ≠ 0 := Nat.find_spec he
    rw [hm] at hh
    exact hh
  have hk : ∃ k : Fin (m+1) → Fin d, coeffDerivative f (m+1) k x ≠ 0 := by
    by_contra! h
    exact hm1 (derivative_zero_of_coefficients h)
  obtain ⟨k,hk⟩ := hk
  refine ⟨m,Fin.tail k,?_,?_⟩
  · simp [coeffDerivative,hm0]
  · intro hz
    apply hk
    have hd := (analyticAt_iterated hf m).differentiableAt.iteratedFDeriv_succ_apply_left'
      (m := fun i => Pi.single (k i) 1)
    change iteratedFDeriv ℂ (m+1) f x (fun i => Pi.single (k i) 1)=0
    rw [hd]
    change fderiv ℂ (coeffDerivative f m (Fin.tail k)) x (Pi.single (k 0) 1)=0
    rw [hz,zero_apply]

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover

theorem regular_zero_patch {d : ℕ} {f : Space d → ℂ} {x : Space d}
    {U : Set (Space d)} (hU : IsOpen U) (hxU : x ∈ U)
    (hf : AnalyticAt ℂ f x) (hx : f x=0) (hd : fderiv ℂ f x ≠ 0) :
    ∃ P : Patch (Space d), P.dim < d ∧ P.image ⊆ U ∩ {y | f y=0} ∧
      ∃ V : Set (Space d), IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, f y=0 → y ∈ P.image := by
  classical
  let L := fderiv ℂ f x
  have hL : L.toLinearMap ≠ 0 := by
    intro hh
    apply hd
    ext v
    exact congrArg (fun q : Space d →ₗ[ℂ] ℂ => q v) hh
  have hr : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hL
  have hk := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented f L
    ((hf.contDiffAt (n := ω)).hasStrictFDerivAt (by simp)) hr hk
  let m := Module.finrank ℂ L.ker
  let e : Space m ≃L[ℂ] L.ker :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm).symm
  have hm : m < d := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hL
    have hh' : m + 1 = d := by simpa only [Space,Module.finrank_fin_fun] using hh
    omega
  have hright : AnalyticAt ℂ φ.rightFun x := by
    exact ((Classical.choose hk).analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hφ : AnalyticAt ℂ φ.implicitFunction.uncurry (φ.prodFun φ.pt) :=
    (φ.contDiffAt_implicitFunction hf.contDiffAt hright.contDiffAt (by simp)).analyticAt
  have hbase : φ.prodFun φ.pt = (0,0) := by
    ext <;> simp [φ,ImplicitFunctionData.prodFun,hx]
  have hval : φ.implicitFunction 0 0 = x := by
    have hh := mem_of_mem_nhds φ.implicitFunction_apply_image
    simpa [φ,hx] using hh
  let g : Space m → Space d := fun z => φ.implicitFunction 0 (e z)
  have hg : AnalyticAt ℂ g 0 := by
    have hh : AnalyticAt ℂ φ.implicitFunction.uncurry (0,e 0) := by
      simpa only [hbase,map_zero] using hφ
    exact AnalyticAt.comp (f := fun z : Space m => (0,e z)) (x := 0) hh
      (analyticAt_const.prod (e.analyticAt 0))
  have hg0 : g 0=x := by simpa [g] using hval
  have hfg : ∀ᶠ z in 𝓝 (0 : Space m), f (g z)=0 := by
    have ht : Tendsto (fun z : Space m => (0,e z)) (𝓝 0) (𝓝 (φ.prodFun φ.pt)) := by
      rw [hbase]
      simpa using (continuous_const.prodMk e.continuous).continuousAt.tendsto (x := 0)
    exact ht.eventually φ.leftFun_implicitFunction
  have hgU : ∀ᶠ z in 𝓝 (0 : Space m), g z∈U :=
    hg.continuousAt (hg0 ▸ hU.mem_nhds hxU)
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp
    (hg.eventually_analyticAt.and (hgU.and hfg))
  let W := Metric.ball (0 : Space m) r
  have hWo : IsOpen W := Metric.isOpen_ball
  have hW0 : (0 : Space m)∈W := Metric.mem_ball_self hr
  have hWh : ∀ z∈W, AnalyticAt ℂ g z ∧ g z∈U ∧ f (g z)=0 := hrW
  let P : Patch (Space d) := ⟨m,W,hWo,(convex_ball (0 : Space m) r).isPreconnected,
    g,fun z hz => (hWh z hz).1⟩
  refine ⟨P,hm,?_,?_⟩
  · rintro y ⟨z,hz,rfl⟩
    exact (hWh z hz).2
  · have hψ : ContinuousAt (fun y => e.symm (φ.rightFun y)) x :=
      e.symm.continuousAt.comp hright.continuousAt
    have hψ0 : e.symm (φ.rightFun x)=0 := by simp [φ]
    have hψW : ∀ᶠ y in 𝓝 x, e.symm (φ.rightFun y)∈W :=
      hψ (by simpa only [hψ0] using hWo.mem_nhds hW0)
    obtain ⟨V,hV,hVo,hVx⟩ := _root_.eventually_nhds_iff.mp
      (hψW.and φ.implicitFunction_apply_image)
    refine ⟨V,hVo,hVx,fun y hy hfy => ?_⟩
    refine ⟨e.symm (φ.rightFun y),(hV y hy).1,?_⟩
    change φ.implicitFunction 0 (e (e.symm (φ.rightFun y)))=y
    rw [e.apply_symm_apply]
    have hh := (hV y hy).2
    simpa only [show φ.leftFun y=f y from rfl,hfy] using hh

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover

 
theorem countable_regular_zero_cover {d : ℕ} {f : Space d → ℂ}
    {U : Set (Space d)} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P ∈ C, P.dim < d ∧ P.image ⊆ U) ∧
      {x | x∈U ∧ f x=0 ∧ fderiv ℂ f x≠0} ⊆ ⋃ P∈C,P.image := by
  classical
  let A := {x | x∈U ∧ f x=0 ∧ fderiv ℂ f x≠0}
  have hlocal (x : A) := regular_zero_patch hU x.property.1
    (hf x x.property.1) x.property.2.1 x.property.2.2
  choose P hdim himg V hVo hVx hVcover using hlocal
  have hcover : A ⊆ ⋃ x : A,V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hVx ⟨x,hx⟩⟩
  obtain ⟨D,hD,hDA⟩ := (HereditarilyLindelofSpace.isLindelof A).elim_countable_subcover V hVo hcover
  refine ⟨P '' D,hD.image P,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨hdim x,fun y hy => (himg x hy).1⟩
  · intro y hy
    obtain ⟨x,hx,hyV⟩ := mem_iUnion₂.mp (hDA hy)
    exact mem_iUnion₂.mpr ⟨P x,mem_image_of_mem P hx,hVcover x y hyV hy.2.1⟩

 

theorem countable_zero_cover {d : ℕ} {f : Space d → ℂ}
    {U : Set (Space d)} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hn : ∀ x∈U, f x=0 → ¬ f =ᶠ[𝓝 x] 0) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P ∈ C, P.dim < d ∧ P.image ⊆ U) ∧
      {x | x∈U ∧ f x=0} ⊆ ⋃ P∈C,P.image := by
  classical
  let I := Σ n : ℕ, Fin n → Fin d
  have hlocal (i : I) := countable_regular_zero_cover hU
    (fun x hx => coeffDerivative_analytic (hf x hx) i.2)
  choose C hC hdim hcover using hlocal
  refine ⟨⋃ i,C i,Set.countable_iUnion hC,?_,?_⟩
  · intro P hP
    obtain ⟨i,hi⟩ := mem_iUnion.mp hP
    exact hdim i P hi
  · intro x hx
    obtain ⟨n,k,hk0,hk1⟩ := exists_regular_derivative (hf x hx.1) hx.2 (hn x hx.1 hx.2)
    obtain ⟨P,hP,hxP⟩ := mem_iUnion₂.mp (hcover ⟨n,k⟩ ⟨hx.1,hk0,hk1⟩)
    exact mem_iUnion₂.mpr ⟨P,mem_iUnion.mpr ⟨⟨n,k⟩,hP⟩,hxP⟩

 
theorem countable_zero_cover_of_nonzero {d : ℕ} {f : Space d → ℂ}
    {U : Set (Space d)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) (hne : ∃ x∈U, f x≠0) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P ∈ C, P.dim < d ∧ P.image ⊆ U) ∧
      {x | x∈U ∧ f x=0} ⊆ ⋃ P∈C,P.image := by
  apply countable_zero_cover hU hf
  intro x hx _ he
  obtain ⟨y,hy,hy0⟩ := hne
  exact hy0 (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hx he hy)

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover



lemma AnalyticSetOn.closure_interior {d : ℕ} {U A : Set (Space d)}
    (h : AnalyticSetOn U A) : closure (interior A) ∩ U ⊆ interior A := by
  intro x hx
  have hxA : x∈A := h.closed ⟨closure_mono interior_subset hx.1,hx.2⟩
  obtain ⟨V,hVo,hVx,hVU,F,hF,hEq⟩ := h.local_equations x hxA
  obtain ⟨r,hr,hBV⟩ := Metric.isOpen_iff.mp hVo x hVx
  let B := Metric.ball x r
  have hBx : x∈B := Metric.mem_ball_self hr
  obtain ⟨y,hyB,hyA⟩ := mem_closure_iff.mp hx.1 B Metric.isOpen_ball hBx
  have hBA : B ⊆ A := by
    intro z hz
    apply (hEq z (hBV hz)).mpr
    intro f hf
    have hfe : f =ᶠ[𝓝 y] 0 := by
      filter_upwards [isOpen_interior.mem_nhds hyA, Metric.isOpen_ball.mem_nhds hyB]
        with w hwA hwB
      exact (hEq w (hBV hwB)).mp (interior_subset hwA) f hf
    exact (hF f hf).mono hBV |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball x r).isPreconnected hyB hfe hz
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
    (Metric.isOpen_ball.mem_nhds hBx) hBA)

 
theorem AnalyticSetOn.interior_eq_empty {d : ℕ} {U A : Set (Space d)}
    (h : AnalyticSetOn U A) (hconn : IsPreconnected U) (hne : ∃ x∈U, x∉A) :
    interior A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hU : U ⊆ interior A := hconn.subset_of_closure_inter_subset isOpen_interior
    ⟨x,h.subset (interior_subset hx),hx⟩ h.closure_interior
  obtain ⟨y,hy,hyA⟩ := hne
  exact hyA (interior_subset (hU hy))

 

lemma AnalyticSetOn.local_cover {d : ℕ} {U A : Set (Space d)}
    (h : AnalyticSetOn U A) (hconn : IsPreconnected U) (hne : ∃ x∈U, x∉A)
    {x : Space d} (hx : x∈A) :
    ∃ B : Set (Space d), IsOpen B ∧ x∈B ∧
      ∃ C : Set (Patch (Space d)), C.Countable ∧
        (∀ P∈C, P.dim < d ∧ P.image ⊆ U) ∧ A ∩ B ⊆ ⋃ P∈C,P.image := by
  classical
  obtain ⟨V,hVo,hVx,hVU,F,hF,hEq⟩ := h.local_equations x hx
  obtain ⟨r,hr,hBV⟩ := Metric.isOpen_iff.mp hVo x hVx
  let B := Metric.ball x r
  have hBx : x∈B := Metric.mem_ball_self hr
  have he : ∃ f∈F, ∃ y∈B, f y≠0 := by
    by_contra! he
    have hBA : B ⊆ A := fun y hy => (hEq y (hBV hy)).mpr (fun f hf => he f hf y hy)
    have hi : x∈interior A := mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hBx) hBA)
    rw [h.interior_eq_empty hconn hne] at hi
    exact hi
  obtain ⟨f,hf,y,hy,hy0⟩ := he
  obtain ⟨C,hC,hP,hcover⟩ := countable_zero_cover_of_nonzero Metric.isOpen_ball
    (convex_ball x r).isPreconnected ((hF f hf).mono hBV) ⟨y,hy,hy0⟩
  refine ⟨B,Metric.isOpen_ball,hBx,C,hC,?_,?_⟩
  · intro P hPC
    exact ⟨(hP P hPC).1,((hP P hPC).2.trans hBV).trans hVU⟩
  · intro z hz
    exact hcover ⟨hz.2,(hEq z (hBV hz.2)).mp hz.1 f hf⟩

 

theorem AnalyticSetOn.countable_lower_cover {d : ℕ} {U A : Set (Space d)}
    (h : AnalyticSetOn U A) (hconn : IsPreconnected U) (hne : ∃ x∈U, x∉A) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P∈C, P.dim < d ∧ P.image ⊆ U) ∧ A ⊆ ⋃ P∈C,P.image := by
  classical
  have hlocal (x : A) := h.local_cover hconn hne x.property
  choose B hBo hBx C hC hdim hcover using hlocal
  have hAB : A ⊆ ⋃ x:A,B x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hBx ⟨x,hx⟩⟩
  obtain ⟨D,hD,hDA⟩ := (HereditarilyLindelofSpace.isLindelof A).elim_countable_subcover B hBo hAB
  refine ⟨⋃ x∈D,C x,hD.biUnion (fun x _ => hC x),?_,?_⟩
  · intro P hP
    obtain ⟨x,hx,hPC⟩ := mem_iUnion₂.mp hP
    exact hdim x P hPC
  · intro z hz
    obtain ⟨x,hx,hzB⟩ := mem_iUnion₂.mp (hDA hz)
    obtain ⟨P,hPC,hzP⟩ := mem_iUnion₂.mp (hcover x ⟨hz,hzB⟩)
    exact mem_iUnion₂.mpr ⟨P, mem_iUnion₂.mpr ⟨x,hx,hPC⟩,hzP⟩

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


omit [CompleteSpace E] in
lemma Patch.comp_image_subset (P : Patch E) (Q : Patch (Space P.dim)) (h : Q.image⊆P.domain) :
    (P.comp Q h).image ⊆ P.image := by
  rintro _ ⟨z,hz,rfl⟩
  exact ⟨Q.map z,h ⟨z,hz,rfl⟩,rfl⟩

 

omit [CompleteSpace E] in
theorem Patch.countable_accepted_cover {M A : Set E}
    (test : ∀ P : Patch E, P.image ⊆ M → ¬ P.image ⊆ A →
      ∃ B : Set (Space P.dim), AnalyticSetOn P.domain B ∧
        (∃ x∈P.domain, x∉B) ∧ {x | x∈P.domain ∧ P.map x∈A} ⊆ B)
    (P : Patch E) (hPM : P.image ⊆ M) :
    ∃ C : Set (Patch E), C.Countable ∧
      (∀ Q∈C, Q.dim ≤ P.dim ∧ Q.image ⊆ M ∩ A) ∧
      P.image ∩ A ⊆ ⋃ Q∈C, Q.image := by
  classical
  generalize hd : P.dim = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hPA : P.image ⊆ A
    · refine ⟨{P},countable_singleton P,?_,?_⟩
      · intro Q hQ
        obtain rfl := mem_singleton_iff.mp hQ
        exact ⟨hd.le,fun y hy => ⟨hPM hy,hPA hy⟩⟩
      · intro y hy
        exact mem_iUnion₂.mpr ⟨P,mem_singleton P,hy.1⟩
    · obtain ⟨B,hB,hproper,hAB⟩ := test P hPM hPA
      obtain ⟨D,hD,hDdim,hcover⟩ := hB.countable_lower_cover P.preconnected_domain hproper
      have hrec (i : D) : ∃ C : Set (Patch E), C.Countable ∧
          (∀ Q∈C, Q.dim ≤ (P.comp i.val (hDdim i.val i.property).2).dim ∧
            Q.image ⊆ M ∩ A) ∧
          (P.comp i.val (hDdim i.val i.property).2).image ∩ A ⊆ ⋃ Q∈C,Q.image := by
        apply ih i.val.dim (by simpa only [← hd] using (hDdim i.val i.property).1)
          (P.comp i.val (hDdim i.val i.property).2)
          ((P.comp_image_subset i.val (hDdim i.val i.property).2).trans hPM) rfl
      choose C hC hdim hCc using hrec
      let : Countable D := hD.to_subtype
      refine ⟨⋃ i,C i,Set.countable_iUnion hC,?_,?_⟩
      · intro Q hQ
        obtain ⟨i,hi⟩ := mem_iUnion.mp hQ
        exact ⟨(hdim i Q hi).1.trans ((le_of_lt (hDdim i.val i.property).1).trans hd.le),(hdim i Q hi).2⟩
      · rintro y ⟨⟨x,hx,rfl⟩,hxy⟩
        obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp (hcover (hAB ⟨hx,hxy⟩))
        obtain ⟨z,hz,hzx⟩ := hxQ
        have hyP : P.map x∈(P.comp Q (hDdim Q hQ).2).image := by
          refine ⟨z,hz,?_⟩
          change P.map (Q.map z)=P.map x
          rw [hzx]
        obtain ⟨R,hR,hyR⟩ := mem_iUnion₂.mp (hCc ⟨Q,hQ⟩ ⟨hyP,hxy⟩)
        exact mem_iUnion₂.mpr ⟨R,mem_iUnion.mpr ⟨⟨Q,hQ⟩,hR⟩,hyR⟩

 

theorem countable_open_patches {d : ℕ} {U : Set (Space d)} (hU : IsOpen U) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P∈C, P.dim=d ∧ P.image ⊆ U) ∧ U ⊆ ⋃ P∈C,P.image := by
  classical
  have hball (x : U) : ∃ r : ℝ, 0<r ∧ Metric.ball (x : Space d) r ⊆ U :=
    Metric.isOpen_iff.mp hU x x.property
  choose r hr hsub using hball
  let P : U → Patch (Space d) := fun x =>
    ⟨d,Metric.ball (x : Space d) (r x),Metric.isOpen_ball,
      (convex_ball (x : Space d) (r x)).isPreconnected,id,fun _ _ => analyticAt_id⟩
  obtain ⟨D,hD,hDU⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    (fun x : U => Metric.ball (x : Space d) (r x)) (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hr ⟨x,hx⟩)⟩)
  refine ⟨P '' D,hD.image P,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨rfl,?_⟩
    rintro y ⟨z,hz,rfl⟩
    exact hsub x hz
  · intro z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp (hDU hz)
    exact mem_iUnion₂.mpr ⟨P x,mem_image_of_mem P hx,⟨z,hzx,rfl⟩⟩

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

namespace SplitTangent.RationalParameters
open AnalyticZeroCover

lemma ev_continuous {N d : ℕ} (b : Bool) :
    Continuous (fun z : ℂ × Coeff N d => ev b z.2 z.1) :=
  continuous_iff_continuousAt.mpr (fun a => (ev_analytic b a).continuousAt)

lemma isOpen_regular (N d : ℕ) : IsOpen (regular N d) := by
  let K := Metric.closedBall (0 : ℂ) 1
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  have h (b : Bool) : IsOpen {τ : Coeff N d | ∀ z : K, ev b τ z≠0} := by
    have hc : IsClosed {z : K × Coeff N d | ev b z.2 z.1=0} :=
      isClosed_eq ((ev_continuous b).comp (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd))
        continuous_const
    have hp := isClosedMap_snd_of_compactSpace _ hc
    convert hp.isOpen_compl using 1
    ext τ
    simp
  convert isOpen_iInter_of_finite h using 1
  ext τ
  simp [regular,K]


variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) [CompactSpace X.Carrier]
variable (x₀ : X.Carrier) {d : ℕ} (P : Patch (Coeff e.N d))
variable (hP : P.image ⊆ regular e.N d ∩ accepted e d)


include hP in
lemma pairEvaluation_holomorphicAt {τ : Space P.dim} (hτ : τ∈P.domain) :
    ContMDiffAt 𝓘(ℂ,Space P.dim) ((ModelWithCorners X).prod (ModelWithCorners X)) ω
      (pairEvaluation e x₀ P) τ := by
  apply ContMDiffAt.prodMk
  · exact (evaluation_holomorphicAt e x₀ P hP false hτ).comp τ
      (contMDiffAt_const.prodMk_space contMDiffAt_id)
  · exact (evaluation_holomorphicAt e x₀ P hP false hτ).comp τ
      (contMDiffAt_const.prodMk_space contMDiffAt_id)



end SplitTangent.RationalParameters

 

open Set Filter Topology
open scoped ContDiff Manifold



open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff


 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover
variable {E F R K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup R] [NormedSpace ℂ R]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [FiniteDimensional ℂ R] [FiniteDimensional ℂ K]

theorem local_image_patch {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x∈U) (hf : AnalyticOnNhd ℂ f U)
    (p : F →L[ℂ] R) (hs : Function.Surjective (p.comp (fderiv ℂ f x)))
    (hr : ∀ y∈U, Module.finrank ℂ (fderiv ℂ f y).range ≤ Module.finrank ℂ R) :
    ∃ P : Patch F, P.dim=Module.finrank ℂ R ∧
      ∃ W : Set E, IsOpen W ∧ x∈W ∧ W⊆U ∧ f '' W ⊆ P.image := by
  classical
  let g : E → R := fun y => p (f y)
  let L := p.comp (fderiv ℂ f x)
  have hg : AnalyticAt ℂ g x := (p.analyticAt _).comp (hf x hx)
  have hgD : HasStrictFDerivAt g L x :=
    p.hasStrictFDerivAt.comp x (((hf x hx).contDiffAt (n := ω)).hasStrictFDerivAt (by simp))
  have hL : L.range=⊤ := LinearMap.range_eq_top.mpr hs
  have hK := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented g L hgD hL hK
  have hright : AnalyticAt ℂ φ.rightFun x :=
    ((Classical.choose hK).analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hφ : AnalyticAt ℂ φ.implicitFunction.uncurry (φ.prodFun φ.pt) :=
    (φ.contDiffAt_implicitFunction hg.contDiffAt hright.contDiffAt (by simp)).analyticAt
  have hbase : φ.prodFun φ.pt=(g x,0) := by
    ext <;> simp [φ,ImplicitFunctionData.prodFun]
  have hval : φ.implicitFunction (g x) 0=x := by
    have hh := mem_of_mem_nhds φ.implicitFunction_apply_image
    simpa [φ] using hh
  have hφ' : AnalyticAt ℂ φ.implicitFunction.uncurry (g x,0) := hbase ▸ hφ
  have hφU : ∀ᶠ z in 𝓝 (g x,(0 : L.ker)), φ.implicitFunction.uncurry z∈U :=
    hφ'.continuousAt (by simpa only [Function.uncurry_apply_pair,hval] using hU.mem_nhds hx)
  have hφp : ∀ᶠ z in 𝓝 (g x,(0 : L.ker)), p (f (φ.implicitFunction.uncurry z))=z.1 := by
    change ∀ᶠ z in 𝓝 (g x,(0 : L.ker)), φ.leftFun (φ.implicitFunction z.1 z.2)=z.1
    rw [← hbase]
    exact φ.leftFun_implicitFunction
  obtain ⟨ε,hε,hεprop⟩ := Metric.mem_nhds_iff.mp
    (hφ'.eventually_analyticAt.and (hφU.and hφp))
  let A := Metric.ball (g x) ε
  let B := Metric.ball (0 : L.ker) ε
  have hAB : A ×ˢ B = Metric.ball (g x,(0 : L.ker)) ε := by
    ext z
    simp only [A,B,mem_prod,Metric.mem_ball,Prod.dist_eq,max_lt_iff]
  let H : R × L.ker → F := f ∘ φ.implicitFunction.uncurry
  have hprop (z : R × L.ker) (hz : z∈A ×ˢ B) :
      AnalyticAt ℂ φ.implicitFunction.uncurry z ∧
        φ.implicitFunction.uncurry z∈U ∧ p (H z)=z.1 := hεprop (hAB ▸ hz)
  have hH : AnalyticOnNhd ℂ H (A ×ˢ B) := fun z hz =>
    (hf _ (hprop z hz).2.1).comp (hprop z hz).1
  have hrH : ∀ z∈A ×ˢ B, Module.finrank ℂ (fderiv ℂ H z).range ≤ Module.finrank ℂ R := by
    intro z hz
    rw [fderiv_comp z (hf _ (hprop z hz).2.1).differentiableAt (hprop z hz).1.differentiableAt]
    exact (finrank_range_comp_le _ _).trans (hr _ (hprop z hz).2.1)
  have hconst {r : R} (hrA : r∈A) {k : L.ker} (hkB : k∈B) : H (r,k)=H (r,0) :=
    constant_vertical Metric.isOpen_ball Metric.isOpen_ball (convex_ball (0 : L.ker) ε).isPreconnected
      hH p (fun z hz => (hprop z hz).2.2) hrH hrA hkB (Metric.mem_ball_self hε)
  let e : Space (Module.finrank ℂ R) ≃L[ℂ] R :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm).symm
  let q : Space (Module.finrank ℂ R) → F := fun z => H (e z,0)
  let c := e.symm (g x)
  have hcA : e c ∈ A := by simpa [c,A] using Metric.mem_ball_self hε (x := g x)
  have hq : AnalyticAt ℂ q c :=
    AnalyticAt.comp (f := fun z => (e z,(0 : L.ker))) (x := c)
      (hH (e c,0) ⟨hcA,Metric.mem_ball_self hε⟩) ((e.analyticAt c).prod analyticAt_const)
  obtain ⟨δ,hδ,hδprop⟩ := Metric.mem_nhds_iff.mp
    (hq.eventually_analyticAt.and (e.continuousAt (Metric.isOpen_ball.mem_nhds hcA)))
  let P : Patch F := ⟨Module.finrank ℂ R,Metric.ball c δ,Metric.isOpen_ball,
    (convex_ball c δ).isPreconnected,q,fun z hz => (hδprop hz).1⟩
  have hnear : ∀ᶠ y in 𝓝 x, e.symm (g y) ∈ Metric.ball c δ :=
    (e.symm.continuousAt.comp hg.continuousAt) (Metric.ball_mem_nhds c hδ)
  have hknear : ∀ᶠ y in 𝓝 x, φ.rightFun y∈B :=
    hright.continuousAt (by simpa [φ,B] using Metric.ball_mem_nhds (0 : L.ker) hε)
  obtain ⟨W,hW,hWo,hWx⟩ := _root_.eventually_nhds_iff.mp
    (Filter.Eventually.and (hU.mem_nhds hx) (hnear.and (hknear.and φ.implicitFunction_apply_image)))
  refine ⟨P,rfl,W,hWo,hWx,fun y hy => (hW y hy).1,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  refine ⟨e.symm (g y),(hW y hy).2.1,?_⟩
  change H (e (e.symm (g y)),0)=f y
  rw [e.apply_symm_apply]
  have hgA : g y∈A := by
    have hh := (hδprop (hW y hy).2.1).2
    simpa only [e.apply_symm_apply] using hh
  rw [← hconst hgA (hW y hy).2.2.1]
  change f (φ.implicitFunction (g y) (φ.rightFun y))=f y
  exact congrArg f (hW y hy).2.2.2

end AnalyticZeroCover


 

open Set Filter Topology
open scoped ContDiff
namespace AnalyticZeroCover

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]


omit [FiniteDimensional ℂ E] in
lemma pivot_analytic {r : ℕ} {f : E → F} {x : E} (hf : AnalyticAt ℂ f x)
    (p : F →L[ℂ] Space r) (s : Space r →L[ℂ] E) : AnalyticAt ℂ (pivot f p s) x := by
  classical
  have hentry (i j : Fin r) : AnalyticAt ℂ
      (fun y => p (fderiv ℂ f y (s (Pi.single j 1))) i) x :=
    ((ContinuousLinearMap.proj i).analyticAt _).comp ((p.analyticAt _).comp
      (((ContinuousLinearMap.apply ℂ F (s (Pi.single j 1))).analyticAt _).comp hf.fderiv))
  change AnalyticAt ℂ (fun y => LinearMap.det ((p.comp (fderiv ℂ f y)).comp s).toLinearMap) x
  simp only [← LinearMap.det_toMatrix',Matrix.det_apply',LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply]
  apply Finset.analyticAt_fun_sum
  intro σ hσ
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact hentry (σ i) i

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
lemma pivot_surjective {r : ℕ} {f : E → F} {x : E}
    (p : F →L[ℂ] Space r) (s : Space r →L[ℂ] E) (h : pivot f p s x ≠ 0) :
    Function.Surjective (p.comp (fderiv ℂ f x)) := by
  let A := ((p.comp (fderiv ℂ f x)).comp s).toLinearMap
  have hker : A.ker=⊥ := by
    by_contra hh
    exact h (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hh)
  have hi : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  have hs := LinearMap.injective_iff_surjective.mp hi
  intro y
  obtain ⟨z,hz⟩ := hs y
  exact ⟨s z,hz⟩

 

omit [FiniteDimensional ℂ F] in
lemma exists_pivot (L : E →L[ℂ] F) :
    ∃ (p : F →L[ℂ] Space (Module.finrank ℂ L.range))
      (s : Space (Module.finrank ℂ L.range) →L[ℂ] E),
      (p.comp L).comp s = ContinuousLinearMap.id ℂ _ := by
  classical
  obtain ⟨q,hq⟩ := Submodule.ClosedComplemented.of_finiteDimensional L.range
  let e : L.range ≃L[ℂ] Space (Module.finrank ℂ L.range) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  let p := e.toContinuousLinearMap.comp q
  have hp : Function.Surjective (p.comp L) := by
    intro y
    obtain ⟨v,hv⟩ := (e.symm y).property
    refine ⟨v,?_⟩
    change e (q (L v))=y
    change L v = (e.symm y : F) at hv
    rw [hv,hq,e.apply_symm_apply]
  obtain ⟨s,hs⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hp
  exact ⟨p,s,ContinuousLinearMap.ext hs⟩

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff ENNReal
namespace AnalyticZeroCover

 
lemma dimH_image_le_of_local {E F : Type*} [TopologicalSpace E]
    [SecondCountableTopology E] [EMetricSpace F] {f : E → F} {V : Set E} {a : ℝ≥0∞}
    (h : ∀ x∈V, ∃ W : Set E, IsOpen W ∧ x∈W ∧ dimH (f '' W)≤a) :
    dimH (f '' V)≤a := by
  classical
  choose W hWo hxW hdim using (fun x : V => h x x.property)
  obtain ⟨D,hD,hcover⟩ := (HereditarilyLindelofSpace.isLindelof V).elim_countable_subcover
    W hWo (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxW ⟨x,hx⟩⟩)
  apply (dimH_mono (show f '' V ⊆ ⋃ i∈D,f '' W i from ?_)).trans
  · rw [dimH_bUnion hD]
    exact iSup₂_le (fun i _ => hdim i)
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨i,hi,mem_image_of_mem f hxi⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

 

theorem rank_dimH_le {d r : ℕ} {f : Space d → F} {U : Set (Space d)}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (hr : ∀ x∈U, Module.finrank ℂ (fderiv ℂ f x).range ≤ r) :
    dimH (f '' U) ≤ (2*r : ℕ) := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hne : U.Nonempty
    · let m := Nat.findGreatest (fun k => ∃ x∈U, Module.finrank ℂ (fderiv ℂ f x).range=k) r
      obtain ⟨x,hx,hxm⟩ : ∃ x∈U, Module.finrank ℂ (fderiv ℂ f x).range=m :=
        Nat.findGreatest_spec (P := fun k => ∃ x∈U, Module.finrank ℂ (fderiv ℂ f x).range=k) (hr hne.choose hne.choose_spec)
          ⟨hne.choose,hne.choose_spec,rfl⟩
      have hm : m≤r := Nat.findGreatest_le r
      have hmax : ∀ y∈U, Module.finrank ℂ (fderiv ℂ f y).range ≤ m := fun y hy =>
        Nat.le_findGreatest (hr y hy) ⟨y,hy,rfl⟩
      obtain ⟨p,s,hps⟩ := exists_pivot (fderiv ℂ f x)
      let θ := pivot f p s
      have hθ : AnalyticOnNhd ℂ θ U := fun y hy => pivot_analytic (hf y hy) p s
      have hθx : θ x≠0 := by
        change LinearMap.det _ ≠ 0
        rw [hps]
        simp
      let V := {y | y∈U ∧ θ y≠0}
      have hV : dimH (f '' V)≤(2*r : ℕ) := by
        apply dimH_image_le_of_local
        intro y hy
        obtain ⟨P,hP,W,hWo,hyW,hWU,hcov⟩ := local_image_patch hU hy.1 hf p
          (pivot_surjective p s hy.2) (fun z hz => by simpa only [Module.finrank_fin_fun,hxm] using hmax z hz)
        refine ⟨W,hWo,hyW,(dimH_mono hcov).trans (P.dimH_image_le.trans ?_)⟩
        exact_mod_cast Nat.mul_le_mul_left 2 (by simpa only [hP,Module.finrank_fin_fun,hxm] using hm)
      obtain ⟨C,hC,hCdim,hcover⟩ := countable_zero_cover_of_nonzero hU hUc hθ ⟨x,hx,hθx⟩
      have hrest (Q : C) : dimH ((f ∘ Q.val.map) '' Q.val.domain) ≤ (2*r : ℕ) := by
        apply ih Q.val.dim (hCdim Q.val Q.property).1 Q.val.isOpen_domain Q.val.preconnected_domain
          (fun z hz => (hf _ ((hCdim Q.val Q.property).2 ⟨z,hz,rfl⟩)).comp (Q.val.analytic z hz))
        intro z hz
        rw [fderiv_comp z (hf _ ((hCdim Q.val Q.property).2 ⟨z,hz,rfl⟩)).differentiableAt
          (Q.val.analytic z hz).differentiableAt]
        exact (finrank_range_comp_le _ _).trans (hr _ ((hCdim Q.val Q.property).2 ⟨z,hz,rfl⟩))
      have hsub : f '' U ⊆ f '' V ∪ ⋃ Q∈C,(f ∘ Q.map) '' Q.domain := by
        rintro _ ⟨y,hy,rfl⟩
        by_cases hθy : θ y=0
        · obtain ⟨Q,hQ,z,hz,hzy⟩ := mem_iUnion₂.mp (hcover ⟨hy,hθy⟩)
          exact Or.inr (mem_iUnion₂.mpr ⟨Q,hQ,z,hz,congrArg f hzy⟩)
        · exact Or.inl ⟨y,⟨hy,hθy⟩,rfl⟩
      apply (dimH_mono hsub).trans
      rw [dimH_union,dimH_bUnion hC]
      exact max_le hV (iSup₂_le (fun Q hQ => hrest ⟨Q,hQ⟩))
    · rw [not_nonempty_iff_eq_empty.mp hne,image_empty,dimH_empty]
      exact bot_le

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff ENNReal
namespace AnalyticZeroCover
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

lemma finrank_range_lt_of_not_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] F) (hL : ¬Function.Surjective L) :
    Module.finrank ℂ L.range < Module.finrank ℂ F := by
  apply lt_of_le_of_ne L.range.finrank_le
  intro heq
  exact hL (LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq heq))

lemma rank_dimH_le_open {d r : ℕ} {f : Space d → F} {U : Set (Space d)}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hr : ∀x∈U,Module.finrank ℂ (fderiv ℂ f x).range≤r) :
    dimH (f '' U)≤(2*r : ℕ) := by
  apply dimH_image_le_of_local
  intro x hx
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU x hx
  exact ⟨Metric.ball x ε,Metric.isOpen_ball,Metric.mem_ball_self hε,
    rank_dimH_le Metric.isOpen_ball (convex_ball x ε).isPreconnected
      (hf.mono hεU) (fun y hy => hr y (hεU hy))⟩

 

theorem exists_surjective_of_countable_cover {A : Type*} [Countable A]
    (d : A → ℕ) (U : ∀a,Set (Space (d a))) (f : ∀a,Space (d a) → F)
    (hU : ∀a,IsOpen (U a)) (hf : ∀a,AnalyticOnNhd ℂ (f a) (U a))
    {V : Set F} (hV : IsOpen V) (hne : V.Nonempty)
    (hcover : V ⊆ ⋃a,f a '' U a) (hdim : 0<Module.finrank ℂ F) :
    ∃a, ∃x, x∈U a ∧ Function.Surjective (fderiv ℂ (f a) x) := by
  classical
  by_contra! hbad
  have hpiece (a : A) : dimH (f a '' U a) ≤ (2*(Module.finrank ℂ F-1) : ℕ) :=
    rank_dimH_le_open (hU a) (hf a) (fun x hx => Nat.le_sub_one_of_lt
      (finrank_range_lt_of_not_surjective _ (hbad a x hx)))
  have hbound : dimH V ≤ (2*(Module.finrank ℂ F-1) : ℕ) := by
    apply (dimH_mono hcover).trans
    rw [dimH_iUnion]
    exact iSup_le hpiece
  obtain ⟨x,hx⟩ := hne
  have hc : Module.finrank ℝ F = 2*Module.finrank ℂ F := by
    rw [← Module.finrank_mul_finrank ℝ ℂ F,Complex.finrank_real_complex]
  rw [Real.dimH_of_mem_nhds (hV.mem_nhds hx),hc] at hbound
  have hnat : 2*Module.finrank ℂ F ≤ 2*(Module.finrank ℂ F-1) := by exact_mod_cast hbound
  omega

end AnalyticZeroCover

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold
namespace SplitTangent
open AnalyticZeroCover

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℂ,F) ω M]

 
theorem exists_chart_submersion_of_cover {A : Type*} [Countable A]
    (d : A → ℕ) (U : ∀a,Set (Space (d a))) (f : ∀a,Space (d a) → M)
    (hU : ∀a,IsOpen (U a))
    (hf : ∀a, ∀x∈U a,ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,F) ω (f a) x)
    {V : Set M} (hV : IsOpen V) (hne : V.Nonempty)
    (hcover : V ⊆ ⋃a,f a '' U a) (hdim : 0<Module.finrank ℂ F) :
    ∃y : M, ∃a, ∃x∈U a, f a x∈(chartAt F y).source ∧
      Function.Surjective (fderiv ℂ ((chartAt F y) ∘ f a) x) := by
  classical
  obtain ⟨y,hy⟩ := hne
  let c := chartAt F y
  let W (a : A) := U a ∩ (f a) ⁻¹' c.source
  have hW (a : A) : IsOpen (W a) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact Filter.inter_mem (hU a |>.mem_nhds hx.1)
      ((hf a x hx.1).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx.2))
  have hc : c∈maximalAtlas 𝓘(ℂ,F) ω M := IsManifold.chart_mem_maximalAtlas y
  have hanalytic (a : A) : AnalyticOnNhd ℂ (c ∘ f a) (W a) := by
    intro x hx
    exact ((contMDiffAt_of_mem_maximalAtlas hc hx.2).comp x (hf a x hx.1)).contDiffAt.analyticAt
  let Z := c.target ∩ c.symm ⁻¹' V
  have hZ : IsOpen Z := c.isOpen_inter_preimage_symm hV
  have hZn : Z.Nonempty := ⟨c y,c.map_source (mem_chart_source F y),by
    change c.symm (c y)∈V
    rw [c.left_inv (mem_chart_source F y)]
    exact hy⟩
  have hZcov : Z ⊆ ⋃a,(c ∘ f a) '' W a := by
    intro z hz
    obtain ⟨a,x,hx,hfx⟩ := mem_iUnion.mp (hcover hz.2)
    refine mem_iUnion.mpr ⟨a,x,⟨hx,?_⟩,?_⟩
    · change f a x∈c.source
      rw [hfx]
      exact c.map_target hz.1
    · change c (f a x)=z
      rw [hfx,c.right_inv hz.1]
  obtain ⟨a,x,hx,hs⟩ := exists_surjective_of_countable_cover d W
    (fun a => c ∘ f a) hW hanalytic hZ hZn hZcov hdim
  exact ⟨y,a,x,hx.1,hx.2,hs⟩

 
omit [FiniteDimensional ℂ F] in
lemma surjective_mfderiv_of_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → M} {x : E} (hf : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f x)
    (y : M) (hy : f x∈(chartAt F y).source)
    (hs : Function.Surjective (fderiv ℂ ((chartAt F y) ∘ f) x)) :
    Function.Surjective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x) := by
  have hc := mdifferentiable_chart (I := 𝓘(ℂ,F)) y
  have hchain := mfderiv_comp x (hc.mdifferentiableAt hy) (hf.mdifferentiableAt (by decide))
  rw [mfderiv_eq_fderiv] at hchain
  intro w
  obtain ⟨v,hv⟩ := hs (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) (chartAt F y) (f x) w)
  refine ⟨v,hc.mfderiv_injective hy ?_⟩
  change ((mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) (chartAt F y) (f x)).comp
    (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x)) v = _
  rw [← hchain]
  exact hv

 

lemma eventually_surjective_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : E → F} {x : E} (hf : AnalyticAt ℂ f x)
    (hs : Function.Surjective (fderiv ℂ f x)) :
    ∀ᶠy in 𝓝 x, Function.Surjective (fderiv ℂ f y) := by
  let e : F ≃L[ℂ] Space (Module.finrank ℂ F) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  obtain ⟨s,hs⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
    (f := e.toContinuousLinearMap.comp (fderiv ℂ f x)) (e.surjective.comp hs)
  have heq : (e.toContinuousLinearMap.comp (fderiv ℂ f x)).comp s = ContinuousLinearMap.id ℂ _ :=
    ContinuousLinearMap.ext hs
  have hp : pivot f e.toContinuousLinearMap s x≠0 := by
    change LinearMap.det _ ≠ 0
    rw [heq]
    simp
  apply ((pivot_analytic hf e.toContinuousLinearMap s).continuousAt.eventually_ne hp).mono
  intro y hy z
  obtain ⟨v,hv⟩ := pivot_surjective e.toContinuousLinearMap s hy (e z)
  exact ⟨v,e.injective hv⟩

end SplitTangent

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalAccepted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Accepted. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

universe u
namespace SplitTangent.RationalParameters
open AnalyticZeroCover

variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) [CompactSpace X.Carrier]

 

lemma analyticSetOn_incidenceAlternative {m : ℕ} {U : Set (Space m)} (hU : IsOpen U)
    {Q : Space m → Fin (e.N+1) → ℂ} (hQ : AnalyticOnNhd ℂ Q U)
    (hnz : ∀ z∈U, Q z≠0) :
    AnalyticSetOn U {z | z∈U ∧ ∃ x, e.Incidence x (Q z)} where
  subset := fun _ h => h.1
  closed := by
    intro z hz
    refine ⟨hz.2,?_⟩
    change Q z ∈ {v | ∃ x, e.Incidence x v}
    rw [← e.isClosed_cone.closure_eq]
    exact (closure_mono (show Q '' {z | z∈U ∧ ∃ x, e.Incidence x (Q z)} ⊆
        {v | ∃ x, e.Incidence x v} from by rintro _ ⟨y,hy,rfl⟩; exact hy.2)
        (mem_closure_image (hQ z hz.2).continuousAt hz.1))
  local_equations := by
    intro z hz
    obtain ⟨D,hD,hDeq⟩ := e.cone_local_equations_any (hnz z hz.1)
    have hcomp : AnalyticAt ℂ (D ∘ Q) z := hD.comp (hQ z hz.1)
    have heq := (hQ z hz.1).continuousAt.eventually hDeq
    obtain ⟨V,hV,hVo,hVz⟩ := eventually_nhds_iff.mp
      (Filter.Eventually.and (hU.mem_nhds hz.1) (hcomp.eventually_analyticAt.and heq))
    let f : Fin (e.N+1) → Space m → ℂ := fun i y => D (Q y) i
    refine ⟨V,hVo,hVz,fun y hy => (hV y hy).1,Set.range f,?_,?_⟩
    · rintro g ⟨i,rfl⟩ y hy
      exact ((ContinuousLinearMap.proj i).analyticAt _).comp (hV y hy).2.1
    · intro y hy
      simp only [mem_ofPred_eq,forall_mem_range]
      have hyU : y∈U := (hV y hy).1
      simp only [hyU,true_and]
      rw [(hV y hy).2.2]
      exact ⟨fun h i => congrFun h i,fun h => funext h⟩

lemma accepted_test {d : ℕ} (P : Patch (Coeff e.N d))
    (hPM : P.image ⊆ regular e.N d) (hPA : ¬P.image ⊆ accepted e d) :
    ∃ B : Set (Space P.dim), AnalyticSetOn P.domain B ∧
      (∃ x∈P.domain, x∉B) ∧ {x | x∈P.domain ∧ P.map x∈accepted e d} ⊆ B := by
  classical
  obtain ⟨τ,hτ,hτA⟩ := Set.not_subset.mp hPA
  obtain ⟨x,hx,rfl⟩ := hτ
  have hn : ∃ b : Bool, ∃ z : ℂ, ¬∃ y, e.Incidence y (ev b (P.map x) z) := by
    simpa only [accepted,mem_ofPred_eq,not_forall] using hτA
  obtain ⟨b,z,hbad⟩ := hn
  let Q : Space P.dim → (Fin (e.N+1) → ℂ) := fun y => ev b (P.map y) z
  have hQ : AnalyticOnNhd ℂ Q P.domain := fun y hy =>
    AnalyticAt.comp (f := fun y => (z,P.map y)) (x := y) (ev_analytic b (z,P.map y))
      (analyticAt_const.prod (P.analytic y hy))
  refine ⟨{y | y∈P.domain ∧ ∃ q, e.Incidence q (Q y)},
    analyticSetOn_incidenceAlternative e P.isOpen_domain hQ
      (fun y hy => regular_nonzero (hPM ⟨y,hy,rfl⟩) b z),?_,?_⟩
  · exact ⟨x,hx,fun h => hbad h.2⟩
  · intro y hy
    exact ⟨hy.1,hy.2 b z⟩

 

theorem countable_accepted {d : ℕ} :
    ∃ C : Set (Patch (Coeff e.N d)), C.Countable ∧
      (∀ P∈C, P.image ⊆ regular e.N d ∩ accepted e d) ∧
      regular e.N d ∩ accepted e d ⊆ ⋃ P∈C,P.image := by
  classical
  obtain ⟨D,hD,hDdim,hcover⟩ := countable_open_patches (isOpen_regular e.N d)
  have H (i : D) := i.val.countable_accepted_cover (accepted_test e) (hDdim i.val i.property).2
  choose C hC hCp hCc using H
  let : Countable D := hD.to_subtype
  refine ⟨⋃ i,C i,Set.countable_iUnion hC,?_,?_⟩
  · intro P hP
    obtain ⟨i,hi⟩ := mem_iUnion.mp hP
    exact (hCp i P hi).2
  · intro τ hτ
    obtain ⟨P,hP,hτP⟩ := mem_iUnion₂.mp (hcover hτ.1)
    obtain ⟨Q,hQ,hτQ⟩ := mem_iUnion₂.mp (hCc ⟨P,hP⟩ ⟨hτP,hτ.2⟩)
    exact mem_iUnion₂.mpr ⟨Q,mem_iUnion.mpr ⟨⟨P,hP⟩,hQ⟩,hτQ⟩

end SplitTangent.RationalParameters

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Encoding. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators
universe u
namespace SplitTangent.RationalParameters


lemma ev_ofPolynomials_false {N d : ℕ} (P : Fin (N+1) → Polynomial ℂ)
    (hP : ∀ i, (P i).natDegree≤d) (z : ℂ) :
    ev false (ofPolynomials d P) z = fun i => (P i).eval z := by
  ext i
  simp only [ev,ofPolynomials,Equiv.symm_apply_apply,Bool.false_eq_true,↓reduceIte]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hP i))]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => (P i).coeff k * z^k) (d+1)

lemma ev_ofPolynomials_true {N d : ℕ} (P : Fin (N+1) → Polynomial ℂ)
    (hP : ∀ i, (P i).natDegree≤d) (z : ℂ) :
    ev true (ofPolynomials d P) z = fun i => ((P i).reflect d).eval z := by
  ext i
  apply tendsto_nhds_unique_of_frequently_eq
    ((continuous_apply i).comp ((ev_continuous true).comp (continuous_id.prodMk continuous_const))).continuousAt
    (by fun_prop : ContinuousAt (fun w => ((P i).reflect d).eval w) z)
  have hfreq : ∃ᶠ w in 𝓝 z, w≠(0 : ℂ) := by
    simpa only [Polynomial.eval_X] using
      PolynomialTuple.frequently_eval_ne_zero Polynomial.X Polynomial.X_ne_zero z
  apply hfreq.mono
  intro w hw
  have he := congrFun (ev_transition (ofPolynomials d P) (inv_ne_zero hw)) i
  rw [ev_ofPolynomials_false P hP,inv_inv] at he
  have hp := PolynomialTuple.reflect_transition (P i) d (hP i) w⁻¹ (inv_ne_zero hw)
  simp only [inv_inv] at hp
  change (P i).eval w⁻¹ = w⁻¹ ^ d * ev true (ofPolynomials d P) w i at he
  exact mul_left_cancel₀ (pow_ne_zero d (inv_ne_zero hw))
    (he.symm.trans (hp.symm.trans (mul_comm _ _)))

 

theorem curve_encoding {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ d : ℕ, ∃ τ : Coeff e.N d, τ∈regular e.N d ∩ accepted e d ∧
      (∀ z, e.Incidence (g.finite z) (ev false τ z)) ∧
      (∀ z, e.Incidence (g.infinity z) (ev true τ z)) := by
  classical
  obtain ⟨d,P,Q,hP,hQ,hdeg,hfinite,hinfty,htrans⟩ := rationalCurve_two_chart_polynomials e g
  let τ := ofPolynomials d P
  have hτf (z : ℂ) : ev false τ z = fun i => (P i).eval z :=
    ev_ofPolynomials_false P (fun i => (hdeg i).1) z
  have hτi (z : ℂ) : ev true τ z = fun i => (Q i).eval z := by
    rw [ev_ofPolynomials_true P (fun i => (hdeg i).1)]
    ext i
    rw [← (hdeg i).2]
  have hf (z : ℂ) : e.Incidence (g.finite z) (ev false τ z) := by
    obtain ⟨k,hk⟩ := Function.ne_iff.mp (e.map (g.finite z)).rep_nonzero
    apply (e.incidence_iff_coordinates hk).mpr
    intro j
    simpa only [hτf] using (hfinite z k j hk).trans (mul_comm _ _)
  have hi (z : ℂ) : e.Incidence (g.infinity z) (ev true τ z) := by
    obtain ⟨k,hk⟩ := Function.ne_iff.mp (e.map (g.infinity z)).rep_nonzero
    apply (e.incidence_iff_coordinates hk).mpr
    intro j
    simpa only [hτi] using (hinfty z k j hk).trans (mul_comm _ _)
  refine ⟨d,τ,⟨?_,?_⟩,hf,hi⟩
  · intro b z hz
    cases b
    · obtain ⟨i,hi⟩ := PolynomialTuple.basepoint_free P hP z
      intro he
      have hh := congrFun he i
      rw [hτf] at hh
      exact hi hh
    · obtain ⟨i,hi⟩ := PolynomialTuple.basepoint_free Q hQ z
      intro he
      have hh := congrFun he i
      rw [hτi] at hh
      exact hi hh
  · intro b z
    cases b
    · exact ⟨g.finite z,hf z⟩
    · exact ⟨g.infinity z,hi z⟩

end SplitTangent.RationalParameters

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Reparam. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent.RationalCurve
variable {X : ComplexManifold.{u}} (g : RationalCurve X)



theorem normalize_endpoints (a b : OnePoint ℂ) (hab : a≠b) :
    ∃ h : RationalCurve X, h.finite 0=g.value a ∧ h.finite 1=g.value b := by
  classical
  induction a using OnePoint.rec with
  | infty =>
    induction b using OnePoint.rec with
    | infty => exact (hab rfl).elim
    | coe b =>
      let h := g.mobius (b-1) 1 1 0 (by norm_num)
      refine ⟨h,?_,?_⟩
      · simp [h,mobius,homogeneousValue,value]
      · simp [h,mobius,homogeneousValue,value]
  | coe a =>
    induction b using OnePoint.rec with
    | infty =>
      let h := g.mobius (1-a) a (-1) 1 (by ring_nf; exact one_ne_zero)
      refine ⟨h,?_,?_⟩
      · simp [h,mobius,homogeneousValue,value]
      · simp [h,mobius,homogeneousValue,value]
    | coe b =>
      have hba : b-a≠0 := sub_ne_zero.mpr (fun hh => hab (congrArg OnePoint.some hh.symm))
      let h := g.mobius (b-a) a 0 1 (by simpa using hba)
      refine ⟨h,?_,?_⟩ <;> simp [h,mobius,homogeneousValue,value]

end SplitTangent.RationalCurve

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.ZariskiPairOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zariski Pair Open. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators
universe u
namespace SplitTangent

lemma bihomogeneous_eval_scale {N a b : ℕ} (p : PairPolynomial N)
    (hp : ∀ m∈p.support, (∑i : Fin (N+1),m (0,i))=a ∧ (∑i : Fin (N+1),m (1,i))=b)
    (v : Fin 2 × Fin (N+1) → ℂ) (s t : ℂ) :
    MvPolynomial.eval (fun k => (if k.1=0 then s else t)*v k) p =
      (s^a*t^b)*MvPolynomial.eval v p := by
  classical
  rw [MvPolynomial.eval_eq',MvPolynomial.eval_eq']
  change (∑m∈p.support, p.coeff m * ∏k, ((if k.1=0 then s else t)*v k)^(m k)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow,Finset.prod_mul_distrib]
  have he : (∏k : Fin 2 × Fin (N+1), (if k.1=0 then s else t)^(m k)) = s^a*t^b := by
    rw [Fintype.prod_prod_type,Fin.prod_univ_two]
    norm_num only [↓reduceIte,Fin.one_eq_zero_iff,ite_eq_left trivial,ite_eq_right not_false]
    rw [Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum,(hp m hm).1,(hp m hm).2]
  rw [he]
  ring

variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

lemma isOpen_pairEval_ne_zero (p : PairPolynomial e.N) (hp : Bihomogeneous p) :
    IsOpen {xy | pairEval e p xy≠0} := by
  classical
  obtain ⟨a,b,hp⟩ := hp
  apply isOpen_iff_mem_nhds.mpr
  intro xy hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map xy.1).rep_nonzero
  obtain ⟨j,hj⟩ := Function.ne_iff.mp (e.map xy.2).rep_nonzero
  let q : X.Carrier × X.Carrier → ℂ := fun uv => MvPolynomial.eval
    (fun k : Fin 2 × Fin (e.N+1) => if k.1=0 then projectiveCoordinates i (e.map uv.1) k.2
      else projectiveCoordinates j (e.map uv.2) k.2) p
  have hq : ContinuousAt q xy := by
    apply (MvPolynomial.continuous_eval p).continuousAt.comp
    apply continuousAt_pi.mpr
    intro k
    split_ifs
    · exact (continuous_apply k.2).continuousAt.comp
        (((e.holomorphic i).continuousOn.continuousAt ((e.open_patch i).mem_nhds hi)).comp continuous_fst.continuousAt)
    · exact (continuous_apply k.2).continuousAt.comp
        (((e.holomorphic j).continuousOn.continuousAt ((e.open_patch j).mem_nhds hj)).comp continuous_snd.continuousAt)
  have hscale (uv : X.Carrier × X.Carrier) : q uv =
      ((e.map uv.1).rep i)⁻¹^a * ((e.map uv.2).rep j)⁻¹^b * pairEval e p uv := by
    have hfun : (fun k : Fin 2 × Fin (e.N+1) =>
        if k.1=0 then projectiveCoordinates i (e.map uv.1) k.2
        else projectiveCoordinates j (e.map uv.2) k.2) =
        (fun k : Fin 2 × Fin (e.N+1) =>
          (if k.1=0 then ((e.map uv.1).rep i)⁻¹ else ((e.map uv.2).rep j)⁻¹) *
          (if k.1=0 then (e.map uv.1).rep k.2 else (e.map uv.2).rep k.2)) := by
      funext k
      split_ifs <;> rfl
    change MvPolynomial.eval _ p = _
    rw [hfun]
    exact bihomogeneous_eval_scale p hp _ _ _
  have hqne : q xy≠0 := by
    rw [hscale]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero a (inv_ne_zero hi)) (pow_ne_zero b (inv_ne_zero hj))) hxy
  apply mem_of_superset (hq.eventually_ne hqne)
  intro uv huv
  change pairEval e p uv≠0
  intro he
  exact huv (by rw [hscale,he,mul_zero])

theorem IsZariskiOpenPair.isOpen {U : Set (X.Carrier × X.Carrier)} (hU : IsZariskiOpenPair e U) :
    IsOpen U := by
  obtain ⟨S,hS,rfl⟩ := hU
  have heq : {xy | ∃p∈S,pairEval e p xy≠0} = ⋃p∈S,{xy | pairEval e p xy≠0} := by ext; simp
  rw [heq]
  exact isOpen_iUnion (fun p => isOpen_iUnion (fun hp => isOpen_pairEval_ne_zero e p (hS p hp)))

end SplitTangent

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalFamilyCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Family Cover. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent
open AnalyticZeroCover RationalParameters

lemma RationallyConnected.fixed_endpoints {X : ComplexManifold.{u}}
    {U : Set (X.Carrier × X.Carrier)}
    (hU : ∀xy∈U,∃g : RationalCurve X, ∃a b : OnePoint ℂ, g.value a=xy.1 ∧ g.value b=xy.2)
    {xy : X.Carrier × X.Carrier} (hxy : xy∈U) :
    ∃g : RationalCurve X, g.finite 0=xy.1 ∧ g.finite 1=xy.2 := by
  classical
  obtain ⟨g,a,b,ha,hb⟩ := hU xy hxy
  by_cases hab : a=b
  · have he : xy.1=xy.2 := ha.symm.trans (hab ▸ hb)
    exact ⟨⟨fun _ => xy.1,fun _ => xy.1,contMDiff_const,contMDiff_const,fun _ _ => rfl⟩,rfl,he⟩
  · obtain ⟨h,h0,h1⟩ := g.normalize_endpoints a b hab
    exact ⟨h,h0.trans ha,h1.trans hb⟩

 

theorem RationallyConnected.countable_family_cover {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
    (x₀ : X.Carrier) :
    ∃C : (d : ℕ) → Set (Patch (Coeff e.N d)),
      (∀d,(C d).Countable) ∧
      (∀d, ∀P∈C d,P.image ⊆ regular e.N d ∩ accepted e d) ∧
      ∃U : Set (X.Carrier × X.Carrier), IsOpen U ∧ U.Nonempty ∧
        U ⊆ ⋃ d, ⋃P∈C d, pairEvaluation e x₀ P '' P.domain := by
  classical
  obtain ⟨U,hUz,hUn,hUd,hU⟩ := hRC
  have Hd (d : ℕ) := countable_accepted e (d := d)
  choose C hC hCP hCc using Hd
  refine ⟨C,hC,hCP,U,hUz.isOpen e,hUn,?_⟩
  intro xy hxy
  obtain ⟨g,hg0,hg1⟩ := RationallyConnected.fixed_endpoints hU hxy
  obtain ⟨d,τ,hτ,hτf,hτi⟩ := curve_encoding e g
  obtain ⟨P,hP,z,hz,hzτ⟩ := mem_iUnion₂.mp (hCc d hτ)
  refine mem_iUnion.mpr ⟨d,mem_iUnion₂.mpr ⟨P,hP,z,hz,?_⟩⟩
  apply Prod.ext
  · change e.coneLift x₀ (ev false (P.map z) 0)=xy.1
    rw [hzτ, e.coneLift_eq x₀ (regular_nonzero hτ.1 false 0) (hτf 0),hg0]
  · change e.coneLift x₀ (ev false (P.map z) 1)=xy.2
    rw [hzτ, e.coneLift_eq x₀ (regular_nonzero hτ.1 false 1) (hτf 1),hg1]

end SplitTangent

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Variation. -/

noncomputable section
open Set Filter Topology IsManifold
open scoped ContDiff Manifold
universe u
namespace SplitTangent
open AnalyticZeroCover RationalParameters

 

theorem RationallyConnected.exists_submersive_familyAlternative_oai {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
    (hdim : 0<X.dim) :
    ∃T : ComplexManifold.{u}, Nonempty T.Carrier ∧
      ∃G : RationalFamily X T, ∀τ, Function.Surjective
        (mfderiv (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X))
          (G.twoPointEvaluation 0 1) τ) := by
  classical
  let : ChartedSpace (Model X × Model X) (X.Carrier × X.Carrier) :=
    prodChartedSpace (Model X) X.Carrier (Model X) X.Carrier
  let : IsManifold 𝓘(ℂ,Model X × Model X) ω (X.Carrier × X.Carrier) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod X.Carrier X.Carrier
  obtain ⟨xy,hxy⟩ := hRC.choose_spec.2.1
  let x₀ := xy.1
  obtain ⟨C,hC,hCP,V,hV,hVn,hcov⟩ := hRC.countable_family_cover e x₀
  let : ∀d, Countable (C d) := fun d => (hC d).to_subtype
  let A := Σd, C d
  let d (a : A) := a.2.val.dim
  let U (a : A) : Set (Space (d a)) := a.2.val.domain
  let f (a : A) := pairEvaluation e x₀ a.2.val
  have hU (a : A) : IsOpen (U a) := a.2.val.isOpen_domain
  have hf (a : A) (x) (hx : x∈U a) :
      ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) ω (f a) x := by
    rw [modelWithCornersSelf_prod]
    exact pairEvaluation_holomorphicAt e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hx
  have hcover : V ⊆ ⋃a,f a '' U a := by
    intro v hv
    obtain ⟨n,hn⟩ := mem_iUnion.mp (hcov hv)
    obtain ⟨P,hP,x,hx,hfx⟩ := mem_iUnion₂.mp hn
    exact mem_iUnion.mpr ⟨⟨n,⟨P,hP⟩⟩,x,hx,hfx⟩
  have hdim' : 0<Module.finrank ℂ (Model X × Model X) := by
    simp only [Module.finrank_prod,Model,Module.finrank_fin_fun]
    omega
  obtain ⟨y,a,x,hx,hfx,hs⟩ := exists_chart_submersion_of_cover d U f hU hf
    hV hVn hcover hdim'
  let c := chartAt (Model X × Model X) y
  have hc : c ∈ maximalAtlas 𝓘(ℂ,Model X × Model X) ω _ :=
    IsManifold.chart_mem_maximalAtlas y
  have hcoord : AnalyticAt ℂ (c ∘ f a) x :=
    ((contMDiffAt_of_mem_maximalAtlas hc hfx).comp x (hf a x hx)).contDiffAt.analyticAt
  have hn : ∀ᶠz in 𝓝 x, z∈U a ∧ f a z∈c.source ∧
      Function.Surjective (fderiv ℂ (c ∘ f a) z) :=
    Filter.Eventually.and ((hU a).mem_nhds hx) (Filter.Eventually.and
      ((hf a x hx).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hfx))
      (eventually_surjective_fderiv hcoord hs))
  obtain ⟨W,hWsub,hW,hxW⟩ := mem_nhds_iff.mp hn
  have hWn : W.Nonempty := ⟨x,hxW⟩
  have hWP : W⊆U a := fun z hz => (hWsub hz).1
  let T := OpenManifold.manifold.{u} W hW hWn
  let G := family e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hW hWn hWP
  refine ⟨T,OpenManifold.nonempty W hWn,G,?_⟩
  intro τ
  let z := OpenManifold.val W τ
  have hz : z∈W := τ.down.property
  have hzf : ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) ω (f a) z :=
    hf a z (hWP hz)
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) (f a) z) :=
    surjective_mfderiv_of_chart hzf y (hWsub hz).2.1 (hWsub hz).2.2
  have hv := (OpenManifold.val_mfderiv_bijective W hW hWn τ).2
  have hchain := mfderiv_comp τ (hzf.mdifferentiableAt (by decide))
    ((OpenManifold.val_holomorphic W hW hWn τ).mdifferentiableAt (by decide))
  rw [← modelWithCornersSelf_prod]
  change Function.Surjective (mfderiv (ModelWithCorners (OpenManifold.manifold.{u} W hW hWn))
    𝓘(ℂ,Model X × Model X)
    ((f a) ∘ (fun τ : (OpenManifold.manifold.{u} W hW hWn).Carrier => OpenManifold.val W τ)) τ)
  rw [hchain]
  exact hsurj.comp hv



end SplitTangent

end

end OAI
end

theorem solution.{u} : type_of% @OAI.SplitTangent.RationallyConnected.exists_submersive_familyAlternative_oai.{u} := @OAI.SplitTangent.RationallyConnected.exists_submersive_familyAlternative_oai.{u}
