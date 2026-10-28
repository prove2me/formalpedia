-- Prove2me | solution 1 for OAI.ThreeTorus.StageState.exists_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:06:27.02568+00:00
-- url     : https://prove2.me/submissions/902f66a9-5b89-49d6-a3cc-75bdc9ebfa1e

import Mathlib
import Definitions.Def_ThreeTorus
import Definitions.Def_OAIQ13Tt000
import Theorems.Thm_OAI_ThreeTorus_exists_colored_separation_small
import Theorems.Thm_OAI_ThreeTorus_exists_predicted_whitening
import Theorems.Thm_OAI_ThreeTorus_exists_two_slow_insertions

section
-- module Solutions.OAIQ13_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Cutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth cylinder cutoffs, circle periodization, and regularity of covering lifts. -/

section

/-! Smooth compact supported cutoffs on the actual real-frequency/slow-circle
cylinder, used for the disjoint stationary images in the passage lemma. -/
noncomputable section
open Set Function Filter Topology
open scoped Topology Manifold
namespace ThreeTorus

/-- A compactly supported Euclidean cutoff, equal to one on a neighborhood
of the prescribed compact set, not merely on the set itself. -/
lemma compact_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      ∀ x ∈ K, f =ᶠ[𝓝 x] 1 := by
  obtain ⟨O,hO,hKO,hOc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨V,hV,hKV,hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hO).mem_nhdsSet.mpr (subset_inter hKU hKO))
  have hcV : IsCompact (closure V) := hOc.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hVU hx).2)
  obtain ⟨W,hW,hKW,hWV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  obtain ⟨f,hf,hfr,hfs,hf1⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := 𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hV isClosed_closure hWV
  refine ⟨f,hf.contDiff,?_,?_,?_,?_⟩
  · simpa only [HasCompactSupport, tsupport, hfs] using hcV
  · rw [tsupport, hfs]
    intro x hx
    exact (hVU hx).1
  · intro x
    exact hfr (mem_range_self x)
  · intro x hx
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    exact (hf1 y).mp (subset_closure hy)

lemma cylinderPeriodize_local_support {f : ℝ × ℝ → ℝ}
    (hc : HasCompactSupport f) (p : ℝ × ℝ) :
    ∃ S : Finset ℤ, ∀ᶠ q in 𝓝 p, support (fun k : ℤ => f (q.1,q.2+k)) ⊆ (S : Set ℤ) := by
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|p.2|+1)
  refine ⟨Finset.Icc (-(N:ℤ)) N,?_⟩
  filter_upwards [continuous_snd.tendsto p (Metric.ball_mem_nhds p.2 (by norm_num : (0:ℝ)<1))] with q hq
  intro k hk
  have hq' : |q.2| < |p.2|+1 := by
    have hh := abs_add_le (q.2-p.2) p.2
    have hi : |q.2-p.2| < 1 := hq
    simpa only [sub_add_cancel] using hh.trans_lt (by linarith : |q.2-p.2|+|p.2| < |p.2|+1)
  have hk' : |q.2+(k:ℝ)| ≤ R :=
    (norm_snd_le (q.1,q.2+(k:ℝ))).trans (hR _ (subset_tsupport f hk))
  have hz : |(k:ℝ)| < (N:ℝ) := calc
    |(k:ℝ)| = |(q.2+k)-q.2| := by congr 1; ring
    _ ≤ |q.2+k|+|q.2| := abs_sub _ _
    _ < (N:ℝ) := by linarith
  rw [Finset.mem_coe,Finset.mem_Icc]
  exact_mod_cast (abs_le.mp hz.le)

lemma contDiff_cylinderPeriodize {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cylinderPeriodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨S,hS⟩ := cylinderPeriodize_local_support hc p
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => ∑ k ∈ S, f (q.1,q.2+k)) :=
    ContDiff.sum (fun _ _ => hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)))
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hS] with q hq
  exact finsum_eq_sum_of_support_subset _ hq

lemma cylinderCutoff_smooth {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    CylinderSmooth (cylinderCutoff f) :=
  Real.smoothTransition.contDiff.comp (contDiff_cylinderPeriodize hf hc)

lemma cylinderCutoff_mem_Icc (f : ℝ × ℝ → ℝ) (p : ℝ × UnitAddCircle) :
    0 ≤ cylinderCutoff f p ∧ cylinderCutoff f p ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma cylinderPeriodize_finite {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f) (p : ℝ × ℝ) :
    HasFiniteSupport (fun k : ℤ => f (p.1,p.2+k)) := by
  obtain ⟨S,hS⟩ := cylinderPeriodize_local_support hc p
  exact S.finite_toSet.subset (hS.self_of_nhds)

lemma cylinderCutoff_one_of_eq_one {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f)
    (hf : ∀ p, 0 ≤ f p) {p : ℝ × ℝ} (hp : f p = 1) :
    cylinderCutoff f (cylinderProjection p) = 1 := by
  apply Real.smoothTransition.one_of_one_le
  change 1 ≤ ∑ᶠ k : ℤ, f (p.1,p.2+k)
  have hfin : (support (fun k : ℤ => f (p.1,p.2+k))).Finite :=
    cylinderPeriodize_finite hc p
  rw [finsum_eq_sum _ hfin]
  have hz : (0:ℤ) ∈ hfin.toFinset := by simp [mem_support, hp]
  simpa [hp] using Finset.single_le_sum (fun (k : ℤ) _ => hf (p.1,p.2+k)) hz

lemma cylinderCutoff_support_subset {f : ℝ × ℝ → ℝ} :
    support (cylinderCutoff f) ⊆ cylinderProjection '' support f := by
  intro p hp
  obtain ⟨q,rfl⟩ := cylinderProjection_surjective p
  have hh : cylinderPeriodize f q ≠ 0 := by
    intro hz
    exact hp (by simp [cylinderProjection,cylinderCutoff_coe,hz])
  obtain ⟨k,hk⟩ : ∃ k : ℤ, f (q.1,q.2+k) ≠ 0 := by
    by_contra h
    push Not at h
    exact hh (by simp [cylinderPeriodize,h])
  refine ⟨(q.1,q.2+k),hk,?_⟩
  dsimp [cylinderProjection]
  congr 1
  simp

lemma cylinderCutoff_tsupport_subset {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f) :
    tsupport (cylinderCutoff f) ⊆ cylinderProjection '' tsupport f := by
  apply closure_minimal
  · exact cylinderCutoff_support_subset.trans (image_mono subset_closure)
  · exact (hc.image continuous_cylinderProjection).isClosed

lemma cylinderCutoff_compactSupport {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (cylinderCutoff f) :=
  (hc.image continuous_cylinderProjection).of_isClosed_subset isClosed_closure
    (cylinderCutoff_tsupport_subset hc)

lemma cylinderCutoff_one_near {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f)
    (hf : ∀ p, 0 ≤ f p) {p : ℝ × ℝ} (hp : f =ᶠ[𝓝 p] 1) :
    cylinderCutoff f =ᶠ[𝓝 (cylinderProjection p)] 1 := by
  obtain ⟨V,hV,hVo,hpV⟩ := mem_nhds_iff.mp hp
  apply Filter.mem_of_superset
    ((isOpenMap_cylinderProjection _ hVo).mem_nhds (mem_image_of_mem _ hpV))
  rintro _ ⟨q,hq,rfl⟩
  exact cylinderCutoff_one_of_eq_one hc hf (hV hq)

lemma compact_cylinder_lift {K : Set (ℝ × UnitAddCircle)} (hK : IsCompact K) :
    ∃ L : Set (ℝ × ℝ), IsCompact L ∧ cylinderProjection '' L = K := by
  obtain ⟨R,hR⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  let B : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc 0 1
  let L := B ∩ cylinderProjection ⁻¹' K
  refine ⟨L,(isCompact_Icc.prod isCompact_Icc).inter_right
    (hK.isClosed.preimage continuous_cylinderProjection),?_⟩
  apply Subset.antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact hp.2
  · intro p hp
    obtain ⟨a,ha,hae⟩ := AddCircle.eq_coe_Ico p.2
    have hs : p.1 ∈ Icc (-R) R := abs_le.mp (hR _ (mem_image_of_mem _ hp))
    refine ⟨(p.1,a),⟨⟨hs,⟨ha.1,ha.2.le⟩⟩,?_⟩,?_⟩
    · simpa [cylinderProjection,hae] using hp
    · exact Prod.ext rfl hae

/-- The exact smooth cutoff needed for a compact stationary image in the cylinder.
The support may be placed in an arbitrary prescribed open neighborhood. -/
theorem compact_cylinder_cutoff {K U : Set (ℝ × UnitAddCircle)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℝ × UnitAddCircle → ℝ, CylinderSmooth χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
      ∀ p ∈ K, χ =ᶠ[𝓝 p] 1 := by
  obtain ⟨L,hL,hLK⟩ := compact_cylinder_lift hK
  obtain ⟨f,hf,hfc,hfs,hfr,hf1⟩ := compact_smooth_cutoff hL
    (hU.preimage continuous_cylinderProjection)
    (fun p hp => hKU (hLK ▸ mem_image_of_mem cylinderProjection hp))
  refine ⟨cylinderCutoff f,cylinderCutoff_smooth hf hfc,
    cylinderCutoff_compactSupport hfc,?_,cylinderCutoff_mem_Icc f,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := cylinderCutoff_tsupport_subset hfc hp
    exact hfs hq
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := hLK.symm ▸ hp
    exact cylinderCutoff_one_near hfc (fun q => (hfr q).1) (hf1 q hq)

/-- Finite disjoint compact stationary images admit simultaneous smooth
cutoffs with disjoint compact supports, in any prescribed neighborhoods. -/
theorem finite_disjoint_cylinder_cutoffs {ι : Type*} [Finite ι]
    (K U : ι → Set (ℝ × UnitAddCircle))
    (hK : ∀ i, IsCompact (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (Disjoint on K)) :
    ∃ χ : ι → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U i ∧
        (∀ p, 0 ≤ χ i p ∧ χ i p ≤ 1) ∧ ∀ p ∈ K i, χ i =ᶠ[𝓝 p] 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  have hd : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) :=
    fun i j hij => disjoint_nhdsSet_nhdsSet (hK i).isClosed (hK j).isClosed (hdisj hij)
  obtain ⟨O,hO,hOd⟩ := hd.exists_mem_filter_of_disjoint
  have hv i : K i ⊆ interior (O i) ∩ U i :=
    subset_inter (subset_interior_iff_mem_nhdsSet.mpr (hO i)) (hKU i)
  choose χ hχ using fun i => compact_cylinder_cutoff (hK i)
    (isOpen_interior.inter (hU i)) (hv i)
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_right,
    (hχ i).2.2.2⟩,?_⟩
  intro i j hij
  exact (hOd hij).mono ((hχ i).2.2.1.trans (inter_subset_left.trans interior_subset))
    ((hχ j).2.2.1.trans (inter_subset_left.trans interior_subset))

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Twists
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product torus, exact angular packets, all integer twist iterates, and measure-preserving passage charts. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma packet_twistIter (φ : UnitAddCircle → UnitAddCircle) (n m : ℤ)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) :
    packet m A (twistIter φ n x) = fourier n (m • φ x.2.1) * packet m A x := by
  change A x.2 * fourier m (x.1+n • φ x.2.1) =
    fourier n (m • φ x.2.1)*(A x.2*fourier m x.1)
  simp only [fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul,smul_smul]
  rw [mul_comm n m]
  ring

lemma continuous_packet {m : ℤ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) : Continuous (packet m A) :=
  (hA.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst)

lemma integral_fourier_pair (m k : ℤ) :
    (∫ θ : UnitAddCircle, starRingEnd ℂ (fourier m θ)*fourier k θ
      ∂AddCircle.haarAddCircle) = if m = k then 1 else 0 := by
  have hh := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1:ℝ)))) m k
  rw [ContinuousMap.inner_toLp] at hh
  simpa only [RCLike.inner_apply,mul_comm] using hh

lemma normSq_complex (z : ℂ) : starRingEnd ℂ z*z = (‖z‖^2 : ℝ) := by
  simp only [Complex.conj_mul',Complex.ofReal_pow]

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Jitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cumulative distribution, smooth quantile inverse, and positive smooth neutral jitter laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics

/-! Approximation of a positive smooth law.
The cumulative distribution and its local smooth inverse are constructed from
the positive smooth density, not assumed as an additional hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

lemma contDiff_periodize {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (periodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R + |x| + 1)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hs : ∀ᶠ y in 𝓝 x, support (fun k : ℤ => f (y+k)) ⊆ (s : Set ℤ) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    intro k hk
    have hy' : |y| < |x| + 1 := by
      have := abs_add_le (y-x) x
      have hy'' : |y-x| < 1 := hy
      simpa only [sub_add_cancel] using this.trans_lt (by linarith : |y-x|+|x| < |x|+1)
    have hk' : |y+(k : ℝ)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR (y+k) (subset_tsupport f hk)
    have hz : |(k : ℝ)| < (N : ℝ) := calc
      |(k : ℝ)| = |(y+k)-y| := by congr 1; ring
      _ ≤ |y+k| + |y| := abs_sub _ _
      _ < ↑N := by linarith
    have hh : -(N : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ ↑N := (abs_le.mp hz.le)
    show k ∈ Finset.Icc (-(N : ℤ)) N
    rw [Finset.mem_Icc]
    exact_mod_cast hh
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∑ k ∈ s, f (y+k)) :=
    ContDiff.sum fun k _ => hf.comp (contDiff_id.add contDiff_const)
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  exact finsum_eq_sum_of_support_subset _ hy

lemma periodize_eq_on_unit {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : periodize f x = f x := by
  unfold periodize
  convert finsum_eq_single (fun k : ℤ => f (x+k)) 0 ?_ using 1
  · simp
  · intro k hk
    by_contra hn
    have hh := hs (show x+(k : ℝ) ∈ support f from hn)
    have h1 : (-1 : ℝ) < (k : ℝ) := by linarith [hx.2, hh.1]
    have h2 : (k : ℝ) < (1 : ℝ) := by linarith [hx.1, hh.2]
    have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (1 : ℤ) := by exact_mod_cast h2
    omega

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

open Function

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

lemma support_branchFamily_subset {Ω : Type*} [TopologicalSpace Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ} :
    support (branchFamily I J F) ⊆ (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchFamily,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchFamily,hs,hz])
  · simp only [hp.2]

lemma branchFamily_compact {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchFamily I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × Ω => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchFamily_subset hn)

lemma branchFamily_continuous {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × Ω → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : Continuous F) (hc : HasCompactSupport F) (hs : tsupport F ⊆ I ×ˢ univ) :
    Continuous (branchFamily I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × Ω} (hp : p ∉ M) : branchFamily I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchFamily_subset hn))
  have hD : Continuous (deriv J) := hJ.continuous_deriv (by simp)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)).continuousAt
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hgi' : ContinuousAt (fun p : ℝ × Ω => g p.1) (J x,a) :=
      hgi.comp_of_eq continuousAt_fst rfl
    have hin : ContinuousAt (fun p : ℝ × Ω => (g p.1,p.2)) (J x,a) :=
      hgi'.prodMk continuousAt_snd
    have hDen : ContinuousAt (fun p : ℝ × Ω => |deriv J (g p.1)|) (J x,a) :=
      (hD.continuousAt.comp hgi').abs
    have hquot : ContinuousAt (fun p : ℝ × Ω => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.continuousAt.comp hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × Ω in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchFamily,ite_eq_left hp,g]
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

open scoped NNReal

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma circle_integral_lift (o : ℝ) (q : UnitAddCircle → ℝ) :
    (∫ x, circleDensityLift o q x) = ∫ a, q a ∂AddCircle.haarAddCircle := by
  rw [circleDensityLift,integral_indicator measurableSet_Ioc]
  have h := AddCircle.integral_preimage 1 o q
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using h

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

/-- Lifting a circle density on one period commutes with every measurable
spectral pushforward. This includes the actual jitter, not just polynomial tests. -/
lemma circleDensityLift_pushforward {Y : Type*} [MeasurableSpace Y]
    {q : UnitAddCircle → ℝ} (hq : Integrable q AddCircle.haarAddCircle)
    {T : UnitAddCircle → Y} (hT : Measurable T) (o : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (circleDensityLift o q)).map
      (fun x : ℝ => T (x : UnitAddCircle)) =
    (AddCircle.haarAddCircle.withDensityᵥ q).map T := by
  have hTm : Measurable (fun x : ℝ => T (x : UnitAddCircle)) := hT.comp AddCircle.measurable_mk'
  ext s hs
  rw [VectorMeasure.map_apply _ hTm hs,VectorMeasure.map_apply _ hT hs,
    withDensityᵥ_apply (integrable_circleDensityLift hq o) (hTm hs),
    withDensityᵥ_apply hq (hT hs)]
  rw [← integral_indicator (hTm hs),← integral_indicator (hT hs)]
  rw [← circle_integral_lift o ((T ⁻¹' s).indicator q)]
  congr 1
  funext x
  by_cases hx : x ∈ Ioc o (o+1) <;> by_cases hxs : T (x : UnitAddCircle) ∈ s <;>
    simp [circleDensityLift,hx,hxs]

lemma circleDensityLift_eq {q : UnitAddCircle → ℝ} {q₀ : ℝ → ℝ} {o : ℝ}
    (he : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hs : Function.support q₀ ⊆ Ioc o (o+1)) : circleDensityLift o q = q₀ := by
  funext x
  by_cases hx : x ∈ Ioc o (o+1)
  · simp [circleDensityLift,hx,he x hx]
  · have hzero : q₀ x = 0 := by by_contra hn; exact hx (hs hn)
    simp [circleDensityLift,hx,hzero]

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Exact pushforward of the old squared coefficient on a branch. The only
inverse assumptions are the ordinary left-inverse identities on that branch. -/
lemma branchDensity_pushforward {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I)) (hJm : Measurable J)
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q) (hqs : Function.support q ⊆ I) :
    ((volume : Measure ℝ).withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J g D q) := by
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hq.integrableOn
  ext s hs
  rw [VectorMeasure.map_apply _ hJm hs,withDensityᵥ_apply hq (hJm hs),withDensityᵥ_apply hK hs]
  rw [← integral_indicator (hJm hs),← integral_indicator hs]
  have hleft : (∫ x, (J ⁻¹' s).indicator q x) = ∫ x in I, (J ⁻¹' s).indicator q x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hqx : q x = 0 := by
      by_contra hh
      exact hx (hqs hh)
    by_cases hxs : x ∈ J ⁻¹' s <;> simp [hxs,hqx]
  have hright : (∫ y, s.indicator (branchDensity I J g D q) y) =
      ∫ y in J '' I, s.indicator (branchDensity I J g D q) y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_cases hys : y ∈ s <;> simp [hys,branchDensity,hy]
  rw [hleft,hright,integral_image_eq_integral_abs_deriv_smul hI hJ hinj]
  apply setIntegral_congr_fun hI
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  by_cases hxs : J x ∈ s
  · rw [indicator_of_mem (show x ∈ J ⁻¹' s from hxs),indicator_of_mem hxs,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  · rw [indicator_of_notMem (show x ∉ J ⁻¹' s from hxs),indicator_of_notMem hxs,mul_zero]

lemma density_map_congr_support {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {T₁ T₂ : X → Y} (h₁ : Measurable T₁) (h₂ : Measurable T₂)
    (he : ∀ x, f x ≠ 0 → T₁ x = T₂ x) :
    (μ.withDensityᵥ f).map T₁ = (μ.withDensityᵥ f).map T₂ := by
  classical
  ext s hs
  rw [VectorMeasure.map_apply _ h₁ hs,VectorMeasure.map_apply _ h₂ hs,
    withDensityᵥ_apply hf (h₁ hs),withDensityᵥ_apply hf (h₂ hs),
    ← integral_indicator (h₁ hs),← integral_indicator (h₂ hs)]
  congr 1
  funext x
  change (if T₁ x ∈ s then f x else 0) = (if T₂ x ∈ s then f x else 0)
  by_cases hx : f x = 0
  · simp [hx]
  · rw [he x hx]

/-- The branch-Jacobian formula on the actual circle. The global periodic
jitter need not be injective; only the good arc bearing the weight is used. -/
lemma circle_branch_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J₀ g D q₀) := by
  have hlift := circleDensityLift_eq hq₀ hq₀s
  have hi : Integrable q₀ := by rw [← hlift]; exact integrable_circleDensityLift hq o
  rw [← circleDensityLift_pushforward hq hj o,hlift]
  rw [density_map_congr_support (T₁ := fun x : ℝ => J (x : UnitAddCircle)) hi (hj.comp AddCircle.measurable_mk') hj₀
    (fun x hx => hJe x (hqs hx))]
  exact branchDensity_pushforward hI himage hj₀ hJ hinj hg hD hi hqs

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

lemma stationaryWeight_signed_compact_continuous {J : ℝ → ℝ}
    {A : UnitAddCircle → ℝ → ℂ} {l u R : ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (hR : 0 < R) (hi : InjOn J (Icc (l-R) (u+R)))
    (hd : ∀ x ∈ Ioo (l-R) (u+R), deriv J x ≠ 0) :
    Continuous (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) ∧
    HasCompactSupport (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) := by
  let F : ℝ × UnitAddCircle → ℝ := fun p => ‖A p.2 p.1‖^2
  have hF : Continuous F := (hA.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hFs : support F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) := by
    intro p hp
    refine ⟨hs p.2 ?_,mem_univ _⟩
    intro hz
    exact hp (by simp [F,show A p.2 p.1 = 0 from hz])
  have hFt : tsupport F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) :=
    closure_minimal hFs (isClosed_Icc.prod isClosed_univ)
  have hc : HasCompactSupport F :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFt
  have hsub : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [stationaryWeight_family_of_branch Ioo_subset_Icc_self hi (fun a => (hs a).trans hsub)]
  exact ⟨branchFamily_continuous hJ isOpen_Ioo (hi.mono Ioo_subset_Icc_self) hd hF hc
    (fun p hp => ⟨hsub (hFt hp).1,mem_univ _⟩),branchFamily_compact hJ.continuous hc⟩

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma periodizedReal_add_int (q : ℝ → ℝ) (x : ℝ) (j : ℤ) :
    periodizedReal q (x+j) = periodizedReal q x := by
  have h := (Equiv.addLeft j).tsum_eq (fun k : ℤ => q (x+k))
  change (∑' k : ℤ, q (x+(j:ℝ)+(k:ℝ))) = ∑' k : ℤ, q (x+(k:ℝ))
  rw [← h]
  apply tsum_congr
  intro k
  congr 1
  change x+(j:ℝ)+(k:ℝ) = x+((j+k:ℤ):ℝ)
  simp only [Int.cast_add,add_assoc]

/-- The displayed lattice formula holds for every real representative. -/
lemma foldCircleDensity_coe_all (q : ℝ → ℝ) (x : ℝ) :
    foldCircleDensity q (x:UnitAddCircle) = ∑' k : ℤ, q (x+k) := by
  let y : ℝ := (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).1
  have hy : y ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).2
  have hxy : (y:UnitAddCircle) = (x:UnitAddCircle) :=
    (AddCircle.equivIoc 1 0).symm_apply_apply (x:UnitAddCircle)
  have hz : ((y-x:ℝ):UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 hz
  have he : y = x+(k:ℝ) := by simpa only [zsmul_eq_mul,mul_one] using eq_add_of_sub_eq' hk.symm
  rw [← hxy,foldCircleDensity_coe hy,he,periodizedReal_add_int]
  rfl

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma vectorMeasure_map_comp {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [AddCommMonoid E] [TopologicalSpace E]
    (ν : VectorMeasure X E) {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g) :
    (ν.map f).map g = ν.map (g ∘ f) := by
  ext s hs
  rw [VectorMeasure.map_apply _ hg hs,VectorMeasure.map_apply _ hf (hg hs),
    VectorMeasure.map_apply _ (hg.comp hf) hs]
  rfl

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_RetainedPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal retained passage vectors, spectral identities, regularity, old marginals, and quantitative cutoff losses. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology

noncomputable section
open Set Function Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

lemma smooth_fourier_lift (m : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (fourier m (x : UnitAddCircle) : ℂ)) := by
  simp only [fourier_coe_apply,Complex.ofReal_one,div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

end ThreeTorus

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology ENNReal
namespace ThreeTorus

/-- A nonnegative integrable density identity proved with signed vector
measures is the identical ordinary measure identity. -/
lemma positive_density_map_of_vectorMeasure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {q : X → ℝ} {p : Y → ℝ}
    (hf : Measurable f) (hq : Integrable q μ) (hp : Integrable p ν)
    (hq0 : ∀ x, 0 ≤ q x) (hp0 : ∀ y, 0 ≤ p y)
    (he : (μ.withDensityᵥ q).map f = ν.withDensityᵥ p) :
    (μ.withDensity (fun x => ENNReal.ofReal (q x))).map f =
      ν.withDensity (fun y => ENNReal.ofReal (p y)) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal hq.integrableOn (Eventually.of_forall hq0),
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn (Eventually.of_forall hp0)]
  congr 1
  have h := congrArg (fun v : VectorMeasure Y ℝ => v s) he
  simpa only [VectorMeasure.map_apply _ hf hs,withDensityᵥ_apply hq (hf hs),
    withDensityᵥ_apply hp hs] using h

lemma branchDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) (y : ℝ) : 0 ≤ branchDensity I J g D q y := by
  classical
  simp only [branchDensity,Set.indicator_apply]
  split_ifs
  · exact div_nonneg (hq _) (abs_nonneg _)
  · rfl

lemma foldCircleDensity_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (z : UnitAddCircle) :
    0 ≤ foldCircleDensity q z := by
  unfold foldCircleDensity periodizedReal
  exact tsum_nonneg (fun k => hq _)

end ThreeTorus
end
end
end
end
end
end

section

/-! Smoothness at the edge of the good arc is essential: the actual retained
spectral densities must be valid smooth inputs to the next stage. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma support_branchDensity_subset {J q : ℝ → ℝ} {I : Set ℝ} :
    support (branchDensity I J (invFunOn J I) (deriv J) q) ⊆ J '' tsupport q := by
  intro y hy
  have hyI : y ∈ J '' I := by
    by_contra hh
    exact hy (by simp [branchDensity,hh])
  have hx := invFunOn_pos hyI
  refine ⟨invFunOn J I y,subset_tsupport q ?_,hx.2⟩
  intro hq
  exact hy (by simp [branchDensity,hyI,hq])

lemma branchDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hq : HasCompactSupport q) :
    HasCompactSupport (branchDensity I J (invFunOn J I) (deriv J) q) := by
  apply HasCompactSupport.intro (hq.image hJ)
  intro y hy
  exact notMem_support.mp (fun hh => hy (support_branchDensity_subset hh))

lemma branchDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let g := invFunOn J I
  have hM : IsCompact (J '' tsupport q) := hc.image hJ.continuous
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ J '' tsupport q
  · obtain ⟨x,hx,rfl⟩ := hy
    have hxI := hs hx
    have hyI : J x ∈ J '' I := mem_image_of_mem J hxI
    have hg := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := hinj (invFunOn_pos hyI).1 hxI (invFunOn_pos hyI).2
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => |deriv J (g y)|) (J x) :=
      (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x)
        (hD.contDiffAt.comp (J x) hg)
    have hquot := (hq.contDiffAt.comp (J x) hg).div hden
      (by simpa only [hge] using abs_ne_zero.mpr (hd x hxI))
    apply hquot.congr_of_eventuallyEq
    filter_upwards [(isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hyI] with z hz
    simp only [branchDensity,indicator_of_mem hz,g]
    rfl
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hy] with z hz
    exact notMem_support.mp (fun hh => hz (support_branchDensity_subset hh))

lemma periodizedReal_eq_periodize {q : ℝ → ℝ} (hc : HasCompactSupport q) :
    periodizedReal q = periodize q := by
  funext x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|x|+1)
  have hs : support (fun k : ℤ => q (x+k)) ⊆ (Finset.Icc (-(N:ℤ)) N : Set ℤ) := by
    intro k hk
    have hr := hR (x+k) (subset_tsupport q hk)
    have hh : |(k:ℝ)| < N := by
      have ha := abs_sub_le (x+(k:ℝ)) 0 x
      simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left,Real.norm_eq_abs] at hr ha
      linarith
    have hab := abs_lt.mp hh
    simp only [Finset.mem_coe,Finset.mem_Icc]
    constructor
    · exact_mod_cast (by linarith : -(N:ℝ) ≤ (k:ℝ))
    · exact_mod_cast (by linarith : (k:ℝ) ≤ (N:ℝ))
  exact tsum_eq_finsum ((Finset.finite_toSet _).subset hs)

lemma foldCircleDensity_smooth_lift {q : ℝ → ℝ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) := by
  have he : (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) = periodize q := by
    funext x
    rw [foldCircleDensity_coe_all]
    exact congrFun (periodizedReal_eq_periodize hc) x
  rw [he]
  exact contDiff_periodize hq hc

end ThreeTorus
end
end

section

/-! Identification of the reference stationary marginal with the actual old
packet spectrum. In particular integer carrier speeds do not change it. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma positive_circle_branch_fold
    {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x:UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (J a:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀) z)) := by
  let w := branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hIm := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  have hwi : Integrable w := integrable_branchDensity hIo.measurableSet hIm hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi.integrableOn
  have hwm : Measurable w := measurable_branchDensity_smooth hJ hIo hinj hd hqm
  have hmap := circle_branch_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet hIm hD hinj (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
  apply positive_density_map_of_vectorMeasure (AddCircle.measurable_mk'.comp hj) hq
    (integrable_foldCircleDensity hwm hwi) hq0
    (foldCircleDensity_nonneg (branchDensity_nonneg hq00))
  rw [← foldCircleDensity_pushforward hwm hwi,← hmap]
  exact (vectorMeasure_map_comp _ hj AddCircle.measurable_mk').symm

lemma stationaryWeight_change_branch {A : ℝ → ℂ} {J : ℝ → ℝ} {C I : Set ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : support A ⊆ I) :
    stationaryWeight C J A = stationaryWeight I J A := by
  have h := stationaryWeight_family_of_branch (Ω := Unit) hIC hi (fun _ => hs)
  funext s
  have hh := congrFun h (s,())
  exact hh

end ThreeTorus
end
end

section

/-! Actual old densities for amplitudes depending on both slow coordinates. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

lemma map_fst_withDensity_marginal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {q : X × Y → ℝ≥0∞} (hq : Measurable q) :
    ((μ.prod ν).withDensity q).map Prod.fst =
      μ.withDensity (fun x => ∫⁻ y, q (x,y) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs,← lintegral_indicator (measurable_fst hs),
    ← lintegral_indicator hs,lintegral_prod _ (hq.indicator (measurable_fst hs)).aemeasurable]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
    apply lintegral_congr
    intro y
    exact Set.indicator_of_mem (show (x,y) ∈ Prod.fst ⁻¹' s from hx) q
  · simp only [Set.indicator_of_notMem hx]
    have hz (y : Y) : ((Prod.fst ⁻¹' s).indicator q) (x,y) = 0 :=
      Set.indicator_of_notMem (show (x,y) ∉ Prod.fst ⁻¹' s from hx) q
    simp only [hz,lintegral_zero]

lemma continuous_slowMarginal {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) :
    Continuous (fun u => ∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle) := by
  have hc : Continuous (uncurry (fun (u a : UnitAddCircle) => ‖A (u,a)‖^2)) := hA.norm.pow 2
  simpa only [setIntegral_univ] using
    continuous_parametric_integral_of_continuous (X := UnitAddCircle) (Y := UnitAddCircle)
      (μ := AddCircle.haarAddCircle) hc isCompact_univ

lemma packetSpectralMeasure_marginal {φ : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {m : ℤ}
    (hφ : Measurable φ) (hA : Continuous A) :
    packetSpectralMeasure φ m A =
      (AddCircle.haarAddCircle.withDensity (fun u => ENNReal.ofReal
        (∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle))).map (fun u => m • φ u) := by
  unfold packetSpectralMeasure slowVolume
  change Measure.map ((fun u => m • φ u) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (show Measurable (fun u => m • φ u) from hφ.const_smul m) measurable_fst,
    map_fst_withDensity_marginal (q := fun p => ENNReal.ofReal (‖A p‖^2))
      (by simpa only [Pi.pow_apply] using (hA.norm.pow 2).measurable.ennreal_ofReal)]
  congr 2
  funext u
  exact (ofReal_integral_eq_lintegral_ofReal
    (((hA.comp (continuous_const.prodMk continuous_id)).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (ae_of_all _ (fun a => sq_nonneg _))).symm

lemma branchDensity_integral {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (I : Set ℝ) (J g D : ℝ → ℝ) (q : ℝ × Ω → ℝ) (s : ℝ) :
    branchDensity I J g D (fun u => ∫ a, q (u,a) ∂ν) s =
      ∫ a, branchDensity I J g D (fun u => q (u,a)) s ∂ν := by
  classical
  unfold branchDensity
  by_cases hs : s ∈ J '' I
  · simp only [Set.indicator_of_mem hs,integral_div]
  · simp only [Set.indicator_of_notMem hs,integral_zero]

/-- An arbitrary smooth/continuous old packet has the stationary marginal as
its temporal density. Spare-coordinate independence is not required. -/
theorem oldPacket_spectralDensity
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m c : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀.uncurry)
    (hAe : ∀ a x, x ∈ Ioc o (o+1) → A ((x:UnitAddCircle),a) = A₀ a x)
    (has : ∀ a, support (A₀ a) ⊆ Ioc o (o+1)) (hAs : ∀ a, support (A₀ a) ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    packetSpectralMeasure (fun a => ((v a-c:ℝ):UnitAddCircle)) m A =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x)
          (A₀ a) s ∂AddCircle.haarAddCircle) z)) := by
  let q : UnitAddCircle → ℝ := fun u => ∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle
  let q₀ : ℝ → ℝ := fun x => ∫ a, ‖A₀ a x‖^2 ∂AddCircle.haarAddCircle
  have hqc : Continuous q := continuous_slowMarginal hA
  have hq₀c : Continuous q₀ := by
    have hc : Continuous (uncurry (fun (x : ℝ) (a : UnitAddCircle) => ‖A₀ a x‖^2)) :=
      (hA₀.comp continuous_swap).norm.pow 2
    simpa only [q₀,setIntegral_univ] using
      continuous_parametric_integral_of_continuous (X := ℝ) (Y := UnitAddCircle)
        (μ := AddCircle.haarAddCircle) hc isCompact_univ
  have hs (K : Set ℝ) (hK : ∀ a, support (A₀ a) ⊆ K) : support q₀ ⊆ K := by
    intro x hx
    by_contra hnot
    apply hx
    have hz (a : UnitAddCircle) : A₀ a x = 0 := by
      by_contra hn
      exact hnot (hK a hn)
    simp only [q₀,hz,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero]
  have hmap := packetSpectralMeasure_marginal (m := m) (A := A)
    (φ := fun a => (((v a-(c:ℝ)) : ℝ):UnitAddCircle))
    (AddCircle.measurable_mk'.comp (hv.sub measurable_const)) hA
  rw [hmap]
  have hmode (a : UnitAddCircle) : m • ((v a-c:ℝ):UnitAddCircle) =
      (((m:ℝ)*v a:ℝ):UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul]
    simp only [zsmul_eq_mul]
    rw [mul_sub]
    have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
      rw [← Int.cast_mul]
      exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
    rw [AddCircle.coe_sub,he,sub_zero]
  simp_rw [hmode]
  have hb : branchDensity I (fun x => (m:ℝ)*V x)
      (invFunOn (fun x => (m:ℝ)*V x) I) (deriv (fun x => (m:ℝ)*V x)) q₀ =
      fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x) (A₀ a) s
        ∂AddCircle.haarAddCircle := by
    funext s
    rw [show q₀ = fun x => ∫ a, ‖A₀ a x‖^2 ∂AddCircle.haarAddCircle from rfl,
      branchDensity_integral (q := fun p : ℝ × UnitAddCircle => ‖A₀ p.2 p.1‖^2)]
    apply integral_congr_ae
    filter_upwards [] with a
    exact congrFun (stationaryWeight_change_branch hIC hinj (hAs a)).symm s
  rw [← hb]
  exact positive_circle_branch_fold
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hq₀c.measurable (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun x hx => integral_congr_ae (ae_of_all _ (fun a => by dsimp only; rw [hAe a x hx])))
    (hs _ has) (hs _ hAs) (hv.const_mul (m:ℝ)) (contDiff_const.mul hV)
    (fun x hx => by rw [hVe x hx]) hIo (hinj.mono hIC) hd

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounded common primitives, neutral and quantile families, exact indices, signal passages, and support tracking. -/

section

/-! Closure of the literal output coefficient class under a passage.
The next passage uses these very coefficients, rather than new placeholders. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators

namespace ThreeTorus
open Set

/-- The buffered real integration interval can always be fixed before the
next passage integer, even when all the coefficients are zero. -/
lemma compact_inside_buffered_interval {K : Set ℝ} {a b : ℝ}
    (hK : IsCompact K) (hab : a < b) (hKI : K ⊆ Ioo a b) :
    ∃ l u R : ℝ, a < l ∧ l < u ∧ u < b ∧ 0 < R ∧
      K ⊆ Ioc l u ∧ Icc (l-2*R) (u+2*R) ⊆ Ioo a b := by
  let K' := insert ((a+b)/2) K
  have hc : IsCompact K' := hK.insert _
  have hsub : K' ⊆ Ioo a b := by
    intro x hx
    rcases mem_insert_iff.mp hx with rfl | hx
    · constructor <;> linarith
    · exact hKI hx
  obtain ⟨x,hx,hmin⟩ := hc.exists_isMinOn (insert_nonempty _ _) continuous_id.continuousOn
  obtain ⟨y,hy,hmax⟩ := hc.exists_isMaxOn (insert_nonempty _ _) continuous_id.continuousOn
  have hx' := hsub hx
  have hy' := hsub hy
  have hxy : x ≤ y := hmin hy
  let l := (a+x)/2
  let u := (y+b)/2
  have hal : a < l := by dsimp [l]; linarith [hx'.1]
  have hlu : l < u := by dsimp [l,u]; linarith [hx'.1,hy'.2]
  have hub : u < b := by dsimp [u]; linarith [hy'.2]
  let R := min (l-a) (b-u)/4
  have hR : 0 < R := div_pos (lt_min (sub_pos.mpr hal) (sub_pos.mpr hub)) (by norm_num)
  have hR₁ : 4*R ≤ l-a := by dsimp [R]; linarith [min_le_left (l-a) (b-u)]
  have hR₂ : 4*R ≤ b-u := by dsimp [R]; linarith [min_le_right (l-a) (b-u)]
  refine ⟨l,u,R,hal,hlu,hub,hR,?_,?_⟩
  · intro z hz
    have hz' : z ∈ K' := mem_insert_of_mem _ hz
    have hminz := hmin hz'
    have hmaxz := hmax hz'
    constructor <;> dsimp [l,u] at * <;> linarith
  · intro z hz
    constructor <;> linarith [hz.1,hz.2]

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed finite packet states, canonical densities, residue reindexing, anchors, reflection, clipping, and state tracking. -/

section

/-! Concrete finite-packet input data and the support bookkeeping used by
iteration. Field regularity is inherited from literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma core_subset (i : ι) : F.core i ⊆ Icc F.l F.u :=
  closure_minimal ((F.support_lift i 0).trans Ioc_subset_Icc_self) isClosed_Icc

lemma core_compact (i : ι) : IsCompact (F.core i) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (F.core_subset i)

end PassagePackets
end ThreeTorus
end
end

section

/-! Canonical smooth density of a literal passage-state packet.  These are
computed from the actual amplitude and speed; no spectral property is a field. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma smooth_zero_lift (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.A₀ i 0) := by
  simpa only [Function.comp_def, AddCircle.coe_zero] using
    (F.smooth_lift i).comp (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (x,(0:ℝ))) from contDiff_id.prodMk contDiff_const)

lemma weight_regular (i : ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.weight i) ∧ HasCompactSupport (F.weight i) := by
  let q := fun x => ‖F.A₀ i 0 x‖^2
  have hqs : tsupport q ⊆ F.core i := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [q,hz])
  have hqc : HasCompactSupport q := (F.core_compact i).of_isClosed_subset isClosed_closure hqs
  have hs : tsupport q ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.core_subset i (hqs hx)
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have has : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have he := stationaryWeight_change_branch Ioo_subset_Icc_self hb.1 has
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (stationaryWeight _ _ _) ∧ HasCompactSupport (stationaryWeight _ _ _)
  rw [he]
  exact ⟨branchDensity_smooth (contDiff_const.mul F.smooth_speed) isOpen_Ioo
    (hb.1.mono Ioo_subset_Icc_self) hb.2 ((F.smooth_zero_lift i).norm_sq (𝕜 := ℂ)) hqc hs,
    branchDensity_compact (continuous_const.mul F.smooth_speed.continuous) hqc⟩

lemma density_smooth (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ => F.density i (x:UnitAddCircle)) :=
  foldCircleDensity_smooth_lift (F.weight_regular i).1 (F.weight_regular i).2

lemma density_continuous (i : ι) : Continuous (F.density i) :=
  continuous_of_continuous_lift (F.density_smooth i).continuous

lemma speed_continuous : Continuous F.periodic.lift := by
  apply Continuous.quotient_lift
  exact F.smooth_speed.continuous

end PassagePackets
end ThreeTorus
end
end

section

/-! Actual conjugation data, invariant cutoff choices, and canonical spectral
reflection. No symmetry of an approximate model is substituted for reality of
the packets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

variable {F}

lemma Reflection.involutive {τ : ι → ι} (h : F.Reflection τ) (hi : Injective F.m) :
    Involutive τ := fun i => hi (by rw [h.index,h.index,neg_neg])

end PassagePackets

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι κ : Type*} (F : PassagePackets ι)

lemma support_subset_cylinderCore (i : ι) (a : UnitAddCircle) {x : ℝ}
    (hx : x ∈ support (F.A₀ i a)) : (x,a) ∈ F.cylinderCore i := subset_tsupport _ hx

lemma clipped_core_subset (q : κ → ι) (χ : κ → ℝ × UnitAddCircle → ℝ)
    (hχ : ∀ k, CylinderSmooth (χ k)) (hc : ∀ k, HasCompactSupport (χ k))
    (hs : ∀ k, support (χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ) (k : κ) :
    (F.clipped q χ hχ hc hs).cylinderCore k ⊆ tsupport (χ k) := by
  apply closure_minimal
  · intro p hp
    apply subset_tsupport
    intro hz
    exact hp (by simp [clipped,hz])
  · exact isClosed_tsupport _

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma marginalWeight_regular (i : ι) : Continuous (F.marginalWeight i) ∧
    HasCompactSupport (F.marginalWeight i) := by
  let w : ℝ × UnitAddCircle → ℝ := fun p => stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
    (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i p.2) p.1
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hw := stationaryWeight_signed_compact_continuous (contDiff_const.mul F.smooth_speed)
    (F.continuous_lift i) (fun a => (F.support_lift i a).trans Ioc_subset_Icc_self) F.Rpos hb.1 hb.2
  have hc : Continuous (F.marginalWeight i) := by
    have hh : Continuous (uncurry (fun (s : ℝ) (a : UnitAddCircle) => w (s,a))) := hw.1
    change Continuous (fun s => ∫ a, w (s,a) ∂AddCircle.haarAddCircle)
    simpa only [setIntegral_univ] using
      continuous_parametric_integral_of_continuous (X := ℝ) (Y := UnitAddCircle)
        (μ := AddCircle.haarAddCircle) hh isCompact_univ
  refine ⟨hc, (hw.2.image continuous_fst).of_isClosed_subset (isClosed_tsupport _) ?_⟩
  apply closure_minimal ?_ (hw.2.image continuous_fst).isClosed
  intro s hs
  by_contra hn
  have hz (a : UnitAddCircle) : w (s,a) = 0 := by
    by_contra hh
    exact hn ⟨(s,a),subset_tsupport w hh,rfl⟩
  apply hs
  simp only [marginalWeight,show ∀ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
    (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s = 0 from hz,integral_zero]

lemma marginalDensity_nonneg (i : ι) (z : UnitAddCircle) : 0 ≤ F.marginalDensity i z :=
  foldCircleDensity_nonneg (fun s => integral_nonneg (fun _a => branchDensity_nonneg
    (fun _ => sq_nonneg _) s)) z

lemma marginalDensity_measurable (i : ι) : Measurable (F.marginalDensity i) :=
  measurable_foldCircleDensity (F.marginalWeight_regular i).1.measurable

lemma marginalDensity_integrable (i : ι) : Integrable (F.marginalDensity i) AddCircle.haarAddCircle :=
  integrable_foldCircleDensity (F.marginalWeight_regular i).1.measurable
    ((F.marginalWeight_regular i).1.integrable_of_hasCompactSupport (F.marginalWeight_regular i).2)

/-- The actual old packet spectrum, without spare independence. -/
theorem marginalDensity_spectral (i : ι) :
    packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.marginalDensity i z)) := by
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hs a : support (F.A₀ i a) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i a hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have he := oldPacket_spectralDensity (m := F.m i) (c := 0) (v := F.periodic.lift)
    (F.continuous_amplitude i) (F.continuous_lift i) (F.lift_matches i)
    (fun a => (F.support_lift i a).trans (by
      intro x hx; exact ⟨lt_of_le_of_lt F.lo hx.1,hx.2.trans F.uo⟩)) hs
    F.speed_continuous.measurable F.smooth_speed (fun _ _ => rfl) isOpen_Ioo Ioo_subset_Icc_self hb.1 hb.2
  change _ = AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
    (foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
      (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s ∂AddCircle.haarAddCircle) z))
  simpa only [Int.cast_zero,sub_zero] using he

end PassagePackets
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PhysicalJets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite passage geometry families, physical charts, and all-jet bounds. -/

section

/-! Finite summation and composition estimates in the original physical L².
These let the literal per-packet passages be assembled without replacing their
vectors by independent spectral models. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalError_nonneg (f g : TripleTorus → ℂ) : 0 ≤ physicalError f g :=
  integral_nonneg (fun _ => sq_nonneg _)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_TrackedPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refresh and residue estimates, physical aggregates, tracked producers, pair/color aggregates, and colored states. -/

section

/-! Literal color sums in the concrete packet state. Colors are labels, not
new independent spectral data. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

variable {ι R : Type*} [Fintype ι] [DecidableEq R]

lemma continuous_colorVector (F : PassagePackets ι) (c : ι → R) (r : R) :
    Continuous (colorVector F c r) := by
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact continuous_packet (F.continuous_amplitude i) | exact continuous_const

lemma continuous_colorDensity (F : PassagePackets ι) (c : ι → R) (r : R) :
    Continuous (colorDensity F c r) := by
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact F.density_continuous i | exact continuous_const

end ThreeTorus
end
end

section

/-! A finite colored state and a pair record containing the two ACTUAL
smooth volume-preserving passage families. The existence theorem is derived
from the concrete neutral/signal producers, not supplied as an oracle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

attribute [instance] ColoredState.finite

namespace ColoredState
variable {R : Type} [DecidableEq R] (C : ColoredState R)
lemma density_continuous (r : R) : Continuous (C.density r) :=
  continuous_colorDensity C.packets C.color r
lemma vector_continuous (r : R) : Continuous (C.vector r) :=
  continuous_colorVector C.packets C.color r
end ColoredState

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketAlgebra
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet algebra and physical L2 metric estimates. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets

variable {ι κ : Type*}

lemma reindex_reflection (F : PassagePackets ι) {r : κ → ι}
    {τ : ι → ι} {σ : κ → κ} (h : F.Reflection τ) (he : ∀ i, r (σ i)=τ (r i)) :
    (F.reindex r).Reflection σ := by
  constructor
  · intro i; change F.m (r (σ i)) = -F.m (r i); rw [he,h.index]
  · intro i p; change F.A (r (σ i)) p = conj (F.A (r i) p); rw [he,h.amplitude]
  · intro i a x; change F.A₀ (r (σ i)) a x = conj (F.A₀ (r i) a x); rw [he,h.lift]

lemma append_good (F : PassagePackets ι) (G : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hF : F.GoodArc δ) (hG : G.GoodArc δ) (hV : G.V=F.V) :
    (F.append G hδ hF hG hV).GoodArc δ :=
  ⟨rfl,lt_min hF.2.1 hG.2.1,max_lt hF.2.2.1 hG.2.2.1,hF.2.2.2⟩

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalDist_nonneg (f g : TripleTorus → ℂ) : 0 ≤ physicalDist f g := Real.sqrt_nonneg _
lemma physicalDist_sq (f g : TripleTorus → ℂ) : physicalDist f g^2=physicalError f g :=
  Real.sq_sqrt (physicalError_nonneg f g)
lemma physicalDist_lt_iff (f g : TripleTorus → ℂ) {ε : ℝ} (hε : 0 < ε) :
    physicalDist f g < ε ↔ physicalError f g < ε^2 := Real.sqrt_lt' hε
lemma physicalDist_symm (f g : TripleTorus → ℂ) : physicalDist f g=physicalDist g f := by
  simp only [physicalDist,physicalError,norm_sub_rev]
lemma norm_toLp_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 ν) : ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂ν := by
  calc
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂ν := L2.inner_def _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx,real_inner_self_eq_norm_sq]
lemma physicalError_eq_norm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalError f g=‖hf.toLp f-hg.toLp g‖^2 := by
  rw [← hf.toLp_sub hg,norm_toLp_sq]
  rfl
lemma physicalDist_eq_norm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalDist f g=‖hf.toLp f-hg.toLp g‖ := by
  rw [physicalDist,physicalError_eq_norm hf hg,Real.sqrt_sq (norm_nonneg _)]
lemma physicalDist_triangle {f g h : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) (hh : MemLp h 2 tripleVolume) :
    physicalDist f h ≤ physicalDist f g+physicalDist g h := by
  rw [physicalDist_eq_norm hf hh,physicalDist_eq_norm hf hg,physicalDist_eq_norm hg hh]
  simpa only [dist_eq_norm] using dist_triangle (hf.toLp f) (hg.toLp g) (hh.toLp h)
lemma physicalDist_finsum {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, MemLp (f i) 2 tripleVolume) (hg : ∀ i, MemLp (g i) 2 tripleVolume) :
    physicalDist (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤ ∑ i, physicalDist (f i) (g i) := by
  classical
  have hsum (a : ι → TripleTorus → ℂ) (ha : ∀ i, MemLp (a i) 2 tripleVolume) :
      (memLp_finsetSum Finset.univ (fun i _ => ha i)).toLp (fun x => ∑ i, a i x) =
        ∑ i, (ha i).toLp (a i) := by
    apply Lp.ext
    filter_upwards [(memLp_finsetSum Finset.univ (fun i _ => ha i)).coeFn_toLp,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i => (ha i).toLp (a i)),
      ae_all_iff.mpr (fun i => (ha i).coeFn_toLp)] with x hx hy hz
    rw [hx,hy]
    exact Finset.sum_congr rfl (fun i _ => (hz i).symm)
  rw [physicalDist_eq_norm (memLp_finsetSum Finset.univ (fun i _ => hf i))
    (memLp_finsetSum Finset.univ (fun i _ => hg i)),hsum f hf,hsum g hg,← Finset.sum_sub_distrib]
  simp_rw [physicalDist_eq_norm (hf _) (hg _)]
  exact norm_sum_le Finset.univ (fun i => (hf i).toLp (f i)-(hg i).toLp (g i))

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_SymmetricPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflected neutral and signal producers, symmetric colors, physical control, and grouped cutoffs. -/

section

/-! Finite physical C-infinity restrictions, on both the map and inverse,
threaded through the actual refresh and transmission integer choices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PhysicalJetData

lemma Close.mono {Q : PhysicalJetData} {ε η : ℝ} {F G : PhysicalFrame} {V W : ℝ → ℝ}
    (h : Q.Close ε F V G W) (he : ε ≤ η) : Q.Close η F V G W :=
  fun i x hx => (h i x hx).trans he

lemma Close.trans {Q : PhysicalJetData} {ε η : ℝ} {F G H : PhysicalFrame}
    {V W U : ℝ → ℝ} (h : Q.Close ε F V G W) (h' : Q.Close η G W H U) :
    Q.Close (ε+η) F V H U := by
  intro i x hx
  exact (dist_triangle _ _ _).trans (by linarith [h i x hx,h' i x hx])

end PhysicalJetData

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Whitening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coefficient-space spectral whitening, including the zero-density set. -/

section

/-!
Exact coefficient-space whitening, including the zero
set of the spectral density. The frequency map is arbitrary; for torus packets
it is `(m,u,a) ↦ m φ(u) mod 1`. No nonvanishing of the density is imposed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical
namespace ThreeTorus

lemma measurable_energyWeight {X : Type*} [MeasurableSpace X] {F : X → ℂ}
    (hF : Measurable F) : Measurable (energyWeight F) :=
  (hF.norm.pow_const 2).ennreal_ofReal

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_FlatPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat support, finite packet L2 estimates, neutral selection, density invariance, and finite spectral whitening. -/

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology ENNReal NNReal
namespace ThreeTorus

lemma integral_packet_pair_L2 {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (hB : MemLp B 2 slowVolume) (m k : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B x ∂tripleVolume) =
      if m = k then ∫ ua, starRingEnd ℂ (A ua)*B ua ∂slowVolume else 0 := by
  have hi : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet m A x)*packet k B x) tripleVolume :=
    (memLp_packet hA m).star.integrable_mul (memLp_packet hB k)
  rw [MeasureTheory.integral_prod_symm _ hi]
  have he (ua : UnitAddCircle × UnitAddCircle) :
      (∫ θ : UnitAddCircle, starRingEnd ℂ (packet m A (θ,ua))*packet k B (θ,ua)
        ∂AddCircle.haarAddCircle) =
      (starRingEnd ℂ (A ua)*B ua)*(if m = k then 1 else 0) := by
    simp only [packet,map_mul]
    have hr (θ : UnitAddCircle) :
        starRingEnd ℂ (A ua)*starRingEnd ℂ (fourier m θ)*(B ua*fourier k θ) =
        (starRingEnd ℂ (A ua)*B ua)*(starRingEnd ℂ (fourier m θ)*fourier k θ) := by ring
    simp_rw [hr]
    rw [integral_const_mul,integral_fourier_pair]
  simp_rw [he]
  split_ifs <;> simp

lemma memLp_frequency_mul {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {A : X → ℂ} (hA : MemLp A 2 ν) {ζ : X → UnitAddCircle}
    (hζ : Measurable ζ) (n : ℤ) :
    MemLp (fun x => fourier n (ζ x)*A x) 2 ν := by
  apply hA.congr_norm
  · exact (((fourier n).continuous.measurable.comp hζ).aestronglyMeasurable).mul
      hA.aestronglyMeasurable
  · filter_upwards [] with x
    simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]

/-- Exact correlation formula, requiring no smoothness of the coefficients. -/
lemma packet_correlation_L2 {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
      packet m A (twistIter φ n x) ∂tripleVolume) =
    ∫ ua : UnitAddCircle × UnitAddCircle,
      fourier n (m • φ ua.1)*(‖A ua‖^2 : ℝ) ∂slowVolume := by
  let B : UnitAddCircle × UnitAddCircle → ℂ :=
    fun ua => fourier n (m • φ ua.1)*A ua
  have hB : MemLp B 2 slowVolume := memLp_frequency_mul hA
    ((hφ.comp measurable_fst).const_smul m) n
  have he : ∀ x, packet m A (twistIter φ n x) = packet m B x := by
    intro x
    rw [packet_twistIter]
    dsimp [packet,B]
    ring
  simp_rw [he]
  rw [integral_packet_pair_L2 hA hB,ite_eq_left rfl]
  apply integral_congr_ae
  filter_upwards [] with ua
  dsimp only [B]
  rw [show starRingEnd ℂ (A ua)*(fourier n (m • φ ua.1)*A ua) =
    fourier n (m • φ ua.1)*(starRingEnd ℂ (A ua)*A ua) by ring,normSq_complex]

/-- Exact pushforward measure even for the endpoint-discontinuous flat vector. -/
lemma packet_spectral_moment_L2 {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hAm : Measurable A)
    (hA : MemLp A 2 slowVolume) (m n : ℤ) :
    (∫ z, fourier n z ∂packetSpectralMeasure φ m A) =
      ∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
        packet m A (twistIter φ n x) ∂tripleVolume := by
  rw [packet_correlation_L2 hA hφ]
  unfold packetSpectralMeasure
  erw [integral_map ((hφ.comp measurable_fst).const_smul m).aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  erw [integral_withDensity_eq_integral_toReal_smul
    (hAm.norm.pow_const 2).ennreal_ofReal (by filter_upwards [] with ua; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with ua
  simp only [Function.comp_apply,Pi.smul_apply]
  rw [ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul,mul_comm]

lemma measurable_circleRep (o : ℝ) : Measurable (circleRep o) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 o).measurable

lemma circleRep_coe {o x : ℝ} (hx : x ∈ Ioc o (o+1)) :
    circleRep o (x : UnitAddCircle) = x := by
  exact congrArg Subtype.val (AddCircle.equivIoc_coe_eq hx)

lemma coe_circleRep (o : ℝ) (z : UnitAddCircle) :
    (circleRep o z : UnitAddCircle) = z := by
  exact AddCircle.coe_equivIoc (p := 1) (a := o) (y := z)

lemma integral_fourier_haar (n : ℤ) :
    (∫ z : UnitAddCircle, fourier n z ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have hh := integral_fourier_pair 0 n
  simpa only [fourier_zero, map_one, one_mul, eq_comm] using hh

end ThreeTorus
end
end

section

/-! Finite measurable packet coefficient families, needed for whitening the
actual output of reflected prediction. The physical vectors remain literal
finite packet sums, not arbitrary Hilbert-space replacements. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma measurable_coefficientFrequency {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) : Measurable (coefficientFrequency φ m) :=
  measurable_from_prod_countable_right (fun i => (hφ.comp measurable_fst).const_smul (m i))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketVector_sub (m : ι → ℤ) (A B : ι → UnitAddCircle × UnitAddCircle → ℂ) :
    finitePacketVector m (fun i x => A i x-B i x) =
      fun x => finitePacketVector m A x-finitePacketVector m B x := by
  funext x
  simp only [finitePacketVector,packet,sub_mul,Finset.sum_sub_distrib]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_inner {m : ι → ℤ} (hm : Injective m)
    {A B : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (hB : ∀ i, MemLp (B i) 2 slowVolume) :
    (∫ x, conj (finitePacketVector m A x)*finitePacketVector m B x ∂tripleVolume) =
      ∑ i, ∫ x, conj (A i x)*B i x ∂slowVolume := by
  classical
  have hi i j : Integrable (fun x => conj (packet (m i) (A i) x)*packet (m j) (B j) x) tripleVolume :=
    (memLp_packet (hA i) (m i)).star.integrable_mul (memLp_packet (hB j) (m j))
  simp only [finitePacketVector,map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi j i))]
  simp_rw [integral_finsetSum _ (fun j _ => hi j _),integral_packet_pair_L2 (hA _) (hB _)]
  simp only [hm.eq_iff]
  simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_energy {m : ι → ℤ} (hm : Injective m)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume) =
      ∑ i, ∫ x, ‖A i x‖^2 ∂slowVolume := by
  have hh := finitePacket_inner hm hA hA
  simp only [normSq_complex,integral_complex_ofReal,← Complex.ofReal_sum] at hh
  exact Complex.ofReal_injective hh

lemma coefficient_integral_normsq {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x : ι × (UnitAddCircle × UnitAddCircle), ‖A x.1 x.2‖^2 ∂coefficientVolume) =
      ∑ i, ∫ x, ‖A i x‖^2 ∂slowVolume := by
  rw [integral_prod _ (integrable_coefficient_normsq hAm hA),integral_count]

end FinitePacket
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma physicalDist_eLpNorm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalDist f g = (eLpNorm (fun x => f x-g x) 2 tripleVolume).toReal := by
  rw [physicalDist_eq_norm hf hg,← hf.toLp_sub hg,Lp.norm_toLp]
  rfl

lemma eLpNorm_packet (m : ℤ) {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : AEStronglyMeasurable A slowVolume) :
    eLpNorm (packet m A) 2 tripleVolume = eLpNorm A 2 slowVolume := by
  have hn (x : TripleTorus) : ‖packet m A x‖ = ‖A x.2‖ := by
    simp only [packet,norm_mul,fourier_apply,Circle.norm_coe,mul_one]
  have hbase : AEStronglyMeasurable (fun point : TripleTorus => A point.2) tripleVolume :=
    hA.comp_measurePreserving measurePreserving_snd
  have hpacket : AEStronglyMeasurable (packet m A) tripleVolume :=
    hbase.mul (((fourier m).continuous.comp continuous_fst).aestronglyMeasurable)
  refine (eLpNorm_congr_norm_ae (Filter.Eventually.of_forall hn)).trans ?_
  exact eLpNorm_comp_measurePreserving hA measurePreserving_snd

lemma physicalDist_packet {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (hB : MemLp B 2 slowVolume) (m : ℤ) :
    physicalDist (packet m A) (packet m B) = (eLpNorm (fun x => A x-B x) 2 slowVolume).toReal := by
  rw [physicalDist_eLpNorm (memLp_packet hA m) (memLp_packet hB m)]
  have he : (fun x => packet m A x-packet m B x) = packet m (fun x => A x-B x) := by
    funext x; simp only [packet,sub_mul]
  rw [he]
  exact congrArg ENNReal.toReal
    (eLpNorm_packet m (hA.aestronglyMeasurable.sub hB.aestronglyMeasurable))

lemma physicalDist_packet_lt {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (hB : MemLp B 2 slowVolume) (m : ℤ) {ε : ℝ}
    (hε : 0 < ε) (hAB : eLpNorm (fun x => A x-B x) 2 slowVolume < ENNReal.ofReal ε) :
    physicalDist (packet m A) (packet m B) < ε := by
  rw [physicalDist_packet hA hB]
  exact (ENNReal.toReal_lt_toReal (hA.sub hB).eLpNorm_ne_top ENNReal.ofReal_ne_top).2 hAB |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

lemma physicalDist_add_le {f g h j : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume)
    (hh : MemLp h 2 tripleVolume) (hj : MemLp j 2 tripleVolume) :
    physicalDist (fun x => f x+h x) (fun x => g x+j x) ≤ physicalDist f g+physicalDist h j := by
  change physicalDist (f+h) (g+j) ≤ _
  rw [physicalDist_eq_norm (hf.add hh) (hg.add hj),hf.toLp_add hh,hg.toLp_add hj]
  rw [show hf.toLp f+hh.toLp h-(hg.toLp g+hj.toLp j) =
    (hf.toLp f-hg.toLp g)+(hh.toLp h-hj.toLp j) by abel]
  simpa only [physicalDist_eq_norm hf hg,physicalDist_eq_norm hh hj] using
    norm_add_le (hf.toLp f-hg.toLp g) (hh.toLp h-hj.toLp j)

lemma physicalDist_small_sum {ι : Type*} [Fintype ι]
    {m : ι → ℤ} {A B : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (hB : ∀ i, MemLp (B i) 2 slowVolume)
    {ε : ℝ} (hε : 0 < ε)
    (hAB : ∀ i, eLpNorm (fun x => A i x-B i x) 2 slowVolume <
      ENNReal.ofReal (ε/(Fintype.card ι+1))) :
    physicalDist (finitePacketVector m A) (finitePacketVector m B) < ε := by
  have hc : (0:ℝ) < Fintype.card ι+1 := by positivity
  have he : 0 < ε/(Fintype.card ι+1) := div_pos hε hc
  calc
    _ ≤ ∑ i, physicalDist (packet (m i) (A i)) (packet (m i) (B i)) :=
      physicalDist_finsum (fun i => memLp_packet (hA i) _) (fun i => memLp_packet (hB i) _)
    _ ≤ ∑ _i : ι, ε/(Fintype.card ι+1) := Finset.sum_le_sum
      (fun i _ => (physicalDist_packet_lt (hA i) (hB i) (m i) he (hAB i)).le)
    _ < ε := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hc).2
      nlinarith

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} [Fintype ι] (F : PassagePackets ι)

lemma modeSum_good (b : ι → ℂ) {δ : ℝ} (hg : F.GoodArc δ) :
    (F.modeSum b).GoodArc δ := hg

lemma modeSum_injective (b : ι → ℂ) : Injective (F.modeSum b).m := Subtype.val_injective

lemma modeSum_vector (b : ι → ℂ) :
    finitePacketVector (F.modeSum b).m (F.modeSum b).A =
      fun x => ∑ i, b i*packet (F.m i) (F.A i) x := by
  classical
  funext x
  change (∑ k : F.ModeIndex, (∑ i, (if F.m i=k.val then b i else 0)*F.A i x.2)*fourier k.val x.1) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let k : F.ModeIndex := ⟨F.m i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  rw [Finset.sum_eq_single k]
  · simp only [k,ite_true,packet,mul_assoc]
  · intro l _ hli
    have hn : F.m i ≠ l.val := by intro h; exact hli (Subtype.ext h.symm)
    simp only [hn,ite_false,zero_mul]
  · exact fun h => (h (Finset.mem_univ _)).elim

lemma modeSum_reflection {τ : ι → ι} (hτ : Involutive τ) (hr : F.Reflection τ)
    {b : ι → ℂ} (hb : ∀ i, b (τ i)=conj (b i)) :
    (F.modeSum b).Reflection (F.modeNeg hr) := by
  classical
  have hs (C : ι → ℂ) (hC : ∀ i, C (τ i)=conj (C i)) (k : F.ModeIndex) :
      (∑ i, (if F.m i= -k.val then b i else 0)*C i) =
        conj (∑ i, (if F.m i=k.val then b i else 0)*C i) := by
    rw [← Equiv.sum_comp (hτ.toPerm τ) (fun i => (if F.m i= -k.val then b i else 0)*C i)]
    simp only [Function.Involutive.coe_toPerm,hr.index,neg_inj,hb,hC,map_sum,map_mul,apply_ite,map_zero]
  constructor
  · intro k; rfl
  · intro k p
    exact hs (fun i => F.A i p) (fun i => hr.amplitude i p) k
  · intro k a x
    exact hs (fun i => F.A₀ i a x) (fun i => hr.lift i a x) k

end PassagePackets
end ThreeTorus
end
end

section

/-! Exact measurable spectral calculus for the literal finite packets.
This is the bridge from the energy-map whitening to the
actual physical packet family. It does not assume a spectral constructor. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma finitePacketSpectralMeasure_eq_sum {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) (m : ι → ℤ) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) :
    finitePacketSpectralMeasure φ m A = ∑ i, packetSpectralMeasure φ (m i) (A i) := by
  classical
  ext s hs
  have hz := measurable_coefficientFrequency hφ m
  have hAm : Measurable (fun x : ι × (UnitAddCircle × UnitAddCircle) => A x.1 x.2) :=
    measurable_from_prod_countable_right hA
  have he := measurable_energyWeight hAm
  rw [finitePacketSpectralMeasure, Measure.map_apply hz hs, withDensity_apply _ (hz hs),
    ← lintegral_indicator (hz hs)]
  rw [lintegral_prod _ (he.indicator (hz hs)).aemeasurable, lintegral_count, tsum_fintype,
    Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hzi : Measurable (fun ua : UnitAddCircle × UnitAddCircle => m i • φ ua.1) :=
    (hφ.comp measurable_fst).const_smul (m i)
  rw [packetSpectralMeasure, Measure.map_apply hzi hs, withDensity_apply _ (hzi hs),
    ← lintegral_indicator (hzi hs)]
  apply lintegral_congr
  intro ua
  simp only [indicator_apply, mem_preimage, coefficientFrequency, energyWeight]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_twist (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (n : ℤ) (x : TripleTorus) :
    finitePacketVector m A (twistIter φ n x) =
      finitePacketVector m (fun i ua => fourier n (m i • φ ua.1) * A i ua) x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [packet_twistIter]
  dsimp only [packet]
  ring

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_correlation {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (n : ℤ) :
    (∫ x, conj (finitePacketVector m A x) * finitePacketVector m A (twistIter φ n x)
      ∂tripleVolume) =
      ∑ i, ∫ ua, fourier n (m i • φ ua.1) * (‖A i ua‖^2 : ℝ) ∂slowVolume := by
  simp_rw [finitePacket_twist]
  have hB : ∀ i, MemLp (fun ua => fourier n (m i • φ ua.1) * A i ua) 2 slowVolume :=
    fun i => memLp_frequency_mul (hA i) ((hφ.comp measurable_fst).const_smul (m i)) n
  rw [finitePacket_inner hm hA hB]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with ua
  rw [show conj (A i ua) * (fourier n (m i • φ ua.1) * A i ua) =
    fourier n (m i • φ ua.1) * (conj (A i ua) * A i ua) by ring, normSq_complex]

lemma coefficient_normsq_eq_physical {m : ι → ℤ} (hm : Injective m)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x : ι × (UnitAddCircle × UnitAddCircle), ‖A x.1 x.2‖^2 ∂coefficientVolume) =
      ∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume := by
  rw [coefficient_integral_normsq hAm hA, finitePacket_energy hm hA]

end FinitePacket
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketCalculus
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trigonometric approximation, spectral calculus, density distances, and reflected clipping. -/

section

/-! Literal measurable finite-packet spectral calculus and Laurent approximation.
No abstract unitary is substituted for the actual twist. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma finite_energy_measure {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : X → ℂ}
    (hF : MemLp F 2 μ) : IsFiniteMeasure (μ.withDensity (energyWeight F)) := by
  apply isFiniteMeasure_withDensity
  have hf := (hasFiniteIntegral_iff_norm _).1
    (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).hasFiniteIntegral
  simpa only [energyWeight,Real.norm_eq_abs,abs_pow,abs_norm] using hf.ne

lemma packetSpectralMeasure_finite {φ : UnitAddCircle → UnitAddCircle} (m : ℤ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hA : MemLp A 2 slowVolume) :
    IsFiniteMeasure (packetSpectralMeasure φ m A) := by
  let := finite_energy_measure hA
  exact Measure.isFiniteMeasure_map (slowVolume.withDensity (energyWeight A)) _

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma finitePacket_spectral_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) (n : ℤ) :
    (∫ x, conj (finitePacketVector m A x)*finitePacketVector m A (twistIter φ n x)
      ∂tripleVolume) = ∫ z, fourier n z ∂finitePacketSpectralMeasure φ m A := by
  rw [finitePacketSpectralMeasure_eq_sum hφ m hAm,integral_finsetSum_measure]
  · rw [finitePacket_correlation hφ hm hA n]
    apply Finset.sum_congr rfl
    intro i _
    rw [packet_spectral_moment_L2 hφ (hAm i) (hA i),packet_correlation_L2 (hA i) hφ]
  · intro i _
    let := packetSpectralMeasure_finite (φ := φ) (m i) (hA i)
    exact (fourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma finitePacket_flat_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hflat : finitePacketSpectralMeasure φ m A = phaseHaar) (n : ℤ) :
    (∫ x, conj (finitePacketVector m A x)*finitePacketVector m A (twistIter φ n x)
      ∂tripleVolume) = if n = 0 then 1 else 0 := by
  rw [finitePacket_spectral_moment hφ hm hAm hA,hflat]
  exact integral_fourier_haar n

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma measurable_multiplyPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {a : UnitAddCircle → ℂ} (ha : Measurable a)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, Measurable (A i)) (i : ι) :
    Measurable (multiplyPackets φ m a A i) :=
  (ha.comp ((hφ.comp measurable_fst).const_smul (m i))).mul (hA i)

end FinitePacket
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeTorus

lemma norm_sq_sum_single_live {ι : Type*} [Fintype ι] (a : ι → ℂ)
    (hd : ∀ i j, i ≠ j → a i=0 ∨ a j=0) :
    ‖∑ i, a i‖^2 = ∑ i, ‖a i‖^2 := by
  classical
  by_cases h : ∃ i, a i ≠ 0
  · obtain ⟨i,hi⟩ := h
    have hz (j : ι) (hj : j ≠ i) : a j=0 := (hd i j hj.symm).resolve_left hi
    rw [Finset.sum_eq_single i,Finset.sum_eq_single i]
    · intro j _ hj; simp [hz j hj]
    · simp
    · intro j _ hj; exact hz j hj
    · simp
  · have hz : ∀ i, a i=0 := by simpa using h
    simp [hz]

lemma packetSpectralMeasure_zero (φ : UnitAddCircle → UnitAddCircle) (m : ℤ) :
    packetSpectralMeasure φ m (fun _ => 0) = 0 := by
  simp [packetSpectralMeasure]

lemma packetSpectralMeasure_sum_disjoint {ι : Type*} [Fintype ι]
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) (m : ℤ)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, Measurable (A i))
    (hd : ∀ x i j, i ≠ j → A i x=0 ∨ A j x=0) :
    packetSpectralMeasure φ m (fun x => ∑ i, A i x) = ∑ i, packetSpectralMeasure φ m (A i) := by
  classical
  ext s hs
  have hz : Measurable (fun ua : UnitAddCircle × UnitAddCircle => m • φ ua.1) :=
    (hφ.comp measurable_fst).const_smul m
  rw [packetSpectralMeasure,Measure.map_apply hz hs,withDensity_apply _ (hz hs),Measure.finsetSum_apply]
  simp_rw [packetSpectralMeasure,Measure.map_apply hz hs,withDensity_apply _ (hz hs)]
  have he : energyWeight (fun x => ∑ i, A i x) = fun x => ∑ i, energyWeight (A i) x := by
    funext x
    simp only [energyWeight,norm_sq_sum_single_live _ (hd x)]
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖A i x‖)
  change (∫⁻ x in (fun ua : UnitAddCircle × UnitAddCircle => m • φ ua.1) ⁻¹' s,
    energyWeight (fun x => ∑ i, A i x) x ∂slowVolume) = _
  rw [he,lintegral_finsetSum]
  · rfl
  · intro i _
    exact measurable_energyWeight (hA i)

/-- Honest gathering by angular frequency preserves the spectral measure
when repeated modes have disjoint physical coefficient supports. -/
theorem gather_spectrum {ι : Type*} [Fintype ι]
    (m : ι → ℤ) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) (J : Finset ℤ) (hJ : ∀ i, m i ∈ J)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (hd : ∀ x i j, i ≠ j → m i=m j → A i x=0 ∨ A j x=0) :
    (∑ k : ↥J, packetSpectralMeasure φ k.val
      (fun x => ∑ i, if m i=k.val then A i x else 0)) =
      ∑ i, packetSpectralMeasure φ (m i) (A i) := by
  classical
  have he (k : ↥J) : packetSpectralMeasure φ k.val
      (fun x => ∑ i, if m i=k.val then A i x else 0) =
      ∑ i, if m i=k.val then packetSpectralMeasure φ (m i) (A i) else 0 := by
    rw [packetSpectralMeasure_sum_disjoint hφ k.val]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : m i=k.val
      · simp [hi]
      · simp [hi,packetSpectralMeasure_zero]
    · intro i
      by_cases hi : m i=k.val <;> simp only [hi,ite_true,ite_false]
      · exact hA i
      · exact measurable_const
    · intro x i j hij
      by_cases hi : m i=k.val <;> by_cases hj : m j=k.val <;> simp only [hi,hj,ite_true,ite_false,eq_self,or_true,true_or]
      exact hd x i j hij (hi.trans hj.symm)
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let k : ↥J := ⟨m i,hJ i⟩
  rw [Finset.sum_eq_single k]
  · simp [k]
  · intro l _ hli
    have hn : m i ≠ l.val := fun h => hli (Subtype.ext h.symm)
    simp [hn]
  · simp

namespace PassagePackets
variable {ι : Type*} [Fintype ι] (F : PassagePackets ι)

lemma amplitude_disjoint_of_cylinderCore
    (hd : ∀ i j, i ≠ j → F.m i=F.m j → Disjoint (F.cylinderCore i) (F.cylinderCore j)) :
    ∀ p i j, i ≠ j → F.m i=F.m j → F.A i p=0 ∨ F.A j p=0 := by
  have _ := (inferInstance : Fintype ι)
  intro p i j hij hm
  let x : ℝ := (AddCircle.equivIoc 1 F.o p.1).1
  have hx : x ∈ Ioc F.o (F.o+1) := (AddCircle.equivIoc 1 F.o p.1).2
  have hpx : (x:UnitAddCircle)=p.1 := (AddCircle.equivIoc 1 F.o).symm_apply_apply p.1
  by_cases hi : F.A i p=0
  · exact Or.inl hi
  · right
    by_contra hj
    have hix : F.A₀ i p.2 x ≠ 0 := by
      rw [← F.lift_matches i p.2 x hx,hpx]
      exact hi
    have hjx : F.A₀ j p.2 x ≠ 0 := by
      rw [← F.lift_matches j p.2 x hx,hpx]
      exact hj
    exact Set.disjoint_left.mp (hd i j hij hm)
      (F.support_subset_cylinderCore i p.2 hix) (F.support_subset_cylinderCore j p.2 hjx)

end PassagePackets
end ThreeTorus
end
end

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ThreeTorus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma l2_integral_norm_sq (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖^2 ∂μ) = ‖f‖^2 := by
  have h := congrArg (RCLike.re (K := ℂ)) (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)] at h
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] using h.symm

lemma integral_norm_product_le (f g : Lp ℂ 2 μ) :
    (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤ ‖f‖ * ‖g‖ := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (show (2 : ℝ).HolderConjugate 2 from Real.holderConjugate_iff.mpr (by norm_num))
    (f := (f : Ω → ℂ)) (g := (g : Ω → ℂ)) (by simpa using Lp.memLp f) (by simpa using Lp.memLp g)
  simp_rw [← Real.sqrt_eq_rpow, Real.rpow_two] at h
  simpa only [l2_integral_norm_sq, Real.sqrt_sq (norm_nonneg _)] using h

lemma density_norm_bound_l2 (f g : Lp ℂ 2 μ) :
    (∫ x, |‖f x‖^2 - ‖g x‖^2| ∂μ) ≤ (‖f‖+‖g‖)*‖f-g‖ := by
  have hiF : Integrable (fun x => ‖f x‖^2) μ := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hiG : Integrable (fun x => ‖g x‖^2) μ := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hid (v : Lp ℂ 2 μ) : Integrable (fun x => ‖v x‖ * ‖(f-g) x‖) μ := by
    exact (Lp.memLp v).norm.integrable_mul (Lp.memLp (f-g)).norm
  have he : ∀ᵐ x ∂μ, |‖f x‖^2 - ‖g x‖^2| ≤
      ‖f x‖ * ‖(f-g) x‖ + ‖g x‖ * ‖(f-g) x‖ := by
    filter_upwards [Lp.coeFn_sub f g] with x hx
    rw [hx, Pi.sub_apply]
    calc
      |‖f x‖^2 - ‖g x‖^2| = |‖f x‖ - ‖g x‖| * (‖f x‖ + ‖g x‖) := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖f x‖ + ‖g x‖)]
        ring
      _ ≤ ‖f x-g x‖ * (‖f x‖ + ‖g x‖) := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ x, ‖f x‖ * ‖(f-g) x‖ + ‖g x‖ * ‖(f-g) x‖ ∂μ :=
      integral_mono_ae ((hiF.sub hiG).abs) ((hid f).add (hid g)) he
    _ = (∫ x, ‖f x‖ * ‖(f-g) x‖ ∂μ) + (∫ x, ‖g x‖ * ‖(f-g) x‖ ∂μ) := integral_add (hid f) (hid g)
    _ ≤ ‖f‖ * ‖f-g‖ + ‖g‖ * ‖f-g‖ := add_le_add (integral_norm_product_le f (f-g)) (integral_norm_product_le g (f-g))
    _ = _ := by ring

end ThreeTorus

end
end

section

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal Topology BigOperators
namespace ThreeTorus

lemma energy_integral_test {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p r : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y))) (hr : Measurable r) :
    (∫ y, p y*r y ∂ν) = ∫ x, ‖F x‖^2*r (ζ x) ∂μ := by
  have hleft : (∫ y, r y ∂ν.withDensity (fun y => ENNReal.ofReal (p y))) =
      ∫ y, p y*r y ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hpn _),smul_eq_mul]
  rw [← hleft,← hpush,integral_map hζ.aemeasurable hr.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_energyWeight hF)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [energyWeight,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

lemma integrable_mul_bounded_real {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) :
    Integrable (fun x => f x*g x) μ := by
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  exact .of_forall fun x => by
    change ‖f x*g x‖ ≤ ‖f x‖
    rw [norm_mul,Real.norm_eq_abs (g x)]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb x)

/-- L¹ contraction for the actual pushed coefficient energies. This proves the
paper's density estimate without postulating any abstract spectral map. -/
lemma energy_density_difference_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F G : X → ℂ} {p q : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hG : Measurable G)
    (hFl : MemLp F 2 μ) (hGl : MemLp G 2 μ)
    (hp : Measurable p) (hq : Measurable q) (hpi : Integrable p ν) (hqi : Integrable q ν)
    (hpn : ∀ y, 0 ≤ p y) (hqn : ∀ y, 0 ≤ q y)
    (hFp : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hGq : (μ.withDensity (energyWeight G)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (q y))) :
    (∫ y, |p y-q y| ∂ν) ≤ ∫ x, |‖F x‖^2-‖G x‖^2| ∂μ := by
  let r : Y → ℝ := fun y => if p y < q y then -1 else 1
  have hr : Measurable r := measurable_const.ite (measurableSet_lt hp hq) measurable_const
  have hb (y) : |r y| ≤ 1 := by dsimp only [r]; split_ifs <;> norm_num
  have he (y) : |p y-q y| = p y*r y-q y*r y := by
    dsimp only [r]
    split_ifs with h
    · rw [abs_of_neg (sub_neg.mpr h)]; ring
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt h))]; ring
  have hFi : Integrable (fun x => ‖F x‖^2) μ := hFl.integrable_norm_pow (by norm_num)
  have hGi : Integrable (fun x => ‖G x‖^2) μ := hGl.integrable_norm_pow (by norm_num)
  have hfr := integrable_mul_bounded_real hFi (hr.comp hζ) (fun x => hb (ζ x))
  have hgr := integrable_mul_bounded_real hGi (hr.comp hζ) (fun x => hb (ζ x))
  calc
    _ = (∫ y, p y*r y ∂ν)-(∫ y, q y*r y ∂ν) := by
      simp_rw [he]
      exact integral_sub (integrable_mul_bounded_real hpi hr hb)
        (integrable_mul_bounded_real hqi hr hb)
    _ = ∫ x, ‖F x‖^2*r (ζ x)-‖G x‖^2*r (ζ x) ∂μ := by
      rw [energy_integral_test hζ hF hp hpn hFp hr,
        energy_integral_test hζ hG hq hqn hGq hr]
      exact (integral_sub hfr hgr).symm
    _ ≤ _ := by
      apply integral_mono (hfr.sub hgr) (hFi.sub hGi).abs
      intro x
      change ‖F x‖^2*r (ζ x)-‖G x‖^2*r (ζ x) ≤ |‖F x‖^2-‖G x‖^2|
      calc
        _ = (‖F x‖^2-‖G x‖^2)*r (ζ x) := by ring
        _ ≤ |(‖F x‖^2-‖G x‖^2)*r (ζ x)| := le_abs_self _
        _ ≤ _ := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hb _)

lemma density_norm_bound_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F G : X → ℂ} (hf : MemLp F 2 μ) (hg : MemLp G 2 μ) :
    (∫ x, |‖F x‖^2-‖G x‖^2| ∂μ) ≤
      (‖hf.toLp F‖+‖hg.toLp G‖)*‖hf.toLp F-hg.toLp G‖ := by
  have he : (∫ x, |‖F x‖^2-‖G x‖^2| ∂μ) =
      ∫ x, |‖hf.toLp F x‖^2-‖hg.toLp G x‖^2| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    rw [hx,hy]
  rw [he]
  exact density_norm_bound_l2 _ _

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeTorus
section
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma coefficient_norm_eq_physical {m : ι → ℤ} (hm : Injective m)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    ‖(coefficient_memLp hAm hA).toLp (fun p : ι × (UnitAddCircle × UnitAddCircle) => A p.1 p.2)‖ =
      ‖(memLp_finitePacketVector hA).toLp (finitePacketVector m A)‖ := by
  have hh := coefficient_normsq_eq_physical hm hAm hA
  rw [← norm_toLp_sq (coefficient_memLp hAm hA),← norm_toLp_sq (memLp_finitePacketVector hA)] at hh
  nlinarith [norm_nonneg ((coefficient_memLp hAm hA).toLp (fun p : ι × (UnitAddCircle × UnitAddCircle) => A p.1 p.2)),
    norm_nonneg ((memLp_finitePacketVector hA).toLp (finitePacketVector m A))]

lemma coefficient_difference_norm {m : ι → ℤ} (hm : Injective m)
    {A B : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hBm : ∀ i, Measurable (B i))
    (hAl : ∀ i, MemLp (A i) 2 slowVolume) (hBl : ∀ i, MemLp (B i) 2 slowVolume) :
    ‖(coefficient_memLp hAm hAl).toLp (fun p : ι × (UnitAddCircle × UnitAddCircle) => A p.1 p.2)-
      (coefficient_memLp hBm hBl).toLp (fun p : ι × (UnitAddCircle × UnitAddCircle) => B p.1 p.2)‖ =
      physicalDist (finitePacketVector m A) (finitePacketVector m B) := by
  have hh := coefficient_norm_eq_physical hm (fun i => (hAm i).sub (hBm i))
    (fun i => (hAl i).sub (hBl i))
  rw [Lp.norm_toLp,Lp.norm_toLp] at hh
  change (eLpNorm (fun p : ι × (UnitAddCircle × UnitAddCircle) => A p.1 p.2-B p.1 p.2) 2 coefficientVolume).toReal =
    (eLpNorm (finitePacketVector m (fun i p => A i p-B i p)) 2 tripleVolume).toReal at hh
  rw [finitePacketVector_sub] at hh
  rw [← MemLp.toLp_sub,Lp.norm_toLp,
    physicalDist_eLpNorm (memLp_finitePacketVector hAl) (memLp_finitePacketVector hBl)]
  exact hh

/-- The source's constant-one density bound for the literal finite packets,
including a nonsmooth old admissible vector. -/
theorem finitePacket_density_distance {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) {m : ι → ℤ} (hm : Injective m)
    {A B : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hBm : ∀ i, Measurable (B i))
    (hAl : ∀ i, MemLp (A i) 2 slowVolume) (hBl : ∀ i, MemLp (B i) 2 slowVolume)
    {p q : UnitAddCircle → ℝ} (hpm : Measurable p) (hqm : Measurable q)
    (hpi : Integrable p phaseHaar) (hqi : Integrable q phaseHaar)
    (hpn : ∀ z, 0 ≤ p z) (hqn : ∀ z, 0 ≤ q z)
    (hAp : finitePacketSpectralMeasure φ m A = phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hBq : finitePacketSpectralMeasure φ m B = phaseHaar.withDensity (fun z => ENNReal.ofReal (q z))) :
    (∫ z, |p z-q z| ∂phaseHaar) ≤
      (‖(memLp_finitePacketVector hAl).toLp (finitePacketVector m A)‖+
       ‖(memLp_finitePacketVector hBl).toLp (finitePacketVector m B)‖)*
        physicalDist (finitePacketVector m A) (finitePacketVector m B) := by
  have ha := coefficient_memLp hAm hAl
  have hb := coefficient_memLp hBm hBl
  have he := coefficient_difference_norm hm hAm hBm hAl hBl
  calc
    _ ≤ ∫ x, |‖A x.1 x.2‖^2-‖B x.1 x.2‖^2| ∂coefficientVolume :=
      energy_density_difference_le (measurable_coefficientFrequency hφ m)
        (measurable_from_prod_countable_right hAm) (measurable_from_prod_countable_right hBm)
        ha hb hpm hqm hpi hqi hpn hqn hAp hBq
    _ ≤ _ := by
      have hh := density_norm_bound_memLp ha hb
      rw [coefficient_norm_eq_physical hm hAm hAl,coefficient_norm_eq_physical hm hBm hBl,he] at hh
      exact hh

end
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeTorus

lemma gather_vector {ι : Type*} [Fintype ι] (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (J : Finset ℤ) (hJ : ∀ i, m i ∈ J) :
    finitePacketVector (fun k : ↥J => k.val)
      (fun k x => ∑ i, if m i=k.val then A i x else 0) = finitePacketVector m A := by
  classical
  funext x
  simp only [finitePacketVector,packet,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let k : ↥J := ⟨m i,hJ i⟩
  rw [Finset.sum_eq_single k]
  · simp [k]
  · intro l _ hli
    have hn : m i ≠ l.val := fun h => hli (Subtype.ext h.symm)
    simp [hn]
  · simp

namespace PassagePackets
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma marginalDensity_sum_spectrum (F : PassagePackets ι) :
    (∑ i, packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i)) =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (∑ i, F.marginalDensity i z)) := by
  simp_rw [F.marginalDensity_spectral]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => F.marginalDensity_nonneg i _)]
  ext s hs
  rw [Measure.finsetSum_apply,withDensity_apply _ hs]
  simp_rw [withDensity_apply _ hs]
  rw [lintegral_finsetSum]
  intro i _
  exact (F.marginalDensity_measurable i).ennreal_ofReal

/-- L1 spectral density distance for DIFFERENT finite lists. Repeated modes
are allowed only with actual disjoint coefficient supports. -/
theorem marginalDensity_distance (F : PassagePackets ι) (G : PassagePackets κ)
    (hV : G.V=F.V)
    (hF : ∀ x i j, i ≠ j → F.m i=F.m j → F.A i x=0 ∨ F.A j x=0)
    (hG : ∀ x i j, i ≠ j → G.m i=G.m j → G.A i x=0 ∨ G.A j x=0) :
    (∫ z, |(∑ i, F.marginalDensity i z)-(∑ j, G.marginalDensity j z)| ∂phaseHaar) ≤
      (physicalDist (finitePacketVector F.m F.A) 0+physicalDist (finitePacketVector G.m G.A) 0)*
        physicalDist (finitePacketVector F.m F.A) (finitePacketVector G.m G.A) := by
  classical
  let J := Finset.univ.image F.m ∪ Finset.univ.image G.m
  have hJF i : F.m i ∈ J := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hJG j : G.m j ∈ J := Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  let A : ↥J → UnitAddCircle × UnitAddCircle → ℂ := fun k x => ∑ i, if F.m i=k.val then F.A i x else 0
  let B : ↥J → UnitAddCircle × UnitAddCircle → ℂ := fun k x => ∑ i, if G.m i=k.val then G.A i x else 0
  have hAc k : Continuous (A k) := continuous_finsetSum _ (fun i _ => by
    by_cases hi : F.m i=k.val <;> simp only [hi,ite_true,ite_false]
    · exact F.continuous_amplitude i
    · exact continuous_const)
  have hBc k : Continuous (B k) := continuous_finsetSum _ (fun i _ => by
    by_cases hi : G.m i=k.val <;> simp only [hi,ite_true,ite_false]
    · exact G.continuous_amplitude i
    · exact continuous_const)
  have hAl k : MemLp (A k) 2 slowVolume := (hAc k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hBl k : MemLp (B k) 2 slowVolume := (hBc k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let φ : UnitAddCircle → UnitAddCircle := fun u => (F.periodic.lift u:UnitAddCircle)
  have hφ : Measurable φ := AddCircle.measurable_mk'.comp F.speed_continuous.measurable
  have hφG : (fun u => (G.periodic.lift u:UnitAddCircle))=φ := by
    funext x
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective x
    exact congrArg (fun t : ℝ => (t:UnitAddCircle)) (congrFun hV x)
  have hp : finitePacketSpectralMeasure φ (fun k : ↥J => k.val) A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (∑ i, F.marginalDensity i z)) := by
    rw [finitePacketSpectralMeasure_eq_sum hφ _ (fun k => (hAc k).measurable)]
    exact (gather_spectrum F.m (fun i => (F.continuous_amplitude i).measurable) J hJF hφ hF).trans
      F.marginalDensity_sum_spectrum
  have hq : finitePacketSpectralMeasure φ (fun k : ↥J => k.val) B =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (∑ i, G.marginalDensity i z)) := by
    rw [finitePacketSpectralMeasure_eq_sum hφ _ (fun k => (hBc k).measurable)]
    refine (gather_spectrum G.m (fun i => (G.continuous_amplitude i).measurable) J hJG hφ hG).trans ?_
    rw [← hφG]
    exact G.marginalDensity_sum_spectrum
  have he := finitePacket_density_distance hφ Subtype.val_injective
    (fun k => (hAc k).measurable) (fun k => (hBc k).measurable) hAl hBl
    (Finset.measurable_sum _ (fun i _ => F.marginalDensity_measurable i))
    (Finset.measurable_sum _ (fun i _ => G.marginalDensity_measurable i))
    (integrable_finsetSum _ (fun i _ => F.marginalDensity_integrable i))
    (integrable_finsetSum _ (fun i _ => G.marginalDensity_integrable i))
    (fun z => Finset.sum_nonneg (fun i _ => F.marginalDensity_nonneg i z))
    (fun z => Finset.sum_nonneg (fun i _ => G.marginalDensity_nonneg i z)) hp hq
  have ha := gather_vector F.m F.A J hJF
  have hb := gather_vector G.m G.A J hJG
  have hnA : ‖(memLp_finitePacketVector hAl).toLp (finitePacketVector (fun k : ↥J => k.val) A)‖ =
      physicalDist (finitePacketVector (fun k : ↥J => k.val) A) 0 := by
    rw [physicalDist_eq_norm (memLp_finitePacketVector hAl) MemLp.zero]
    simp
  have hnB : ‖(memLp_finitePacketVector hBl).toLp (finitePacketVector (fun k : ↥J => k.val) B)‖ =
      physicalDist (finitePacketVector (fun k : ↥J => k.val) B) 0 := by
    rw [physicalDist_eq_norm (memLp_finitePacketVector hBl) MemLp.zero]
    simp
  rw [hnA,hnB,ha,hb] at he
  exact he
end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Function
open scoped BigOperators
namespace ThreeTorus

lemma sum_reflected_indices {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (m : ι → ℤ) (hm : ∀ i, m i ≠ 0) (τ : ι → ι) (hτ : Involutive τ)
    (hr : ∀ i, m (τ i) = -m i) (f : ι → M) :
    ∑ i, f i = (∑ i : {i : ι // 0 < m i}, f i.val)+(∑ i : {i : ι // 0 < m i}, f (τ i.val)) := by
  classical
  rw [← (reflectedIndexEquiv m hm τ hτ hr).sum_comp f,Fintype.sum_sum_type]
  rfl

end ThreeTorus
end
end

section

noncomputable section
open Function Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus
variable {ι : Type*} [Fintype ι]

lemma reflectedVector_eq {m : ι → ℤ} (hm : ∀ i, m i ≠ 0)
    {τ : ι → ι} (hτ : Involutive τ) (hr : ∀ i, m (τ i) = -m i)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hAr : ∀ i p, A (τ i) p=conj (A i p)) :
    finitePacketVector m A = reflectedVector m τ (fun i => A i.val) := by
  funext x
  rw [finitePacketVector,sum_reflected_indices m hm τ hτ hr]
  unfold reflectedVector
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact funext (hAr i.val)

lemma memLp_conj {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : MemLp (fun x => conj (f x)) 2 μ := hf.star

lemma eLpNorm_conj {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℂ) :
    eLpNorm (fun x => conj (f x)) 2 μ = eLpNorm f 2 μ :=
  eLpNorm_star

/-- A single positive-half coefficient approximation controls the entire
real physical vector; the negative half is its exact conjugate copy. -/
lemma physicalDist_reflectedVector {m : ι → ℤ} (τ : ι → ι)
    {A B : PositiveIndex m → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (hB : ∀ i, MemLp (B i) 2 slowVolume)
    {ε : ℝ} (hε : 0 < ε)
    (he : ∀ i, eLpNorm (fun p => A i p-B i p) 2 slowVolume <
      ENNReal.ofReal ((ε/2)/(Fintype.card (PositiveIndex m)+1))) :
    physicalDist (reflectedVector m τ A) (reflectedVector m τ B) < ε := by
  have he2 : 0 < ε/2 := by positivity
  have hp := physicalDist_small_sum (m := fun i : PositiveIndex m => m i.val) hA hB he2 he
  have hn := physicalDist_small_sum (m := fun i : PositiveIndex m => m (τ i.val))
    (fun i => memLp_conj (hA i)) (fun i => memLp_conj (hB i)) he2 (fun i => by
      simpa only [← map_sub,eLpNorm_conj] using he i)
  have ht := physicalDist_add_le
    (memLp_finitePacketVector (m := fun i : PositiveIndex m => m i.val) hA)
    (memLp_finitePacketVector (m := fun i : PositiveIndex m => m i.val) hB)
    (memLp_finitePacketVector (m := fun i : PositiveIndex m => m (τ i.val)) (fun i => memLp_conj (hA i)))
    (memLp_finitePacketVector (m := fun i : PositiveIndex m => m (τ i.val)) (fun i => memLp_conj (hB i)))
  exact ht.trans_lt (by linarith)

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

variable {ι : Type} [Fintype ι] (F : PassagePackets ι)
variable (J : PositiveIndex F.m → Type)

lemma ratioTag_reflect (b : ∀ i, J i → ℂ) (i : RatioIndex F J) :
    ratioTag F J b i.swap = conj (ratioTag F J b i) := by
  have _ := (inferInstance : Fintype ι)
  cases i <;> simp only [ratioTag,Sum.swap_inl,Sum.swap_inr,Sum.elim_inl,Sum.elim_inr,starRingEnd_self_apply]

variable {F J}

lemma clipped_reflection {τ : ι → ι} (hr : F.Reflection τ)
    {χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ k, CylinderSmooth (ratioCut F J χ k))
    (hc : ∀ k, HasCompactSupport (ratioCut F J χ k))
    (hs : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ) :
    (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).Reflection Sum.swap := by
  have _ := (inferInstance : Fintype ι)
  constructor
  · intro i
    cases i with
    | inl p => exact hr.index p.1.val
    | inr p => change F.m p.1.val = -F.m (τ p.1.val); rw [hr.index,neg_neg]
  · intro i p
    cases i <;> simp only [PassagePackets.clipped,ratioRoot,ratioCut,Sum.swap_inl,
      Sum.swap_inr,Sum.elim_inl,Sum.elim_inr,hr.amplitude,map_mul,Complex.conj_ofReal,starRingEnd_self_apply]
  · intro i a x
    cases i <;> simp only [PassagePackets.clipped,ratioRoot,ratioCut,Sum.swap_inl,
      Sum.swap_inr,Sum.elim_inl,Sum.elim_inr,hr.lift,map_mul,Complex.conj_ofReal,starRingEnd_self_apply]

lemma clipped_equal_mode_disjoint (hi : Injective F.m) {τ : ι → ι} (hr : F.Reflection τ)
    {χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ k, CylinderSmooth (ratioCut F J χ k))
    (hc : ∀ k, HasCompactSupport (ratioCut F J χ k))
    (hs : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ)
    (hd : ∀ i, Pairwise (fun j k => Disjoint (tsupport (χ i j)) (tsupport (χ i k)))) :
    ∀ i j, i ≠ j →
      (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m i =
      (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m j →
      Disjoint ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).cylinderCore i)
        ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).cylinderCore j) := by
  have _ := (inferInstance : Fintype ι)
  intro i j hij he
  apply Disjoint.mono (F.clipped_core_subset _ _ hχ hc hs i)
    (F.clipped_core_subset _ _ hχ hc hs j)
  rcases i with ⟨i,r⟩|⟨i,r⟩ <;> rcases j with ⟨j,s⟩|⟨j,s⟩
  · change F.m i.val=F.m j.val at he
    have hei : i=j := Subtype.ext (hi he)
    subst j
    exact hd i (by intro h; change r=s at h; subst s; exact hij rfl)
  · change F.m i.val=F.m (τ j.val) at he
    rw [hr.index] at he
    have h1 := i.property; have h2 := j.property
    omega
  · change F.m (τ i.val)=F.m j.val at he
    rw [hr.index] at he
    have h1 := i.property; have h2 := j.property
    omega
  · change F.m (τ i.val)=F.m (τ j.val) at he
    rw [hr.index,hr.index,neg_inj] at he
    have hei : i=j := Subtype.ext (hi he)
    subst j
    exact hd i (by intro h; change r=s at h; subst s; exact hij rfl)

variable [∀ i, Fintype (J i)]

lemma tagged_clipped_vector {τ : ι → ι} (hr : F.Reflection τ)
    {χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ k, CylinderSmooth (ratioCut F J χ k))
    (hc : ∀ k, HasCompactSupport (ratioCut F J χ k))
    (hs : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ)
    (b : ∀ i, J i → ℂ) :
    (fun x => ∑ k, ratioTag F J b k *
      packet ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m k)
        ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).A k) x) =
    reflectedVector F.m τ (fun i p => ∑ j, b i j*((cylinderTorusCutoff (χ i j) p:ℂ)*F.A i.val p)) := by
  classical
  funext x
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,ratioTag,ratioRoot,ratioCut,
    PassagePackets.clipped,Sum.elim_inl,Sum.elim_inr,reflectedVector,packet,hr.amplitude,
    map_sum,map_mul,Complex.conj_ofReal,Finset.sum_mul,mul_assoc]

lemma untagged_clipped_vector {τ : ι → ι} (hr : F.Reflection τ)
    {χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ k, CylinderSmooth (ratioCut F J χ k))
    (hc : ∀ k, HasCompactSupport (ratioCut F J χ k))
    (hs : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ) :
    finitePacketVector (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m
      (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).A =
    reflectedVector F.m τ (fun i p => ∑ j, (cylinderTorusCutoff (χ i j) p:ℂ)*F.A i.val p) := by
  have hh := tagged_clipped_vector hr hχ hc hs (fun _ _ => 1)
  have h1 (k : RatioIndex F J) : ratioTag F J (fun _ _ => 1) k = 1 := by
    cases k <;> simp only [ratioTag,Sum.elim_inl,Sum.elim_inr,map_one]
  change (fun x => ∑ k, packet ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m k)
    ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).A k) x) = _
  simpa only [h1,one_mul] using hh

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Preparation
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real perturbation, smooth cylinder approximation, tensor preparation, real packet families, and two neutral separations. -/

section

/-!
Concrete preparation with null zero sets for the packet ratios.
The perturbation parameter is REAL and works simultaneously for all packets.
No stage, spectral conclusion, or transport theorem is assumed here.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace ThreeTorus

/-- Apart from a Lebesgue null set of real parameters, a real perturbation
has no zero where the target coefficient is nonzero, up to the original measure.
This is the Fubini step in the manuscript, also for complex coefficients. -/
lemma real_perturbation_nonzero_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {F H : X → ℂ}
    (hF : Measurable F) (hH : Measurable H) :
    ∀ᵐ t : ℝ, ∀ᵐ x ∂μ, F x + (t : ℂ) * H x = 0 → H x = 0 := by
  have hm : MeasurableSet
      {p : X × ℝ | F p.1 + (p.2 : ℂ) * H p.1 = 0 → H p.1 = 0} := by
    apply MeasurableSet.imp
    · exact measurableSet_eq_fun ((hF.comp measurable_fst).add
        ((Complex.measurable_ofReal.comp measurable_snd).mul (hH.comp measurable_fst)))
        measurable_const
    · exact measurableSet_eq_fun (hH.comp measurable_fst) measurable_const
  apply (Measure.ae_ae_comm hm).1
  filter_upwards [] with x
  by_cases hx : H x = 0
  · exact Filter.Eventually.of_forall (fun _ _ => hx)
  · have hc : {t : ℝ | F x + (t : ℂ) * H x = 0}.Subsingleton := by
      intro t ht u hu
      apply Complex.ofReal_injective
      exact mul_right_cancel₀ hx (add_left_cancel (ht.trans hu.symm))
    have hz := hc.countable.measure_zero volume
    have hne : ∀ᵐ t : ℝ, F x + (t : ℂ) * H x ≠ 0 := by
      simpa only [ae_iff, not_not] using hz
    filter_upwards [hne] with t ht
    exact fun h => (ht h).elim

/-- The common real parameter avoids all the finite/countable list's bad fibers. -/
lemma real_perturbation_family_ae {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) [SFinite μ] {F H : ι → X → ℂ}
    (hF : ∀ i, Measurable (F i)) (hH : ∀ i, Measurable (H i)) :
    ∀ᵐ t : ℝ, ∀ i, ∀ᵐ x ∂μ, F i x + (t : ℂ) * H i x = 0 → H i x = 0 := by
  rw [ae_all_iff]
  intro i
  exact real_perturbation_nonzero_ae μ (hF i) (hH i)

/-- The parameter may be chosen positive and smaller than any prescribed tolerance,
simultaneously for a countable family of coefficient pairs. -/
lemma exists_small_real_perturbation {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) [SFinite μ] {F H : ι → X → ℂ}
    (hF : ∀ i, Measurable (F i)) (hH : ∀ i, Measurable (H i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧
      ∀ i, ∀ᵐ x ∂μ, F i x + (t : ℂ) * H i x = 0 → H i x = 0 := by
  have hvol : volume (Ioo (0 : ℝ) ε) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨t, ht, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae (real_perturbation_family_ae μ hF hH))
  exact ⟨t, ht.1, ht.2, hgood⟩

lemma ratio_mul_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F H : X → ℂ}
    (hzero : ∀ᵐ x ∂μ, F x = 0 → H x = 0) :
    (fun x => H x / F x * F x) =ᵐ[μ] H := by
  filter_upwards [hzero] with x hx
  by_cases h : F x = 0
  · simp [h, hx h]
  · exact div_mul_cancel₀ _ h

/-- Ratios are genuinely square integrable for the weighted measure; no
nonvanishing hypothesis on the source coefficient is imposed everywhere. -/
lemma ratio_memLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F H : X → ℂ} (hF : Measurable F) (hH : Measurable H)
    (hH₂ : MemLp H 2 μ) (hzero : ∀ᵐ x ∂μ, F x = 0 → H x = 0) :
    MemLp (fun x => H x / F x) 2 (coefficientMeasure μ F) := by
  apply (memLp_two_iff_integrable_sq_norm (hH.div hF).aestronglyMeasurable).2
  change Integrable (fun x => ‖H x / F x‖ ^ 2)
    (μ.withDensity (fun x => ((‖F x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)))
  rw [integrable_withDensity_iff_integrable_smul (hF.nnnorm.pow_const 2)]
  apply hH₂.integrable_norm_pow (by norm_num) |>.congr
  filter_upwards [ratio_mul_ae hzero] with x hx
  have he := congrArg (fun z : ℂ => ‖z‖ ^ 2) hx
  simpa only [norm_mul, mul_pow, NNReal.smul_def, NNReal.coe_pow,
    coe_nnnorm, smul_eq_mul, mul_comm] using he.symm

end ThreeTorus
end
end

section

/-! Measurable ratio localization by actual disjoint smooth cylinder cutoffs.
Compact inner regularity replaces a particular rectangular grid; the retained
pieces are still finitely many disjoint compact subsets of the good cylinder. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
namespace ThreeTorus

lemma simple_compact_capture (ν : Measure (ℝ × UnitAddCircle)) [IsFiniteMeasure ν]
    [ν.InnerRegularCompactLTTop] (s : SimpleFunc (ℝ × UnitAddCircle) ℂ)
    {U : Set (ℝ × UnitAddCircle)} (hU : IsOpen U) (hν : ν Uᶜ = 0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : ↥s.range → Set (ℝ × UnitAddCircle),
      (∀ i, IsCompact (K i) ∧ K i ⊆ U ∩ s ⁻¹' {i.val}) ∧
      Pairwise (Disjoint on K) ∧ ν (⋃ i, K i)ᶜ < ε := by
  classical
  let I := ↥s.range
  obtain ⟨δ,hδ,hδε⟩ := ENNReal.exists_pos_mul_lt (a := (Fintype.card I : ℝ≥0∞))
    (by finiteness) hε
  have he (i : I) := (hU.measurableSet.inter (s.measurableSet_preimage {i.val})).exists_isCompact_sdiff_lt
    (μ := ν) (measure_ne_top _ _) hδ.ne'
  choose K hKU hK hdiff using he
  refine ⟨K,fun i => ⟨hK i,hKU i⟩,?_,?_⟩
  · intro i j hij
    change Disjoint (K i) (K j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    apply Subtype.ext
    exact (hKU i hxi).2.symm.trans (hKU j hxj).2
  · have hsub : (⋃ i, K i)ᶜ ⊆ Uᶜ ∪ ⋃ i : I, (U ∩ s ⁻¹' {i.val}) \ K i := by
      intro x hx
      by_cases hxU : x ∈ U
      · right
        let i : I := ⟨s x,s.mem_range_self x⟩
        exact mem_iUnion.mpr ⟨i,⟨⟨hxU,rfl⟩,fun h => hx (mem_iUnion.mpr ⟨i,h⟩)⟩⟩
      · exact Or.inl hxU
    calc
      ν (⋃ i, K i)ᶜ ≤ ν (Uᶜ ∪ ⋃ i : I, (U ∩ s ⁻¹' {i.val}) \ K i) := measure_mono hsub
      _ ≤ ν Uᶜ + ν (⋃ i : I, (U ∩ s ⁻¹' {i.val}) \ K i) := measure_union_le _ _
      _ = ν (⋃ i : I, (U ∩ s ⁻¹' {i.val}) \ K i) := by rw [hν,zero_add]
      _ ≤ ∑ i : I, ν ((U ∩ s ⁻¹' {i.val}) \ K i) := by
        simpa only [tsum_fintype] using measure_iUnion_le (fun i : I => (U ∩ s ⁻¹' {i.val}) \ K i)
      _ ≤ ∑ _i : I, δ := Finset.sum_le_sum (fun i _ => (hdiff i).le)
      _ = δ * (Fintype.card I : ℝ≥0∞) := by simp [mul_comm]
      _ < ε := hδε

lemma disjoint_cutoffs_value {ι : Type*} [Fintype ι]
    {K : ι → Set (ℝ × UnitAddCircle)} {χ : ι → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ i x, x ∈ K i → χ i x = 1)
    (hd : Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))))
    {i : ι} {x : ℝ × UnitAddCircle} (hx : x ∈ K i) :
    χ i x = 1 ∧ ∀ j, j ≠ i → χ j x = 0 := by
  refine ⟨hχ i x hx,fun j hji => ?_⟩
  by_contra hj
  have hi : x ∈ tsupport (χ i) := subset_tsupport _ (by change χ i x ≠ 0; rw [hχ i x hx]; exact one_ne_zero)
  exact Set.disjoint_left.1 (hd hji) (subset_tsupport _ hj) hi

/-- Smooth disjoint bump representation agrees with a prescribed simple
function off a set of arbitrarily small measure. It also recovers the
untagged constant one there. Zero simple values are retained as colors. -/
theorem simple_smooth_disjoint_capture (ν : Measure (ℝ × UnitAddCircle)) [IsFiniteMeasure ν]
    [ν.InnerRegularCompactLTTop] (s : SimpleFunc (ℝ × UnitAddCircle) ℂ)
    {U : Set (ℝ × UnitAddCircle)} (hU : IsOpen U) (hν : ν Uᶜ = 0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ χ : ↥s.range → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U ∧
        ∀ x, 0 ≤ χ i x ∧ χ i x ≤ 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      ∃ Z : Set (ℝ × UnitAddCircle), MeasurableSet Z ∧ ν Z < ε ∧
        ∀ x ∉ Z, (∑ i, χ i x) = 1 ∧ (∑ i, i.val * (χ i x:ℂ)) = s x := by
  classical
  obtain ⟨K,hK,hd,hεK⟩ := simple_compact_capture ν s hU hν hε
  obtain ⟨χ,hχ,hdχ⟩ := finite_disjoint_cylinder_cutoffs K (fun _ => U)
    (fun i => (hK i).1) (fun _ => hU) (fun i => (hK i).2.trans inter_subset_left) hd
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1,(hχ i).2.2.2.1⟩,
    hdχ,(⋃ i, K i)ᶜ,(isClosed_iUnion_of_finite (fun i => (hK i).1.isClosed)).measurableSet.compl,
    hεK,?_⟩
  intro x hx
  have hx' : x ∈ ⋃ i, K i := not_not.mp hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx'
  have hh := disjoint_cutoffs_value (fun r y hy => ((hχ r).2.2.2.2 y hy).self_of_nhds) hdχ hi
  have hs : s x = i.val := (hK i).2 hi |>.2
  constructor
  · rw [Finset.sum_eq_single i]
    · exact hh.1
    · intro j _ hj; exact hh.2 j hj
    · simp
  · rw [Finset.sum_eq_single i]
    · rw [hh.1,Complex.ofReal_one,mul_one,hs]
    · intro j _ hj; rw [hh.2 j hj,Complex.ofReal_zero,mul_zero]
    · simp

end ThreeTorus
end
end

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace ThreeTorus

/-- A bounded error supported on a sufficiently small set has small L² norm.
The bound is selected before the exceptional set/cutoffs are selected. -/
lemma exists_measure_bound_eLpNorm_lt {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure X) {B : ℝ} (hB : 0 ≤ B)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ (Z : Set X), MeasurableSet Z → μ Z < δ →
      ∀ f : X → E, AEStronglyMeasurable f μ →
        (∀ x, ‖f x‖ ≤ B) → (∀ x ∉ Z, f x = 0) → eLpNorm f 2 μ < ε := by
  obtain ⟨c,hc,hcε⟩ := ENNReal.exists_pos_mul_lt (a := ‖B‖ₑ) (by finiteness) hε
  refine ⟨c^2,by positivity,fun Z hZ hμ f hfm hf hz => ?_⟩
  have hmono : eLpNorm f 2 μ ≤ eLpNorm (Z.indicator (fun _ : X => B)) 2 μ := by
    apply eLpNorm_mono
    intro x
    by_cases hx : x ∈ Z
    · simpa [Set.indicator_of_mem hx,Real.norm_eq_abs,abs_of_nonneg hB] using hf x
    · simp [Set.indicator_of_notMem hx,hz x hx]
  have hr : (c^2) ^ (1/(2:ℝ)) = c := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    norm_num
  calc
    eLpNorm f 2 μ ≤ eLpNorm (Z.indicator (fun _ : X => B)) 2 μ := hmono
    _ = ‖B‖ₑ * μ Z ^ (1/(2:ℝ)) := by
      rw [eLpNorm_indicator_const₀ (c := B) hZ.nullMeasurableSet (by norm_num) (by norm_num)]
      norm_num
    _ ≤ ‖B‖ₑ * (c^2) ^ (1/(2:ℝ)) := mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hμ.le (by positivity))
    _ = c * ‖B‖ₑ := by rw [hr,mul_comm]
    _ < ε := hcε

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
namespace ThreeTorus

/-- Weighted simultaneous approximation of the untagged vector and its
measurable ratio. The finite constants are fixed before the interior trimming;
zero constants are not discarded. -/
theorem weighted_smooth_disjoint_approx (ν : Measure (ℝ × UnitAddCircle)) [IsFiniteMeasure ν]
    [ν.InnerRegularCompactLTTop] {R : ℝ × UnitAddCircle → ℂ} (hR : MemLp R 2 ν)
    {U : Set (ℝ × UnitAddCircle)} (hU : IsOpen U) (hν : ν Uᶜ = 0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : SimpleFunc (ℝ × UnitAddCircle) ℂ,
    ∃ χ : ↥s.range → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U ∧
        ∀ x, 0 ≤ χ i x ∧ χ i x ≤ 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      eLpNorm (fun x => (1:ℂ) - ∑ i, (χ i x:ℂ)) 2 ν < ε ∧
      eLpNorm (fun x => R x - ∑ i, i.val * (χ i x:ℂ)) 2 ν < ε := by
  classical
  have hε2 : ε / 2 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε,by norm_num⟩
  obtain ⟨s,hs,_⟩ := hR.exists_simpleFunc_eLpNorm_sub_lt (by norm_num) hε2
  let I := ↥s.range
  let B : ℝ := 1 + Fintype.card I + 2 * ∑ i : I, ‖i.val‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨δ,hδ,hsmall⟩ := exists_measure_bound_eLpNorm_lt (E := ℂ) ν hB hε2
  obtain ⟨χ,hχ,hd,Z,hZ,hZδ,heq⟩ := simple_smooth_disjoint_capture ν s hU hν hδ.ne'
  have hnχ (i : I) (x : ℝ × UnitAddCircle) : ‖(χ i x:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ((hχ i).2.2.2 x).1]
      using ((hχ i).2.2.2 x).2
  have hnχsum (x : ℝ × UnitAddCircle) : ‖∑ i : I, (χ i x:ℂ)‖ ≤ Fintype.card I := calc
    _ ≤ ∑ i : I, ‖(χ i x:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, (1:ℝ) := Finset.sum_le_sum (fun i _ => hnχ i x)
    _ = _ := by simp
  have hntagsum (x : ℝ × UnitAddCircle) : ‖∑ i : I, i.val * (χ i x:ℂ)‖ ≤ ∑ i : I, ‖i.val‖ := calc
    _ ≤ ∑ i : I, ‖i.val * (χ i x:ℂ)‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hnχ i x))
  have hns (x : ℝ × UnitAddCircle) : ‖s x‖ ≤ ∑ i : I, ‖i.val‖ := by
    let i : I := ⟨s x,s.mem_range_self x⟩
    exact Finset.single_le_sum (fun j _ => norm_nonneg j.val) (Finset.mem_univ i)
  have hu : eLpNorm (fun x => (1:ℂ) - ∑ i, (χ i x:ℂ)) 2 ν < ε/2 := by
    apply hsmall Z hZ hZδ
    · apply Continuous.aestronglyMeasurable
      exact continuous_const.sub (continuous_finsetSum _ (fun i _ =>
        Complex.continuous_ofReal.comp (hχ i).1.continuous))
    · intro x
      have hh := norm_sub_le (1:ℂ) (∑ i : I, (χ i x:ℂ))
      rw [norm_one] at hh
      change ‖(1:ℂ) - ∑ i : I, (χ i x:ℂ)‖ ≤ 1 + Fintype.card I + 2 * ∑ i : I, ‖i.val‖
      have hp : 0 ≤ ∑ i : I, ‖i.val‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      linarith [hnχsum x]
    · intro x hx
      rw [sub_eq_zero]
      have hh := congrArg (fun t : ℝ => (t:ℂ)) (heq x hx).1
      simpa using hh.symm
  have ht : eLpNorm (fun x => s x - ∑ i, i.val * (χ i x:ℂ)) 2 ν < ε/2 := by
    apply hsmall Z hZ hZδ
    · apply s.measurable.aestronglyMeasurable.sub
      apply Continuous.aestronglyMeasurable
      exact continuous_finsetSum _ (fun i _ =>
        continuous_const.mul (Complex.continuous_ofReal.comp (hχ i).1.continuous))
    · intro x
      have hh := norm_sub_le (s x) (∑ i : I, i.val * (χ i x:ℂ))
      have hc : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
      change ‖s x - ∑ i : I, i.val * (χ i x:ℂ)‖ ≤ 1 + Fintype.card I + 2 * ∑ i : I, ‖i.val‖
      linarith [hns x,hntagsum x]
    · intro x hx
      exact sub_eq_zero.mpr ((heq x hx).2.symm)
  refine ⟨s,χ,hχ,hd,hu.trans_le (by simpa only [ENNReal.add_halves] using (le_self_add : ε/2 ≤ ε/2+ε/2)),?_⟩
  calc
    eLpNorm (fun x => R x - ∑ i, i.val * (χ i x:ℂ)) 2 ν =
      eLpNorm ((R - ⇑s) + (fun x => s x - ∑ i, i.val * (χ i x:ℂ))) 2 ν := by
        congr 1; funext x; simp
    _ ≤ eLpNorm (R-⇑s) 2 ν + eLpNorm (fun x => s x - ∑ i, i.val * (χ i x:ℂ)) 2 ν :=
      eLpNorm_add_le (hR.1.sub s.measurable.aestronglyMeasurable) (s.measurable.aestronglyMeasurable.sub (Continuous.aestronglyMeasurable (continuous_finsetSum _ (fun i _ => continuous_const.mul (Complex.continuous_ofReal.comp (hχ i).1.continuous))))) (by norm_num)
    _ < ε/2 + ε/2 := ENNReal.add_lt_add hs ht
    _ = ε := ENNReal.add_halves ε

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
namespace ThreeTorus

lemma eLpNorm_coefficientMeasure {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F g : X → ℂ} (hF : Measurable F) (hg : Measurable g) :
    eLpNorm g 2 (coefficientMeasure μ F) = eLpNorm (fun x => g x * F x) 2 μ := by
  change eLpNorm g 2 (coefficientMeasure μ F) = eLpNorm (g * F) 2 μ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  change (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂μ.withDensity (fun x => (‖F x‖₊ ^ 2:ℝ≥0∞))) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hF.nnnorm.coe_nnreal_ennreal.pow_const 2)
    (hg.enorm.pow_const _)]
  apply lintegral_congr
  intro x
  simp [Pi.mul_apply,mul_pow,enorm_eq_nnnorm,mul_comm]

lemma finite_coefficientMeasure {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F : X → ℂ} (hF : MemLp F 2 μ) : IsFiniteMeasure (coefficientMeasure μ F) := by
  apply isFiniteMeasure_withDensity
  have hf := (hasFiniteIntegral_iff_norm _).1
    (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).hasFiniteIntegral
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm,ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm,enorm_eq_nnnorm,ENNReal.coe_pow] using hf.ne

/-- The literal coefficient errors after constant-ratio trimming, not just
errors of the ratios in an auxiliary weighted space. -/
theorem coefficient_smooth_disjoint_approx (μ : Measure (ℝ × UnitAddCircle))
    {F H : ℝ × UnitAddCircle → ℂ} (hFm : Measurable F) (hHm : Measurable H)
    (hF : MemLp F 2 μ) (hH : MemLp H 2 μ)
    (hzero : ∀ᵐ x ∂μ, F x = 0 → H x = 0)
    {U : Set (ℝ × UnitAddCircle)} (hU : IsOpen U)
    (hsupp : ∀ᵐ x ∂μ, x ∉ U → F x = 0) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : SimpleFunc (ℝ × UnitAddCircle) ℂ,
    ∃ χ : ↥s.range → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U ∧
        ∀ x, 0 ≤ χ i x ∧ χ i x ≤ 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      eLpNorm (fun x => F x - ∑ i, (χ i x:ℂ)*F x) 2 μ < ε ∧
      eLpNorm (fun x => H x - ∑ i, i.val * ((χ i x:ℂ)*F x)) 2 μ < ε := by
  let := finite_coefficientMeasure hF
  have hν : coefficientMeasure μ F Uᶜ = 0 := by
    rw [coefficientMeasure,withDensity_apply _ hU.measurableSet.compl]
    calc
      _ = ∫⁻ x, (0 : ℝ≥0∞) ∂μ.restrict Uᶜ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hsupp,ae_restrict_mem hU.measurableSet.compl] with x hx hxu
        simp [hx hxu]
      _ = 0 := lintegral_zero
  have hR := ratio_memLp hFm hHm hH hzero
  obtain ⟨s,χ,hχ,hd,hu,ht⟩ := weighted_smooth_disjoint_approx (coefficientMeasure μ F) hR hU hν hε
  have hc : ∀ i, Measurable (fun x => (χ i x:ℂ)) := fun i =>
    Complex.measurable_ofReal.comp (hχ i).1.continuous.measurable
  have hsum : Measurable (fun x => ∑ i, (χ i x:ℂ)) := Finset.measurable_sum _ (fun i _ => hc i)
  have htsum : Measurable (fun x => ∑ i, i.val * (χ i x:ℂ)) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (hc i))
  rw [eLpNorm_coefficientMeasure (g := fun x => (1 : ℂ) - ∑ i, (χ i x:ℂ)) hFm (measurable_const.sub hsum)] at hu
  rw [eLpNorm_coefficientMeasure (g := fun x => H x / F x - ∑ i, i.val * (χ i x:ℂ)) hFm ((hHm.div hFm).sub htsum)] at ht
  refine ⟨s,χ,hχ,hd,?_,?_⟩
  · convert hu using 1
    all_goals try with_reducible_and_instances rfl
    congr 1; funext x
    simp only [sub_mul,one_mul,Finset.sum_mul]
  · rw [← eLpNorm_congr_ae (show (fun x => (H x/F x - ∑ i, i.val*(χ i x:ℂ))*F x) =ᵐ[μ]
      (fun x => H x - ∑ i, i.val*((χ i x:ℂ)*F x)) from ?_)]
    · exact ht
    · filter_upwards [ratio_mul_ae hzero] with x hx
      simp only [sub_mul,hx,Finset.sum_mul,mul_assoc]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurePreserving_cylinderToSlow (o : ℝ) :
    MeasurePreserving cylinderToSlow (cylinderVolume o) slowVolume := by
  have h : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) phaseHaar := by
    simpa [phaseHaar,AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  exact h.prod (MeasurePreserving.id phaseHaar)

lemma measurable_slowToCylinder (o : ℝ) : Measurable (slowToCylinder o) :=
  ((measurable_circleRep o).comp measurable_fst).prodMk measurable_snd

lemma cylinderToSlow_slowToCylinder (o : ℝ) (p : UnitAddCircle × UnitAddCircle) :
    cylinderToSlow (slowToCylinder o p) = p := by
  simp [cylinderToSlow,slowToCylinder,coe_circleRep]

lemma slowToCylinder_cylinderToSlow (o : ℝ) :
    (slowToCylinder o ∘ cylinderToSlow) =ᵐ[cylinderVolume o] id := by
  have hh : ∀ᵐ x ∂volume.restrict (Ioc o (o+1)), x ∈ Ioc o (o+1) :=
    ae_restrict_mem measurableSet_Ioc
  have hm : ∀ᵐ p ∂cylinderVolume o, p.1 ∈ Ioc o (o+1) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).2
      (hh.mono (fun x hx => Filter.Eventually.of_forall (fun _y : UnitAddCircle => hx)))
  filter_upwards [hm] with x hx
  simp only [Function.comp_apply,cylinderToSlow,slowToCylinder,id_eq]
  congr 1
  exact circleRep_coe hx

lemma measurePreserving_slowToCylinder (o : ℝ) :
    MeasurePreserving (slowToCylinder o) slowVolume (cylinderVolume o) := by
  refine ⟨measurable_slowToCylinder o,?_⟩
  rw [← (measurePreserving_cylinderToSlow o).map_eq,
    Measure.map_map (measurable_slowToCylinder o) (measurePreserving_cylinderToSlow o).measurable,
    Measure.map_congr (slowToCylinder_cylinderToSlow o),Measure.map_id]

instance instIsProbabilityMeasureProdRealUnitAddCircleCylinderVolume (o : ℝ) : IsProbabilityMeasure (cylinderVolume o) := by
  rw [← (measurePreserving_slowToCylinder o).map_eq]
  exact Measure.isProbabilityMeasure_map (measurable_slowToCylinder o).aemeasurable

lemma eLpNorm_slow_pull (o : ℝ) (f : ℝ × UnitAddCircle → ℂ)
    (hf : AEStronglyMeasurable f (cylinderVolume o)) :
    eLpNorm (f ∘ slowToCylinder o) 2 slowVolume = eLpNorm f 2 (cylinderVolume o) :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_slowToCylinder o)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

attribute [local instance] OAI.ThreeTorus.instMeasureSpaceUnitAddCircle_solutions_2
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_2 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

lemma multiTrigPolynomial_apply (c : (d → ℤ) →₀ ℂ) (x : UnitAddTorus d) :
    multiTrigPolynomial c x = ∑ k ∈ c.support, c k * UnitAddTorus.mFourier k x := by
  simp [multiTrigPolynomial,Finsupp.sum]

lemma mFourier_smooth_lift (k : d → ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : d → ℝ => UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle))) := by
  change ContDiff ℝ _ (fun x : d → ℝ => ∏ i, fourier (k i) (x i : UnitAddCircle))
  apply contDiff_prod
  intro i _
  simp only [fourier_coe_apply,Complex.ofReal_one,div_one]
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i))).cexp

lemma multiTrigPolynomial_smooth_lift (c : (d → ℤ) →₀ ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : d → ℝ => multiTrigPolynomial c (fun i => (x i : UnitAddCircle))) := by
  simp_rw [multiTrigPolynomial_apply]
  exact ContDiff.sum (fun k _ => contDiff_const.mul (mFourier_smooth_lift k))

/-- The exact existing multivariate Fourier basis supplies smooth finite
polynomials in the FULL torus space, not just a cyclic subspace. -/
theorem exists_L2_multiTrig {f : UnitAddTorus d → ℂ} (hf : MemLp f 2 volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : (d → ℤ) →₀ ℂ,
      eLpNorm (fun x => f x-multiTrigPolynomial c x) 2 volume < ENNReal.ofReal ε := by
  classical
  have hd : hf.toLp f ∈ ((Submodule.span ℂ (range (UnitAddTorus.mFourierLp (d := d) 2))).topologicalClosure : Set (Lp ℂ 2 (volume : Measure (UnitAddTorus d)))) := by
    rw [UnitAddTorus.span_mFourierLp_closure_eq_top (by norm_num : (2:ℝ≥0∞) ≠ ∞)]
    trivial
  change hf.toLp f ∈ closure (Submodule.span ℂ (range (UnitAddTorus.mFourierLp (d := d) 2)) : Set (Lp ℂ 2 (volume : Measure (UnitAddTorus d)))) at hd
  obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.1 hd ε hε
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hg
  have he : ContinuousMap.toLp (E := ℂ) 2 volume ℂ (multiTrigPolynomial c) = g := by
    rw [← hc,multiTrigPolynomial]
    simp [Finsupp.sum]
  have hae : (fun x => f x-multiTrigPolynomial c x) =ᵐ[volume] (fun x => (hf.toLp f-g) x) := by
    filter_upwards [hf.coeFn_toLp,ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (multiTrigPolynomial c),
      Lp.coeFn_sub (hf.toLp f) g] with x hx hy hz
    rw [he] at hy
    simp only [hz,Pi.sub_apply,hx,hy]
  refine ⟨c,?_⟩
  rw [eLpNorm_congr_ae hae,← Lp.enorm_def,← ofReal_norm]
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  simpa only [dist_eq_norm] using hfg

lemma exists_uniform_multiTrig {f : UnitAddTorus d → ℂ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : (d → ℤ) →₀ ℂ, ∀ x, ‖f x-multiTrigPolynomial c x‖ < ε := by
  let F : C(UnitAddTorus d,ℂ) := ⟨f,hf⟩
  have hd : F ∈ (Submodule.span ℂ (range (UnitAddTorus.mFourier (d := d)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    trivial
  change F ∈ closure (Submodule.span ℂ (range (UnitAddTorus.mFourier (d := d))) : Set C(UnitAddTorus d,ℂ)) at hd
  obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.1 hd ε hε
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hg
  refine ⟨c,?_⟩
  intro x
  have he : multiTrigPolynomial c = g := hc
  rw [he]
  exact (ContinuousMap.norm_coe_le_norm (F-g) x).trans_lt (by simpa only [dist_eq_norm] using hfg)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

lemma continuous_slowPair_symm : Continuous slowPair.symm := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

attribute [local instance] OAI.ThreeTorus.instMeasureSpaceUnitAddCircle_solutions_3
lemma measurePreserving_slowPair : MeasurePreserving slowPair volume slowVolume :=
  measurePreserving_piFinTwo (fun _ : Fin 2 => phaseHaar)

/-- Arbitrary actual L² coefficients admit smooth periodic approximation in
both slow variables. Density is in the full two-torus L² space. -/
lemma exists_smooth_slow_approx {f : UnitAddCircle × UnitAddCircle → ℂ}
    (hf : MemLp f 2 slowVolume) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : UnitAddCircle × UnitAddCircle → ℂ, Continuous g ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => g (p.1,p.2)) ∧
      eLpNorm (fun p => f p-g p) 2 slowVolume < ENNReal.ofReal ε := by
  obtain ⟨c,hc⟩ := exists_L2_multiTrig (hf.comp_measurePreserving measurePreserving_slowPair) hε
  let g : UnitAddCircle × UnitAddCircle → ℂ := multiTrigPolynomial c ∘ slowPair.symm
  have hgc : Continuous g := (multiTrigPolynomial c).continuous.comp continuous_slowPair_symm
  refine ⟨g,hgc,?_,?_⟩
  · have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => ![p.1,p.2]) := by
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact contDiff_fst
      · exact contDiff_snd
    have he : (fun p : ℝ × ℝ => g (p.1,p.2)) =
        (fun x : Fin 2 → ℝ => multiTrigPolynomial c (fun i => (x i : UnitAddCircle))) ∘
          (fun p : ℝ × ℝ => ![p.1,p.2]) := by
      funext p
      change multiTrigPolynomial c (slowPair.symm ((p.1:UnitAddCircle),(p.2:UnitAddCircle))) = _
      apply congrArg (multiTrigPolynomial c)
      ext i
      fin_cases i <;> rfl
    rw [he]
    exact (multiTrigPolynomial_smooth_lift c).comp hd
  · have he : (fun p => f p-g p) ∘ slowPair =
        fun x => (f ∘ slowPair) x-multiTrigPolynomial c x := by
      funext x
      simp [g,Function.comp_def]
    have heq := eLpNorm_comp_measurePreserving
      (g := fun p => f p-g p) (p := 2)
      (hf.aestronglyMeasurable.sub hgc.aestronglyMeasurable) measurePreserving_slowPair
    rw [he] at heq
    exact heq ▸ hc

lemma circleRep_mem (o : ℝ) (u : UnitAddCircle) : circleRep o u ∈ Ioc o (o+1) :=
  ((AddCircle.measurableEquivIoc 1 o) u).property

lemma cylinderTorusCutoff_rep {χ : ℝ × UnitAddCircle → ℝ} {o : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) (p : UnitAddCircle × UnitAddCircle) :
    cylinderTorusCutoff χ p = χ (circleRep o p.1,p.2) := by
  have hh := cylinderTorusCutoff_eq hs (circleRep_mem o p.1) p.2
  simpa only [coe_circleRep] using hh

lemma cylinderTorusCutoff_bounds {χ : ℝ × UnitAddCircle → ℝ} {o : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) (hb : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1)
    (p : UnitAddCircle × UnitAddCircle) :
    0 ≤ cylinderTorusCutoff χ p ∧ cylinderTorusCutoff χ p ≤ 1 := by
  rw [cylinderTorusCutoff_rep hs p]
  exact hb _

lemma cylinderTorusCutoff_fixes {χ : ℝ × UnitAddCircle → ℝ} {o l u : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) (hol : o < l) (huo : u < o+1)
    (hχ : ∀ p ∈ Icc l u ×ˢ univ, χ p = 1)
    {f : UnitAddCircle × UnitAddCircle → ℂ}
    (hf : support f ⊆ ((fun x : ℝ => (x:UnitAddCircle)) '' Icc l u) ×ˢ univ) (p) :
    (cylinderTorusCutoff χ p:ℂ)*f p = f p := by
  by_cases hz : f p = 0
  · simp [hz]
  obtain ⟨x,hx,hxp⟩ := (hf hz).1
  have hxI : x ∈ Ioc o (o+1) := ⟨hol.trans_le hx.1,hx.2.trans huo.le⟩
  have he : p = ((x:UnitAddCircle),p.2) := Prod.ext hxp.symm rfl
  rw [he,cylinderTorusCutoff_eq hs hxI p.2,hχ _ ⟨hx,mem_univ _⟩]
  simp

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma cylinder_mem_open_ae (o : ℝ) :
    ∀ᵐ p ∂cylinderVolume o, p ∈ Ioo o (o+1) ×ˢ (univ : Set UnitAddCircle) := by
  have hh : ∀ᵐ x ∂volume.restrict (Ioc o (o+1)), x ∈ Ioo o (o+1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (o+1))] with x hx hn
    exact ⟨hx.1,lt_of_le_of_ne hx.2 hn⟩
  apply (Measure.ae_prod_iff_ae_ae (isOpen_Ioo.prod isOpen_univ).measurableSet).2
  filter_upwards [hh] with x hx
  exact .of_forall fun _ => ⟨hx,mem_univ _⟩

/-- Actual torus coefficient version of weighted ratio approximation. The
cutoffs are compact on the cylinder, but both errors are in normalized torus
L². No mass is dropped where the finite tag is zero. -/
theorem torus_coefficient_smooth_disjoint_approx (o : ℝ)
    {F H : UnitAddCircle × UnitAddCircle → ℂ} (hFm : Measurable F) (hHm : Measurable H)
    (hF : MemLp F 2 slowVolume) (hH : MemLp H 2 slowVolume)
    (hzero : ∀ᵐ x ∂slowVolume, F x=0 → H x=0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : SimpleFunc (ℝ × UnitAddCircle) ℂ,
    ∃ χ : ↥s.range → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ Ioo o (o+1) ×ˢ univ ∧ ∀ x, 0 ≤ χ i x ∧ χ i x ≤ 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      eLpNorm (fun x => F x - ∑ i, (cylinderTorusCutoff (χ i) x:ℂ)*F x) 2 slowVolume < ε ∧
      eLpNorm (fun x => H x - ∑ i, i.val*((cylinderTorusCutoff (χ i) x:ℂ)*F x)) 2 slowVolume < ε := by
  let π := cylinderToSlow
  have hπ := measurePreserving_cylinderToSlow o
  have hFm' := hFm.comp hπ.measurable
  have hHm' := hHm.comp hπ.measurable
  have hF' := hF.comp_measurePreserving hπ
  have hH' := hH.comp_measurePreserving hπ
  obtain ⟨s,χ,hχ,hd,hu,ht⟩ := coefficient_smooth_disjoint_approx (cylinderVolume o)
    hFm' hHm' hF' hH' (hπ.quasiMeasurePreserving.ae hzero)
    (isOpen_Ioo.prod isOpen_univ)
    ((cylinder_mem_open_ae o).mono (fun x hx hn => False.elim (hn hx))) hε
  simp only [comp_apply] at hu ht
  have hχsupp i : support (χ i) ⊆ Ioo o (o+1) ×ˢ univ := subset_tsupport (χ i) |>.trans (hχ i).2.2.1
  have hcm i : Measurable (χ i) := (hχ i).1.continuous.measurable
  have hum : AEStronglyMeasurable (fun x => F (cylinderToSlow x)-∑ i, (χ i x:ℂ)*F (cylinderToSlow x))
      (cylinderVolume o) :=
    (hFm'.sub (Finset.measurable_sum _ (fun i _ => (Complex.measurable_ofReal.comp (hcm i)).mul hFm'))).aestronglyMeasurable
  have htm : AEStronglyMeasurable (fun x => H (cylinderToSlow x)-∑ i, i.val*((χ i x:ℂ)*F (cylinderToSlow x)))
      (cylinderVolume o) :=
    (hHm'.sub (Finset.measurable_sum _ (fun i _ => measurable_const.mul
      ((Complex.measurable_ofReal.comp (hcm i)).mul hFm')))).aestronglyMeasurable
  have he i x : χ i (slowToCylinder o x) = cylinderTorusCutoff (χ i) x :=
    (cylinderTorusCutoff_rep (hχsupp i) x).symm
  refine ⟨s,χ,hχ,hd,?_,?_⟩
  · rw [← eLpNorm_slow_pull o _ hum] at hu
    simpa only [Function.comp_def,cylinderToSlow_slowToCylinder,he] using hu
  · rw [← eLpNorm_slow_pull o _ htm] at ht
    simpa only [Function.comp_def,cylinderToSlow_slowToCylinder,he] using ht

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma vector_reindex_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : PassagePackets ι) (e : κ ≃ ι) :
    finitePacketVector (F.reindex e).m (F.reindex e).A = finitePacketVector F.m F.A := by
  funext x
  exact e.sum_comp (fun i => packet (F.m i) (F.A i) x)

lemma tagged_vector_reindex_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : PassagePackets ι) (e : κ ≃ ι) (b : ι → ℂ) :
    (fun x => ∑ i, b (e i)*packet ((F.reindex e).m i) ((F.reindex e).A i) x) =
      fun x => ∑ i, b i*packet (F.m i) (F.A i) x := by
  funext x
  exact e.sum_comp (fun i => b i*packet (F.m i) (F.A i) x)

/-- Source05 constant-ratio preparation, including all zero-tag pieces.
The finite constant tags and compact smooth supports are chosen on positive
modes, then reflected literally. No weighted null set is divided by. -/
theorem exists_reflected_ratio_packets {ι : Type} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m)
    {τ : ι → ι} (hr : F.Reflection τ)
    (H : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hHm : ∀ i, Measurable (H i)) (hHl : ∀ i, MemLp (H i) 2 slowVolume)
    (hHr : ∀ i p, H (τ i) p=conj (H i p))
    (hzero : ∀ i, ∀ᵐ p ∂slowVolume, F.A i p=0 → H i p=0)
    {δ ε : ℝ} (hg : F.GoodArc δ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ G : PassagePackets (Fin n), ∃ σ : Fin n → Fin n, ∃ b : Fin n → ℂ,
      G.V=F.V ∧ G.GoodArc δ ∧ Involutive σ ∧ G.Reflection σ ∧
      (∀ i, b (σ i)=conj (b i)) ∧
      (∀ i j, i ≠ j → G.m i=G.m j → Disjoint (G.cylinderCore i) (G.cylinderCore j)) ∧
      physicalDist (finitePacketVector F.m F.A) (finitePacketVector G.m G.A) < ε ∧
      physicalDist (finitePacketVector F.m H) (fun x => ∑ i, b i*packet (G.m i) (G.A i) x) < ε := by
  classical
  have hFl i : MemLp (F.A i) 2 slowVolume := (F.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  let η := (ε/2)/(Fintype.card (PositiveIndex F.m)+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have ht (i : PositiveIndex F.m) := torus_coefficient_smooth_disjoint_approx F.o
    (F.continuous_amplitude i.val).measurable (hHm i.val) (hFl i.val) (hHl i.val)
    (hzero i.val) ((ENNReal.ofReal_pos.mpr hη).ne')
  choose s χ hχ hd hFe hHe using ht
  let J : PositiveIndex F.m → Type := fun i => ↥(s i).range
  let (i : PositiveIndex F.m) : Fintype (J i) := inferInstanceAs (Fintype ↥(s i).range)
  have hcs : ∀ k, CylinderSmooth (ratioCut F J χ k) := by
    intro k; cases k with
    | inl p => exact (hχ p.1 p.2).1
    | inr p => exact (hχ p.1 p.2).1
  have hcc : ∀ k, HasCompactSupport (ratioCut F J χ k) := by
    intro k; cases k with
    | inl p => exact (hχ p.1 p.2).2.1
    | inr p => exact (hχ p.1 p.2).2.1
  have hss : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ := by
    intro k; cases k with
    | inl p => exact (subset_tsupport _).trans (hχ p.1 p.2).2.2.1
    | inr p => exact (subset_tsupport _).trans (hχ p.1 p.2).2.2.1
  let G₀ := F.clipped (ratioRoot F J τ) (ratioCut F J χ) hcs hcc hss
  let b₀ : RatioIndex F J → ℂ := ratioTag F J (fun _ j => j.val)
  let e : Fin (Fintype.card (RatioIndex F J)) ≃ RatioIndex F J := (Fintype.equivFin _).symm
  let G := G₀.reindex e
  let σ : Fin (Fintype.card (RatioIndex F J)) → Fin (Fintype.card (RatioIndex F J)) :=
    fun i => e.symm (e i).swap
  have heσ i : e (σ i)=(e i).swap := e.apply_symm_apply _
  have hσ : Involutive σ := by intro i; simp only [σ,Equiv.apply_symm_apply,Sum.swap_swap,Equiv.symm_apply_apply]
  have hr₀ : G₀.Reflection Sum.swap := clipped_reflection hr hcs hcc hss
  have hd₀ := clipped_equal_mode_disjoint hi hr hcs hcc hss hd
  have hv : finitePacketVector G.m G.A = finitePacketVector G₀.m G₀.A := vector_reindex_equiv G₀ e
  have htv : (fun x => ∑ i, b₀ (e i)*packet (G.m i) (G.A i) x) =
      (fun x => ∑ i, b₀ i*packet (G₀.m i) (G₀.A i) x) := tagged_vector_reindex_equiv G₀ e b₀
  refine ⟨_,G,σ,b₀ ∘ e,rfl,hg,hσ,G₀.reindex_reflection hr₀ heσ,?_,?_,?_,?_⟩
  · intro i
    exact (congrArg b₀ (heσ i)).trans (ratioTag_reflect F J _ (e i))
  · intro i j hij hm
    exact hd₀ (e i) (e j) (fun h => hij (e.injective h)) hm
  · rw [hv,untagged_clipped_vector hr hcs hcc hss,
        reflectedVector_eq F.nonzero (hr.involutive hi) hr.index hr.amplitude]
    apply physicalDist_reflectedVector τ (fun i => hFl i.val) _ hε hFe
    intro i
    apply Continuous.memLp_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_finsetSum _ (fun j _ =>
      (Complex.continuous_ofReal.comp (cylinderTorusCutoff_continuous (hχ i j).1 (hχ i j).2.1)).mul
        (F.continuous_amplitude i.val))
  · change physicalDist _ (fun x => ∑ i, b₀ (e i)*packet (G.m i) (G.A i) x) < ε
    rw [htv,tagged_clipped_vector hr hcs hcc hss,
      reflectedVector_eq F.nonzero (hr.involutive hi) hr.index hHr]
    apply physicalDist_reflectedVector τ (fun i => hHl i.val) _ hε hHe
    intro i
    apply Continuous.memLp_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_finsetSum _ (fun j _ => continuous_const.mul
      ((Complex.continuous_ofReal.comp (cylinderTorusCutoff_continuous (hχ i j).1 (hχ i j).2.1)).mul
        (F.continuous_amplitude i.val)))

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
namespace ThreeTorus

lemma physicalDist_add_smul {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) (c : ℂ) :
    physicalDist f (fun x => f x+c*g x) = ‖c‖*‖hg.toLp g‖ := by
  change physicalDist f (f+c • g) = _
  rw [physicalDist_eq_norm hf (hf.add (hg.const_smul c)),MemLp.toLp_add,
    MemLp.toLp_const_smul]
  · simp only [sub_add_cancel_left,norm_neg,norm_smul]
  · exact hg
  · exact hf
  · exact hg.const_smul c

namespace PassagePackets
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma append_weighted_vector (F : PassagePackets ι) (H : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hgF : F.GoodArc δ) (hgH : H.GoodArc δ) (hV : H.V=F.V)
    (a b : ℂ) :
    (fun x => ∑ i, Sum.elim (fun _ => a) (fun _ => b) i *
      packet ((F.append H hδ hgF hgH hV).m i) ((F.append H hδ hgF hgH hV).A i) x) =
      fun x => a*finitePacketVector F.m F.A x+b*finitePacketVector H.m H.A x := by
  funext x
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,append,finitePacketVector,Finset.mul_sum]

lemma modeSum_add_amplitude (F : PassagePackets ι) (a b : ι → ℂ) (t : ℂ)
    (k : F.ModeIndex) (p : UnitAddCircle × UnitAddCircle) :
    (F.modeSum (fun i => a i+t*b i)).A k p =
      (F.modeSum a).A k p+t*(F.modeSum b).A k p := by
  classical
  change (∑ i, (if F.m i=k.val then a i+t*b i else 0)*F.A i p) =
    (∑ i, (if F.m i=k.val then a i else 0)*F.A i p)+t*∑ i, (if F.m i=k.val then b i else 0)*F.A i p
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring
end PassagePackets

/-- Two actual real smooth packet vectors in a common good-arc twist admit
simultaneous constant-tag clipping. Repeated modes are honestly regrouped;
zero pieces of either vector are retained before the real null-set perturbation. -/
theorem exists_ratio_packets_for_pair {ι κ : Type} [Fintype ι] [Fintype κ]
    (F : PassagePackets ι) (H : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hgF : F.GoodArc δ) (hgH : H.GoodArc δ) (hV : H.V=F.V)
    (τ : ι → ι) (σ : κ → κ) (hτ : Involutive τ) (hσ : Involutive σ)
    (hrF : F.Reflection τ) (hrH : H.Reflection σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ G : PassagePackets (Fin n), ∃ ρ : Fin n → Fin n, ∃ b : Fin n → ℂ,
      G.V=F.V ∧ G.GoodArc δ ∧ Involutive ρ ∧ G.Reflection ρ ∧
      (∀ i, b (ρ i)=conj (b i)) ∧
      (∀ i j, i ≠ j → G.m i=G.m j → Disjoint (G.cylinderCore i) (G.cylinderCore j)) ∧
      physicalDist (finitePacketVector F.m F.A) (finitePacketVector G.m G.A) < ε ∧
      physicalDist (finitePacketVector H.m H.A) (fun x => ∑ i, b i*packet (G.m i) (G.A i) x) < ε := by
  classical
  let U := F.append H hδ hgF hgH hV
  let a : ι ⊕ κ → ℂ := Sum.elim (fun _ => 1) (fun _ => 0)
  let b : ι ⊕ κ → ℂ := Sum.elim (fun _ => 0) (fun _ => 1)
  let B := U.modeSum a
  let C := U.modeSum b
  let r : ι ⊕ κ → ι ⊕ κ := Sum.map τ σ
  have hr : U.Reflection r := F.append_reflection H hδ hgF hgH hV hrF hrH
  have hri : Involutive r := by
    intro i; cases i with
    | inl i => exact congrArg Sum.inl (hτ i)
    | inr i => exact congrArg Sum.inr (hσ i)
  have ha : ∀ i, a (r i)=conj (a i) := by intro i; cases i <;> simp [a,r]
  have hb : ∀ i, b (r i)=conj (b i) := by intro i; cases i <;> simp [b,r]
  have hcv : finitePacketVector C.m C.A = finitePacketVector H.m H.A := by
    rw [U.modeSum_vector b,F.append_weighted_vector H hδ hgF hgH hV]
    simp only [zero_mul,one_mul,zero_add]
  have hbl i : MemLp (B.A i) 2 slowVolume := (B.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hcl i : MemLp (C.A i) 2 slowVolume := (C.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hFl : MemLp (finitePacketVector F.m F.A) 2 tripleVolume := memLp_finitePacketVector
    (fun i => (F.continuous_amplitude i).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hHl : MemLp (finitePacketVector H.m H.A) 2 tripleVolume := memLp_finitePacketVector
    (fun i => (H.continuous_amplitude i).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  let M := ‖hHl.toLp (finitePacketVector H.m H.A)‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨t,ht,htε,htz⟩ := exists_small_real_perturbation slowVolume
    (fun i => (B.continuous_amplitude i).measurable) (fun i => (C.continuous_amplitude i).measurable)
    (div_pos (half_pos hε) hM)
  let D := U.modeSum (fun i => a i+(t:ℂ)*b i)
  have hD : D.Reflection (U.modeNeg hr) := U.modeSum_reflection hri hr (by
    intro i; simp only [ha,hb,map_add,map_mul,Complex.conj_ofReal])
  have hC : C.Reflection (U.modeNeg hr) := U.modeSum_reflection hri hr hb
  have hz i : ∀ᵐ p ∂slowVolume, D.A i p=0 → C.A i p=0 := by
    simpa only [D,U.modeSum_add_amplitude] using htz i
  obtain ⟨n,G,ρ,q,hGV,hGg,hρ,hrG,hq,hd,hDG,hCG⟩ := exists_reflected_ratio_packets D
    (U.modeSum_injective _) hD C.A (fun i => (C.continuous_amplitude i).measurable)
    hcl hC.amplitude hz (U.modeSum_good _ (F.append_good H hδ hgF hgH hV)) (half_pos hε)
  have hDv : finitePacketVector D.m D.A = fun x => finitePacketVector F.m F.A x+(t:ℂ)*finitePacketVector H.m H.A x := by
    rw [U.modeSum_vector]
    have he : (fun i => a i+(t:ℂ)*b i) = Sum.elim (fun _ => 1) (fun _ => (t:ℂ)) := by
      funext i; cases i <;> simp [a,b]
    simp_rw [congrFun he]
    rw [F.append_weighted_vector H hδ hgF hgH hV]
    simp only [one_mul]
  have hDt : physicalDist (finitePacketVector F.m F.A) (finitePacketVector D.m D.A) < ε/2 := by
    rw [hDv,physicalDist_add_smul hFl hHl,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
    have hh := (lt_div_iff₀ hM).mp htε
    have hn := norm_nonneg (hHl.toLp (finitePacketVector H.m H.A))
    dsimp only [M] at hh
    nlinarith
  refine ⟨n,G,ρ,q,hGV,hGg,hρ,hrG,hq,hd,?_,?_⟩
  · have hDl : MemLp (finitePacketVector D.m D.A) 2 tripleVolume := memLp_finitePacketVector (fun i => (D.continuous_amplitude i).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    have hGl : MemLp (finitePacketVector G.m G.A) 2 tripleVolume := memLp_finitePacketVector (fun i => (G.continuous_amplitude i).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    exact (physicalDist_triangle hFl hDl hGl).trans_lt (by linarith)
  · change physicalDist (finitePacketVector C.m C.A) _ < ε/2 at hCG
    rw [hcv] at hCG
    exact hCG.trans (by linarith)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

attribute [instance] RealPacketFamily.finite
namespace RealPacketFamily
variable (F : RealPacketFamily)
lemma continuous_vector : Continuous F.vector :=
  continuous_finsetSum _ (fun i _ => continuous_packet (F.data.continuous_amplitude i))
lemma vector_memLp : MemLp F.vector 2 tripleVolume :=
  F.continuous_vector.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma density_integrable : Integrable F.density phaseHaar :=
  integrable_finsetSum _ (fun i _ => F.data.marginalDensity_integrable i)

end RealPacketFamily
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalDist_continuous_comp (α : Equiv.Perm TripleTorus) (hc : Continuous α)
    (hm : MeasurePreserving α tripleVolume tripleVolume) (f g : TripleTorus → ℂ) :
    physicalDist (f ∘ α) (g ∘ α)=physicalDist f g := by
  unfold physicalDist physicalError
  exact congrArg Real.sqrt (hm.integral_comp (hc.measurableEmbedding α.injective) (fun x => ‖f x-g x‖^2))

lemma physicalDist_add_right (f g h : TripleTorus → ℂ) :
    physicalDist (fun x => f x+h x) (fun x => g x+h x)=physicalDist f g := by
  unfold physicalDist physicalError
  simp only [add_sub_add_right_eq_sub]

lemma densityDist_triangle {p q r : UnitAddCircle → ℝ}
    (hp : Integrable p phaseHaar) (hq : Integrable q phaseHaar) (hr : Integrable r phaseHaar) :
    (∫ z, |p z-r z| ∂phaseHaar) ≤ (∫ z, |p z-q z| ∂phaseHaar)+(∫ z, |q z-r z| ∂phaseHaar) := by
  calc
    _ ≤ ∫ z, |p z-q z|+|q z-r z| ∂phaseHaar :=
      integral_mono (hp.sub hr).abs (((hp.sub hq).abs).add ((hq.sub hr).abs))
        (fun z => abs_sub_le (p z) (q z) (r z))
    _ = _ := integral_add (hp.sub hq).abs (hq.sub hr).abs
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

attribute [local instance] OAI.ThreeTorus.instMeasureSpaceUnitAddCircle_solutions_4
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_4 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

lemma multiTrigPolynomial_add (c b : (d → ℤ) →₀ ℂ) :
    multiTrigPolynomial (c+b) = multiTrigPolynomial c+multiTrigPolynomial b := by
  unfold multiTrigPolynomial
  exact Finsupp.sum_add_index' (by intro k; exact zero_smul ℂ (UnitAddTorus.mFourier k)) (fun k a b => add_smul a b (UnitAddTorus.mFourier k))

lemma multiTrigPolynomial_smul (a : ℂ) (c : (d → ℤ) →₀ ℂ) :
    multiTrigPolynomial (a • c) = a • multiTrigPolynomial c := by
  unfold multiTrigPolynomial
  rw [Finsupp.sum_smul_index (h := fun k (a : ℂ) => a • UnitAddTorus.mFourier k) (fun k => zero_smul ℂ (UnitAddTorus.mFourier k))]
  simp only [smul_smul,Finsupp.sum,Finset.smul_sum]

lemma multiTrigPolynomial_single (k : d → ℤ) (a : ℂ) :
    multiTrigPolynomial (Finsupp.single k a) = a • UnitAddTorus.mFourier k := by
  unfold multiTrigPolynomial
  exact Finsupp.sum_single_index (h := fun k (a : ℂ) => a • UnitAddTorus.mFourier k) (zero_smul ℂ (UnitAddTorus.mFourier k))

omit [Fintype d] in
lemma conjugateCoefficients_apply (c : (d → ℤ) →₀ ℂ) (k : d → ℤ) :
    conjugateCoefficients c k = conj (c (-k)) := by
  have h := Finsupp.mapDomain_apply (neg_injective : Injective (fun k : d → ℤ => -k))
    (Finsupp.mapRange conj (map_zero _) c) (-k)
  simpa only [conjugateCoefficients,neg_neg,Finsupp.mapRange_apply] using h

lemma multiTrigPolynomial_conjugate (c : (d → ℤ) →₀ ℂ) (x : UnitAddTorus d) :
    multiTrigPolynomial (conjugateCoefficients c) x = conj (multiTrigPolynomial c x) := by
  simp only [multiTrigPolynomial,conjugateCoefficients]
  rw [Finsupp.sum_mapDomain_index (h := fun k (a : ℂ) => a • UnitAddTorus.mFourier k) (fun k => zero_smul ℂ (UnitAddTorus.mFourier k)) (fun k a b => add_smul a b (UnitAddTorus.mFourier k))]
  rw [Finsupp.sum_mapRange_index (h := fun k (a : ℂ) => a • UnitAddTorus.mFourier (-k)) (fun k => zero_smul ℂ (UnitAddTorus.mFourier (-k)))]
  simp only [Finsupp.sum,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    UnitAddTorus.mFourier_neg,map_sum,map_mul]

lemma integral_mFourier (k : d → ℤ) :
    (∫ x : UnitAddTorus d, UnitAddTorus.mFourier k x) = if k=0 then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := d)) (0:d → ℤ) k
  simpa only [ContinuousMap.inner_toLp,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,
    map_one,one_mul,mul_one,eq_comm] using h

lemma integral_multiTrigPolynomial (c : (d → ℤ) →₀ ℂ) :
    (∫ x : UnitAddTorus d, multiTrigPolynomial c x) = c 0 := by
  classical
  simp only [multiTrigPolynomial_apply]
  rw [integral_finsetSum _ (fun k _ =>
    ((UnitAddTorus.mFourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul (c k))]
  simp only [integral_const_mul,integral_mFourier,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

/-- A finite FULL-torus polynomial can be made exactly real and centered,
with reflected coefficients, without changing the density statement. -/
theorem exists_real_centered_uniform_multiTrig {h : UnitAddTorus d → ℂ}
    (hh : Continuous h) (hr : ∀ x, conj (h x) = h x)
    (hc : ∫ x, h x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : (d → ℤ) →₀ ℂ, c 0 = 0 ∧ (∀ k, c (-k)=conj (c k)) ∧
      ∀ x, ‖h x-multiTrigPolynomial c x‖ < ε := by
  classical
  obtain ⟨b,hb⟩ := exists_uniform_multiTrig hh (show 0 < ε/4 by positivity)
  let r : (d → ℤ) →₀ ℂ := (1/2:ℂ) • (b+conjugateCoefficients b)
  have hrk (k : d → ℤ) : r (-k) = conj (r k) := by
    simp only [r,Finsupp.smul_apply,Finsupp.add_apply,conjugateCoefficients_apply,
      neg_neg,smul_eq_mul,map_mul,map_div₀,map_one,map_ofNat,map_add,starRingEnd_self_apply]
    congr 1
    exact add_comm _ _
  have hrp (x : UnitAddTorus d) : multiTrigPolynomial r x =
      (multiTrigPolynomial b x+conj (multiTrigPolynomial b x))/2 := by
    simp only [r,multiTrigPolynomial_smul,multiTrigPolynomial_add,ContinuousMap.smul_apply,
      ContinuousMap.add_apply,smul_eq_mul,multiTrigPolynomial_conjugate]
    ring
  have hdist (x : UnitAddTorus d) : ‖h x-multiTrigPolynomial r x‖ < ε/4 := by
    rw [hrp]
    have he : h x-(multiTrigPolynomial b x+conj (multiTrigPolynomial b x))/2 =
        ((h x-multiTrigPolynomial b x)+conj (h x-multiTrigPolynomial b x))/2 := by
      rw [map_sub,hr x]; ring
    rw [he,norm_div]
    have hn := norm_add_le (h x-multiTrigPolynomial b x) (conj (h x-multiTrigPolynomial b x))
    simp only [Complex.norm_conj] at hn
    rw [Complex.norm_ofNat]
    linarith [hb x]
  have hint : Integrable h volume := hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrint : Integrable (multiTrigPolynomial r) volume :=
    (multiTrigPolynomial r).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr0 : ‖r 0‖ ≤ ε/4 := by
    have he : (∫ x, h x-multiTrigPolynomial r x) = -r 0 := by
      rw [integral_sub hint hrint,hc,integral_multiTrigPolynomial,zero_sub]
    have hbnd := norm_integral_le_of_norm_le (μ := (volume : Measure (UnitAddTorus d))) (integrable_const (ε/4)) (.of_forall fun x => (hdist x).le)
    simpa only [he,norm_neg,integral_const,probReal_univ,one_smul] using hbnd
  let c : (d → ℤ) →₀ ℂ := r-Finsupp.single 0 (r 0)
  have hcapply (k : d → ℤ) : c k = r k - if k=0 then r 0 else 0 := by
    simp only [c,Finsupp.sub_apply,Finsupp.single_apply,eq_comm]
  refine ⟨c,by simp [hcapply],?_,?_⟩
  · intro k
    by_cases hk : k=0
    · simp [hcapply,hk]
    · simp [hcapply,hk,hrk]
  · intro x
    have hep : multiTrigPolynomial c x = multiTrigPolynomial r x-r 0 := by
      have hec : c = r+(-1:ℂ) • Finsupp.single 0 (r 0) := by
        simp only [c,neg_one_smul,sub_eq_add_neg]
      rw [hec,multiTrigPolynomial_add,multiTrigPolynomial_smul (-1) (Finsupp.single 0 (r 0)),multiTrigPolynomial_single]
      simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,
        UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,mul_one,neg_one_mul,sub_eq_add_neg]
    rw [hep,sub_sub_eq_add_sub]
    have he : h x+r 0-multiTrigPolynomial r x = (h x-multiTrigPolynomial r x)+r 0 := by ring
    rw [he]
    exact (norm_add_le _ _).trans_lt (by linarith [hdist x])

end ThreeTorus
end
end

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma toTriple_apply (x : Torus) : toTriple x = (x 0,x 1,x 2) := rfl

lemma toTriple_symm_apply (x : TripleTorus) : toTriple.symm x = ![x.1,x.2.1,x.2.2] := by
  apply toTriple.injective
  simp only [MeasurableEquiv.apply_symm_apply,toTriple_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

lemma measurePreserving_toTriple : MeasurePreserving toTriple μ tripleVolume := by
  exact ((MeasurePreserving.id AddCircle.haarAddCircle).prod
    (measurePreserving_piFinTwo (fun _ : Fin 2 => AddCircle.haarAddCircle))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => AddCircle.haarAddCircle) 0)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators RealInnerProductSpace ENNReal
namespace ThreeTorus

/-- Removing a fiber mean is an orthogonal projection, with constant ONE.
This is the estimate preserving the source good-arc sqrt(beta) loss. -/
lemma integral_sq_sub_mean {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℂ} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x-∫ y, f y ∂μ‖^2 ∂μ) =
      (∫ x, ‖f x‖^2 ∂μ)-‖∫ y, f y ∂μ‖^2 := by
  have hi := hf.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hinner : (∫ x, inner ℝ (f x) (∫ y, f y ∂μ) ∂μ) = ‖∫ y, f y ∂μ‖^2 := by
    calc
      _ = ∫ x, inner ℝ (∫ y, f y ∂μ) (f x) ∂μ := integral_congr_ae
        (.of_forall fun x => real_inner_comm _ _)
      _ = inner ℝ (∫ y, f y ∂μ) (∫ y, f y ∂μ) := integral_inner hi _
      _ = _ := real_inner_self_eq_norm_sq _
  simp_rw [norm_sub_sq_real]
  have hn : Integrable (fun x => ‖f x‖^2) μ := hf.integrable_norm_pow (by norm_num)
  have hh : Integrable (fun x => 2*inner ℝ (f x) (∫ y, f y ∂μ)) μ :=
    (hi.inner_const (𝕜 := ℝ) (∫ y, f y ∂μ)).const_mul 2
  have ha := integral_add (hn.sub hh) (integrable_const (μ := μ) (‖∫ y, f y ∂μ‖^2))
  dsimp only [Pi.sub_apply] at ha
  rw [ha,integral_sub hn hh,integral_const,probReal_univ,one_smul,integral_const_mul,hinner]
  ring

lemma integral_sq_sub_mean_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℂ} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x-∫ y, f y ∂μ‖^2 ∂μ) ≤ ∫ x, ‖f x‖^2 ∂μ := by
  rw [integral_sq_sub_mean hf]
  exact sub_le_self _ (sq_nonneg _)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma mFourier_toTriple (k : TensorIndex) (x : TripleTorus) :
    UnitAddTorus.mFourier k (toTriple.symm x) = tensorCharacter k x := by
  change (∏ i, fourier (k i) (toTriple.symm x i)) = _
  simp only [Fin.prod_univ_three,toTriple_symm_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,tensorCharacter]
  rfl

lemma tensorPolynomial_eq (c : TensorIndex →₀ ℂ) : tensorPolynomial c = multiTrigPolynomial c ∘ toTriple.symm := by
  funext x
  simp only [tensorPolynomial,multiTrigPolynomial_apply,Function.comp_apply,Finsupp.sum,mFourier_toTriple]

lemma continuous_toTriple : Continuous toTriple := by
  change Continuous (fun x : Torus => (x 0,x 1,x 2))
  fun_prop

lemma continuous_toTriple_symm : Continuous toTriple.symm := by
  simp only [show (toTriple.symm : TripleTorus → Torus) = fun x => ![x.1,x.2.1,x.2.2] from funext toTriple_symm_apply]
  exact continuous_pi (fun i => by fin_cases i <;> fun_prop)

lemma tensorCharacter_continuous (k : TensorIndex) : Continuous (tensorCharacter k) := by
  unfold tensorCharacter
  fun_prop

lemma tensorPolynomial_continuous (c : TensorIndex →₀ ℂ) : Continuous (tensorPolynomial c) := by
  rw [tensorPolynomial_eq]
  exact (multiTrigPolynomial c).continuous.comp continuous_toTriple_symm

attribute [local instance] OAI.ThreeTorus.instMeasureSpaceUnitAddCircle_solutions_5
lemma exists_real_centered_tensor {h : TripleTorus → ℂ} (hh : Continuous h)
    (hr : ∀ x, conj (h x) = h x) (hc : ∫ x, h x ∂tripleVolume = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : TensorIndex →₀ ℂ, c 0=0 ∧ (∀ k, c (-k)=conj (c k)) ∧
      ∀ x, ‖h x-tensorPolynomial c x‖ < ε := by
  have hm : (volume : Measure (UnitAddTorus (Fin 3))) = μ := rfl
  have hcen : ∫ x : UnitAddTorus (Fin 3), h (toTriple x) = 0 := by
    rw [hm,measurePreserving_toTriple.integral_comp toTriple.measurableEmbedding,hc]
  obtain ⟨c,hc0,hcr,hcε⟩ := exists_real_centered_uniform_multiTrig
    (hh.comp continuous_toTriple) (fun x => hr (toTriple x)) hcen hε
  refine ⟨c,hc0,hcr,fun x => ?_⟩
  simpa only [tensorPolynomial_eq,comp_apply,toTriple.apply_symm_apply] using hcε (toTriple.symm x)

lemma tensor_split (c : TensorIndex →₀ ℂ) :
    tensorAngular c + tensorMiddle c + tensorLast c = c := by
  classical
  ext k
  simp only [tensorAngular,tensorMiddle,tensorLast,Finsupp.add_apply,Finsupp.filter_apply]
  by_cases h0 : k 0=0 <;> by_cases h1 : k 1=0 <;> simp [h0,h1]

end ThreeTorus
end
end

section

/-! The two neutral passages of source05, on the same literal packet family.
The first separates cylinder supports and the second makes angular modes
injective. Physical and density estimates retain each original root label. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma scalar_cylinder_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : ℝ × UnitAddCircle => f p.1) := by
  apply (hf.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport _) 
  apply closure_minimal _ (hf.isClosed.prod isClosed_univ)
  intro p hp
  exact ⟨subset_tsupport f hp,mem_univ _⟩

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_TensorPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good-arc cutoffs, scalar and tensor packet constructors, fiber insertion, and initial dense tests. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

lemma sharp_cutoff_integral_bound {δ t : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ)
    (hu : δ+t < 1/2) {b : ℝ → ℝ} (hbc : Continuous b) (_hbs : HasCompactSupport b)
    (hb : ∀ x, 0 ≤ b x ∧ b x ≤ 1)
    (hone : ∀ x ∈ Icc (δ+t) (1-δ-t), b x = 1) :
    (∫ x in Ioo (0:ℝ) 1, (1-b x)^2) ≤ 2*δ+2*t := by
  have hbint : IntegrableOn (fun x : ℝ => b x^2) (Ioo (0:ℝ) 1) :=
    (hbc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hlower : 1-2*δ-2*t ≤ ∫ x in Ioo (0:ℝ) 1, b x^2 := by
    calc
      _ = ∫ x in Icc (δ+t) (1-δ-t), (1:ℝ) := by
        simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,
          Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-δ-t-(δ+t))]
        ring
      _ = ∫ x in Icc (δ+t) (1-δ-t), b x^2 := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        dsimp only
        rw [hone x hx,one_pow]
      _ ≤ ∫ x in Ioo (0:ℝ) 1, b x^2 := by
        apply setIntegral_mono_set hbint (.of_forall fun _ => sq_nonneg _)
        exact .of_forall fun x hx => ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo (0:ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  calc
    _ ≤ ∫ x in Ioo (0:ℝ) 1, 1-b x^2 := by
      apply setIntegral_mono_on
        ((continuous_const.sub hbc).pow 2 |>.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
        (hi.sub hbint) measurableSet_Ioo
      intro x _
      change (1-b x)^2 ≤ 1-b x^2
      nlinarith [(hb x).1,(hb x).2]
    _ = 1-∫ x in Ioo (0:ℝ) 1, b x^2 := by rw [integral_sub hi hbint]; simp
    _ ≤ _ := by linarith

/-- Smooth compact arc cutoffs with arbitrarily small excess over the ACTUAL
complement length. The standard neutral 4δ estimate is not sharp enough here. -/
theorem exists_sharp_arc_cutoff {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t)
    (hu : δ+t < 1/2) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ioo δ (1-δ) ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ Icc (δ+t) (1-δ-t), χ x = 1) ∧
      (∫ x in Ioo (0:ℝ) 1, (1-χ x)^2) ≤ 2*δ+2*t := by
  let b : ContDiffBump (1/2:ℝ) := ⟨1/2-δ-t,1/2-δ-t/2,by linarith,by linarith⟩
  have hs : tsupport (b : ℝ → ℝ) ⊆ Ioo δ (1-δ) := by
    intro x hx
    rw [b.tsupport_eq] at hx
    change |x-1/2| ≤ 1/2-δ-t/2 at hx
    have hh := abs_le.mp hx
    constructor <;> linarith
  have hone : ∀ x ∈ Icc (δ+t) (1-δ-t), b x = 1 := by
    intro x hx
    apply b.one_of_mem_closedBall
    change |x-1/2| ≤ 1/2-δ-t
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  refine ⟨b,b.contDiff,b.hasCompactSupport,hs,fun x => ⟨b.nonneg,b.le_one⟩,hone,?_⟩
  exact sharp_cutoff_integral_bound ht hδ hu b.continuous b.hasCompactSupport
    (fun _ => ⟨b.nonneg,b.le_one⟩) hone

lemma circle_cutoff_squared_error {χ : ℝ → ℝ}
    (_hc : HasCompactSupport χ) (hs : support χ ⊆ Ioo (0:ℝ) 1)
    (_hb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ x, (1-(periodize_periodic χ).lift x)^2 ∂AddCircle.haarAddCircle) =
      ∫ x in Ioo (0:ℝ) 1, (1-χ x)^2 := by
  have he := AddCircle.integral_preimage 1 0
    (fun x : UnitAddCircle => (1-(periodize_periodic χ).lift x)^2)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  change (1-periodize χ x)^2 = (1-χ x)^2
  rw [periodize_eq_on_unit hs ⟨hx.1.le,hx.2.le⟩]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma cylinderTorusCutoff_scalar (χ : ℝ → ℝ) (p : UnitAddCircle × UnitAddCircle) :
    cylinderTorusCutoff (fun q => χ q.1) p = (periodize_periodic χ).lift p.1 := by
  rcases p with ⟨p,q⟩
  obtain ⟨x,hx⟩ := QuotientAddGroup.mk_surjective p
  subst p
  rfl

/-- A common scalar good-arc cutoff produces literal smooth input packets;
all data are fixed before any passage integer is chosen. -/
theorem exists_scalar_cutoff_packets {ι : Type*}
    (m : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (C : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hCc : ∀ i, Continuous (C i))
    (hCs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => C i (p.1,p.2)))
    {χ : ℝ → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (hχI : tsupport χ ⊆ Ioo δ (1-δ))
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) :
    ∃ F : PassagePackets ι, F.m=m ∧ F.V=V ∧ F.GoodArc δ ∧
      (∀ i p, F.A i p = ((periodize_periodic χ).lift p.1:ℂ)*C i p) ∧
      ∀ i a x, F.A₀ i a x = (χ x:ℂ)*C i ((x:UnitAddCircle),a) := by
  obtain ⟨l,u,R,hdl,hlu,hud,hR,hKI,hbuffer⟩ := compact_inside_buffered_interval
    hχc (by linarith : δ < 1-δ) hχI
  have hs : CylinderSmooth (fun p : ℝ × UnitAddCircle => χ p.1) := hχs.comp contDiff_fst
  have hc : HasCompactSupport (fun p : ℝ × UnitAddCircle => χ p.1) := scalar_cylinder_compact hχc
  have hso : support (fun p : ℝ × UnitAddCircle => χ p.1) ⊆ Ioo (0:ℝ) (0+1) ×ˢ univ := by
    intro p hp
    have h := hχI (subset_tsupport χ hp)
    exact ⟨⟨hδ.trans_lt h.1,by linarith [h.2]⟩,mem_univ _⟩
  have hsi : support (fun p : ℝ × UnitAddCircle => χ p.1) ⊆ Ioc l u ×ˢ univ :=
    fun p hp => ⟨hKI (subset_tsupport χ hp),mem_univ _⟩
  let F := cutoffPackets m hm C hCc hCs (fun _ p => χ p.1) (fun _ => hs) (fun _ => hc)
    0 l u R (fun _ => hso) (fun _ => hsi) (hδ.trans hdl.le) (by linarith) hlu.le hR
    V hVp hVs (fun x hx => hVd x (hbuffer hx))
  refine ⟨F,rfl,rfl,⟨rfl,hdl,hud,hVd⟩,?_,fun _ _ _ => rfl⟩
  intro i p
  change (cylinderTorusCutoff (fun q => χ q.1) p:ℂ)*C i p = _
  rw [cylinderTorusCutoff_scalar]

lemma scalar_packets_reflection {ι : Type*} (F : PassagePackets ι)
    {τ : ι → ι} {m : ι → ℤ} {C : ι → UnitAddCircle × UnitAddCircle → ℂ}
    {χ : ℝ → ℝ} (hm : F.m=m) (hmi : ∀ i, m (τ i) = -m i)
    (hc : ∀ i p, C (τ i) p = conj (C i p))
    (hA : ∀ i p, F.A i p = ((periodize_periodic χ).lift p.1:ℂ)*C i p)
    (hA₀ : ∀ i a x, F.A₀ i a x = (χ x:ℂ)*C i ((x:UnitAddCircle),a)) :
    F.Reflection τ := by
  constructor
  · simpa only [hm] using hmi
  · intro i p; rw [hA,hA,hc]; simp only [map_mul,Complex.conj_ofReal]
  · intro i a x; rw [hA₀,hA₀,hc]; simp only [map_mul,Complex.conj_ofReal]

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
namespace ThreeTorus

lemma tensor_filter_reflection {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k))
    (P : TensorIndex → Prop) [DecidablePred P] (hP : ∀ k, P (-k) ↔ P k) :
    ∀ k, (c.filter P) (-k)=conj ((c.filter P) k) := by
  intro k
  simp only [Finsupp.filter_apply,hP,hc,apply_ite,map_zero]
  split_ifs <;> rfl

lemma tensorAngular_reflection {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    ∀ k, tensorAngular c (-k)=conj (tensorAngular c k) :=
  tensor_filter_reflection hc _ (fun _ => by simp)

lemma tensorSupportNeg_involutive {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    Involutive (tensorSupportNeg hc) := fun _ => Subtype.ext (neg_neg _)

/-- Literal smooth packets of a finite tensor polynomial after a cyclic
coordinate change. The unused old coordinate is not silently discarded. -/
theorem exists_rotated_tensor_packets (c : TensorIndex →₀ ℂ)
    (hc : ∀ k, c (-k)=conj (c k)) (a b d : Fin 3)
    (hn : ∀ k ∈ c.support, k a ≠ 0)
    {χ : ℝ → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (hχI : tsupport χ ⊆ Ioo δ (1-δ))
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) :
    ∃ F : PassagePackets ↥c.support, F.V=V ∧ F.GoodArc δ ∧
      F.Reflection (tensorSupportNeg hc) ∧
      (∀ k, F.m k=k.val a) ∧
      ∀ x, finitePacketVector F.m F.A x = ((periodize_periodic χ).lift x.2.1:ℂ)*
        ∑ k ∈ c.support, c k*(fourier (k a) x.1*fourier (k b) x.2.1*fourier (k d) x.2.2) := by
  let C : ↥c.support → UnitAddCircle × UnitAddCircle → ℂ :=
    fun k ua => c k.val*fourier (k.val b) ua.1*fourier (k.val d) ua.2
  have hCc k : Continuous (C k) := by dsimp [C]; fun_prop
  have hCs k : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => C k (p.1,p.2)) :=
    (contDiff_const.mul ((smooth_fourier_lift (k.val b)).comp contDiff_fst)).mul
      ((smooth_fourier_lift (k.val d)).comp contDiff_snd)
  obtain ⟨F,hFm,hFV,hFg,hFA,hFA₀⟩ := exists_scalar_cutoff_packets
    (fun k : ↥c.support => k.val a) (fun k => hn k.val k.property) C hCc hCs
    hχs hχc hδ hd hχI V hVp hVs hVd
  have hCr k p : C (tensorSupportNeg hc k) p=conj (C k p) := by
    simp only [C,tensorSupportNeg,hc,Pi.neg_apply,fourier_neg,map_mul]
  have hFr := scalar_packets_reflection F hFm (fun _ => rfl) hCr hFA hFA₀
  refine ⟨F,hFV,hFg,hFr,fun _ => congrFun hFm _,?_⟩
  intro x
  simp only [finitePacketVector,packet,hFA,hFm,C]
  rw [Finset.mul_sum]
  change (∑ k ∈ c.support.attach, _) = _
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans
    (Finset.sum_attach c.support (fun k => ((periodize_periodic χ).lift x.2.1:ℂ)*
      (c k*(fourier (k a) x.1*fourier (k b) x.2.1*fourier (k d) x.2.2))))
  ring

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma tensorPolynomial_filter (c : TensorIndex →₀ ℂ) (p : TensorIndex → Prop)
    [DecidablePred p] (x : TripleTorus) :
    tensorPolynomial (c.filter p) x = ∑ k ∈ c.support, if p k then c k*tensorCharacter k x else 0 := by
  classical
  simp only [tensorPolynomial,Finsupp.sum,Finsupp.support_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : p k <;> simp [h]

lemma tensorCharacter_angular_integral (k : TensorIndex) (ua : UnitAddCircle × UnitAddCircle) :
    (∫ θ, tensorCharacter k (θ,ua) ∂phaseHaar) =
      if k 0=0 then fourier (k 1) ua.1*fourier (k 2) ua.2 else 0 := by
  simp only [tensorCharacter,integral_mul_const,integral_fourier_haar]
  split_ifs <;> simp_all

lemma tensorAngular_eq_remove_mean (c : TensorIndex →₀ ℂ) (x : TripleTorus) :
    tensorPolynomial (tensorAngular c) x =
      tensorPolynomial c x-∫ θ, tensorPolynomial c (θ,x.2) ∂phaseHaar := by
  classical
  have hsplit : ∀ k, (if k 0≠0 then c k*tensorCharacter k x else 0) =
      c k*tensorCharacter k x-c k*(if k 0=0 then fourier (k 1) x.2.1*fourier (k 2) x.2.2 else 0) := by
    intro k
    by_cases hk : k 0=0
    · simp [hk,tensorCharacter]
    · simp [hk]
  rw [tensorAngular,tensorPolynomial_filter]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]
  congr 1
  change _ = ∫ θ, ∑ k ∈ c.support, c k*tensorCharacter k (θ,x.2) ∂phaseHaar
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul,tensorCharacter_angular_integral]
  · intro k _
    exact (continuous_const.mul ((tensorCharacter_continuous k).comp
      (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

lemma tensorAngular_fiber_energy_le (c : TensorIndex →₀ ℂ) {B : ℝ} (_hB : 0 ≤ B)
    (hc : ∀ x, ‖tensorPolynomial c x‖ ≤ B) (ua : UnitAddCircle × UnitAddCircle) :
    (∫ θ, ‖tensorPolynomial (tensorAngular c) (θ,ua)‖^2 ∂phaseHaar) ≤ B^2 := by
  have hcont : Continuous (fun θ => tensorPolynomial c (θ,ua)) :=
    (tensorPolynomial_continuous c).comp (continuous_id.prodMk continuous_const)
  simp_rw [tensorAngular_eq_remove_mean]
  have hf := hcont.memLp_of_hasCompactSupport (p := 2) (μ := phaseHaar) (HasCompactSupport.of_compactSpace _)
  refine (integral_sq_sub_mean_le hf).trans ?_
  have he : (∫ θ : UnitAddCircle, B^2 ∂phaseHaar) = B^2 := by simp
  rw [← he]
  apply integral_mono (hcont.norm.pow 2 |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (integrable_const _)
  intro θ
  exact pow_le_pow_left₀ (norm_nonneg _) (hc (θ,ua)) 2

/-- Exact constant-one angular cutoff bound; it is the actual lost arc length,
not four times that length, which appears in the preparation error. -/
lemma tensorAngular_cutoff_energy (c : TensorIndex →₀ ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ x, ‖tensorPolynomial c x‖ ≤ B) {χ : UnitAddCircle → ℝ} (hχ : Continuous χ) :
    (∫ x : TripleTorus, ‖tensorPolynomial (tensorAngular c) x-
      (χ x.2.1:ℂ)*tensorPolynomial (tensorAngular c) x‖^2 ∂tripleVolume) ≤
      B^2 * ∫ u, (1-χ u)^2 ∂phaseHaar := by
  let f := tensorPolynomial (tensorAngular c)
  have hfc : Continuous f := tensorPolynomial_continuous _
  have he (x : TripleTorus) : ‖f x-(χ x.2.1:ℂ)*f x‖^2 = (1-χ x.2.1)^2*‖f x‖^2 := by
    rw [show f x-(χ x.2.1:ℂ)*f x = ((1-χ x.2.1:ℝ):ℂ)*f x by push_cast; ring,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  change (∫ x : TripleTorus, ‖f x-(χ x.2.1:ℂ)*f x‖^2 ∂tripleVolume) ≤ _
  simp_rw [he]
  have hi : Integrable (fun x : TripleTorus => (1-χ x.2.1)^2*‖f x‖^2) tripleVolume :=
    (((continuous_const.sub (hχ.comp (continuous_fst.comp continuous_snd))).pow 2).mul
      (hfc.norm.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_prod_symm _ hi]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∫ ua, (1-χ ua.1)^2*B^2 ∂slowVolume := by
      apply integral_mono (by simpa only [integral_const_mul] using hi.integral_prod_right)
        ((((continuous_const.sub (hχ.comp continuous_fst)).pow 2).mul continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      intro ua
      exact mul_le_mul_of_nonneg_left (tensorAngular_fiber_energy_le c hB hc ua) (sq_nonneg _)
    _ = _ := by
      rw [integral_prod]
      · simp only [integral_const,probReal_univ,one_smul]
        rw [integral_mul_const,mul_comm]
      · exact (((continuous_const.sub (hχ.comp continuous_fst)).pow 2).mul continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma tensorAngular_nonzero {c : TensorIndex →₀ ℂ} {k : TensorIndex}
    (hk : k ∈ (tensorAngular c).support) : k 0 ≠ 0 := by
  have hh := Finsupp.mem_support_iff.mp hk
  intro hn
  exact hh (by simp [tensorAngular,hn])

lemma tensor_split_vector (c : TensorIndex →₀ ℂ) (x : TripleTorus) :
    tensorPolynomial c x=tensorPolynomial (tensorAngular c) x+
      tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x := by
  have hs := congrArg (fun q => tensorPolynomial q x) (tensor_split c)
  unfold tensorPolynomial at hs
  rw [Finsupp.sum_add_index' (by simp) (by intros; ring),
    Finsupp.sum_add_index' (by simp) (by intros; ring)] at hs
  exact hs.symm
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma physicalDist_le_of_uniform {f g : TripleTorus → ℂ} (hf : Continuous f) (hg : Continuous g)
    {e : ℝ} (he : 0 ≤ e) (h : ∀ x, ‖f x-g x‖ ≤ e) : physicalDist f g ≤ e := by
  have hh : physicalDist f g^2 ≤ e^2 := by
    rw [physicalDist_sq,physicalError]
    calc
      _ ≤ ∫ _x : TripleTorus, e^2 ∂tripleVolume :=
        integral_mono (((hf.sub hg).norm.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (integrable_const _)
          (fun x => pow_le_pow_left₀ (norm_nonneg _) (h x) 2)
      _ = _ := by simp
  nlinarith [physicalDist_nonneg f g]

lemma small_angular_loss {δ e t : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (he : 0 < e) (hem : e ≤ 1/8) (ht : 0 < t) (htm : t ≤ e^2) :
    (1+e)^2*(2*δ+2*t) < (Real.sqrt (2*δ)+5*e)^2 := by
  have hs : 0 ≤ Real.sqrt (2*δ) := Real.sqrt_nonneg _
  have hss : (Real.sqrt (2*δ))^2=2*δ := Real.sq_sqrt (by positivity)
  have hs1 : Real.sqrt (2*δ) ≤ 1 := (Real.sqrt_le_iff).2 ⟨by norm_num,by linarith⟩
  have he2 : e^2 ≤ e/8 := by nlinarith
  have hm : (1+e)*(Real.sqrt (2*δ)+2*e) < Real.sqrt (2*δ)+5*e := by
    have hh := mul_le_mul_of_nonneg_left hs1 he.le
    nlinarith
  have hn : 0 ≤ (1+e)*(Real.sqrt (2*δ)+2*e) := by positivity
  have hb : 2*δ+2*t ≤ (Real.sqrt (2*δ)+2*e)^2 := by
    nlinarith [mul_nonneg hs he.le]
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg (1+e))
  have hsq := sq_lt_sq₀ hn (by positivity : 0 ≤ Real.sqrt (2*δ)+5*e) |>.2 hm
  rw [mul_pow] at hsq
  exact hmul.trans_lt hsq

/-- The INITIAL cutoff costs the exact old complement square root. Both slow
components are retained as the very same finite real tensor polynomial. -/
theorem exists_initial_tensor_test {h : TripleTorus → ℂ} (hh : Continuous h)
    (hr : ∀ x, conj (h x)=h x) (hc : ∫ x, h x ∂tripleVolume=0) (hb : ∀ x, ‖h x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (V : ℝ → ℝ) (hp : Periodic V 1) (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hv : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : TensorIndex →₀ ℂ, c 0=0 ∧ (∀ k, c (-k)=conj (c k)) ∧
      ∃ H : RealPacketFamily, H.data.V=V ∧ H.data.GoodArc δ ∧
      physicalDist h (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x)
        < Real.sqrt (2*δ)+ε := by
  classical
  let e := min (ε/8) (1/8)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have hem : e ≤ 1/8 := min_le_right _ _
  have heε : 8*e ≤ ε := by have := min_le_left (ε/8) (1/8); dsimp [e]; linarith
  obtain ⟨c,hc0,hcr,hce⟩ := exists_real_centered_tensor hh hr hc he
  let t := min (e^2) ((1/2-δ)/2)
  have ht : 0 < t := lt_min (sq_pos_of_pos he) (by linarith)
  have hdt : δ+t < 1/2 := by have := min_le_right (e^2) ((1/2-δ)/2); dsimp [t]; linarith
  obtain ⟨χ,hχs,hχc,hχI,hχb,_hχ1,hχe⟩ := exists_sharp_arc_cutoff hδ ht hdt
  obtain ⟨P,hPV,hPg,hPr,_hPm,hPv⟩ := exists_rotated_tensor_packets (tensorAngular c)
    (tensorAngular_reflection hcr) 0 1 2 (fun _ => tensorAngular_nonzero)
    hχs hχc hδ hd hχI V hp hs hv
  let H : RealPacketFamily := ⟨_,inferInstance,P,tensorSupportNeg (tensorAngular_reflection hcr),
    tensorSupportNeg_involutive _,hPr⟩
  refine ⟨c,hc0,hcr,H,hPV,hPg,?_⟩
  have hχsupp : support χ ⊆ Ioo (0:ℝ) 1 := fun x hx => by
    have hx := hχI (subset_tsupport _ hx)
    exact ⟨hδ.trans_lt hx.1,by linarith [hx.2]⟩
  have hχcont : Continuous ((periodize_periodic χ).lift) :=
    continuous_of_continuous_lift (by simpa only [Periodic.lift_coe] using (contDiff_periodize hχs hχc).continuous)
  have hHv : H.vector = fun x => ((periodize_periodic χ).lift x.2.1:ℂ)*tensorPolynomial (tensorAngular c) x := by
    funext x
    exact hPv x
  have hcb (x : TripleTorus) : ‖tensorPolynomial c x‖ ≤ 1+e := by
    have ht := norm_le_norm_add_norm_sub (h x) (tensorPolynomial c x)
    linarith [hb x,hce x]
  have hA : physicalDist (tensorPolynomial (tensorAngular c)) H.vector < Real.sqrt (2*δ)+5*e := by
    apply (physicalDist_lt_iff _ _ (by positivity)).2
    rw [hHv]
    have htE := tensorAngular_cutoff_energy c (by positivity : 0 ≤ 1+e) hcb hχcont
    have hl := circle_cutoff_squared_error hχc hχsupp hχb
    rw [hl] at htE
    exact htE.trans_lt ((mul_le_mul_of_nonneg_left hχe (sq_nonneg (1+e))).trans_lt
      (small_angular_loss hδ hd he hem ht (min_le_left _ _)))
  have hpoly : physicalDist h (tensorPolynomial c) ≤ e := physicalDist_le_of_uniform hh
    (tensorPolynomial_continuous c) he.le (fun x => (hce x).le)
  let K := fun x => H.vector x+tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x
  have hKc : Continuous K := (H.continuous_vector.add (tensorPolynomial_continuous _)).add (tensorPolynomial_continuous _)
  have hAK : physicalDist (tensorPolynomial c) K = physicalDist (tensorPolynomial (tensorAngular c)) H.vector := by
    have hcFun := funext (tensor_split_vector c)
    rw [hcFun]
    change physicalDist (fun x => (tensorPolynomial (tensorAngular c) x+tensorPolynomial (tensorMiddle c) x)+tensorPolynomial (tensorLast c) x)
      (fun x => (H.vector x+tensorPolynomial (tensorMiddle c) x)+tensorPolynomial (tensorLast c) x) = _
    rw [physicalDist_add_right,physicalDist_add_right]
  have hsum := physicalDist_triangle (continuous_triple_memLp hh) (continuous_triple_memLp (tensorPolynomial_continuous c))
    (continuous_triple_memLp hKc)
  rw [hAK] at hsum
  have hh' := hsum.trans_lt (add_lt_add_of_le_of_lt hpoly hA)
  exact hh'.trans_le (by dsimp [e] at *; linarith)
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Prediction
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Laurent prediction, flat packet filling, color energies, measurable packets, reflected smoothing, and prepared pairs. -/

section

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus
section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma memLp_multiplyPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {a : UnitAddCircle → ℂ} (ha : Continuous a)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hAm : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (i : ι) :
    MemLp (multiplyPackets φ m a A i) 2 slowVolume := by
  obtain ⟨C,hC⟩ := (isCompact_range ha).isBounded.exists_norm_le
  apply (hA i).of_le_mul (measurable_multiplyPackets hφ m ha.measurable hAm i).aestronglyMeasurable
  filter_upwards [] with ua
  exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (hC _ (mem_range_self _)) (norm_nonneg _))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketLaurent_eq_multiplier (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (c : ℤ →₀ ℂ) (x : TripleTorus) :
    finitePacketLaurent φ m A c x =
      finitePacketVector m (multiplyPackets φ m (fun z => ∑ k ∈ c.support, c k*fourier k z) A) x := by
  simp only [finitePacketLaurent,finitePacketVector,Finset.mul_sum,packet_twistIter]
  simp only [multiplyPackets,packet]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

end FinitePacket
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

lemma totalVector_continuous : Continuous C.totalVector :=
  continuous_finsetSum _ (fun r _ => C.vector_continuous r)

end ColoredState
end ThreeTorus
end
end

section

/-! Literal finite measurable packet states. The spectral measure is defined
from coefficient energy, not carried as an unspecified abstract spectrum. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

attribute [instance] MeasurablePackets.finite
namespace MeasurablePackets
variable (F : MeasurablePackets)
lemma spectrum_eq [MeasurableSpace F.Index] [MeasurableSingletonClass F.Index]
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) :
    F.spectrum φ = finitePacketSpectralMeasure φ F.m F.A :=
  (finitePacketSpectralMeasure_eq_sum hφ F.m F.measurable).symm

lemma flat_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (hflat : F.spectrum φ = phaseHaar) (n : ℤ) :
    (∫ x, conj (F.vector x)*F.vector (twistIter φ n x) ∂tripleVolume) =
      if n = 0 then 1 else 0 := by
  let : MeasurableSpace F.Index := ⊤
  let : MeasurableSingletonClass F.Index := ⟨fun _ => trivial⟩
  exact finitePacket_flat_moment hφ F.injective F.measurable F.memLp
    ((F.spectrum_eq hφ).symm.trans hflat) n
end MeasurablePackets

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

/-- Approximation is chosen on the positive members only; the negative
members are their literal conjugates. Thus reality is exact, not merely AE. -/
lemma exists_reflected_slow_approx (F : MeasurablePackets)
    {τ : F.Index → F.Index} (hr : F.Reflection τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : F.Index → UnitAddCircle × UnitAddCircle → ℂ,
      (∀ i, Continuous (g i)) ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => g i (p.1,p.2))) ∧
      (∀ i p, g (τ i) p = conj (g i p)) ∧
      ∀ i, eLpNorm (fun p => F.A i p-g i p) 2 slowVolume < ENNReal.ofReal ε := by
  classical
  choose a hac has hae using fun i => exists_smooth_slow_approx (F.memLp i) hε
  let g := fun i => if 0 < F.m i then a i else fun p => conj (a (τ i) p)
  have hneg (i : F.Index) (hi : ¬ 0 < F.m i) : 0 < F.m (τ i) := by
    rw [hr.2.1]
    have hn := F.nonzero i
    omega
  refine ⟨g,?_,?_,?_,?_⟩
  · intro i
    dsimp only [g]
    split_ifs
    · exact hac i
    · exact Complex.continuous_conj.comp (hac (τ i))
  · intro i
    dsimp only [g]
    split_ifs
    · exact has i
    · exact Complex.conjCLE.contDiff.comp (has (τ i))
  · intro i p
    by_cases hi : 0 < F.m i
    · have hti : ¬ 0 < F.m (τ i) := by rw [hr.2.1]; omega
      simp [g,hi,hti,hr.1 i]
    · simp [g,hi,hneg i hi]
  · intro i
    by_cases hi : 0 < F.m i
    · simpa only [g,hi,ite_eq_left] using hae i
    · have he : (fun p => F.A i p-g i p) = fun p => conj (F.A (τ i) p-a (τ i) p) := by
        funext p
        simp [g,hi,map_sub,hr.2.2]
      rw [he]
      have hn : eLpNorm (fun p => conj (F.A (τ i) p-a (τ i) p)) 2 slowVolume =
          eLpNorm (fun p => F.A (τ i) p-a (τ i) p) 2 slowVolume :=
        eLpNorm_star
      rw [hn]
      exact hae (τ i)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

/-- Initial smoothing of the SAME supported admissible vector, with exact
reflection and arbitrarily small actual full-space L² error. -/
theorem exists_smooth_reflected_packets (F : MeasurablePackets)
    {τ : F.Index → F.Index} (hr : F.Reflection τ)
    {δ l u : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2) (hdl : δ < l) (hud : u < 1-δ)
    (hsupp : F.Supported l u)
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : PassagePackets F.Index, G.m=F.m ∧ G.V=V ∧ G.GoodArc δ ∧
      G.Reflection τ ∧ physicalDist F.vector (finitePacketVector G.m G.A) < ε := by
  classical
  obtain ⟨χ,hχs,hχc,hχI,hχb,hχ1⟩ := compact_smooth_cutoff isCompact_Icc isOpen_Ioo
    (show Icc l u ⊆ Ioo δ (1-δ) from fun x hx => ⟨hdl.trans_le hx.1,hx.2.trans_lt hud⟩)
  have hχsupp : support (fun p : ℝ × UnitAddCircle => χ p.1) ⊆ Ioo (0:ℝ) (0+1) ×ˢ univ := by
    intro p hp
    have h := hχI (subset_tsupport χ hp)
    exact ⟨⟨hδ.trans_lt h.1,by linarith [h.2]⟩,mem_univ _⟩
  have hχone : ∀ p ∈ Icc l u ×ˢ (univ : Set UnitAddCircle), χ p.1 = 1 :=
    fun p hp => (hχ1 p.1 hp.1).self_of_nhds
  have hc : (0:ℝ) < Fintype.card F.Index+1 := by positivity
  obtain ⟨C,hCc,hCs,hCr,hCe⟩ := exists_reflected_slow_approx F hr (div_pos hε hc)
  obtain ⟨G,hGm,hGV,hGd,hGA,hGA₀⟩ := exists_scalar_cutoff_packets F.m F.nonzero C
    hCc hCs hχs hχc hδ hd hχI V hVp hVs hVd
  have hGr : G.Reflection τ := scalar_packets_reflection G hGm hr.2.1 hCr hGA hGA₀
  refine ⟨G,hGm,hGV,hGd,hGr,?_⟩
  have hGl i : MemLp (G.A i) 2 slowVolume := (G.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hge i : eLpNorm (fun p => F.A i p-G.A i p) 2 slowVolume <
      ENNReal.ofReal (ε/(Fintype.card F.Index+1)) := by
    apply lt_of_le_of_lt
      (eLpNorm_mono ?_)
      (hCe i)
    intro p
    have he := cylinderTorusCutoff_fixes hχsupp (hδ.trans_lt hdl) (by linarith : u < 0+1)
      hχone (hsupp i) p
    rw [cylinderTorusCutoff_scalar] at he
    have hb := cylinderTorusCutoff_bounds hχsupp (fun p => hχb p.1) p
    rw [cylinderTorusCutoff_scalar] at hb
    calc
      _ = ‖((periodize_periodic χ).lift p.1:ℂ)*(F.A i p-C i p)‖ := by
        rw [hGA,mul_sub,he]
      _ ≤ _ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  rw [hGm]
  exact physicalDist_small_sum F.memLp hGl hε hge

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma physicalDist_zero_eq_norm {f : TripleTorus → ℂ} (hf : MemLp f 2 tripleVolume) :
    physicalDist f 0 = ‖hf.toLp f‖ := by
  rw [physicalDist_eq_norm hf MemLp.zero]
  simp

namespace MeasurablePackets
variable (F : MeasurablePackets)
lemma flat_norm {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (hflat : F.spectrum φ=phaseHaar) : physicalDist F.vector 0=1 := by
  have hm := F.flat_moment hφ hflat 0
  have hi : (∫ x, ‖F.vector x‖^2 ∂tripleVolume)=1 := by
    have he : (fun x => conj (F.vector x)*F.vector (twistIter φ 0 x)) =
        fun x => ((‖F.vector x‖^2:ℝ):ℂ) := by
      funext x
      simp only [twistIter,zero_smul,add_zero]
      exact normSq_complex (F.vector x)
    rw [he,integral_complex_ofReal] at hm
    simp only [ite_true] at hm
    exact_mod_cast hm
  have hd : physicalDist F.vector 0^2=1 := by
    rw [physicalDist_sq,physicalError]
    simpa only [Pi.zero_apply,sub_zero] using hi
  nlinarith [physicalDist_nonneg F.vector 0]

/-- Smoothing an admissible vector preserves its actual density in L1; the
constant is obtained from the SAME two physical packet vectors. -/
lemma smooth_density_distance (G : PassagePackets F.Index) (hm : G.m=F.m)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (hφG : φ=fun u => (G.periodic.lift u:UnitAddCircle)) (hflat : F.spectrum φ=phaseHaar) :
    (∫ z, |(∑ i, G.marginalDensity i z)-1| ∂phaseHaar) ≤
      (physicalDist (finitePacketVector G.m G.A) 0+1)*
        physicalDist F.vector (finitePacketVector G.m G.A) := by
  let : MeasurableSpace F.Index := ⊤
  let : MeasurableSingletonClass F.Index := ⟨fun _ => trivial⟩
  have hGl i : MemLp (G.A i) 2 slowVolume := (G.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hGp : finitePacketSpectralMeasure φ F.m G.A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (∑ i, G.marginalDensity i z)) := by
    rw [← hm,hφG]
    have hψ : Measurable (fun u => (G.periodic.lift u:UnitAddCircle)) :=
      AddCircle.measurable_mk'.comp G.speed_continuous.measurable
    exact (finitePacketSpectralMeasure_eq_sum hψ G.m (fun i => (G.continuous_amplitude i).measurable)).trans
      G.marginalDensity_sum_spectrum
  have hFp : finitePacketSpectralMeasure φ F.m F.A =
      phaseHaar.withDensity (fun _ => ENNReal.ofReal (1:ℝ)) := by
    rw [← F.spectrum_eq hφ,hflat]
    simp
  have he := finitePacket_density_distance hφ F.injective
    (fun i => (G.continuous_amplitude i).measurable) F.measurable hGl F.memLp
    (Finset.measurable_sum _ (fun i _ => G.marginalDensity_measurable i)) measurable_const
    (integrable_finsetSum _ (fun i _ => G.marginalDensity_integrable i)) (integrable_const _)
    (fun z => Finset.sum_nonneg (fun i _ => G.marginalDensity_nonneg i z)) (fun _ => zero_le_one)
    hGp hFp
  rw [← physicalDist_zero_eq_norm (memLp_finitePacketVector hGl),
    ← physicalDist_zero_eq_norm (memLp_finitePacketVector F.memLp)] at he
  change (∫ z, |(∑ i, G.marginalDensity i z)-1| ∂phaseHaar) ≤
      (physicalDist (finitePacketVector F.m G.A) 0+physicalDist F.vector 0)*
        physicalDist (finitePacketVector F.m G.A) F.vector at he
  rw [F.flat_norm hφ hflat,physicalDist_symm _ F.vector] at he
  simpa only [hm] using he
end MeasurablePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Source05's full preparation, including both slow insertions. The old
admissible vector and the test are compared in their ACTUAL common chart. -/
theorem exists_prepared_pair (F : MeasurablePackets)
    {τ : F.Index → F.Index} (hr : F.Reflection τ)
    {δ l u : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2) (hdl : δ < l) (hud : u < 1-δ)
    (hsupp : F.Supported l u)
    (V : ℝ → ℝ) (hp : Periodic V 1) (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hv : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x)
    (hflat : F.spectrum (fun z => (hp.lift z:UnitAddCircle))=phaseHaar)
    {h : TripleTorus → ℂ} (hh : Continuous h) (hrh : ∀ x, conj (h x)=h x)
    (hch : ∫ x, h x ∂tripleVolume=0) (hbh : ∀ x, ‖h x‖ ≤ 1)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ G H : RealPacketFamily, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ H.data.V=G.data.V ∧ Injective G.data.m ∧
      (∃ δ' : ℝ, 0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ G.data.GoodArc δ' ∧ H.data.GoodArc δ') ∧
      Q.Close ζ frame V frame' G.data.V ∧
      physicalDist F.vector (G.vector ∘ α) < ε ∧
      physicalDist h (H.vector ∘ α) < Real.sqrt (2*δ)+ε ∧
      (∫ z, |G.density z-1| ∂phaseHaar) < ε := by
  classical
  let e := min (ε/16) (1/16)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have heε : 16*e ≤ ε := by have := min_le_left (ε/16) (1/16); dsimp [e]; linarith
  obtain ⟨P,hPm,hPV,hPg,hPr,hPe⟩ := exists_smooth_reflected_packets F hr hδ hd hdl hud hsupp V hp hs hv he
  let P' : RealPacketFamily := ⟨F.Index,F.finite,P,τ,hr.1,hPr⟩
  have hPi : Injective P'.data.m := hPm ▸ F.injective
  have hφ : Measurable (fun z => (hp.lift z:UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (continuous_of_continuous_lift (by simpa only [Periodic.lift_coe] using hs.continuous)).measurable
  have hnorm := F.flat_norm hφ hflat
  have hPnorm : physicalDist P'.vector 0 < 1+e := by
    have ht := physicalDist_triangle P'.vector_memLp F.vector_memLp MemLp.zero
    rw [physicalDist_symm P'.vector F.vector,hnorm] at ht
    change physicalDist F.vector P'.vector < e at hPe
    linarith
  have hpD : (∫ z, |P'.density z-1| ∂phaseHaar) < 3*e := by
    have hdens := F.smooth_density_distance P hPm hφ (by
      funext z
      obtain ⟨z,rfl⟩ := Quotient.mk_surjective z
      exact congrArg (fun t : ℝ => (t:UnitAddCircle)) (congrFun hPV z).symm) hflat
    change (∫ z, |P'.density z-1| ∂phaseHaar) ≤
      (physicalDist P'.vector 0+1)*physicalDist F.vector P'.vector at hdens
    have hne : physicalDist P'.vector 0+1 < 3 := by linarith
    have hbd := mul_le_mul_of_nonneg_left hPe.le (by have := Real.sqrt_nonneg (physicalError P'.vector 0); dsimp [physicalDist]; linarith : 0 ≤ physicalDist P'.vector 0+1)
    exact hdens.trans hbd |>.trans_lt (mul_lt_mul_of_pos_right hne he)
  obtain ⟨c,hc0,hcr,H₀,hHV,hHg,hHe⟩ := exists_initial_tensor_test hh hrh hch hbh hδ hd V hp hs hv he
  obtain ⟨G,H,α,frame',hαc,hαm,hfr,hHV',hGi,hgood,hjet,hPF,hHH,hpd⟩ :=
    exists_two_slow_insertions P' H₀ hPi hδ hPg hHg (hHV.trans hPV.symm)
      c hc0 hcr Q frame he hκ hζ
  refine ⟨G,H,α,frame',hαc,hαm,hfr,hHV',hGi,hgood,?_,?_,?_,?_⟩
  · simpa only [show P'.data.V=V from hPV] using hjet
  · exact ((physicalDist_triangle F.vector_memLp P'.vector_memLp
      (continuous_triple_memLp (G.continuous_vector.comp hαc))).trans_lt
      (add_lt_add hPe hPF)).trans_le (by linarith)
  · have ht := physicalDist_triangle (continuous_triple_memLp hh)
      (continuous_triple_memLp ((H₀.continuous_vector.add (tensorPolynomial_continuous (tensorMiddle c))).add (tensorPolynomial_continuous (tensorLast c))))
      (continuous_triple_memLp (H.continuous_vector.comp hαc))
    exact (ht.trans_lt (add_lt_add hHe hHH)).trans_le (by linarith)
  · exact ((densityDist_triangle G.density_integrable P'.density_integrable (integrable_const _)).trans_lt
      (add_lt_add hpd hpD)).trans_le (by linarith)
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_CyclicPrediction
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated blocks, prediction budgets, physical Laurent polynomials, and actual cyclic approximation. -/

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Full source05 preparation through BOTH support-separating passages. The
same arbitrary tags, reality, physical errors and total density are retained. -/
theorem exists_prediction_ready (F : MeasurablePackets)
    {τ : F.Index → F.Index} (hr : F.Reflection τ)
    {δ l u : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2) (hdl : δ < l) (hud : u < 1-δ)
    (hsupp : F.Supported l u)
    (V : ℝ → ℝ) (hp : Periodic V 1) (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hv : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x)
    (hflat : F.spectrum (fun z => (hp.lift z:UnitAddCircle))=phaseHaar)
    {h : TripleTorus → ℂ} (hh : Continuous h) (hrh : ∀ x, conj (h x)=h x)
    (hch : ∫ x, h x ∂tripleVolume=0) (hbh : ∀ x, ‖h x‖ ≤ 1)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ n : ℕ, ∃ C : ColoredState (Fin n), ∃ ρ : Fin n → Fin n,
      ∃ b : Fin n → ℂ, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ Involutive ρ ∧ C.Reflection ρ ∧
      (∀ i, b (ρ i)=conj (b i)) ∧
      (∃ δ' : ℝ, 0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ C.packets.GoodArc δ') ∧
      Q.Close ζ frame V frame' C.packets.V ∧
      physicalDist F.vector (C.totalVector ∘ α) < ε ∧
      physicalDist h ((fun x => ∑ i, b i*C.vector i x) ∘ α) < Real.sqrt (2*δ)+ε ∧
      (∫ z, |blockTotal C.density z-1| ∂phaseHaar) < ε := by
  classical
  let e := min (ε/32) (1/32)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e < 1/4 := (min_le_right _ _).trans_lt (by norm_num)
  have heε : 32*e ≤ ε := by have := min_le_left (ε/32) (1/32); dsimp [e]; linarith
  obtain ⟨G,H,α,P,hαc,hαm,hP,hHV,hGi,⟨d,hd0,hd8,hdκ,hGg,hHg⟩,hjet,hFG,hHH,hpG⟩ :=
    exists_prepared_pair F hr hδ hd hdl hud hsupp V hp hs hv hflat hh hrh hch hbh Q frame he hκ (half_pos hζ)
  obtain ⟨n,R,ρ,b,hRV,hRg,hρ,hRr,hb,hdR,hGR,hHR⟩ :=
    exists_ratio_packets_for_pair G.data H.data hd0.le hGg hHg hHV G.neg H.neg
      G.invol H.invol G.reflected H.reflected he
  let R' : RealPacketFamily := ⟨Fin n,inferInstance,R,ρ,hρ,hRr⟩
  change physicalDist G.vector R'.vector < e at hGR
  change physicalDist H.vector (fun x => ∑ i, b i*packet (R.m i) (R.A i) x) < e at hHR
  have hφ : Measurable (fun z => (hp.lift z:UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (continuous_of_continuous_lift (by simpa only [Periodic.lift_coe] using hs.continuous)).measurable
  have hf1 := F.flat_norm hφ hflat
  have hnG : physicalDist G.vector 0 < 1+e := by
    have ht := physicalDist_triangle (continuous_triple_memLp (G.continuous_vector.comp hαc)) F.vector_memLp MemLp.zero
    rw [physicalDist_symm (G.vector ∘ α) F.vector,hf1] at ht
    have hz : (0 : TripleTorus → ℂ) ∘ α = 0 := rfl
    rw [← hz,physicalDist_continuous_comp α hαc hαm] at ht
    linarith
  have hnR : physicalDist R'.vector 0 < 1+2*e := by
    have ht := physicalDist_triangle R'.vector_memLp G.vector_memLp MemLp.zero
    rw [physicalDist_symm R'.vector G.vector] at ht
    change physicalDist G.vector R'.vector < e at hGR
    linarith
  have hpR : (∫ z, |R'.density z-G.density z| ∂phaseHaar) < 4*e := by
    have hh := G.data.marginalDensity_distance R hRV
      (by intro x i j hij hm; exact (hij (hGi hm)).elim)
      (R.amplitude_disjoint_of_cylinderCore hdR)
    change (∫ z, |G.density z-R'.density z| ∂phaseHaar) ≤
      (physicalDist G.vector 0+physicalDist R'.vector 0)*physicalDist G.vector R'.vector at hh
    have hnorm : physicalDist G.vector 0+physicalDist R'.vector 0 < 4 := by linarith
    have hmp := mul_le_mul_of_nonneg_left hGR.le (add_nonneg (physicalDist_nonneg G.vector 0) (physicalDist_nonneg R'.vector 0))
    simp_rw [abs_sub_comm (R'.density _) (G.density _)]
    exact (hh.trans hmp).trans_lt (mul_lt_mul_of_pos_right hnorm he)
  obtain ⟨C,β,P',hβc,hβm,hP',hCr,hgood,hjet',hRC,hRb,hpC⟩ :=
    exists_colored_separation_small R hdR ρ hρ hRr b Q P he hκ (half_pos hζ)
  have hβac : Continuous (α.trans β) := hβc.comp hαc
  have hβam : MeasurePreserving (α.trans β) tripleVolume tripleVolume := hβm.comp hαm
  have hRC' : physicalDist (R'.vector ∘ α) (C.totalVector ∘ (α.trans β)) < e := by
    change physicalDist (R'.vector ∘ α) ((C.totalVector ∘ β) ∘ α) < e
    rw [physicalDist_continuous_comp α hαc hαm]
    exact hRC
  have hGR' : physicalDist (G.vector ∘ α) (R'.vector ∘ α) < e := by
    rw [physicalDist_continuous_comp α hαc hαm]
    exact hGR
  have hHC' : physicalDist (H.vector ∘ α)
      ((fun x => ∑ i, b i*C.vector i x) ∘ (α.trans β)) < 2*e := by
    have htag : Continuous (fun x => ∑ i, b i*packet (R.m i) (R.A i) x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_packet (R.continuous_amplitude i)))
    have hctag : Continuous (fun x => ∑ i, b i*C.vector i x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (C.vector_continuous i))
    change physicalDist (H.vector ∘ α) (((fun x => ∑ i, b i*C.vector i x) ∘ β) ∘ α) < 2*e
    rw [physicalDist_continuous_comp α hαc hαm]
    exact (physicalDist_triangle H.vector_memLp (continuous_triple_memLp htag)
      (continuous_triple_memLp (hctag.comp hβc))).trans_lt (by linarith)
  refine ⟨n,C,ρ,b,α.trans β,P',hβac,hβam,?_,hρ,hCr,hb,hgood,?_,?_,?_,?_⟩
  · rw [hP',hP]; rfl
  · rw [hRV] at hjet'
    exact (hjet.trans hjet').mono (by linarith)
  · have ht := physicalDist_triangle (continuous_triple_memLp (G.continuous_vector.comp hαc))
      (continuous_triple_memLp (R'.continuous_vector.comp hαc))
      (continuous_triple_memLp (C.totalVector_continuous.comp hβac))
    have ht' := physicalDist_triangle F.vector_memLp (continuous_triple_memLp (G.continuous_vector.comp hαc))
      (continuous_triple_memLp (C.totalVector_continuous.comp hβac))
    linarith
  · have hctag : Continuous (fun x => ∑ i, b i*C.vector i x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (C.vector_continuous i))
    have ht := physicalDist_triangle (continuous_triple_memLp hh) (continuous_triple_memLp (H.continuous_vector.comp hαc))
      (continuous_triple_memLp (hctag.comp hβac))
    linarith
  · have hpCi : Integrable (blockTotal C.density) phaseHaar :=
      integrable_finsetSum _ (fun i _ => (C.density_continuous i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have ht := densityDist_triangle hpCi R'.density_integrable G.density_integrable
    have ht' := densityDist_triangle hpCi G.density_integrable (integrable_const (1:ℝ))
    change (∫ z, |blockTotal C.density z-R'.density z| ∂phaseHaar) < e at hpC
    linarith
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Stages
attribute [-instance] _root_.OAI.ThreeTorus.PhysicalTest.instNonempty _root_.OAI.ThreeTorus.PhysicalTest.instSecondCountableTopology _root_.OAI.ThreeTorus.PhysicalTest.instTopologicalSpace _root_.OAI.ThreeTorus.StageState.instTopologicalSpace _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good-arc flattening, exact predicted whitening, unconditional one-stage construction, and stage states and successors. -/

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma MeasurablePackets.laurent_memLp (W : MeasurablePackets)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) (c : ℤ →₀ ℂ) :
    MemLp (finitePacketLaurent φ W.m W.A c) 2 tripleVolume := by
  have he : finitePacketLaurent φ W.m W.A c = finitePacketVector W.m
      (multiplyPackets φ W.m (fun z => ∑ k ∈ c.support, c k*fourier k z) W.A) :=
    funext (finitePacketLaurent_eq_multiplier φ W.m W.A c)
  rw [he]
  apply memLp_finitePacketVector
  exact memLp_multiplyPackets hφ W.m (continuous_finsetSum _
    (fun k _ => continuous_const.mul (fourier k).continuous)) W.measurable W.memLp

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- The unconditional one-stage producer (source05 Proposition `stage`). All
packets, tags, two separations, actual prediction and whitening are constructed.
The three tolerances are independent; finite physical jets include both signs. -/
theorem exists_one_stage (F : MeasurablePackets)
    {τ : F.Index → F.Index} (hr : F.Reflection τ)
    {δ l u : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2) (hdl : δ < l) (hud : u < 1-δ)
    (hsupp : F.Supported l u)
    (V : ℝ → ℝ) (hp : Periodic V 1) (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hv : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x)
    (hflat : F.spectrum (fun z => (hp.lift z:UnitAddCircle))=phaseHaar)
    {h : TripleTorus → ℂ} (hh : Continuous h) (hrh : ∀ x, conj (h x)=h x)
    (hch : ∫ x, h x ∂tripleVolume=0) (hbh : ∀ x, ‖h x‖ ≤ 1)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε η κ ζ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ W : MeasurablePackets, ∃ V' : ℝ → ℝ, ∃ hp' : Periodic V' 1,
      ∃ _hs' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V',
      ∃ δ' l' u' : ℝ, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame, ∃ c : ℤ →₀ ℂ,
      0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ δ' < l' ∧ l' < u' ∧ u' < 1-δ' ∧
      (∀ x ∈ Ioo δ' (1-δ'), 0 < deriv V' x) ∧ W.Supported l' u' ∧
      (∃ τ', W.Reflection τ') ∧ W.spectrum (fun z => (hp'.lift z:UnitAddCircle))=phaseHaar ∧
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ Q.Close ζ frame V frame' V' ∧
      physicalDist F.vector (W.vector ∘ α) < ε ∧
      physicalDist h (finitePacketLaurent (fun z => (hp'.lift z:UnitAddCircle)) W.m W.A c ∘ α)
        < Real.sqrt (2*δ)+η := by
  let r := min (ε/8) (1/8)
  have hr0 : 0 < r := lt_min (by positivity) (by norm_num)
  have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hrε : 8*r ≤ ε := by have := min_le_left (ε/8) (1/8); dsimp [r]; linarith
  let e := min ((r^2/64)^2) (min (η/4) (r/4))
  have he : 0 < e := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have her : e ≤ (r^2/64)^2 := min_le_left _ _
  have heη : e ≤ η/4 := (min_le_right _ _).trans (min_le_left _ _)
  have her' : e ≤ r/4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n,C,ρ,b,α,P,hαc,hαm,hP,hρ,hCr,hb,hgood,hjet,hFC,hHC,hpC⟩ :=
    exists_prediction_ready F hr hδ hd hdl hud hsupp V hp hs hv hflat hh hrh hch hbh Q frame he hκ (half_pos hζ)
  obtain ⟨W,V',hp',hs',δ',l',u',β,P',c,hδ',hδ8,hδκ,hdl',hlu',hud',hv',hWs,hWr,hWflat,
    hβc,hβm,hP',hjet',hCW,hHW⟩ := exists_predicted_whitening C ρ hρ hCr b hb Q P he hr0 hr1 her
      (half_pos hη) hκ (half_pos hζ) hpC
  have hβαc : Continuous (α.trans β) := hβc.comp hαc
  have hβαm : MeasurePreserving (α.trans β) tripleVolume tripleVolume := hβm.comp hαm
  have hφ : Measurable (fun z => (hp'.lift z:UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (continuous_of_continuous_lift (by simpa only [Periodic.lift_coe] using hs'.continuous)).measurable
  refine ⟨W,V',hp',hs',δ',l',u',α.trans β,P',c,hδ',hδ8,hδκ,hdl',hlu',hud',hv',hWs,hWr,
    hWflat,hβαc,hβαm,?_,(hjet.trans hjet').mono (by linarith),?_,?_⟩
  · rw [hP',hP]; rfl
  · have ht := physicalDist_triangle F.vector_memLp
      (continuous_triple_memLp (C.totalVector_continuous.comp hαc))
      (W.vector_memLp.comp_measurePreserving hβαm)
    have hCW' : physicalDist (C.totalVector ∘ α) (W.vector ∘ (α.trans β)) < e+r := by
      change physicalDist (C.totalVector ∘ α) ((W.vector ∘ β) ∘ α) < e+r
      rw [physicalDist_continuous_comp α hαc hαm]
      exact hCW
    linarith
  · have hctag : Continuous (fun x => ∑ i, b i*C.vector i x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (C.vector_continuous i))
    have hHW' : physicalDist ((fun x => ∑ i, b i*C.vector i x) ∘ α)
        (finitePacketLaurent (fun z => (hp'.lift z:UnitAddCircle)) W.m W.A c ∘ (α.trans β)) < η/2 := by
      change physicalDist ((fun x => ∑ i, b i*C.vector i x) ∘ α)
        ((finitePacketLaurent (fun z => (hp'.lift z:UnitAddCircle)) W.m W.A c ∘ β) ∘ α) < η/2
      rw [physicalDist_continuous_comp α hαc hαm]
      exact hHW
    have ht := physicalDist_triangle (continuous_triple_memLp hh)
      (continuous_triple_memLp (hctag.comp hαc))
      ((W.laurent_memLp hφ c).comp_measurePreserving hβαm)
    linarith
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace StageState
variable (s : StageState)
lemma vec_ae : s.vec =ᵐ[tripleVolume] s.vector := MemLp.coeFn_toLp _

lemma mapPow_apply (k : ℤ) (x : TripleTorus) :
    s.mapPow k x = s.frame.chart.symm (twistIter s.speed k (s.frame.chart x)) := by
  rfl
lemma orbit_ae (k : ℤ) : s.orbit k =ᵐ[tripleVolume] fun x => s.vector (s.mapPow k x) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving s.vec (s.mapPow_mp k),
    (s.mapPow_mp k).quasiMeasurePreserving.ae s.vec_ae] with x hx hy
  exact hx.trans hy

lemma laurent_ae (c : ℤ →₀ ℂ) : s.laurent c =ᵐ[tripleVolume]
    finitePacketLaurent s.speed s.packets.m s.packets.A c ∘ s.frame.chart := by
  classical
  have ha := ae_all_iff.mpr (fun k => s.orbit_ae k)
  filter_upwards [Lp.coeFn_finsetSum (c.support) (fun k => c k • s.orbit k),ha,
    ae_all_iff.mpr (fun k => Lp.coeFn_smul (c k) (s.orbit k))] with x hx hy hz
  change (∑ k ∈ c.support, c k • s.orbit k) x = _ at hx ⊢
  rw [hx]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hz,hy,vector,mapPow_apply,
    Function.comp_apply,s.frame.chart.apply_symm_apply,finitePacketLaurent,MeasurablePackets.vector]

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace PhysicalTest
variable (h : PhysicalTest)
lemma vec_ae : h.vec =ᵐ[tripleVolume] h.fn := MemLp.coeFn_toLp _
end PhysicalTest

lemma physicalDist_reps {f g : TripleTorus → ℂ} {F G : StageState.L2}
    (hf : F =ᵐ[tripleVolume] f) (hg : G =ᵐ[tripleVolume] g) :
    physicalDist f g = dist F G := by
  have hfl : MemLp f 2 tripleVolume := (Lp.memLp F).ae_eq hf
  have hgl : MemLp g 2 tripleVolume := (Lp.memLp G).ae_eq hg
  have hF : hfl.toLp f=F := Lp.ext (hfl.coeFn_toLp.trans hf.symm)
  have hG : hgl.toLp g=G := Lp.ext (hgl.coeFn_toLp.trans hg.symm)
  rw [physicalDist_eq_norm hfl hgl,hF,hG,dist_eq_norm]

namespace StageState
/-- The already proved stage producer, transferred to the SAME global physical
coordinates. Real tests are pulled back only to apply that producer. -/
theorem exists_step_oai (s : StageState) (h : PhysicalTest) (Q : PhysicalJetData)
    {ε η κ ζ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ t : StageState, ∃ c : ℤ →₀ ℂ,
      t.δ < κ ∧ Q.Close ζ s.frame s.V t.frame t.V ∧
      dist s.vec t.vec < ε ∧ dist h.vec (t.laurent c) < Real.sqrt (2*s.δ)+η := by
  obtain ⟨τ,hr⟩ := s.reflected
  let h' := h.fn ∘ s.frame.chart.symm
  have hc : Continuous h' := h.fn.continuous.comp s.chart_symm_cont
  have hcen : ∫ x, h' x ∂tripleVolume=0 := by
    change ∫ x, h.fn (s.frame.chart.symm x) ∂tripleVolume=0
    rw [s.chart_symm_mp.integral_comp s.chartHomeo.symm.toMeasurableEquiv.measurableEmbedding,h.centered]
  obtain ⟨W,V,hp,hs,δ,l,u,α,P,c,hδ,hδ8,hδκ,hdl,hlu,hud,hv,hWs,hWr,hflat,
    hαc,hαm,hP,hjet,hFW,hHW⟩ := exists_one_stage s.packets hr s.δ_pos.le s.δ_half
      s.δ_l s.u_δ s.supported s.V s.periodic s.smooth s.increasing s.flat hc
      (fun x => h.real _) hcen (fun x => h.bound _) Q s.frame hε hη hκ hζ
  have hPc : Continuous P.chart := by
    rw [hP]; exact hαc.comp s.chart_cont
  have hPm : MeasurePreserving P.chart tripleVolume tripleVolume := by
    rw [hP]; exact hαm.comp s.chart_mp
  let t : StageState := {
    frame := P, chart_cont := hPc, chart_mp := hPm, packets := W,
    reflected := hWr, V := V, periodic := hp, smooth := hs,
    δ := δ, l := l, u := u, δ_pos := hδ, δ_half := by linarith,
    δ_l := hdl, l_u := hlu, u_δ := hud, increasing := hv, supported := hWs, flat := hflat }
  refine ⟨t,c,hδκ,hjet,?_,?_⟩
  · rw [← physicalDist_reps s.vec_ae t.vec_ae]
    change physicalDist (s.packets.vector ∘ s.frame.chart) (W.vector ∘ P.chart) < ε
    rw [hP]
    change physicalDist (s.packets.vector ∘ s.frame.chart) ((W.vector ∘ α) ∘ s.frame.chart) < ε
    rw [physicalDist_continuous_comp s.frame.chart s.chart_cont s.chart_mp]
    exact hFW
  · rw [← physicalDist_reps h.vec_ae (t.laurent_ae c)]
    change physicalDist h.fn (finitePacketLaurent (fun z => (hp.lift z:UnitAddCircle)) W.m W.A c ∘ P.chart) < _
    rw [hP]
    have he : (h.fn : TripleTorus → ℂ)=h' ∘ s.frame.chart := by
      funext x; exact congrArg h.fn (s.frame.chart.symm_apply_apply x).symm
    rw [he]
    change physicalDist (h' ∘ s.frame.chart)
      ((finitePacketLaurent (fun z => (hp.lift z:UnitAddCircle)) W.m W.A c ∘ α) ∘ s.frame.chart) < _
    rw [physicalDist_continuous_comp s.frame.chart s.chart_cont s.chart_mp]
    exact hHW

end StageState
end ThreeTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.StageState.exists_step_oai := @OAI.ThreeTorus.StageState.exists_step_oai
