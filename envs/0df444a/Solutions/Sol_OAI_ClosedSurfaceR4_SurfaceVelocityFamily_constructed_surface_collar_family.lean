-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:49:55.825228+00:00
-- url     : https://prove2.me/submissions/0d9cd9bb-74f8-4d3c-a96e-bd27e0a7d83d

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_OAIQ249SI007
import Definitions.Def_OAIQ249SI009
import Theorems.Thm_OAI_ClosedSurfaceR4_CollarVelocity_small_shift_collar_density

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma contDiff_realTwoJet {F : RField 4} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (realTwoJet F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CompactSmoothCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested compact cutoffs in finite-dimensional parameter spaces. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.CollarVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma supported_local_mul {χ f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hn : x ∉ tsupport χ := fun h => hx (hs h)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    exact (congrArg (fun t : ℝ => t * f y) hy).trans (zero_mul _)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedScalarQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth supported quotient only requires a nonzero denominator on its support. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma supported_quotient_smooth {χ d : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hd : ContDiff ℝ ∞ d)
    (hne : ∀ x ∈ tsupport χ, d x ≠ 0) :
    ContDiff ℝ ∞ (fun x => χ x / d x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.div hd.contDiffAt (hne x hx)
  · have hz : χ =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hx
    have he : (fun y => χ y / d y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hz] with y hy
      rw [hy, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq he

omit [NormedSpace ℝ E] in
lemma supported_quotient_support (χ d : E → ℝ) :
    tsupport (fun x => χ x / d x) ⊆ tsupport χ := by
  simpa only [div_eq_mul_inv] using
    (tsupport_mul_subset_left (f := χ) (g := fun x => (d x)⁻¹))

omit [NormedSpace ℝ E] in
lemma supported_quotient_compact {χ d : E → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (fun x => χ x / d x) := by
  exact hχ.of_isClosed_subset (isClosed_tsupport _) (supported_quotient_support χ d)

omit [NormedSpace ℝ E] in
lemma supported_quotient_cancel {χ d : E → ℝ}
    (hne : ∀ x ∈ tsupport χ, d x ≠ 0) (x : E) : (χ x / d x) * d x = χ x := by
  by_cases hd : d x = 0
  · have hx : x ∉ tsupport χ := fun h => hne x h hd
    rw [image_eq_zero_of_notMem_tsupport hx, zero_div, zero_mul]
  · exact div_mul_cancel₀ _ hd

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseSmallFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A narrow transverse correction with arbitrarily small values and a fixed first jet. -/
noncomputable section
open Set Metric
open scoped ContDiff

namespace ClosedSurfaceR4.TransverseSmallFunction

lemma cutoff_zero : cutoff 0 = 1 :=
  cutoff.one_of_mem_closedBall (mem_closedBall_self cutoff.rIn_pos.le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma correction_smooth {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (δ : ℝ) :
    ContDiff ℝ ∞ (correction f g δ) :=
  (hf.mul hg).mul (cutoff.contDiff.comp (hf.div_const δ))

/-- At the defining curve the cutoff introduces no change in the prescribed first jet. -/
lemma correction_hasFDerivAt {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hf0 : f x = 0) (δ : ℝ) :
    HasFDerivAt (correction f g δ) (g x • fderiv ℝ f x) x := by
  have hcd : Differentiable ℝ (cutoff : ℝ → ℝ) :=
    (cutoff.contDiff : ContDiff ℝ ∞ (cutoff : ℝ → ℝ)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdiv : DifferentiableAt ℝ (fun y => f y / δ) x := by
    simpa only [div_eq_mul_inv] using hf.mul_const δ⁻¹
  have hc : DifferentiableAt ℝ (fun y => cutoff (f y / δ)) x :=
    DifferentiableAt.comp x (g := (cutoff : ℝ → ℝ)) (f := fun y => f y / δ)
      (hcd (f x / δ)) hdiv
  have hd := (hf.hasFDerivAt.mul hg.hasFDerivAt).mul hc.hasFDerivAt
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Pi.mul_apply, hf0, zero_div, cutoff_zero, zero_mul, zero_smul, zero_add, one_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma correction_abs_le {f g : E → ℝ} {δ G : ℝ} (hδ : 0 < δ) (hG : 0 ≤ G)
    (hg : ∀ x, |g x| ≤ G) (x : E) : |correction f g δ x| ≤ δ * G := by
  by_cases hz : cutoff (f x / δ) = 0
  · simp only [correction, hz, mul_zero, abs_zero]
    exact mul_nonneg hδ.le hG
  have hmem : f x / δ ∈ ball (0 : ℝ) cutoff.rOut := by
    rw [← cutoff.support_eq]
    exact hz
  have hr : |f x / δ| < 1 := by
    change dist (f x / δ) 0 < 1 at hmem
    simpa only [Real.dist_eq, sub_zero] using hmem
  have hf : |f x| ≤ δ := by
    rw [abs_div, abs_of_pos hδ] at hr
    exact ((div_lt_one hδ).mp hr).le
  have hc : |cutoff (f x / δ)| ≤ 1 := by
    rw [abs_of_nonneg cutoff.nonneg]
    exact cutoff.le_one
  calc
    |correction f g δ x| = |f x| * |g x| * |cutoff (f x / δ)| := by
      simp only [correction, abs_mul]
    _ ≤ δ * G * 1 := mul_le_mul (mul_le_mul hf (hg x) (abs_nonneg _) hδ.le)
      hc (abs_nonneg _) (mul_nonneg hδ.le hG)
    _ = δ * G := mul_one _

omit [NormedSpace ℝ E] in
lemma correction_support (f g : E → ℝ) (δ : ℝ) :
    tsupport (correction f g δ) ⊆ tsupport g := by
  change tsupport ((f * g) * (fun x => cutoff (f x / δ))) ⊆ tsupport g
  exact tsupport_mul_subset_left.trans tsupport_mul_subset_right

/-- Narrowing the support in the defining-function direction makes the value
arbitrarily small without changing any prescribed derivative along its zero set. -/
theorem exists_small_correction {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {G ε : ℝ} (hG : 0 ≤ G) (hgb : ∀ x, |g x| ≤ G) (hε : 0 < ε) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ tsupport H ⊆ tsupport g ∧
      (∀ x, |H x| < ε) ∧
      ∀ x, f x = 0 → fderiv ℝ H x = g x • fderiv ℝ f x := by
  let δ := ε / (G + 1)
  have hden : 0 < G + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδG : δ * G < ε := by
    change ε / (G + 1) * G < ε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  refine ⟨correction f g δ, correction_smooth hf hg δ, correction_support f g δ,
    (fun x => lt_of_le_of_lt (correction_abs_le hδ hG hgb x) hδG), ?_⟩
  intro x hx
  exact (correction_hasFDerivAt (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
    (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x) hx δ).fderiv

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseFinitePatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite patching of narrow corrections along defining curves. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.TransverseSmallFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem finite_small_correction {f g : ι → E → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hgc : ∀ i, HasCompactSupport (g i)) {K : Set E}
    (hz : ∀ i x, x ∈ K → x ∈ tsupport (g i) → f i x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ ⋃ i, tsupport (g i) ∧ (∀ x, |H x| < ε) ∧
      ∀ x ∈ K, fderiv ℝ H x = ∑ i, g i x • fderiv ℝ (f i) x := by
  classical
  let e := ε / ((Fintype.card ι : ℝ) + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have he : 0 < e := div_pos hε hden
  have hbound (i : ι) : ∃ G : ℝ, 0 ≤ G ∧ ∀ x, |g i x| ≤ G := by
    obtain ⟨A, hA⟩ := (hg i).continuous.bounded_above_of_compact_support (hgc i)
    refine ⟨max 0 A, le_max_left _ _, ?_⟩
    intro x
    have hx : |g i x| ≤ A := by simpa only [Real.norm_eq_abs] using hA x
    exact hx.trans (le_max_right _ _)
  choose G hG hb using hbound
  choose H hH hHs hHe hHd using fun i => exists_small_correction (hf i) (hg i) (hG i) (hb i) he
  let F : E → ℝ := fun x => ∑ i, H i x
  have hFs : tsupport F ⊆ ⋃ i, tsupport (g i) := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      have hn (i : ι) : x ∉ tsupport (H i) := by
        intro hh
        exact hnot (mem_iUnion.mpr ⟨i, hHs i hh⟩)
      have hFx : F x = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact image_eq_zero_of_notMem_tsupport (hn i)
      exact hx hFx
    · exact isClosed_iUnion_of_finite (fun i => isClosed_tsupport (g i))
  have hFc : HasCompactSupport F :=
    (isCompact_iUnion fun i => hgc i).of_isClosed_subset (isClosed_tsupport F) hFs
  refine ⟨F, ContDiff.sum (fun i _ => hH i), hFc, hFs, ?_, ?_⟩
  · intro x
    have hsum : |F x| ≤ (Fintype.card ι : ℝ) * e := by
      calc
        |F x| ≤ ∑ i, |H i x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : ι, e := Finset.sum_le_sum (fun i _ => (hHe i x).le)
        _ = (Fintype.card ι : ℝ) * e := by simp
    apply lt_of_le_of_lt hsum
    change (Fintype.card ι : ℝ) * (ε / ((Fintype.card ι : ℝ) + 1)) < ε
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  · intro x hx
    change fderiv ℝ (fun y => ∑ i, H i y) x = _
    rw [fderiv_fun_sum (fun i _ => (hH i).differentiable (by simp) x)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hgi : x ∈ tsupport (g i)
    · exact hHd i x (hz i x hx hgi)
    · have hHi : x ∉ tsupport (H i) := fun hh => hgi (hHs i hh)
      rw [fderiv_of_notMem_tsupport ℝ hHi, image_eq_zero_of_notMem_tsupport hgi, zero_smul]

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PrescribedTransverseDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prescribe a transverse derivative using actual defining functions and smooth cutoffs. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.TransverseSmallFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem exists_prescribed_transverse_derivative
    {f χ : ι → E → ℝ} {T : E → ℝ} {K : Set E} (v : E)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i)) (hT : ContDiff ℝ ∞ T)
    (hden : ∀ i x, x ∈ tsupport (χ i) → fderiv ℝ (f i) x v ≠ 0)
    (hzero : ∀ i x, x ∈ K → x ∈ tsupport (χ i) → f i x = 0)
    (hpartition : ∀ x ∈ K, T x ≠ 0 → (∑ i, χ i x) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ ⋃ i, tsupport (χ i) ∧ (∀ x, |H x| < ε) ∧
      ∀ x ∈ K, fderiv ℝ H x v = T x := by
  let d : ι → E → ℝ := fun i x => fderiv ℝ (f i) x v
  let g : ι → E → ℝ := fun i x => (χ i x * T x) / d i x
  have hd (i : ι) : ContDiff ℝ ∞ (d i) :=
    ((hf i).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hsupp (i : ι) : tsupport (g i) ⊆ tsupport (χ i) := by
    exact (supported_quotient_support (fun x => χ i x * T x) (d i)).trans
      tsupport_mul_subset_left
  have hg (i : ι) : ContDiff ℝ ∞ (g i) := by
    apply supported_quotient_smooth ((hχ i).mul hT) (hd i)
    intro x hx
    exact hden i x (tsupport_mul_subset_left hx)
  have hgc (i : ι) : HasCompactSupport (g i) :=
    supported_quotient_compact (hχc i |>.mul_right)
  have hcoef (i : ι) (x : E) : g i x * d i x = χ i x * T x := by
    exact supported_quotient_cancel (χ := fun y => χ i y * T y) (d := d i)
      (fun y hy => hden i y (tsupport_mul_subset_left hy)) x
  obtain ⟨H, hH, hHc, hHs, hHsmall, hHd⟩ := finite_small_correction hf hg hgc
    (fun i x hx hs => hzero i x hx (hsupp i hs)) hε
  refine ⟨H, hH, hHc, hHs.trans (iUnion_mono hsupp), hHsmall, ?_⟩
  intro x hx
  rw [hHd x hx]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  change (∑ i, g i x * d i x) = T x
  simp_rw [hcoef]
  rw [← Finset.sum_mul]
  by_cases hTx : T x = 0
  · simp [hTx]
  · rw [hpartition x hx hTx, one_mul]

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CompactTransverseCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact transverse correction from local defining functions, with the cutoffs constructed. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.TransverseSmallFunction

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Local defining functions on the support of the desired derivative suffice. -/
theorem compact_transverse_correction {K O : Set E} {T : E → ℝ} (v : E)
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hT : ContDiff ℝ ∞ T)
    (hlocal : ∀ p ∈ K ∩ tsupport T, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ (∀ x ∈ K ∩ U, f x = 0) ∧
        ∀ x ∈ U, fderiv ℝ f x v ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ O ∧
      (∀ x, |H x| < ε) ∧ ∀ x ∈ K, fderiv ℝ H x v = T x := by
  classical
  let I := {p : E // p ∈ K ∩ tsupport T}
  have hl (p : I) := hlocal p.val p.property
  choose U hU hpU f hf hzero hden using hl
  let W : I → Set E := fun p => (U p ∩ O) ∩ Metric.ball p.val 1
  have hW (p : I) : IsOpen (W p) := ((hU p).inter hO).inter Metric.isOpen_ball
  have hpW (p : I) : p.val ∈ W p :=
    ⟨⟨hpU p, hKO p.property.1⟩, Metric.mem_ball_self zero_lt_one⟩
  have hcover : K ∩ tsupport T ⊆ ⋃ p : I, W p := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpW ⟨x, hx⟩⟩
  have hC : IsCompact (K ∩ tsupport T) := hK.inter_right (isClosed_tsupport T)
  obtain ⟨J, hJ⟩ := hC.elim_finite_subcover W hW hcover
  have hcJ : K ∩ tsupport T ⊆ ⋃ p : J, W p.val := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨χ, hχs⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, E))
    hC.isClosed (fun p : J => W p.val) (fun p => hW p.val) hcJ
  have hχ (p : J) : ContDiff ℝ ∞ (χ p) := (χ p).contMDiff.contDiff
  have hχc (p : J) : HasCompactSupport (χ p) := by
    apply (isCompact_closedBall p.val.val 1).of_isClosed_subset (isClosed_tsupport _)
    intro x hx
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp (hχs p hx).2).le
  obtain ⟨H, hH, hHc, hHs, hHb, hHd⟩ := exists_prescribed_transverse_derivative
    (f := fun p : J => f p.val) (χ := fun p : J => χ p) (K := K) v
    (fun p => hf p.val) hχ hχc hT
    (fun p x hx => hden p.val x (hχs p hx).1.1)
    (fun p x hx hs => hzero p.val x ⟨hx, (hχs p hs).1.1⟩)
    (fun x hx hTx => by
      simpa only [finsum_eq_sum_of_fintype] using
        χ.sum_eq_one ⟨hx, subset_tsupport T (Function.mem_support.mpr hTx)⟩) hε
  refine ⟨H, hH, hHc, ?_, hHb, hHd⟩
  intro x hx
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hHs hx)
  exact (hχs p hp).1.2

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SpecialPointCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small affine bumps prescribe the vertical derivative near an isolated special point. -/
noncomputable section
open Filter Set Metric
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

lemma pointCorrection_smooth (p : Base) (φ : ContDiffBump p) (B : ℝ) :
    ContDiff ℝ ∞ (pointCorrection p φ B) :=
  (contDiff_const.mul (contDiff_snd.sub contDiff_const)).mul φ.contDiff

lemma pointCorrection_support (p : Base) (φ : ContDiffBump p) (B : ℝ) :
    tsupport (pointCorrection p φ B) ⊆ closedBall p φ.rOut := by
  rw [← φ.tsupport_eq]
  exact tsupport_mul_subset_right

lemma pointCorrection_compact (p : Base) (φ : ContDiffBump p) (B : ℝ) :
    HasCompactSupport (pointCorrection p φ B) := by
  exact φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    (by rw [φ.tsupport_eq]; exact pointCorrection_support p φ B)

lemma pointCorrection_derivative {p x : Base} (φ : ContDiffBump p) (B : ℝ)
    (hx : x ∈ ball p φ.rIn) :
    fderiv ℝ (pointCorrection p φ B) x (0, 1) = B := by
  have he : pointCorrection p φ B =ᶠ[𝓝 x] (fun y : Base => B * (y.2 - p.2)) := by
    filter_upwards [φ.eventuallyEq_one_of_mem_ball hx] with y hy
    simp only [pointCorrection, hy, Pi.one_apply, mul_one]
  rw [he.fderiv_eq]
  have hd : HasFDerivAt (fun y : Base => B * (y.2 - p.2))
      (B • (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (hasFDerivAt_snd.sub_const p.2).const_mul B
  rw [hd.fderiv]
  simp

lemma pointCorrection_abs_le (p : Base) (φ : ContDiffBump p) (B : ℝ) (x : Base) :
    |pointCorrection p φ B x| ≤ |B| * φ.rOut := by
  by_cases hz : φ x = 0
  · simp only [pointCorrection, hz, mul_zero, abs_zero]
    exact mul_nonneg (abs_nonneg _) φ.rOut_pos.le
  have hmem : x ∈ ball p φ.rOut := by
    rw [← φ.support_eq]
    exact hz
  have hdist : dist x p < φ.rOut := hmem
  have hcoord : |x.2 - p.2| ≤ dist x p := by
    simpa only [dist_eq_norm, Prod.snd_sub, Real.norm_eq_abs] using norm_snd_le (x - p)
  have hφ : |φ x| ≤ 1 := by rw [abs_of_nonneg φ.nonneg]; exact φ.le_one
  calc
    |pointCorrection p φ B x| = |B| * |x.2 - p.2| * |φ x| := by simp only [pointCorrection, abs_mul]
    _ ≤ |B| * φ.rOut * 1 := mul_le_mul (mul_le_mul_of_nonneg_left
      (hcoord.trans hdist.le) (abs_nonneg B)) hφ (abs_nonneg _)
        (mul_nonneg (abs_nonneg B) φ.rOut_pos.le)
    _ = |B| * φ.rOut := mul_one _

theorem exists_special_point_correction {p : Base} {U : Set Base}
    (hU : IsOpen U) (hpU : p ∈ U) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Base → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ U ∧
      (∀ x, |H x| < ε) ∧ ∃ V : Set Base, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, fderiv ℝ H x (0, 1) = B := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU p hpU
  let δ := min (r / 2) (ε / (|B| + 1))
  have hden : 0 < |B| + 1 := by positivity
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hε hden)
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let φ : ContDiffBump p := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hball : closedBall p δ ⊆ U := by
    intro x hx
    exact hrU ((mem_ball).mpr (lt_of_le_of_lt hx hδr))
  have hsmall : |B| * δ < ε := by
    have hb : |B| * (ε / (|B| + 1)) < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).mpr
      nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg B)) hb
  refine ⟨pointCorrection p φ B, pointCorrection_smooth p φ B,
    pointCorrection_compact p φ B, (pointCorrection_support p φ B).trans hball,
    (fun x => lt_of_le_of_lt (pointCorrection_abs_le p φ B x) hsmall),
    ball p φ.rIn, isOpen_ball, mem_ball_self φ.rIn_pos, ?_, ?_⟩
  · exact (ball_subset_closedBall.trans (closedBall_subset_closedBall φ.rIn_lt_rOut.le)).trans hball
  · exact fun x hx => pointCorrection_derivative φ B hx

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSpecialPointCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous small affine corrections around finitely many distinct special points. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.TransverseSmallFunction

theorem exists_finite_special_correction {ι : Type*} [Fintype ι]
    (p : ι → Base) (hp : Function.Injective p) {U : Set Base}
    (hU : IsOpen U) (hpU : ∀ i, p i ∈ U) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Base → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ U ∧
      (∀ x, |H x| < ε) ∧ ∃ V : Set Base, IsOpen V ∧ (∀ i, p i ∈ V) ∧ V ⊆ U ∧
        ∀ x ∈ V, fderiv ℝ H x (0, 1) = B := by
  classical
  obtain ⟨W, hW, hdisj⟩ := (Set.finite_range p).t2_separation
  let e := ε / ((Fintype.card ι : ℝ) + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have he : 0 < e := div_pos hε hden
  have hlocal (i : ι) := exists_special_point_correction
    ((hW (p i)).2.inter hU) ⟨(hW (p i)).1, hpU i⟩ B he
  choose H hH hHc hHs hHb V hVo hpV hVU hVD using hlocal
  let F : Base → ℝ := fun x => ∑ i, H i x
  have hFs : tsupport F ⊆ ⋃ i, tsupport (H i) := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      have hz : F x = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact image_eq_zero_of_notMem_tsupport (fun hi => hnot (mem_iUnion.mpr ⟨i, hi⟩))
      exact hx hz
    · exact isClosed_iUnion_of_finite (fun i => isClosed_tsupport (H i))
  have hFc : HasCompactSupport F :=
    (isCompact_iUnion (fun i => hHc i)).of_isClosed_subset (isClosed_tsupport F) hFs
  have hFU : tsupport F ⊆ U := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hFs hx)
    exact (hHs i hi).2
  refine ⟨F, ContDiff.sum (fun i _ => hH i), hFc, hFU, ?_, ⋃ i, V i,
    isOpen_iUnion hVo, (fun i => mem_iUnion.mpr ⟨i, hpV i⟩), ?_, ?_⟩
  · intro x
    have hsum : |F x| ≤ (Fintype.card ι : ℝ) * e := by
      calc
        |F x| ≤ ∑ i, |H i x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : ι, e := Finset.sum_le_sum (fun i _ => (hHb i x).le)
        _ = (Fintype.card ι : ℝ) * e := by simp
    apply lt_of_le_of_lt hsum
    change (Fintype.card ι : ℝ) * (ε / ((Fintype.card ι : ℝ) + 1)) < ε
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hVU i hi).2
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    change fderiv ℝ (fun y => ∑ j, H j y) x (0, 1) = B
    rw [fderiv_fun_sum (fun j _ => (hH j).differentiable (by simp) x), sum_apply]
    rw [Finset.sum_eq_single i]
    · exact hVD i x hi
    · intro j _ hji
      have hxWi : x ∈ W (p i) := (hVU i hi).1
      have hd : Disjoint (W (p i)) (W (p j)) :=
        hdisj (mem_range_self i) (mem_range_self j) (fun hij => hji (hp hij).symm)
      have hnot : x ∉ tsupport (H j) := fun hh =>
        (Set.disjoint_left.mp hd) hxWi (hHs j hh).1
      rw [fderiv_of_notMem_tsupport ℝ hnot]
      rfl
    · simp

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteExceptionalTransverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small function with constant vertical derivative on a compact curve set,
allowing finitely many exceptional points. The regular local defining functions
are the only geometric input; all support and patching choices are constructed. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

theorem finite_exceptional_transverse_correction {K O P : Set Base}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧
      ∃ f : Base → ℝ, ContDiff ℝ ∞ f ∧ (∀ x ∈ K ∩ U, f x = 0) ∧
        ∀ x ∈ U, fderiv ℝ f x (0, 1) ≠ 0)
    (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Base → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ O ∧
      (∀ x, |H x| < ε) ∧ ∀ x ∈ K, fderiv ℝ H x (0, 1) = B := by
  classical
  let : Fintype P := hP.fintype
  obtain ⟨H₀, hH₀, hH₀c, hH₀s, hH₀b, V, hV, hPV, _, hH₀d⟩ :=
    exists_finite_special_correction (fun p : P => p.val) Subtype.val_injective hO
      (fun p => hKO (hPK p.property)) B (half_pos hε)
  let T : Base → ℝ := fun x => B - fderiv ℝ H₀ x (0, 1)
  have hT : ContDiff ℝ ∞ T :=
    contDiff_const.sub (((hH₀.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const))
  have hTV (p : Base) (hp : p ∈ V) : p ∉ tsupport T := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hV.mem_nhds hp] with x hx
    change B - fderiv ℝ H₀ x (0, 1) = 0
    rw [hH₀d x hx, sub_self]
  have hl (p : Base) (hp : p ∈ K ∩ tsupport T) :=
    hlocal p ⟨hp.1, fun hpp => hTV p (hPV ⟨p, hpp⟩) hp.2⟩
  obtain ⟨H₁, hH₁, hH₁c, hH₁s, hH₁b, hH₁d⟩ :=
    compact_transverse_correction (0, 1) hK hO hKO hT hl (half_pos hε)
  refine ⟨fun x => H₀ x + H₁ x, hH₀.add hH₁, ?_, ?_, ?_, ?_⟩
  · exact (hH₀c.union hH₁c).of_isClosed_subset (isClosed_tsupport _) (tsupport_add H₀ H₁)
  · exact (tsupport_add H₀ H₁).trans (union_subset hH₀s hH₁s)
  · intro x
    calc
      |H₀ x + H₁ x| ≤ |H₀ x| + |H₁ x| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hH₀b x) (hH₁b x)
      _ = ε := add_halves ε
  · intro x hx
    rw [fderiv_fun_add (hH₀.differentiable (by simp) x)
      (hH₁.differentiable (by simp) x), add_apply, hH₁d x hx]
    change fderiv ℝ H₀ x (0, 1) + (B - fderiv ℝ H₀ x (0, 1)) = B
    ring

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalDefiningFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a local transverse defining function smoothly before applying the
compact correction construction. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

lemma localize_defining_function {K U : Set Base} {p : Base} {f : Base → ℝ}
    (hU : IsOpen U) (hp : p ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hz : ∀ x ∈ K ∩ U, f x = 0) (hd : fderiv ℝ f p (0, 1) ≠ 0) :
    ∃ W : Set Base, IsOpen W ∧ p ∈ W ∧
      ∃ F : Base → ℝ, ContDiff ℝ ∞ F ∧ (∀ x ∈ K ∩ W, F x = 0) ∧
        ∀ x ∈ W, fderiv ℝ F x (0, 1) ≠ 0 := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU p hp
  let φ : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hs : tsupport φ ⊆ U := by
    rw [φ.tsupport_eq]
    exact fun x hx => hrU (lt_of_le_of_lt hx (by change r / 2 < r; linarith))
  let F : Base → ℝ := fun x => φ x * f x
  have hF : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact φ.contDiff.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hs hx)))
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change φ y * f y = 0
      rw [show φ y = 0 from hy, zero_mul]
  have he : F =ᶠ[𝓝 p] f := by
    filter_upwards [φ.eventuallyEq_one_of_mem_ball (mem_ball_self φ.rIn_pos)] with x hx
    change φ x * f x = f x
    rw [show φ x = 1 from hx, one_mul]
  have hFp : fderiv ℝ F p (0, 1) ≠ 0 := by rw [he.fderiv_eq]; exact hd
  let N : Set Base := {x | fderiv ℝ F x (0, 1) ≠ 0}
  have hdF : ContDiff ℝ ∞ (fun x => fderiv ℝ F x (0, 1)) :=
    (hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hN : IsOpen N := isOpen_ne.preimage hdF.continuous
  refine ⟨ball p φ.rIn ∩ N, isOpen_ball.inter hN, ⟨mem_ball_self φ.rIn_pos, hFp⟩,
    F, hF, ?_, fun x hx => hx.2⟩
  intro x hx
  have hxU : x ∈ U := hrU (lt_trans hx.2.1 (by change r / 4 < r; linarith))
  change φ x * f x = 0
  rw [hz x ⟨hx.1, hxU⟩, mul_zero]

/-- The small-value derivative construction with local smooth curve equations.
This is the local analytic content of manuscript Lemma `small-value-derivative`. -/
theorem small_value_prescribed_derivative {K O P : Set Base}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f U ∧ (∀ x ∈ K ∩ U, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Base → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ O ∧
      (∀ x, |H x| < ε) ∧ ∀ x ∈ K, fderiv ℝ H x (0, 1) = B := by
  apply finite_exceptional_transverse_correction hK hO hKO hP hPK _ B hε
  intro p hp
  obtain ⟨U, hU, hpU, f, hf, hz, hd⟩ := hlocal p hp
  exact localize_defining_function hU hpU hf hz hd

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveDensityClock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular clock associated to a positive periodic density of mass one. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {ρ : B × ℝ → ℝ} {U : Set B}

lemma clock_smoothOn [FiniteDimensional ℝ B] (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : B × ℝ => clock ρ z.1 z.2) (U ×ˢ univ) := by
  apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
  intro z hz
  obtain ⟨G, hG, he⟩ := SmoothParameterIntegral.exists_smooth_extension_near hU hρ hz.1
  apply (PeriodicPrimitive.contDiff_rawPrimitive_joint hG).contDiffAt.congr_of_eventuallyEq
  have he' := (continuous_fst.continuousAt : Tendsto Prod.fst (𝓝 z) (𝓝 z.1)).eventually he
  filter_upwards [he'] with w hw
  change (∫ s in 0..w.2, ρ (w.1, s)) = ∫ s in 0..w.2, G (w.1, s)
  congr 1
  funext s
  exact (hw s).symm

lemma hasDerivAt_clock (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    {b : B} (hb : b ∈ U) (t : ℝ) : HasDerivAt (clock ρ b) (ρ (b, t)) t :=
  ((LocalPeriodicCalculus.smooth_slice hU hρ hb).continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

lemma clock_strictMono (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t)) {b : B} (hb : b ∈ U) :
    StrictMono (clock ρ b) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_clock hU hρ hb t).deriv]
  exact hpos b hb t

lemma clock_continuous (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    {b : B} (hb : b ∈ U) : Continuous (clock ρ b) :=
  (show Differentiable ℝ (clock ρ b) from
    fun t => (hasDerivAt_clock hU hρ hb t).differentiableAt).continuous

lemma clock_period (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) (t : ℝ) : clock ρ b (t + 1) = clock ρ b t + 1 := by
  rw [clock, (hper b hb).intervalIntegral_add_eq_add 0 t
    (fun x y => (LocalPeriodicCalculus.smooth_slice hU hρ hb).continuous.intervalIntegrable x y)]
  simp only [zero_add, hmass b hb, clock]

lemma clock_surjective (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) : Function.Surjective (clock ρ b) := by
  exact (clock_continuous hU hρ hb).surjective
    ((hper b hb).tendsto_atTop_intervalIntegral_of_pos (by rw [hmass b hb]; norm_num) zero_lt_one)
    ((hper b hb).tendsto_atBot_intervalIntegral_of_pos (by rw [hmass b hb]; norm_num) zero_lt_one)

end ClosedSurfaceR4.PositiveDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveDensityInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive density's circle diffeomorphism has a jointly smooth inverse. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {ρ : B × ℝ → ℝ} {U : Set B}

omit [FiniteDimensional ℝ B] in
lemma clock_inverseClock (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1) {b : B} (hb : b ∈ U) (θ : ℝ) :
    clock ρ b (inverseClock ρ b θ) = θ :=
  Function.rightInverse_invFun (clock_surjective hU hρ hper hmass hb) θ

omit [FiniteDimensional ℝ B] in
lemma inverseClock_clock (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t)) {b : B} (hb : b ∈ U) (t : ℝ) :
    inverseClock ρ b (clock ρ b t) = t :=
  Function.leftInverse_invFun (clock_strictMono hU hρ hpos hb).injective t

omit [FiniteDimensional ℝ B] in
lemma inverseClock_period (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1) {b : B} (hb : b ∈ U) (θ : ℝ) :
    inverseClock ρ b (θ + 1) = inverseClock ρ b θ + 1 := by
  apply (clock_strictMono hU hρ hpos hb).injective
  rw [clock_inverseClock hU hρ hper hmass hb, clock_period hU hρ hper hmass hb,
    clock_inverseClock hU hρ hper hmass hb]

private lemma equation_smoothOn (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (equation ρ) ((U ×ˢ univ) ×ˢ univ) := by
  exact ((clock_smoothOn hU hρ).comp
    (contDiffOn_fst.fst.prodMk contDiffOn_snd) (fun z hz => ⟨hz.1.1, mem_univ _⟩)).sub
    contDiffOn_fst.snd

private lemma equation_partial (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    {b : B} (hb : b ∈ U) (θ t : ℝ) :
    fderiv ℝ (equation ρ) ((b, θ), t) ∘L ContinuousLinearMap.inr ℝ (B × ℝ) ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ (ρ (b, t)) := by
  have hc : ContDiffAt ℝ ∞ (equation ρ) ((b, θ), t) :=
    (equation_smoothOn hU hρ).contDiffAt
      (((hU.prod isOpen_univ).prod isOpen_univ).mem_nhds ⟨⟨hb, mem_univ θ⟩, mem_univ t⟩)
  have hi : HasFDerivAt (fun s : ℝ => ((b, θ), s))
      (ContinuousLinearMap.inr ℝ (B × ℝ) ℝ) t := hasFDerivAt_prodMk_right (b, θ) t
  have hcomp := (hc.differentiableAt (by simp)).hasFDerivAt.comp t hi
  exact hcomp.unique ((hasDerivAt_clock hU hρ hb t).sub_const θ).hasFDerivAt

private lemma equation_partial_invertible (hU : IsOpen U)
    (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t)) {b : B} (hb : b ∈ U) (θ t : ℝ) :
    (fderiv ℝ (equation ρ) ((b, θ), t) ∘L ContinuousLinearMap.inr ℝ (B × ℝ) ℝ).IsInvertible := by
  rw [equation_partial hU hρ hb]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (ρ (b, t))⁻¹)
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, (hpos b hb t).ne']
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, (hpos b hb t).ne']

/-- No regularity of the inverse is assumed: it follows from positivity and the IFT. -/
theorem inverseClock_smoothOn (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1) :
    ContDiffOn ℝ ∞ (fun z : B × ℝ => inverseClock ρ z.1 z.2) (U ×ˢ univ) := by
  apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
  intro z hz
  let u : (B × ℝ) × ℝ := (z, inverseClock ρ z.1 z.2)
  have hu : u ∈ (U ×ˢ univ) ×ˢ univ := ⟨hz, mem_univ _⟩
  have hc := (equation_smoothOn hU hρ).contDiffAt
    (((hU.prod isOpen_univ).prod isOpen_univ).mem_nhds hu)
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hi := equation_partial_invertible hU hρ hpos hz.1 z.2 (inverseClock ρ z.1 z.2)
  have hs := hc.contDiffAt_implicitFunction hn hi
  have he := hc.eventually_apply_implicitFunction hn hi
  have hnear : ∀ᶠ w : B × ℝ in 𝓝 z, w.1 ∈ U :=
    continuous_fst.continuousAt.eventually (hU.mem_nhds hz.1)
  have heq : (fun w : B × ℝ => inverseClock ρ w.1 w.2) =ᶠ[𝓝 z]
      hc.implicitFunction hn hi := by
    filter_upwards [he, hnear] with w hw hwu
    apply (clock_strictMono hU hρ hpos hwu).injective
    rw [clock_inverseClock hU hρ hper hmass hwu]
    change clock ρ w.1 (hc.implicitFunction hn hi w) - w.2 =
      clock ρ z.1 (inverseClock ρ z.1 z.2) - z.2 at hw
    rw [clock_inverseClock hU hρ hper hmass hz.1, sub_self] at hw
    exact (sub_eq_zero.mp hw).symm
  exact hs.congr_of_eventuallyEq heq

end ClosedSurfaceR4.PositiveDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveDensityReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reparametrization converts an exact positive weighted mean into the uniform mean. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ρ : B × ℝ → ℝ} {F : B × ℝ → E} {U : Set B}

omit [CompleteSpace E] in
lemma reparametrize_smoothOn (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (reparametrize ρ F) (U ×ˢ univ) :=
  hF.comp (contDiffOn_fst.prodMk (inverseClock_smoothOn hU hρ hpos hper hmass))
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

omit [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
lemma reparametrize_periodic (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    (hFper : ∀ b ∈ U, Function.Periodic (fun t => F (b, t)) 1)
    {b : B} (hb : b ∈ U) : Function.Periodic (fun t => reparametrize ρ F (b, t)) 1 := by
  intro t
  simp only [reparametrize, inverseClock_period hU hρ hpos hper hmass hb]
  exact hFper b hb _

omit [CompleteSpace E] in
/-- The exact change of variables, for the actual vector-valued velocity. -/
theorem reparametrize_mean (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) {b : B} (hb : b ∈ U) :
    (∫ θ in 0..1, reparametrize ρ F (b, θ)) = ∫ t in 0..1, ρ (b, t) • F (b, t) := by
  have hri := reparametrize_smoothOn hU hρ hpos hper hmass hF
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (a := 0) (b := 1) (f := clock ρ b) (f' := fun t => ρ (b, t))
    (g := fun θ => reparametrize ρ F (b, θ))
    (fun t _ => hasDerivAt_clock hU hρ hb t)
    (LocalPeriodicCalculus.smooth_slice hU hρ hb).continuous.continuousOn
    (LocalPeriodicCalculus.smooth_slice hU hri hb).continuous
  have h1 : clock ρ b 1 = 1 := hmass b hb
  simpa only [Function.comp_apply, reparametrize, inverseClock_clock hU hρ hpos hb,
    clock_zero, h1] using hsub.symm

end ClosedSurfaceR4.PositiveDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveDensityPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reparametrization commutes exactly with pulling back the parameter family. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PositiveDensity

variable {B E F : Type}

lemma clock_pullback (ρ : B × ℝ → ℝ) (σ : E → B) (x : E) (t : ℝ) :
    clock (pullbackDensity ρ σ) x t = clock ρ (σ x) t := rfl

variable [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma pullbackDensity_smoothOn {ρ : B × ℝ → ℝ} {σ : E → B} {U : Set E} {W : Set B}
    (hρ : ContDiffOn ℝ ∞ ρ (W ×ˢ univ)) (hσ : ContDiffOn ℝ ∞ σ U)
    (hσW : MapsTo σ U W) :
    ContDiffOn ℝ ∞ (pullbackDensity ρ σ) (U ×ˢ univ) := by
  exact hρ.comp ((hσ.comp contDiffOn_fst (fun z hz => hz.1)).prodMk contDiffOn_snd)
    (fun z hz => ⟨hσW hz.1, mem_univ _⟩)

end ClosedSurfaceR4.PositiveDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit small circular arc and positive averaging density. This gives
an alternative collar construction without solving a squared-amplitude equation. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma density_mul_arcX (a t : ℝ) :
    density a t * arcX a t = (1 - (a * Real.cos t) ^ 2) / (1 + a ^ 2 / 2) := by
  unfold density arcX
  field_simp [(arcDen_pos a t).ne', (densityDen_pos a).ne']

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact mean constraints for the explicit collar velocity arc. -/
noncomputable section
open MeasureTheory

namespace ClosedSurfaceR4.CollarVelocity

lemma integral_cos_sq_period : (∫ t in (0 : ℝ)..2 * Real.pi, Real.cos t ^ 2) = Real.pi := by
  rw [integral_cos_sq]
  simp

lemma integral_arc_num (a : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, 1 - (a * Real.cos t) ^ 2) =
      2 * Real.pi * (1 - a ^ 2 / 2) := by
  simp only [mul_pow]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
    (g := fun t : ℝ => a ^ 2 * Real.cos t ^ 2) intervalIntegrable_const
    ((continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_cos_sq_period]
  simp only [sub_zero, smul_eq_mul, mul_one]
  ring

lemma mean_density_arcX (a : ℝ) :
    circleMean (fun t => density a t * arcX a t) = (1 - a ^ 2 / 2) / (1 + a ^ 2 / 2) := by
  unfold circleMean
  simp_rw [density_mul_arcX]
  rw [intervalIntegral.integral_div, integral_arc_num]
  field_simp [(densityDen_pos a).ne', Real.pi_ne_zero]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibrate the explicit collar arc to the required tangential mean. -/
noncomputable section

namespace ClosedSurfaceR4.CollarVelocity

lemma amplitude_sq (R v a : ℝ) : amplitude R v a ^ 2 = 2 * a ^ 2 / (R + v) ^ 2 := by
  unfold amplitude
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The mean has exactly the prescribed tangential component. -/
theorem calibrated_mean {R v a : ℝ} (hR : 0 < R) (hv : 0 < v)
    (hquad : R ^ 2 = v ^ 2 + a ^ 2) :
    circleMean (fun t => density (amplitude R v a) t * arcX (amplitude R v a) t) = v / R := by
  rw [mean_density_arcX, amplitude_sq]
  have hp : R + v ≠ 0 := ne_of_gt (add_pos hR hv)
  have hd : (R + v) ^ 2 + a ^ 2 ≠ 0 := by positivity
  have heq : (1 - 2 * a ^ 2 / (R + v) ^ 2 / 2) /
      (1 + 2 * a ^ 2 / (R + v) ^ 2 / 2) =
      ((R + v) ^ 2 - a ^ 2) / ((R + v) ^ 2 + a ^ 2) := by
    field_simp
  rw [heq]
  have hn : (R + v) ^ 2 - a ^ 2 = 2 * v * (R + v) := by nlinarith
  have hd' : (R + v) ^ 2 + a ^ 2 = 2 * R * (R + v) := by nlinarith
  rw [hn, hd']
  field_simp

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityAngle
attribute [-simp] _root_.OAI.ClosedSurfaceR4.CollarVelocity.angle_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit collar arc has exactly two stationary angular positions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma baseAngle_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => baseAngle z.1 z.2) :=
  contDiff_const.mul ((contDiff_fst.mul contDiff_snd.cos).arctan)

lemma hasDerivAt_baseAngle (a t : ℝ) :
    HasDerivAt (baseAngle a) (-2 * a * Real.sin t / (1 + (a * Real.cos t) ^ 2)) t := by
  refine (((Real.hasDerivAt_cos t).const_mul a).arctan.const_mul 2).congr_deriv (Eq.symm ?_)
  · field_simp [(arcDen_pos a t).ne']

lemma hasDerivAt_inverseClock (a θ : ℝ) :
    HasDerivAt (inverseClock a) (density a (inverseClock a θ))⁻¹ θ := by
  have hi : Differentiable ℝ (inverseClock a) :=
    (inverseClock_smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc := (hasDerivAt_clock a (inverseClock a θ)).comp θ (hi θ).hasDerivAt
  have hid : (fun x => clock a (inverseClock a x)) = id := by funext x; simp
  change HasDerivAt (fun x => clock a (inverseClock a x)) _ θ at hc
  rw [hid] at hc
  have heq : density a (inverseClock a θ) * deriv (inverseClock a) θ = 1 :=
    hc.unique (hasDerivAt_id θ)
  convert (hi θ).hasDerivAt using 1
  all_goals try with_reducible_and_instances rfl
  apply mul_left_cancel₀ (density_pos a (inverseClock a θ)).ne'
  rw [mul_inv_cancel₀ (density_pos a (inverseClock a θ)).ne', heq]

lemma deriv_angle (a θ : ℝ) :
    deriv (angle a) θ =
      (-2 * a * Real.sin (inverseClock a θ) /
        (1 + (a * Real.cos (inverseClock a θ)) ^ 2)) *
          (density a (inverseClock a θ))⁻¹ :=
  ((hasDerivAt_baseAngle a (inverseClock a θ)).comp θ
    (hasDerivAt_inverseClock a θ)).deriv

lemma deriv_angle_eq_zero_iff {a θ : ℝ} (ha : a ≠ 0) :
    deriv (angle a) θ = 0 ↔ Real.sin (inverseClock a θ) = 0 := by
  rw [deriv_angle]
  simp [(density_pos a (inverseClock a θ)).ne', (arcDen_pos a (inverseClock a θ)).ne', ha]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityTurns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact turning positions for the collar arc, including after reparametrization. -/
noncomputable section

namespace ClosedSurfaceR4.CollarVelocity

lemma clock_of_sin_eq_zero (a : ℝ) {t : ℝ} (ht : Real.sin t = 0) : clock a t = t := by
  simp [clock, Real.sin_two_mul, ht]

lemma inverseClock_of_sin_eq_zero (a : ℝ) {t : ℝ} (ht : Real.sin t = 0) :
    inverseClock a t = t := by
  apply (clock_strictMono a).injective
  rw [clock_inverseClock, clock_of_sin_eq_zero a ht]

lemma sin_inverseClock_eq_zero_iff (a θ : ℝ) :
    Real.sin (inverseClock a θ) = 0 ↔ Real.sin θ = 0 := by
  constructor
  · intro h
    have ht := clock_of_sin_eq_zero a h
    rw [clock_inverseClock] at ht
    rwa [ht]
  · intro h
    rwa [inverseClock_of_sin_eq_zero a h]

lemma deriv_angle_eq_zero_iff_sin {a θ : ℝ} (ha : a ≠ 0) :
    deriv (angle a) θ = 0 ↔ Real.sin θ = 0 :=
  (deriv_angle_eq_zero_iff ha).trans (sin_inverseClock_eq_zero_iff a θ)

/-- There are precisely two turns in one half-open period. -/
theorem angle_two_turns {a θ : ℝ} (ha : a ≠ 0) (hθ : θ ∈ Set.Ico 0 (2 * Real.pi)) :
    deriv (angle a) θ = 0 ↔ θ = 0 ∨ θ = Real.pi := by
  rw [deriv_angle_eq_zero_iff_sin ha]
  constructor
  · intro h
    by_cases hp : θ < Real.pi
    · left
      exact (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos, hθ.1]) hp).mp h
    · right
      have hs : Real.sin (θ - Real.pi) = 0 := by
        simp [Real.sin_sub, h]
      have hz := (Real.sin_eq_zero_iff_of_lt_of_lt
        (x := θ - Real.pi) (by linarith [Real.pi_pos]) (by linarith [hθ.2])).mp hs
      linarith
  · rintro (rfl | rfl) <;> simp

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityAngleInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interpolate the collar angle to a circle-covering interior angle without extra turns. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma hasDerivAt_blendedAngle (a A s h t : ℝ) :
    HasDerivAt (blendedAngle a A s h)
      (-Real.sin t * ((1 - s) * (2 * a / (1 + (a * Real.cos t) ^ 2)) + s * A)) t := by
  have hd := (((hasDerivAt_baseAngle a t).const_mul (1 - s)).add
    (((Real.hasDerivAt_cos t).const_mul A).const_mul s)).const_add h
  refine (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp only [blendedAngle, Pi.add_apply]
    ring
  · ring

lemma blended_speed_positive {a A s : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) :
    0 < (1 - s) * (2 * a / (1 + (a * Real.cos t) ^ 2)) + s * A := by
  have hd : 0 < 2 * a / (1 + (a * Real.cos t) ^ 2) :=
    div_pos (by positivity) (arcDen_pos a t)
  by_cases hz : s = 0
  · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero] using hd
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hs1) hd.le) (mul_pos (lt_of_le_of_ne hs (Ne.symm hz)) hA)

lemma blendedAngle_zero (a A s h : ℝ) :
    blendedAngle a A s h 0 = h + ((1 - s) * (2 * Real.arctan a) + s * A) := by
  simp [blendedAngle, baseAngle]
  ring

lemma blendedAngle_pi (a A s h : ℝ) :
    blendedAngle a A s h Real.pi = h - ((1 - s) * (2 * Real.arctan a) + s * A) := by
  simp [blendedAngle, baseAngle, Real.arctan_neg]
  ring

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityLinear
attribute [-simp] _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three linear moment equations for a positive loop density. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LoopDensity

lemma augment_continuous : Continuous augment := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [augment] <;> fun_prop

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BlendedVelocityPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth transition paths and their strict convex-hull margin. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma blendedPath_smooth {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun z : B × ℝ => blendedPath (a z.1) (A z.1) (s z.1) (h z.1) z.2) := by
  have hangle : ContDiff ℝ ∞ (fun z : B × ℝ =>
      blendedAngle (a z.1) (A z.1) (s z.1) (h z.1) (2 * Real.pi * z.2)) := by
    have hb : ContDiff ℝ ∞ (fun z : B × ℝ => baseAngle (a z.1) (2 * Real.pi * z.2)) :=
      baseAngle_smooth.comp ((ha.comp contDiff_fst).prodMk (contDiff_const.mul contDiff_snd))
    exact ((hh.comp contDiff_fst).add
      ((contDiff_const.sub (hs.comp contDiff_fst)).mul hb)).add
        ((hs.comp contDiff_fst).mul ((hA.comp contDiff_fst).mul
          (contDiff_const.mul contDiff_snd).cos))
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact hangle.cos
  · exact hangle.sin

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PositiveDensityTurns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive changes of circle coordinate preserve stationary points and their spatial jets. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {ρ : B × ℝ → ℝ} {U : Set B}

lemma hasDerivAt_inverseClock (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1) {b : B} (hb : b ∈ U) (θ : ℝ) :
    HasDerivAt (inverseClock ρ b) (ρ (b, inverseClock ρ b θ))⁻¹ θ := by
  have hi : Differentiable ℝ (inverseClock ρ b) :=
    (LocalPeriodicCalculus.smooth_slice hU
      (inverseClock_smoothOn hU hρ hpos hper hmass) hb).differentiable (by simp)
  have hc := (hasDerivAt_clock hU hρ hb (inverseClock ρ b θ)).comp θ (hi θ).hasDerivAt
  have hid : (fun x => clock ρ b (inverseClock ρ b x)) = id :=
    funext (clock_inverseClock hU hρ hper hmass hb)
  change HasDerivAt (fun x => clock ρ b (inverseClock ρ b x)) _ θ at hc
  rw [hid] at hc
  have heq : ρ (b, inverseClock ρ b θ) * deriv (inverseClock ρ b) θ = 1 :=
    hc.unique (hasDerivAt_id θ)
  convert (hi θ).hasDerivAt using 1
  all_goals try with_reducible_and_instances rfl
  apply mul_left_cancel₀ (hpos b hb (inverseClock ρ b θ)).ne'
  rw [mul_inv_cancel₀ (hpos b hb (inverseClock ρ b θ)).ne', heq]

lemma deriv_reparametrize_eq_zero_iff
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {F : B × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    {b : B} (hb : b ∈ U) (θ : ℝ) :
    deriv (fun t => reparametrize ρ F (b, t)) θ = 0 ↔
      deriv (fun t => F (b, t)) (inverseClock ρ b θ) = 0 := by
  have hf := (LocalPeriodicCalculus.smooth_slice hU hF hb).differentiable (by simp)
  have hd := (hf (inverseClock ρ b θ)).hasDerivAt.comp θ
    (hasDerivAt_inverseClock hU hρ hpos hper hmass hb θ)
  change deriv ((fun t => F (b, t)) ∘ inverseClock ρ b) θ = 0 ↔ _
  rw [hd.deriv]
  simp [(hpos b hb (inverseClock ρ b θ)).ne']

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At a turn, the extra spatial chain-rule term from the inverse clock is zero. -/
theorem spatial_derivative_at_turn
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {F : B × ℝ → E} (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    {b : B} (hb : b ∈ U) (θ : ℝ)
    (hzero : fderiv ℝ F (b, inverseClock ρ b θ) (0, 1) = 0) (v : B) :
    fderiv ℝ (fun x => reparametrize ρ F (x, θ)) b v =
      fderiv ℝ (fun x => F (x, inverseClock ρ b θ)) b v := by
  have hInv : ContDiffAt ℝ ∞ (fun z : B × ℝ => inverseClock ρ z.1 z.2) (b, θ) :=
    (inverseClock_smoothOn hU hρ hpos hper hmass).contDiffAt
    ((hU.prod isOpen_univ).mem_nhds ⟨hb, mem_univ θ⟩)
  have hi : DifferentiableAt ℝ (fun x => inverseClock ρ x θ) b :=
    (hInv.comp b (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hF' : DifferentiableAt ℝ F (b, inverseClock ρ b θ) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hb, mem_univ _⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := hF'.hasFDerivAt.comp b ((hasFDerivAt_id b).prodMk hi.hasFDerivAt)
  have hf := hF'.hasFDerivAt.comp b (hasFDerivAt_prodMk_left (𝕜 := ℝ) b (inverseClock ρ b θ))
  simp only [id_eq] at hd
  change fderiv ℝ (F ∘ fun x => (x, inverseClock ρ x θ)) b v =
    fderiv ℝ (F ∘ fun x => (x, inverseClock ρ b θ)) b v
  rw [hd.fderiv, hf.fderiv]
  change fderiv ℝ F (b, inverseClock ρ b θ)
    (v, fderiv ℝ (fun x => inverseClock ρ x θ) b v) =
      fderiv ℝ F (b, inverseClock ρ b θ) (v, 0)
  rw [show (v, fderiv ℝ (fun x => inverseClock ρ x θ) b v) =
    (v, 0) + (fderiv ℝ (fun x => inverseClock ρ x θ) b v) • (0, 1) by simp]
  rw [map_add, map_smul, hzero, smul_zero, add_zero]

end ClosedSurfaceR4.PositiveDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BlendedReparamTurns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-turn geometry for the blended path after positive reparametrization. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma unitAngle_smooth {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun z : B × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2) := by
  have hb : ContDiff ℝ ∞ (fun z : B × ℝ => baseAngle (a z.1) (2 * Real.pi * z.2)) :=
    baseAngle_smooth.comp ((ha.comp contDiff_fst).prodMk (contDiff_const.mul contDiff_snd))
  exact ((hh.comp contDiff_fst).add
    ((contDiff_const.sub (hs.comp contDiff_fst)).mul hb)).add
      ((hs.comp contDiff_fst).mul ((hA.comp contDiff_fst).mul
        (contDiff_const.mul contDiff_snd).cos))

lemma unitAngle_deriv_zero_iff {a A s : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hs : s ∈ Icc (0 : ℝ) 1) (h t : ℝ) :
    deriv (unitAngle a A s h) t = 0 ↔ Real.sin (2 * Real.pi * t) = 0 := by
  have hd := (hasDerivAt_blendedAngle a A s h (2 * Real.pi * t)).comp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi))
  change deriv ((blendedAngle a A s h) ∘ fun u => 2 * Real.pi * u) t = 0 ↔ _
  rw [hd.deriv]
  have hspeed := (blended_speed_positive ha hA hs.1 hs.2 (2 * Real.pi * t)).ne'
  simp [hspeed, Real.pi_ne_zero]

lemma unit_sin_zero_iff {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    Real.sin (2 * Real.pi * t) = 0 ↔ t = 0 ∨ t = 1 / 2 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hperiod : 2 * Real.pi * t ∈ Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg hp.le ht.1, by nlinarith [ht.2]⟩
  have hzero := (deriv_angle_eq_zero_iff_sin (a := 1) (θ := 2 * Real.pi * t) one_ne_zero).symm.trans
    (angle_two_turns (a := 1) one_ne_zero hperiod)
  rw [hzero]
  constructor
  · rintro (hz | hz)
    · left; nlinarith
    · right; nlinarith [Real.pi_pos]
  · rintro (rfl | rfl)
    · simp
    · right; ring

variable [FiniteDimensional ℝ B] {ρ : B × ℝ → ℝ} {U : Set B}

omit [FiniteDimensional ℝ B] in
lemma inverseClock_mem_period (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) {θ : ℝ} (hθ : θ ∈ Ico (0 : ℝ) 1) :
    PositiveDensity.inverseClock ρ b θ ∈ Ico (0 : ℝ) 1 := by
  have hm := PositiveDensity.clock_strictMono hU hρ hpos hb
  have hi := PositiveDensity.clock_inverseClock hU hρ hper hmass hb θ
  have hc1 : PositiveDensity.clock ρ b 1 = 1 := hmass b hb
  constructor
  · apply hm.le_iff_le.mp
    simpa only [PositiveDensity.clock_zero, hi] using hθ.1
  · apply hm.lt_iff_lt.mp
    rw [hi, hc1]
    exact hθ.2

theorem reparametrized_two_turns
    {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h)
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) (hab : 0 < a b) (hAb : 0 < A b)
    (hsb : s b ∈ Icc (0 : ℝ) 1) {θ : ℝ} (hθ : θ ∈ Ico (0 : ℝ) 1) :
    deriv (fun t => PositiveDensity.reparametrize ρ
      (fun z => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2) (b, t)) θ = 0 ↔
      θ = 0 ∨ θ = PositiveDensity.clock ρ b (1 / 2) := by
  rw [PositiveDensity.deriv_reparametrize_eq_zero_iff hU hρ hpos hper hmass
    (unitAngle_smooth ha hA hs hh).contDiffOn hb θ]
  change deriv (unitAngle (a b) (A b) (s b) (h b)) (PositiveDensity.inverseClock ρ b θ) = 0 ↔ _
  rw [unitAngle_deriv_zero_iff hab hAb hsb,
    unit_sin_zero_iff (inverseClock_mem_period hU hρ hpos hper hmass hb hθ)]
  constructor
  · rintro (hz | hz)
    · left
      have hi := PositiveDensity.clock_inverseClock hU hρ hper hmass hb θ
      simpa only [hz, PositiveDensity.clock_zero] using hi.symm
    · right
      have hi := PositiveDensity.clock_inverseClock hU hρ hper hmass hb θ
      simpa only [hz] using hi.symm
  · rintro (rfl | rfl)
    · left
      have hi := PositiveDensity.inverseClock_clock hU hρ hpos hb 0
      simpa only [PositiveDensity.clock_zero] using hi
    · exact Or.inr (PositiveDensity.inverseClock_clock hU hρ hpos hb (1 / 2))

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BlendedSpatialTurns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spatial derivative at each turn of the normalized blended loop. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma unitAngle_zero (a A s h : ℝ) :
    unitAngle a A s h 0 = h + blendedAmplitude a A s := by
  simpa only [unitAngle, mul_zero, blendedAmplitude] using blendedAngle_zero a A s h

lemma unitAngle_half (a A s h : ℝ) :
    unitAngle a A s h (1 / 2) = h - blendedAmplitude a A s := by
  have he : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  simpa only [unitAngle, he, blendedAmplitude] using blendedAngle_pi a A s h

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma blendedAmplitude_smooth {a A s : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A) (hs : ContDiff ℝ ∞ s) :
    ContDiff ℝ ∞ (fun x => blendedAmplitude (a x) (A x) (s x)) :=
  ((contDiff_const.sub hs).mul (contDiff_const.mul ha.arctan)).add (hs.mul hA)

lemma unitAngle_angular_zero {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) (b : B) {t : ℝ}
    (ht : Real.sin (2 * Real.pi * t) = 0) :
    fderiv ℝ (fun z : B × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2)
      (b, t) (0, 1) = 0 := by
  have hd := (hasDerivAt_blendedAngle (a b) (A b) (s b) (h b) (2 * Real.pi * t)).comp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi))
  have hf := SmoothPeriodicCalculus.angle_hasDerivAt (unitAngle_smooth ha hA hs hh) b t
  have he := hf.unique hd
  simpa only [ht, neg_zero, zero_mul, SmoothPeriodicCalculus.angleDerivative] using he

variable [FiniteDimensional ℝ B] {ρ : B × ℝ → ℝ} {U : Set B}

theorem reparametrized_spatial_turns {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h)
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) (v : B) :
    let F := fun z : B × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2
    let amp := fun x => blendedAmplitude (a x) (A x) (s x)
    fderiv ℝ (fun x => PositiveDensity.reparametrize ρ F (x, 0)) b v =
      fderiv ℝ h b v + fderiv ℝ amp b v ∧
    fderiv ℝ (fun x => PositiveDensity.reparametrize ρ F
      (x, PositiveDensity.clock ρ b (1 / 2))) b v =
      fderiv ℝ h b v - fderiv ℝ amp b v := by
  dsimp only
  let F := fun z : B × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2
  let amp := fun x => blendedAmplitude (a x) (A x) (s x)
  have hF : ContDiff ℝ ∞ F := unitAngle_smooth ha hA hs hh
  have hamp : ContDiff ℝ ∞ amp := blendedAmplitude_smooth ha hA hs
  have hi₀ : PositiveDensity.inverseClock ρ b 0 = 0 := by
    simpa only [PositiveDensity.clock_zero] using
      PositiveDensity.inverseClock_clock hU hρ hpos hb 0
  have hi₁ := PositiveDensity.inverseClock_clock hU hρ hpos hb (1 / 2)
  have hz₀ : fderiv ℝ F (b, PositiveDensity.inverseClock ρ b 0) (0, 1) = 0 := by
    rw [hi₀]
    exact unitAngle_angular_zero ha hA hs hh b (by simp)
  have hz₁ : fderiv ℝ F
      (b, PositiveDensity.inverseClock ρ b (PositiveDensity.clock ρ b (1 / 2))) (0, 1) = 0 := by
    rw [hi₁]
    apply unitAngle_angular_zero ha hA hs hh b
    have he : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
    rw [he, Real.sin_pi]
  have hd₀ := PositiveDensity.spatial_derivative_at_turn hU hρ hpos hper hmass
    hF.contDiffOn hb 0 hz₀ v
  have hd₁ := PositiveDensity.spatial_derivative_at_turn hU hρ hpos hper hmass
    hF.contDiffOn hb (PositiveDensity.clock ρ b (1 / 2)) hz₁ v
  rw [hi₀] at hd₀
  rw [hi₁] at hd₁
  have he₀ : (fun x => F (x, 0)) = (fun x => h x + amp x) :=
    funext (fun x => unitAngle_zero (a x) (A x) (s x) (h x))
  have he₁ : (fun x => F (x, 1 / 2)) = (fun x => h x - amp x) :=
    funext (fun x => unitAngle_half (a x) (A x) (s x) (h x))
  rw [he₀, fderiv_fun_add (hh.differentiable (by simp) b)
    (hamp.differentiable (by simp) b), add_apply] at hd₀
  rw [he₁, fderiv_fun_sub (hh.differentiable (by simp) b)
    (hamp.differentiable (by simp) b), sub_apply] at hd₁
  exact ⟨hd₀, hd₁⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityMoments
attribute [-simp] _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extract mass one and the vector mean from the three augmented moments. -/
noncomputable section

namespace ClosedSurfaceR4.LoopDensity

theorem mass_and_mean {ρ : ℝ → ℝ} {p : ℝ → Plane} {c : Plane}
    (hρ : Continuous ρ) (hp : Continuous p)
    (hm : (∫ t in 0..1, ρ t • augment (p t)) = augment c) :
    (∫ t in 0..1, ρ t) = 1 ∧ (∫ t in 0..1, ρ t • p t) = c := by
  have hi : IntervalIntegrable (fun t => ρ t • augment (p t)) MeasureTheory.volume 0 1 :=
    (hρ.smul (augment_continuous.comp hp)).intervalIntegrable 0 1
  have hpi : IntervalIntegrable (fun t => ρ t • p t) MeasureTheory.volume 0 1 :=
    (hρ.smul hp).intervalIntegrable 0 1
  have hcoord (i : Fin 3) :
      (∫ t in 0..1, (ρ t • augment (p t)) i) = (augment c) i := by
    have he := congrArg (fun x : Moments => x i) hm
    have hev : (∫ t in 0..1, ρ t • augment (p t)) i =
        ∫ t in 0..1, (ρ t • augment (p t)) i :=
      ((ContinuousLinearMap.proj i : Moments →L[ℝ] ℝ).intervalIntegral_comp_comm hi).symm
    rwa [hev] at he
  constructor
  · simpa [augment] using hcoord 0
  · ext i
    have hev : (∫ t in 0..1, ρ t • p t) i = ∫ t in 0..1, (ρ t • p t) i :=
      ((ContinuousLinearMap.proj i : Plane →L[ℝ] ℝ).intervalIntegral_comp_comm hpi).symm
    rw [hev]
    fin_cases i
    · simpa [augment] using hcoord 1
    · simpa [augment] using hcoord 2

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SmallTurnFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the small translation of the angle with a large derivative at both
turns. Compactness bounds the endpoint-amplitude derivative before this choice. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open TransverseSmallFunction

/-- The two endpoint derivatives can be made arbitrarily large while the
translation itself is arbitrarily small. The geometric input is the checked
local curve-equation form of the finite-curve correction lemma. -/
theorem exists_small_turn_function {K O P : Set Base}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f U ∧ (∀ x ∈ K ∩ U, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    {a A s : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hA : ContDiff ℝ ∞ A) (hs : ContDiff ℝ ∞ s) (T : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Base → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ O ∧
      (∀ x, |h x| < ε) ∧ ∀ x ∈ K,
        T < fderiv ℝ (fun y => h y + blendedAmplitude (a y) (A y) (s y)) x (0, 1) ∧
        T < fderiv ℝ (fun y => h y - blendedAmplitude (a y) (A y) (s y)) x (0, 1) := by
  let amp := fun y => blendedAmplitude (a y) (A y) (s y)
  have hamp : ContDiff ℝ ∞ amp := blendedAmplitude_smooth ha hA hs
  have hD : Continuous (fun x => fderiv ℝ amp x (0, 1)) :=
    ((hamp.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).continuous
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hD.continuousOn
  obtain ⟨h, hh, hhc, hhs, hhb, hhd⟩ := small_value_prescribed_derivative
    hK hO hKO hP hPK hlocal (M + T + 1) hε
  refine ⟨h, hh, hhc, hhs, hhb, ?_⟩
  intro x hx
  have hb : |fderiv ℝ amp x (0, 1)| ≤ M := hM x hx
  have hlow := (abs_le.mp hb).1
  have hupp := (abs_le.mp hb).2
  have hp := hhd x hx
  have hd₁ := fderiv_fun_add (hh.differentiable (by simp) x)
    (hamp.differentiable (by simp) x)
  have hd₂ := fderiv_fun_sub (hh.differentiable (by simp) x)
    (hamp.differentiable (by simp) x)
  constructor
  · change T < fderiv ℝ (fun y => h y + amp y) x (0, 1)
    rw [hd₁, add_apply, hp]
    linarith
  · change T < fderiv ℝ (fun y => h y - amp y) x (0, 1)
    rw [hd₂, sub_apply, hp]
    linarith

/-- Any subsequently chosen positive density retains the large spatial derivatives. -/
theorem large_turns_after_reparametrization
    {a A s h : Base → ℝ} {K U : Set Base} {T : ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h)
    (hU : IsOpen U) (hKU : K ⊆ U) {ρ : Base × ℝ → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    (hlarge : ∀ x ∈ K,
      T < fderiv ℝ (fun y => h y + blendedAmplitude (a y) (A y) (s y)) x (0, 1) ∧
      T < fderiv ℝ (fun y => h y - blendedAmplitude (a y) (A y) (s y)) x (0, 1)) :
    let F := fun z : Base × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2
    ∀ x ∈ K,
      T < fderiv ℝ (fun y => PositiveDensity.reparametrize ρ F (y, 0)) x (0, 1) ∧
      T < fderiv ℝ (fun y => PositiveDensity.reparametrize ρ F
        (y, PositiveDensity.clock ρ x (1 / 2))) x (0, 1) := by
  intro F x hx
  obtain ⟨hd₁, hd₂⟩ := reparametrized_spatial_turns ha hA hs hh hU hρ hpos hper hmass
    (hKU hx) (0, 1)
  obtain ⟨h₁, h₂⟩ := hlarge x hx
  rw [fderiv_fun_add (hh.differentiable (by simp) x)
    ((blendedAmplitude_smooth ha hA hs).differentiable (by simp) x), add_apply] at h₁
  rw [fderiv_fun_sub (hh.differentiable (by simp) x)
    ((blendedAmplitude_smooth ha hA hs).differentiable (by simp) x), sub_apply] at h₂
  exact ⟨hd₁.symm ▸ h₁, hd₂.symm ▸ h₂⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ControlledInteriorLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the interior velocity angle: a small translation with large turn
jets, an actual positive density, the exact prescribed vector mean, and exactly
two turns. No density or transverse-correction solvability is assumed. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open TransverseSmallFunction

lemma unitAngle_periodic (a A s h : ℝ) : Function.Periodic (unitAngle a A s h) 1 := by
  intro t
  simp [unitAngle, blendedAngle, baseAngle, mul_add, Real.cos_add_two_pi]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetVelocityLoop
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A controlled loop on a neighborhood of the actual second-jet section.
Its translation depends on position alone, so the prescribed turn derivatives
along the original section persist under the joint density construction. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open RealModes TransverseSmallFunction

lemma jetSection_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (jetSection F) := contDiff_id.prodMk (contDiff_realTwoJet hF)

lemma jetAngle_on_section (F : RField 4) (ρ : JetBase × ℝ → ℝ)
    (a A s : JetBase → ℝ) (h : Base → ℝ) (x : Base) (t : ℝ) :
    jetAngle ρ a A s (fun z => h z.1) (jetSection F x, t) =
      normalizedAngle (PositiveDensity.pullbackDensity ρ (jetSection F))
        (a ∘ jetSection F) (A ∘ jetSection F) (s ∘ jetSection F) h (x, t) := rfl

theorem controlled_jet_loop {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {K O P : Set Base} {L U C : Set JetBase}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : MapsTo (jetSection F) K L)
    (hO : IsOpen O) (hKO : K ⊆ O)
    (hOU : ∀ j ∈ U, j.1 ∉ O)
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    {a A s : JetBase → ℝ} {c : JetBase → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    (hapos : ∀ x ∈ K, 0 < a (jetSection F x))
    (hcollar : ∀ j ∈ U, s j = 0 ∧ c j = ![(1 - a j ^ 2 / 2) / (1 + a j ^ 2 / 2), 0])
    (hshape : ∀ j ∈ L \ U,
      (0 < a j ∧ 2 * Real.arctan (a j) ≤ A j ∧ s j ∈ Icc (0 : ℝ) 1 ∧
        c j = ![(1 - a j ^ 2 / 2) / (1 + a j ^ 2 / 2), 0]) ∨
      (s j = 1 ∧ Real.pi < A j ∧ c j 0 ^ 2 + c j 1 ^ 2 < 1))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Base → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ O ∧
      (∀ x, |h x| < ε) ∧ ∃ W : Set JetBase, IsOpen W ∧ L ⊆ W ∧
      ∃ ρ : JetBase × ℝ → ℝ, ContDiffOn ℝ ∞ ρ (W ×ˢ univ) ∧
        (∀ j ∈ W, ∀ t, 0 < ρ (j, t)) ∧
        (∀ j, Function.Periodic (fun t => ρ (j, t)) 1) ∧
        (∀ j ∈ W, (∫ t in 0..1, ρ (j, t)) = 1) ∧
        (∀ j ∈ W ∩ C, ∀ t, ρ (j, t) = unitDensity (a j) t) ∧
        ContDiffOn ℝ ∞ (jetAngle ρ a A s (fun j => h j.1)) (W ×ˢ univ) ∧
        (∀ j ∈ W, Function.Periodic (fun t => jetAngle ρ a A s (fun j => h j.1) (j, t)) 1) ∧
        (∀ j ∈ W, (∫ t in 0..1,
          ![Real.cos (jetAngle ρ a A s (fun j => h j.1) (j, t)),
            Real.sin (jetAngle ρ a A s (fun j => h j.1) (j, t))]) = c j) ∧
        (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
          deriv (fun t => jetAngle ρ a A s (fun j => h j.1) (jetSection F x, t)) θ = 0 ↔
            θ = 0 ∨ θ = PositiveDensity.clock ρ (jetSection F x) (1 / 2)) ∧
        ∀ x ∈ K,
          T < fderiv ℝ (fun y => jetAngle ρ a A s (fun j => h j.1) (jetSection F y, 0)) x (0, 1) ∧
          T < fderiv ℝ (fun y => jetAngle ρ a A s (fun j => h j.1)
            (jetSection F y, PositiveDensity.clock ρ (jetSection F x) (1 / 2))) x (0, 1) := by
  have hσ := jetSection_smooth hF
  have haσ := ha.comp hσ
  have hAσ := hA.comp hσ
  have hsσ := hs.comp hσ
  obtain ⟨δ, hδ, hdensity⟩ := small_shift_collar_density ha hA hs hc hU hC hCU hL hcollar hshape
  obtain ⟨h, hh, hhc, hhs, hhb, hlarge⟩ := exists_small_turn_function
    hK hO hKO hP hPK hlocal haσ hAσ hsσ T (lt_min hε hδ)
  let H : JetBase → ℝ := fun j => h j.1
  have hH : ContDiff ℝ ∞ H := hh.comp contDiff_fst
  have hHδ : ∀ j, |H j| < δ := fun j => lt_of_lt_of_le (hhb j.1) (min_le_right _ _)
  have hHz : ∀ j ∈ U, H j = 0 := by
    intro j hj
    by_contra hn
    exact hOU j hj (hhs (subset_tsupport h (Function.mem_support.mpr hn)))
  obtain ⟨W, hW, hLW, ρ, hρ, hpos, hper, hmom, hfixed⟩ := hdensity H hH hHδ hHz
  have hboth (j : JetBase) (hj : j ∈ W) := LoopDensity.mass_and_mean
    (LocalPeriodicCalculus.smooth_slice hW hρ hj).continuous
    ((blendedPath_smooth ha hA hs hH).continuous.comp
      (continuous_const.prodMk continuous_id)) (hmom j hj)
  have hmass : ∀ j ∈ W, (∫ t in 0..1, ρ (j, t)) = 1 := fun j hj => (hboth j hj).1
  have hα := PositiveDensity.reparametrize_smoothOn hW hρ hpos
    (fun j _ => hper j) hmass (unitAngle_smooth ha hA hs hH).contDiffOn
  let Wσ := (jetSection F) ⁻¹' W
  have hWσ : IsOpen Wσ := hW.preimage hσ.continuous
  have hKWσ : K ⊆ Wσ := fun x hx => hLW (hKL hx)
  let ρσ := PositiveDensity.pullbackDensity ρ (jetSection F)
  have hρσ : ContDiffOn ℝ ∞ ρσ (Wσ ×ˢ univ) :=
    PositiveDensity.pullbackDensity_smoothOn hρ hσ.contDiffOn (fun _ hx => hx)
  have hposσ : ∀ x ∈ Wσ, ∀ t, 0 < ρσ (x, t) := fun x hx t => hpos _ hx t
  have hperσ : ∀ x ∈ Wσ, Function.Periodic (fun t => ρσ (x, t)) 1 :=
    fun x _ => hper (jetSection F x)
  have hmassσ : ∀ x ∈ Wσ, (∫ t in 0..1, ρσ (x, t)) = 1 := fun x hx => hmass _ hx
  refine ⟨h, hh, hhc, hhs, (fun x => lt_of_lt_of_le (hhb x) (min_le_left _ _)),
    W, hW, hLW, ρ, hρ, hpos, hper, hmass, hfixed, hα, ?_, ?_, ?_, ?_⟩
  · exact fun j hj => PositiveDensity.reparametrize_periodic hW hρ hpos
      (fun j _ => hper j) hmass (fun j _ => unitAngle_periodic (a j) (A j) (s j) (H j)) hj
  · intro j hj
    exact (PositiveDensity.reparametrize_mean hW hρ hpos (fun j _ => hper j) hmass
      (blendedPath_smooth ha hA hs hH).contDiffOn hj).trans (hboth j hj).2
  · intro x hx θ hθ
    have hnotU : jetSection F x ∉ U := fun hj => hOU _ hj (hKO hx)
    have hAb : 0 < A (jetSection F x) := by
      rcases hshape _ ⟨hKL hx, hnotU⟩ with hbase | hinterior
      · exact lt_of_lt_of_le (mul_pos (by norm_num) (Real.arctan_pos.mpr hbase.1)) hbase.2.1
      · exact Real.pi_pos.trans hinterior.2.1
    have hsb : s (jetSection F x) ∈ Icc (0 : ℝ) 1 := by
      rcases hshape _ ⟨hKL hx, hnotU⟩ with hbase | hinterior
      · exact hbase.2.2.1
      · rw [hinterior.1]; exact ⟨zero_le_one, le_rfl⟩
    simpa only [jetAngle_on_section, ρσ, normalizedAngle, PositiveDensity.clock_pullback] using reparametrized_two_turns
      haσ hAσ hsσ hh hWσ hρσ hposσ hperσ hmassσ (hKWσ hx) (hapos x hx) hAb hsb hθ
  · simpa only [jetAngle_on_section, ρσ, normalizedAngle, PositiveDensity.clock_pullback] using large_turns_after_reparametrization
      haσ hAσ hsσ hh hWσ hKWσ hρσ hposσ hperσ hmassσ hlarge

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ScalarCollarData
attribute [-simp] _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the scalar angle data from a local calibrated collar and an
interior target in the open unit disk. The cutoffs are actual smooth functions. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem scalar_collar_data {C L U : Set E} (hC : IsCompact C)
    (hU : IsOpen U) (hCU : C ⊆ U)
    {β : E → ℝ} {c : E → LoopDensity.Plane}
    (hβ : ContDiffOn ℝ ∞ β U)
    (hβpos : ∀ x ∈ (L \ C) ∩ U, 0 < β x)
    (hcal : ∀ x ∈ U, c x = ![(1 - β x ^ 2 / 2) / (1 + β x ^ 2 / 2), 0])
    (hinterior : ∀ x ∈ L \ C, c x 0 ^ 2 + c x 1 ^ 2 < 1) :
    ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧
      ∃ b s : E → ℝ, ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ s ∧
        (∀ x, s x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x ∈ L \ W, 0 < b x) ∧
        (∀ x ∈ W, b x = β x ∧ s x = 0 ∧
          c x = ![(1 - b x ^ 2 / 2) / (1 + b x ^ 2 / 2), 0]) ∧
        (∀ x ∈ L \ W,
          (0 < b x ∧ 2 * Real.arctan (b x) ≤ Real.pi + 1 ∧
            s x ∈ Icc (0 : ℝ) 1 ∧
            c x = ![(1 - b x ^ 2 / 2) / (1 + b x ^ 2 / 2), 0]) ∨
          (s x = 1 ∧ Real.pi < Real.pi + 1 ∧ c x 0 ^ 2 + c x 1 ^ 2 < 1)) := by
  obtain ⟨W, hW, hCW, hWU, φ, χ, hφ, hχ, _, _, hφr, hχr,
    hχs, hφs, hφone, hχone⟩ := nested_compact_cutoffs hC hU hCU
  let b : E → ℝ := fun x => χ x * β x + (1 - χ x)
  let s : E → ℝ := fun x => 1 - φ x
  have hb : ContDiff ℝ ∞ b :=
    (supported_local_mul hU hχ hβ hχs).add (contDiff_const.sub hχ)
  have hs : ContDiff ℝ ∞ s := contDiff_const.sub hφ
  have hsr (x : E) : s x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨hl, hu⟩ := hφr x
    exact ⟨by dsimp [s] <;> linarith, by dsimp [s] <;> linarith⟩
  have hnc (x : E) (hx : x ∈ L \ W) : x ∈ L \ C :=
    ⟨hx.1, fun hc => hx.2 (hCW hc)⟩
  have hbp (x : E) (hx : x ∈ L \ W) : 0 < b x := by
    obtain ⟨hl, hu⟩ := hχr x
    by_cases hz : χ x = 0
    · simp [b, hz]
    · have hxp : x ∈ U := hχs (subset_tsupport χ (Function.mem_support.mpr hz))
      have hp := hβpos x ⟨hnc x hx, hxp⟩
      have hχp : 0 < χ x := lt_of_le_of_ne hl (Ne.symm hz)
      dsimp [b]
      exact add_pos_of_pos_of_nonneg (mul_pos hχp hp) (sub_nonneg.mpr hu)
  have hwb (x : E) (hx : x ∈ W) : b x = β x := by
    have hφnz : φ x ≠ 0 := by rw [hφone x hx]; norm_num
    have hχx := hχone x (subset_tsupport φ (Function.mem_support.mpr hφnz))
    simp [b, hχx]
  refine ⟨W, hW, hCW, hWU, b, s, hb, hs, hsr, hbp, ?_, ?_⟩
  · intro x hx
    exact ⟨hwb x hx, by simp [s, hφone x hx], by rw [hwb x hx]; exact hcal x (hWU hx)⟩
  · intro x hx
    by_cases hfull : s x = 1
    · exact Or.inr ⟨hfull, by linarith, hinterior x (hnc x hx)⟩
    · have hφnz : φ x ≠ 0 := by intro hz; exact hfull (by simp [s, hz])
      have hxs := subset_tsupport φ (Function.mem_support.mpr hφnz)
      have hbx : b x = β x := by simp [b, hχone x hxs]
      refine Or.inl ⟨hbp x hx, ?_, hsr x, ?_⟩
      · linarith [Real.arctan_lt_pi_div_two (b x)]
      · rw [hbx]
        exact hcal x (hφs hxs)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CalibratedCollarData
attribute [-simp] _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Obtain the scalar loop data from smooth radius and velocity coordinates,
including the extension from the admissible parameter neighborhood. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma calibrated_rational_mean {R v a : ℝ} (hR : 0 < R) (hv : 0 < v)
    (hquad : R ^ 2 = v ^ 2 + a ^ 2) :
    (1 - amplitude R v a ^ 2 / 2) / (1 + amplitude R v a ^ 2 / 2) = v / R := by
  rw [← mean_density_arcX]
  exact calibrated_mean hR hv hquad

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem calibrated_collar_data {C L U Ω : Set E}
    (hC : IsCompact C) (hL : IsCompact L) (hCL : C ⊆ L)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    {R u v a : E → ℝ} (hR : ContDiffOn ℝ ∞ R Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ContDiffOn ℝ ∞ a Ω)
    (hRp : ∀ x ∈ Ω, 0 < R x)
    (hquad : ∀ x ∈ Ω, R x ^ 2 = u x ^ 2 + v x ^ 2 + a x ^ 2)
    (hup : ∀ x ∈ U, 0 < u x) (hvz : ∀ x ∈ U, v x = 0)
    (hap : ∀ x ∈ L \ C, 0 < a x) :
    ∃ c : E → LoopDensity.Plane, ContDiff ℝ ∞ c ∧
      ∃ V : Set E, IsOpen V ∧ L ⊆ V ∧ V ⊆ Ω ∧
      (∀ x ∈ V, c x = ![u x / R x, v x / R x]) ∧
      ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧
        ∃ b s : E → ℝ, ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ s ∧
          (∀ x, s x ∈ Icc (0 : ℝ) 1) ∧
          (∀ x ∈ L \ W, 0 < b x) ∧
          (∀ x ∈ W, b x = amplitude (R x) (u x) (a x) ∧ s x = 0 ∧
            c x = ![(1 - b x ^ 2 / 2) / (1 + b x ^ 2 / 2), 0]) ∧
          (∀ x ∈ L \ W,
            (0 < b x ∧ 2 * Real.arctan (b x) ≤ Real.pi + 1 ∧
              s x ∈ Icc (0 : ℝ) 1 ∧
              c x = ![(1 - b x ^ 2 / 2) / (1 + b x ^ 2 / 2), 0]) ∨
            (s x = 1 ∧ Real.pi < Real.pi + 1 ∧ c x 0 ^ 2 + c x 1 ^ 2 < 1)) := by
  let target : E → LoopDensity.Plane := fun x => ![u x / R x, v x / R x]
  have htarget : ContDiffOn ℝ ∞ target Ω := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact hu.div hR (fun x hx => (hRp x hx).ne')
    · exact hv.div hR (fun x hx => (hRp x hx).ne')
  obtain ⟨V, hV, hLV, hVΩ, c, hc, hct⟩ := compact_smooth_extension hL hΩ hLΩ htarget
  let U' := U ∩ V
  have hU' : IsOpen U' := hU.inter hV
  have hCU' : C ⊆ U' := fun x hx => ⟨hCU hx, hLV (hCL hx)⟩
  have hβ : ContDiffOn ℝ ∞ (fun x => amplitude (R x) (u x) (a x)) U' := by
    exact (contDiffOn_const.mul (ha.mono (inter_subset_left.trans hUΩ))).div
      ((hR.add hu).mono (inter_subset_left.trans hUΩ))
      (fun x hx => (add_pos (hRp x (hUΩ hx.1)) (hup x hx.1)).ne')
  have hβp : ∀ x ∈ (L \ C) ∩ U', 0 < amplitude (R x) (u x) (a x) := by
    intro x hx
    exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hap x hx.1))
      (add_pos (hRp x (hUΩ hx.2.1)) (hup x hx.2.1))
  have hcal : ∀ x ∈ U', c x =
      ![(1 - amplitude (R x) (u x) (a x) ^ 2 / 2) /
        (1 + amplitude (R x) (u x) (a x) ^ 2 / 2), 0] := by
    intro x hx
    rw [hct hx.2]
    have hq : R x ^ 2 = u x ^ 2 + a x ^ 2 := by
      simpa [hvz x hx.1] using hquad x (hUΩ hx.1)
    rw [calibrated_rational_mean (hRp x (hUΩ hx.1)) (hup x hx.1) hq]
    simp [target, hvz x hx.1]
  have hi : ∀ x ∈ L \ C, c x 0 ^ 2 + c x 1 ^ 2 < 1 := by
    intro x hx
    rw [hct (hLV hx.1)]
    change (u x / R x) ^ 2 + (v x / R x) ^ 2 < 1
    have hr := hRp x (hLΩ hx.1)
    have hq := hquad x (hLΩ hx.1)
    have ha' := hap x hx
    rw [div_pow, div_pow, ← add_div, div_lt_one (sq_pos_of_pos hr)]
    nlinarith [sq_pos_of_pos ha']
  obtain ⟨W, hW, hCW, hWU', b, s, hb, hs, hsr, hbp, hw, hshape⟩ :=
    scalar_collar_data hC hU' hCU' hβ hβp hcal hi
  exact ⟨c, hc, V, hV, hLV, hVΩ, hct, W, hW, hCW,
    hWU'.trans inter_subset_left, b, s, hb, hs, hsr, hbp, hw, hshape⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityCircleLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lift a normalized planar loop to the actual four-dimensional velocity
plane, retaining its exact mean, length, and leading metric. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma planeLift_unit {e₁ e₂ : Vec} {p : LoopDensity.Plane}
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hp : p 0 ^ 2 + p 1 ^ 2 = 1) :
    planeLift e₁ e₂ p ⬝ᵥ planeLift e₁ e₂ p = 1 := by
  have horth' : e₂ ⬝ᵥ e₁ = 0 := (dotProduct_comm _ _).trans horth
  simp only [planeLift_apply, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h₁, h₂, horth, horth', mul_zero, zero_add, add_zero, mul_one]
  nlinarith

lemma planeLift_scaled_length {e₁ e₂ : Vec} {p : LoopDensity.Plane}
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hp : p 0 ^ 2 + p 1 ^ 2 = 1) (R : ℝ) :
    (R • planeLift e₁ e₂ p) ⬝ᵥ (R • planeLift e₁ e₂ p) = R ^ 2 := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    planeLift_unit h₁ h₂ horth hp]
  ring

lemma planeLift_mean (e₁ e₂ : Vec) (R : ℝ) {p : ℝ → LoopDensity.Plane}
    (hp : Continuous p) {c : LoopDensity.Plane} (hmean : (∫ t in 0..1, p t) = c) :
    (∫ t in 0..1, R • planeLift e₁ e₂ (p t)) = R • planeLift e₁ e₂ c := by
  rw [intervalIntegral.integral_smul]
  have hi : IntervalIntegrable p MeasureTheory.volume 0 1 := hp.intervalIntegrable 0 1
  have he := (planeLift e₁ e₂).intervalIntegral_comp_comm hi
  change R • (∫ t in 0..1, (planeLift e₁ e₂) (p t)) = _
  rw [he, hmean]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityPlaneBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinates in the actual two-dimensional velocity plane. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma velocity_frame_independent {Y C e₁ e₂ : Vec}
    (hD : gramDet Y C ≠ 0) (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (h12 : e₁ ⬝ᵥ e₂ = 0) (hY1 : Y ⬝ᵥ e₁ = 0) (hY2 : Y ⬝ᵥ e₂ = 0)
    (hC1 : C ⬝ᵥ e₁ = 0) (hC2 : C ⬝ᵥ e₂ = 0) :
    LinearIndependent ℝ ![Y, C, e₁, e₂] := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have he : a 0 • Y + (a 1 • C + (a 2 • e₁ + a 3 • e₂)) = 0 := by
    simpa [Fin.sum_univ_succ] using ha
  have hy := congrArg (fun w => Y ⬝ᵥ w) he
  have hc := congrArg (fun w => C ⬝ᵥ w) he
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hY1, hY2, hC1, hC2,
    mul_zero, add_zero, dotProduct_zero, dotProduct_comm C Y] at hy hc
  have haD : a 0 * gramDet Y C = 0 := by
    unfold gramDet
    linear_combination (C ⬝ᵥ C) * hy - (Y ⬝ᵥ C) * hc
  have hbD : a 1 * gramDet Y C = 0 := by
    unfold gramDet
    linear_combination (Y ⬝ᵥ Y) * hc - (Y ⬝ᵥ C) * hy
  have ha0 := (mul_eq_zero.mp haD).resolve_right hD
  have ha1 := (mul_eq_zero.mp hbD).resolve_right hD
  have hz : a 2 • e₁ + a 3 • e₂ = 0 := by simpa [ha0, ha1] using he
  have h2 := congrArg (fun w => e₁ ⬝ᵥ w) hz
  have h3 := congrArg (fun w => e₂ ⬝ᵥ w) hz
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, h₁, h₂, h12,
    dotProduct_comm e₂ e₁, mul_one, mul_zero, add_zero, zero_add, dotProduct_zero] at h2 h3
  intro i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact h2
  · exact h3

lemma orthogonal_frame_eq_zero {Y C e₁ e₂ w : Vec}
    (hlin : LinearIndependent ℝ ![Y, C, e₁, e₂])
    (hY : Y ⬝ᵥ w = 0) (hC : C ⬝ᵥ w = 0)
    (h1 : e₁ ⬝ᵥ w = 0) (h2 : e₂ ⬝ᵥ w = 0) : w = 0 := by
  have hs := hlin.span_eq_top_of_card_eq_finrank (by simp [Vec])
  have hw : w ∈ Submodule.span ℝ (Set.range ![Y, C, e₁, e₂]) := by
    rw [hs]
    trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  apply dotProduct_self_eq_zero.mp
  calc
    w ⬝ᵥ w = (∑ i, a i • (![Y, C, e₁, e₂] i)) ⬝ᵥ w := by rw [ha]
    _ = 0 := by simp [Fin.sum_univ_succ, add_dotProduct, smul_dotProduct, hY, hC, h1, h2]

theorem plane_coordinates_reconstruct {Y C e₁ e₂ v : Vec}
    (hD : gramDet Y C ≠ 0) (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (h12 : e₁ ⬝ᵥ e₂ = 0) (hY1 : Y ⬝ᵥ e₁ = 0) (hY2 : Y ⬝ᵥ e₂ = 0)
    (hC1 : C ⬝ᵥ e₁ = 0) (hC2 : C ⬝ᵥ e₂ = 0)
    (hYv : Y ⬝ᵥ v = 0) (hCv : C ⬝ᵥ v = 0) :
    planeLift e₁ e₂ (planeCoordinates e₁ e₂ v) = v := by
  apply sub_eq_zero.mp
  apply orthogonal_frame_eq_zero (velocity_frame_independent hD h₁ h₂ h12 hY1 hY2 hC1 hC2)
  all_goals simp [planeLift_apply, planeCoordinates, dotProduct_sub, dotProduct_add,
    dotProduct_smul, hY1, hY2, hC1, hC2, hYv, hCv, h₁, h₂, h12,
    dotProduct_comm e₂ e₁, dotProduct_comm e₁ v, dotProduct_comm e₂ v]

lemma plane_coordinates_length {Y C e₁ e₂ v : Vec}
    (hD : gramDet Y C ≠ 0) (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (h12 : e₁ ⬝ᵥ e₂ = 0) (hY1 : Y ⬝ᵥ e₁ = 0) (hY2 : Y ⬝ᵥ e₂ = 0)
    (hC1 : C ⬝ᵥ e₁ = 0) (hC2 : C ⬝ᵥ e₂ = 0)
    (hYv : Y ⬝ᵥ v = 0) (hCv : C ⬝ᵥ v = 0) :
    (v ⬝ᵥ e₁) ^ 2 + (v ⬝ᵥ e₂) ^ 2 = v ⬝ᵥ v := by
  have hr := plane_coordinates_reconstruct hD h₁ h₂ h12 hY1 hY2 hC1 hC2 hYv hCv
  have hd := congrArg (fun w => w ⬝ᵥ w) hr
  simpa [planeLift_apply, planeCoordinates, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, h₁, h₂, h12, dotProduct_comm e₂ e₁, pow_two] using hd

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityCoordinateData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth velocity coordinates and their calibrated collar values. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_smul_normalize {v : Vec} (hv : v ≠ 0) :
    Real.sqrt (v ⬝ᵥ v) • normalize v = v := by
  simp [normalize, smul_smul, (Real.sqrt_pos.mpr (dot_self_pos hv)).ne']

lemma dot_normalize_self {v : Vec} (hv : v ≠ 0) :
    v ⬝ᵥ normalize v = Real.sqrt (v ⬝ᵥ v) := by
  have hp := dot_self_pos hv
  have hn := (Real.sqrt_pos.mpr hp).ne'
  simp only [normalize, dotProduct_smul, smul_eq_mul]
  apply (inv_mul_eq_iff_eq_mul₀ hn).mpr
  nlinarith [Real.sq_sqrt hp.le]

lemma collar_coordinates {v e₁ e₂ : Vec} (hv : v ≠ 0)
    (he : e₁ = normalize v) (horth : e₁ ⬝ᵥ e₂ = 0) :
    0 < v ⬝ᵥ e₁ ∧ v ⬝ᵥ e₂ = 0 := by
  refine ⟨?_, ?_⟩
  · rw [he, dot_normalize_self hv]
    exact Real.sqrt_pos.mpr (dot_self_pos hv)
  · calc
      v ⬝ᵥ e₂ = (Real.sqrt (v ⬝ᵥ v) • e₁) ⬝ᵥ e₂ := by rw [he, norm_smul_normalize hv]
      _ = 0 := by rw [smul_dotProduct, horth, smul_zero]

lemma velocityRadius_sq (v : Vec) (a : ℝ) :
    velocityRadius v a ^ 2 = v ⬝ᵥ v + a ^ 2 := by
  apply Real.sq_sqrt
  exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (sq_nonneg a)

lemma velocityRadius_smoothOn {v : E → Vec} {a : E → ℝ} {U : Set E}
    (hv : ContDiffOn ℝ ∞ v U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, v x ≠ 0 ∨ a x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => velocityRadius (v x) (a x)) U := by
  apply ((dot_smoothOn hv hv).add (ha.pow 2)).sqrt
  intro x hx
  have hp := velocityRadius_pos (hn x hx)
  exact (Real.sqrt_pos.mp hp).ne'

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_GeometricControlledVelocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual four-dimensional velocity with exact mean and
metric, from its smooth geometric frame. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes TransverseSmallFunction

lemma scaled_coordinates_reconstruct {e₁ e₂ v : Vec} {R : ℝ} (hR : R ≠ 0)
    (hr : planeLift e₁ e₂ (planeCoordinates e₁ e₂ v) = v) :
    R • planeLift e₁ e₂ ![(v ⬝ᵥ e₁) / R, (v ⬝ᵥ e₂) / R] = v := by
  calc
    _ = planeLift e₁ e₂ (planeCoordinates e₁ e₂ v) := by
      ext i
      simp only [planeLift_apply, planeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      field_simp
    _ = v := hr

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ConstructedSurfaceLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the analytic surface-loop input from the geometric frame and
the controlled angle; no periodic velocity family is assumed here. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates
open VelocityFrame NormalFrame TransverseSmallFunction

lemma jetSlot_smooth (i : Fin 5) :
    ContDiff ℝ ∞ (fun j : CollarVelocity.JetBase => j.2 i) :=
  (ContinuousLinearMap.proj i : RealTwoJet →L[ℝ] Vec).contDiff.comp contDiff_snd

lemma jetNormal_smooth {Ω : Set CollarVelocity.JetBase}
    (hD : ∀ j ∈ Ω, gramDet (j.2 1) (j.2 4) ≠ 0) :
    ContDiffOn ℝ ∞ jetNormal Ω := by
  intro j hj
  exact (contDiffAt_realNormalPart (jetSlot_smooth 1).contDiffAt
    (jetSlot_smooth 4).contDiffAt (jetSlot_smooth 0).contDiffAt (hD j hj)).contDiffWithinAt

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmallCollarAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small collar amplitude controls every angle after any clock change.
The collar and permitted translation size are fixed before prescribing turns. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.CollarVelocity

lemma abs_baseAngle_le (a t : ℝ) : |baseAngle a t| ≤ 2 * Real.arctan |a| := by
  have hab : |a * Real.cos t| ≤ |a| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one t)
  have hl := Real.arctan_strictMono.monotone (neg_le_of_abs_le hab)
  have hu := Real.arctan_strictMono.monotone (le_of_abs_le hab)
  rw [Real.arctan_neg] at hl
  rw [baseAngle,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hl,hu⟩) (by norm_num)

lemma abs_unitAngle_collar_le (a A h t : ℝ) :
    |unitAngle a A 0 h t| ≤ |h| + 2 * Real.arctan |a| := by
  calc
    |unitAngle a A 0 h t| = |h + baseAngle a (2 * Real.pi * t)| := by
      simp [unitAngle,blendedAngle]
    _ ≤ |h| + |baseAngle a (2 * Real.pi * t)| := abs_add_le _ _
    _ ≤ |h| + 2 * Real.arctan |a| := add_le_add_right (abs_baseAngle_le _ _) _

variable {E : Type} [NormedAddCommGroup E]

lemma small_collar_angle_window {C W : Set E} (hW : IsOpen W) (hCW : C ⊆ W)
    {b : E → ℝ} (hb : Continuous b) (hbC : ∀ x ∈ C, b x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set E, IsOpen V ∧ C ⊆ V ∧ V ⊆ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (A s h : E → ℝ) (ρ : E × ℝ → ℝ),
        (∀ x ∈ W, s x = 0) → (∀ x, |h x| < δ) →
        ∀ x ∈ V, ∀ t : ℝ,
        |PositiveDensity.reparametrize ρ
          (fun z => unitAngle (b z.1) (A z.1) (s z.1) (h z.1) z.2) (x,t)| < ε := by
  let V := W ∩ {x | 2 * Real.arctan |b x| < ε/2}
  have hV : IsOpen V := hW.inter (isOpen_lt
    (continuous_const.mul (Real.continuous_arctan.comp hb.abs)) continuous_const)
  have hCV : C ⊆ V := by
    intro x hx
    refine ⟨hCW hx,?_⟩
    simp only [mem_ofPred_eq,hbC x hx,abs_zero,Real.arctan_zero,mul_zero]
    positivity
  refine ⟨V,hV,hCV,inter_subset_left,ε/2,half_pos hε,?_⟩
  intro A s h ρ hs hh x hx t
  change |unitAngle (b x) (A x) (s x) (h x) (PositiveDensity.inverseClock ρ x t)| < ε
  rw [hs x hx.1]
  have hxsmall : 2 * Real.arctan |b x| < ε/2 := hx.2
  exact (abs_unitAngle_collar_le _ _ _ _).trans_lt (by linarith [hh x])

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CalibratedCollarFamily
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small-angle collar is chosen before the compact interior curve set
and before its turn threshold. The later translation may overlap that collar. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.CollarVelocity
open RealModes TransverseSmallFunction

theorem calibrated_jet_collar_family {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {C L U Ω : Set JetBase} (hC : IsCompact C) (hL : IsCompact L) (hCL : C ⊆ L)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    {R u v a : JetBase → ℝ} (hR : ContDiffOn ℝ ∞ R Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hRp : ∀ j ∈ Ω, 0 < R j)
    (hquad : ∀ j ∈ Ω, R j ^ 2 = u j ^ 2 + v j ^ 2 + a j ^ 2)
    (hup : ∀ j ∈ U, 0 < u j) (hvz : ∀ j ∈ U, v j = 0)
    (hap : ∀ j ∈ L \ C, 0 < a j) (haC : ∀ j ∈ C, a j = 0) :
    ∃ W : Set JetBase, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : Set JetBase, IsOpen V ∧ C ⊆ V ∧ V ⊆ W ∧
      ∀ (K O P : Set Base), IsCompact K → MapsTo (jetSection F) K L →
        IsOpen O → K ⊆ O → (∀ j ∈ C, j.1 ∉ closure O) →
        P.Finite → P ⊆ K →
        (∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
          ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
            fderiv ℝ f p (0,1) ≠ 0) →
      ∀ T : ℝ, ∃ Z : Set JetBase, IsOpen Z ∧ L ⊆ Z ∧ Z ⊆ Ω ∧
        ∃ α : JetBase × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
          (∀ j ∈ Z, (∫ t in 0..1, ![Real.cos (α (j,t)),Real.sin (α (j,t))]) =
            ![u j/R j,v j/R j]) ∧
          (∀ j ∈ V, ∀ t, |α (j,t)| < ε) ∧
          (∃ W' : Set JetBase, IsOpen W' ∧ C ⊆ W' ∧ W' ⊆ W ∧
            ∀ j ∈ W', a j = 0 → ∀ t, α (j,t) = 0) ∧
          ∃ τ : Base → ℝ,
            (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
              deriv (fun t => α (jetSection F x,t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
            ∀ x ∈ K,
              T < fderiv ℝ (fun y => α (jetSection F y,0)) x (0,1) ∧
              T < fderiv ℝ (fun y => α (jetSection F y,τ x)) x (0,1) := by
  obtain ⟨c,hc,V₀,hV₀,hLV₀,hV₀Ω,hcL,W,hW,hCW,hWU,b,s,hb,hs,hsr,hbp,hw,hshape⟩ :=
    calibrated_collar_data hC hL hCL hU hΩ hCU hUΩ hLΩ hR hu hv ha hRp hquad hup hvz hap
  have hbC : ∀ j ∈ C, b j = 0 := by
    intro j hj
    rw [(hw j (hCW hj)).1,haC j hj]
    simp [amplitude]
  have hbpos : ∀ j ∈ L \ C, 0 < b j := by
    intro j hj
    by_cases hjW : j ∈ W
    · rw [(hw j hjW).1]
      exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hap j hj))
        (add_pos (hRp j (hLΩ hj.1)) (hup j (hWU hjW)))
    · exact hbp j ⟨hj.1,hjW⟩
  refine ⟨W,hW,hCW,hWU,?_⟩
  intro ε hε
  obtain ⟨V,hV,hCV,hVW,δ,hδ,hangle⟩ := small_collar_angle_window hW hCW hb.continuous hbC hε
  refine ⟨V,hV,hCV,hVW,?_⟩
  intro K O P hK hKL hO hKO hCO hP hPK hlocal T
  let W' : Set JetBase := W ∩ (Prod.fst ⁻¹' closure O)ᶜ
  have hW' : IsOpen W' := hW.inter (isClosed_closure.preimage continuous_fst).isOpen_compl
  have hCW' : C ⊆ W' := fun j hj => ⟨hCW hj,hCO j hj⟩
  have hW'W : W' ⊆ W := inter_subset_left
  have hOW' : ∀ j ∈ W', j.1 ∉ O := fun j hj ho => hj.2 (subset_closure ho)
  have hbK : ∀ x ∈ K, 0 < b (jetSection F x) := by
    intro x hx
    apply hbpos _ ⟨hKL hx,?_⟩
    intro hxc
    exact hCO _ hxc (subset_closure (hKO hx))
  have hshape' : ∀ j ∈ L \ W',
      (0 < b j ∧ 2 * Real.arctan (b j) ≤ Real.pi+1 ∧ s j ∈ Icc (0 : ℝ) 1 ∧
        c j = ![(1-b j^2/2)/(1+b j^2/2),0]) ∨
      (s j = 1 ∧ Real.pi < Real.pi+1 ∧ c j 0^2+c j 1^2 < 1) := by
    intro j hj
    by_cases hjW : j ∈ W
    · left
      refine ⟨hbpos j ⟨hj.1,fun hc => hj.2 (hCW' hc)⟩,?_,hsr j,(hw j hjW).2.2⟩
      linarith [Real.arctan_lt_pi_div_two (b j)]
    · exact hshape j ⟨hj.1,hjW⟩
  obtain ⟨h,_,_,hhs,hhδ,V₁,hV₁,hLV₁,ρ,_,_,_,_,_,hα,hper,hmean,hturn,hlarge⟩ :=
    controlled_jet_loop hF hK hL hKL hO hKO hOW' hW' hC.isClosed hCW'
      hP hPK hlocal hb (A := fun _ => Real.pi+1) contDiff_const hs hc hbK
      (fun j hj => ⟨(hw j (hW'W hj)).2.1,(hw j (hW'W hj)).2.2⟩) hshape' T hδ
  let α := jetAngle ρ b (fun _ => Real.pi+1) s (fun j => h j.1)
  have hz (j : JetBase) (hj : j ∈ W') : h j.1 = 0 := by
    by_contra hn
    exact hOW' j hj (hhs (subset_tsupport h (Function.mem_support.mpr hn)))
  refine ⟨V₁ ∩ V₀,hV₁.inter hV₀,subset_inter hLV₁ hLV₀,
    inter_subset_right.trans hV₀Ω,α,hα.mono (prod_mono inter_subset_left Subset.rfl),
    (fun j hj => hper j hj.1),(fun j hj => (hmean j hj.1).trans (hcL j hj.2)),?_,
    ⟨W',hW',hCW',hW'W,?_⟩,_,hturn,hlarge⟩
  · intro j hj t
    exact hangle (fun _ => Real.pi+1) s (fun j => h j.1) ρ
      (fun j hj => (hw j hj).2.1) (fun j => hhδ j.1) j hj t
  · intro j hj haz t
    have hbz : b j = 0 := by rw [(hw j (hW'W hj)).1]; simp [amplitude,haz]
    simp [α,jetAngle,PositiveDensity.reparametrize,unitAngle,blendedAngle,baseAngle,
      hbz,(hw j (hW'W hj)).2.1,hz j hj]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ConstructedCollarFamily
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported analytic loops with a small-angle collar fixed before the
interior compact set and its large turn derivative are selected. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates
open VelocityFrame NormalFrame TransverseSmallFunction

theorem constructed_surface_collar_family_oai {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {C₀ L U Ω : Set CollarVelocity.JetBase}
    (hC₀ : IsCompact C₀) (hL : IsCompact L) (hCL : C₀ ⊆ L)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C₀ ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    {e₁ e₂ : CollarVelocity.JetBase → Vec} {a : CollarVelocity.JetBase → ℝ}
    (he₁ : ContDiffOn ℝ ∞ e₁ Ω) (he₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hD : ∀ j ∈ Ω, gramDet (j.2 1) (j.2 4) ≠ 0)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    (hcollar : ∀ j ∈ U, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j))
    (hn : ∀ j ∈ Ω, jetNormal j ≠ 0 ∨ a j ≠ 0)
    (hap : ∀ j ∈ L \ C₀, 0 < a j) (haC : ∀ j ∈ C₀, a j = 0) :
    ∃ W : Set CollarVelocity.JetBase, IsOpen W ∧ C₀ ⊆ W ∧ W ⊆ U ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : Set CollarVelocity.JetBase, IsOpen V ∧ C₀ ⊆ V ∧ V ⊆ W ∧
      ∀ (K O P : Set SmallModes.Base), IsCompact K → MapsTo (CollarVelocity.jetSection F) K L →
        IsOpen O → K ⊆ O → (∀ j ∈ C₀, j.1 ∉ closure O) → P.Finite → P ⊆ K →
        (∀ p ∈ K \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
          ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
            fderiv ℝ f p (0,1) ≠ 0) →
      ∀ T : ℝ, ∃ Z : TopologicalSpace.Opens CollarVelocity.JetBase,
        L ⊆ Z ∧ (Z : Set CollarVelocity.JetBase) ⊆ Ω ∧
        ∃ l : Loop (jetDomain Z), (∀ J, l.amplitude J = a (decode J)) ∧
          (∃ W' : Set CollarVelocity.JetBase, IsOpen W' ∧ C₀ ⊆ W' ∧ W' ⊆ W ∧
            ∀ J, decode J ∈ W' → a (decode J) = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
          ∃ α : CollarVelocity.JetBase × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
            (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
            (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J)) •
              direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
            (∀ j ∈ V, ∀ t, |α (j,t)| < ε) ∧
            ∃ τ : SmallModes.Base → ℝ,
              (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
                deriv (fun t => α (CollarVelocity.jetSection F x,t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
              ∀ x ∈ K, T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,0)) x (0,1) ∧
                T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,τ x)) x (0,1) := by
  let R := fun j => velocityRadius (jetNormal j) (a j)
  let u := fun j => jetNormal j ⬝ᵥ e₁ j
  let w := fun j => jetNormal j ⬝ᵥ e₂ j
  have hv := jetNormal_smooth hD
  have hR := velocityRadius_smoothOn hv ha hn
  have hRp : ∀ j ∈ Ω, 0 < R j := fun j hj => velocityRadius_pos (hn j hj)
  have hvperp (j : CollarVelocity.JetBase) (hj : j ∈ Ω) :
      j.2 1 ⬝ᵥ jetNormal j = 0 ∧ j.2 4 ⬝ᵥ jetNormal j = 0 :=
    realNormalPart_perp _ _ _ (hD j hj)
  have hreconstruct (j : CollarVelocity.JetBase) (hj : j ∈ Ω) :
      planeLift (e₁ j) (e₂ j) (VelocityFrame.planeCoordinates (e₁ j) (e₂ j) (jetNormal j)) = jetNormal j := by
    obtain ⟨h1,h2,h12,hy1,hc1,hy2,hc2⟩ := hframe j hj
    exact plane_coordinates_reconstruct (hD j hj) h1 h2 h12 hy1 hy2 hc1 hc2
      (hvperp j hj).1 (hvperp j hj).2
  have hquad (j : CollarVelocity.JetBase) (hj : j ∈ Ω) :
      R j^2 = u j^2+w j^2+a j^2 := by
    obtain ⟨h1,h2,h12,hy1,hc1,hy2,hc2⟩ := hframe j hj
    have hlen := plane_coordinates_length (hD j hj) h1 h2 h12 hy1 hy2 hc1 hc2
      (hvperp j hj).1 (hvperp j hj).2
    change velocityRadius (jetNormal j) (a j)^2 = _
    rw [velocityRadius_sq,← hlen]
  have huc (j : CollarVelocity.JetBase) (hj : j ∈ U) : 0 < u j ∧ w j = 0 :=
    collar_coordinates (hcollar j hj).1 (hcollar j hj).2 (hframe j (hUΩ hj)).2.2.1
  obtain ⟨W,hW,hCW,hWU,hfamily⟩ := CollarVelocity.calibrated_jet_collar_family hF hC₀ hL hCL
    hU hΩ hCU hUΩ hLΩ hR (dot_smoothOn hv he₁) (dot_smoothOn hv he₂) ha hRp hquad
    (fun j hj => (huc j hj).1) (fun j hj => (huc j hj).2) hap haC
  refine ⟨W,hW,hCW,hWU,?_⟩
  intro ε hε
  obtain ⟨V,hV,hCV,hVW,hfamily'⟩ := hfamily ε hε
  refine ⟨V,hV,hCV,hVW,?_⟩
  intro K O P hK hKL hO hKO hCO hP hPK hlocal T
  obtain ⟨Z,hZ,hLZ,hZΩ,α,hα,hper,hmean,hsmall,hzero,τ,hturn,hlarge⟩ :=
    hfamily' K O P hK hKL hO hKO hCO hP hPK hlocal T
  let V₀ : CollarVelocity.JetBase × ℝ → Vec := fun z =>
    R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)
  have hVs : ContDiffOn ℝ ∞ V₀ (Z ×ˢ univ) :=
    ((hR.mono hZΩ).comp contDiffOn_fst (fun z hz => hz.1)).smul
      ((hα.cos.smul ((he₁.mono hZΩ).comp contDiffOn_fst (fun z hz => hz.1))).add
        (hα.sin.smul ((he₂.mono hZΩ).comp contDiffOn_fst (fun z hz => hz.1))))
  have hVy : ∀ j ∈ Z, ∀ t, j.2 1 ⬝ᵥ V₀ (j,t) = 0 := by
    intro j hj t
    simp [V₀,direction,dotProduct_smul,dotProduct_add,(hframe j (hZΩ hj)).2.2.2.1,
      (hframe j (hZΩ hj)).2.2.2.2.2.1]
  have hVc : ∀ j ∈ Z, ∀ t, j.2 4 ⬝ᵥ V₀ (j,t) = 0 := by
    intro j hj t
    simp [V₀,direction,dotProduct_smul,dotProduct_add,(hframe j (hZΩ hj)).2.2.2.2.1,
      (hframe j (hZΩ hj)).2.2.2.2.2.2]
  have hlen : ∀ j ∈ Z, ∀ t, V₀ (j,t) ⬝ᵥ V₀ (j,t) = jetNormal j ⬝ᵥ jetNormal j + a j^2 := by
    intro j hj t
    obtain ⟨h1,h2,h12,_,_,_,_⟩ := hframe j (hZΩ hj)
    exact (planeLift_scaled_length (p := ![Real.cos (α (j,t)),Real.sin (α (j,t))])
      h1 h2 h12 (Real.cos_sq_add_sin_sq (α (j,t))) (R j)).trans (velocityRadius_sq _ _)
  have hmean' : ∀ j ∈ Z, (∫ t in 0..1, V₀ (j,t)) = jetNormal j := by
    intro j hj
    have hp : Continuous (fun t => ![Real.cos (α (j,t)),Real.sin (α (j,t))]) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact Real.continuous_cos.comp (LocalPeriodicCalculus.smooth_slice hZ hα hj).continuous
      · exact Real.continuous_sin.comp (LocalPeriodicCalculus.smooth_slice hZ hα hj).continuous
    exact (planeLift_mean (e₁ j) (e₂ j) (R j) hp (hmean j hj)).trans
      (scaled_coordinates_reconstruct (hRp j (hZΩ hj)).ne' (hreconstruct j (hZΩ hj)))
  let Z' : TopologicalSpace.Opens CollarVelocity.JetBase := ⟨Z,hZ⟩
  have hVp : ∀ j ∈ Z, Function.Periodic (fun t => V₀ (j,t)) 1 := by
    intro j hj
    have he : (fun t => V₀ (j,t)) =
        (fun θ => R j • direction (e₁ j) (e₂ j) θ) ∘ (fun t => α (j,t)) := rfl
    rw [he]
    exact (hper j hj).comp _
  let l : Loop (jetDomain Z') := Loop.ofGeometric (ha.mono hZΩ) hVs
    hVp (fun j hj => hD j (hZΩ hj))
    (fun j hj => hn j (hZΩ hj)) hVy hVc hlen hmean'
  refine ⟨Z',hLZ,hZΩ,l,(fun _ => rfl),?_,α,hα,hper,(fun _ _ => rfl),hsmall,τ,hturn,hlarge⟩
  obtain ⟨W',hW',hCW',hW'W,hzero'⟩ := hzero
  refine ⟨W',hW',hCW',hW'W,?_⟩
  intro J hJ haz t
  change R (decode J) • direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)) = _
  rw [hzero' (decode J) hJ haz t]
  simp only [direction,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero]
  change velocityRadius (jetNormal (decode J)) (a (decode J)) • e₁ (decode J) = _
  rw [haz,(hcollar (decode J) (hWU (hW'W hJ))).2]
  change velocityRadius (jetNormal (decode J)) 0 • normalize (jetNormal (decode J)) =
    jetNormal (decode J)
  simpa only [velocityRadius,zero_pow (by decide : 2 ≠ 0),add_zero] using
    norm_smul_normalize (hcollar (decode J) (hWU (hW'W hJ))).1

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family_oai
