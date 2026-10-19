-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.faber_hilbert_coefficient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:31:19.800661+00:00
-- url     : https://prove2.me/submissions/561a519c-b228-4308-b859-a54be024115a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberEnergy.lean:L80-L113
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.faber_hilbert_coefficient_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Theorems.Thm_OAI_DirectCrouzeix_Faber_boundaryCoefficient_no_nonnegative
import Theorems.Thm_OAI_DirectCrouzeix_Faber_boundaryKernel_character
import Theorems.Thm_OAI_DirectCrouzeix_Faber_boundaryKernel_marginals
import Theorems.Thm_OAI_DirectCrouzeix_Faber_energy_orthogonal_positiveSeries
import Theorems.Thm_OAI_DirectCrouzeix_Faber_faberBasis_exterior
import Theorems.Thm_OAI_DirectCrouzeix_Faber_hasDerivAt_chordIntegral_left
import Theorems.Thm_OAI_DirectCrouzeix_Faber_integral_inner_positiveSeries
import Theorems.Thm_OAI_DirectCrouzeix_Faber_markov_kernel_contraction

-- ---- from OAI.Analysis.DirectCrouzeix.CompactIntegrals ----
namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem integrable_of_continuous_compact {α : Type u_87} {E : Type u_88} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuousOn_integral_compact {α : Type u_89} {β : Type u_90} {E : Type u_91}
    [MetricSpace α] [ProperSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [CompactSpace β] [SecondCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure β) [IsFiniteMeasure μ] {s : Set α} (hs : IsOpen s)
    {f : α → β → E} (hf : ContinuousOn f.uncurry (s ×ˢ univ)) :
    ContinuousOn (fun x => ∫ t, f x t ∂μ) s := by
  intro x hx
  obtain ⟨ε,hε,hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
  have hc : Continuous (fun p : closedBall x ε × β => f p.1 p.2) := by
    apply hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    intro p
    exact ⟨hsub p.1.property,mem_univ _⟩
  have hi : Continuous (fun y : closedBall x ε => ∫ t, f y t ∂μ) := by
    simpa using continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ
  have hi' : ContinuousOn (fun y => ∫ t, f y t ∂μ) (closedBall x ε) :=
    continuousOn_iff_continuous_domRestrict.mpr hi
  exact (hi'.continuousAt (closedBall_mem_nhds x hε)).continuousWithinAt

theorem chord_mem {s : Set ℂ} (hs : Convex ℝ s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : chord u v t ∈ s :=
  hs hu hv (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel _ _)

theorem continuous_chord : Continuous (fun p : (ℂ × ℂ) × ℝ => chord p.1.1 p.1.2 p.2) := by
  unfold chord
  fun_prop

theorem continuousOn_chordIntegral {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : ContinuousOn f s) {w : Parameter → ℂ} (hw : Continuous w) :
    ContinuousOn (fun p : ℂ × ℂ => chordIntegral f w p.1 p.2) (s ×ˢ s) := by
  apply continuousOn_integral_compact volume (hs.prod hs)
  apply (hw.comp continuous_snd).continuousOn.mul
  apply hf.comp
  · exact (continuous_chord.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).continuousOn
  · intro p hp
    exact chord_mem hconv hp.1.1 hp.1.2 p.2.property

theorem analyticOnNhd_chordIntegral_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {v : ℂ} (hv : v ∈ s) : AnalyticOnNhd ℂ (fun u => chordIntegral f w u v) s := by
  apply DifferentiableOn.analyticOnNhd _ hs
  intro u hu
  exact (hasDerivAt_chordIntegral_left hs hconv hf hw hu hv).differentiableAt.differentiableWithinAt

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.DividedDifferences ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem continuousOn_correction {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c : ℂ}
    (hH : ∀ u ∈ s, ∀ v ∈ s, chordDenominator c g u v ≠ 0) :
    ContinuousOn (fun p : ℂ × ℂ => correction c g p.1 p.2) (s ×ˢ s) := by
  have hD := continuousOn_chordIntegral hs hconv hg.deriv.continuousOn (continuous_const (y := (1:ℂ)))
  have hE := continuousOn_chordIntegral hs hconv hg.deriv.deriv.continuousOn
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop)
  exact ((continuous_fst.mul continuous_snd).continuousOn.mul
    (hD.add (continuous_fst.continuousOn.mul hE))).div
    (continuousOn_const.sub ((continuous_fst.mul continuous_snd).continuousOn.mul hD))
    (fun p hp => hH p.1 hp.1 p.2 hp.2)

theorem analyticOnNhd_correction_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c v : ℂ} (hv : v ∈ s)
    (hH : ∀ u ∈ s, chordDenominator c g u v ≠ 0) :
    AnalyticOnNhd ℂ (fun u => correction c g u v) s := by
  have hD := analyticOnNhd_chordIntegral_left hs hconv hg.deriv (continuous_const (y := (1:ℂ))) hv
  have hE := analyticOnNhd_chordIntegral_left hs hconv hg.deriv.deriv
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop) hv
  intro u hu
  exact (((analyticAt_id.mul analyticAt_const).mul ((hD u hu).add (analyticAt_id.mul (hE u hu)))).div
    (analyticAt_const.sub ((analyticAt_id.mul analyticAt_const).mul (hD u hu))) (hH u hu))

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.TaylorFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem taylorCoeff_eq_series {E : Type u_102} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 r) (k : ℕ) : taylorCoeff f k = p.coeff k := by
  have hh := hp.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin k => (1:ℂ))
  simp only [← iteratedDeriv_eq_iteratedFDeriv,Finset.sum_const,Finset.card_univ,
    Fintype.card_perm,Fintype.card_fin] at hh
  change iteratedDeriv k f 0 = k.factorial • p.coeff k at hh
  rw [taylorCoeff,hh,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  simp [Nat.factorial_ne_zero]

theorem unitPoint_continuous : Continuous unitPoint := (fourier 1).continuous

theorem unitPoint_pow (t : Angle) (k : ℕ) : unitPoint t ^ k = fourier (k:ℤ) t := by
  simp only [unitPoint,fourier_apply,one_zsmul,← Circle.coe_pow,
    ← AddCircle.toCircle_nsmul,natCast_zsmul]

theorem integral_character_smul {E : Type u_103} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (a b : ℤ) (v : E) :
    (∫ t : Angle, fourier (-a) t • (fourier b t • v) ∂angularMeasure) = if b = a then v else 0 := by
  rw [show (fun t : Angle => fourier (-a) t • (fourier b t • v)) =
      (fun t => (fourier (-a) t * fourier b t) • v) by funext t; rw [smul_smul],
    integral_smul_const]
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) b) a
  change (∫ t : Angle, fourier (-a) t * fourier b t ∂angularMeasure) = _ at hh
  rw [hh]
  by_cases hab : b = a
  · subst b; simp
  · simp [Ne.symm hab,hab]

theorem fourierCoeff_of_powerSeries {E : Type u_104} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 r) (hr : 1 < r) (k : ℤ) :
    fourierCoeff (fun t : Angle => f (unitPoint t)) k =
      if 0 ≤ k then taylorCoeff f k.toNat else 0 := by
  have h1 : (1:ℂ) ∈ Metric.eball 0 p.radius := by
    simpa [Metric.mem_eball,edist_dist] using hr.trans_le hp.r_le
  have hs : Summable (fun n => ‖p.coeff n‖) := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,one_pow,one_smul] using p.summable_norm_apply h1
  have hp' (t : Angle) : HasSum (fun n : ℕ => fourier n t • p.coeff n) (f (unitPoint t)) := by
    have ht : unitPoint t ∈ Metric.eball 0 r := by
      simpa [Metric.mem_eball,edist_dist] using hr
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,unitPoint_pow,zero_add] using hp.hasSum ht
  have hi := hasSum_integral_of_dominated_convergence
    (μ := angularMeasure) (bound := fun (n : ℕ) (_ : Angle) => ‖p.coeff n‖)
    (F := fun (n : ℕ) (t : Angle) => fourier (-k) t • (fourier n t • p.coeff n))
    (f := fun t => fourier (-k) t • f (unitPoint t))
    (fun n => ((fourier (-k)).continuous.smul ((fourier n).continuous.smul continuous_const)).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun t => by simp [norm_smul,fourier_apply,Circle.norm_coe]))
    (ae_of_all _ (fun _ => hs)) (integrable_const _)
    (ae_of_all _ (fun t => (hp' t).const_smul (fourier (-k) t)))
  simp only [integral_character_smul] at hi
  change HasSum (fun n : ℕ => if (n:ℤ) = k then p.coeff n else 0)
    (fourierCoeff (fun t : Angle => f (unitPoint t)) k) at hi
  rw [← hi.tsum_eq]
  cases k with
  | ofNat k =>
    simp [taylorCoeff_eq_series hp]
  | negSucc k =>
    simp

theorem fourierCoeff_of_analytic {E : Type u_105} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (k : ℤ) :
    fourierCoeff (fun t : Angle => f (unitPoint t)) k =
      if 0 ≤ k then taylorCoeff f k.toNat else 0 := by
  obtain ⟨ρ,hρ1,hρR⟩ := exists_between hR
  let ρ' : ℝ≥0 := ⟨ρ,by linarith⟩
  have hd : DifferentiableOn ℂ f (closedBall 0 (ρ':ℝ)) :=
    hf.differentiableOn.mono (closedBall_subset_ball hρR)
  have hp := hd.hasFPowerSeriesOnBall (R := ρ') (by change 0 < ρ; linarith)
  apply fourierCoeff_of_powerSeries hp
  exact_mod_cast hρ1

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberPolynomials ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_106 u_107

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem fourierCoeff_comp_neg {E : Type u_106} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Angle → E) (k : ℤ) :
    fourierCoeff (fun t => f (-t)) k = fourierCoeff f (-k) := by
  unfold fourierCoeff
  rw [← integral_neg_eq_self (fun t : Angle => fourier (-k) t • f (-t)) angularMeasure]
  congr 1
  funext t
  simp [fourier_apply,smul_neg,neg_smul]

theorem fourierCoeff_of_antianalytic {E : Type u_107} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (k : ℤ) :
    fourierCoeff (fun t : Angle => f ((unitPoint t)⁻¹)) k =
      if k ≤ 0 then taylorCoeff f (-k).toNat else 0 := by
  have he : (fun t : Angle => f ((unitPoint t)⁻¹)) = (fun t => (fun s => f (unitPoint s)) (-t)) := by
    funext t; change f ((unitPoint t)⁻¹) = f (unitPoint (-t)); rw [unitPoint_neg]
  rw [he,fourierCoeff_comp_neg (fun t : Angle => f (unitPoint t)) k,fourierCoeff_of_analytic hR hf]
  simp only [neg_nonneg]

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.BoundaryKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115 u_116

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem continuous_circle_integral {α : Type u_108} {E : Type u_109} [TopologicalSpace α]
    [FirstCountableTopology α] [LocallyCompactSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → Angle → E} (hf : Continuous f.uncurry) :
    Continuous (fun x => ∫ t, f x t ∂angularMeasure) := by
  simpa using continuous_parametric_integral_of_continuous (μ := angularMeasure) hf isCompact_univ

theorem continuous_slice_left {α : Type u_110} {β : Type u_111} {E : Type u_112}
    [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace E] (f : α → β → E) (hf : Continuous f.uncurry) (y : β) :
    Continuous (fun x => f x y) := by
  simpa only [Function.comp_def,Function.uncurry] using! hf.comp (continuous_id.prodMk continuous_const)

theorem unitPoint_ne_zero (t : Angle) : unitPoint t ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [unitPoint_norm]; norm_num)

theorem unitPoint_inv_mem {R : ℝ} (hR : 1 < R) (t : Angle) :
    (unitPoint t)⁻¹ ∈ ball (0:ℂ) R := by
  simpa only [mem_ball,dist_zero_right,norm_inv,unitPoint_norm,inv_one] using hR

theorem continuous_boundaryCorrection {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) :
    Continuous (boundaryCorrection c g).uncurry := by
  have hi : Continuous (fun t => (unitPoint t)⁻¹) := unitPoint_continuous.inv₀ unitPoint_ne_zero
  let f : Angle × Angle → ℂ × ℂ := fun p => ((unitPoint p.1)⁻¹,(unitPoint p.2)⁻¹)
  have hf : Continuous f := (hi.comp continuous_fst).prodMk (hi.comp continuous_snd)
  have hmaps : MapsTo f univ (ball 0 R ×ˢ ball 0 R) :=
    fun p _ => ⟨unitPoint_inv_mem hR p.1,unitPoint_inv_mem hR p.2⟩
  have he : (boundaryCorrection c g).uncurry = (fun p : ℂ × ℂ => correction c g p.1 p.2) ∘ f := rfl
  rw [he]
  exact (continuousOn_correction isOpen_ball (convex_ball 0 R) hg hH).comp_continuous hf
    (fun p => hmaps (mem_univ p))

theorem continuous_boundaryCoefficient {c : ℂ} {g : ℂ → ℂ}
    (hS : Continuous (boundaryCorrection c g).uncurry) (k : ℕ) :
    Continuous (boundaryCoefficient c g k) := by
  have hs : Continuous (fun p : Angle × Angle => boundaryCorrection c g p.2 p.1) := by
    simpa only [Function.uncurry,Function.comp_def] using! hS.comp continuous_swap
  have hf : Continuous (fun p : Angle × Angle => fourier (-(-(k:ℤ))) p.2) :=
    (fourier (-(-(k:ℤ)))).continuous.comp continuous_snd
  have hh := continuous_circle_integral (f := fun s t => fourier (-(-(k:ℤ))) t • boundaryCorrection c g t s)
    (hf.smul hs)
  exact hh

theorem boundaryCorrection_left_coeff {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (s : Angle) (j : ℤ) :
    fourierCoeff (fun t => boundaryCorrection c g t s) j =
      if j ≤ 0 then taylorCoeff (fun u => correction c g u ((unitPoint s)⁻¹)) (-j).toNat else 0 := by
  exact fourierCoeff_of_antianalytic hR
    (analyticOnNhd_correction_left isOpen_ball (convex_ball 0 R) hg (unitPoint_inv_mem hR s)
      (fun u hu => hH u hu _ (unitPoint_inv_mem hR s))) j

theorem boundaryCoefficient_eq_taylor {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (s : Angle) :
    boundaryCoefficient c g k s = taylorCoeff (fun u => correction c g u ((unitPoint s)⁻¹)) k := by
  simp [boundaryCoefficient,boundaryCorrection_left_coeff hR hg hH]

theorem boundaryCoefficient_zero {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) (s : Angle) :
    boundaryCoefficient c g 0 s = 0 := by
  rw [boundaryCoefficient_eq_taylor hR hg hH]; simp

theorem faberBasis_boundary {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (s : Angle) :
    (faberBasis c g k).eval (boundary c g s) = fourier (k:ℤ) s + boundaryCoefficient c g k s := by
  rw [boundaryCoefficient_eq_taylor hR hg hH]
  have he := faberBasis_exterior (by linarith : 0 < R) hg hc (unitPoint_inv_mem hR s)
    (inv_ne_zero (unitPoint_ne_zero s)) (fun u hu => hH u hu _ (unitPoint_inv_mem hR s)) k
  simpa only [inv_inv,unitPoint_pow,boundary] using he

theorem continuous_boundaryKernel {c : ℂ} {g : ℂ → ℂ}
    (hS : Continuous (boundaryCorrection c g).uncurry) : Continuous (boundaryKernel c g).uncurry := by
  exact continuous_const.add (continuous_const.mul (Complex.continuous_re.comp hS))

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.KernelContraction ----
namespace OAI

universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section Hilbert

variable {E : Type u_127} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem continuous_positiveSeries {E : Type u_127} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {N : ℕ} (C : Fin N → E) :
    Continuous (positiveSeries C) := by
  exact continuous_finsetSum _ (fun k _ => (fourier (k:ℤ)).continuous.smul continuous_const)

theorem fourierCoeff_finite_smul {N : ℕ} (f : Fin N → Angle → ℂ)
    (hf : ∀ k, Continuous (f k)) (C : Fin N → E) (j : ℤ) :
    fourierCoeff (fun t => ∑ k, f k t • C k) j = ∑ k, fourierCoeff (f k) j • C k := by
  unfold fourierCoeff
  simp_rw [Finset.smul_sum,smul_smul]
  rw [integral_finsetSum]
  · simp_rw [integral_smul_const,smul_eq_mul]
  · intro k hk
    exact integrable_of_continuous_compact _ (((fourier (-j)).continuous.mul (hf k)).smul continuous_const)

theorem fourierCoeff_positiveSeries {N : ℕ} (C : Fin N → E) (j : Fin N) :
    fourierCoeff (positiveSeries C) (j:ℤ) = C j := by
  classical
  unfold positiveSeries
  rw [fourierCoeff_finite_smul _ (fun k => (fourier (k:ℤ)).continuous)]
  simp_rw [fourierCoeff_fourier]
  simp only [Pi.single_apply,ite_smul,one_smul,zero_smul]
  have hinj (k : Fin N) : (j:ℤ) = (k:ℤ) ↔ j = k := by
    constructor
    · intro h; apply Fin.ext; exact_mod_cast h
    · intro h; rw [h]
  simp_rw [hinj]
  simp

theorem energy_positiveSeries {N : ℕ} (C : Fin N → E) :
    (∫ t, ‖positiveSeries C t‖^2 ∂angularMeasure) = ∑ k, ‖C k‖^2 := by
  have hp := continuous_positiveSeries C
  have he (t : Angle) : ‖positiveSeries C t‖^2 = RCLike.re (inner ℂ (positiveSeries C t) (positiveSeries C t)) := by
    simp [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow]
  simp_rw [he]
  rw [integral_re (integrable_of_continuous_compact _ (hp.inner hp)),integral_inner_positiveSeries C _ hp]
  simp only [fourierCoeff_positiveSeries,inner_self_eq_norm_sq_to_K,map_sum]
  change (∑ k, ((‖C k‖ : ℂ)^2).re) = ∑ k, ‖C k‖^2
  simp [← Complex.ofReal_pow]

end Hilbert

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FaberHilbert

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberEnergy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_128 u_129

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem continuous_boundaryRemainder {E : Type u_128} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E)
    (hS : Continuous (boundaryCorrection c g).uncurry) : Continuous (boundaryRemainder c g C) := by
  exact continuous_finsetSum _ (fun k _ => (continuous_boundaryCoefficient hS k).smul continuous_const)

theorem faberBoundarySeries_decomp {E : Type u_128} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {N : ℕ} (C : Fin N → E) (t : Angle) :
    faberBoundarySeries c g C t = positiveSeries C t + boundaryRemainder c g C t := by
  simp only [faberBoundarySeries,faberBasis_boundary hR hg hc hH,add_smul,
    Finset.sum_add_distrib,positiveSeries,boundaryRemainder]

theorem boundaryRemainder_no_nonnegative {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {N : ℕ} (C : Fin N → E) (j : ℤ) (hj : 0 ≤ j) :
    fourierCoeff (boundaryRemainder c g C) j = 0 := by
  have hS := continuous_boundaryCorrection hR hg hH
  unfold boundaryRemainder
  rw [fourierCoeff_finite_smul _ (fun k => continuous_boundaryCoefficient hS k)]
  simp only [boundaryCoefficient_no_nonnegative hR hg hH _ j hj,zero_smul,Finset.sum_const_zero]

theorem boundaryKernel_action {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {N : ℕ} (C : Fin N → E) (s : Angle) :
    (∫ t, boundaryKernel c g t s • positiveSeries (nonconstantCoefficients C) t ∂angularMeasure) =
      boundaryRemainder c g C s := by
  have hK := continuous_slice_left _ (continuous_boundaryKernel (continuous_boundaryCorrection hR hg hH)) s
  simp only [positiveSeries,Finset.smul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : (k:ℕ) = 0
    · simp [nonconstantCoefficients,hk0,boundaryCoefficient_zero hR hg hH]
    · simp only [nonconstantCoefficients,ite_eq_right hk0]
      rw [show (fun t => boundaryKernel c g t s • (fourier (k:ℤ) t • C k)) =
        (fun t => ((boundaryKernel c g t s : ℂ)*fourier (k:ℤ) t) • C k) by
          funext t; rw [← smul_assoc,Complex.real_smul], integral_smul_const,
        boundaryKernel_character hR hg hH k hk0 s]
  · intro k hk
    exact integrable_of_continuous_compact _ (hK.smul ((fourier (k:ℤ)).continuous.smul continuous_const))

theorem faber_hilbert_coefficient_bounds {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hpositive : ∀ t s, 0 ≤ boundaryKernel c g t s)
    {N : ℕ} (C : Fin N → E) :
    (∑ k, ‖C k‖^2 ≤ ∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) ∧
      ((∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) ≤
        ∑ k : Fin N, (if (k:ℕ) = 0 then 1 else 2)*‖C k‖^2) := by
  have hS := continuous_boundaryCorrection hR hg hH
  have hr := continuous_boundaryRemainder c g C hS
  have he : (∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) =
      (∑ k, ‖C k‖^2) + ∫ t, ‖boundaryRemainder c g C t‖^2 ∂angularMeasure := by
    simp_rw [faberBoundarySeries_decomp hR hg hc hH]
    exact energy_orthogonal_positiveSeries C _ hr (boundaryRemainder_no_nonnegative hR hg hH C)
  have hrnonneg : 0 ≤ ∫ t, ‖boundaryRemainder c g C t‖^2 ∂angularMeasure :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hrbound : (∫ t, ‖boundaryRemainder c g C t‖^2 ∂angularMeasure) ≤
      ∑ k, ‖nonconstantCoefficients C k‖^2 := by
    let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    have hm := boundaryKernel_marginals hR hg hH
    have ht := markov_kernel_contraction angularMeasure angularMeasure (boundaryKernel c g)
      (positiveSeries (nonconstantCoefficients C)) (continuous_boundaryKernel hS)
      (continuous_positiveSeries _) hpositive hm.1 hm.2
    simp_rw [boundaryKernel_action hR hg hH C,energy_positiveSeries] at ht
    exact ht
  have hw : (∑ k, ‖C k‖^2) + ∑ k, ‖nonconstantCoefficients C k‖^2 =
      ∑ k : Fin N, (if (k:ℕ) = 0 then 1 else 2)*‖C k‖^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : (k:ℕ) = 0 <;> simp [nonconstantCoefficients,hk0] ; ring
  constructor
  · rw [he]; linarith
  · rw [he,← hw]; linarith

end FaberHilbert

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

end BanachAlgebra

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.faber_hilbert_coefficient_bounds := @_root_.OAI.DirectCrouzeix.Faber.faber_hilbert_coefficient_bounds
