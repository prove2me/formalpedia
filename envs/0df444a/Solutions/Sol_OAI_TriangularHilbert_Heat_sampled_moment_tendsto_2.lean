-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.sampled_moment_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:16:50.135968+00:00
-- url     : https://prove2.me/submissions/cd3d4583-07fb-44fd-bb7c-a723fbebdb90

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SampledMoment.lean:L45-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.sampled_moment_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicSlice
import Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledMoment
import Theorems.Thm_OAI_TriangularHilbert_Heat_sampledKernelOutput_tendsto

-- ---- from OAI.Analysis.TriangularHilbert.GridCell ----
namespace OAI

universe uE uF

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma gridCell_mem_iff {h x : ℝ} (hh : 0 < h) (i : ℤ) :
    x ∈ gridCell h i ↔ gridIndex h x = i := by
  unfold gridCell gridIndex
  rw [Int.floor_eq_iff]
  simp only [Set.mem_Ico]
  constructor
  · intro hx
    exact ⟨(le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hx.1),
      (div_lt_iff₀ hh).mpr (by simpa only [mul_comm] using hx.2)⟩
  · intro hx
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hh).mp hx.1,
      by simpa only [mul_comm] using (div_lt_iff₀ hh).mp hx.2⟩

lemma gridPoint_le {h : ℝ} (hh : 0 < h) (x : ℝ) : gridPoint h x ≤ x := by
  exact ((gridCell_mem_iff hh (gridIndex h x)).mpr rfl).1

lemma gridPoint_lt_add {h : ℝ} (hh : 0 < h) (x : ℝ) : x < gridPoint h x+h := by
  have hh' := ((gridCell_mem_iff hh (gridIndex h x)).mpr rfl).2
  dsimp [gridCell,gridPoint] at *
  linarith only [hh']

lemma abs_gridPoint_sub_lt {h : ℝ} (hh : 0 < h) (x : ℝ) : |gridPoint h x-x| < h := by
  rw [abs_of_nonpos (sub_nonpos.mpr (gridPoint_le hh x))]
  linarith only [gridPoint_lt_add hh x]

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Quantization ----
namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma measurable_gridIndex (h : ℝ) : Measurable (gridIndex h) := by
  exact Int.measurable_floor.comp (measurable_id.div_const h)

lemma measurable_gridPoint (h : ℝ) : Measurable (gridPoint h) := by
  exact measurable_const.mul ((measurable_of_countable (fun i : ℤ => (i:ℝ))).comp (measurable_gridIndex h))

lemma sampled_support {E : Type uE} [Zero E] (f : ℝ×ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hf : ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ |z.2| ≤ M)
    (z : ℝ×ℝ) (hz : f (gridSquare h z) ≠ 0) :
    |z.1| ≤ M+1 ∧ |z.2| ≤ M+1 := by
  have ha := hf _ hz
  have h1 := abs_gridPoint_sub_lt hh z.1
  have h2 := abs_gridPoint_sub_lt hh z.2
  have e1 := abs_add_le (z.1-gridPoint h z.1) (gridPoint h z.1)
  have e2 := abs_add_le (z.2-gridPoint h z.2) (gridPoint h z.2)
  simp only [sub_add_cancel] at e1 e2
  rw [abs_sub_comm] at h1 h2
  dsimp [gridSquare] at ha
  exact ⟨by linarith [ha.1],by linarith [ha.2]⟩
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.BoundedBox ----
namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma mem_closedBox (M : ℝ) (z : ℝ×ℝ) : z ∈ closedBox M ↔ |z.1| ≤ M ∧ |z.2| ≤ M := by
  simp only [closedBox,Set.mem_prod,Set.mem_Icc,abs_le]
lemma measurableSet_closedBox (M : ℝ) : MeasurableSet (closedBox M) := measurableSet_Icc.prod measurableSet_Icc
lemma isCompact_closedBox (M : ℝ) : IsCompact (closedBox M) := isCompact_Icc.prod isCompact_Icc
lemma volume_closedBox_ne_top (M : ℝ) : volume (closedBox M) ≠ ⊤ := (isCompact_closedBox M).measure_ne_top

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SampledOutput ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma measurable_sampledIntegrand (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (h : ℝ) (K : ℝ → ℝ) (hK : Measurable K) :
    Measurable (fun q : (ℝ×ℝ)×ℝ => sampledIntegrand B C h K q.1 q.2) := by
  have ha : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.1.1) := (measurable_gridPoint h).comp (measurable_fst.comp measurable_fst)
  have hb : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.1.2) := (measurable_gridPoint h).comp (measurable_snd.comp measurable_fst)
  have hc : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.2) := (measurable_gridPoint h).comp measurable_snd
  exact ((hB.comp (hb.prodMk hc)).mul (hC.comp (hc.prodMk ha))).mul
    (Complex.measurable_ofReal.comp (hK.comp ((ha.add hb).add hc)))

lemma measurable_sampledKernelOutput (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (h : ℝ) (K : ℝ → ℝ) (hK : Measurable K) : Measurable (sampledKernelOutput B C h K) :=
  (measurable_sampledIntegrand B C hB hC h K hK).stronglyMeasurable.integral_prod_right'.measurable

lemma sampledIntegrand_support_c (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ)
    (hc : sampledIntegrand B C h K z c ≠ 0) : |c| ≤ M+1 := by
  have hne : B (gridSquare h (z.2,c)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  exact (sampled_support B hh hh1 hB (z.2,c) hne).2

lemma sampledIntegrand_support_z (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ)
    (hc : sampledIntegrand B C h K z c ≠ 0) : z ∈ closedBox (M+1) := by
  apply (mem_closedBox _ _).mpr
  have hneB : B (gridSquare h (z.2,c)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  have hneC : C (gridSquare h (c,z.1)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  exact ⟨(sampled_support C hh hh1 hC (c,z.1) hneC).2,(sampled_support B hh hh1 hB (z.2,c) hneB).1⟩

lemma sampledKernelOutput_support (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) (hz : z ∉ closedBox (M+1)) :
    sampledKernelOutput B C h K z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with c
  by_contra hc
  exact hz (sampledIntegrand_support_z B C hh hh1 hB hC K z c hc)
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SampledConvergence ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma norm_sampledIntegrand_le (B C : ℝ×ℝ → ℂ) {CB CC L : ℝ}
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC) (K : ℝ → ℝ)
    (hk : ∀ t, |K t| ≤ L) (h : ℝ) (z : ℝ×ℝ) (c : ℝ) :
    ‖sampledIntegrand B C h K z c‖ ≤ CB*CC*L := by
  unfold sampledIntegrand
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul (hb _) (hc _) (norm_nonneg _) ((norm_nonneg (B 0)).trans (hb 0)))
    (hk _) (abs_nonneg _) (mul_nonneg ((norm_nonneg (B 0)).trans (hb 0)) ((norm_nonneg (C 0)).trans (hc 0)))

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.FiniteMoment ----
namespace OAI

universe uκ

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

lemma complexMoment_nonneg (z : ℂ) : 0 ≤ complexMoment z := by unfold complexMoment; positivity
lemma continuous_complexMoment : Continuous complexMoment := continuous_norm.mul (Real.continuous_sqrt.comp continuous_norm)
lemma complexMoment_le {z : ℂ} {b : ℝ} (hz : ‖z‖ ≤ b) : complexMoment z ≤ b*Real.sqrt b :=
  mul_le_mul hz (Real.sqrt_le_sqrt hz) (Real.sqrt_nonneg _) ((norm_nonneg _).trans hz)

lemma finiteMoment_eq {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    ∃ k, finiteMoment f = complexMoment (f k) := by
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => complexMoment (f k))
  exact ⟨k,hk⟩
lemma finiteMoment_nonneg {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    0 ≤ finiteMoment f := by
  obtain ⟨k,hk⟩ := finiteMoment_eq f
  rw [hk]
  exact complexMoment_nonneg _
lemma finiteMoment_le {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) {b : ℝ}
    (hb : ∀ k, ‖f k‖ ≤ b) : finiteMoment f ≤ b*Real.sqrt b :=
  Finset.sup'_le _ _ (fun k _ => complexMoment_le (hb k))
lemma continuous_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] : Continuous (finiteMoment (κ := κ)) := by
  unfold finiteMoment
  exact Continuous.finset_sup'_apply _ (fun k _ => continuous_complexMoment.comp (continuous_apply k))
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SampledMoment ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma outputBound_nonneg (M : ℝ) {CB CC L : ℝ} (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L) :
    0 ≤ outputBound M CB CC L :=
  integral_nonneg (fun c => Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCB hCC) hL) c)

lemma sampledKernelOutput_bound (B C : ℝ×ℝ → ℂ) {M CB CC L h : ℝ}
    (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC) (hh : 0 < h) (hh1 : h ≤ 1)
    (K : ℝ → ℝ) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ) :
    ‖sampledKernelOutput B C h K z‖ ≤ outputBound M CB CC L := by
  apply norm_integral_le_of_norm_le
    ((integrableOn_const (μ := volume) (s := Set.Icc (-(M+1)) (M+1)) (C := CB*CC*L)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc)
  filter_upwards [] with c
  by_cases he : sampledIntegrand B C h K z c = 0
  · rw [he,norm_zero]
    exact Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCB hCC) hL) c
  · rw [Set.indicator_of_mem (show c ∈ Set.Icc (-(M+1)) (M+1) from
      abs_le.mp (sampledIntegrand_support_c B C hh hh1 hs K z c he))]
    exact norm_sampledIntegrand_le B C hb hc K hk _ _ _

lemma sampled_moment_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ)
    (hK : ∀ k, Measurable (K k)) (hk : ∀ k t, |K k t| ≤ L)
    (hcont : ∀ k (z : ℝ×ℝ), ∀ᵐ c : ℝ, ContinuousAt (K k) (z.1+z.2+c)) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C (h n) (K k) z)) atTop
      (𝓝 (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (K k) z))) := by
  let T := outputBound M CB CC L
  have hT : 0 ≤ T := outputBound_nonneg M hCB hCC hL
  let b : ℝ×ℝ → ℝ := (closedBox (M+1)).indicator (fun _ => T*Real.sqrt T)
  apply tendsto_integral_of_dominated_convergence b
  · intro n
    exact (continuous_finiteMoment.measurable.comp (Measurable.of_eval
      (fun k => measurable_sampledKernelOutput B C hB.measurable hC.measurable (h n) (K k) (hK k)))).aestronglyMeasurable
  · exact (integrableOn_const (μ := volume) (s := closedBox (M+1)) (C := T*Real.sqrt T)
      (volume_closedBox_ne_top _)).integrable_indicator (measurableSet_closedBox _)
  · intro n
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (finiteMoment_nonneg _)]
    by_cases hz : z ∈ closedBox (M+1)
    · dsimp only [b]
      rw [Set.indicator_of_mem hz]
      exact finiteMoment_le _ (fun k => sampledKernelOutput_bound B C hsB hCB hCC hL hb hc (hh n) (hh1 n) (K k) (hk k) z)
    · have he : (fun k => sampledKernelOutput B C (h n) (K k) z) = fun _ : κ => (0:ℂ) :=
        funext (fun k => sampledKernelOutput_support B C (hh n) (hh1 n) hsB hsC (K k) z hz)
      rw [he,finiteMoment_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hT (Real.sqrt_nonneg _)) z
  · filter_upwards [] with z
    apply continuous_finiteMoment.continuousAt.tendsto.comp
    exact tendsto_pi_nhds.mpr (fun k => sampledKernelOutput_tendsto B C hB hC hsB hCB hCC hL hb hc
      hh hh1 ht (K k) (hK k) (hk k) z (hcont k z))
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology


theorem solution.{uκ} : type_of% @_root_.OAI.TriangularHilbert.Heat.sampled_moment_tendsto.{uκ} := @_root_.OAI.TriangularHilbert.Heat.sampled_moment_tendsto.{uκ}
