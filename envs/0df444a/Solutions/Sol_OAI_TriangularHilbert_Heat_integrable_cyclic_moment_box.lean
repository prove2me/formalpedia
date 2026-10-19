-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.integrable_cyclic_moment_box
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:22:54.775071+00:00
-- url     : https://prove2.me/submissions/3e56158b-6cc7-4304-9fa7-e8e98f93af0d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/CyclicMeasurable.lean:L63-L84
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.integrable_cyclic_moment_box. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteDual
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscreteMax

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

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicMeasurable ----
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

lemma measurable_cyclicKernelOutput (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (K : ℝ → ℝ) (hK : Measurable K) : Measurable (cyclicKernelOutput B C K) := by
  have hm : Measurable (fun q : (ℝ×ℝ)×ℝ => B (q.1.2,q.2)*C (q.2,q.1.1)*(K (q.1.1+q.1.2+q.2):ℂ)) := by
    apply Measurable.mul
    · exact (hB.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
        (hC.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    · exact Complex.measurable_ofReal.comp (hK.comp
        (((measurable_fst.comp measurable_fst).add (measurable_snd.comp measurable_fst)).add measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma cyclicKernelOutput_support (B C : ℝ×ℝ → ℂ) {M : ℝ}
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) (hz : z ∉ closedBox M) :
    cyclicKernelOutput B C K z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with c
  by_cases hb : B (z.2,c) = 0
  · simp only [hb,zero_mul,Pi.zero_apply]
  · have hc : C (c,z.1) = 0 := by
      by_contra hc
      exact hz ((mem_closedBox _ _).mpr ⟨(hC _ hc).2,(hB _ hb).1⟩)
    simp only [hc,mul_zero,zero_mul,Pi.zero_apply]

lemma cyclicKernelOutput_bound (B C : ℝ×ℝ → ℂ) {M CB CC L : ℝ}
    (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (_hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    (K : ℝ → ℝ) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ) :
    ‖cyclicKernelOutput B C K z‖ ≤ outputBound M CB CC L := by
  apply norm_integral_le_of_norm_le
    ((integrableOn_const (μ := volume) (s := Set.Icc (-(M+1)) (M+1)) (C := CB*CC*L)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc)
  filter_upwards [] with c
  by_cases hmem : c ∈ Set.Icc (-(M+1)) (M+1)
  · rw [Set.indicator_of_mem hmem,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul (hb _) (hc _) (norm_nonneg _) hCB) (hk _) (abs_nonneg _)
      (mul_nonneg hCB hCC)
  · have he : B (z.2,c) = 0 := by
      by_contra he
      apply hmem
      exact abs_le.mp ((hs _ he).2.trans (by linarith))
    simp only [he,zero_mul,norm_zero,Set.indicator_of_notMem hmem,le_refl]

lemma integrable_cyclic_moment_box (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    {M CB CC L : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ)
    (hK : ∀ k, Measurable (K k)) (hk : ∀ k t, |K k t| ≤ L) :
    Integrable (fun z : ℝ×ℝ => finiteMoment (fun k => cyclicKernelOutput B C (K k) z)) := by
  let T := outputBound M CB CC L
  have hT : 0 ≤ T := outputBound_nonneg M hCB hCC hL
  apply ((integrableOn_const (μ := volume) (s := closedBox M) (C := T*Real.sqrt T)
    (volume_closedBox_ne_top _)).integrable_indicator (measurableSet_closedBox _)).mono'
  · exact (continuous_finiteMoment.measurable.comp (Measurable.of_eval
      (fun k => measurable_cyclicKernelOutput B C hB hC (K k) (hK k)))).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (finiteMoment_nonneg _)]
    by_cases hz : z ∈ closedBox M
    · rw [Set.indicator_of_mem hz]
      exact finiteMoment_le _ (fun k => cyclicKernelOutput_bound B C hsB hCB hCC hL hb hc (K k) (hk k) z)
    · have he : (fun k => cyclicKernelOutput B C (K k) z) = fun _ : κ => (0:ℂ) :=
        funext (fun k => cyclicKernelOutput_support B C hsB hsC (K k) z hz)
      rw [he,finiteMoment_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hT (Real.sqrt_nonneg _)) z
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology


theorem solution.{uκ} : type_of% @_root_.OAI.TriangularHilbert.Heat.integrable_cyclic_moment_box.{uκ} := @_root_.OAI.TriangularHilbert.Heat.integrable_cyclic_moment_box.{uκ}
