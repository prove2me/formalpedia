-- Prove2me | solution 1 for OAI.TriangularHilbert.lintegral_cyclicMax_moment_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:32:06.392464+00:00
-- url     : https://prove2.me/submissions/9a17cf9a-5295-4434-a8db-84b594483790

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/CyclicMaxMoment.lean:L58-L71
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.lintegral_cyclicMax_moment_le. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicMaxMoment
import Theorems.Thm_OAI_TriangularHilbert_Heat_lintegral_cyclic_moment_le
import Theorems.Thm_OAI_TriangularHilbert_Heat_tendsto_cyclicKernelOutput_of_cubic_dom
import Theorems.Thm_OAI_TriangularHilbert_exists_cubic_approximation

-- ---- from OAI.Analysis.TriangularHilbert.HardScalar ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma measurable_hardKernel (r R : ℝ) : Measurable (hardKernel r R) := by
  unfold hardKernel
  exact ((measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const).sub
    (measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const)).div measurable_id

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.RationalSup ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal
noncomputable section

lemma RatEndpoints.sequence_surjective : Function.Surjective RatEndpoints.sequence := by
  intro q
  exact ⟨Encodable.encode q,by simp [RatEndpoints.sequence,Encodable.encodek]⟩
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

lemma finiteMoment_eq {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    ∃ k, finiteMoment f = complexMoment (f k) := by
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => complexMoment (f k))
  exact ⟨k,hk⟩
lemma le_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) (k : κ) :
    complexMoment (f k) ≤ finiteMoment f  := by
  exact Finset.le_sup' (fun k => complexMoment (f k)) (Finset.mem_univ k)
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicMeasurable ----
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

lemma measurable_cyclicKernelOutput (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (K : ℝ → ℝ) (hK : Measurable K) : Measurable (cyclicKernelOutput B C K) := by
  have hm : Measurable (fun q : (ℝ×ℝ)×ℝ => B (q.1.2,q.2)*C (q.2,q.1.1)*(K (q.1.1+q.1.2+q.2):ℂ)) := by
    apply Measurable.mul
    · exact (hB.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
        (hC.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    · exact Complex.measurable_ofReal.comp (hK.comp
        (((measurable_fst.comp measurable_fst).add (measurable_snd.comp measurable_fst)).add measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicDensity ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma aemeasurable_cyclic_hard (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) : AEMeasurable (cyclicKernelOutput B C (hardKernel r R)) volume := by
  obtain ⟨F,hF,D,hD,_,hb⟩ := exists_cubic_approximation B hB
  obtain ⟨G,hG,E,hE,_,hc⟩ := exists_cubic_approximation C hC
  have ht := tendsto_cyclicKernelOutput_of_cubic_dom B C F G (fun n => (hF n).1) (fun n => (hG n).1) hD hE hb hc
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (measurable_cyclicKernelOutput (F n) (G n) (hF n).1.measurable (hG n).1.measurable _
      (measurable_hardKernel r R)).aemeasurable)
  filter_upwards [ht] with z hz
  exact hz r R hr hR

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MomentPower ----
namespace OAI

universe uκ

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

lemma real_three_halves (x : ℝ) (hx : 0 ≤ x) : x^((3:ℝ)/2) = x*Real.sqrt x := by
  by_cases he : x = 0
  · subst x; norm_num
  · rw [show (3:ℝ)/2 = 1+(1:ℝ)/2 by norm_num,Real.rpow_add (lt_of_le_of_ne hx (Ne.symm he)),Real.rpow_one,Real.sqrt_eq_rpow]

lemma ofReal_complexMoment (z : ℂ) : ENNReal.ofReal (complexMoment z) = ENNReal.ofReal ‖z‖^((3:ℝ)/2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),real_three_halves _ (norm_nonneg _)]
  rfl

lemma ofReal_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    ENNReal.ofReal (finiteMoment f) = ⨆ k, ENNReal.ofReal (complexMoment (f k)) := by
  apply le_antisymm
  · obtain ⟨k,hk⟩ := finiteMoment_eq f
    rw [hk]
    exact le_iSup (fun k => ENNReal.ofReal (complexMoment (f k))) k
  · exact iSup_le (fun k => ENNReal.ofReal_le_ofReal (le_finiteMoment f k))
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicMaxMoment ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal
noncomputable section

lemma rationalMoment_mono (B C : Plane → ℂ) (z : Plane) : Monotone (fun n => rationalMoment B C n z) := by
  intro n m hnm
  apply iSup_le
  intro k
  exact le_iSup (fun k : Fin (m+1) => ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
    (hardKernel (RatEndpoints.sequence k).toEndpoints.lower (RatEndpoints.sequence k).toEndpoints.upper) z)))
    ⟨k,lt_of_lt_of_le k.2 (Nat.add_le_add_right hnm 1)⟩

lemma cyclicMax_rpow_eq (B C : Plane → ℂ) (z : Plane) :
    cyclicMax B C z ^ ((3:ℝ)/2) = ⨆ n, rationalMoment B C n z := by
  rw [cyclicMax]
  change (ENNReal.orderIsoRpow ((3:ℝ)/2) (by norm_num)) _ = _
  rw [OrderIso.map_iSup]
  simp only [ENNReal.orderIsoRpow_apply, ← ofReal_complexMoment]
  apply le_antisymm
  · apply iSup_le
    intro q
    obtain ⟨n,rfl⟩ := RatEndpoints.sequence_surjective q
    exact le_iSup_of_le n (le_iSup (fun k : Fin (n+1) => ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
      (hardKernel (RatEndpoints.sequence k).toEndpoints.lower (RatEndpoints.sequence k).toEndpoints.upper) z)))
      ⟨n,Nat.lt_succ_self n⟩)
  · apply iSup_le
    intro n
    apply iSup_le
    intro k
    exact le_iSup (fun q : RatEndpoints => ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
      (hardKernel (q.1.1:ℝ) (q.1.2:ℝ)) z))) (RatEndpoints.sequence k)

lemma aemeasurable_rationalMoment (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) (n : ℕ) :
    AEMeasurable (rationalMoment B C n) volume := by
  unfold rationalMoment
  simp_rw [ofReal_complexMoment]
  apply AEMeasurable.iSup
  intro k
  exact ((aemeasurable_cyclic_hard B C hB hC (RatEndpoints.sequence k).toEndpoints.lower_pos
    (RatEndpoints.sequence k).toEndpoints.lower_lt_upper.le).norm.ennreal_ofReal).pow_const _

lemma lintegral_cyclicMax_moment_le (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    (∫⁻ z : Plane, cyclicMax B C z ^ ((3:ℝ)/2)) ≤
      ENNReal.ofReal (momentConstant*((∫ z : Plane, ‖B z‖^3)+(∫ z : Plane, ‖C z‖^3))) := by
  simp_rw [cyclicMax_rpow_eq]
  rw [lintegral_iSup' (aemeasurable_rationalMoment B C hB hC)
    (Eventually.of_forall (rationalMoment_mono B C))]
  apply iSup_le
  intro n
  have h := lintegral_cyclic_moment_le B C hB hC
    (fun k : Fin (n+1) => (RatEndpoints.sequence k).toEndpoints.lower)
    (fun k : Fin (n+1) => (RatEndpoints.sequence k).toEndpoints.upper)
    (fun k => (RatEndpoints.sequence k).toEndpoints.lower_pos)
    (fun k => (RatEndpoints.sequence k).toEndpoints.lower_lt_upper.le)
  simpa only [ofReal_finiteMoment,rationalMoment] using h
end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal


theorem solution : type_of% @_root_.OAI.TriangularHilbert.lintegral_cyclicMax_moment_le := @_root_.OAI.TriangularHilbert.lintegral_cyclicMax_moment_le
