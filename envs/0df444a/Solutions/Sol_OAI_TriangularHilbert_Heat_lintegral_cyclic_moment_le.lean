-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.lintegral_cyclic_moment_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:28:56.882799+00:00
-- url     : https://prove2.me/submissions/fef30a9c-803c-4b81-b41f-83672e7a7127

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/CyclicDensity.lean:L33-L54
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.lintegral_cyclic_moment_le. The node keeps its source
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
import Theorems.Thm_OAI_TriangularHilbert_Heat_ae_continuousAt_hardKernel
import Theorems.Thm_OAI_TriangularHilbert_Heat_gridLift_kernelOutput_eq
import Theorems.Thm_OAI_TriangularHilbert_Heat_hardPairing_le
import Theorems.Thm_OAI_TriangularHilbert_Heat_integrable_cyclic_moment_box
import Theorems.Thm_OAI_TriangularHilbert_Heat_sampled_moment_tendsto
import Theorems.Thm_OAI_TriangularHilbert_Heat_tendsto_cyclicKernelOutput_of_cubic_dom
import Theorems.Thm_OAI_TriangularHilbert_exists_cubic_approximation
import Theorems.Thm_OAI_TriangularHilbert_finite_cubic_dual
import Theorems.Thm_OAI_TriangularHilbert_gridLift_eq
import Theorems.Thm_OAI_TriangularHilbert_integral_gridLift
import Theorems.Thm_OAI_TriangularHilbert_sampled_cubic_tendsto

-- ---- from OAI.Analysis.TriangularHilbert.HardScalar ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma abs_hardKernel_le {r R : ℝ} (hr : 0 < r) (hb : r ≤ R) (t : ℝ) : |hardKernel r R t| ≤ 1/r := by
  unfold hardKernel
  by_cases hrt : r < |t|
  · by_cases hRt : R < |t|
    · simp [hrt,hRt,hr.le]
    · simp only [hrt,hRt,ite_true,ite_false,sub_zero,abs_div,abs_one]
      exact one_div_le_one_div_of_le hr hrt.le
  · have hRt : ¬R < |t| := fun h => hrt (hb.trans_lt h)
    simp [hrt,hRt,hr.le]

lemma measurable_hardKernel (r R : ℝ) : Measurable (hardKernel r R) := by
  unfold hardKernel
  exact ((measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const).sub
    (measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const)).div measurable_id

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GridCell ----
namespace OAI

universe uE uF

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma gridLift_comp {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} {F : Type uF} [AddCommMonoid E] [AddCommMonoid F]
    (f : D → D → E) (g : E → F) (hg : g 0 = 0) (z : ℝ×ℝ) :
    g (gridLift D h f z) = gridLift D h (fun i j => g (f i j)) z := by
  simp only [gridLift_eq hh]
  split_ifs <;> simp only [hg]

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

lemma mem_sampleIndices {h : ℝ} (hh : 0 < h) (M : ℝ) (i : ℤ) :
    i ∈ sampleIndices h M ↔ |h*i| ≤ M := by
  rw [sampleIndices,Finset.mem_Icc,Int.ceil_le,Int.le_floor,abs_le]
  constructor
  · rintro ⟨hi,hj⟩
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hh).mp hi,
      by simpa only [mul_comm] using (le_div_iff₀ hh).mp hj⟩
  · rintro ⟨hi,hj⟩
    exact ⟨(div_le_iff₀ hh).mpr (by simpa only [mul_comm] using hi),
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hj)⟩

lemma gridLift_sampled {E : Type uE} [AddCommMonoid E] (f : ℝ×ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hf : ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ |z.2| ≤ M) (z : ℝ×ℝ) :
    gridLift (sampleIndices h M) h (sampledMatrix f h M) z = f (gridSquare h z) := by
  rw [gridLift_eq hh]
  split_ifs with hi hj
  · rfl
  · symm
    by_contra hn
    exact hj ((mem_sampleIndices hh M _).mpr (hf _ hn).2)
  · symm
    by_contra hn
    exact hi ((mem_sampleIndices hh M _).mpr (hf _ hn).1)

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

lemma compactSupport_box {E : Type uE} [Zero E] (f : ℝ×ℝ → E) (hf : HasCompactSupport f) :
    ∃ M > 0, BoxSupport f M := by
  obtain ⟨M,hM,hm⟩ := hf.isBounded.exists_pos_norm_le
  refine ⟨M,hM,fun z hz => ?_⟩
  have hb := hm z (subset_tsupport f hz)
  have hleft : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  have hright : |z.2| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le z
  exact ⟨hleft.trans hb,hright.trans hb⟩

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
lemma finiteMoment_eq {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    ∃ k, finiteMoment f = complexMoment (f k) := by
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => complexMoment (f k))
  exact ⟨k,hk⟩
lemma finiteMoment_nonneg {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    0 ≤ finiteMoment f := by
  obtain ⟨k,hk⟩ := finiteMoment_eq f
  rw [hk]
  exact complexMoment_nonneg _
lemma continuous_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] : Continuous (finiteMoment (κ := κ)) := by
  unfold finiteMoment
  exact Continuous.finset_sup'_apply _ (fun k _ => continuous_complexMoment.comp (continuous_apply k))
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.DiscreteMax ----
namespace OAI

universe uι uκ

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma hardOutput_moment (D : Finset ℤ) (B C : Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r R : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (hb : ∀ i j, r i j ≤ R i j) :
    (∑ i, ∑ j, h^2*complexMoment (kernelOutput B C h (fun m => h*(m:ℤ))
      (fun i j => hardKernel (r i j) (R i j)) i j)) ≤
      momentConstant*(matrixCubic B h+matrixCubic C h) := by
  classical
  let u : D×D → ℂ := fun p => kernelOutput B C h (fun m => h*(m:ℤ))
    (fun i j => hardKernel (r i j) (R i j)) p.1 p.2
  have HH (f : D×D → ℂ) : ‖∑ p, (h^2:ℝ)*f p*u p‖ ≤ hardPairingConstant*
      ((∑ p, h^2*‖f p‖^3)+(matrixCubic B h+matrixCubic C h)) := by
    let A : Three → Matrix D D ℂ := ![fun i j => f (i,j),B,C]
    have ha := hardPairing_le D A hh r R hr hb
    have hA0 : A 0 = fun i j => f (i,j) := rfl
    have hA1 : A 1 = B := rfl
    have hA2 : A 2 = C := rfl
    simpa only [kernelPairing,arrayCubic,Fin.sum_univ_three,hA0,hA1,hA2,
      Fintype.sum_prod_type,matrixCubic,u,add_assoc] using ha
  have hh' := finite_cubic_dual u (fun _ => h^2) (fun _ => sq_nonneg h) hardPairingConstant_pos HH
  simpa only [Fintype.sum_prod_type,u,complexMoment,momentConstant] using hh'

lemma finiteHardOutput_moment (D : Finset ℤ) (B C : Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ)
    (hr : ∀ k, h ≤ r k) (hb : ∀ k, r k ≤ R k) :
    (∑ i, ∑ j, h^2*finiteMoment (fun k => kernelOutput B C h (fun m => h*(m:ℤ))
      (fun _ _ => hardKernel (r k) (R k)) i j)) ≤
      momentConstant*(matrixCubic B h+matrixCubic C h) := by
  classical
  let U (i j : D) (k : κ) := kernelOutput B C h (fun m => h*(m:ℤ))
    (fun _ _ => hardKernel (r k) (R k)) i j
  choose s hs using (fun i j : D => finiteMoment_eq (U i j))
  have ha := hardOutput_moment D B C hh (fun i j => r (s i j)) (fun i j => R (s i j))
    (fun i j => hr (s i j)) (fun i j => hb (s i j))
  have he (i j : D) : finiteMoment (U i j) = complexMoment (kernelOutput B C h (fun m => h*(m:ℤ))
      (fun i j => hardKernel (r (s i j)) (R (s i j))) i j) := hs i j
  simp_rw [← he] at ha
  exact ha
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.ContinuumMesh ----
namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter MatrixEnergy
open scoped Topology BigOperators
noncomputable section

lemma gridLift_pi (D : Finset ℤ) {h : ℝ} (hh : 0 < h) {κ : Type uκ}
    (U : κ → D → D → ℂ) (z : ℝ×ℝ) :
    gridLift D h (fun i j k => U k i j) z = fun k => gridLift D h (U k) z := by
  funext k
  simp only [gridLift_eq hh]
  split_ifs <;> rfl

lemma sampled_moment_integral_eq (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C h (K k) z)) =
      ∑ i, ∑ j, h^2*finiteMoment (fun k => kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h
        (fun m => h*(m:ℤ)) (fun _ _ => K k) i j) := by
  have he (z : ℝ×ℝ) : finiteMoment (fun k => sampledKernelOutput B C h (K k) z) =
      gridLift (sampleIndices h M) h (fun i j => finiteMoment (fun k =>
        kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h (fun m => h*(m:ℤ))
          (fun _ _ => K k) i j)) z := by
    simp_rw [← gridLift_kernelOutput_eq B C hh hsB hsC]
    rw [← gridLift_pi _ hh,gridLift_comp hh _ finiteMoment finiteMoment_zero]
  simp_rw [he]
  rw [integral_gridLift _ _ _ hh.le]
  rfl

lemma sampled_cubic_integral_eq (B : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hsB : BoxSupport B M) :
    (∫ z : ℝ×ℝ, ‖B (gridSquare h z)‖^3) = matrixCubic (sampledMatrix B h M) h := by
  simp_rw [← gridLift_sampled B hh hsB,gridLift_comp hh _ (fun w : ℂ => ‖w‖^3) (by simp)]
  rw [integral_gridLift _ _ _ hh.le]
  rfl

lemma sampled_moment_le (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ)
    (hr : ∀ k, h ≤ r k) (hb : ∀ k, r k ≤ R k) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C h (hardKernel (r k) (R k)) z)) ≤
      momentConstant*((∫ z : ℝ×ℝ, ‖B (gridSquare h z)‖^3)+(∫ z : ℝ×ℝ, ‖C (gridSquare h z)‖^3)) := by
  rw [sampled_moment_integral_eq B C hh hsB hsC,sampled_cubic_integral_eq B hh hsB,sampled_cubic_integral_eq C hh hsC]
  exact finiteHardOutput_moment (sampleIndices h M) (sampledMatrix B h M) (sampledMatrix C h M) hh r R hr hb
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CompactMoment ----
namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter MatrixEnergy
open scoped Topology BigOperators
noncomputable section

lemma continuum_moment_le_box (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z)) ≤
      momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3)) := by
  classical
  let δ : ℝ := min 1 (Finset.univ.inf' Finset.univ_nonempty r)
  have hδ : 0 < δ := lt_min zero_lt_one ((Finset.lt_inf'_iff _).mpr (fun k _ => hr k))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδr (k : κ) : δ ≤ r k := (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ k))
  let h : ℕ → ℝ := fun n => δ/((n:ℝ)+1)
  have hh (n : ℕ) : 0 < h n := div_pos hδ (by positivity)
  have hhδ (n : ℕ) : h n ≤ δ := (div_le_self hδ.le (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have hh1 (n : ℕ) : h n ≤ 1 := (hhδ n).trans hδ1
  have ht : Tendsto h atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using (tendsto_const_nhds (x := δ)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hs := sampled_moment_tendsto B C hB hC hsB hsC hCB hCC (show 0 ≤ 1/δ by positivity) hb hc
    hh hh1 ht (fun k => hardKernel (r k) (R k)) (fun k => measurable_hardKernel _ _)
    (fun k t => (abs_hardKernel_le (hr k) (hR k) t).trans (one_div_le_one_div_of_le hδ (hδr k)))
    (fun k z => ae_continuousAt_hardKernel (r k) (R k) (z.1+z.2))
  have hsB' := sampled_cubic_tendsto B hB hsB hCB hb hh hh1 ht
  have hsC' := sampled_cubic_tendsto C hC hsC hCC hc hh hh1 ht
  exact le_of_tendsto_of_tendsto hs (tendsto_const_nhds.mul (hsB'.add hsC'))
    (Filter.Eventually.of_forall (fun n => sampled_moment_le B C (hh n) hsB hsC r R
      (fun k => (hhδ n).trans (hδr k)) hR))

lemma continuum_moment_le_compact (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    (hsB : HasCompactSupport B) (hsC : HasCompactSupport C)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z)) ≤
      momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3)) := by
  obtain ⟨MB,hMB,hb⟩ := compactSupport_box B hsB
  obtain ⟨MC,hMC,hc⟩ := compactSupport_box C hsC
  obtain ⟨CB,hCB⟩ := hB.bounded_above_of_compact_support hsB
  obtain ⟨CC,hCC⟩ := hC.bounded_above_of_compact_support hsC
  have hCB0 : 0 ≤ CB := (norm_nonneg (B 0)).trans (hCB 0)
  have hCC0 : 0 ≤ CC := (norm_nonneg (C 0)).trans (hCC 0)
  exact continuum_moment_le_box B C hB hC
    (M := max MB MC) (fun z hz => ⟨(hb z hz).1.trans (le_max_left _ _),(hb z hz).2.trans (le_max_left _ _)⟩)
    (fun z hz => ⟨(hc z hz).1.trans (le_max_right _ _),(hc z hz).2.trans (le_max_right _ _)⟩)
    hCB0 hCC0 hCB hCC r R hr hR
end
end TriangularHilbert.Heat
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

-- ---- from OAI.Analysis.TriangularHilbert.CyclicCompact ----
namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma integrable_cyclic_moment_compact (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    (hsB : HasCompactSupport B) (hsC : HasCompactSupport C)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    Integrable (fun z : ℝ×ℝ => finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z)) := by
  classical
  obtain ⟨MB,_,hb⟩ := compactSupport_box B hsB
  obtain ⟨MC,_,hc⟩ := compactSupport_box C hsC
  obtain ⟨CB,hCB⟩ := hB.bounded_above_of_compact_support hsB
  obtain ⟨CC,hCC⟩ := hC.bounded_above_of_compact_support hsC
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty r
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun k _ => hr k)
  have hδr (k : κ) : δ ≤ r k := Finset.inf'_le _ (Finset.mem_univ k)
  apply integrable_cyclic_moment_box B C hB.measurable hC.measurable
    (M := max MB MC) (fun z hz => ⟨(hb z hz).1.trans (le_max_left _ _),(hb z hz).2.trans (le_max_left _ _)⟩)
    (fun z hz => ⟨(hc z hz).1.trans (le_max_right _ _),(hc z hz).2.trans (le_max_right _ _)⟩)
    ((norm_nonneg (B 0)).trans (hCB 0)) ((norm_nonneg (C 0)).trans (hCC 0))
    (show 0 ≤ 1/δ by positivity) hCB hCC (fun k => hardKernel (r k) (R k))
    (fun k => measurable_hardKernel _ _)
  exact fun k t => (abs_hardKernel_le (hr k) (hR k) t).trans (one_div_le_one_div_of_le hδ (hδr k))

lemma lintegral_cyclic_moment_le_compact (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    (hsB : HasCompactSupport B) (hsC : HasCompactSupport C)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫⁻ z : ℝ×ℝ, ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z))) ≤
      ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cyclic_moment_compact B C hB hC hsB hsC r R hr hR)
    (Eventually.of_forall (fun z => finiteMoment_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (continuum_moment_le_compact B C hB hC hsB hsC r R hr hR)
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CubicLimit ----
namespace OAI

universe uα

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma tendsto_integral_cubes (f : ℝ×ℝ → ℂ) (g : ℕ → ℝ×ℝ → ℂ) (hg : ∀ n, Continuous (g n))
    {D : ℝ×ℝ → ℝ} (hD : Integrable D)
    (hb : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖g n z‖^3 ≤ D z) ∧ Tendsto (fun n => g n z) atTop (𝓝 (f z))) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, ‖g n z‖^3) atTop (𝓝 (∫ z : ℝ×ℝ, ‖f z‖^3)) := by
  apply tendsto_integral_of_dominated_convergence D (fun n => (hg n).norm.pow 3 |>.aestronglyMeasurable) hD
  · intro n
    filter_upwards [hb] with z hz
    simpa only [Pi.pow_apply,Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)] using hz.1 n
  · filter_upwards [hb] with z hz
    exact hz.2.norm.pow 3

lemma lintegral_le_of_ae_tendsto {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} {b : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hm : ∀ n, AEMeasurable (F n) μ) (ht : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a)))
    (hb : ∀ n, (∫⁻ a, F n a ∂μ) ≤ b n) (hc : Tendsto b atTop (𝓝 c)) :
    (∫⁻ a, f a ∂μ) ≤ c := by
  calc
    (∫⁻ a, f a ∂μ) = ∫⁻ a, liminf (fun n => F n a) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with a ha
      exact ha.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le' hm
    _ ≤ liminf b atTop := liminf_le_liminf (Eventually.of_forall hb)
    _ = c := hc.liminf_eq
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicDensity ----
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
open scoped Topology ENNReal
noncomputable section

lemma lintegral_cyclic_moment_le (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫⁻ z : ℝ×ℝ, ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z))) ≤
      ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3))) := by
  obtain ⟨F,hF,D,hD,_,hb⟩ := exists_cubic_approximation B hB
  obtain ⟨G,hG,E,hE,_,hc⟩ := exists_cubic_approximation C hC
  have ht := tendsto_cyclicKernelOutput_of_cubic_dom B C F G (fun n => (hF n).1) (fun n => (hG n).1) hD hE hb hc
  apply lintegral_le_of_ae_tendsto
    (F := fun n z => ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput (F n) (G n) (hardKernel (r k) (R k)) z)))
    (b := fun n => ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖F n z‖^3)+(∫ z : ℝ×ℝ, ‖G n z‖^3))))
  · intro n
    exact (ENNReal.continuous_ofReal.comp continuous_finiteMoment).measurable.comp
      (Measurable.of_eval (fun k => measurable_cyclicKernelOutput (F n) (G n)
        (hF n).1.measurable (hG n).1.measurable _ (measurable_hardKernel _ _))) |>.aemeasurable
  · filter_upwards [ht] with z hz
    exact (ENNReal.continuous_ofReal.comp continuous_finiteMoment).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr (fun k => hz (r k) (R k) (hr k) (hR k)))
  · intro n
    exact lintegral_cyclic_moment_le_compact (F n) (G n) (hF n).1 (hG n).1 (hF n).2.1 (hG n).2.1 r R hr hR
  · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul ((tendsto_integral_cubes B F (fun n => (hF n).1) hD hb).add
        (tendsto_integral_cubes C G (fun n => (hG n).1) hE hc)))
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology ENNReal


theorem solution.{uκ} : type_of% @_root_.OAI.TriangularHilbert.Heat.lintegral_cyclic_moment_le.{uκ} := @_root_.OAI.TriangularHilbert.Heat.lintegral_cyclic_moment_le.{uκ}
