-- Prove2me | solution 1 for OAI.RuledApproximation.hyperbolic_local_patch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:52:24.72828+00:00
-- url     : https://prove2.me/submissions/eb3720a9-d9c0-4fc0-b6bb-1e75553d9b06

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/HyperbolicCover.lean:L186-L251
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.hyperbolic_local_patch. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Theorems.Thm_OAI_RuledApproximation_c1_local_remainder
import Theorems.Thm_OAI_RuledApproximation_framed_local_cover
import Theorems.Thm_OAI_RuledApproximation_hyperbolic_lattice_model

-- ---- from OAI.Geometry.RuledCovering.LocalApproximation ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Extending a nonnegative continuous weight from a compact patch does not alter it there. -/
theorem continuous_nonneg_extension {E : Type*} [TopologicalSpace E] [NormalSpace E]
    {K : Set E} (hK : IsClosed K) {f : E → ℝ} (hf : ContinuousOn f K)
    (hn : ∀ x ∈ K, 0 ≤ f x) :
    ∃ F : E → ℝ, Continuous F ∧ (∀ x, 0 ≤ F x) ∧ Set.EqOn F f K := by
  let fc : C(K, ℝ) := ⟨_, continuousOn_iff_continuous_domRestrict.mp hf⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hK fc
  refine ⟨fun x => max (g x) 0, g.continuous.max continuous_const, fun x => le_max_right _ _, ?_⟩
  intro x hx
  have hgx : g x = f x := congrArg (fun q : C(K, ℝ) => q ⟨x, hx⟩) hg
  dsimp only
  rw [hgx, max_eq_left (hn x hx)]

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.HyperbolicCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma hyperbolic_frame (A : Plane →L[ℝ] Plane) {lam : ℝ} (hlam : 0 < lam)
    (hplus : Module.End.HasEigenvalue A.toLinearMap lam)
    (hminus : Module.End.HasEigenvalue A.toLinearMap (-lam)) :
    ∃ M : Coordinates ≃L[ℝ] Plane, ∀ z : Coordinates,
      M.symm (A (M z)) = ![lam * z 1, lam * z 0] := by
  obtain ⟨u, hu⟩ := hplus.exists_hasEigenvector
  obtain ⟨v, hv⟩ := hminus.exists_hasEigenvector
  have hvals : Function.Injective (![lam, -lam] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  have hli : LinearIndependent ℝ (![u, v] : Fin 2 → Plane) :=
    Module.End.eigenvectors_linearIndependent' A.toLinearMap ![lam, -lam] hvals ![u, v] (by
      intro i
      fin_cases i
      · exact hu
      · exact hv)
  let B : Module.Basis (Fin 2) ℝ Plane :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  let M : Coordinates ≃L[ℝ] Plane :=
    (sumDifference.trans B.equivFun.symm).toContinuousLinearEquiv
  have hM (z : Coordinates) : M z = (z 0 + z 1) • u + (z 0 - z 1) • v := by
    simp only [M]
    simp [B, sumDifference]
  have huA : A u = lam • u := hu.apply_eq_smul
  have hvA : A v = (-lam) • v := hv.apply_eq_smul
  refine ⟨M, fun z => ?_⟩
  apply M.injective
  rw [M.apply_symm_apply, hM, map_add, map_smul, map_smul,
    huA, hvA, hM]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  module
lemma HasFiniteCover.mono {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (h : HasFiniteCover shape T A) (hST : S ⊆ T) (hAB : A ≤ B) :
    HasFiniteCover shape S B := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := h
  exact ⟨n, C, hC, hST.trans hcov, hcost.trans hAB⟩

lemma physicalWeight_pos (h : ℝ) (g : Plane) : 0 < physicalWeight h g := by
  apply one_div_pos.mpr
  apply Real.sqrt_pos.mpr
  positivity

lemma physicalWeight_continuous (h : ℝ) : Continuous (physicalWeight h) := by
  apply continuous_const.div
  · apply Real.continuous_sqrt.comp
    fun_prop
  · intro g
    exact (Real.sqrt_pos.mpr (by positivity : 0 < 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2)).ne'

lemma exists_small_inflation (L R : ℝ) {B : ℝ} (hB : 1 < B) :
    ∃ delta : ℝ, 0 < delta ∧ (1 + 2 * L * delta * R) ^ 2 < B := by
  have hc : Continuous (fun d : ℝ => (1 + 2 * L * d * R) ^ 2) := by fun_prop
  have he : ∀ᶠ d : ℝ in 𝓝 0, (1 + 2 * L * d * R) ^ 2 < B :=
    hc.continuousAt.eventually (Iio_mem_nhds (by simpa using hB))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r / 2, half_pos hr, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

/-- Every hyperbolic label has a patch whose compact subsets admit finite covers,
with one prescribed arbitrarily small area inflation. -/
theorem hyperbolic_local_patch {h L B : ℝ} (hh : 0 < h) (hL : 0 < L) (hB : 1 < B)
    {v : Plane → Plane} {U : Set Plane} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : Plane} (hp : p ∈ U) (hhyp : HyperbolicAt L v p) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ K : Set Plane, IsCompact K → K ⊆ V →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover Cylinder.parallelogram (physicalRuled h K v L)
        (h * B * (∫ q in K, physicalWeight h (v q)) + eps) := by
  obtain ⟨lam, hlam, hsmall, hplus, hminus⟩ := hhyp
  have hlampos : 0 < lam := by nlinarith
  obtain ⟨M, hM⟩ := hyperbolic_frame (fderiv ℝ v p) hlampos hplus hminus
  let A : Coordinates →L[ℝ] Coordinates := lam • swapCLM
  let R : ℝ := 1 / (2 * (1 - L * lam))
  have hR : 0 < R := by dsimp [R]; positivity
  have hmodel : LatticeModel A L R := hyperbolic_lattice_model hL hlam hsmall
  obtain ⟨delta, hd, hDB⟩ := exists_small_inflation L R hB
  let w : Coordinates → Coordinates := fun x => M.symm (v (M x))
  let Uc : Set Coordinates := M ⁻¹' U
  have hUco : IsOpen Uc := hU.preimage M.continuous
  have hpc : M.symm p ∈ Uc := by simpa [Uc]
  have hvc : ContDiffOn ℝ 1 (fun x => v (M x)) Uc :=
    hv.comp M.contDiff.contDiffOn (fun x hx => hx)
  have hwc : ContDiffOn ℝ 1 w Uc := M.symm.contDiff.comp_contDiffOn hvc
  have hvder := (hv.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hwd : fderiv ℝ w (M.symm p) = A := by
    have hvd : HasFDerivAt (fun x => v (M x))
        ((fderiv ℝ v p).comp M.toContinuousLinearMap) (M.symm p) := by
      have hvdp : HasFDerivAt v (fderiv ℝ v p) (M (M.symm p)) := by
        simpa using hvder.hasFDerivAt
      exact hvdp.comp (M.symm p) M.hasFDerivAt
    have hcomp := M.symm.hasFDerivAt.comp (M.symm p) hvd
    change fderiv ℝ (M.symm ∘ (fun x => v (M x))) (M.symm p) = A
    rw [hcomp.fderiv]
    ext z i
    have hz := congrArg (fun a : Coordinates => a i) (hM z)
    fin_cases i <;> simpa [A, swapCLM, swapLinear] using hz
  obtain ⟨r, hr, hrU, hrem⟩ := c1_local_remainder hUco hwc hpc hd
  let Vc := ball (M.symm p) (r / 2)
  have hrhalf : r / 2 < r := by linarith
  have hclU : closedBall (M.symm p) (r / 2) ⊆ Uc :=
    (closedBall_subset_ball hrhalf).trans hrU
  have hclF : ContinuousOn (fun x => physicalWeight h (v (M x)))
      (closedBall (M.symm p) (r / 2)) :=
    (physicalWeight_continuous h).comp_continuousOn (hvc.continuousOn.mono hclU)
  obtain ⟨F, hF, hFnon, hFeq⟩ := continuous_nonneg_extension isClosed_closedBall hclF
    (fun x _ => (physicalWeight_pos h (v (M x))).le)
  refine ⟨M '' Vc, M.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · exact ⟨M.symm p, mem_ball_self (half_pos hr), M.apply_symm_apply p⟩
  · intro K hK hKV eps heps
    let Kc := M.symm '' K
    have hKc : IsCompact Kc := hK.image M.symm.continuous
    have hKcV : Kc ⊆ Vc := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKV hq
      simpa using hx
    have himg : M '' Kc = K := by simp [Kc]
    have hc := framed_local_cover M hh hL.le hR.le hd.le hKc isOpen_ball hKcV v A hmodel
      (fun x hx y hy => by
        rw [← hwd]
        exact hrem x (ball_subset_ball hrhalf.le hx) y (ball_subset_ball hrhalf.le hy))
      hF hFnon (fun x hx => hFeq (ball_subset_closedBall hx)) heps
    rw [himg] at hc
    apply hc.mono Subset.rfl
    have hI : 0 ≤ ∫ q in K, physicalWeight h (v q) :=
      integral_nonneg (fun q => (physicalWeight_pos h (v q)).le)
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDB.le hh.le) hI]

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.hyperbolic_local_patch := @_root_.OAI.RuledApproximation.hyperbolic_local_patch
