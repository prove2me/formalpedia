-- Prove2me | solution 1 for KleywegtSAA.ValueCLT.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:13:58.542365+00:00
-- url     : https://prove2.me/submissions/413e0871-2139-4750-8ee0-90647bc97cb9

import Mathlib
import Definitions.Def_KleywegtSAA_ValueCLT_Setting
import Theorems.Thm_KleywegtSAA_ValueCLT_joint_clt
import Theorems.Thm_KleywegtSAA_ValueCLT_scaled_gap_tendsto_zero
import Theorems.Thm_KleywegtSAA_ValueCLT_sqrt_mul_minOnOpt_sub

open MeasureTheory ProbabilityTheory Filter Topology
open KleywegtSAA.ValueCLT

open Classical in
theorem solution
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P)
    (hvar : ∀ x ∈ optSet S hS (KleywegtSAA.ExpRate.trueObj G P W), MemLp (fun ω => G x (W 0 ω)) 2 P) :
    ∀ {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
      (Y : Ω' → EuclideanSpace ℝ (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W))),
      HasLaw Y (multivariateGaussian 0 (covMat G P W (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)))) Q →
      TendstoInDistribution
        (fun (N : ℕ) ω => Real.sqrt N * (S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - S.inf' hS (KleywegtSAA.ExpRate.trueObj G P W)))
        atTop
        (fun ω' => Finset.univ.inf'
          (Finset.univ_nonempty_iff.2 (optSet_nonempty S hS (KleywegtSAA.ExpRate.trueObj G P W)).to_subtype)
          (fun x => Y ω' x))
        (fun _ => P) Q := by
  intro Ω' _ Q _ Y hY
  have hTS : optSet S hS (KleywegtSAA.ExpRate.trueObj G P W) ⊆ S := Finset.filter_subset _ _
  have hne : (Finset.univ : Finset (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W))).Nonempty :=
    Finset.univ_nonempty_iff.2 (optSet_nonempty S hS (KleywegtSAA.ExpRate.trueObj G P W)).to_subtype
  -- the continuous functional `y ↦ min_{x ∈ S*} y x`
  let F : EuclideanSpace ℝ (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)) → ℝ := fun y => Finset.univ.inf' hne (fun x => y x)
  have hF : Continuous F := by
    refine Continuous.finset_inf'_apply hne (fun x _ => ?_)
    exact (EuclideanSpace.proj (𝕜 := ℝ) x).continuous
  -- joint CLT on `S*`
  have hclt := joint_clt S G hG P W hWm hind hid _ hTS hvar Q Y hY
  have h1 := hclt.continuous_comp hF
  -- the gap
  obtain ⟨-, hgap⟩ := scaled_gap_tendsto_zero S hS G hG P W hWm hind hid hint
  -- measurability of the gap
  have hsm : ∀ N, ∀ x ∈ S, Measurable (fun ω => KleywegtSAA.ExpRate.sampleObj G W N ω x) := by
    intro N x hx
    unfold KleywegtSAA.ExpRate.sampleObj
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ (fun n _ => (hG x hx).comp (hWm n))
  have hinf : ∀ (U : Finset X) (hU : U.Nonempty), U ⊆ S → ∀ N : ℕ,
      Measurable (fun ω : Ω => U.inf' hU (KleywegtSAA.ExpRate.sampleObj G W N ω)) := by
    intro U hU hUS N
    have : (fun ω => U.inf' hU (KleywegtSAA.ExpRate.sampleObj G W N ω)) =
        U.inf' hU (fun x ω => KleywegtSAA.ExpRate.sampleObj G W N ω x) := by
      funext ω; rw [Finset.inf'_apply]
    rw [this]
    exact Finset.inf'_induction hU _ (fun _ hf _ hg => hf.inf hg) (fun x hx => hsm N x (hUS hx))
  have hgapm : ∀ N : ℕ, AEMeasurable (fun ω =>
      Real.sqrt N * (S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - minOnOpt S hS G P W N ω)) P := by
    intro N
    refine (Measurable.const_mul ?_ _).aemeasurable
    exact (hinf S hS subset_rfl N).sub (hinf _ _ hTS N)
  have h2 := h1.add_of_tendstoInMeasure_const hgap hgapm
  refine h2.congr ?_ ?_
  · intro N
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [Pi.add_apply, Function.comp_apply]
    have key := sqrt_mul_minOnOpt_sub S hS G P W N ω
    have hFe : F (scaledDev G P W (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)) N ω) =
        (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)).inf'
          (optSet_nonempty S hS (KleywegtSAA.ExpRate.trueObj G P W)) (fun x =>
          Real.sqrt N * (KleywegtSAA.ExpRate.sampleObj G W N ω x - KleywegtSAA.ExpRate.trueObj G P W x)) := by
      apply le_antisymm
      · refine Finset.le_inf' _ _ (fun x hx => ?_)
        exact Finset.inf'_le (f := fun y : (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)) =>
          (scaledDev G P W (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)) N ω) y)
          (Finset.mem_univ (⟨x, hx⟩ : (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W))))
      · refine Finset.le_inf' _ _ (fun x _ => ?_)
        exact Finset.inf'_le (f := fun y =>
          Real.sqrt N * (KleywegtSAA.ExpRate.sampleObj G W N ω y - KleywegtSAA.ExpRate.trueObj G P W y)) x.2
    rw [hFe, ← key]
    ring
  · exact Filter.Eventually.of_forall (fun ω => by simp [F])
