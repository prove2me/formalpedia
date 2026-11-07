-- Prove2me | solution 1 for GlynnSTS.Length.proposition_2_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:52:28.185702+00:00
-- url     : https://prove2.me/submissions/fe852e33-bc4e-4bae-b9b4-d738a64b1bbb

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTSProp28

/-- The evaluation σ-algebra on `C[0,1]`. -/
def Mev : MeasurableSpace C(unitInterval, ℝ) :=
  ⨆ t : unitInterval, MeasurableSpace.comap (fun f : C(unitInterval, ℝ) => f t) inferInstance

theorem measurableSet_eval (t : unitInterval) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet[Mev] ((fun f : C(unitInterval, ℝ) => f t) ⁻¹' S) :=
  le_iSup (fun t : unitInterval =>
    MeasurableSpace.comap (fun f : C(unitInterval, ℝ) => f t) inferInstance) t _ ⟨S, hS, rfl⟩

theorem measurableSet_closedBall (f0 : C(unitInterval, ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    MeasurableSet[Mev] (Metric.closedBall f0 r) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense unitInterval
  have heq : Metric.closedBall f0 r =
      ⋂ d ∈ D, (fun f : C(unitInterval, ℝ) => f d) ⁻¹' Metric.closedBall (f0 d) r := by
    ext f
    simp only [Metric.mem_closedBall, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h d _
      exact (ContinuousMap.dist_apply_le_dist d).trans h
    · intro h
      rw [ContinuousMap.dist_le hr]
      have hcl : IsClosed {x : unitInterval | dist (f x) (f0 x) ≤ r} :=
        isClosed_le (f.continuous.dist f0.continuous) continuous_const
      have hsub : D ⊆ {x : unitInterval | dist (f x) (f0 x) ≤ r} := fun d hd => h d hd
      have := hcl.closure_subset_iff.2 hsub
      rw [hDd.closure_eq] at this
      intro x; exact this (Set.mem_univ x)
  rw [heq]
  exact MeasurableSet.biInter hDc (fun d _ => measurableSet_eval d Metric.isClosed_closedBall.measurableSet)

theorem borel_le_Mev : (inferInstance : MeasurableSpace C(unitInterval, ℝ)) ≤ Mev := by
  have hb : (inferInstance : MeasurableSpace C(unitInterval, ℝ)) = borel _ := rfl
  rw [hb, borel]
  refine MeasurableSpace.generateFrom_le (fun U hU => ?_)
  obtain ⟨Dc, hDcc, hDcd⟩ := TopologicalSpace.exists_countable_dense C(unitInterval, ℝ)
  let C : Set (C(unitInterval, ℝ) × ℚ) :=
    {p | p.1 ∈ Dc ∧ 0 < p.2 ∧ Metric.closedBall p.1 (p.2 : ℝ) ⊆ U}
  have hCc : C.Countable :=
    (hDcc.prod (Set.countable_univ : (Set.univ : Set ℚ).Countable)).mono
      (fun p hp => Set.mem_prod.2 ⟨hp.1, Set.mem_univ _⟩)
  have heq : U = ⋃ p ∈ C, Metric.closedBall p.1 (p.2 : ℝ) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (show IsOpen U from hU) x hx
      obtain ⟨d, hd, hdD⟩ := (Metric.dense_iff.1 hDcd) x (ε / 4) (by positivity)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
      rw [Metric.mem_ball] at hd
      refine Set.mem_biUnion (x := (d, q)) ⟨hdD, ?_, ?_⟩ ?_
      · exact_mod_cast (show (0:ℝ) < q by linarith)
      · intro y hy
        apply hball
        rw [Metric.mem_closedBall] at hy
        rw [Metric.mem_ball]
        calc dist y x ≤ dist y d + dist d x := dist_triangle _ _ _
          _ < ε := by simp only at hy; linarith
      · rw [Metric.mem_closedBall, dist_comm]; linarith
    · exact Set.iUnion₂_subset (fun p hp => hp.2.2)
  rw [heq]
  exact MeasurableSet.biUnion hCc (fun p hp =>
    measurableSet_closedBall p.1 (by exact_mod_cast hp.2.1.le))

end GlynnSTSProp28

open GlynnSTSProp28 in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g) :
    IndepFun (fun ω => B ω 1) (fun ω => g (B ω)) P := by
  classical
  obtain ⟨hBm, W, hW, hBW⟩ := hB
  have hpre := hW.toIsPreBrownianReal
  let wt : unitInterval → ℝ≥0 := fun t => ⟨t, t.2.1⟩
  let X : Unit → Ω → ℝ := fun _ ω => W (wt 1) ω
  let Y : unitInterval → Ω → ℝ := fun t ω => W (wt t) ω - (t : ℝ) * W (wt 1) ω
  have hGP : IsGaussianProcess (Sum.elim X Y) P := by
    refine hpre.isGaussianProcess.of_isGaussianProcess (fun s => ?_)
    rcases s with u | t
    · exact ⟨{wt 1},
        { toFun x := x ⟨wt 1, by simp⟩
          map_add' := by simp
          map_smul' := by simp },
        by intro ω; simp [X]⟩
    · exact ⟨{wt t, wt 1},
        { toFun x := x ⟨wt t, by simp⟩ - (t : ℝ) * x ⟨wt 1, by simp⟩
          map_add' x y := by simp; ring
          map_smul' c x := by simp; ring },
        by intro ω; simp [Y]⟩
  have hmem : ∀ s : ℝ≥0, MemLp (W s) 2 P := fun s =>
    (hpre.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have mX : ∀ s, AEMeasurable (X s) P := fun _ => hpre.aemeasurable _
  have mY : ∀ t, AEMeasurable (Y t) P := fun t =>
    (hpre.aemeasurable _).sub ((hpre.aemeasurable _).const_mul _)
  have hcov : ∀ s t, cov[X s, Y t; P] = 0 := by
    intro s t
    simp only [X, Y]
    rw [covariance_fun_sub_right (hmem _) (hmem _) ((hmem _).const_mul _),
      covariance_const_mul_right, hpre.covariance_eval, hpre.covariance_eval]
    have h1 : min (wt 1) (wt t) = wt t := min_eq_right (by
      show (t : ℝ) ≤ ((1 : unitInterval) : ℝ)
      exact t.2.2)
    rw [h1, min_self]
    show (t:ℝ) - (t:ℝ) * ((1:unitInterval):ℝ) = 0
    simp
  have hind := hGP.indepFun_of_covariance_eq_zero mX mY hcov
  -- the bridge as a `C[0,1]`-valued random element
  let Z : Ω → C(unitInterval, ℝ) := fun ω => GlynnSTS.Length.Gamma (B ω)
  have hZY : ∀ ω t, Z ω t = Y t ω := by
    intro ω t
    simp only [Z, Y, GlynnSTS.Length.Gamma, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      GlynnSTS.Limit.kfun, ContinuousMap.coe_mk, smul_eq_mul, hBW]
    ring
  have hle : MeasurableSpace.comap Z inferInstance ≤
      MeasurableSpace.comap (fun ω t => Y t ω) MeasurableSpace.pi := by
    refine (MeasurableSpace.comap_mono borel_le_Mev).trans ?_
    simp only [Mev, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup_le (fun t => ?_)
    have : ((fun f : C(unitInterval, ℝ) => f t) ∘ Z) =
        (fun f : unitInterval → ℝ => f t) ∘ (fun ω t => Y t ω) := by
      funext ω; simp [hZY]
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply t).comap_le
  have hind2 : IndepFun (fun ω s => X s ω) Z P := by
    rw [IndepFun_iff_Indep] at hind ⊢
    exact indep_of_indep_of_le_right hind hle
  have hfin := hind2.comp (φ := fun f : Unit → ℝ => f ()) (ψ := g)
    (by fun_prop : Measurable fun f : Unit → ℝ => f ()) hg.1
  have e1 : (fun ω => B ω 1) = (fun f : Unit → ℝ => f ()) ∘ (fun ω s => X s ω) := by
    funext ω; simp only [Function.comp_apply, X, hBW]; rfl
  have e2 : (fun ω => g (B ω)) = g ∘ Z := by
    funext ω
    simp only [Function.comp_apply, Z, GlynnSTS.Length.Gamma]
    exact (hg.2.2.1 (B ω 1) (B ω)).symm
  rw [e1, e2]
  exact hfin
