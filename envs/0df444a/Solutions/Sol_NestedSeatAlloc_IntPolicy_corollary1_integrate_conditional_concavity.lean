-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.corollary1_integrate_conditional_concavity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:26:10.506039+00:00
-- url     : https://prove2.me/submissions/2336d74b-2fb2-48d1-bc92-3e1ce1744d0d

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_measurable_prefixRevenueRebuild
import Theorems.Thm_revenue_integrable_of_seat_model
import Theorems.Thm_condRevenue_eq_integral_prefix_law
import Theorems.Thm_concaveOn_of_ae_integral_representation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (k : ℕ)
    (hcond : ∀ y : ℝ, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) :
    ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p (k + 1)) := by
  letI : IsProbabilityMeasure P := hM.isProb
  let S : Finset ℕ := Finset.Icc 1 k
  let T : Finset ℕ := {k + 1}
  let U : Ω → S → ℝ := fun ω i => X i.1 ω
  have hU : Measurable U :=
    measurable_pi_lambda U (fun i => hM.meas i.1)
  have hV : Measurable (X (k + 1)) := hM.meas (k + 1)
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiT
    have hiS' := Finset.mem_Icc.mp hiS
    have hiT' := Finset.mem_singleton.mp hiT
    omega
  have hTuple : IndepFun (fun ω (i : S) => X i.1 ω)
      (fun ω (i : T) => X i.1 ω) P :=
    iIndepFun.indepFun_finset S T hST hM.indep hM.meas
  have hVU : IndepFun (X (k + 1)) U P := by
    have heval : Measurable (fun t : T → ℝ => t ⟨k + 1, by simp [T]⟩) :=
      measurable_pi_apply _
    simpa [Function.comp_def, U, T] using
      hTuple.symm.comp heval measurable_id
  let rebuild := prefixRevenueRebuild k
  have hRebuild := measurable_prefixRevenueRebuild k
  have hPair : Measurable (fun ω : Ω => (X (k + 1) ω, U ω)) :=
    Measurable.prodMk hV hU
  have hJoint (s : ℝ) : Measurable (fun z : ℝ × (Finset.Icc 1 k → ℝ) =>
      revenue f p (rebuild z) (k + 1) s) :=
    (revenue_joint_measurable f p (k + 1)).comp
      (Measurable.prodMk hRebuild measurable_const)
  have hRevenueEq (ω : Ω) (s : ℝ) :
      revenue f p (fun i => X i ω) (k + 1) s =
        revenue f p (rebuild (X (k + 1) ω, U ω)) (k + 1) s := by
    exact revenue_extensional_on_prefix f p (fun i => X i ω)
      (rebuild (X (k + 1) ω, U ω)) (k + 1) (by
        intro i hi
        by_cases hprefix : i ∈ Finset.Icc 1 k
        · simp [rebuild, prefixRevenueRebuild, hprefix, U]
        · have hi' := Finset.mem_Icc.mp hi
          have hnext : i = k + 1 := by
            have hn : ¬ i ≤ k := by
              intro hik
              exact hprefix (Finset.mem_Icc.mpr ⟨hi'.1, hik⟩)
            omega
          simp [rebuild, prefixRevenueRebuild, hprefix, hnext]) s
  have hLaw :
      Measure.map (fun ω : Ω => (X (k + 1) ω, U ω)) P =
        (Measure.map (X (k + 1)) P).prod (Measure.map U P) :=
    hVU.map_prod_eq_prod_map_map hV.aemeasurable hU.aemeasurable
  have hProductIntegrable (s : ℝ) (hs : 0 ≤ s) :
      Integrable (fun z : ℝ × (Finset.Icc 1 k → ℝ) =>
        revenue f p (rebuild z) (k + 1) s)
        ((Measure.map (X (k + 1)) P).prod (Measure.map U P)) := by
    rw [← hLaw]
    have hComp : Integrable
        (fun ω : Ω => revenue f p
          (rebuild (X (k + 1) ω, U ω)) (k + 1) s) P :=
      (revenue_integrable_of_seat_model P X f p hM hp k s hs).congr
        (Filter.Eventually.of_forall (fun ω => hRevenueEq ω s))
    exact (integrable_map_measure (hJoint s).aestronglyMeasurable
      hPair.aemeasurable).mpr hComp
  have hRevenueUpdateEq (ω : Ω) (y s : ℝ) :
      revenue f p (Function.update (fun i => X i ω) (k + 1) y) (k + 1) s =
        revenue f p (rebuild (y, U ω)) (k + 1) s := by
    apply revenue_extensional_on_prefix
    intro i hi
    by_cases hprefix : i ∈ Finset.Icc 1 k
    · have hne : i ≠ k + 1 := by
        intro heq
        subst i
        have hiS := Finset.mem_Icc.mp hprefix
        omega
      simp [rebuild, prefixRevenueRebuild, hprefix, hne, Function.update, U]
    · have hi' := Finset.mem_Icc.mp hi
      have hnext : i = k + 1 := by
        have hn : ¬ i ≤ k := by
          intro hik
          exact hprefix (Finset.mem_Icc.mpr ⟨hi'.1, hik⟩)
        omega
      simp [rebuild, prefixRevenueRebuild, hprefix, hnext, Function.update]
  have hInnerEq (y s : ℝ) :=
    condRevenue_eq_integral_prefix_law P X f p k U rebuild hU hJoint
      hRevenueUpdateEq y s
  have hBridge (s : ℝ) (hs : 0 ≤ s) :
      expRevenue P X f p (k + 1) s =
        ∫ y, condRevenue P X f p (k + 1) y s ∂Measure.map (X (k + 1)) P := by
    unfold expRevenue
    calc
      _ = ∫ ω, revenue f p
          (rebuild (X (k + 1) ω, U ω)) (k + 1) s ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => hRevenueEq ω s)
      _ = ∫ z, revenue f p (rebuild z) (k + 1) s
          ∂Measure.map (fun ω => (X (k + 1) ω, U ω)) P := by
        symm
        exact integral_map hPair.aemeasurable
          (hJoint s).aestronglyMeasurable
      _ = ∫ z, revenue f p (rebuild z) (k + 1) s
          ∂((Measure.map (X (k + 1)) P).prod (Measure.map U P)) := by
        rw [hLaw]
      _ = ∫ y, ∫ u, revenue f p (rebuild (y, u)) (k + 1) s
          ∂Measure.map U P ∂Measure.map (X (k + 1)) P :=
        integral_prod
          (fun z : ℝ × (S → ℝ) => revenue f p (rebuild z) (k + 1) s)
          (hProductIntegrable s hs)
      _ = ∫ y, condRevenue P X f p (k + 1) y s
          ∂Measure.map (X (k + 1)) P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => hInnerEq y s)
  have hSectionIntegrable (s : ℝ) (hs : 0 ≤ s) :
      Integrable (fun y => condRevenue P X f p (k + 1) y s)
        (Measure.map (X (k + 1)) P) := by
    convert (hProductIntegrable s hs).integral_prod_left using 1
    funext y
    exact (hInnerEq y s).symm
  have hVnonneg : ∀ᵐ y ∂Measure.map (X (k + 1)) P, 0 ≤ y := by
    rw [ae_map_iff (hM.meas (k + 1)).aemeasurable measurableSet_Ici]
    exact Filter.Eventually.of_forall (fun ω => hM.nonneg (k + 1) ω)
  have hSectionConcave :
      ∀ᵐ y ∂Measure.map (X (k + 1)) P,
        ConcaveOn ℝ (Set.Ici 0)
          (fun s => condRevenue P X f p (k + 1) y s) := by
    filter_upwards [hVnonneg] with y hy
    exact hcond y hy
  have hConcave := concaveOn_of_ae_integral_representation
    (Measure.map (X (k + 1)) P) (expRevenue P X f p (k + 1))
    (fun y s => condRevenue P X f p (k + 1) y s)
    (fun s hs => hBridge s hs) hSectionConcave hSectionIntegrable
  exact hConcave
