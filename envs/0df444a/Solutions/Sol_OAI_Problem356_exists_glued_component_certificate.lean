-- Prove2me | solution 1 for OAI.Problem356.exists_glued_component_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:26:44.242531+00:00
-- url     : https://prove2.me/submissions/b4f2b6dd-4033-4f7b-8304-6355d5467ff2

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate

open OAI OAI.Problem356
universe uIndex
open Set Filter Metric
open scoped ENNReal BigOperators
open OAI OAI.Problem356 in
theorem ap_fcc_cont : Continuous coulombCost := by
  have hc : ∀ (f g : Triple → E3), Continuous f → Continuous g →
      Continuous (fun t => (ENNReal.ofReal ‖f t - g t‖)⁻¹) := fun f g hf hg =>
    continuous_inv.comp (ENNReal.continuous_ofReal.comp (hf.sub hg).norm)
  unfold coulombCost invDistance tripleFst tripleSnd tripleThd
  exact ((hc _ _ continuous_fst (continuous_fst.comp continuous_snd)).add
    (hc _ _ continuous_fst (continuous_snd.comp continuous_snd))).add
    (hc _ _ (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))

theorem h41_fcc {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (v : ι → E3 → ℝ)
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hv : ∀ i, ContinuousAt (v i) (p i))
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r : ℝ, 0 < r ∧ ∀ a, ∀ x y z : E3,
      x ∈ ball (p a.1) r → y ∈ ball (p a.2.1) r → z ∈ ball (p a.2.2) r →
      ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) ≤ coulombCost (x, (y, z)) ∧
      (ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) = coulombCost (x, (y, z)) ↔
        Good a ∧ Contact a (x, (y, z))) := by
  classical
  have hloc : ∀ a : ι × (ι × ι), ∃ ra > 0, ∀ t : Triple,
      dist t (p a.1, (p a.2.1, p a.2.2)) < ra →
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) = coulombCost t ↔
        Good a ∧ Contact a t) := by
    intro a
    rw [← Metric.eventually_nhds_iff]
    by_cases hg : Good a
    · filter_upwards [hgood a hg] with t ht
      exact ⟨ht.1, by simp [hg, ht.2]⟩
    · have hc : ContinuousAt (fun t : Triple =>
          ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2))
          (p a.1, (p a.2.1, p a.2.2)) := by
        refine ENNReal.continuous_ofReal.continuousAt.comp ?_
        exact ((ContinuousAt.comp_of_eq (hv a.1) continuousAt_fst rfl).add
          (ContinuousAt.comp_of_eq (hv a.2.1) (continuousAt_fst.comp continuousAt_snd) rfl)).add
          (ContinuousAt.comp_of_eq (hv a.2.2) (continuousAt_snd.comp continuousAt_snd) rfl)
      filter_upwards [hc.eventually_lt ap_fcc_cont.continuousAt (hbad a hg)] with t ht
      exact ⟨ht.le, by simp [hg, ht.ne]⟩
  choose R hR hRP using hloc
  have hev : ∀ᶠ r in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ a, r < R a := by
    rw [Filter.eventually_all]
    intro a
    exact nhdsWithin_le_nhds (Iio_mem_nhds (hR a))
  obtain ⟨r, hr, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨r, hr0, fun a x y z hx hy hz => ?_⟩
  apply hRP
  have : dist ((x, (y, z)) : Triple) (p a.1, (p a.2.1, p a.2.2)) < r := by
    rw [Metric.mem_ball] at hx hy hz
    simp only [Prod.dist_eq]
    exact max_lt hx (max_lt hy hz)
  exact this.trans (hr a)

theorem h41_gcc {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (p i) r
      let u := ComponentPotential.glue U v
      (∀ i, U i ⊆ V i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) ↔
          componentContact U Good Contact (x, (y, z)))) := by
  classical
  have hva : ∀ i, ContinuousAt (v i) (p i) := fun i => (hv i).continuousAt ((hV i).mem_nhds (hpV i))
  obtain ⟨r1, hr1, hcert⟩ := h41_fcc p v Good Contact hva hgood hbad
  -- disjoint closed balls inside V
  have hunif : ∀ {κ : Type uIndex} [Finite κ] (r : κ → ℝ), (∀ i, 0 < r i) → ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ r i := by
    intro κ _ r hr
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · have := Fintype.ofFinite κ
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ r Finset.univ_nonempty
      exact ⟨r i₀, hr i₀, fun i => hi₀ i (Finset.mem_univ i)⟩
  obtain ⟨δ, hδ, hle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ q : {q : ι × ι // q.1 ≠ q.2}, δ ≤ dist (p q.1.1) (p q.1.2) / 3 := by
    obtain ⟨δ, hδ, h⟩ := hunif (κ := ULift.{uIndex} {q : ι × ι // q.1 ≠ q.2})
      (fun q => dist (p q.down.1.1) (p q.down.1.2) / 3)
      (fun q => by have := dist_pos.mpr (hp.ne q.down.2); positivity)
    exact ⟨δ, hδ, fun q => h ⟨q⟩⟩
  have hε : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ball (p i) ε ⊆ V i := fun i =>
    Metric.isOpen_iff.mp (hV i) (p i) (hpV i)
  choose ε hε hεV using hε
  obtain ⟨η, hη, hηle⟩ := hunif ε hε
  -- bound
  have hb : ∀ i, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ ball (p i) ρ, |v i x| ≤ |v i (p i)| + 1 := by
    intro i
    obtain ⟨ρ, hρ, h⟩ := Metric.continuousAt_iff.mp (hva i) 1 one_pos
    refine ⟨ρ, hρ, fun x hx => ?_⟩
    have := h (Metric.mem_ball.mp hx)
    rw [Real.dist_eq] at this
    have h2 := abs_sub_abs_le_abs_sub (v i x) (v i (p i))
    linarith
  choose ρ hρ hρb using hb
  obtain ⟨ρ0, hρ0, hρle⟩ := hunif ρ hρ
  set M : ℝ := 1 + ∑ i, |v i (p i)| with hM
  have hMpos : 0 < M := by positivity
  have hMi : ∀ i, |v i (p i)| + 1 ≤ M := fun i => by
    have : |v i (p i)| ≤ ∑ j, |v j (p j)| :=
      Finset.single_le_sum (f := fun j => |v j (p j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  set r : ℝ := min (min r1 δ) (min η ρ0) with hr
  have hr0 : 0 < r := lt_min (lt_min hr1 hδ) (lt_min hη hρ0)
  have hrr1 : r ≤ r1 := (min_le_left _ _).trans (min_le_left _ _)
  have hrδ : r ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hrη : r ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hrρ : r ≤ ρ0 := (min_le_right _ _).trans (min_le_right _ _)
  have hUV : ∀ i, ball (p i) r ⊆ V i := fun i =>
    (Metric.ball_subset_ball (hrη.trans (hηle i))).trans (hεV i)
  have hmem : ∀ {i j : ι} {x : E3}, x ∈ ball (p i) r → x ∈ ball (p j) r → i = j := by
    intro i j x hi hj
    by_contra hij
    have h3 := hle ⟨(i, j), hij⟩
    have h4 := dist_triangle_right (p i) (p j) x
    rw [Metric.mem_ball] at hi hj
    simp only at h3
    rw [dist_comm (p i) x, dist_comm (p j) x] at h4
    linarith
  have hdisj : Pairwise (fun i j => Disjoint (ball (p i) r) (ball (p j) r)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    exact hij (hmem hi hj)
  have hglue_in : ∀ i x, x ∈ ball (p i) r →
      ComponentPotential.glue (fun i => ball (p i) r) v x = v i x := by
    intro i x hx
    unfold ComponentPotential.glue
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hx _
    · intro j _ hji
      exact Set.indicator_of_notMem (fun hj => hji (hmem hj hx)) _
    · intro h; exact absurd (Finset.mem_univ i) h
  have hglue_out : ∀ x, (∀ i, x ∉ ball (p i) r) →
      ComponentPotential.glue (fun i => ball (p i) r) v x = 0 := by
    intro x hx
    unfold ComponentPotential.glue
    exact Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (hx i) _
  refine ⟨r, M, hr0, hMpos, hUV, hdisj, ?_, ?_, ?_, ?_⟩
  · unfold ComponentPotential.glue
    refine Finset.measurable_sum _ fun i _ => ?_
    have : (ball (p i) r).indicator (v i) = (ball (p i) r).piecewise (v i) (fun _ => 0) := by
      funext x; simp [Set.piecewise, Set.indicator]
    rw [this]
    exact ContinuousOn.measurable_piecewise ((hv i).mono (hUV i)) continuousOn_const
      Metric.isOpen_ball.measurableSet
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    refine ContinuousAt.continuousWithinAt ?_
    have hev : (fun y => v i y) =ᶠ[nhds x] ComponentPotential.glue (fun i => ball (p i) r) v :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hi) fun y hy => (hglue_in i y hy).symm
    exact ((hv i).continuousAt ((hV i).mem_nhds (hUV i hi))).congr hev
  · intro x
    by_cases h : ∃ i, x ∈ ball (p i) r
    · obtain ⟨i, hi⟩ := h
      rw [hglue_in i x hi]
      exact (hρb i x (Metric.ball_subset_ball (hrρ.trans (hρle i)) hi)).trans (hMi i)
    · simp only [not_exists] at h
      rw [hglue_out x h, abs_zero]
      exact hMpos.le
  · intro x hx y hy z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    rw [hglue_in i x hi, hglue_in j y hj, hglue_in k z hk]
    have hc := hcert (i, (j, k)) x y z (Metric.ball_subset_ball hrr1 hi)
      (Metric.ball_subset_ball hrr1 hj) (Metric.ball_subset_ball hrr1 hk)
    refine ⟨hc.1, ?_⟩
    rw [hc.2]
    constructor
    · rintro ⟨hg, hcon⟩
      exact ⟨(i, (j, k)), hi, hj, hk, hg, hcon⟩
    · rintro ⟨a, ha1, ha2, ha3, hg, hcon⟩
      have e1 : a.1 = i := hmem ha1 hi
      have e2 : a.2.1 = j := hmem ha2 hj
      have e3 : a.2.2 = k := hmem ha3 hk
      obtain ⟨a1, a2, a3⟩ := a
      simp only at e1 e2 e3
      subst e1 e2 e3
      exact ⟨hg, hcon⟩

theorem solution {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (p i) r
      let u := ComponentPotential.glue U v
      (∀ i, U i ⊆ V i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) ↔
          componentContact U Good Contact (x, (y, z)))) := by
  exact h41_gcc p hp V hV hpV v hv Good Contact hgood hbad

