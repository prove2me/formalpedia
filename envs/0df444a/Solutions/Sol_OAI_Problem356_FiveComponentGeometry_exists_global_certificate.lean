-- Prove2me | solution 1 for OAI.Problem356.FiveComponentGeometry.exists_global_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:38:31.020437+00:00
-- url     : https://prove2.me/submissions/2a207ece-9c2a-4755-bb81-76edc6c61bcb

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
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry

open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Filter Metric
open scoped ENNReal InnerProductSpace
open CenterCertificate GoodTypePermutation
universe uIndex

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

theorem h41_gccf {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop) (Contact : Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t → Contact t))
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
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          Contact (x, (y, z)))) := by
  obtain ⟨r, M, hr, hM, h1, h2, h3, h4, h5, h6⟩ := h41_gcc p hp V hV hpV v hv Good
    (fun a t => ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) = coulombCost t ∧ Contact t)
    (fun a ha => (hgood a ha).mono fun t ht => ⟨ht.1, ⟨fun he => ⟨he, ht.2 he⟩, fun he => he.1⟩⟩) hbad
  refine ⟨r, M, hr, hM, h1, h2, h3, h4, h5, fun x hx y hy z hz => ⟨(h6 x hx y hy z hz).1, fun he => ?_⟩⟩
  obtain ⟨a, -, -, -, -, -, hc⟩ := (h6 x hx y hy z hz).2.mp he
  exact hc


theorem h41_cost12 (x y z : E3) : coulombCost (x, (y, z)) = coulombCost (y, (x, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance, norm_sub_rev x y]
  ring

theorem h41_cost23 (x y z : E3) : coulombCost (x, (y, z)) = coulombCost (x, (z, y)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance, norm_sub_rev y z]
  ring

open GoodTypePermutation in
theorem h41_cog {U : Fin 5 → Set E3} {v : Fin 5 → E3 → ℝ} {Contact : Triple → Prop}
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c)))
    (h012 : LocalTypeCertificate U v Contact 0 1 2)
    (h034 : LocalTypeCertificate U v Contact 0 3 4)
    (i j k : Fin 5) (hgood : CenterCertificate.Good i j k) :
    LocalTypeCertificate U v Contact i j k := by
  have s12 : ∀ {a b c : Fin 5}, LocalTypeCertificate U v Contact a b c →
      LocalTypeCertificate U v Contact b a c := by
    intro a b c h x hx y hy z hz
    obtain ⟨h1, h2⟩ := h y hy x hx z hz
    rw [← h41_cost12, show v a y + v b x + v c z = v b x + v a y + v c z by ring] at h1 h2
    exact ⟨h1, fun he => hperm (List.Perm.swap x y [z]) (h2 he)⟩
  have s23 : ∀ {a b c : Fin 5}, LocalTypeCertificate U v Contact a b c →
      LocalTypeCertificate U v Contact a c b := by
    intro a b c h x hx y hy z hz
    obtain ⟨h1, h2⟩ := h x hx z hz y hy
    rw [← h41_cost23, show v a x + v b z + v c y = v a x + v c y + v b z by ring] at h1 h2
    exact ⟨h1, fun he => hperm (List.Perm.cons x (List.Perm.swap y z [])) (h2 he)⟩
  have key : ∀ i j k : Fin 5, CenterCertificate.Good i j k →
      (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 1 ∧ j = 0 ∧ k = 2) ∨ (i = 0 ∧ j = 2 ∧ k = 1) ∨
      (i = 2 ∧ j = 0 ∧ k = 1) ∨ (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 1 ∧ k = 0) ∨
      (i = 0 ∧ j = 3 ∧ k = 4) ∨ (i = 3 ∧ j = 0 ∧ k = 4) ∨ (i = 0 ∧ j = 4 ∧ k = 3) ∨
      (i = 4 ∧ j = 0 ∧ k = 3) ∨ (i = 3 ∧ j = 4 ∧ k = 0) ∨ (i = 4 ∧ j = 3 ∧ k = 0) := by
    unfold CenterCertificate.Good
    decide
  rcases key i j k hgood with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h012
  · exact s12 h012
  · exact s23 h012
  · exact s12 (s23 h012)
  · exact s23 (s12 h012)
  · exact s12 (s23 (s12 h012))
  · exact h034
  · exact s12 h034
  · exact s23 h034
  · exact s12 (s23 h034)
  · exact s23 (s12 h034)
  · exact s12 (s23 (s12 h034))


open OAI OAI.Problem356 OAI.Problem356.CenterCertificate in
theorem ap_cc_norm (a b : Fin 5) : ‖point a - point b‖ = distance a b := by
  fin_cases a <;> fin_cases b <;>
    simp [point, distance, EuclideanSpace.norm_eq, Fin.sum_univ_three] <;> norm_num

open scoped ENNReal in
theorem ap_cc_lt : (5/2 : ℝ≥0∞) < 1 + 1 + (ENNReal.ofReal √2)⁻¹ := by
  have h1 : (ENNReal.ofReal √2)⁻¹ = ENNReal.ofReal (√2)⁻¹ :=
    (ENNReal.ofReal_inv_of_pos (by positivity)).symm
  have h2 : (5/2 : ℝ≥0∞) = ENNReal.ofReal (5/2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have h3 : (1:ℝ≥0∞) + 1 + ENNReal.ofReal (√2)⁻¹ = ENNReal.ofReal (1 + 1 + (√2)⁻¹) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_add (by norm_num) (by norm_num)]
    simp
  rw [h1, h2, h3, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have hs : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have : (2:ℝ)⁻¹ < (√2)⁻¹ := inv_strictAnti₀ (by positivity) hs
  linarith

open OAI OAI.Problem356 OAI.Problem356.CenterCertificate in
open scoped ENNReal in
theorem h41_son (i j k : Fin 5) (h : ¬ Good i j k) :
    potential i + potential j + potential k <
      coulombCost (point i, (point j, point k)) := by
  have key : ∀ a b, invDistance (point a) (point b) = (ENNReal.ofReal (distance a b))⁻¹ :=
    fun a b => by rw [invDistance, ap_cc_norm]
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, key]
  revert h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp (config := {decide := true}) [Good, distance, potential] <;>
    first
    | exact ENNReal.div_lt_top (by norm_num) (by norm_num)
    | (convert ap_cc_lt using 1; try ring)

open OAI OAI.Problem356 StationaryMap in
theorem h41_val (a : E3) (ha : ‖a‖ = 1) : jointPotential a (a, (0, -a)) = 0 := by
  have h2 : ‖-a - a‖ = 2 := by
    rw [show -a - a = -((2:ℝ) • a) by rw [two_smul]; abel, norm_neg, norm_smul, ha]; norm_num
  simp only [jointPotential, statePotential, CoulombCalculus.pairCost, zero_sub, norm_neg, ha,
    sub_neg_eq_add, zero_add, h2, neg_add_cancel, inner_zero_right, norm_zero]
  norm_num

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p1 : ‖point 1‖ = 1 := by
  simp [point, EuclideanSpace.norm_eq, Fin.sum_univ_three]

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p3 : ‖point 3‖ = 1 := by
  simp [point, EuclideanSpace.norm_eq, Fin.sum_univ_three]

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p2 : point 2 + point 1 = 0 := by
  ext i; fin_cases i <;> simp [point]

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p4 : point 4 + point 3 = 0 := by
  ext i; fin_cases i <;> simp [point]

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p0 : point 0 = 0 := by
  ext i; fin_cases i <;> simp [point]

open LocalGeometry StationaryMap in
theorem h41_scg (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (i j k : Fin 5) (h : ¬ Good i j k) :
    ENNReal.ofReal (potentials C₁ C₂ i (point i) +
      potentials C₁ C₂ j (point j) + potentials C₁ C₂ k (point k)) <
      coulombCost (point i, (point j, point k)) := by
  have q0 : potentials C₁ C₂ 0 (point 0) = 5 / 2 := by
    show (5 : ℝ) / 2 - 10 * ‖point 0‖ ^ 2 = 5 / 2
    simp [h41_p0]
  have q1 : potentials C₁ C₂ 1 (point 1) = 0 := by
    show C₁.value (point 1) = 0
    rw [C₁.value_base]; exact h41_val _ h41_p1
  have q2 : potentials C₁ C₂ 2 (point 2) = 0 := by
    show (5 : ℝ) / 4 * inner ℝ (point 1) (point 2 + point 1) - 10 * ‖point 2 + point 1‖ ^ 2 = 0
    simp [h41_p2]
  have q3 : potentials C₁ C₂ 3 (point 3) = 0 := by
    show C₂.value (point 3) = 0
    rw [C₂.value_base]; exact h41_val _ h41_p3
  have q4 : potentials C₁ C₂ 4 (point 4) = 0 := by
    show (5 : ℝ) / 4 * inner ℝ (point 3) (point 4 + point 3) - 10 * ‖point 4 + point 3‖ ^ 2 = 0
    simp [h41_p4]
  have hpot : ∀ i, potentials C₁ C₂ i (point i) = (potential i).toReal := by
    intro i
    fin_cases i
    · rw [show ((⟨0, by decide⟩ : Fin 5)) = 0 from rfl, q0]; simp [potential]
    · rw [show ((⟨1, by decide⟩ : Fin 5)) = 1 from rfl, q1]; simp [potential]
    · rw [show ((⟨2, by decide⟩ : Fin 5)) = 2 from rfl, q2]; simp [potential]
    · rw [show ((⟨3, by decide⟩ : Fin 5)) = 3 from rfl, q3]; simp [potential]
    · rw [show ((⟨4, by decide⟩ : Fin 5)) = 4 from rfl, q4]; simp [potential]
  have hne : ∀ i, potential i ≠ ⊤ := by
    intro i; unfold potential; split_ifs <;> simp [ENNReal.div_eq_top]
  have hsum : ENNReal.ofReal (potentials C₁ C₂ i (point i) +
      potentials C₁ C₂ j (point j) + potentials C₁ C₂ k (point k)) =
      potential i + potential j + potential k := by
    rw [hpot, hpot, hpot, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_toReal (hne i),
      ENNReal.ofReal_toReal (hne j), ENNReal.ofReal_toReal (hne k)]
  rw [hsum]
  exact h41_son i j k h


open scoped InnerProductSpace in
open LocalGeometry StationaryMap in
theorem h41_elc {a : E3} (C : ChartsAt a) {x y z : E3}
    (hy : y ∈ ball a C.parameterRadius)
    (hx : x ∈ ball (0 : E3) C.stateRadius)
    (hz : z ∈ ball (-a) C.stateRadius)
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) ≤ coulombCost (x, (y, z)) ∧
    (ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) = coulombCost (x, (y, z)) ↔
      x = C.charts.central y ∧ z = C.charts.opposite y) := by
  have hsrc : y ∈ C.charts.central.source := by rw [C.source_ball]; exact hy
  have hst : (x, z) ∈ C.charts.stateDomain := by
    rw [C.state_ball, Metric.mem_ball, Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp hx) (Metric.mem_ball.mp hz)
  have hsup := C.supporting y hsrc (x, z) hst
  have hcon := C.contact y hsrc (x, z) hst
  rw [dist_eq_norm] at hxy hxz hyz
  have hzy : 0 < ‖z - y‖ := by rw [norm_sub_rev]; exact hyz
  set R : ℝ := ‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖z - y‖⁻¹ with hRdef
  have hRpos : 0 < R := by positivity
  have hR : coulombCost (x, (y, z)) = ENNReal.ofReal R := by
    simp only [coulombCost, invDistance, tripleFst, tripleSnd, tripleThd]
    rw [hRdef, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_inv_of_pos hxy, ENNReal.ofReal_inv_of_pos hxz, norm_sub_rev y z,
      ENNReal.ofReal_inv_of_pos hzy]
  have hF : jointPotential a (y, (x, z)) = R - ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) -
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2) := by
    simp only [jointPotential, statePotential, CoulombCalculus.pairCost, hRdef]
  rw [hF] at hsup hcon
  rw [hR]
  refine ⟨ENNReal.ofReal_le_ofReal (by linarith), ?_⟩
  constructor
  · intro h
    have hL : 0 ≤ ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
        ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2) := by
      by_contra hneg
      rw [ENNReal.ofReal_of_nonpos (not_le.mp hneg).le] at h
      exact (ENNReal.ofReal_pos.mpr hRpos).ne h
    rw [ENNReal.ofReal_eq_ofReal_iff hL hRpos.le] at h
    have := hcon.mp (by linarith)
    exact Prod.mk.injEq _ _ _ _ ▸ this
  · rintro ⟨rfl, rfl⟩
    have := hcon.mpr rfl
    congr 1
    linarith


theorem h41_sep {x y c c' : E3} {r r' : ℝ} (hx : x ∈ ball c r) (hy : y ∈ ball c' r')
    (h : r + r' ≤ dist c c') : 0 < dist x y := by
  rw [Metric.mem_ball] at hx hy
  have := dist_triangle4 c x y c'
  rw [dist_comm c x] at this
  linarith

theorem h41_pt_dist (a b : Fin 5) (h : a ≠ b) : 1 ≤ dist (point a) (point b) := by
  rw [dist_eq_norm]
  fin_cases a <;> fin_cases b <;> simp [point, EuclideanSpace.norm_eq, Fin.sum_univ_three] at h ⊢ <;>
    norm_num [Real.le_sqrt]

theorem h41_p2' : point 2 = -point 1 := by
  ext i; fin_cases i <;> simp [point]

theorem h41_p4' : point 4 = -point 3 := by
  ext i; fin_cases i <;> simp [point]

theorem h41_p0' : point 0 = 0 := by
  ext i; fin_cases i <;> simp [point]

theorem h41_canon
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ W : Fin 5 → Set E3,
      (∀ i, W i ∈ nhds (point i)) ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 1 2 ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 3 4 := by
  set r0 := min (min C₁.stateRadius C₂.stateRadius) (1 / 3 : ℝ) with hr0
  set r1 := min C₁.parameterRadius (1 / 3 : ℝ) with hr1
  set r2 := min C₁.stateRadius (1 / 3 : ℝ) with hr2
  set r3 := min C₂.parameterRadius (1 / 3 : ℝ) with hr3
  set r4 := min C₂.stateRadius (1 / 3 : ℝ) with hr4
  have p0 : 0 < r0 := lt_min (lt_min C₁.stateRadius_pos C₂.stateRadius_pos) (by norm_num)
  have p1 : 0 < r1 := lt_min C₁.parameterRadius_pos (by norm_num)
  have p2 : 0 < r2 := lt_min C₁.stateRadius_pos (by norm_num)
  have p3 : 0 < r3 := lt_min C₂.parameterRadius_pos (by norm_num)
  have p4 : 0 < r4 := lt_min C₂.stateRadius_pos (by norm_num)
  have l0 : r0 ≤ 1 / 3 := min_le_right _ _
  have l1 : r1 ≤ 1 / 3 := min_le_right _ _
  have l2 : r2 ≤ 1 / 3 := min_le_right _ _
  have l3 : r3 ≤ 1 / 3 := min_le_right _ _
  have l4 : r4 ≤ 1 / 3 := min_le_right _ _
  have d01 := h41_pt_dist 0 1 (by decide)
  have d02 := h41_pt_dist 0 2 (by decide)
  have d12 := h41_pt_dist 1 2 (by decide)
  have d03 := h41_pt_dist 0 3 (by decide)
  have d04 := h41_pt_dist 0 4 (by decide)
  have d34 := h41_pt_dist 3 4 (by decide)
  refine ⟨![ball (point 0) r0, ball (point 1) r1, ball (point 2) r2, ball (point 3) r3,
    ball (point 4) r4], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ball_mem_nhds _ p0
    · exact ball_mem_nhds _ p1
    · exact ball_mem_nhds _ p2
    · exact ball_mem_nhds _ p3
    · exact ball_mem_nhds _ p4
  · intro x hx y hy z hz
    change x ∈ ball (point 0) r0 at hx
    change y ∈ ball (point 1) r1 at hy
    change z ∈ ball (point 2) r2 at hz
    have hxy := h41_sep hx hy (by linarith)
    have hxz := h41_sep hx hz (by linarith)
    have hyz := h41_sep hy hz (by linarith)
    have hy' : y ∈ ball (point 1) C₁.parameterRadius := Metric.ball_subset_ball (min_le_left _ _) hy
    have hx' : x ∈ ball (0 : E3) C₁.stateRadius := by
      have := Metric.ball_subset_ball (x := point 0) ((min_le_left _ _).trans (min_le_left _ _)) hx
      rwa [h41_p0'] at this
    have hz' : z ∈ ball (-point 1) C₁.stateRadius := by
      have := Metric.ball_subset_ball (min_le_left _ _) hz
      rwa [h41_p2'] at this
    have H := h41_elc C₁ hy' hx' hz' hxy hxz hyz
    refine ⟨H.1, fun he => ?_⟩
    obtain ⟨e1, e2⟩ := H.2.mp he
    refine Or.inl ⟨y, ?_, ?_⟩
    · rw [C₁.source_ball]; exact hy'
    · rw [e1, e2]
  · intro x hx y hy z hz
    change x ∈ ball (point 0) r0 at hx
    change y ∈ ball (point 3) r3 at hy
    change z ∈ ball (point 4) r4 at hz
    have hxy := h41_sep hx hy (by linarith)
    have hxz := h41_sep hx hz (by linarith)
    have hyz := h41_sep hy hz (by linarith)
    have hy' : y ∈ ball (point 3) C₂.parameterRadius := Metric.ball_subset_ball (min_le_left _ _) hy
    have hx' : x ∈ ball (0 : E3) C₂.stateRadius := by
      have := Metric.ball_subset_ball (x := point 0) ((min_le_left _ _).trans (min_le_right _ _)) hx
      rwa [h41_p0'] at this
    have hz' : z ∈ ball (-point 3) C₂.stateRadius := by
      have := Metric.ball_subset_ball (min_le_left _ _) hz
      rwa [h41_p4'] at this
    have H := h41_elc C₂ hy' hx' hz' hxy hxz hyz
    refine ⟨H.1, fun he => ?_⟩
    obtain ⟨e1, e2⟩ := H.2.mp he
    refine Or.inr ⟨y, ?_, ?_⟩
    · rw [C₂.source_ball]; exact hy'
    · rw [e1, e2]

theorem solution
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (point i) r
      let u := ComponentPotential.glue U (potentials C₁ C₂)
      (∀ i, U i ⊆ domains C₁ C₂ i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          branchContact C₁ C₂ (x, (y, z)))) := by
  classical
  have hV : ∀ i, IsOpen (domains C₁ C₂ i) := by
    intro i
    fin_cases i
    · exact isOpen_univ
    · exact C₁.charts.central.open_source
    · exact isOpen_univ
    · exact C₂.charts.central.open_source
    · exact isOpen_univ
  have hpV : ∀ i, point i ∈ domains C₁ C₂ i := by
    intro i
    fin_cases i
    · exact Set.mem_univ _
    · exact C₁.charts.point_mem
    · exact Set.mem_univ _
    · exact C₂.charts.point_mem
    · exact Set.mem_univ _
  have hv : ∀ i, ContinuousOn (potentials C₁ C₂ i) (domains C₁ C₂ i) := by
    intro i
    fin_cases i
    · exact (show Continuous (fun x : E3 => (5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) by fun_prop).continuousOn
    · exact C₁.value_analytic.continuousOn
    · exact (show Continuous (fun z : E3 => (5 : ℝ) / 4 * ⟪point 1, z + point 1⟫_ℝ - 10 * ‖z + point 1‖ ^ 2) by fun_prop).continuousOn
    · exact C₂.value_analytic.continuousOn
    · exact (show Continuous (fun z : E3 => (5 : ℝ) / 4 * ⟪point 3, z + point 3⟫_ℝ - 10 * ‖z + point 3‖ ^ 2) by fun_prop).continuousOn
  have hinj : Function.Injective point := by
    intro a b h
    by_contra hab
    have := h41_pt_dist a b hab
    rw [h, dist_self] at this
    linarith
  obtain ⟨W, hW, h012, h034⟩ := h41_canon C₁ C₂
  have hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      branchContact C₁ C₂ (x, (y, z)) → branchContact C₁ C₂ (a, (b, c)) := by
    intro x y z a b c hp h
    rcases h with ⟨w, hw, hq⟩ | ⟨w, hw, hq⟩
    · exact Or.inl ⟨w, hw, hp.symm.trans hq⟩
    · exact Or.inr ⟨w, hw, hp.symm.trans hq⟩
  exact h41_gccf point hinj (domains C₁ C₂) hV hpV (potentials C₁ C₂) hv
    (fun a => Good a.1 a.2.1 a.2.2) (branchContact C₁ C₂)
    (fun a ha => by
      have hc := h41_cog hperm h012 h034 a.1 a.2.1 a.2.2 ha
      filter_upwards [prod_mem_nhds (hW a.1) (prod_mem_nhds (hW a.2.1) (hW a.2.2))] with t ht
      exact hc t.1 ht.1 t.2.1 ht.2.1 t.2.2 ht.2.2)
    (fun a ha => h41_scg C₁ C₂ _ _ _ ha)

