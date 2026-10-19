-- Prove2me | solution 1 for OAI.Problem356.finite_component_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:30:55.040901+00:00
-- url     : https://prove2.me/submissions/0643caf9-7e08-4fcc-8fda-463b0aebd04d

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

theorem solution {ι : Type uIndex} [Fintype ι]
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

