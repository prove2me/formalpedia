-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SdFin.exists_of_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:35:04.385472+00:00
-- url     : https://prove2.me/submissions/c5a8df93-e729-4262-bb00-1aba76594ebf

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_JR_DualLattice_box_dual
import Theorems.Thm_GlobalTheory_JR_DualLattice_box_eq
import Theorems.Thm_GlobalTheory_JR_DualLattice_box_open_compact
import Theorems.Thm_GlobalTheory_JR_exists_small_dual_lattices
import Theorems.Thm_GlobalTheory_T_self_dual_lattice_filtration_character
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SdFin
open GlobalTheory.JR.DualLattice
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K]
namespace GlobalTheory.CompanionTheory.SdFin
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : GlobalTheory.JR.IsStdChar ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (V : Type) [AddCommGroup V] [Module K V] [Module.Finite K V] [TopologicalSpace V]
    [IsModuleTopology K V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (β : LinearMap.BilinForm K V) (hs : β.IsSymm) (hβ : β.Nondegenerate) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) := by
  classical
  let e := Module.finBasis K V
  let e' := β.dualBasis hβ e
  have hB : ∀ x y, β x y = ∑ i, e.repr x i * e'.repr y i := by
    intro x y
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, hs.eq]
  obtain ⟨t, ht0, ht1⟩ := NormedField.exists_norm_lt_one K
  have htne : t ≠ 0 := norm_pos_iff.1 ht0
  have hz : ∀ k : ℤ, t ^ k ≠ 0 := fun k => zpow_ne_zero k htne
  have hp : ∀ k : ℤ, 0 < ‖t ^ k‖ := fun k => norm_pos_iff.2 (hz k)
  have hp' : ∀ k : ℤ, 0 < ‖(t ^ k)⁻¹‖ := fun k => norm_pos_iff.2 (inv_ne_zero (hz k))
  have hex : ∀ (b : Module.Basis (Fin (Module.finrank K V)) K V) (x : V),
      ∃ n : ℕ, ∀ i, ‖b.repr x i‖ ≤ ‖t‖⁻¹ ^ n := by
    intro b x
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ i, ‖b.repr x i‖) (one_lt_inv₀ ht0 |>.2 ht1)
    exact ⟨n, fun i => (Finset.single_le_sum (f := fun i => ‖b.repr x i‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans hn.le⟩
  refine GlobalTheory.T.self_dual_lattice_filtration_character V _ (fun k => box e ‖t ^ k‖ (norm_nonneg _))
    (fun k => box e' ‖(t ^ k)⁻¹‖ (norm_nonneg _)) (fun x x' y => ?_) (fun x y => ?_) (fun x y => hu _)
    (GlobalTheory.JR.exists_small_dual_lattices K ψ hψ V β hs hβ).1
    (fun k => ⟨(box_open_compact e _ (hp k)).1, (box_open_compact e _ (hp k)).2,
      (box_open_compact e' _ (hp' k)).1, (box_open_compact e' _ (hp' k)).2⟩) ?_ ?_ ?_ ?_
    (fun k y => box_dual hψ e e' (fun x y => β x y) hB (t ^ k) (hz k) y) (fun k x => ?_)
  · simp [AddChar.map_add_eq_mul]
  · rw [hs.eq]
  · intro a b hab x hx i
    refine (hx i).trans ?_
    rw [norm_zpow, norm_zpow]
    exact zpow_le_zpow_right_of_le_one₀ ht0 ht1.le hab
  · intro U hU
    have h0 : (coordHomeo e).symm 0 = 0 := map_zero e.equivFun.symm
    have hU' : (coordHomeo e).symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank K V) → K) :=
      (coordHomeo e).symm.continuous.continuousAt.preimage_mem_nhds (by rwa [h0])
    obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU'
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε ht1
    refine ⟨(n : ℤ), ?_⟩
    rw [box_eq]
    intro x hx
    have h2 : ‖t ^ (n : ℤ)‖ ≤ ε := by simpa using hn.le
    have := hsub (Metric.closedBall_subset_closedBall h2 hx)
    simpa using this
  · intro x
    obtain ⟨n, hn⟩ := hex e x
    refine ⟨-(n : ℤ), fun i => (hn i).trans_eq ?_⟩
    simp [norm_zpow]
  · intro y
    obtain ⟨n, hn⟩ := hex e' y
    refine ⟨(n : ℤ), fun i => (hn i).trans_eq ?_⟩
    simp
  · have := box_dual hψ e' e (fun y x => β x y)
      (fun y x => by simp only [hB, mul_comm]) (t ^ k)⁻¹ (inv_ne_zero (hz k)) x
    simpa only [inv_inv] using this
end GlobalTheory.CompanionTheory.SdFin
