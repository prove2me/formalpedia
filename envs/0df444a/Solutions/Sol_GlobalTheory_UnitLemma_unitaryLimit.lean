-- Prove2me | solution 1 for GlobalTheory.UnitLemma.unitaryLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:53:40.986085+00:00
-- url     : https://prove2.me/submissions/a23a8d3d-511e-4bcd-8e96-31cbc3418867

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualStableLatticeUnitOrbitsFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElementsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRhoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UUEqSumOverTorusOrbitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusModIntegralUnitsStructureAndIntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteAlgebraInvolutionRhoPowEqCardBoxStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TendstoRatioBoxCountsProdOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryLatticeCountRatioTendsto
import Theorems.Thm_GlobalTheory_HullClasses_key
import Theorems.Thm_GlobalTheory_T_UU_eq_sum_over_torus_orbits
import Theorems.Thm_GlobalTheory_T_finiteAlgebraInvolution_rho_pow_eq_card_box
import Theorems.Thm_GlobalTheory_T_fullLattice_sandwich_between_integral_elements
import Theorems.Thm_GlobalTheory_T_selfDual_stable_lattice_unit_orbits_finite
import Theorems.Thm_GlobalTheory_T_tendsto_ratio_box_counts_prod_one
import Theorems.Thm_GlobalTheory_T_torus_mod_integralUnits_structure_and_integrality
import Theorems.Thm_GlobalTheory_T_torus_orbit_lattice_count_bounded_by_rho
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution : UnitaryLimit := by
  have L0 := GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite
  have S1 := GlobalTheory.T.fullLattice_sandwich_between_integral_elements
  have S2 := GlobalTheory.T.torus_orbit_lattice_count_bounded_by_rho
  have S3 := GlobalTheory.T.UU_eq_sum_over_torus_orbits
  have S4 := GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality
  have S5 := GlobalTheory.T.finiteAlgebraInvolution_rho_pow_eq_card_box
  have S6 := GlobalTheory.T.tendsto_ratio_box_counts_prod_one

  intro K B hB a ha x hx
  classical
  obtain ⟨r, φ, c, hsurj, hker, hc, hint⟩ := S4 K B hB a ha
  have hrho : ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) :=
    S5 K B a r φ c hsurj hker hint
  have hpos : ∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j) := fun j => by
    rw [hrho]; exact Finset.prod_pos fun i _ => by omega
  obtain ⟨hfin, hstab⟩ := L0 K B hB.2 x hx.1 hx.2
  choose m hm using fun o : Orb K.O B.T (B.X x) => S1 K B hB a ha _ (Quot.out o).2.1
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  set M := Finset.univ.sup m with hMdef
  have hmM : ∀ o, m o ≤ M := fun o => Finset.le_sup (Finset.mem_univ o)
  have key := fun (k : ℕ) (hk : M ≤ k) (o : Orb K.O B.T (B.X x)) =>
    S2 K B _ (hstab _ (Quot.out o).2).1 (hstab _ (Quot.out o).2).2 a hpos M k hk
      (hm o M (hmM o)).1 (hm o M (hmM o)).2
  have hUU : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) =
      ∑ o : Orb K.O B.T (B.X x), (Nat.card {L' : Submodule K.O B.A // (∃ t ∈ B.T, L' = mulLat K.O (t : B.A) (Quot.out o).1) ∧
        algebraMap K.O B.A a ^ k ∈ L'} : ℝ) := by
    intro k hk
    rw [S3 K B x _ hfin (fun o => (key k hk o).1), finsum_eq_sum_of_fintype]
    push_cast; rfl
  have hN : (B.N x : ℝ) = ∑ o : Orb K.O B.T (B.X x),
      (((stabLat K.O (Quot.out o).1 ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℝ) := by
    unfold InvAlg.N orbSum
    rw [finsum_eq_sum_of_fintype]
    push_cast
    simp
  have hlo : ∀ k, M ≤ k → (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) ≤ B.UU x (algebraMap K.O B.A a ^ k) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.1
  have hhi : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) ≤ (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.2
  have hposR : ∀ j, (0 : ℝ) < B.rho (algebraMap K.O B.A a ^ j) := fun j => by exact_mod_cast hpos j
  have hup : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have := (S6 r c M).const_mul (B.N x : ℝ)
    rw [mul_one] at this
    refine this.congr fun k => ?_
    rw [hrho, hrho, mul_div_assoc]
  have hdown : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have h1 := ((S6 r c M).inv₀ one_ne_zero).comp (tendsto_sub_atTop_nat M)
    have h2 := h1.const_mul (B.N x : ℝ)
    rw [inv_one, mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop M] with k hk
    simp only [Function.comp_apply, inv_div]
    rw [Nat.sub_add_cancel hk, hrho, hrho, mul_div_assoc]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hdown hup ?_ ?_
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hlo k hk) (hposR k).le
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hhi k hk) (hposR k).le
end GlobalTheory.UnitLemma
