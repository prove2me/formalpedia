-- Prove2me | solution 1 for GlobalTheory.EllipticPoles.exists_mul_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:43:17.417939+00:00
-- url     : https://prove2.me/submissions/367e532e-6945-4f98-8544-d48838b612c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAnalyticOfTendsto
import Theorems.Thm_GlobalTheory_EllipticPoles_tendsto_add_ne
import Theorems.Thm_GlobalTheory_EllipticPoles_no_pole_case
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.EllipticPoles
variable (L : PeriodPair)
namespace GlobalTheory.EllipticPoles
theorem _root_.solution (L : PeriodPair) (φ : ℂ → ℂ) (hφ : GlobalTheory.MomOne.Ell L φ) :
    ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ),
      (∀ i, P i ∉ L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧
      ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, φ z * ∏ i, (L.weierstrassP z - L.weierstrassP (P i)) =
        A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
  classical
  obtain ⟨hf, hp⟩ := hφ
  have hK := (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure
  set K := closure (ZSpan.fundamentalDomain L.basis)
  have hS := hK.finite_sdiff_of_mem_codiscreteWithin
    (hf.meromorphicOn (s := K)).analyticAt_mem_codiscreteWithin
  let S : Finset ℂ := hS.toFinset.filter fun a ↦ a ∉ L.lattice ∧ meromorphicOrderAt φ a < 0
  choose n hn using id hf
  let e := Fintype.equivFin (Σ a : S, Fin (n a))
  let D : ℂ → ℂ := fun z ↦ ∏ a ∈ S, (℘[L] z - ℘[L] a) ^ n a
  have hD : ∀ z, ∏ i, (℘[L] z - ℘[L] (e.symm i).1) = D z := fun z ↦ by
    rw [e.symm.prod_comp (fun x : (Σ a : S, Fin (n a)) ↦ ℘[L] z - ℘[L] x.1), Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Finset.prod_coe_sort S fun a ↦ (℘[L] z - ℘[L] a) ^ n a
  have hK' : ∀ a ∈ K, a ∉ L.lattice → ∃ c, Tendsto (fun z ↦ φ z * D z) (𝓝[≠] a) (𝓝 c) := by
    intro a haK ha
    have hP := L.analyticOnNhd_weierstrassP a ha
    have hP' := hP.continuousAt
    by_cases haS : a ∈ S
    · obtain ⟨u, hu, hu'⟩ := (natCast_le_analyticOrderAt (f := fun z ↦ ℘[L] z - ℘[L] a)
        (z₀ := a) (by fun_prop) (n := 1)).mp
        ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (by fun_prop)).mpr fun i hi ↦ by
          interval_cases i; simp)
      have h1 := (hn a).continuousAt
      have h2 := hu.continuousAt
      have h3 : ContinuousAt (fun z ↦ ((z - a) ^ n a • φ z) * u z ^ n a *
          ∏ b ∈ S.erase a, (℘[L] z - ℘[L] b) ^ n b) a := by fun_prop
      refine ⟨_, (h3.tendsto.congr' ?_).mono_left nhdsWithin_le_nhds⟩
      filter_upwards [hu'] with z hz
      simp only [D]
      rw [← Finset.mul_prod_erase _ _ haS, hz]
      simp only [smul_eq_mul, mul_pow]
      ring
    · have h1 : 0 ≤ meromorphicOrderAt φ a := by
        by_contra h
        refine haS (Finset.mem_filter.2 ⟨?_, ha, not_le.1 h⟩)
        simp only [Set.Finite.mem_toFinset]
        exact ⟨haK, fun h' ↦ h (AnalyticAt.meromorphicOrderAt_nonneg h')⟩
      obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf a)).2 h1
      have h2 : ContinuousAt D a := by simp only [D]; fun_prop
      exact ⟨_, hc.mul (h2.tendsto.mono_left nhdsWithin_le_nhds)⟩
  have hper : ∀ z, ∀ l ∈ L.lattice, φ (z + l) * D (z + l) = φ z * D z := fun z l hl ↦ by
    simp only [D, hp l hl z, L.weierstrassP_add_coe z ⟨l, hl⟩]
  obtain ⟨A, B, hAB⟩ := no_pole_case L (g := fun z ↦ φ z * D z)
    (fun a ↦ by
      have h1 := hf a
      have h2 := L.meromorphic_weierstrassP a
      simp only [D]
      fun_prop)
    (fun z hz ↦ by
      have hl : -(ZSpan.floor L.basis z : ℂ) ∈ L.lattice := by
        rw [L.lattice_eq_span_range_basis]; exact neg_mem (ZSpan.floor L.basis z).2
      obtain ⟨c, hc⟩ := hK' (z + -ZSpan.floor L.basis z)
        (by rw [← sub_eq_add_neg]; exact subset_closure (ZSpan.fract_mem_fundamentalDomain L.basis z))
        (by rwa [L.lattice.add_mem_iff_left hl])
      exact ⟨c, (hc.comp (tendsto_add_ne z _)).congr fun w ↦ hper w _ hl⟩)
    hper
  refine ⟨_, fun i ↦ (e.symm i).1, A, B, fun i ↦ (Finset.mem_filter.1 (e.symm i).1.2).2, fun z₀ ↦ ?_⟩
  simpa only [hD] using hAB z₀
end GlobalTheory.EllipticPoles
