-- Prove2me | solution 1 for GlobalTheory.EllipticPoles.no_pole_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:51.185571+00:00
-- url     : https://prove2.me/submissions/ce13607e-2f0e-47ed-883e-9041fbf97367

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAnalyticOfTendsto
import Theorems.Thm_GlobalTheory_EllipticPoles_tendsto_neg_ne
import Theorems.Thm_GlobalTheory_EllipticPoles_tendsto_add_ne
import Theorems.Thm_GlobalTheory_EllipticPoles_tendsto_two_ne
import Theorems.Thm_GlobalTheory_EllipticPoles_exists_analytic_of_tendsto
import Theorems.Thm_GlobalTheory_EllipticPoles_even_case
import Theorems.Thm_GlobalTheory_derivWeierstrassP_eq_zero_iff
import Theorems.Thm_GlobalTheory_eventually_ne_notMem_periodLattice
import Theorems.Thm_GlobalTheory_hasDerivAt_derivWeierstrassP
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
import Theorems.Thm_GlobalTheory_weierstrassP_second_ne_zero
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
theorem _root_.solution {g : ℂ → ℂ} (hg : Meromorphic g)
    (hd : ∀ a ∉ L.lattice, ∃ c, Tendsto g (𝓝[≠] a) (𝓝 c))
    (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z) :
    ∃ A B : Polynomial ℂ, ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀,
      g z = A.eval (℘[L] z) + B.eval (℘[L] z) * ℘'[L] z := by
  have hgn : Meromorphic fun z ↦ g (-z) := fun a ↦
    MeromorphicAt.comp_analyticAt (f := g) (g := fun z ↦ -z) (hg (-a)) (by fun_prop)
  have hdn : ∀ a ∉ L.lattice, ∃ c, Tendsto (fun z ↦ g (-z)) (𝓝[≠] a) (𝓝 c) := fun a ha ↦ by
    obtain ⟨c, hc⟩ := hd (-a) (by simpa using ha)
    exact ⟨c, hc.comp (tendsto_neg_ne a)⟩
  have hpn : ∀ z, ∀ l ∈ L.lattice, g (-(z + l)) = g (-z) := fun z l hl ↦ by
    rw [neg_add, hp _ _ (neg_mem hl)]
  obtain ⟨A, hA⟩ := even_case L (g := fun z ↦ (g z + g (-z)) / 2)
    (fun a ↦ by have := hg a; have := hgn a; fun_prop)
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨c', hc'⟩ := hdn a ha
      exact ⟨_, (hc.add hc').div_const 2⟩)
    (fun z l hl ↦ by simp only [hp z l hl, hpn z l hl])
    (fun z ↦ by simp only [neg_neg, add_comm])
  let o : ℂ → ℂ := fun z ↦ (g z - g (-z)) / 2
  have ho : Meromorphic o := fun a ↦ by have := hg a; have := hgn a; fun_prop
  have hop : ∀ z, ∀ l ∈ L.lattice, o (z + l) = o z := fun z l hl ↦ by
    simp only [o, hp z l hl, hpn z l hl]
  have hon : ∀ z, o (-z) = -o z := fun z ↦ by simp only [o, neg_neg]; ring
  obtain ⟨B, hB⟩ := even_case L (g := fun z ↦ o z / ℘'[L] z)
    (fun a ↦ (ho a).div (L.meromorphic_derivWeierstrassP a))
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨c', hc'⟩ := hdn a ha
      have h1 : Tendsto o (𝓝[≠] a) (𝓝 ((c - c') / 2)) := (hc.sub hc').div_const 2
      have hP := hasDerivAt_derivWeierstrassP L ha
      by_cases h0 : ℘'[L] a = 0
      · have h2 := (derivWeierstrassP_eq_zero_iff L ha).1 h0
        obtain ⟨h, hh, hoh⟩ := exists_analytic_of_tendsto (ho a) h1
        have h3 : Tendsto o (𝓝[≠] a) (𝓝 (h a)) :=
          (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hoh.symm
        have h4 : Tendsto (fun z : ℂ ↦ -z + (a + a)) (𝓝[≠] a) (𝓝[≠] a) := by
          have := (tendsto_add_ne (-a) (a + a)).comp (tendsto_neg_ne a)
          simpa [Function.comp_def] using this
        have h5 : Tendsto o (𝓝[≠] a) (𝓝 (-h a)) :=
          (h3.comp h4).neg.congr fun z ↦ by simp [hop _ _ h2, hon]
        have h6 : h a = 0 := CharZero.eq_neg_self_iff.1 (tendsto_nhds_unique h3 h5)
        refine ⟨_, ((hasDerivAt_iff_tendsto_slope.1 hh.differentiableAt.hasDerivAt).div
          (hasDerivAt_iff_tendsto_slope.1 hP) (weierstrassP_second_ne_zero L ha h0)).congr' ?_⟩
        filter_upwards [hoh, self_mem_nhdsWithin] with z hz hza
        have : z - a ≠ 0 := sub_ne_zero.2 hza
        simp only [Pi.div_apply, slope_def_field, h6, h0, sub_zero, hz]
        rw [div_div_div_cancel_right₀ this]
      · exact ⟨_, h1.div (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h0⟩)
    (fun z l hl ↦ by simp only [hop z l hl, L.derivWeierstrassP_add_coe z ⟨l, hl⟩])
    (fun z ↦ by simp only [hon, derivWeierstrassP_neg, neg_div_neg_eq])
  refine ⟨A, B, fun z₀ ↦ ?_⟩
  filter_upwards [hA z₀, hB z₀,
    (tendsto_two_ne z₀).eventually (eventually_ne_notMem_periodLattice L (z₀ + z₀))]
    with z h1 h2 h3
  have h4 : ℘'[L] z ≠ 0 := fun h ↦
    h3 ((derivWeierstrassP_eq_zero_iff L fun hz ↦ h3 (add_mem hz hz)).1 h)
  rw [← h1, ← h2, div_mul_cancel₀ _ h4]
  simp only [o]
  ring
end GlobalTheory.EllipticPoles
