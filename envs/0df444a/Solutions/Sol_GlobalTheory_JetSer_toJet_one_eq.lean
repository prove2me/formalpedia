-- Prove2me | solution 1 for GlobalTheory.JetSer.toJet_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:24:52.567086+00:00
-- url     : https://prove2.me/submissions/29637450-80d5-44c8-a6f7-36b43b58ad16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DualNumberValueToJet
import Theorems.Thm_GlobalTheory_JetSer_toJet_eq_mk_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution {O κ : Type} [CommRing O] [Fintype κ] (u : MvPowerSeries κ O) :
    toJet 1 u = Ideal.Quotient.mk _ (MvPolynomial.C (constantCoeff u) +
      ∑ q, MvPolynomial.C (coeff (Finsupp.single q 1) u) * MvPolynomial.X q) := by
  classical
  refine (toJet_eq_mk_iff 1 u _).2 fun a ha => ?_
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C, MvPolynomial.coeff_X]
  by_cases h0 : Finsupp.degree a = 0
  · rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    simp [Finsupp.single_eq_zero]
  · have h1 : a ∈ {d : κ →₀ ℕ | Finsupp.degree d = 1} := by
      show Finsupp.degree a = 1
      omega
    rw [← Finsupp.range_single_one] at h1
    obtain ⟨q, rfl⟩ := h1
    rw [if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_add, Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      rwa [Finsupp.single_left_inj one_ne_zero]
    · simp
end GlobalTheory.JetSer
