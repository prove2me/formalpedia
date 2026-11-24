-- Prove2me | solution 1 for GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:14:50.905814+00:00
-- url     : https://prove2.me/submissions/bf7ac391-0909-4c65-990f-e590289b6b45

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantValueCopiesEqZeroOfLowCoeff
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_coeff_mul_congr
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_constantCoeff_DmonN_congr
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_constantCoeff_DpolyN_eq
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_isLinearMap_DmonN


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.PowGerm
namespace GlobalTheory.PowGerm
theorem _root_.solution :
    ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u f P hf
  classical
  unfold nabValN
  rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hdeg : a.degree ≤ P.totalDegree := by
    have := MvPolynomial.le_totalDegree ha
    rwa [Finsupp.degree_apply]
  rw [NabJet.constantCoeff_DmonN_congr _ cp u a _ 0 fun mo hmo => ?_,
    (NabJet.isLinearMap_DmonN (B.FK K) cp u a).map_zero, map_zero, mul_zero]
  rw [NabJet.coeff_mul_congr P.totalDegree f 0 _ (fun b hb => by rw [hf b hb, map_zero]) mo (hmo.trans hdeg), zero_mul]
end GlobalTheory.PowGerm
