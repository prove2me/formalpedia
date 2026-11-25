-- Prove2me | solution 1 for GlobalTheory.JetSer.dualNumber_value_toJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:42.886912+00:00
-- url     : https://prove2.me/submissions/03f0c242-9dc6-4691-9359-c1de51e6962c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DualNumberValueToJet
import Theorems.Thm_GlobalTheory_JetSer_toJet_one_eq
import Theorems.Thm_GlobalTheory_JetSer_constantCoeff_dof

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
theorem _root_.solution : ∀ (R O : Type) [CommRing R] [CommRing O] (f : R →+* O) (d : ℕ) (G : FGLaw R d) (e : Fin d → O) (u : PS O 1 d) (S : Type) [CommRing S] [Algebra O S] (ψ : JetR O (Fin 1 × Fin d) 1 →ₐ[O] DualNumber S), (∀ q, ψ (zR 1 q) = TrivSqZeroExt.inr (algebraMap O S (e q.2))) → ψ (toJet 1 u) = TrivSqZeroExt.inl (algebraMap O S (MvPowerSeries.constantCoeff u)) + TrivSqZeroExt.inr (algebraMap O S (MvPowerSeries.constantCoeff (Dof (G.mapF f) e u))) := by
  intro R O _ _ f d G e u S _ _ ψ hψ
  have hC : ∀ c : O, ψ (Ideal.Quotient.mk _ (MvPolynomial.C c)) = TrivSqZeroExt.inl (algebraMap O S c) :=
    fun c => ψ.commutes c
  have hX : ∀ q, ψ (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
      TrivSqZeroExt.inr (algebraMap O S (e q.2)) := hψ
  rw [toJet_one_eq, constantCoeff_dof]
  simp only [map_add, map_sum, map_mul, hC, hX, Fintype.sum_prod_type, Fin.sum_univ_one]
  congr 1
  ext
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, mul_comm]
    simp only [Algebra.smul_def]
end GlobalTheory.JetSer
