-- Prove2me | solution 1 for GlobalTheory.EigenDer.exists_jet_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:51.510005+00:00
-- url     : https://prove2.me/submissions/bee68cc8-0043-4b61-a0cc-db16550f4657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SubstMapAlgebraMap
import Theorems.Thm_GlobalTheory_algHom_sub_aeval_truncTotal_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EigenDer
variable {R : Type} [CommRing R]
namespace GlobalTheory.EigenDer
theorem _root_.solution {κ A : Type} [Finite κ] [CommRing A] [Algebra R A] (T : MvPowerSeries κ R →ₐ[R] A)
    (hT : ∀ p, IsNilpotent (T (X p))) :
    ∃ (n : ℕ) (Θ : JetR R κ (n + 1) →ₐ[R] A), ∀ g, Θ (toJet (n + 1) g) = T g := by
  let J : Ideal A := Ideal.span (Set.range fun p => T (X p))
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have hn : IsNilpotent J := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 (by
    rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    exact hT p)
  obtain ⟨n, hn⟩ := hn
  have hJ : J ^ (n + 1 + 1) = ⊥ := by
    rw [add_assoc, pow_add, hn, zero_mul, Ideal.zero_eq_bot]
  have hm : ∀ p, T (X p) ∈ J := fun p => Ideal.subset_span ⟨p, rfl⟩
  refine ⟨n, jetLift R J hJ (fun p => T (X p)) hm, fun g => ?_⟩
  have h := GlobalTheory.algHom_sub_aeval_truncTotal_mem T hm (n + 1 + 1) g
  rw [hJ, Ideal.mem_bot, sub_eq_zero] at h
  exact h.symm
end GlobalTheory.EigenDer
