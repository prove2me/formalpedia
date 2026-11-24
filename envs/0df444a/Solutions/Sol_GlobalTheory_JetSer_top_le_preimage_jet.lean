-- Prove2me | solution 1 for GlobalTheory.JetSer.top_le_preimage_jet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:41:26.995915+00:00
-- url     : https://prove2.me/submissions/b9f0fcba-0ebc-4a96-aa30-a145aa0d9657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Theorems.Thm_GlobalTheory_JetSer_top_le_preimage_of_nil
import Theorems.Thm_GlobalTheory_JetSer_jetTruncR_surjective
import Theorems.Thm_GlobalTheory_JetSer_isNilpotent_of_mem_ker_jetTruncR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}
namespace GlobalTheory.JetSer
theorem _root_.solution {X : Scheme.{0}} (p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X)
    (hp : ∀ m, (spMap (jetTruncR R κ m)).left ≫ p (m + 1) = p m) (U : X.Opens) (h : ⊤ ≤ p 0 ⁻¹ᵁ U) (m : ℕ) :
    ⊤ ≤ p m ⁻¹ᵁ U := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [← hp m] at ih
    exact top_le_preimage_of_nil (jetTruncR R κ m).toRingHom (jetTruncR_surjective m)
      (isNilpotent_of_mem_ker_jetTruncR m) _ U ih
end GlobalTheory.JetSer
