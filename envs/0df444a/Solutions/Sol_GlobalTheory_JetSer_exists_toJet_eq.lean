-- Prove2me | solution 1 for GlobalTheory.JetSer.exists_toJet_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:29.601021+00:00
-- url     : https://prove2.me/submissions/b8ead8b0-a60c-4270-831b-91602e6779e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Theorems.Thm_GlobalTheory_JetSer_jet_mk_eq_iff
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}
variable [Finite κ]
namespace GlobalTheory.JetSer
theorem _root_.solution (p : ∀ m, JetR R κ m) (hp : ∀ m, jetTruncR R κ m (p (m + 1)) = p m) :
    ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = p m := by
  choose P hP using fun m => Ideal.Quotient.mk_surjective (p m)
  have h1 : ∀ m (e : κ →₀ ℕ), Finsupp.degree e < m + 1 → (P (m + 1)).coeff e = (P m).coeff e := fun m => by
    rw [← jet_mk_eq_iff, hP m, ← hp m, ← hP (m + 1)]
    rfl
  have h2 : ∀ (e : κ →₀ ℕ) m, Finsupp.degree e ≤ m → (P (Finsupp.degree e)).coeff e = (P m).coeff e := by
    intro e m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [ih, h1 m e (by omega)]
  refine ⟨fun e => (P (Finsupp.degree e)).coeff e, fun m => ?_⟩
  rw [← hP m]
  exact (toJet_eq_mk_iff m _ _).2 fun e he => h2 e m (by omega)
end GlobalTheory.JetSer
