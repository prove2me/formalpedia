-- Prove2me | solution 1 for GlobalTheory.ActLimit.tendsToCoeffwise_germEvalTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:11:29.852658+00:00
-- url     : https://prove2.me/submissions/e1d9a0c7-74c8-41de-9abe-76171513fc56

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_const
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActLimit
variable {C : Type} [Field C] {V : VF C}
variable {dd : ℕ}
namespace GlobalTheory.ActLimit
theorem _root_.solution {n : ℕ} {a b : ℕ → Pt C n dd} {a' b' : Pt C n dd}
    (ha : ∀ k i, MvPowerSeries.constantCoeff (a k i) = 0) (hb : ∀ k i, MvPowerSeries.constantCoeff (b k i) = 0)
    (ha' : ∀ i, TendsS V (fun k => a k i) (a' i)) (hb' : ∀ i, TendsS V (fun k => b k i) (b' i)) (f : PS C 2 dd) :
    TendsS V (fun k => ev ![a k, b k] f) (ev ![a', b'] f) :=
  TendsS.subst (a := fun k (p : Fin 2 × Fin dd) => ![a k, b k] p.1 p.2)
    (fun k p => by obtain ⟨j, i⟩ := p; fin_cases j; exacts [ha k i, hb k i])
    (fun p => by obtain ⟨j, i⟩ := p; fin_cases j; exacts [ha' i, hb' i]) (TendsS.const f)
end GlobalTheory.ActLimit
