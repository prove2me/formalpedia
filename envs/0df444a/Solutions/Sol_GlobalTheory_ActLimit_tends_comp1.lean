-- Prove2me | solution 1 for GlobalTheory.ActLimit.tends_comp1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:19:57.735797+00:00
-- url     : https://prove2.me/submissions/9c163425-372b-4ea2-98fe-9e72c986293c

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
theorem _root_.solution {n : ℕ} {φ : ℕ → Pt C 1 dd} {e : Pt C 1 dd} (h : ∀ i, TendsS V (fun k => φ k i) (e i))
    {a : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    TendsS V (fun k => comp1 (φ k) a i) (comp1 e a i) :=
  TendsS.subst (a := fun _ (p : Fin 1 × Fin dd) => ![a] p.1 p.2)
    (fun _ p => by obtain ⟨j, i⟩ := p; fin_cases j; exact ha i) (fun _ => TendsS.const _) (h i)
end GlobalTheory.ActLimit
