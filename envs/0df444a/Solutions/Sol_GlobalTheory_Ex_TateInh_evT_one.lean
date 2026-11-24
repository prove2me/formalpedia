-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.evT_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:32:24.724803+00:00
-- url     : https://prove2.me/submissions/3276d435-95fe-4632-bd87-6fed3bf429fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh
open scoped BigOperators
variable {O : Type} [CommRing O]
namespace GlobalTheory.Ex.TateInh
namespace _root_.GlobalTheory.Ex.TateInh
theorem _root_.solution (N : _root_.GlobalTheory.Ex.NumD O) (m : ℕ)
    (p : N.QT (m ^ 2)) (χ : N.X) :
    N.evT m p 1 χ = N.txT m p χ := by
  unfold _root_.GlobalTheory.Ex.NumD.evT
    _root_.GlobalTheory.Ex.NumD.txT
  simp only [_root_.GlobalTheory.Ex.NumD.Gt.generator_inv_base,
    _root_.GlobalTheory.Ex.NumD.Gt.one_b, one_mul, N.cub.N_one]
end _root_.GlobalTheory.Ex.TateInh
end GlobalTheory.Ex.TateInh
