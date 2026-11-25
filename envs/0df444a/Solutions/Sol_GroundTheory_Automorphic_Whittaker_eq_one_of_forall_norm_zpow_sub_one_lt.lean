-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.eq_one_of_forall_norm_zpow_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:07.507554+00:00
-- url     : https://prove2.me/submissions/7290ca94-e7aa-41d2-96b9-2cc3226fb8d1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_P2M_GroundTheory_Variant__N1_eq_one_of_forall_norm_zpow_sub_one_lt_cdf30090e0e9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {z : ℂ} (h : ∀ m : ℤ, ‖z ^ m - 1‖ < 1) : z = 1 :=
  _root_.GroundTheory.Variant₂.N1.eq_one_of_forall_norm_zpow_sub_one_lt h
end GroundTheory.Automorphic.Whittaker
