-- Prove2me | solution 1 for GlobalTheory.TeichSeq.root_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:24:31.497805+00:00
-- url     : https://prove2.me/submissions/763c1ddc-d4fc-4378-a2d6-7b9e7e55ca4f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqOfMapEqOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusLiftEmbeddingsUnit
import Theorems.Thm_GlobalTheory_RootsOfUnityInjective_eq_of_map_eq_of_pow_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.TeichSeq
namespace GlobalTheory.TeichSeq
theorem _root_.solution {R k : Type} [CommRing R] [IsDomain R] [CommRing k] [IsDomain k] (π : R →+* k)
    {N : ℕ} (hN : (N : k) ≠ 0) {u w : R} (hu : u ^ N = 1) (hw : w ^ N = 1) (h : π u = π w) :
    u = w := by
  first
  | (rename_i h_2 h_3 h_4 h_5; revert R k h_2 h_3 h_4 h_5 π N hN u w hu hw h; exact @_root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one)
  | exact @_root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one
  | exact _root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one
  | (apply _root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one ..)
end GlobalTheory.TeichSeq
