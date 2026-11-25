-- Prove2me | solution 1 for GlobalTheory.CechDR.cmpO_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:08:16.745351+00:00
-- url     : https://prove2.me/submissions/ee8b30f3-8994-43ce-b605-5bbf8814daa3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsSpecFromPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocycleLocalSectionsRestrictCompatiblyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGluedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafComparisonInjective
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_T_cochainValueOnThickeningHom_eq_sub_of_glued
import Theorems.Thm_GlobalTheory_T_cocycle_local_sections_restrict_compatibly
import Theorems.Thm_GlobalTheory_T_exists_glue_functions_spec_from_pairs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    Function.Injective (cmpO s) := by
  intro R _ X s
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
  have hg' : ∀ ⦃U V : AffOp X⦄ (a : U ⟶ V),
      g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a) :=
    fun U V a ↦ congrFun (congrFun (congrFun hg U) V) a
  have ex : ∀ T : TT s, ∃ G : T.obj.B, ∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p :=
    fun T ↦ GlobalTheory.T.exists_glue_functions_spec_from_pairs T.obj.B (pt T) (hSec f g T) fun p q hpq ↦ GlobalTheory.T.cocycle_local_sections_restrict_compatibly f g hg' T p q hpq
  choose G hG using ex
  exact H1.mk_eq_zero.2 ⟨G, funext fun T ↦ funext fun T' ↦ funext fun φ ↦
    (GlobalTheory.T.cochainValueOnThickeningHom_eq_sub_of_glued f g hg' φ (G T) (G T') (hG T) (hG T')).symm⟩
end GlobalTheory.CechDR
