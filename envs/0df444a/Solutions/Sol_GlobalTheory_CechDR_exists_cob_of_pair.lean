-- Prove2me | solution 1 for GlobalTheory.CechDR.exists_cob_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:23:30.799177+00:00
-- url     : https://prove2.me/submissions/7e925661-9a0a-4f75-92a4-6fee21492e56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormEqZeroOfVanishingOnPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffinePairRestrictionInjectiveFirstCohomology
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_sec_eq_of_pair
import Theorems.Thm_GlobalTheory_T_exists_glue_functions_affineOpen_from_pairs


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
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR
open Opposite KaehlerDifferential
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}
namespace GlobalTheory.CechDR
theorem _root_.solution (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (f : Z1 (OAff s'))
    (g : ∀ p : Pair φ, (OAff s').obj (op p.1.1))
    (hg : ∀ (p q : Pair φ) (hqp : q ≤ p), f.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
      g q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g p)) :
    ∃ G : C0 (OAff s'), d0 (OAff s') G = f.1 ∧ ∀ (W : X'.affineOpens) (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op (G (op W)) = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
  have ex : ∀ W : X'.affineOpens, ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op G = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
    intro W
    refine GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs φ s' W _ fun p q hp hq hqp ↦ ?_
    have e := Z1.comp f (homOfLE hp).op (homOfLE (Pair.le_fst hqp)).op
    rw [show (homOfLE hp).op ≫ (homOfLE (Pair.le_fst hqp)).op = (homOfLE hq).op from rfl, hg p q hqp] at e
    rw [map_sub, e]
    ring
  choose G hG using ex
  refine ⟨fun T ↦ G T.unop, ?_, hG⟩
  funext T T' a
  refine sec_eq_of_pair φ s' T'.unop _ _ fun p hp ↦ ?_
  have e1 := Z1.comp f a (homOfLE hp).op
  have e2 : a ≫ (homOfLE hp).op = (homOfLE (hp.trans (leOfHom a.unop))).op := rfl
  rw [e2] at e1
  rw [amitsur_d0_apply, map_sub, ← mp_comp, e2, hG, hG]
  linear_combination e1
end GlobalTheory.CechDR
