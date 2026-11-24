-- Prove2me | solution 1 for GlobalTheory.CechDR.pairRes_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:38:51.251479+00:00
-- url     : https://prove2.me/submissions/3de7779a-1aa2-4e50-898d-c2ae3d465d2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormEqZeroOfVanishingOnPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffinePairRestrictionInjectiveFirstCohomology
import Theorems.Thm_GlobalTheory_CechDR_exists_cob_of_pair
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamCoefMapOneForms_restrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_pullHyp1_mk
import Theorems.Thm_GlobalTheory_T_oneForm_eq_zero_of_vanishing_on_pairs


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
namespace GlobalTheory.CechDR
theorem _root_.solution : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧
      Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by
  intro R' _ X X' φ s'
  refine ⟨?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    obtain ⟨G, hG, -⟩ := exists_cob_of_pair φ s' f (fun p ↦ g (op p)) fun p q hqp ↦
      (congrFun (congrFun (congrFun hg (op p)) (op q)) (homOfLE hqp).op).symm
    exact H1.mk_eq_zero.2 ⟨G, hG⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    have h0 : ∀ p : Pair φ, ω.1 (op p.1.1) = 0 := fun p ↦
      (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) (op p) _).symm.trans
        (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 (op p)) hω)
    refine Subtype.ext (funext fun W ↦ GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop _ fun p hp ↦ ?_)
    rw [← ω.2 (homOfLE hp).op]
    exact h0 p
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := Hyp1.mk_surjective _ c
    rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let g' : ∀ p : Pair φ, (OAff s').obj (op p.1.1) := fun p ↦ g (op p)
    have hf : ∀ (p q : Pair φ) (hqp : q ≤ p), z.1.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
        g' q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g' p) := fun p q hqp ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.1 (op p) (op q) (homOfLE hqp).op) hg).symm
    have hω : ∀ p : Pair φ, D R' _ (g' p) = z.1.2 (op p.1.1) := fun p ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.2 (op p)) hg).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor _ _ _ _)
    obtain ⟨G, hG, hGp⟩ := exists_cob_of_pair φ s' (cechDeRhamTotalCocyclesOne.fn _ z) g' hf
    refine Hyp1.mk_eq_zero.2 ⟨G, Tot1.ext (fun T T' a ↦ congrFun (congrFun (congrFun hG T) T') a)
      fun W ↦ ?_⟩
    refine (sub_eq_zero.1 (GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop (D R' _ (G W) - z.1.2 W) fun p hp ↦ ?_))
    have e := cechDeRhamTotalCocyclesOne.conn z (homOfLE hp).op
    rw [map_sub, p1_D, hGp, map_sub, hω]
    change _ - (p1 _ _ _) = _
    rw [e, show ((cechDeRhamTotalCocyclesOne.fn (OAff s') z : Z1 (OAff s')) : C1 (OAff s')) = z.1.1 from rfl]
    abel
end GlobalTheory.CechDR
