-- Prove2me | solution 1 for GlobalTheory.CechDR.restrict_bijective_one_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:03.556223+00:00
-- url     : https://prove2.me/submissions/f6e52d48-2c18-4f1e-bddb-9f571a570b8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_restrict_pull1_injective_of_sep_glue
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_oneCocycle_vanishing_comma_of_basis
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_comma_of_basis
import Theorems.Thm_GlobalTheory_CatCoh_pull1_restrict_surjective_of_comma
import Theorems.Thm_GlobalTheory_CechDR_FormExt_glue_one_forms
import Theorems.Thm_GlobalTheory_CechDR_form_eq_zero_of_basis_cover
import Theorems.Thm_GlobalTheory_CechDR_hasLoc_OAff
import Theorems.Thm_GlobalTheory_CechDR_pullHyp1_restrict_injective
import Theorems.Thm_GlobalTheory_CechDR_pullHyp1_restrict_surjective
import Theorems.Thm_GlobalTheory_CechDR_twoForm_sep_of_basis
import Theorems.Thm_GlobalTheory_cocycle_one_forms_coboundary_of_restrict
import Theorems.Thm_GlobalTheory_compat_family_extend
import Theorems.Thm_GlobalTheory_restrict_glob1_bijective
import Theorems.Thm_GlobalTheory_sep_of_factoring_cover


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
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
namespace GlobalTheory.CechDR
theorem _root_.solution {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    {C' : Type} [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X')
    (hcov : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u)
    (hdir : ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) :
    Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s') G)) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') G H hcov hdir
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' G hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' G hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' G hcov
  have b1 : Function.Bijective (CoefMap.restrict (OAff s') G).pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  exact ⟨_root_.GlobalTheory.CechDR.pullHyp1_restrict_injective _ _ b1.1 (_root_.GlobalTheory.compat_family_extend _ _ hs hg) bg.1,
    _root_.GlobalTheory.CechDR.pullHyp1_restrict_surjective _ _ b1.2 (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2⟩
end GlobalTheory.CechDR
