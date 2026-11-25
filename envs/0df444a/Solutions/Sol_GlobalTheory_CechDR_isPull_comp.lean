-- Prove2me | solution 1 for GlobalTheory.CechDR.isPull_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:56.640805+00:00
-- url     : https://prove2.me/submissions/1533815a-f5c2-4fa6-ad0d-49086e7cff39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Theorems.Thm_GlobalTheory_CechDR_cechTripleRestrictComposite_injective_first
import Theorems.Thm_GlobalTheory_CechDR_cechTripleRestrictComposite_injective_second
import Theorems.Thm_GlobalTheory_CechDR_tri_pull_pull1
import Theorems.Thm_GlobalTheory_CechDR_tri_pull_pull2
import Theorems.Thm_GlobalTheory_CechDR_tri_res_pull1
import Theorems.Thm_GlobalTheory_CechDR_tri_res_pull2
import Theorems.Thm_GlobalTheory_CechDR_cechTriple_restrict_restrict_first
import Theorems.Thm_GlobalTheory_CechDR_cechTriple_restrict_restrict_second
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


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
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}
namespace GlobalTheory.CechDR
theorem _root_.solution (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) :
    (∀ a a' a'', IsPull1 h a a' → IsPull1 h' a' a'' → IsPull1 h'' a a'') ∧
      (∀ a a' a'', IsPull2 h a a' → IsPull2 h' a' a'' → IsPull2 h'' a a'') := by
  refine ⟨fun a a' a'' p p' ↦ cechTripleRestrictComposite_injective_first ψ φ s'' ?_,
    fun a a' a'' p p' ↦ cechTripleRestrictComposite_injective_second ψ φ s'' ?_⟩
  · have p0 : pullHyp1 (pairPull h) a = pullHyp1 (pairRes φ s') a' := p
    have p1 : pullHyp1 (pairPull h') a' = pullHyp1 (pairRes ψ s'') a'' := p'
    rw [tri_pull_pull1 h h' h'', p0, tri_res_pull1, p1, cechTriple_restrict_restrict_first]
  · have p0 : pullHyp2 (pairPull h) a = pullHyp2 (pairRes φ s') a' := p
    have p1 : pullHyp2 (pairPull h') a' = pullHyp2 (pairRes ψ s'') a'' := p'
    rw [tri_pull_pull2 h h' h'', p0, tri_res_pull2, p1, cechTriple_restrict_restrict_second]
end GlobalTheory.CechDR
