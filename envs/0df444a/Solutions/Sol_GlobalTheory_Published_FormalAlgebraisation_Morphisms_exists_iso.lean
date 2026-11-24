-- Prove2me | solution 1 for GlobalTheory.Published.FormalAlgebraisation.Morphisms.exists_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:48.492815+00:00
-- url     : https://prove2.me/submissions/f95c7d4c-5a07-44f8-b0b9-aa0f4940a7ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.FormalAlgebraisation
variable {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
namespace GlobalTheory.Published.FormalAlgebraisation
namespace Morphisms
theorem _root_.solution (H : Morphisms) (hI : IsAdicComplete I R)
    {X X' : Over (Spec (CommRingCat.of R))} [hX : IsProper X.hom] [hX' : IsProper X'.hom]
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {b : ∀ e, (Y e).left ⟶ X.left}
    {b' : ∀ e, (Y e).left ⟶ X'.left}
    (hb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e)
    (hb' : ∀ e, IsPullback (b' e) (Y e).hom X'.hom (thick R I e))
    (hβ' : ∀ e, β e ≫ b' (e + 1) = b' e) :
    ∃ g : X ≅ X', (∀ e, b e ≫ g.hom.left = b' e) ∧
      ∀ g' : X ⟶ X', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom := by
  obtain ⟨g, hg, hu⟩ := H R I hI X X' hX inferInstance inferInstance inferInstance Y β b hb hβ b'
    (fun e => (hb' e).w) hβ'
  obtain ⟨k, hk, -⟩ := H R I hI X' X hX' inferInstance inferInstance inferInstance Y β b' hb' hβ' b
    (fun e => (hb e).w) hβ
  refine ⟨⟨g, k, ?_, ?_⟩, hg, hu⟩
  · exact (H R I hI X X hX inferInstance inferInstance inferInstance Y β b hb hβ b
      (fun e => (hb e).w) hβ).unique
      (fun e => by rw [Over.comp_left, ← Category.assoc, hg, hk]) (fun e => Category.comp_id _)
  · exact (H R I hI X' X' hX' inferInstance inferInstance inferInstance Y β b' hb' hβ' b'
      (fun e => (hb' e).w) hβ').unique
      (fun e => by rw [Over.comp_left, ← Category.assoc, hk, hg]) (fun e => Category.comp_id _)
end Morphisms
end GlobalTheory.Published.FormalAlgebraisation
