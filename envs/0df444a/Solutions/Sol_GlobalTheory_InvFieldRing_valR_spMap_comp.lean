-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.valR_spMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:56.312269+00:00
-- url     : https://prove2.me/submissions/0ea28ee5-c0be-4791-8f9e-fb7f8c7ed083

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
import Theorems.Thm_GlobalTheory_InvFieldRing_valR_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
noncomputable section
open GlobalTheory GlobalTheory.InvFieldRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {A : Type} [CommRing A] {Y : Scheme.{0}}
namespace GlobalTheory.InvFieldRing
theorem _root_.solution {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (f : Γ(Y, V)) : valR (spMap ψ ≫ x) V f = ψ (valR x V f) := by
  have h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ V := fun y _ => h (Set.mem_univ ((spMap ψ) y))
  rw [valR_of _ V h', valR_of x V h]
  have e : (spMap ψ ≫ x).appLE V ⊤ h' = x.appLE V ⊤ h ≫ (spMap ψ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap ψ) x V ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ x).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f =
    (x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f
  rw [e, Category.assoc, n]
end GlobalTheory.InvFieldRing
