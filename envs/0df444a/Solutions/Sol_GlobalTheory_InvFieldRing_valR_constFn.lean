-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.valR_constFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:43.360167+00:00
-- url     : https://prove2.me/submissions/d7876491-5948-4e0a-9e39-540dc2dfd92b

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
import Theorems.Thm_GlobalTheory_InvFieldRing_valR_of
import Theorems.Thm_GlobalTheory_InvFieldRing_valR_appLE

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
theorem _root_.solution {B : Type} [CommRing B] (x : Sp A ⟶ Y) (p : Y ⟶ Sp B) (ψ : B →+* A) (hx : x ≫ p = spMap ψ)
    (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : B) : valR x V (constFn p V a) = ψ a := by
  unfold constFn
  refine (valR_appLE x p ⊤ V (fun _ _ => trivial) h _).trans ?_
  rw [hx, valR_of _ _ le_rfl]
  have n := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  have e' : ((spMap ψ).appLE ⊤ ⊤ le_rfl) = (spMap ψ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (ψ a) =
    (spMap ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a) at n
  rw [e', ← n]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _
end GlobalTheory.InvFieldRing
