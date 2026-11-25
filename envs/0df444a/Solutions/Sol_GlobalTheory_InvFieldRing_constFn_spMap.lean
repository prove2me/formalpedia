-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.constFn_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:36.073303+00:00
-- url     : https://prove2.me/submissions/32f03c79-a294-42b6-a721-c8afea04f23c

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst

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
namespace GlobalTheory.InvFieldRing
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (φ : R →+* S)
    (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  rw [h] at h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  unfold constFn
  rw [← h3, h2]
end GlobalTheory.InvFieldRing
