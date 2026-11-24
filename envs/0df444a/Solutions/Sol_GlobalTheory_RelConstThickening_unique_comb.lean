-- Prove2me | solution 1 for GlobalTheory.RelConstThickening.unique_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:55:15.597821+00:00
-- url     : https://prove2.me/submissions/ba23d7e9-049a-4403-a080-9b22d50a5166

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Theorems.Thm_GlobalTheory_RelConstThickening_res_comb
import Theorems.Thm_GlobalTheory_RelConstThickening_le_iSup_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.RelConstThickening
variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {π : Y' ⟶ Sp R} {ρ : Y' ⟶ Y} {ε : R}
namespace GlobalTheory.RelConstThickening
theorem _root_.solution {W : Y.Opens}
    (H : ∀ V : Y.Opens, IsAffineOpen V → V ≤ W → ∀ F : Γ(Y', ρ ⁻¹ᵁ V), ∃! ab : Γ(Y, V) × Γ(Y, V),
      F = (ρ.app V).hom ab.1 + constFn π _ ε * (ρ.app V).hom ab.2)
    {O : Y.Opens} (hO : O ≤ W) {a b a' b' : Γ(Y, O)}
    (h : (ρ.app O).hom a + constFn π _ ε * (ρ.app O).hom b =
      (ρ.app O).hom a' + constFn π _ ε * (ρ.app O).hom b') : a = a' ∧ b = b' := by
  have loc : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a, (Y.presheaf.map (homOfLE U.2.2).op).hom b) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a', (Y.presheaf.map (homOfLE U.2.2).op).hom b') := fun U => by
    have h' : ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun x hx => U.2.2 hx
    have e := congrArg (Y'.presheaf.map (homOfLE h').op).hom h
    rw [res_comb U.2.2, res_comb U.2.2] at e
    exact (H _ U.2.1 (U.2.2.trans hO) _).unique rfl e
  exact ⟨Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) a a'
      fun U => congrArg Prod.fst (loc U),
    Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) b b'
      fun U => congrArg Prod.snd (loc U)⟩
end GlobalTheory.RelConstThickening
