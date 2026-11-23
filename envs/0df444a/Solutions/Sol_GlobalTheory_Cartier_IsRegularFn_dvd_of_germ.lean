-- Prove2me | solution 1 for GlobalTheory.Cartier.IsRegularFn.dvd_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:07.386811+00:00
-- url     : https://prove2.me/submissions/03229080-1e76-435b-9853-c38625561b7a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_ext_germ
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul_right_cancel

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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
namespace IsRegularFn
theorem _root_.solution {U : X.Opens} {a b : Γ(X, U)} (ha : IsRegularFn a)
    (h : ∀ x (hx : x ∈ U), (X.presheaf.germ U x hx).hom a ∣ (X.presheaf.germ U x hx).hom b) :
    a ∣ b := by
  have loc : ∀ x : U, ∃ (V : X.Opens) (hV : V ≤ U) (_ : x.1 ∈ V) (c : Γ(X, V)),
      Geo.Tor.resG X hV b = c * Geo.Tor.resG X hV a := by
    rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ := h x hx
    obtain ⟨V, hV, c, rfl⟩ := X.presheaf.exists_germ_eq t
    have hm : x ∈ U ⊓ V := ⟨hx, hV⟩
    have e : (X.presheaf.germ (U ⊓ V) x hm).hom (Geo.Tor.resG X inf_le_left b) =
        (X.presheaf.germ (U ⊓ V) x hm).hom
          (Geo.Tor.resG X inf_le_right c * Geo.Tor.resG X inf_le_left a) := by
      rw [map_mul, germ_resG, germ_resG, germ_resG, ht, mul_comm]
    obtain ⟨W, hW, i₁, i₂, e'⟩ := X.presheaf.germ_eq x hm hm _ _ e
    have le : W ≤ U ⊓ V := i₁.le
    have e'' : Geo.Tor.resG X le (Geo.Tor.resG X inf_le_left b) = Geo.Tor.resG X le
      (Geo.Tor.resG X inf_le_right c * Geo.Tor.resG X inf_le_left a) := e'
    rw [map_mul, resG_resG, resG_resG, resG_resG] at e''
    exact ⟨W, le.trans inf_le_left, hW, _, e''⟩
  choose V hV hx c hc using loc
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hV i))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) c (fun i j => by
      have e₁ := congrArg (Geo.Tor.resG X (inf_le_left : V i ⊓ V j ≤ V i)) (hc i)
      have e₂ := congrArg (Geo.Tor.resG X (inf_le_right : V i ⊓ V j ≤ V j)) (hc j)
      rw [map_mul, resG_resG, resG_resG] at e₁ e₂
      exact (ha.resG (inf_le_left.trans (hV i))).mul_right_cancel (e₁.symm.trans e₂))
  refine ⟨s, ext_germ fun x hx' => ?_⟩
  have e := congrArg (X.presheaf.germ _ x (hx ⟨x, hx'⟩)).hom (hc ⟨x, hx'⟩)
  have hs' : ∀ s' : Γ(X, U), Geo.Tor.resG X (hV ⟨x, hx'⟩) s' = c ⟨x, hx'⟩ →
      (X.presheaf.germ U x hx').hom b = (X.presheaf.germ U x hx').hom (a * s') := fun s' hs' => by
    rw [← hs', ← map_mul (Geo.Tor.resG X _), germ_resG, germ_resG, mul_comm] at e
    exact e
  exact hs' s (hs ⟨x, hx'⟩)
end IsRegularFn
end GlobalTheory.Cartier
