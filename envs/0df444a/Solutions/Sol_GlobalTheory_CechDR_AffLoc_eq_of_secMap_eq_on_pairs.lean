-- Prove2me | solution 1 for GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:38.000048+00:00
-- url     : https://prove2.me/submissions/e042ee10-8971-447f-80be-5e34e5abee59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairs
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
namespace GlobalTheory.CechDR.AffLoc
theorem _root_.solution {X : Scheme.{0}} (B B' : Type) [CommRing B] [CommRing B']
    (x : Sp B ⟶ X) (ψ : Sp B' ⟶ Sp B) (a b : B')
    (h : ∀ (V' : (Sp B').affineOpens) (p : Pair x), V'.1 ≤ ψ ⁻¹ᵁ p.1.1.1 →
      (secMap (𝟙 (Sp B')) V'.1).hom a = (secMap (𝟙 (Sp B')) V'.1).hom b) : a = b := by
  have hex : ∀ y : Sp B', ∃ V' : (Sp B').affineOpens, y ∈ V'.1 ∧
      ∃ p : Pair x, V'.1 ≤ ψ ⁻¹ᵁ p.1.1.1 := by
    intro y
    obtain ⟨U, hU, hyU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x (ψ y)) trivial
    obtain ⟨V, hV, hyV, hVU⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Sp B) (U := x ⁻¹ᵁ U) (x := ψ y) hyU
    obtain ⟨W, hW, hyW, hWV⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Sp B') (U := ψ ⁻¹ᵁ V) (x := y) hyV
    exact ⟨⟨W, hW⟩, hyW, ⟨(⟨V, hV⟩, ⟨U, hU⟩), hVU⟩, hWV⟩
  choose W hyW p hp using hex
  have key : (Scheme.ΓSpecIso (CommRingCat.of B')).inv a = (Scheme.ΓSpecIso (CommRingCat.of B')).inv b := by
    refine (Sp B').sheaf.eq_of_locally_eq' (fun y => (W y).1) ⊤ (fun _ => homOfLE le_top)
      (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyW y⟩) _ _ (fun y => ?_)
    have := h (W y) (p y) (hp y)
    simp only [secMap, Scheme.Hom.appLE, Scheme.Hom.id_app, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  exact (Scheme.ΓSpecIso (CommRingCat.of B')).symm.commRingCatIsoToRingEquiv.injective key
end GlobalTheory.CechDR.AffLoc
