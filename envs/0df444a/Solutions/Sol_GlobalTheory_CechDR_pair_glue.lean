-- Prove2me | solution 1 for GlobalTheory.CechDR.pair_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:24:56.147811+00:00
-- url     : https://prove2.me/submissions/b5da75e0-d87c-4044-8525-9d3483635e68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairs
import Theorems.Thm_GlobalTheory_CechDR_Pair_exists_le
import Theorems.Thm_GlobalTheory_CechDR_Pair_exists_le_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option autoImplicit false
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)),
    (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p),
      mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) →
    ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by
  intro R' _ X X' φ s' W k hk
  let U : {p : Pair φ // p.1.1 ≤ W} → X'.Opens := fun i ↦ i.1.1.1.1
  let sf : ∀ i : {p : Pair φ // p.1.1 ≤ W}, ToType (X'.sheaf.1.obj (op (U i))) := fun i ↦ k i.1 i.2

  have key : ∀ (i : {p : Pair φ // p.1.1 ≤ W}) (r : Pair φ) (hr : r ≤ i.1) {x : X'} (hx : x ∈ r.1.1.1),
      X'.presheaf.germ (U i) x (Pair.le_fst hr hx) (sf i) =
        X'.presheaf.germ r.1.1.1 x hx (k r ((Pair.le_fst hr).trans i.2)) := by
    intro i r hr x hx
    rw [← hk i.1 r i.2 ((Pair.le_fst hr).trans i.2) hr]
    exact (X'.presheaf.germ_res_apply (homOfLE (show r.1.1.1 ≤ U i from Pair.le_fst hr)) x hx _).symm
  have hcomp : TopCat.Presheaf.IsCompatible X'.sheaf.1 U sf := by
    intro i j
    refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun x hx ↦ ?_
    obtain ⟨r, hri, hrj, hxr⟩ := Pair.exists_le_le φ i.1 j.1 hx
    change X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf i)) = X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf j))
    exact ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLELeft (U i) (U j)) x hx (sf i)).trans
      (key i r hri hxr)).trans ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLERight (U i) (U j))
        x hx (sf j)).trans (key j r hrj hxr)).symm
  have hcov : W.1 ≤ iSup U := fun x hx ↦ by
    obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨G, hG, -⟩ := X'.sheaf.existsUnique_gluing' U W.1 (fun i ↦ homOfLE i.2) hcov sf hcomp
  exact ⟨G, fun p hp ↦ hG ⟨p, hp⟩⟩
end GlobalTheory.CechDR
