-- Prove2me | solution 1 for GlobalTheory.CechDR.AffLoc.exists_glue_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:03:21.970425+00:00
-- url     : https://prove2.me/submissions/12f1d517-233d-4600-9e8f-bc7520d1e161

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsSpecFromPairs
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
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
namespace GlobalTheory.CechDR.AffLoc
theorem _root_.solution {X : Scheme.{0}} (B : Type) [CommRing B] (x : Sp B ⟶ X)
    (h : ∀ p : Pair x, Γ(Sp B, p.1.1.1))
    (hh : ∀ p q : Pair x, ∀ hpq : p ≤ q,
      ((Sp B).presheaf.map (homOfLE (Pair.le_fst hpq)).op).hom (h q) = h p) :
    ∃ G : B, ∀ p : Pair x, (secMap (𝟙 (Sp B)) p.1.1.1).hom G = h p := by
  have sub : ∀ (p q : Pair x) (y : Sp B), y ∈ p.1.1.1 → y ∈ q.1.1.1 →
      ∃ r : Pair x, r ≤ p ∧ r ≤ q ∧ y ∈ r.1.1.1 := by
    intro p q y hp hq
    have hyU : x.base y ∈ p.1.2.1 ⊓ q.1.2.1 := ⟨p.2 hp, q.2 hq⟩
    obtain ⟨W, hW, hyW, hWs⟩ := exists_isAffineOpen_mem_and_subset hyU
    have hyV : y ∈ p.1.1.1 ⊓ q.1.1.1 ⊓ x ⁻¹ᵁ W := ⟨⟨hp, hq⟩, hyW⟩
    obtain ⟨V, hV, hyV', hVs⟩ := exists_isAffineOpen_mem_and_subset hyV
    refine ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), fun z hz ↦ (hVs hz).2⟩, ?_, ?_, hyV'⟩
    · exact ⟨fun z hz ↦ (hVs hz).1.1, fun z hz ↦ (hWs hz).1⟩
    · exact ⟨fun z hz ↦ (hVs hz).1.2, fun z hz ↦ (hWs hz).2⟩
  have cover : ∀ y : Sp B, ∃ p : Pair x, y ∈ p.1.1.1 := by
    intro y
    obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (show x.base y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hyV, hVs⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ x ⁻¹ᵁ W from hyW)
    exact ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), fun z hz ↦ hVs hz⟩, hyV⟩
  have key : ∀ (p r : Pair x) (hr : r ≤ p) (y : Sp B) (hy : y ∈ r.1.1.1),
      (Sp B).presheaf.germ p.1.1.1 y (Pair.le_fst hr hy) (h p) =
        (Sp B).presheaf.germ r.1.1.1 y hy (h r) := by
    intro p r hr y hy
    rw [← hh r p hr]
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  let U : Pair x → (Sp B).Opens := fun p ↦ p.1.1.1
  have hc : TopCat.Presheaf.IsCompatible (Sp B).presheaf U h := by
    intro i j
    refine TopCat.Presheaf.section_ext (Sp B).sheaf _ _ _ fun y hy ↦ ?_
    obtain ⟨r, hri, hrj, hyr⟩ := sub i j y hy.1 hy.2
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ((key i r hri y hyr).trans
      ((key j r hrj y hyr).symm.trans (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm))
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (Sp B).sheaf U ⊤
    (fun _ ↦ homOfLE le_top) (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 (cover y)) h hc
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom s, fun p ↦ ?_⟩
  rw [← hs p]
  have e1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s) = s :=
    Iso.hom_inv_id_apply _ _
  change ((𝟙 (Sp B) : Sp B ⟶ Sp B).appLE ⊤ p.1.1.1 le_top).hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s)) = _
  rw [e1]
  simp [Scheme.Hom.appLE]
  rfl
end GlobalTheory.CechDR.AffLoc
