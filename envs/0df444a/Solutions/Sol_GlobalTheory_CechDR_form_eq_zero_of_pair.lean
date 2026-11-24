-- Prove2me | solution 1 for GlobalTheory.CechDR.form_eq_zero_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:07.741684+00:00
-- url     : https://prove2.me/submissions/1c547f6a-0897-4c7b-b239-c58fdacb87b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormEqZeroOfVanishingOnPairs
import Theorems.Thm_GlobalTheory_CechDR_form_pow_smul_eq_zero_of_basicOpen
import Theorems.Thm_GlobalTheory_CechDR_Pair_exists_basicOpen
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
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) : ω = 0 := by
  let A := (OAff s').obj (op W)
  let J : Ideal A := (Submodule.span A {ω}).annihilator
  let I : Set Γ(X', W.1) := {a | (show A from a) ∈ J}
  have hcov : W.1 ≤ ⨆ a : I, X'.basicOpen a.1 := by
    intro x hx
    obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
    obtain ⟨⟨⟨U, hU⟩, V⟩, hpV⟩ := p
    dsimp only at e hxp
    subst e
    have hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W := X'.basicOpen_le f
    obtain ⟨n, hn⟩ := form_pow_smul_eq_zero_of_basicOpen s' W f hU hle ω
      (h ⟨(⟨X'.basicOpen f, hU⟩, V), hpV⟩ hle)
    have hxn : x ∈ X'.basicOpen (f ^ n) := by
      rcases n with _ | n
      · rw [pow_zero, X'.basicOpen_of_isUnit isUnit_one]; exact hx
      · rwa [X'.basicOpen_pow f n.succ_pos]
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨f ^ n, show ((show A from f) ^ n) ∈ J from
        (Submodule.mem_annihilator_span_singleton ω _).2 hn⟩, hxn⟩
  have hI := (W.2.self_le_iSup_basicOpen_iff).1 hcov
  have hJ : Ideal.span I ≤ J := Ideal.span_le.2 fun a ha ↦ ha
  have h1 : (1 : A) ∈ J := hJ (hI ▸ Submodule.mem_top)
  simpa using (Submodule.mem_annihilator_span_singleton _ _).1 h1
end GlobalTheory.CechDR
