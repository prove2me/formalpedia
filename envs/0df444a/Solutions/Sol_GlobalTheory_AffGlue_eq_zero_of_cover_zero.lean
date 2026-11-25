-- Prove2me | solution 1 for GlobalTheory.AffGlue.eq_zero_of_cover_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:10:22.266771+00:00
-- url     : https://prove2.me/submissions/498ca52f-95d8-4a73-bfe2-ce743f62250a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineGlueSeparated
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffGlue
namespace GlobalTheory.AffGlue
theorem _root_.solution : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ x : D.M V hV, (∀ i, D.ρ hV (hW i) (hWV i) x = 0) → x = 0 := by
  intro T D V hV ι W hW hWV hcov x hx
  let J : Ideal Γ(T, V) := LinearMap.ker (LinearMap.toSpanSingleton Γ(T, V) (D.M V hV) x)
  have hJ : ∀ a : Γ(T, V), a ∈ J ↔ a • x = 0 := fun a => by
    simp [J, LinearMap.toSpanSingleton_apply]
  let s : Set Γ(T, V) := {f | ∃ n : ℕ, f ^ n • x = 0}
  have hs : V ≤ ⨆ f : s, T.basicOpen f.1 := by
    intro y hy
    have hy' : y ∈ ⨆ i, W i := hcov hy
    rw [TopologicalSpace.Opens.mem_iSup] at hy'
    obtain ⟨i, hi⟩ := hy'
    obtain ⟨f, hfle, hyf⟩ := hV.exists_basicOpen_le (V := W i) ⟨y, hi⟩ hy
    have hD : IsAffineOpen (T.basicOpen f) := hV.basicOpen f
    have h0 : D.ρ hV hD (T.basicOpen_le f) x = 0 := by
      have := D.ρ_ρ hV (hW i) hD (hWV i) hfle x
      rw [hx i, map_zero] at this
      exact this.symm
    obtain ⟨n, hn⟩ := D.loc_inj hV f hD x h0
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨f, n, hn⟩, hyf⟩
  have hspan : Ideal.span s = ⊤ := (hV.self_le_iSup_basicOpen_iff).mp hs
  have hrad : J.radical = ⊤ := by
    rw [eq_top_iff, ← hspan, Ideal.span_le]
    rintro f ⟨n, hn⟩
    exact ⟨n, (hJ _).mpr hn⟩
  have h1 : (1 : Γ(T, V)) ∈ J := by
    rw [Ideal.radical_eq_top] at hrad
    rw [hrad]; trivial
  simpa using (hJ 1).mp h1
end GlobalTheory.AffGlue
