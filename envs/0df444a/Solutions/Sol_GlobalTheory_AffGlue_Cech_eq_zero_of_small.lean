-- Prove2me | solution 1 for GlobalTheory.AffGlue.Cech.eq_zero_of_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:31:08.16814+00:00
-- url     : https://prove2.me/submissions/f959e5d0-877d-4712-a936-a95b2b479975

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineCoverSectionsGlue
import Theorems.Thm_GlobalTheory_AffGlue_Cech_span_small_eq_top
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
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
open GlobalTheory GlobalTheory.AffGlue GlobalTheory.AffGlue.Cech
variable {T : Scheme.{0}}
namespace GlobalTheory.AffGlue.Cech
theorem _root_.solution (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type}
    (W : ι → T.Opens) (hc : V ≤ ⨆ i, W i) (x : D.M V hV)
    (hx : ∀ (i : ι) (O : T.Opens) (hO : IsAffineOpen O) (h : O ≤ V), O ≤ W i →
      D.ρ hV hO h x = 0) : x = 0 := by
  have := Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule Γ(T, V) (D.M V hV)) _
    (span_small_eq_top hV W hc) x (by
      rintro ⟨f, i, hf⟩
      obtain ⟨n, hn⟩ := D.loc_inj hV f (hV.basicOpen f) x (hx i _ _ _ hf)
      exact ⟨n, by simpa using hn⟩)
  simpa using this
end GlobalTheory.AffGlue.Cech
