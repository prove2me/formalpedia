-- Prove2me | solution 1 for GlobalTheory.FullLevel.smul_mem_M
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:37:32.81281+00:00
-- url     : https://prove2.me/submissions/ba39c662-93c4-4f2f-99cf-372ae24bd3f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open GlobalTheory GlobalTheory.FullLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.FullLevel
theorem _root_.solution (l : Level H) {D : Datum H} {c : 𝓞 E} (hc : c ∈ l.Mb) {a : D.La}
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ y : D.La, c • a = l.M • y := by
  refine Submodule.smul_induction_on ha ?_ ?_
  · intro r hr t _
    have : c * r ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul hc hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨s • t, by rw [← mul_smul, ← hs, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]⟩
  · rintro x y ⟨x', hx'⟩ ⟨y', hy'⟩
    exact ⟨x' + y', by rw [smul_add, hx', hy', smul_add]⟩
end GlobalTheory.FullLevel
