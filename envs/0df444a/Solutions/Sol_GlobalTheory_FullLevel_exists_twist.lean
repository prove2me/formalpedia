-- Prove2me | solution 1 for GlobalTheory.FullLevel.exists_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:54:55.170266+00:00
-- url     : https://prove2.me/submissions/488f7bbd-fae2-4a70-9426-64b20c3a7dc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIso
import Theorems.Thm_GlobalTheory_FullLevel_bar_bar
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
theorem _root_.solution (l : Level H) (L : ℤ) (hL : (l.A : ℤ) ∣ L - 1) :
    ∃ u w c : 𝓞 E, c ∈ l.Mb ∧ u = 1 + (l.A : 𝓞 E) * c ∧
      H.bar u * u = (L : 𝓞 E) + (l.M' : 𝓞 E) * w := by
  obtain ⟨q, hq⟩ := hL
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.1 h1
  have hbn : H.bar n ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hn
  have hbm : H.bar m ∈ l.Mb := by
    obtain ⟨m0, hm0, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hm
    simpa [bar_bar] using hm0
  have hbar1 : H.bar n + H.bar m = 1 := by rw [← map_add, hnm, map_one]
  have hxN : H.bar n - m ∈ l.Mb := by
    have e : H.bar n - m = n - H.bar m := by linear_combination hbar1 - hnm
    rw [e]; exact sub_mem hn hbm
  have hxN' : H.bar n - m ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := sub_mem hbn hm
  have hx : H.bar n - m ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have e : H.bar n - m = n * (H.bar n - m) + (H.bar n - m) * m := by
      linear_combination -(H.bar n - m) * hnm
    rw [e]
    exact add_mem (Ideal.mul_mem_mul hn hxN') (Ideal.mul_mem_mul hxN hm)
  have hnn : n * H.bar n ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_mem_mul hn hbn
  rw [l.prod] at hx hnn
  obtain ⟨y1, hy1⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨y2, hy2⟩ := Ideal.mem_span_singleton'.1 hnn
  have hg : ((l.M : ℕ) : 𝓞 E) * l.A = (l.M' : 𝓞 E) * (Nat.gcd l.M l.A : ℕ) := by
    have := Nat.gcd_mul_lcm l.M l.A
    unfold Level.M'
    exact_mod_cast (by rw [mul_comm (Nat.lcm _ _), this] : l.M * l.A = Nat.lcm l.M l.A * Nat.gcd l.M l.A)
  have hq' : (L : 𝓞 E) - 1 = (l.A : 𝓞 E) * q := by exact_mod_cast hq
  refine ⟨1 + ((L : 𝓞 E) - 1) * n, (Nat.gcd l.M l.A : 𝓞 E) * q * (y1 + ((L : 𝓞 E) - 1) * y2),
    (q : 𝓞 E) * n, Ideal.mul_mem_left _ _ hn, ?_, ?_⟩
  · rw [hq']; ring
  · have hb : H.bar (1 + ((L : 𝓞 E) - 1) * n) = 1 + ((L : 𝓞 E) - 1) * H.bar n := by
      simp [map_add, map_mul, map_sub, map_one, map_intCast]
    rw [hb]
    linear_combination ((L : 𝓞 E) - 1) * hnm - ((L : 𝓞 E) - 1) * hy1 - ((L : 𝓞 E) - 1) ^ 2 * hy2
      + (l.M : 𝓞 E) * (y1 + ((L : 𝓞 E) - 1) * y2) * hq' + (q : 𝓞 E) * (y1 + ((L : 𝓞 E) - 1) * y2) * hg
end GlobalTheory.FullLevel
