-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.triv_of_primary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:06.955744+00:00
-- url     : https://prove2.me/submissions/f1993e89-ea62-44ab-ad70-da277d16c81f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_split
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_of_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
variable (I : TateIso D k Q (fun a x => ρ a x) e) (hu : Uniq e) (hρ : IsAct ρ) {P : Ideal (𝓞 E)} [hP : P.IsMaximal]
  (hco : P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {p : ℕ} (hp : 0 < p) (hpP : (p : 𝓞 E) ∈ P)
include I hu hρ hco
omit hP
namespace GlobalTheory.HeckeCompare
theorem _root_.solution {n : ℕ} (hn : 0 < n) {x y : Q} (hx : x ^ n = 1) (hy : y ^ n = 1) {r s : ℕ}
    (h : ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ r, ρ a x = 1)
    (h' : ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ s, ρ a y = 1) : e n x y 1 := by
  have h₄ : IsCoprime (P ^ s) (P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ r) := (Ideal.isCoprime_iff_sup_eq.2 hco).pow
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h₄
  have := hρ.split hab x
  rw [h b hb, mul_one] at this
  rw [← this]
  refine triv_of_kill I hu hn hx hy (h' _ ?_)
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) ha
end GlobalTheory.HeckeCompare
