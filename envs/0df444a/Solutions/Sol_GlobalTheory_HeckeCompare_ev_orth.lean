-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.ev_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:05:52.058799+00:00
-- url     : https://prove2.me/submissions/3607c89c-f5f5-44b4-8aa3-ec52443e254a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_ev_pow
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_mul
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_of_kill
import Theorems.Thm_GlobalTheory_HeckeCompare_datum_tors

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
include hp hpP
variable {C₀ : Subgroup Q} (h₁ : ∀ a, ∀ x ∈ C₀, ρ a x ∈ C₀)
  (h₂ : ∀ x ∈ C₀, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1)
include h₂
include h₁
omit hco h₁ hP
namespace GlobalTheory.HeckeCompare
theorem _root_.solution {a : D.La} (ha : a ∈ P • (⊤ : Submodule (𝓞 E) D.La)) : ∀ c ∈ C₀, e p (I.ev p a) c 1 := by
  intro c hc
  have ht := datum_tors hρ hpP h₂ hc
  refine Submodule.smul_induction_on ha (fun π hπ b _ => ?_) fun a b ha hb => ?_
  · rw [I.lin]
    exact triv_of_kill I hu hp (ev_pow I hp b) ht (h₂ c hc _ (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hπ))
  · rw [I.add]
    exact triv_mul I hu hp (ev_pow I hp a) (ev_pow I hp b) ht ha hb
end GlobalTheory.HeckeCompare
