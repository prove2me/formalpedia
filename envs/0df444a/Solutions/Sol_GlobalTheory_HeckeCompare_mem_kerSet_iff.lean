-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.mem_kerSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:05:52.839953+00:00
-- url     : https://prove2.me/submissions/d4e91975-65a0-43a1-8a8c-84ea89526460

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_exists_split_two
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_of_dvd
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_split
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_pow_tors
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_mul
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_adj
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_of_kill
import Theorems.Thm_GlobalTheory_HeckeCompare_conj_isMaximal
import Theorems.Thm_GlobalTheory_HeckeCompare_datum_tors
import Theorems.Thm_GlobalTheory_HeckeTate_IsPart_exists_inv
import Theorems.Thm_GlobalTheory_HeckeTate_IsPart_of_dvd


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
namespace GlobalTheory.HeckeCompare
theorem _root_.solution (x : Q) : x ∈ kerSet ρ e p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) C₀ ↔
    ∃ x' x₂ : Q, x = x' * x₂ ∧ (x' ^ p = 1 ∧ ∀ c ∈ C₀, e p x' c 1) ∧
      (∃ n : ℕ, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ n, ρ a x₂ = 1) ∧ x₂ ^ p ∈ C₀ := by
  have ht : ∀ c ∈ C₀, c ^ p = 1 := fun c hc => datum_tors hρ hpP h₂ hc
  constructor
  · rintro ⟨x₁, x₂, x₃, rfl, ⟨t₁, a, ha, -, k₁⟩, k₂, t₃, -, k₃⟩
    refine ⟨x₁ * x₃, x₂, mul_right_comm _ _ _, ⟨by rw [mul_pow, t₁, t₃, mul_one], fun c hc => ?_⟩, k₂⟩
    refine triv_mul I hu hp t₁ t₃ (ht c hc) ?_ (k₃ c hc)
    obtain ⟨b, π, hπ, h⟩ := hP.exists_inv ha
    have := hρ.split h x₁
    rw [mul_comm b, hρ.2.1, k₁, map_one, one_mul] at this
    rw [← this]
    exact triv_of_kill I hu hp t₁ (ht c hc) (h₂ c hc _ (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hπ))
  · rintro ⟨x', x₂, rfl, ⟨t, o⟩, ⟨r, k₂⟩, k₂'⟩
    have := conj_isMaximal H P
    obtain ⟨m, n, w, u, v, a, h, ha, ha', hw, hu', hv⟩ :=
      exists_split_two (Nat.cast_ne_zero.2 hp.ne' : (p : 𝓞 E) ≠ 0) P _ hco
    refine ⟨ρ w x', ρ v x' * x₂, ρ u x', ?_, ⟨hρ.pow_tors t w, a, ha, ha', ?_⟩, ⟨⟨n + r, fun b hb => ?_⟩, ?_⟩,
      hρ.pow_tors t u, ⟨m, fun b hb => ?_⟩, fun c hc => ?_⟩
    · rw [← mul_assoc, mul_right_comm, ← hρ.2.2, ← hρ.2.2, h, hρ.1]
    · rw [← hρ.2.1]; exact hρ.of_dvd t hw
    · rw [map_mul, ← hρ.2.1, hρ.of_dvd t (hv b (Ideal.pow_le_pow_right (Nat.le_add_right _ _) hb)),
        k₂ b (Ideal.pow_le_pow_right (Nat.le_add_left _ _) hb), mul_one]
    · rwa [mul_pow, hρ.pow_tors t v, one_mul]
    · rw [← hρ.2.1]; exact hρ.of_dvd t (hu' b hb)
    · rw [triv_adj I hu hp t (ht c hc)]
      exact o _ (h₁ _ c hc)
end GlobalTheory.HeckeCompare
