-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.eq_kerSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:53.350146+00:00
-- url     : https://prove2.me/submissions/20190d56-bdb7-4373-8022-aa02b6c941c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_exists_split_one
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_split
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_kill_mul_iff
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_symm
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_down
import Theorems.Thm_GlobalTheory_HeckeCompare_conj_isMaximal
import Theorems.Thm_GlobalTheory_HeckeCompare_datum_tors
import Theorems.Thm_GlobalTheory_HeckeCompare_mem_kerSet_iff
import Theorems.Thm_GlobalTheory_HeckeCompare_exists_subgroup

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
omit h₁ h₂
namespace GlobalTheory.HeckeCompare
theorem _root_.solution [IsAlgClosed k] [CharZero k] (hf : Finite {x : Q // x ^ p = 1}) (C : Subgroup Q)
    (c₁ : ∀ x ∈ C, ∀ a, ρ a x ∈ C)
    (c₃ : ∀ x ∈ C, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1)
    (c₄ : ∀ x ∈ C, ∀ y ∈ C, e (p * p) x y 1) (c₅ : Nat.card C = Nat.card {x : Q // x ^ p = 1}) :
    (∀ a, ∀ x ∈ C.map (powMonoidHom p), ρ a x ∈ C.map (powMonoidHom p)) ∧
    (∀ x ∈ C.map (powMonoidHom p), ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1) ∧
    (C : Set Q) = kerSet ρ e p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) (C.map (powMonoidHom p)) := by
  have h₁ : ∀ a, ∀ x ∈ C.map (powMonoidHom p), ρ a x ∈ C.map (powMonoidHom p) := by
    rintro a _ ⟨x, hx, rfl⟩
    exact ⟨ρ a x, c₁ x hx a, (map_pow _ _ _).symm⟩
  have h₂ : ∀ x ∈ C.map (powMonoidHom p), ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hρ.kill_mul_iff p _ x).1 (c₃ x hx)
  refine ⟨h₁, h₂, ?_⟩
  obtain ⟨C', e₁, -, -, -, -, e₂, -⟩ := exists_subgroup I hu hρ hco hp hpP h₁ h₂ hf
  have : Nonempty {x : Q // x ^ p = 1} := ⟨⟨1, one_pow _⟩⟩
  have : Finite C' := Nat.finite_of_card_ne_zero (by rw [e₂]; exact Nat.card_pos.ne')
  rw [← e₁]
  refine congrArg _ (Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [e₂, c₅]))
  have := conj_isMaximal H P
  obtain ⟨n, π, j, hπ, h, hj⟩ := exists_split_one (Nat.cast_ne_zero.2 hp.ne' : (p : 𝓞 E) ≠ 0)
    (P.map (H.bar : 𝓞 E →+* 𝓞 E))
  have t : ρ π x ^ p = 1 := by rw [← map_pow]; exact h₂ _ ⟨x, hx, rfl⟩ π hπ
  refine e₁.ge ((mem_kerSet_iff I hu hρ hco hp hpP h₁ h₂ x).2 ⟨ρ π x, ρ j x, (hρ.split h x).symm, ⟨t, ?_⟩,
    ⟨n + 1, fun a ha => ?_⟩, ⟨_, c₁ x hx j, rfl⟩⟩)
  · rintro _ ⟨y, hy, rfl⟩
    have ty : (y ^ p) ^ p = 1 := datum_tors hρ hpP h₂ ⟨y, hy, rfl⟩
    exact triv_symm I hu hp ty t ((triv_down I hu hp (by rw [pow_mul, ty]) t).1 (c₄ y hy _ (c₁ x hx π)))
  · rw [← hρ.2.1]
    exact c₃ x hx _ (hj a ha)
end GlobalTheory.HeckeCompare
