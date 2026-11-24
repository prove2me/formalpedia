-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormZero.card_zero_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:08:10.483441+00:00
-- url     : https://prove2.me/submissions/02647eb1-af56-44d1-8319-63413b73ee63

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_finite_of_resAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_card_fx
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_card_axes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormZero
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormZero
theorem _root_.solution (h : ResAlg E τ q ε) {e : E} (he : e * e = e) (hτ : τ e = 1 - e) :
    Nat.card {a : E // a * τ a = 0} + 1 = 2 * q := by
  have hτf : τ (1 - e) = e := by rw [map_sub, map_one, hτ]; ring
  let g : Fx τ × Fx τ → E := fun p => (p.1 : E) * e + (p.2 : E) * (1 - e)
  have hnorm : ∀ p, g p * τ (g p) = (p.1 : E) * (p.2 : E) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    show (x * e + y * (1 - e)) * τ (x * e + y * (1 - e)) = x * y
    rw [map_add, map_mul, map_mul, hx, hy, hτ, hτf]
    linear_combination (2 * x * y - x ^ 2 - y ^ 2) * he
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      have h1 : x * e + y * (1 - e) = x' * e + y' * (1 - e) := hxy
      have h2 : x * (1 - e) + y * e = x' * (1 - e) + y' * e := by
        have := congrArg τ h1
        simpa only [map_add, map_mul, hx, hy, hx', hy', hτ, hτf] using this
      have hxe : x * e = x' * e := by
        linear_combination e * h1 + (y - y' - x + x') * he
      have hye : y * e = y' * e := by
        linear_combination e * h2 + (x - x' - y + y') * he
      have h5 : x = x' := by linear_combination h2 + hxe - hye
      have h6 : y = y' := by linear_combination h1 - hxe + hye
      subst h5 h6
      rfl
    · intro a
      refine ⟨(⟨a * e + τ a * (1 - e), ?_⟩, ⟨a * (1 - e) + τ a * e, ?_⟩), ?_⟩
      · rw [map_add, map_mul, map_mul, h.inv, hτ, hτf]; ring
      · rw [map_add, map_mul, map_mul, h.inv, hτ, hτf]; ring
      · show (a * e + τ a * (1 - e)) * e + (a * (1 - e) + τ a * e) * (1 - e) = a
        linear_combination (2 * a - 2 * τ a) * he
  have hz : ∀ p : Fx τ × Fx τ, (p.1 = zeroFx τ ∨ p.2 = zeroFx τ) ↔ g p * τ (g p) = 0 := by
    intro p
    rw [hnorm]
    constructor
    · rintro (h0 | h0)
      · rw [h0]; simp [zeroFx]
      · rw [h0]; simp [zeroFx]
    · intro h0
      by_cases hx : (p.1 : E) = 0
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext ((h.fixedUnit _ p.1.2 hx).mul_right_eq_zero.1 h0))
  have hcard : Nat.card {p : Fx τ × Fx τ // p.1 = zeroFx τ ∨ p.2 = zeroFx τ}
      = Nat.card {a : E // a * τ a = 0} :=
    Nat.card_congr ((Equiv.ofBijective g hg).subtypeEquiv hz)
  haveI := finite_of_resAlg h
  rw [← hcard, card_axes, card_fx h]
end GlobalTheory.CompanionTheory.UnrDens.NormZero
