-- Prove2me | solution 1 for KrohnRhodes.LocalDivisor.localDivides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:54:11.967499+00:00
-- url     : https://prove2.me/submissions/e0d5703d-b660-4a77-bc7e-c1ecc65e27d6

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor

set_option autoImplicit true
@[expose] public section
public section
open FreeMonoid Computability Pointwise
universe u
variable {α : Type u}
open KrohnRhodes
open KrohnRhodes.LocalDivisor
variable {M : Type*} [Monoid M] {c : M}
namespace KrohnRhodes.LocalDivisor
theorem _root_.solution : MonoidDivides (LocalDivisor M c) M := by
  -- The submonoid S = {t | c*t ∈ Mc} = {t | ∃ b, c*t = b*c}.
  let S : Submonoid M :=
    { carrier := {t : M | ∃ b : M, c * t = b * c}
      one_mem' := ⟨1, by rw [mul_one, one_mul]⟩
      mul_mem' := by
        rintro t t' ⟨b, hb⟩ ⟨b', hb'⟩
        -- c*(t*t') = (c*t)*t' = (b*c)*t' = b*(c*t') = b*(b'*c) = (b*b')*c
        refine ⟨b * b', ?_⟩
        rw [← mul_assoc, hb, mul_assoc, hb', ← mul_assoc, mul_assoc] }
  -- The map t ↦ c*t lands in LocalDivisor M c.
  have hmem : ∀ t : S, (∃ a : M, c * t.1 = c * a) ∧ (∃ b : M, c * t.1 = b * c) :=
    fun t => ⟨⟨t.1, rfl⟩, t.2⟩
  let γ : S → LocalDivisor M c := fun t => ⟨c * t.1, hmem t⟩
  have hγval : ∀ t : S, (γ t).val = c * t.1 := fun _ => rfl
  refine ⟨S, ?_, ?_⟩
  · refine { toFun := γ, map_one' := ?_, map_mul' := ?_ }
    · apply LocalDivisor.ext
      rw [hγval, one_val]; exact mul_one c
    · intro t t'
      apply LocalDivisor.ext
      -- γ(t*t').val = c*(t.1*t'.1); (γt * γt').val = (γt).val * t'.1 (since (γt').val = c*t'.1)
      have h1 : (γ (t * t')).val = c * (t.1 * t'.1) := hγval (t * t')
      have h2 : (γ t * γ t').val = c * t.1 * t'.1 := by
        rw [mul_val_of_eq (γ t) (γ t') (hγval t'), hγval t]
      rw [h1, h2, mul_assoc]
  · -- surjectivity: x ∈ cM∩Mc, x = c*a (witness of mem_left); a ∈ S and γ(a)=x.
    intro x
    obtain ⟨a, ha⟩ := x.mem_left
    obtain ⟨b, hb⟩ := x.mem_right
    refine ⟨⟨a, ⟨b, by rw [← ha, hb]⟩⟩, ?_⟩
    apply LocalDivisor.ext
    show c * a = x.val
    exact ha.symm
end KrohnRhodes.LocalDivisor
