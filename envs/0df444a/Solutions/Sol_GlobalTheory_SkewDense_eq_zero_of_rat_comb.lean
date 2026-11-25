-- Prove2me | solution 1 for GlobalTheory.SkewDense.eq_zero_of_rat_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:11:15.401528+00:00
-- url     : https://prove2.me/submissions/c9c9ba77-6d55-41e9-ae84-63484c507869

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian

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
open NumberField
open GlobalTheory GlobalTheory.SkewDense
namespace GlobalTheory.SkewDense
theorem _root_.solution {P G : Type} [Fintype G] (r : G → P → ℂ) (Q : MvPolynomial P ℂ)
    (hrat : ∀ t : G → ℚ, MvPolynomial.eval (fun p => ∑ g, (t g : ℂ) * r g p) Q = 0)
    (hspan : ∀ y : P → ℂ, ∃ z : G → ℂ, y = fun p => ∑ g, z g * r g p) : Q = 0 := by
  classical
  let Q' := MvPolynomial.bind₁ (fun p => ∑ J, MvPolynomial.X J * MvPolynomial.C (r J p)) Q
  have heval : ∀ z, MvPolynomial.eval z Q' = MvPolynomial.eval (fun p => ∑ J, z J * r J p) Q := by
    intro z
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) z Q' = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext p
    simp [map_sum]
  have hQ' : Q' = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Rat.cast : ℚ → ℂ))
      (fun _ => Set.infinite_range_of_injective Rat.cast_injective) fun z hz => ?_
    choose t ht using fun J => hz J (Set.mem_univ _)
    have hz' : z = fun J => (t J : ℂ) := by funext J; exact (ht J).symm
    rw [heval, hz', hrat, map_zero]
  refine MvPolynomial.funext fun y => ?_
  obtain ⟨z, rfl⟩ := hspan y
  rw [← heval, hQ', map_zero, map_zero]
end GlobalTheory.SkewDense
