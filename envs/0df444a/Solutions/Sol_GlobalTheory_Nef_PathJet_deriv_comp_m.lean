-- Prove2me | solution 1 for GlobalTheory.Nef.PathJet.deriv_comp_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:02:53.888723+00:00
-- url     : https://prove2.me/submissions/86600872-01d2-4aae-80a7-9a3a4ac85767

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PathJet
open PowerSeries
variable {A B R : Type} [CommRing A] [CommRing B] [CommRing R]
namespace GlobalTheory.Nef.PathJet
theorem _root_.solution (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (E : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (hE : ∀ f g, E (f * g) = β (ε f) * E g + β (ε g) * E f) (hEπ : ∀ a, E (π a) = 0) (f : A) :
    E (m f) = 2 * E f := by
  have hsq : ∀ x ∈ RingHom.ker ε ^ 2, E x = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [RingHom.mem_ker] at ha hb
      rw [hE, ha, hb]; simp
    · rw [map_add, ha, hb, add_zero]
  have hk : f - π (ε f) ∈ RingHom.ker ε := by
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply ε π, hεπ, RingHom.id_apply, sub_self]
  have h1 : m f = π (ε f) + (m (f - π (ε f)) - 2 * (f - π (ε f))) + (f - π (ε f)) + (f - π (ε f)) := by
    have : m (π (ε f)) = π (ε f) := by rw [← RingHom.comp_apply m π, hmπ]
    rw [map_sub, this]; ring
  have h2 : f = π (ε f) + (f - π (ε f)) := by ring
  rw [h1, map_add, map_add, map_add, hEπ, hsq _ (hm2 _ hk)]
  conv_rhs => rw [h2, map_add, hEπ]
  ring
end GlobalTheory.Nef.PathJet
