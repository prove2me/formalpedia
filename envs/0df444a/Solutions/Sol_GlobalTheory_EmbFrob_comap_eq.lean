-- Prove2me | solution 1 for GlobalTheory.EmbFrob.comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:37.401928+00:00
-- url     : https://prove2.me/submissions/791e01e8-6a18-4afb-ba82-7d006f9f0f4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPowOfFiniteField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.EmbFrob
open Polynomial
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
namespace GlobalTheory.EmbFrob
theorem _root_.solution {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [IsDedekindDomain OE]
    [CharZero OE] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
    (hp : ¬ IsUnit (p : R)) (w : Place p OE) {P : Ideal OE}
    (hP : ∀ Q : Ideal OE, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) (σ : OE →+* R)
    (hσ : extend σ w.e = 1) : (IsLocalRing.maximalIdeal R).comap σ = P := by
  by_contra hne
  have hpQ : (p : OE) ∈ (IsLocalRing.maximalIdeal R).comap σ := by
    rw [Ideal.mem_comap, map_natCast]; exact hp
  have hQ : ((IsLocalRing.maximalIdeal R).comap σ).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h => ?_
    rw [h, Ideal.mem_bot] at hpQ
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpQ
  let φ : w.Ow →+* R := Ideal.Quotient.lift _ (extend σ).toRingHom (by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    simp [hσ])
  have hφ : ∀ a, φ (w.toOw a) = σ a := fun a => by
    show extend (p := p) σ (1 ⊗ₜ a) = σ a
    simp
  have hle : ((IsLocalRing.maximalIdeal R).comap σ).map w.toOw ≤
      (IsLocalRing.maximalIdeal R).comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ]
    exact ha
  rw [hP _ hQ hne, top_le_iff] at hle
  exact Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle
end GlobalTheory.EmbFrob
