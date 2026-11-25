-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.exists_eq_mul_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:55.310455+00:00
-- url     : https://prove2.me/submissions/8fd85b8d-1b5f-48ac-b7a0-add15ad99cba

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Theorems.Thm_GroundTheory_Global_Cyclotomic_toPadicInt_surjective
import Theorems.Thm_GroundTheory_Global_Cyclotomic_mem_of_forall_toPadicInt
import Theorems.Thm_GroundTheory_Global_Cyclotomic_ext_toPadicInt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂))
    (hne : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h ≠ 0) :
    ∃ g : ℤ̂, (∀ q : Nat.Primes, toPadicInt q g ≠ 0) ∧ ∀ y, y ∈ H ↔ ∃ a, y = g * a := by
  let I : Ideal ℤ̂ := idealOfIsClosed H hH
  have hI : ∀ q : Nat.Primes, I.map (toPadicInt q) ≠ ⊥ := by
    intro q hbot
    obtain ⟨h, hh, hh0⟩ := hne q
    apply hh0
    have : toPadicInt q h ∈ I.map (toPadicInt q) := Ideal.mem_map_of_mem _ hh
    rwa [hbot, Ideal.mem_bot] at this
  choose v hv using fun q => PadicInt.ideal_eq_span_pow_p (hI q)
  have hmem : ∀ (q : Nat.Primes) (z : ℤ_[q]), (∃ h ∈ H, toPadicInt q h = z) ↔ (q : ℤ_[q]) ^ v q ∣ z := by
    intro q z
    rw [← Ideal.mem_span_singleton, ← hv q, Ideal.mem_map_iff_of_surjective _
      (toPadicInt_surjective q)]
    rfl
  let g : ℤ̂ := ofPadics fun q => (q : ℤ_[q]) ^ v q
  have hg : ∀ q : Nat.Primes, toPadicInt q g = (q : ℤ_[q]) ^ v q := fun q =>
    congrFun (toPadics_ofPadics _) q
  refine ⟨g, fun q => by rw [hg]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 q.2.ne_zero), ?_⟩
  intro y
  constructor
  · intro hy
    choose t ht using fun q => (hmem q (toPadicInt q y)).1 ⟨y, hy, rfl⟩
    refine ⟨ofPadics t, ext_toPadicInt fun q => ?_⟩
    rw [map_mul, hg, ht q]
    congr 1
    exact (congrFun (toPadics_ofPadics t) q).symm
  · rintro ⟨a, rfl⟩
    have hgH : g ∈ H := mem_of_forall_toPadicInt H hH fun q =>
      (hmem q _).2 (by rw [hg])
    rw [mul_comm]
    exact mul_mem_of_isClosed' H hH hgH a
end GroundTheory.Global.Cyclotomic
