-- Prove2me | solution 1 for GlobalTheory.addHom_zmod_pow_algebraMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:10.957896+00:00
-- url     : https://prove2.me/submissions/7cba6425-070e-4a0a-8638-4b4dabc56d7d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsZmodPowCoboundaryOfRationalCoboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] (l m : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] O] (A : O →+ ZMod (l ^ m)) (u : ℤ_[l]) (o : O) :
    A (algebraMap ℤ_[l] O u * o) = PadicInt.toZModPow m u * A o := by
  set v : ℕ := (PadicInt.toZModPow m u).val with hv

  have hk : u - (v : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hv, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨w, hw⟩ := hk
  have hu : u = (v : ℤ_[l]) + w * (l : ℤ_[l]) ^ m := by rw [hw]; ring
  have hkill : ∀ x : O, A ((l : O) ^ m * x) = 0 := by
    intro x
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hsplit : algebraMap ℤ_[l] O u * o
      = v • o + (l : O) ^ m * (algebraMap ℤ_[l] O w * o) := by
    rw [hu, map_add, map_mul, map_pow, map_natCast, map_natCast, nsmul_eq_mul]
    ring
  rw [hsplit, map_add, hkill, add_zero, map_nsmul, nsmul_eq_mul, hv, ZMod.natCast_zmod_val]
end GlobalTheory
