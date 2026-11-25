-- Prove2me | solution 1 for GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:53.877799+00:00
-- url     : https://prove2.me/submissions/7d78832a-861e-4e62-a8ed-f3d0c86e2430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulMemLattice
import Theorems.Thm_GlobalTheory_IntMulIntegerSmulMemLattice_exists_int_mul_eq_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntMulIntegerSmulMemLattice
open NumberField
namespace GlobalTheory.IntMulIntegerSmulMemLattice
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ (0 : ℤ) ∧ (m : 𝓞 E) • w ∈ Λ := by
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    rw [hΛ.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : ((a * b : ℤ) : 𝓞 E) • (x + y)
        = (b : 𝓞 E) • ((a : 𝓞 E) • x) + (a : 𝓞 E) • ((b : 𝓞 E) • y) := by
      rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : 𝓞 E) (a : 𝓞 E)]
    rw [h]
    exact Λ.add_mem (Λ.smul_mem _ hax) (Λ.smul_mem _ hby)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, r, hr⟩ := exists_int_mul_eq_integer c
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    have h : ((d * a : ℤ) : 𝓞 E) • (c • x) = r • ((a : 𝓞 E) • x) := by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_intCast, Algebra.algebraMap_self,
        RingHom.id_apply, Int.cast_mul, map_mul]
      have hr' : algebraMap (𝓞 E) E r = (d : E) * c := hr
      rw [hr', Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      ring
    rw [h]
    exact Λ.smul_mem _ hax
end GlobalTheory.IntMulIntegerSmulMemLattice
