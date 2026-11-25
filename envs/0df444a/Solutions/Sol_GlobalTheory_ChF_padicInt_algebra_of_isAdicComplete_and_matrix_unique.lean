-- Prove2me | solution 1 for GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:07.665831+00:00
-- url     : https://prove2.me/submissions/53af8794-5d77-4b0c-a60e-6affba5900b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicIntAlgebraOfIsAdicCompleteMatrixUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.ChF
private theorem nonempty_padicInt_ringHom (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (I : Ideal O) [IsAdicComplete I O] (hp : (p : O) ∈ I) : Nonempty (ℤ_[p] →+* O) := by
  have hd : ∀ n : ℕ, ringChar (O ⧸ I ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk (I ^ n)), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow hp n
  refine ⟨IsAdicComplete.liftRingHom I
    (fun n => (ZMod.castHom (hd n) (O ⧸ I ^ n)).comp (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact RingHom.ext_zmod _ _
private theorem padicInt_ringHom_matrix_ext (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (n : ℕ)
    (f g : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]) : f c = g c := by
  ext i j
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {(p : O)}) inferInstance _ fun k => ?_
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k c)
  have hc : c = (c.appr k : ℤ_[p]) + ((p ^ k : ℕ) : ℤ_[p]) * d := by
    rw [Nat.cast_pow, ← hd]; ring
  have h : f c - g c = (p ^ k : ℕ) • (f d - g d) := by
    rw [hc]
    simp only [map_add, map_mul, map_natCast, nsmul_eq_mul, mul_sub]
    abel
  have h' : f c i j - g c i j = (p : O) ^ k * (f d i j - g d i j) := by
    have := congrFun (congrFun h i) j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sub_apply, nsmul_eq_mul, Nat.cast_pow] at this
    exact this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
end GlobalTheory.ChF
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O],
      Nonempty (Algebra ℤ_[p] O) ∧ ∀ [Algebra ℤ_[p] O] (n : ℕ)
        (f : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]),
        f c = algebraMap ℤ_[p] O c • (1 : Matrix (Fin n) (Fin n) O) := by
  intro p _ O _ _
  refine ⟨?_, fun n f c => ?_⟩
  · obtain ⟨φ⟩ := nonempty_padicInt_ringHom p O _ (Ideal.mem_span_singleton_self _)
    exact ⟨φ.toAlgebra⟩
  · rw [padicInt_ringHom_matrix_ext p O n f
      ((algebraMap O (Matrix (Fin n) (Fin n) O)).comp (algebraMap ℤ_[p] O)) c,
      RingHom.comp_apply, Algebra.algebraMap_eq_smul_one (A := Matrix (Fin n) (Fin n) O)]
end GlobalTheory.ChF
