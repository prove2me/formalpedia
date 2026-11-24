-- Prove2me | solution 1 for GlobalTheory.derivation_normalise_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:33:36.696898+00:00
-- url     : https://prove2.me/submissions/6e6ab98e-2dbf-461c-80d4-947268c69a67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationsDualToFamilyOfNilpotentAug

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by
  intro k A _ _ _ ε hnil d x D hD
  let M : Matrix (Fin d) (Fin d) A := Matrix.of fun i j => D i (x j)
  have hε : (ε : A →+* k).mapMatrix M = 1 := by
    ext i j
    simp [M, hD, Matrix.one_apply]
  have hdet : ε M.det = 1 := by
    have h := RingHom.map_det (ε : A →+* k) M
    rw [hε, Matrix.det_one] at h
    simpa using h
  have hunit : IsUnit M.det := by
    obtain ⟨n, hn⟩ := hnil
    have hmem : M.det - 1 ∈ RingHom.ker ε := by simp [RingHom.mem_ker, hdet]
    have hN : IsNilpotent (M.det - 1) := ⟨n, by
      have h : (M.det - 1) ^ n ∈ (RingHom.ker ε) ^ n := Ideal.pow_mem_pow hmem n
      rw [hn] at h
      simpa using h⟩
    have h := hN.isUnit_one_add
    simpa using h
  refine ⟨fun i => ∑ l, (M⁻¹ i l) • D l, fun i j => ?_⟩
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have h := congrFun (congrFun hinv i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  have hev := map_sum (AddMonoidHom.mk' (fun δ : Derivation k A A => δ (x j)) (fun a b => rfl))
    (fun l => M⁻¹ i l • D l) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hev
  rw [hev]
  simp [M]
end GlobalTheory
