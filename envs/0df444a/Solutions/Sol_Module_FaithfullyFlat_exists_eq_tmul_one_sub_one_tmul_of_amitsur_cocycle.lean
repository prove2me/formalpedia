-- Prove2me | solution 1 for Module.FaithfullyFlat.exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c9a925fb-8bee-5cc7-acbc-50d4024a7e75

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle

set_option autoImplicit false

universe u v

open TensorProduct

namespace AmitsurDegreeOne

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

noncomputable abbrev d0 : S →ₗ[R] S ⊗[R] S := Algebra.TensorProduct.includeLeftSubRight R S

noncomputable def d1 : S ⊗[R] S →ₗ[R] S ⊗[R] (S ⊗[R] S) :=
  (Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)).toLinearMap -
    (Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)).toLinearMap +
    (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)).toLinearMap

theorem d1_apply (c : S ⊗[R] S) : d1 R S c =
    Algebra.TensorProduct.map (AlgHom.id R S) (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) c -
      Algebra.TensorProduct.map (AlgHom.id R S) (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) c +
      (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) c := rfl

theorem d1_tmul (a b : S) :
    d1 R S (a ⊗ₜ[R] b) = a ⊗ₜ[R] (b ⊗ₜ[R] 1) - a ⊗ₜ[R] (1 ⊗ₜ[R] b) + 1 ⊗ₜ[R] (a ⊗ₜ[R] b) := by
  rw [d1_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeRight_apply]
  rfl

theorem d0_apply (s : S) : d0 R S s = s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s := rfl

theorem d1_comp_d0 : d1 R S ∘ₗ d0 R S = 0 := by
  ext s
  rw [LinearMap.comp_apply, d0_apply, map_sub, d1_tmul, d1_tmul, LinearMap.zero_apply]
  abel

noncomputable def h1 : S ⊗[R] (S ⊗[R] S) →ₗ[R] S ⊗[R] S :=
  (LinearMap.mul' R S).rTensor S ∘ₗ (TensorProduct.assoc R S S S).symm.toLinearMap

noncomputable def h2 : S ⊗[R] (S ⊗[R] (S ⊗[R] S)) →ₗ[R] S ⊗[R] (S ⊗[R] S) :=
  (LinearMap.mul' R S).rTensor (S ⊗[R] S) ∘ₗ (TensorProduct.assoc R S S (S ⊗[R] S)).symm.toLinearMap

theorem h1_tmul (t a b : S) : h1 R S (t ⊗ₜ[R] (a ⊗ₜ[R] b)) = (t * a) ⊗ₜ[R] b := by
  simp [h1]

theorem h2_tmul (t a : S) (w : S ⊗[R] S) : h2 R S (t ⊗ₜ[R] (a ⊗ₜ[R] w)) = (t * a) ⊗ₜ[R] w := by
  simp [h2]

theorem homotopy :
    h2 R S ∘ₗ (d1 R S).lTensor S - (d0 R S).lTensor S ∘ₗ h1 R S = LinearMap.id := by
  apply TensorProduct.ext'
  intro t w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul, d1_tmul,
      tmul_add, tmul_sub, map_add, map_sub, h2_tmul, h2_tmul, h2_tmul, h1_tmul, LinearMap.lTensor_tmul,
      d0_apply, tmul_sub, mul_one, LinearMap.id_apply]
    abel
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

theorem exact_lTensor : Function.Exact ((d0 R S).lTensor S) ((d1 R S).lTensor S) := by
  intro x
  constructor
  · intro hx
    have key := LinearMap.congr_fun (homotopy R S) x
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hx, map_zero, zero_sub,
      LinearMap.id_apply] at key
    exact ⟨-(h1 R S x), by rw [map_neg]; exact key⟩
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, d1_comp_d0, LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem exact [Module.FaithfullyFlat R S] : Function.Exact (d0 R S) (d1 R S) :=
  Module.FaithfullyFlat.lTensor_reflects_exact R S _ _ (exact_lTensor R S)

end AmitsurDegreeOne

theorem solution
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (c : S ⊗[R] S)
    (hc : Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) c +
          (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) c =
        Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) c) :
    ∃ s : S, c = s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s := by
  have hd : AmitsurDegreeOne.d1 R S c = 0 := by
    rw [AmitsurDegreeOne.d1_apply, sub_add_eq_add_sub, hc, sub_self]
  obtain ⟨s, hs⟩ := ((AmitsurDegreeOne.exact R S) c).mp hd
  exact ⟨s, hs.symm⟩

end S_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle
end P2MW
export P2MW.S_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle (solution)
