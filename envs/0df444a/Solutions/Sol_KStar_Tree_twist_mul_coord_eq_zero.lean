-- Prove2me | solution 1 for KStar.Tree.twist_mul_coord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:19.732831+00:00
-- url     : https://prove2.me/submissions/4426ba29-2220-4fc3-9f86-731ed887ab94

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TwistTrace
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_PolarTraceMulVecMulVecEq
import Theorems.Thm_KStar_Tree_polar_cocycle_conj_eq
import Theorems.Thm_KStar_Tree_polar_trace_mul_vecMulVec_eq
import Theorems.Thm_KStar_Tree_twist_smul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
open Matrix
namespace KStar.Tree
theorem _root_.solution : ∀ (Γ A : Type) [Group Γ] [CommRing A] [IsLocalRing A] (r : ℕ) (T T' : Γ →* Matrix (Fin r) (Fin r) A) (χ : Γ →* A) (c : Γ →* Γ) (J : GL (Fin r) A) (L : Subgroup Γ) (z : Γ) (d : Aˣ) (x y : Γ → Fin r → A), Submodule.span A (Set.range T) = ⊤ → (∀ g, T' (c g) = (J : Matrix (Fin r) (Fin r) A) * (χ g • T g) * ((J⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)) → L.Normal → (∀ h ∈ L, c h ∈ L) → (∀ h ∈ L, T h = 1 ∧ T' h = 1) → T z = (d : A) • 1 → T' z = ((d⁻¹ : Aˣ) : A) • 1 → T (c z) = ((d⁻¹ : Aˣ) : A) • 1 → T' (c z) = (d : A) • 1 → IsUnit ((d : A) ^ 2 - 1) → (∀ g h, x (g * h) = x g + (T g).mulVec (x h)) → (∀ g h, y (g * h) = y g + (T' g).mulVec (y h)) → (∀ h ∈ L, x h ⬝ᵥ y h = x (c h) ⬝ᵥ y (c h)) → ∀ g₀ : Γ, ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (χ g₀ ^ r - 1) * x h a * y h' b = 0 := by
  intro Γ A _ _ _ r T T' χ c J L z d x y hspan hT' hL hcL hTL hTz hT'z hTcz hT'cz hd hx hy hdiag
    g₀ h hh h' hh' a b
  have addx : ∀ u ∈ L, ∀ v, x (u * v) = x u + x v := by
    intro u hu v
    rw [hx, (hTL u hu).1, Matrix.one_mulVec]
  have addy : ∀ u ∈ L, ∀ v, y (u * v) = y u + y v := by
    intro u hu v
    rw [hy, (hTL u hu).2, Matrix.one_mulVec]
  have sym : ∀ u ∈ L, ∀ v ∈ L, x u ⬝ᵥ y v + x v ⬝ᵥ y u =
      x (c u) ⬝ᵥ y (c v) + x (c v) ⬝ᵥ y (c u) := by
    intro u hu v hv
    have e := hdiag (u * v) (L.mul_mem hu hv)
    rw [map_mul, addx u hu, addy u hu, addx (c u) (hcL u hu), addy (c u) (hcL u hu)] at e
    simp only [add_dotProduct, dotProduct_add] at e
    linear_combination e - hdiag u hu - hdiag v hv
  have hde : (d : A) * ((d⁻¹ : Aˣ) : A) = 1 := Units.mul_inv d
  have key : ∀ u ∈ L, ∀ v ∈ L, x v ⬝ᵥ y u = x (c u) ⬝ᵥ y (c v) := by
    intro u hu v hv
    have hzu : z * u * z⁻¹ ∈ L := hL.conj_mem u hu z
    have ex : x (z * u * z⁻¹) = (d : A) • x u := by
      rw [polar_cocycle_conj_eq T L hL (fun k hk => (hTL k hk).1) x hx z u hu, hTz,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have ey : y (z * u * z⁻¹) = ((d⁻¹ : Aˣ) : A) • y u := by
      rw [polar_cocycle_conj_eq T' L hL (fun k hk => (hTL k hk).2) y hy z u hu, hT'z,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have ecx : x (c (z * u * z⁻¹)) = ((d⁻¹ : Aˣ) : A) • x (c u) := by
      rw [map_mul, map_mul, map_inv,
        polar_cocycle_conj_eq T L hL (fun k hk => (hTL k hk).1) x hx (c z) (c u) (hcL u hu), hTcz,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have ecy : y (c (z * u * z⁻¹)) = (d : A) • y (c u) := by
      rw [map_mul, map_mul, map_inv,
        polar_cocycle_conj_eq T' L hL (fun k hk => (hTL k hk).2) y hy (c z) (c u) (hcL u hu), hT'cz,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have s1 := sym u hu v hv
    have s2 := sym (z * u * z⁻¹) hzu v hv
    rw [ex, ey, ecx, ecy] at s2
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at s2
    have hz : ((d : A) ^ 2 - 1) * (x v ⬝ᵥ y u - x (c u) ⬝ᵥ y (c v)) = 0 := by
      linear_combination (d : A) * ((d : A) * s1 - s2) +
        (x v ⬝ᵥ y u - x (c u) ⬝ᵥ y (c v)) * hde
    exact sub_eq_zero.mp ((hd.mul_right_eq_zero).mp hz)
  have main := twist_smul_eq_zero Γ A r T χ hspan (Matrix.vecMulVec (x h) (y h'))
    (((J⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) * Matrix.vecMulVec (y (c h)) (x (c h')) *
      (J : Matrix (Fin r) (Fin r) A)) ?_ g₀
  · have e := congrFun (congrFun main a) b
    simpa [Matrix.vecMulVec_apply, mul_assoc] using e
  · intro g
    have hgh : g * h * g⁻¹ ∈ L := hL.conj_mem h hh g
    rw [polar_trace_mul_vecMulVec_eq,
      ← polar_cocycle_conj_eq T L hL (fun k hk => (hTL k hk).1) x hx g h hh,
      key h' hh' _ hgh, map_mul, map_mul, map_inv,
      polar_cocycle_conj_eq T' L hL (fun k hk => (hTL k hk).2) y hy (c g) (c h) (hcL h hh),
      dotProduct_comm, ← polar_trace_mul_vecMulVec_eq, hT' g]
    set Jm := (J : Matrix (Fin r) (Fin r) A)
    set Ji := ((J⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)
    set W := Matrix.vecMulVec (y (c h)) (x (c h'))
    calc (Jm * (χ g • T g) * Ji * W).trace = (Jm * ((χ g • T g) * (Ji * W))).trace := by
          simp only [mul_assoc]
      _ = ((χ g • T g) * (Ji * W) * Jm).trace := Matrix.trace_mul_comm _ _
      _ = χ g * (T g * (Ji * W * Jm)).trace := by
          rw [mul_assoc, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
end KStar.Tree
