-- Prove2me | solution 1 for HeckeEis.exists_iota0_inv_mul_mem_heckeUpper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0da70ff0-136c-565d-9777-1e123e180cb1

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_IharaIota
import Theorems.Thm_Int_exists_modEq_and_modEq_and_isCoprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "heckeUpper mem_heckeUpper"
p2m_open "HeckeEis"
namespace Sh4
open CongruenceSubgroup Matrix
open scoped MatrixGroups

theorem iota0_inv_mul_apply (N q : ℕ) (h : Gamma0 (N * q)) (γ : Gamma0 N) :
    (((Ihara.ι₀ N q h)⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) 0 1 =
      ((h : SL(2, ℤ)) 1 1) * ((γ : SL(2, ℤ)) 0 1) -
        ((h : SL(2, ℤ)) 0 1) * ((γ : SL(2, ℤ)) 1 1) := by
  have h1 : (((Ihara.ι₀ N q h)⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) =
      ((h : SL(2, ℤ)))⁻¹ * (γ : SL(2, ℤ)) := by
    push_cast [Ihara.coe_iota0]
    rfl
  rw [h1]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

def gamma0Of (M : ℕ) (a b k d : ℤ) (hdet : a * d + k * ((M : ℤ) * b) = 1) : Gamma0 M :=
  ⟨⟨!![a, b; -(k * (M : ℤ)), d], by rw [Matrix.det_fin_two_of]; linear_combination hdet⟩, by
    rw [Gamma0_mem]
    show ((-(k * (M : ℤ)) : ℤ) : ZMod M) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨-k, by ring⟩⟩

@[scoped simp] theorem gamma0Of_apply_zero_one (M : ℕ) (a b k d : ℤ) (hdet : a * d + k * ((M : ℤ) * b) = 1) :
    ((gamma0Of M a b k d hdet : Gamma0 M) : SL(2, ℤ)) 0 1 = b := rfl

@[scoped simp] theorem gamma0Of_apply_one_one (M : ℕ) (a b k d : ℤ) (hdet : a * d + k * ((M : ℤ) * b) = 1) :
    ((gamma0Of M a b k d hdet : Gamma0 M) : SL(2, ℤ)) 1 1 = d := rfl

theorem exists_iota0_inv_mul_mem_heckeUpper (N p ℓ : ℕ) (hℓ : Nat.Coprime ℓ (N * p)) (γ : Gamma0 N) :
    ∃ h : Gamma0 (N * p), (Ihara.ι₀ N p h)⁻¹ * γ ∈ heckeUpper N ℓ := by

  set g00 : ℤ := (γ : SL(2, ℤ)) 0 0
  set g01 : ℤ := (γ : SL(2, ℤ)) 0 1
  set g10 : ℤ := (γ : SL(2, ℤ)) 1 0
  set g11 : ℤ := (γ : SL(2, ℤ)) 1 1
  have hdet : g00 * g11 - g01 * g10 = 1 := by
    rw [← Matrix.det_fin_two]; exact (γ : SL(2, ℤ)).2

  have hcop : IsCoprime (ℓ : ℤ) ((N * p : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hℓ
  obtain ⟨u, v, huv⟩ := hcop
  set M : ℤ := ((N * p : ℕ) : ℤ) with hM

  set d0 : ℤ := g11 * (v * M) + u * (ℓ : ℤ) with hd0

  have h3 : ∃ x y z : ℤ, x * g01 + y * d0 + z * ((ℓ : ℤ) * M) = 1 := by
    refine ⟨-g10 * (v * M), g00 * (v * M) + u * (ℓ : ℤ), u * v * (g00 - 1) * (g11 - 1), ?_⟩
    linear_combination (v * M) * hdet + (M * g00 * g11 * v + (ℓ : ℤ) * u + 1) * huv
  obtain ⟨b, d, hb, hd, hbd⟩ := Int.exists_modEq_and_modEq_and_isCoprime h3

  have hdM : IsCoprime d M := by
    have hd1 : d ≡ 1 [ZMOD M] := by
      have h1 : d0 ≡ 1 [ZMOD M] := by
        have : d0 - 1 = M * (g11 * v - v) := by
          rw [hd0]; linear_combination huv
        exact (Int.modEq_iff_dvd.mpr ⟨-(g11 * v - v), by linear_combination (-1 : ℤ) * this⟩)
      exact (hd.of_mul_left _).trans h1
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hd1.symm

    exact ⟨1, -k, by linear_combination hk⟩
  have hcop2 : IsCoprime d (M * b) := hdM.mul_right hbd.symm
  obtain ⟨a', k, hak⟩ := hcop2
  refine ⟨gamma0Of (N * p) a' b k d (by rw [← hM]; linear_combination hak), ?_⟩
  rw [mem_heckeUpper, iota0_inv_mul_apply, gamma0Of_apply_one_one, gamma0Of_apply_zero_one]

  have hdℓ : d ≡ g11 [ZMOD (ℓ : ℤ)] := by
    have h1 : d0 ≡ g11 [ZMOD (ℓ : ℤ)] := by
      have : d0 - g11 = (ℓ : ℤ) * (u - g11 * u) := by
        rw [hd0]; linear_combination g11 * huv
      exact Int.modEq_iff_dvd.mpr ⟨-(u - g11 * u), by linear_combination (-1 : ℤ) * this⟩
    exact (hd.of_mul_right _).trans h1
  have hbℓ : b ≡ g01 [ZMOD (ℓ : ℤ)] := hb.of_mul_right _
  have : d * g01 - b * g11 ≡ g11 * g01 - g01 * g11 [ZMOD (ℓ : ℤ)] :=
    (hdℓ.mul_right _).sub (hbℓ.mul_right _)
  rw [show g11 * g01 - g01 * g11 = 0 by ring] at this
  exact (Int.modEq_zero_iff_dvd.mp this)

end Sh4
p2m_reactivate "P2MW.S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper.HeckeEis.Sh4"
end HeckeEis
p2m_reactivate "P2MW.S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper.HeckeEis.Sh4 P2MW.S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper.HeckeEis"

end
p2m_reactivate "P2MW.S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper.HeckeEis.Sh4 P2MW.S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper.HeckeEis"

theorem solution (N p ℓ : ℕ) (hℓ : Nat.Coprime ℓ (N * p))
    (γ : CongruenceSubgroup.Gamma0 N) :
    ∃ h : CongruenceSubgroup.Gamma0 (N * p), (Ihara.ι₀ N p h)⁻¹ * γ ∈ HeckeEis.heckeUpper N ℓ :=
  HeckeEis.Sh4.exists_iota0_inv_mul_mem_heckeUpper N p ℓ hℓ γ

end S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper
end P2MW
export P2MW.S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper (solution)
