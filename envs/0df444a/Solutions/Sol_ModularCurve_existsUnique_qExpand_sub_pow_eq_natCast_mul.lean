-- Prove2me | solution 1 for ModularCurve.existsUnique_qExpand_sub_pow_eq_natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c7698150-590b-50ae-9a61-69478f5d649b

import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "laurentMap laurentMap_coeff laurentMap_qExpand qExpand pow_char_eq_map_frobenius_qExpand"
namespace K2a0
p2m_open "ModularCurve"

theorem pow_eq_qExpand_zmod (p : ℕ) [Fact p.Prime] (s : LaurentSeries (ZMod p)) :
    s ^ p = qExpand (ZMod p) p s := by
  rw [pow_char_eq_map_frobenius_qExpand p s, ZMod.frobenius_zmod]
  ext k
  simp

theorem laurentMap_qExpand_sub_pow (p : ℕ) [Fact p.Prime] (f : LaurentSeries ℤ) :
    laurentMap (Int.castRingHom (ZMod p)) (qExpand ℤ p f - f ^ p) = 0 := by
  rw [map_sub, map_pow, laurentMap_qExpand, pow_eq_qExpand_zmod, sub_self]

theorem main (q : ℕ) [Fact q.Prime] (f : LaurentSeries ℤ) :
    ∃! S : LaurentSeries ℤ, qExpand ℤ q f - f ^ q = (q : LaurentSeries ℤ) * S := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  set g : LaurentSeries ℤ := qExpand ℤ q f - f ^ q with hg

  have hdvd : ∀ k : ℤ, (q : ℤ) ∣ g.coeff k := by
    intro k
    have h := congrArg (fun x : LaurentSeries (ZMod q) => x.coeff k) (laurentMap_qExpand_sub_pow q f)
    simp only [laurentMap_coeff, HahnSeries.coeff_zero, eq_intCast] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h

  let S : LaurentSeries ℤ := g.map (⟨fun n : ℤ => n / (q : ℤ), by simp⟩ : ZeroHom ℤ ℤ)
  have hS : ∀ k : ℤ, S.coeff k = g.coeff k / (q : ℤ) := fun k => rfl
  have hcast : ((q : LaurentSeries ℤ)) = HahnSeries.C (q : ℤ) := by
    rw [map_natCast]
  have hqS : (q : LaurentSeries ℤ) * S = g := by
    ext k
    rw [hcast, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hS, smul_eq_mul]
    exact Int.mul_ediv_cancel' (hdvd k)
  refine ⟨S, hqS.symm, ?_⟩
  intro S' hS'
  have hne : (q : LaurentSeries ℤ) ≠ 0 := by
    rw [hcast]
    intro h
    exact hq0 (HahnSeries.C_injective (h.trans HahnSeries.C_zero.symm))
  apply mul_left_cancel₀ hne
  rw [← hS', hqS]

end ModularCurve.K2a0

theorem solution (q : ℕ) [Fact q.Prime] (f : LaurentSeries ℤ) :
    ∃! S : LaurentSeries ℤ, qExpand ℤ q f - f ^ q = (q : LaurentSeries ℤ) * S :=
  ModularCurve.K2a0.main q f

end S_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul
end P2MW
export P2MW.S_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul (solution)
