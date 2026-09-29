-- Prove2me | solution 1 for ModularCurve.ssJSet_eq_image_algebraMap_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/440672b0-75ca-53c1-afbf-3f9925dd4066

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_ssJSet_eq_ssJSetHasse
import Theorems.Thm_ModularCurve_ssJSetHasse_eq_image_legendreJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed.ModularCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "ssJSet mem_ssJSet_iff ssJSet_eq_ssJSetHasse ssJSetHasse ssJSetHasse_eq_image_legendreJ legendreJ"
namespace HSSBody
p2m_open "ModularCurve"

theorem ssJSet_eq_of_decEq (p : ℕ) (L : Type*) [Field L] (i₁ i₂ : DecidableEq L) :
    @ssJSet p L _ i₁ = @ssJSet p L _ i₂ := by
  rw [Subsingleton.elim i₁ i₂]

section CharTwo
variable (L : Type*) [Field L] [IsAlgClosed L] [CharP L 2]

theorem two_eq_zero' : (2 : L) = 0 := by
  have := CharP.cast_eq_zero L 2
  exact_mod_cast this

theorem neg_eq' (y : L) : -y = y := by linear_combination (-y) * two_eq_zero' L

theorem a₁_eq_zero_of_j_eq_zero (W : WeierstrassCurve L) [W.IsElliptic] (hj : W.j = 0) : W.a₁ = 0 := by
  have h2 := two_eq_zero' L
  have hc4 : W.c₄ = 0 := by
    rw [WeierstrassCurve.j] at hj
    have h : W.Δ = 0 ∨ W.c₄ = 0 := by simpa using hj
    rcases h with h | h
    · exact absurd h (by rw [← W.coe_Δ']; exact W.Δ'.ne_zero)
    · exact h
  have : W.c₄ = W.a₁ ^ 4 := by
    rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    linear_combination (4 * W.a₁ ^ 2 * W.a₂ + 8 * W.a₂ ^ 2 - 24 * W.a₄ - 12 * W.a₁ * W.a₃) * h2
  rw [this] at hc4
  exact pow_eq_zero_iff (by norm_num) |>.mp hc4

theorem Δ_eq_zero_of_a₁_a₃ (W : WeierstrassCurve L) (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) : W.Δ = 0 := by
  have h2 := two_eq_zero' L
  rw [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, h1, h3]
  linear_combination (-(8 * W.a₂ ^ 2) * (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) - 32 * W.a₄ ^ 3 - 216 * W.a₆ ^ 2
    + 144 * W.a₂ * W.a₄ * W.a₆) * h2

theorem ssJSet_two (i : DecidableEq L) : @ssJSet 2 L _ i = {0} := by
  have h2 := two_eq_zero' L
  ext j
  rw [Set.mem_singleton_iff, mem_ssJSet_iff]
  constructor
  · intro hss
    by_contra hj

    have h1728 : (1728 : L) = 0 := by linear_combination 864 * h2
    letI := i
    have hW : WeierstrassCurve.ofJ j = WeierstrassCurve.ofJNe0Or1728 j :=
      WeierstrassCurve.ofJ_ne_0_ne_1728 j hj (by rw [h1728]; exact hj)
    have ha3 : (WeierstrassCurve.ofJ j).a₃ = 0 := by rw [hW]; rfl
    have ha6 : (WeierstrassCurve.ofJ j).a₆ = -(j - 1728) ^ 5 := by rw [hW]; rfl
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (-(j - 1728) ^ 5 : L) two_pos
    have heq : (WeierstrassCurve.ofJ j).toAffine.Equation 0 y := by
      rw [WeierstrassCurve.Affine.equation_iff]
      change y ^ 2 + (WeierstrassCurve.ofJ j).a₁ * 0 * y + (WeierstrassCurve.ofJ j).a₃ * y =
        0 ^ 3 + (WeierstrassCurve.ofJ j).a₂ * 0 ^ 2 + (WeierstrassCurve.ofJ j).a₄ * 0 + (WeierstrassCurve.ofJ j).a₆
      rw [ha3, ha6, ← hy]
      ring
    have hnon : (WeierstrassCurve.ofJ j).toAffine.Nonsingular 0 y :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq
    have hnegY : y = (WeierstrassCurve.ofJ j).toAffine.negY 0 y := by
      rw [WeierstrassCurve.Affine.negY]
      change y = -y - (WeierstrassCurve.ofJ j).a₁ * 0 - (WeierstrassCurve.ofJ j).a₃
      rw [ha3]
      linear_combination y * h2
    let P : (WeierstrassCurve.ofJ j).toAffine.Point := WeierstrassCurve.Affine.Point.some _ _ hnon
    have hP : (2 : ℕ) • P = 0 := by
      rw [two_nsmul]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hnegY
    have := hss (WeierstrassCurve.ofJ j) (WeierstrassCurve.ofJ_j j) P hP
    exact WeierstrassCurve.Affine.Point.some_ne_zero hnon this
  · rintro rfl W _ hj P hP
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · exfalso
      have h1 := a₁_eq_zero_of_j_eq_zero L W hj
      by_cases hy : y = W.toAffine.negY x y
      ·
        have h3 : W.a₃ = 0 := by
          rw [WeierstrassCurve.Affine.negY] at hy
          change y = -y - W.a₁ * x - W.a₃ at hy
          rw [h1] at hy
          linear_combination hy + (-y) * h2
        exact W.Δ'.ne_zero (by exact_mod_cast Δ_eq_zero_of_a₁_a₃ L W h1 h3)
      · rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy] at hP
        exact WeierstrassCurve.Affine.Point.some_ne_zero _ hP

end CharTwo

section Odd
variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]
  (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K] [CharP K p]

theorem legendreJ_algebraMap (t : k) : legendreJ (algebraMap k K t) = algebraMap k K (legendreJ t) := by
  simp only [legendreJ, map_div₀, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat]

theorem deuring_map_ne_zero : (deuringPolynomial p).map (Int.castRingHom k) ≠ 0 := by
  intro h
  have hc := congrArg (fun q : k[X] => q.coeff ((p - 1) / 2)) h
  simp only [Polynomial.coeff_map, coeff_zero] at hc
  rw [deuringPolynomial, finsetSum_coeff] at hc
  rw [Finset.sum_eq_single ((p - 1) / 2)] at hc
  · simp [coeff_C_mul, coeff_X_pow] at hc
  · intro b _ hb
    rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
  · intro h'
    exfalso
    exact h' (Finset.mem_range.mpr (Nat.lt_succ_self _))

theorem roots_eq_image :
    {t : K | ((deuringPolynomial p).map (Int.castRingHom K)).eval t = 0} =
      algebraMap k K '' {t : k | ((deuringPolynomial p).map (Int.castRingHom k)).eval t = 0} := by
  have hmap : (deuringPolynomial p).map (Int.castRingHom K) =
      ((deuringPolynomial p).map (Int.castRingHom k)).map (algebraMap k K) := by
    rw [Polynomial.map_map]
    congr 1
    ext n
    simp
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro ht

    have halg : IsAlgebraic k t := by
      refine ⟨(deuringPolynomial p).map (Int.castRingHom k), deuring_map_ne_zero p k, ?_⟩
      rw [Polynomial.aeval_def, ← eval_map, ← hmap]
      exact ht
    obtain ⟨t₀, rfl⟩ : t ∈ (algebraMap k K).range :=
      minpoly.mem_range_of_degree_eq_one k _
        (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible halg.isIntegral))
    refine ⟨t₀, ?_, rfl⟩
    rw [hmap, eval_map, eval₂_hom] at ht
    exact (map_eq_zero _).mp ht
  · rintro ⟨t₀, ht₀, rfl⟩
    rw [hmap, eval_map, eval₂_hom, ht₀, map_zero]

theorem ssJSet_eq_image_odd (hp2 : p ≠ 2) (iK : DecidableEq K) (ik : DecidableEq k) :
    @ssJSet p K _ iK = algebraMap k K '' @ssJSet p k _ ik := by
  rw [ssJSet_eq_ssJSetHasse p hp2 K, ssJSet_eq_ssJSetHasse p hp2 k,
    ssJSetHasse_eq_image_legendreJ p hp2 K, ssJSetHasse_eq_image_legendreJ p hp2 k, roots_eq_image p k K,
    Set.image_image, Set.image_image]
  congr 1
  ext t
  exact legendreJ_algebraMap k K t

end Odd

end ModularCurve.HSSBody

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed.ModularCurve ModularCurve.HSSBody in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K] :
    @ssJSet p K _ (Classical.decEq K) = algebraMap k K '' @ssJSet p k _ (Classical.decEq k) := by
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  by_cases hp2 : p = 2
  · subst hp2
    rw [ssJSet_two K, ssJSet_two k, Set.image_singleton, map_zero]
  · exact ssJSet_eq_image_odd p k K hp2 _ _

#print axioms solution

end S_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed (solution)
