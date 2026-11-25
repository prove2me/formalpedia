-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.mem_LDeg_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:55.903569+00:00
-- url     : https://prove2.me/submissions/202fed7f-63b5-4a49-aeef-74ffd8bbfaf9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_sum_expHom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_mult_eq_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_one_le_mult
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_sum_nsmul_mult
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayToLaurent_mk
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_coeff_toLaurent_eq_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_coeff_toLaurent_expHom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_xprod_mem
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_mk_mem_awayDeg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) (ℓ : Laurent A n) :
    ℓ ∈ LDeg A (Set.range i) k ↔
      ∃ z ∈ ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k,
        awayToLaurent i z = ℓ := by
  classical
  constructor
  · intro hℓ
    let G := (ProjTwist.awayDeg (grading A n) (xprod_mem (A := A) i) (Nat.succ_pos p) k).map
      (awayToLaurent i).toAddMonoidHom
    suffices h : ∀ ℓ ∈ LDeg A (Set.range i) k, ℓ ∈ G by
      obtain ⟨z, hz, rfl⟩ := h ℓ hℓ
      exact ⟨z, hz, rfl⟩
    intro ℓ hℓ
    have hsum : ℓ = ∑ m ∈ ℓ.coeff.support, AddMonoidAlgebra.single m (ℓ.coeff m) := by
      apply AddMonoidAlgebra.coeff_injective
      rw [AddMonoidAlgebra.coeff_sum]
      simp only [AddMonoidAlgebra.coeff_single]
      exact (Finsupp.sum_single ℓ.coeff).symm
    rw [hsum]
    refine G.sum_mem fun m hm => ?_
    have hA : Allowed (Set.range i) k m := hℓ m (Finsupp.mem_support_iff.mp hm)
    set c := ℓ.coeff m
    set N : ℕ := ∑ j, (m j).natAbs
    have hN : ∀ j, ((m j).natAbs : ℤ) ≤ N := fun j => by
      exact_mod_cast Finset.single_le_sum (f := fun j => (m j).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have hpos : ∀ j, 0 ≤ m j + N * mult i j := fun j => by
      by_cases hj : j ∈ Set.range i
      · have h1 := one_le_mult i hj
        have h2 := hN j
        have h3 : -(m j) ≤ ((m j).natAbs : ℤ) := by omega
        nlinarith
      · rw [mult_eq_zero i hj, mul_zero, add_zero]
        exact hA.2 j hj
    let e : Fin (n + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => (m j + N * mult i j).toNat
    have hexp : expHom n e = m + N • mult i := by
      funext j
      change ((m j + N * mult i j).toNat : ℤ) = m j + N • mult i j
      rw [nsmul_eq_mul]
      exact Int.toNat_of_nonneg (hpos j)
    have hdeg : (e.degree : ℤ) = N * (p + 1 : ℕ) + k := by
      rw [← sum_expHom, hexp]
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_nsmul_mult, hA.1]
      ring
    refine ⟨Localization.mk (monomial e c) (ProjTwist.fpow (xprod i) N),
      ProjTwist.mk_mem_awayDeg _ _ (isHomogeneous_monomial c rfl) hdeg, ?_⟩
    change awayToLaurent i _ = _
    rw [awayToLaurent_mk, toLaurent_monomial, AddMonoidAlgebra.single_mul_single, hexp, mul_one,
      add_neg_cancel_right]
  · rintro ⟨z, ⟨N, j, a, ha, hj, rfl⟩, rfl⟩ m hm
    rw [awayToLaurent_mk, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, neg_neg] at hm
    by_cases hr : m + N • mult i ∈ Set.range (expHom n)
    · obtain ⟨e, he⟩ := hr
      rw [← he, coeff_toLaurent_expHom] at hm
      have hdeg : (e.degree : ℤ) = j := by
        have := ha hm
        rw [Finsupp.degree_eq_weight_one]
        exact_mod_cast this
      have hm' : m = expHom n e - N • mult i := by rw [he]; abel
      refine ⟨?_, fun j' hj' => ?_⟩
      · have hs := sum_nsmul_mult i N
        rw [hm']
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_expHom, hdeg, hj, hs]
        ring
      · rw [hm']
        simp [mult_eq_zero i hj', expHom]
    · exact (hm (coeff_toLaurent_eq_zero hr)).elim
end GroundTheory.Arith.SchemeCoh.ProjSpace
