-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.symmetricLaurent_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:57.582914+00:00
-- url     : https://prove2.me/submissions/35b505b0-4a7a-4ca5-a8e6-41b3b2f0f3a9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_monomial_const_mem
import Theorems.Thm_GroundTheory_Automorphic_Spherical_polyEmb_injective
import Theorems.Thm_GroundTheory_Automorphic_Spherical_polyEmb_rename
import Theorems.Thm_GroundTheory_Automorphic_Spherical_mem_range_polyEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open AddMonoidAlgebra MvPolynomial
open GroundTheory.Automorphic.Spherical
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution {A : Subalgebra ℂ (LaurentRing n)}
    (he : ∀ k, polyEmb n (esymm (Fin n) ℂ k) ∈ A) (hinv : monomial (fun _ => (-1 : ℤ)) ∈ A) :
    symmetricLaurent n ≤ A := by
  classical
  intro p hp
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ l ∈ p.coeff.support, ∀ i, -(N : ℤ) ≤ l i := by
    refine ⟨p.coeff.support.sup fun l => Finset.univ.sup fun i => (l i).natAbs, fun l hl i => ?_⟩
    have h1 : (l i).natAbs ≤ Finset.univ.sup fun i => (l i).natAbs :=
      Finset.le_sup (f := fun i => (l i).natAbs) (Finset.mem_univ i)
    have h2 := Finset.le_sup (f := fun l : Fin n → ℤ => Finset.univ.sup fun i => (l i).natAbs) hl
    have h3 : ((l i).natAbs : ℤ) ≤ _ := Nat.cast_le.2 (h1.trans h2)
    rw [Int.natCast_natAbs] at h3
    have h4 := neg_abs_le (l i)
    linarith
  set c : LaurentRing n := monomial (fun _ => (N : ℤ))
  set q := c * p
  have hq : q ∈ symmetricLaurent n := Subalgebra.mul_mem _ (monomial_const_mem _) hp
  have hqs : ∀ l ∈ q.coeff.support, ∀ i, 0 ≤ l i := by
    intro l hl i
    have hsub := AddMonoidAlgebra.support_coeff_mul_subset c p hl
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hsub
    have ha' : a = fun _ => (N : ℤ) := by
      have := Finsupp.support_single_subset ha
      simpa using this
    subst ha'
    have := hN b hb i
    simp only [Pi.add_apply]
    omega
  obtain ⟨Q, hQ⟩ := mem_range_polyEmb hqs
  change polyEmb n Q = q at hQ
  have hQsym : Q ∈ symmetricSubalgebra (Fin n) ℂ := by
    rw [mem_symmetricSubalgebra]
    intro σ
    apply polyEmb_injective
    rw [polyEmb_rename, hQ, hq σ]
  obtain ⟨P, hP⟩ := esymmAlgHom_surjective ℂ (σ := Fin n) (n := n) (Fintype.card_fin n).le ⟨Q, hQsym⟩
  have hQP : Q = aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) P := by
    rw [← esymmAlgHom_apply, hP]
  have hqA : q ∈ A := by
    rw [← hQ, hQP, ← AlgHom.comp_apply, comp_aeval]
    have : aeval (fun i : Fin n => polyEmb n (esymm (Fin n) ℂ (i + 1))) P ∈
        (aeval fun i : Fin n => polyEmb n (esymm (Fin n) ℂ (i + 1))).range :=
      AlgHom.mem_range_self _ _
    rw [aeval_range] at this
    exact Algebra.adjoin_le (Set.range_subset_iff.2 fun i => he _) this
  have hp' : p = monomial (fun _ => (-1 : ℤ)) ^ N * q := by
    rw [AddMonoidAlgebra.single_pow, one_pow, ← mul_assoc, AddMonoidAlgebra.single_mul_single,
      one_mul]
    have : (N • fun _ : Fin n => (-1 : ℤ)) + (fun _ => (N : ℤ)) = 0 := by
      funext i
      simp
    rw [this, ← AddMonoidAlgebra.one_def, one_mul]
  rw [hp']
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hinv _) hqA
end GroundTheory.Automorphic.Spherical
