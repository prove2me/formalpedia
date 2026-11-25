-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:26:22.872428+00:00
-- url     : https://prove2.me/submissions/fe705d02-c06d-4414-baa4-3492b3b43bc0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_eval_subsetPoly
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_evalCoef_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_exists_isUniv
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_natDegree_prod_X_add_C
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_eval_domain
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_gen_monic
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_gen_natDegree
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_gen_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_eq_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubsetSum
namespace GlobalTheory.CompanionTheory.SubsetSum
theorem _root_.solution (R : Type) [CommRing R] (r : ℕ) (m : Multiset R) (A B : R[X])
    (hr : 0 < r) (hA : A.Monic) (hB : B.Monic) (hd : A.natDegree = r)
    (h : A * B = (m.map fun x => X + C x).prod) :
    ((m.powersetCard r).map fun S => A.coeff (r - 1) - S.sum).prod = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hm : Multiset.card m = r + B.natDegree := by
    rw [← natDegree_prod_X_add_C, ← h, hA.natDegree_mul hB, hd]
  obtain ⟨Φ, hΦ⟩ := exists_isUniv (r + B.natDegree) r
  let U := MvPolynomial (Fin r ⊕ Fin B.natDegree) ℤ
  let g : U →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (Sum.elim (fun i => A.coeff i) (fun j => B.coeff j))
  let A₀ : U[X] := gen r fun i => MvPolynomial.X (Sum.inl i)
  let B₀ : U[X] := gen B.natDegree fun j => MvPolynomial.X (Sum.inr j)
  have hA₀ : A₀.map g = A :=
    (gen_map _ _ _).trans ((congrArg (gen r) (funext fun i => MvPolynomial.eval₂_X _ _ _)).trans
      (eq_gen A hA r hd).symm)
  have hB₀ : B₀.map g = B :=
    (gen_map _ _ _).trans ((congrArg (gen _) (funext fun j => MvPolynomial.eval₂_X _ _ _)).trans
      (eq_gen B hB _ rfl).symm)
  have hBd : B₀.natDegree = B.natDegree := gen_natDegree _ _
  have key := eval_domain r hr A₀ B₀ (gen_monic _ _) (gen_monic _ _) (gen_natDegree _ _)
    (by rw [hBd]) hΦ
  have := congrArg g key
  rw [map_zero, ← eval_map_apply, Polynomial.map_map, evalCoef_comp, Polynomial.map_mul, hA₀, hB₀,
    ← coeff_map, hA₀, h, hΦ R m hm, eval_subsetPoly] at this
  exact this
end GlobalTheory.CompanionTheory.SubsetSum
