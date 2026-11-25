-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_lcoeffMod_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:29.577349+00:00
-- url     : https://prove2.me/submissions/d1c2421d-24ab-49ef-ac72-07383c10304f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_dvd_monicAssoc
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_natDegree_monicAssoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
variable {F : Type*} [Field F]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {q f : F[X]} (hq : q ≠ 0) (hf : ¬ q ∣ f) :
    ∃ g, lcoeffMod q (f * g) ≠ 0 := by
  set q' := monicAssoc q with hq'
  have hm : q'.Monic := monicAssoc_monic hq
  set r := f %ₘ q' with hr
  have hr0 : r ≠ 0 := fun h =>
    hf ((dvd_monicAssoc q).trans ((modByMonic_eq_zero_iff_dvd hm).1 h))
  have hdeg : r.natDegree < q.natDegree := by
    rw [← natDegree_monicAssoc hq]
    exact natDegree_lt_natDegree hr0 (degree_modByMonic_lt f hm)
  set j := q.natDegree - 1 - r.natDegree
  refine ⟨X ^ j, ?_⟩
  have e1 : (f * X ^ j) %ₘ q' = (r * X ^ j) %ₘ q' := by
    have : f * X ^ j = r * X ^ j + q' * ((f /ₘ q') * X ^ j) := by
      conv_lhs => rw [← modByMonic_add_div f q']
      ring
    rw [this, add_modByMonic, ((modByMonic_eq_zero_iff_dvd hm).2 (dvd_mul_right _ _)), add_zero]
  have hdeg2 : (r * X ^ j).natDegree = q.natDegree - 1 := by
    rw [natDegree_mul_X_pow _ hr0]
    omega
  have e2 : (r * X ^ j) %ₘ q' = r * X ^ j := by
    rw [modByMonic_eq_self_iff hm]
    apply degree_lt_degree
    rw [hdeg2, natDegree_monicAssoc hq]
    omega
  rw [lcoeffMod, e1, e2]
  have e3 : q.natDegree - 1 = r.natDegree + j := by omega
  rw [e3, coeff_mul_X_pow]
  exact leadingCoeff_ne_zero.2 hr0
end GroundTheory.Automorphic.ContragredientTranspose
