-- Prove2me | solution 1 for GroundTheory.PAdicHodge.map_scale_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:01.256201+00:00
-- url     : https://prove2.me/submissions/9e82ff64-91f6-4aab-a541-c11aa89fcdda

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {Q : F[X]} (hQ : Q.Monic) (β c : F) (hc : c ≠ 0) :
    (Polynomial.C (c⁻¹ ^ Q.natDegree) * Q.comp (Polynomial.C β + Polynomial.C c * X)).map
        (algebraMap F E) =
      ((Q.map (algebraMap F E)).roots.map fun γ =>
        X - Polynomial.C ((γ - algebraMap F E β) / algebraMap F E c)).prod := by
  set f := Q.map (algebraMap F E)
  have hf : f = (f.roots.map fun γ => X - Polynomial.C γ).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic (hQ.map _)
  have hcard : Multiset.card f.roots = Q.natDegree := by
    rw [← (IsAlgClosed.splits f).natDegree_eq_card_roots, natDegree_map]
  have hc' : algebraMap F E c ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).2 hc
  rw [Polynomial.map_mul, Polynomial.map_C, map_comp, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
  change _ * f.comp _ = _
  conv_lhs => rw [hf]
  rw [multiset_prod_comp, Multiset.map_map, ← hcard]
  have key : ∀ γ : E, (X - Polynomial.C γ).comp (Polynomial.C (algebraMap F E β) +
      Polynomial.C (algebraMap F E c) * X) = Polynomial.C (algebraMap F E c) *
      (X - Polynomial.C ((γ - algebraMap F E β) / algebraMap F E c)) := by
    intro γ
    simp only [sub_comp, X_comp, C_comp, mul_sub, ← Polynomial.C_mul]
    rw [mul_div_cancel₀ _ hc', Polynomial.C_sub]
    ring
  simp only [Function.comp_def, key]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← mul_assoc,
    map_pow, map_inv₀, ← Polynomial.C_pow, ← Polynomial.C_mul, ← mul_pow, inv_mul_cancel₀ hc',
    one_pow, Polynomial.C_1, one_mul]
end GroundTheory.PAdicHodge
