-- Prove2me | solution 1 for OAI.ComplexCancellation.GradedMap.mvpolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:00:35.320687+00:00
-- url     : https://prove2.me/submissions/893f8591-bc4f-4533-a432-022f0b48531a

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/GradedMap.lean:L11-L26
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.GradedMap.mvpolynomial. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation

-- ---- from OAI.Algebra.AffineCancellation.GradedMap ----
namespace OAI

noncomputable section

namespace ComplexCancellation.GradedMap
open MvPolynomial
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]
lemma mvpolynomial {ι : Type*} (G : ℤ → Submodule k R) [GradedAlgebra G]
    (w : ι → ℤ) (f : MvPolynomial ι k →ₐ[k] R)
    (hX : ∀ i, f (X i) ∈ G (w i)) {p : MvPolynomial ι k} {e : ℤ}
    (hp : IsWeightedHomogeneous w p e) : f p ∈ G e := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact (G e).zero_mem
  | add p q hp hq ihp ihq => rw [map_add]; exact add_mem ihp ihq
  | monomial d a hd =>
    rw [monomial_eq,map_mul,MvPolynomial.C_eq_algebraMap,AlgHom.commutes,← Algebra.smul_def]
    apply (G e).smul_mem
    rw [Finsupp.prod,map_prod]
    simp only [map_pow]
    have ht := SetLike.prod_pow_mem_graded G w (fun i => f (X i)) (F := d.support) (fun i => d i) (fun i _ => hX i)
    convert ht using 1
    rw [← hd,Finsupp.weight_apply,Finsupp.sum]

end ComplexCancellation.GradedMap

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.GradedMap
open MvPolynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.GradedMap.mvpolynomial := @_root_.OAI.ComplexCancellation.GradedMap.mvpolynomial
