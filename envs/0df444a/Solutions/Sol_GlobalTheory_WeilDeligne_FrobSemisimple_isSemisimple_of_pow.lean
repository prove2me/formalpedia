-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.FrobSemisimple.isSemisimple_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:13:09.738879+00:00
-- url     : https://prove2.me/submissions/475f4b83-552f-4178-bd3a-9f3ba9cd273b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrob
import Theorems.Thm_GlobalTheory_WeilDeligne_FrobSemisimple_minpoly_eval_zero_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.FrobSemisimple
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace GlobalTheory.WeilDeligne.FrobSemisimple
theorem _root_.solution {g : End ℂ V} (hg : IsUnit g) {m : ℕ} (hm : 0 < m)
    (hs : (g ^ m).IsSemisimple) : g.IsSemisimple := by
  have hsep : (minpoly ℂ (g ^ m)).Separable :=
    PerfectField.separable_iff_squarefree.mpr hs.minpoly_squarefree
  have h0 := minpoly_eval_zero_ne_zero (hg.pow m)
  set p := minpoly ℂ (g ^ m) with hp
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := expand ℂ m p)
    (Separable.squarefree ?_) ?_
  · rw [Separable, derivative_expand]
    refine IsCoprime.mul_right (IsCoprime.map hsep (expand ℂ m).toRingHom)
      (IsCoprime.mul_right ?_ (IsCoprime.pow_right ?_))
    · have : IsUnit ((m : ℕ) : ℂ[X]) := by
        rw [← C_eq_natCast]
        exact isUnit_C.mpr (Ne.isUnit (Nat.cast_ne_zero.mpr hm.ne'))
      exact (isCoprime_mul_unit_left_right this _ 1).mpr isCoprime_one_right |>.of_mul_right_left
    · refine ((irreducible_X.coprime_iff_not_dvd).mpr ?_).symm
      rw [X_dvd_iff, coeff_zero_eq_eval_zero, expand_eval, zero_pow hm.ne']
      exact h0
  · rw [expand_aeval]
    exact minpoly.aeval ℂ _
end GlobalTheory.WeilDeligne.FrobSemisimple
