-- Prove2me | solution 1 for GlobalTheory.ChowHt.Model.isChowForm_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:52.36126+00:00
-- url     : https://prove2.me/submissions/f3ddf41e-4cee-43cf-8a2a-fbac197de999

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
import Theorems.Thm_P2M_GlobalTheory_BorelAlg_irreducible_det__000b129e89d6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model
namespace GlobalTheory.ChowHt.Model
theorem _root_.solution (k : Type) [Field k] :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) k)) 1 1
      (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s hs b
    rw [Matrix.det_fin_two] at hs
    simp only [Matrix.of_apply, X, monomial_mul, mul_one] at hs
    have h1 := support_sub _ _ _ hs
    rw [Finset.mem_union] at h1
    rcases h1 with h | h <;>
    · have := support_monomial_subset h
      rw [Finset.mem_singleton] at this
      subst this
      fin_cases b <;> simp [Fin.sum_univ_two, Finsupp.single_apply]
  · have := GlobalTheory.BorelAlg.irreducible_det' (R := AlgebraicClosure k) (k := 2) (by norm_num) id
      Function.injective_id
    convert this using 1
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
  · intro u
    have : MvPolynomial.aeval u
        (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det =
        (Matrix.of fun i j : Fin 2 => u (i, j)).det := by
      simp [Matrix.det_fin_two]
    rw [this, ← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨y, hy, fun g hg => by simp [Ideal.mem_bot.1 hg], fun i => ?_⟩
      simpa [Matrix.mulVec, dotProduct] using congrFun h i
    · rintro ⟨y, hy, -, h⟩
      refine ⟨y, hy, funext fun i => ?_⟩
      simpa [Matrix.mulVec, dotProduct] using h i
end GlobalTheory.ChowHt.Model
