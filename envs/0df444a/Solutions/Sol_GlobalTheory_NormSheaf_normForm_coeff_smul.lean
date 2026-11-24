-- Prove2me | solution 1 for GlobalTheory.NormSheaf.normForm_coeff_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:47.774116+00:00
-- url     : https://prove2.me/submissions/3ac626c1-4e57-47cc-ae68-593fffa9b13b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFormCoefficientIdealMapLocalizationAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheaf
namespace GlobalTheory.NormSheaf
theorem _root_.solution (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (y : Fin m → L) (c : K) (s : Fin m →₀ ℕ) :
    (normForm K L (fun i => algebraMap K L c * y i)).coeff s =
      c ^ Module.finrank K L * (normForm K L y).coeff s := by
  have hM : ∀ i, (Algebra.leftMulMatrix (Module.finBasis K L) (algebraMap K L c * y i)).map
      (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) =
      (MvPolynomial.C c : MvPolynomial (Fin m) K) • (Algebra.leftMulMatrix (Module.finBasis K L) (y i)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) := by
    intro i
    rw [← Algebra.smul_def, map_smul]
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, MvPolynomial.C_mul]
  have : normForm K L (fun i => algebraMap K L c * y i) =
      MvPolynomial.C (c ^ Module.finrank K L) * normForm K L y := by
    unfold normForm
    simp_rw [hM, smul_comm (MvPolynomial.X _ : MvPolynomial (Fin m) K) (MvPolynomial.C c), ← Finset.smul_sum,
      Matrix.det_smul, Fintype.card_fin, map_pow]
  rw [this, MvPolynomial.coeff_C_mul]
end GlobalTheory.NormSheaf
