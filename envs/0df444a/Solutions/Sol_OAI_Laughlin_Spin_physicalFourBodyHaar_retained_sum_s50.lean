-- Prove2me | solution 1 for OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:10:59.088916+00:00
-- url     : https://prove2.me/submissions/ab8e690d-ebc2-413f-bfaf-2302e1905616

import Mathlib
import Definitions.Def_OAIQ050L023
import Definitions.Def_OAIQ050L024
import Theorems.Thm_OAI_Laughlin_Spin_fourBody_haar_unequal_spin_s50
import Theorems.Thm_OAI_Laughlin_Spin_fourCoupledBasis_complex_complete_s50
import Theorems.Thm_OAI_Laughlin_Spin_physicalFourBodyHaar_hermitian_s50
import Theorems.Thm_OAI_Laughlin_Spin_physicalFourBodyHaar_high_column_s50
import Theorems.Thm_OAI_Laughlin_Spin_physical_fourBody_haar_multiplicity_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem retainedFourInclusion_column (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D)
    (n : Fin (fourSpinWeight Q D+1)) (i : FourWedgeIndex Q) :
    retainedFourInclusion Q D hQ r i n =
      (fourBodyCopy Q (oddPairDeficit r) D
        (by have := oddPairDeficit_le r; omega)
        (by have := oddPairDeficit_le r; omega)
        (by have := oddPairDeficit_le r; unfold genericCoupledWeight; omega) n.val i : ℂ) := rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem retainedFourIndex_column (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r : OddPairLabel D) (n : Fin (fourSpinWeight Q D+1)) (i : FourWedgeIndex Q) :
    (fourCoupledBasis Q i (retainedFourIndex Q D hQ r n) : ℂ) =
      retainedFourInclusion Q D hQ r i n := by
  have hd := retainedFourIndex_deficit Q D hQ r n
  change (fourBodyCopy Q (oddPairDeficit r) _ _ _ _ n.val i : ℂ) = _
  rw [retainedFourInclusion_column]
  unfold fourCoupledDeficit at hd
  simp only [hd]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem sum_fourCoupled_retained {A : Type*} [AddCommMonoid A]
    (Q : ℕ) (hQ : 25 ≤ Q) (f : FourCoupledIndex Q → A)
    (hz : ∀ s, 23 < fourCoupledDeficit s → f s=0) :
    (∑ s, f s) = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
      ∑ n : Fin (fourSpinWeight Q (d.val+1)+1),
        f (retainedFourIndex Q (d.val+1) (by have := d.isLt; omega) r n) := by
  classical
  rw [Finset.sum_congr_set (s := {s : FourCoupledIndex Q | fourCoupledDeficit s ≤ 23})
    f (fun s => f s.val) (fun _ _ => rfl) (by intro s hs; exact hz s (by simpa using hs))]
  have h := Fintype.sum_equiv (retainedFourColumnsEquiv Q hQ)
    (fun x => f (retainedFourIndex Q (x.1.val+1) (by have := x.1.isLt; omega) x.2.1 x.2.2))
    (fun s => f s.val) (fun _ => rfl)
  convert (by simpa only [Fintype.sum_sigma,Fintype.sum_prod_type] using h.symm) using 1
  all_goals try with_reducible_and_instances rfl
  apply Fintype.sum_equiv (Equiv.refl _)
  intro s
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem fourBody_retained_reconstruction (Q : ℕ) (hQ : 25 ≤ Q)
    (A : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ)
    (hz : ∀ s : FourCoupledIndex Q, 23 < fourCoupledDeficit s →
      A *ᵥ (fun i => (fourCoupledBasis Q i s : ℂ)) = 0) :
    A = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
      A * retainedFourInclusion Q (d.val+1) (by omega) r *
        (retainedFourInclusion Q (d.val+1) (by omega) r)ᴴ := by
  classical
  have hc : A = (A * (fourCoupledBasis Q).map Complex.ofReal) *
      ((fourCoupledBasis Q).map Complex.ofReal)ᴴ := by
    rw [Matrix.mul_assoc,fourCoupledBasis_complex_complete_s50,Matrix.mul_one]
  ext i j
  have he := congrFun (congrFun hc i) j
  simp only [Matrix.mul_apply,Matrix.map_apply,Matrix.conjTranspose_apply] at he
  rw [he]
  rw [sum_fourCoupled_retained Q hQ
    (fun s => (∑ k, A i k*(fourCoupledBasis Q k s : ℂ))*star (fourCoupledBasis Q j s : ℂ))
    (by intro s hs; have h := congrFun (hz s hs) i; change (∑ k, A i k*_) = 0 at h; rw [h,zero_mul])]
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,retainedFourIndex_column]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_GlobalHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation Fock
open scoped BigOperators Matrix

theorem physicalFourBodyHaar_retained_sum_s50_oai (Q : ℕ) (hQ : 25 ≤ Q) :
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) =
    ∑ d : Fin 23, (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) •
      fourCopyOperator Q (d.val+1) (by omega)
        (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s)) := by
  classical
  let A : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ := matrixIntegral sourceHaar
    (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal))
  let U (d : Fin 23) (r : OddPairLabel (d.val+1)) :
      Matrix (FourWedgeIndex Q) (Fin (fourSpinWeight Q (d.val+1)+1)) ℂ :=
    retainedFourInclusion Q (d.val+1) (by omega) r
  have hr : A = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1), A*U d r*(U d r)ᴴ :=
    fourBody_retained_reconstruction Q hQ A (physicalFourBodyHaar_high_column_s50 Q)
  have hl : A = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1), U d r*(U d r)ᴴ*A := by
    have ha : Aᴴ=A := physicalFourBodyHaar_hermitian_s50 Q
    have h := congrArg Matrix.conjTranspose hr
    simpa only [Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,ha,← Matrix.mul_assoc] using h
  have he (d : Fin 23) (r : OddPairLabel (d.val+1)) :
      U d r*(U d r)ᴴ*A = ∑ s : OddPairLabel (d.val+1),
        ((physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s) : ℂ) /
          ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) • (U d r*(U d s)ᴴ) := by
    calc
      _ = ∑ e : Fin 23, ∑ s : OddPairLabel (e.val+1),
          U d r*((U d r)ᴴ*A*U e s)*(U e s)ᴴ := by
        conv_lhs => rw [hr]
        simp only [Matrix.mul_sum,Matrix.mul_assoc]
      _ = ∑ s : OddPairLabel (d.val+1),
          U d r*((U d r)ᴴ*A*U d s)*(U d s)ᴴ := by
        apply Finset.sum_eq_single d
        · intro e he hed
          apply Finset.sum_eq_zero
          intro s hs
          have hz : (U d r)ᴴ*A*U e s=0 :=
            fourBody_haar_unequal_spin_s50 Q (d.val+1) (e.val+1) (by omega) (by omega)
              (by intro hv; exact hed (Fin.ext (by omega))) r s _
          rw [hz,Matrix.mul_zero,Matrix.zero_mul]
        · simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        have hb : (U d r)ᴴ*A*U d s =
            ((physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s) : ℂ) /
              ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) • 1 :=
          physical_fourBody_haar_multiplicity_s50 Q (d.val+1) hQ (by omega) r s
        rw [hb,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
  change A = _
  rw [hl]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [he,fourCopyOperator,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  simp only [div_eq_mul_inv,one_mul,mul_comm]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_s50_oai := @OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_s50_oai
