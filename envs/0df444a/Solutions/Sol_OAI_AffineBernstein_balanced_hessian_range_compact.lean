-- Prove2me | solution 1 for OAI.AffineBernstein.balanced_hessian_range_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:13:34.326779+00:00
-- url     : https://prove2.me/submissions/4054090f-eafb-4bbd-95b6-61e37d0ae99e

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_balanced_global_directional_bddAbove

section
-- module Solutions.OAIQ22_AB.AffineBernstein_HessianCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section HessianCompactness
open Matrix

lemma posSemidef_entry_abs_le_diagonals {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i j : Fin n) : |A i j| ≤ (A i i+A j j)/2 := by
  have hsym : A j i = A i j := (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).apply i j
  have hp := hA.dotProduct_mulVec_nonneg (Pi.single i 1+Pi.single j 1)
  have hm := hA.dotProduct_mulVec_nonneg (Pi.single i 1-Pi.single j 1)
  simp only [star_trivial,Matrix.mulVec_add,Matrix.mulVec_sub,add_dotProduct,sub_dotProduct,
    dotProduct_add,dotProduct_sub,Matrix.mulVec_single_one,single_dotProduct,Matrix.col_apply,
    one_mul,hsym] at hp hm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma balanced_hessian_range_compact_oai {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbal : SectionBalance univ u ρ) : IsCompact (closure (range (hessian u))) := by
  classical
  have hb := fun i : Fin n => balanced_global_directional_bddAbove hn hu hp hm hρ hρ1 hbal (coordinateVector n i)
  choose C hC using hb
  have hc (x : Space n) (i : Fin n) : hessian u x i i ≤ C i := hC i ⟨x,rfl⟩
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => (C i+C j)/2
  let K := univ.pi (fun i : Fin n => univ.pi (fun j : Fin n => Icc (-D i j) (D i j)))
  have hK : IsCompact K := isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  have hsub : range (hessian u) ⊆ K := by
    rintro A ⟨x,rfl⟩ i hi j hj
    have H := (posSemidef_entry_abs_le_diagonals (hp x).posSemidef i j).trans
      (show (hessian u x i i+hessian u x j j)/2 ≤ D i j by dsimp [D]; linarith [hc x i,hc x j])
    exact abs_le.mp H
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

end HessianCompactness


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.balanced_hessian_range_compact_oai := @OAI.AffineBernstein.balanced_hessian_range_compact_oai
