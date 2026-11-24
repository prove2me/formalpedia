-- Prove2me | solution 1 for GlobalTheory.SW.Emb.exists_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:38.44087+00:00
-- url     : https://prove2.me/submissions/2f8eca23-87ad-4897-925b-e51ccfb229df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Emb
theorem _root_.solution (v : Fin (N + 1) → E) (hv : v ≠ 0) :
    ∃ b : Matrix (Fin (N + 1)) (Fin (N + 1)) E, IsUnit b.det ∧ ∀ i, b i 0 = v i := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra hc
    exact hv (funext fun i => by_contra fun hi => hc ⟨i, hi⟩)
  set c : Matrix (Fin (N + 1)) (Fin (N + 1)) E := Matrix.of fun i j =>
    Fin.cases (v (Equiv.swap 0 k i)) (fun j' : Fin N => if i = j'.succ then (1 : E) else 0) j with hcdef
  have hc : c.det = v k := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have e : c.submatrix Fin.succ (Fin.succAbove 0) = 1 := by
      ext i j
      simp [hcdef, Matrix.one_apply]
    rw [e]
    simp [hcdef, Fin.succ_ne_zero, eq_comm (a := (0 : Fin (N + 1)))]
  refine ⟨c.submatrix (Equiv.swap 0 k) id, ?_, fun i => ?_⟩
  · rw [Matrix.det_permute, hc]
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero ?_ hk)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 k)) with hs | hs <;> simp [hs]
  · simp [hcdef]
end GlobalTheory.SW.Emb
