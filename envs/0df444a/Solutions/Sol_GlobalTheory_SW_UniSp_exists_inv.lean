-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:53.593332+00:00
-- url     : https://prove2.me/submissions/6662ce4d-21fb-433c-9bb2-ee82eafe518e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
import Theorems.Thm_GlobalTheory_SW_UniSp_zeta_eq
import Theorems.Thm_GlobalTheory_SW_Dict_sum_type
import Theorems.Thm_GlobalTheory_SW_Dict_zetaOf_surj


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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UniSp
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}
namespace GlobalTheory.SW.UniSp
theorem _root_.solution (hΨ : IsType Ψ) : ∃ S' : Matrix ((Fin N ⊕ Fin N) × Ψ) (QI E N) ℂ,
    Sm Ψ N * S' = 1 ∧ S' * Sm Ψ N = 1 := by
  choose z z' h using fun p : QI E N =>
    Dict.zetaOf_surj (n := 1) hΨ fun _ => (Pi.single p 1 : QI E N → ℂ)
  have h1 : Sm Ψ N * (Matrix.of fun (q : (Fin N ⊕ Fin N) × Ψ) (p : QI E N) =>
      Sum.elim (z p q.2 0) (z' p q.2 0) q.1) = 1 := by
    ext q p
    have := congrFun (congrFun (h p) 0) q
    rw [zeta_eq, Pi.single_apply] at this
    rw [Matrix.one_apply, ← this]
    rfl
  have hc : Fintype.card (QI E N) = Fintype.card ((Fin N ⊕ Fin N) × Ψ) := by
    have := Dict.sum_type hΨ (fun _ => 1)
    simp only [Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul, mul_one,
      mul_add] at this
    have h2 : Module.finrank ℚ E = Fintype.card Ψ + Fintype.card Ψ := by exact_mod_cast this
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, h2]
    ring
  exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).1 h1⟩
end GlobalTheory.SW.UniSp
