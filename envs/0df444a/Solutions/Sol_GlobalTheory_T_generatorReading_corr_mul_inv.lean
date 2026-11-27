-- Prove2me | solution 1 for GlobalTheory.T.generatorReading_corr_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:45:09.975715+00:00
-- url     : https://prove2.me/submissions/3e047346-cb3c-48d1-b37e-b00c79a8830f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInvStatement
import Theorems.Thm_GlobalTheory_AnValGenCorr_genRd_corr_mul_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (φ' : K' → (Z ⟶ A.left)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (t' : LB.Gen (LB.LinComb L.L φ' ε')) (q : Sp ℂ ⟶ Z) (p : K → Fin g → ℂ) (p' : K' → Fin g → ℂ) (v v' : ℂ), Φ.GenRd φ ε t q p v → Φ.GenRd φ' ε' t' q p' v' → (LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι, (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧ v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k) ∧ (LB.Gen.Corr L.L φ ε φ' ε' t t' → LB.SameSum φ ε φ' ε' → (∃ π : (Z ⟶ A.left) → Fin g → ℂ, (∀ k, p k = π (φ k)) ∧ ∀ k, p' k = π (φ' k)) → v = v') ∧ Φ.GenRd (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' t t') q (Sum.elim p p') (v * v') ∧ Φ.GenRd φ (fun k => -ε k) (LB.invGen L.L φ ε t) q p v⁻¹ := by
  first | exact @GlobalTheory.AnValGenCorr.genRd_corr_mul_inv | exact GlobalTheory.AnValGenCorr.genRd_corr_mul_inv | (intros; apply GlobalTheory.AnValGenCorr.genRd_corr_mul_inv <;> assumption)
end _root_.GlobalTheory.T
