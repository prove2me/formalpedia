-- Prove2me | solution 1 for GlobalTheory.T.exists_latticeDatum_of_selfDual_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:17:49.177156+00:00
-- url     : https://prove2.me/submissions/d1aa06fd-abef-421b-a3ef-03b473e03231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLatticeStatement
import Theorems.Thm_GlobalTheory_LatticeDatum_exists_datum_of_selfDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r → E)), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → Λ'.FG → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (ξ * herm Gm v y) = n) ↔ v ∈ Λ') → ∃ (D' : Datum H) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧ LinearMap.range φ' = Λ' ∧ (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) := by
  first | exact @GlobalTheory.LatticeDatum.exists_datum_of_selfDual | exact GlobalTheory.LatticeDatum.exists_datum_of_selfDual | (intros; apply GlobalTheory.LatticeDatum.exists_datum_of_selfDual <;> assumption)
end _root_.GlobalTheory.T
