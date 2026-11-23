-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.coord_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:56.793679+00:00
-- url     : https://prove2.me/submissions/97370cad-363f-4eac-b020-3013f45b7de7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
theorem _root_.solution (β : Module.Basis (Fin d) R A) (H : Matrix (Fin M) (Fin M) A)
    (g : Matrix (Fin M × Fin d) (Fin M × Fin d) R)
    (hg : ∀ p q, g p q = β.repr (H p.1 q.1 * β q.2) p.2) (x : Fin M → A) :
    coord β (H *ᵥ x) = g *ᵥ coord β x := by
  funext p
  have hterm : ∀ j, H p.1 j * x j = ∑ l, β.repr (x j) l • (H p.1 j * β l) := by
    intro j
    conv_lhs => rw [← β.sum_repr (x j)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_smul_comm _ _ _
  simp only [coord, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hg]
  simp only [hterm, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
end GlobalTheory.CompanionTheory.SW.TraceCoord
