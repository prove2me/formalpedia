-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.eta_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:48.995596+00:00
-- url     : https://prove2.me/submissions/e9376d30-ec47-4a0a-a342-3b0487f67d77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_eta_norm_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (B : InvAlg K) (x : B.A) (b : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    K.eta (Matrix.of fun i j => B.herm x (b i) (b j)).det = K.eta (B.gramDet x) := by
  set c := Module.finBasis K.E B.A
  set M := c.toMatrix b with hM
  have hb : ∀ i, b i = ∑ k, M k i • c k := fun i => (c.sum_toMatrix_smul_self b i).symm
  have e : (Matrix.of fun i j => B.herm x (b i) (b j)) =
      M.transpose * (Matrix.of fun i j => B.herm x (c i) (c j)) * (K.c : K.E →+* K.E).mapMatrix M := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, InvAlg.herm, RingHom.coe_coe]
    rw [hb i, hb j, map_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def (M l j), map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det]
  exact eta_norm_mul _ _ (c.isUnit_det b).ne_zero
end GlobalTheory.UnitLemma.Orbit
