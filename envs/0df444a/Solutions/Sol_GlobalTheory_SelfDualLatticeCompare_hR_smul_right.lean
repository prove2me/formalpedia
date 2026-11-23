-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeCompare.hR_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:53.66586+00:00
-- url     : https://prove2.me/submissions/6f9ba599-2a54-4b36-9848-746fff795e90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.SelfDualLatticeCompare
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.SelfDualLatticeCompare
theorem _root_.solution {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E)
    (c : R ⊗[F] E) : hR R σ J x (c • y) = c * hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.SelfDualLatticeCompare
