-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.map_eqs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:39.606335+00:00
-- url     : https://prove2.me/submissions/b559e497-45cb-4f6f-aba8-34f4dfb133e1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_mat_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_mat_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
namespace GlobalTheory.CompanionTheory.SW.HProj
theorem _root_.solution {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R')
    (A A' : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (g : HA R' σ J)
    (hA : A.map (tm E φ) = ((HA.mat R' σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R' ⊗[F] E)))
    (hA' : A'.map (tm E φ) = ((HA.mat R' σ J g⁻¹ : GL _ _) : Matrix (Fin M) (Fin M) (R' ⊗[F] E))) :
    (A * A').map (tm E φ) = (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (tm E φ) ∧
      (cT (sigR R σ) A * JR R J * A).map (tm E φ) = (JR R J).map (tm E φ) := by
  constructor
  · rw [Matrix.map_mul, hA, hA', Matrix.map_one (tm E φ) (map_zero _) (map_one _), ← Units.val_mul,
      ← mat_mul, mul_inv_cancel, mat_one, Units.val_one]
  · rw [map_unitary, hA, map_JR]
    exact (show HR R' σ J from g).2
end GlobalTheory.CompanionTheory.SW.HProj
