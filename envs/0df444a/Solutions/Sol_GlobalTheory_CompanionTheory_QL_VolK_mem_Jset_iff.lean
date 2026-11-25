-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.VolK.mem_Jset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:36.007378+00:00
-- url     : https://prove2.me/submissions/a1aa5937-d4b6-47b8-99e2-c06b326c9482

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_redM_eq_map
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_map_toO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.VolK
variable {F : Type} [Field F] [ValuativeRel F]
namespace GlobalTheory.CompanionTheory.QL.VolK
theorem _root_.solution {r : ℕ} {x : Matrix (Fin r) (Fin r) F} (h : x ∈ intMat 𝒪[F] r r) :
    x ∈ Jset (GLint 𝒪[F] r) ↔ IsUnit (redM x).det := by
  have hdet : (redM x).det = IsLocalRing.residue 𝒪[F] (toO h).det := by
    rw [redM_eq_map h, RingHom.map_det]
  rw [hdet, isUnit_map_iff]
  constructor
  · rintro ⟨g, ⟨-, hg'⟩, hgx⟩
    have hgx' : (g : Matrix (Fin r) (Fin r) F) = x := hgx
    have hg'' : ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ intMat 𝒪[F] r r := hg'
    have hmul : toO h * toO hg'' = 1 := by
      have h1 : (𝒪[F].subtype).mapMatrix (toO h * toO hg'') = (𝒪[F].subtype).mapMatrix 1 := by
        rw [map_mul, map_toO, map_toO, map_one, ← hgx']
        exact Units.mul_inv g
      exact Matrix.map_injective (f := 𝒪[F].subtype) Subtype.val_injective h1
    exact Matrix.isUnit_det_of_right_inverse hmul
  · intro hu
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
    let φ : Matrix (Fin r) (Fin r) 𝒪[F] →* Matrix (Fin r) (Fin r) F :=
      RingHom.toMonoidHom (𝒪[F].subtype).mapMatrix
    have hval : φ (u : Matrix (Fin r) (Fin r) 𝒪[F]) = x := by
      rw [hu']
      exact map_toO h
    refine ⟨Units.map φ u, ⟨?_, ?_⟩, hval⟩
    · intro i j
      have : ((Units.map φ u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = x := hval
      rw [this]
      exact h i j
    · intro i j
      exact (((u⁻¹ : GL (Fin r) 𝒪[F]) : Matrix (Fin r) (Fin r) 𝒪[F]) i j).2
end GlobalTheory.CompanionTheory.QL.VolK
