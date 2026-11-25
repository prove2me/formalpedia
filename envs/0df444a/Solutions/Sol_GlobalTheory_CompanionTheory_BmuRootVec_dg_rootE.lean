-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.dg_rootE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:02.309444+00:00
-- url     : https://prove2.me/submissions/2094157b-1dff-4364-ae4f-ec367f7de161

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuRootVec
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuRootVec
theorem _root_.solution {d : Fin (2 * r + k + 1) → ℝ} (hd : IsTor k r d) (a : Fin r) (κ : ℂ) :
    dg d * rootE k r a κ = ((d (eI k r a) / d (nxt k r a) : ℝ) : ℂ) • (rootE k r a κ * dg d) := by
  have ha := a.isLt
  obtain ⟨h0, h1, -, -⟩ := hd
  have e1 := h1 (eI k r a) (esI k r a) (by simp only [outer, eI]; omega) (by simp only [eI, esI]; omega)
  have e2 := h1 (nxtS k r a) (nxt k r a) (by simp only [outer, nxtS]; omega)
    (by simp only [nxtS, nxt]; omega)
  have hn := (h0 (nxt k r a)).ne'
  have f1 : d (eI k r a) = d (eI k r a) / d (nxt k r a) * d (nxt k r a) := by field_simp
  have f2 : d (nxtS k r a) = d (eI k r a) / d (nxt k r a) * d (esI k r a) := by
    field_simp; rw [e1, e2]
  generalize d (eI k r a) / d (nxt k r a) = α at f1 f2
  ext p q
  simp only [dg, rootE, diagonal_mul, mul_diagonal, Matrix.smul_apply, Matrix.sub_apply, single_apply,
    smul_eq_mul]
  have g1 : (d p : ℂ) * (if eI k r a = p ∧ nxt k r a = q then κ else 0) =
      α * ((if eI k r a = p ∧ nxt k r a = q then κ else 0) * d q) := by
    split_ifs with h
    · rw [← h.1, ← h.2, f1]; push_cast; ring
    · simp
  have g2 : (d p : ℂ) * (if nxtS k r a = p ∧ esI k r a = q then conj κ else 0) =
      α * ((if nxtS k r a = p ∧ esI k r a = q then conj κ else 0) * d q) := by
    split_ifs with h
    · rw [← h.1, ← h.2, f2]; push_cast; ring
    · simp
  rw [mul_sub, g1, g2]; ring
end GlobalTheory.CompanionTheory.BmuRootVec
