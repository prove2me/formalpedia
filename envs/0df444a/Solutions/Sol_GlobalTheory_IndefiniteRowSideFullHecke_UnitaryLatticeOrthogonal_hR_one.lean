-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.hR_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:59:35.98208+00:00
-- url     : https://prove2.me/submissions/f1f9d49e-aa75-4c32-a83b-95f4c75a636b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
theorem _root_.solution {M : ℕ} (z y : Fin M → Ev F E v) :
    hR (Fv F v) σ (1 : Matrix (Fin M) (Fin M) E) z y = ∑ i, sigR (Fv F v) σ (z i) * y i := by
  simp only [hR, Formalism.UG.hform, JR]
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  simp [Matrix.one_apply]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
