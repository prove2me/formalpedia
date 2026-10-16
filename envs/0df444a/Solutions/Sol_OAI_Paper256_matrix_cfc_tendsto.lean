-- Prove2me | solution 1 for OAI.Paper256.matrix_cfc_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:58:56.150738+00:00
-- url     : https://prove2.me/submissions/f51e4324-973d-453c-8d9c-145439e0db85

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/SpectralContinuity.lean:L14-L33
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.matrix_cfc_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

-- ---- from OAI.Analysis.HyperbolicCones.SpectralContinuity ----
namespace OAI

/-! Finite spectral convergence, including eigenvalues equal to zero. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
universe u

namespace Paper256

theorem matrix_cfc_tendsto {n : ℕ} (A : Mat n ℝ) (hA : A.IsHermitian) {T : Type u} {L : Filter T}
    (f : T → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ i, Tendsto (fun t => f t (hA.eigenvalues i)) L
      (𝓝 (g (hA.eigenvalues i)))) :
    Tendsto (fun t => cfc (f t) A) L (𝓝 (cfc g A)) := by
  have hcoord : Tendsto (fun t i => f t (hA.eigenvalues i)) L
      (𝓝 (fun i => g (hA.eigenvalues i))) := tendsto_pi_nhds.mpr hf
  have hdiag := (continuous_id.matrix_diagonal.tendsto
    (fun i => g (hA.eigenvalues i))).comp hcoord
  have hprod := ((tendsto_const_nhds (x := (hA.eigenvectorUnitary : Mat n ℝ))).mul hdiag).mul
    (tendsto_const_nhds (x := ((hA.eigenvectorUnitary : Mat n ℝ)ᴴ)))
  simpa only [hA.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
    (hprod : Tendsto (fun t => (hA.eigenvectorUnitary : Mat n ℝ) *
      diagonal (fun i => f t (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Mat n ℝ)ᴴ) L
      (𝓝 ((hA.eigenvectorUnitary : Mat n ℝ) *
      diagonal (fun i => g (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Mat n ℝ)ᴴ)))

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology


theorem solution.{u} : type_of% @_root_.OAI.Paper256.matrix_cfc_tendsto.{u} := @_root_.OAI.Paper256.matrix_cfc_tendsto.{u}
