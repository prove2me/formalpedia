-- Prove2me | solution 1 for OAI.Paper256.positiveLinearMap_common_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:02:32.994209+00:00
-- url     : https://prove2.me/submissions/beefd3b2-5265-41cc-82f8-58fb52cf952b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PositiveMaps.lean:L30-L45
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.positiveLinearMap_common_kernel. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_interior_line_pair
import Theorems.Thm_OAI_Paper256_isOpen_posDef

-- ---- from OAI.Analysis.HyperbolicCones.PencilKernel ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u

namespace Paper256

theorem posSemidef_pair_kernel {n : ℕ} {A H : Mat n ℝ}
    (hplus : (A + H).PosSemidef) (hminus : (A - H).PosSemidef)
    (v : Fin n → ℝ) (hv : A *ᵥ v = 0) : H *ᵥ v = 0 := by
  have hp := hplus.dotProduct_mulVec_nonneg v
  have hm := hminus.dotProduct_mulVec_nonneg v
  simp only [star_trivial, add_mulVec, sub_mulVec, hv, zero_add, zero_sub,
    dotProduct_neg] at hp hm
  have hz : v ⬝ᵥ ((A + H) *ᵥ v) = 0 := by
    simp only [add_mulVec, hv, zero_add]
    linarith
  have hh := (hplus.dotProduct_mulVec_zero_iff v).mp (by simpa only [star_trivial] using hz)
  simpa only [add_mulVec, hv, zero_add] using hh

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PositiveMaps ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem positiveLinearMap_common_kernel {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ X : Sym m, (X : Mat m ℝ).PosSemidef → (D X : Mat n ℝ).PosSemidef)
    (X : Sym m) (v : Fin n → ℝ) (hv : (D 1 : Mat n ℝ) *ᵥ v = 0) :
    (D X : Mat n ℝ) *ᵥ v = 0 := by
  have hI : (1 : Sym m) ∈ interior {Y : Sym m | (Y : Mat m ℝ).PosDef} := by
    rw [(isOpen_posDef m).interior_eq]
    exact Matrix.PosDef.one
  obtain ⟨ε, hε, hp, hm⟩ := interior_line_pair hI X
  have hp' := hD (1 + ε • X) hp.posSemidef
  have hm' := hD (1 - ε • X) hm.posSemidef
  have hz : (ε • (D X : Mat n ℝ)) *ᵥ v = 0 := by
    apply posSemidef_pair_kernel (A := (D 1 : Mat n ℝ)) _ _ v hv
    · simpa using hp'
    · simpa using hm'
  rw [smul_mulVec] at hz
  exact (smul_eq_zero.mp hz).resolve_left hε.ne'

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder


theorem solution : type_of% @_root_.OAI.Paper256.positiveLinearMap_common_kernel := @_root_.OAI.Paper256.positiveLinearMap_common_kernel
