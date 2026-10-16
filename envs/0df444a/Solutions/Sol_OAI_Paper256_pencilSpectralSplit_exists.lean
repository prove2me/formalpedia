-- Prove2me | solution 1 for OAI.Paper256.pencilSpectralSplit_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:10:46.797635+00:00
-- url     : https://prove2.me/submissions/80893a35-7cd0-487e-8c97-bf5639deb544

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/SplitFrame.lean:L23-L46
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.pencilSpectralSplit_exists. The node keeps its source
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

-- ---- from OAI.Analysis.HyperbolicCones.SplitFrame ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem pencilSpectralSplit_exists {m : ℕ} (A : Sym m)
    (hA : (A : Mat m ℝ).PosSemidef) (hne : (A : Mat m ℝ) ≠ 0)
    (hnpd : ¬ (A : Mat m ℝ).PosDef) : Nonempty (PencilSpectralSplit A) := by
  classical
  let p : Fin m → Prop := fun i => 0 < (sym_isHermitian A).eigenvalues i
  have hp : ∃ i, p i := by
    by_contra! hh
    apply hne
    apply (sym_isHermitian A).eigenvalues_eq_zero_iff.mp
    funext i
    exact le_antisymm (le_of_not_gt (hh i)) (hA.eigenvalues_nonneg i)
  have hn : ∃ i, ¬ p i := by
    by_contra! hh
    exact hnpd ((sym_isHermitian A).posDef_iff_eigenvalues_pos.mpr hh)
  let J := {i : Fin m // p i}
  let Q := {i : Fin m // ¬ p i}
  let a := Fintype.card J
  let c := Fintype.card Q
  let f : Fin a ≃ J := (Fintype.equivFin J).symm
  let g : Fin c ≃ Q := (Fintype.equivFin Q).symm
  let e : (Fin a ⊕ Fin c) ≃ Fin m := (Equiv.sumCongr f g).trans (Equiv.sumCompl p)
  have ha : 0 < a := Fintype.card_pos_iff.mpr ⟨⟨hp.choose, hp.choose_spec⟩⟩
  have hc : 0 < c := Fintype.card_pos_iff.mpr ⟨⟨hn.choose, hn.choose_spec⟩⟩
  exact ⟨⟨a, c, ha, hc, e, fun i => (f i).property, fun i => (g i).property⟩⟩

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.pencilSpectralSplit_exists := @_root_.OAI.Paper256.pencilSpectralSplit_exists
