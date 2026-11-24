-- Prove2me | solution 1 for GlobalTheory.CubeColim.exists_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:47.550654+00:00
-- url     : https://prove2.me/submissions/221274c9-5f74-497f-b5ad-b5392507269a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechComplexDirectLimit
import Theorems.Thm_GlobalTheory_CubeColim_trans_congr
import Theorems.Thm_GlobalTheory_CubeColim_nonempty_of_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Filter
open GlobalTheory
open GlobalTheory.CubeColim
variable {ι : Type} [LinearOrder ι] [Fintype ι]
namespace GlobalTheory.CubeColim
theorem _root_.solution {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (c : ℕ) (x : Cube.Term (A c) m) (hx : Cube.termMap (ρ c) m x = 0) :
    ∃ J, Cube.termMap (μ J c (c + J) rfl) m x = 0 := by
  choose j hj using fun s : {s : Finset ι // s.card = m} =>
    h4 s.1 (nonempty_of_card hm s) c (x s) (congrFun hx s)
  refine ⟨Finset.univ.sup j, funext fun s => ?_⟩
  have hle := Finset.le_sup (f := j) (Finset.mem_univ s)
  have hcomp := h2 (j s) (Finset.univ.sup j - j s) c (c + j s) (c + Finset.univ.sup j) rfl
    (by omega) (by omega)
  have e : μ (Finset.univ.sup j) c (c + Finset.univ.sup j) rfl =
      μ (j s + (Finset.univ.sup j - j s)) c (c + Finset.univ.sup j) (by omega) :=
    trans_congr μ _ _ (by omega)
  rw [Cube.termMap_apply, e, ← hcomp]
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have e : ((μ (j s) c (c + j s) rfl).app s.1).hom (x s) = 0 := hj s
  rw [e, map_zero]
  rfl
end GlobalTheory.CubeColim
