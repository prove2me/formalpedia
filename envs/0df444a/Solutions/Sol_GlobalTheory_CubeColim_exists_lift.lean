-- Prove2me | solution 1 for GlobalTheory.CubeColim.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:48.457142+00:00
-- url     : https://prove2.me/submissions/69341e43-8380-4450-8abc-550c26aa65f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechComplexDirectLimit
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
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) :
    ∃ C, ∃ a : Cube.Term (A C) m, Cube.termMap (ρ C) m a = z := by
  choose c a ha using fun s : {s : Finset ι // s.card = m} => h3 s.1 (nonempty_of_card hm s) (z s)
  have hc : ∀ s, c s + (Finset.univ.sup c - c s) = Finset.univ.sup c := fun s => by
    have := Finset.le_sup (f := c) (Finset.mem_univ s); omega
  refine ⟨Finset.univ.sup c,
    fun s => ((μ _ (c s) _ (hc s)).app s.1).hom (a s), funext fun s => ?_⟩
  have e := congrArg (fun f => (f.app s.1).hom (a s)) (h1 _ (c s) _ (hc s))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [Cube.termMap_apply, e]
  exact ha s
end GlobalTheory.CubeColim
