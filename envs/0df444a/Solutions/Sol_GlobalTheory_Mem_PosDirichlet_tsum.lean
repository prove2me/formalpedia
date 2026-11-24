-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:17:36.975713+00:00
-- url     : https://prove2.me/submissions/2f6b911f-2439-401f-8ae4-e9ec68874773

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_norm_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
open GlobalTheory.Mem.PosDirichlet
namespace GlobalTheory.Mem.PosDirichlet
theorem _root_.solution {J : Type} {F : J → ℂ → ℂ} (hF : ∀ j, PosDirichlet (F j))
    (hs : ∀ s : ℂ, 1 < s.re → Summable (fun j => F j s)) :
    PosDirichlet (fun s => ∑' j, F j s) := by
  choose ι w N hw hN h using hF
  refine ⟨Σ j, ι j, fun p => w p.1 p.2, fun p => N p.1 p.2, fun p => hw _ _, fun p => hN _ _,
    fun s hs' => ?_⟩
  have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs'
  have key : ∀ j, HasSum (fun i => ‖(w j i : ℂ) * (N j i : ℂ) ^ (-s)‖) (F j s.re).re := by
    intro j
    simp only [norm_term (hw _ _) (hN _ _)]
    exact Complex.hasSum_re (h j _ hσ)
  have hsum : Summable (fun p : Σ j, ι j => (w p.1 p.2 : ℂ) * (N p.1 p.2 : ℂ) ^ (-s)) := by
    apply Summable.of_norm
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun j => (key j).summable, ?_⟩
    simp only [fun j => (key j).tsum_eq]
    exact (Complex.hasSum_re (hs _ hσ).hasSum).summable
  have h2 := hsum.hasSum.sigma (fun j => h j s hs')
  show HasSum _ (∑' j, F j s)
  rw [h2.tsum_eq]
  exact hsum.hasSum
end GlobalTheory.Mem.PosDirichlet
