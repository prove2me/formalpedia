-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.independenceNumber_le_of_cohomomorphism
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:25:53.496118+00:00
-- url     : https://prove2.me/submissions/2b0893af-b108-4d11-ab7e-6d3609c10737

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (G : SimpleGraph V) (H : SimpleGraph W)
    [Fintype V] [Fintype W]
    (f : V → W) (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v)) :
    G.indepNum ≤ H.indepNum := by
  classical
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_indep : G.IsIndepSet (S : Set V) :=
    (SimpleGraph.isMaximumIndepSet_iff G S).1 hSmax |>.1
  let fS := S.image f
  have hfS_indep : H.IsIndepSet (fS : Set W) := by
    apply (SimpleGraph.isIndepSet_iff H).2
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    have hxy : x ≠ y := fun h => huv (by simp [h])
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS_indep
    have hnadj : ¬ G.Adj x y := hpair (by simpa using hx) (by simpa using hy) hxy
    exact fun hadj => (hf x y hxy hnadj).2 hadj
  have hf_inj : Set.InjOn f ↑S := by
    intro x hx y hy hxy
    by_contra hne
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS_indep
    have hnadj : ¬ G.Adj x y := hpair (by simpa using hx) (by simpa using hy) hne
    exact (hf x y hne hnadj).1 hxy
  have hcard : fS.card = S.card := Finset.card_image_of_injOn hf_inj
  have hle : S.card ≤ H.indepNum := by
    simpa [hcard] using SimpleGraph.IsIndepSet.card_le_indepNum (G := H) (t := fS) hfS_indep
  have hS_card : S.card = G.indepNum := by
    simpa using SimpleGraph.maximumIndepSet_card_eq_indepNum (G := G) S hSmax
  calc G.indepNum = S.card := hS_card.symm
    _ ≤ H.indepNum := hle
end GroupTheoreticShannonCapacity
