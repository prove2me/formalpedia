-- Prove2me | solution 1 for GlobalTheory.FunObj.hasCompactSupport_flatIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:06:55.93661+00:00
-- url     : https://prove2.me/submissions/75392fa9-a1e4-45b6-a1a9-061b2788ecac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Theorems.Thm_GlobalTheory_FunObj_exists_fill_entry
import Theorems.Thm_GlobalTheory_FunObj_exists_isCompact_of_mul_mem
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
namespace GlobalTheory.FunObj
theorem _root_.solution (hs : 1 ≤ G.s) (ψ : AddChar k Circle) {ϖ : kˣ} {e : ℕ}
    {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : HasCompactSupport (flatIntegrand hs ψ (moved G keep g T) x y) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  choose a b c h using exists_fill_entry hs x y
  choose K hK hK' using fun j : Fin (G.m - 1) => exists_isCompact_of_mul_mem
    (Assignment.one.read (g (Edge.theta G.m j).tgt))⁻¹ (Assignment.one.read (g (Edge.theta G.m j).src))
  refine HasCompactSupport.intro (K := Set.univ.pi fun j => Set.univ.pi fun rs =>
    (fun M => M (a j rs) (b j rs) - c j rs) '' K j) (isCompact_univ_pi fun j => isCompact_univ_pi fun rs =>
      (hK j).image ((continuous_id.matrix_elem _ _).sub continuous_const)) fun v hv => ?_
  have h0 : T (G.moveArgs .one g (fill hs x y v)) = 0 := by
    by_contra hne
    refine hv fun j _ rs _ => ⟨_, hK' j _ ?_, (h j rs v).symm⟩
    by_contra hn
    exact hne (hT.2.1 _ (.theta G.m j) (by have := j.2; simp [oppositePath]; omega) hn)
  simp [flatIntegrand, moved, Grid.pathAct, h0]
end GlobalTheory.FunObj
