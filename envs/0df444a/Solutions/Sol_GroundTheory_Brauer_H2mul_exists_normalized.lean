-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.exists_normalized
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:44:21.342162+00:00
-- url     : https://prove2.me/submissions/824b77b4-c00c-43df-a80d-7bb9ec577d26

import Mathlib
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Theorems.Thm_P2M_GroundTheory_Brauer_isMulCocycle__of_isMulCoboundary__1fe17ff20d13
import Theorems.Thm_P2M_GroundTheory_Brauer_map_one_fst_of_isMulCocycle__of_eq_one_6aa62c1a601e
import Theorems.Thm_P2M_GroundTheory_Brauer_map_one_snd_of_isMulCocycle__of_eq_one_f07df9f0d9d6
import Theorems.Thm_GroundTheory_Brauer_H2mul_mk_eq_mk_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v u' v'
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
open GroundTheory.Brauer.H2mul
variable {G M}
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution (x : H2mul G M) :
    ∃ f : mulCocycles₂ G M, mk G M f = x ∧ (f : G × G → M) (1, 1) = 1 ∧
      ∀ g : G, (f : G × G → M) (1, g) = 1 ∧ (f : G × G → M) (g, 1) = 1 := by
  induction x using induction_on with
  | h c =>
    have hd : IsMulCoboundary₂ (fun p : G × G => p.1 • (c : G × G → M) (1, 1)) :=
      ⟨fun _ => (c : G × G → M) (1, 1), fun g h => by simp⟩
    let d : mulCocycles₂ G M := ⟨_, isMulCocycle₂_of_isMulCoboundary₂ hd⟩
    have h1 : ((c / d : mulCocycles₂ G M) : G × G → M) (1, 1) = 1 := by
      simp [d]
    refine ⟨c / d, ?_, h1, fun g => ⟨?_, ?_⟩⟩
    · rw [mk_eq_mk_iff]
      have : ((c / d : mulCocycles₂ G M) : G × G → M) / c = (d : G × G → M)⁻¹ := by
        simp only [Subgroup.coe_div]
        rw [div_right_comm, div_self', one_div]
      rw [this]
      exact (mulCoboundaries₂ G M).inv_mem hd
    · exact map_one_fst_of_isMulCocycle₂_of_eq_one (c / d).2 h1 g
    · exact map_one_snd_of_isMulCocycle₂_of_eq_one (c / d).2 h1 g
end GroundTheory.Brauer.H2mul
