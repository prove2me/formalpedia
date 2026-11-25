-- Prove2me | solution 1 for GlobalTheory.dmonOf_mul_congr_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:31:24.873414+00:00
-- url     : https://prove2.me/submissions/0ce4e4a2-7a99-478e-8f9e-25679aef5f01

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DmonOfMulCongrOfCongr
import Theorems.Thm_GlobalTheory_ExpCong_along_add
import Theorems.Thm_GlobalTheory_ExpCong_along_mul_mem
import Theorems.Thm_GlobalTheory_ExpCong_dmonOf_eq_along
import Theorems.Thm_GlobalTheory_ExpCong_exists_along_eq_dmonOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) := by
  intro R _ d F I ι _ u f f' g h mo
  have hsub : ∀ (m : ι →₀ ℕ) (a b : PS R 1 d),
      DmonOf F u m (a - b) = DmonOf F u m a - DmonOf F u m b := fun m a b => by
    have e := ExpCong.along_add (fun l => Dof F (u l)) (fun l => GE.dof_add F (u l))
      (ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (a - b) b
    rw [sub_add_cancel, ← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along,
      ← ExpCong.dmonOf_eq_along] at e
    rw [e, add_sub_cancel_right]
  have key := ExpCong.along_mul_mem (fun l => Dof F (u l)) (constantCoeff : PS R 1 d →+* R)
    (fun a => GE.dof_add F (u a)) (fun a => GE.dof_mul F (u a)) Set.univ I.toAddSubgroup
    (fun s _ j hj => I.mul_mem_left s hj)
    (ExpCong.grouped (Finset.univ : Finset ι).toList mo).reverse g (f - f')
    (fun _ _ => Set.mem_univ _)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F u mo v hv
      rw [hm', hsub, map_sub]
      exact h m')
  rw [← ExpCong.dmonOf_eq_along, show g * (f - f') = f * g - f' * g by ring, hsub, map_sub] at key
  exact key
end GlobalTheory
