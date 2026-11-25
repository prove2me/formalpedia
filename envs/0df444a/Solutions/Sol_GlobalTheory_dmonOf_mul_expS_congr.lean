-- Prove2me | solution 1 for GlobalTheory.dmonOf_mul_expS_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:31:13.86504+00:00
-- url     : https://prove2.me/submissions/dccb4500-7de7-4cc0-bd2a-234b6d1c426a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Theorems.Thm_GlobalTheory_ExpCong_along_mul_exp
import Theorems.Thm_GlobalTheory_ExpCong_dmonOf_eq_along
import Theorems.Thm_GlobalTheory_ExpCong_exists_along_eq_dmonOf
import Theorems.Thm_GlobalTheory_NablaExpConj_Dof_expS
import Theorems.Thm_GlobalTheory_map_dmonOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_exp


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (φ : PS k 1 d), constantCoeff φ = 0 → (∀ m : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m φ) = algebraMap R k r) → ∀ (f : PS R 1 d) (m : ι →₀ ℕ), ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m (FB.toK k f * FB.expS k φ)) = algebraMap R k (constantCoeff (DmonOf F u m f) + r) := by
  intro R _ d k _ _ _ F I ι _ u φ hφ0 hφ f m
  set F' : Fin d → PS k 2 d := fun i => MvPowerSeries.map (algebraMap R k) (F i) with hF'
  set u' : ι → Fin d → k := fun l i => algebraMap R k (u l i) with hu'
  have hmap : ∀ m' : ι →₀ ℕ, constantCoeff (DmonOf F' u' m' (FB.toK k f)) =
      algebraMap R k (constantCoeff (DmonOf F u m' f)) := fun m' => by
    rw [hF', hu', FB.toK, ← map_dmonOf, constantCoeff_map]
  have key := ExpCong.along_mul_exp (fun l => Dof F' (u' l)) (constantCoeff : PS k 1 d →+* k)
    (fun a => GE.dof_add F' (u' a)) (fun a => GE.dof_mul F' (u' a)) (Set.range (algebraMap R k))
    (I.toAddSubgroup.map (algebraMap R k).toAddMonoidHom)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨j, hj, rfl⟩
      exact ⟨s * j, I.mul_mem_left s hj, map_mul (algebraMap R k) s j⟩)
    (by
      rintro _ ⟨j, -, rfl⟩
      exact ⟨j, rfl⟩)
    (FB.expS k φ) φ (fun a => NablaExpConj.Dof_expS k F' (u' a) hφ0) (WickVanishing.constantCoeff_exp hφ0)
    (ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (FB.toK k f)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      exact ⟨_, by rw [hm', hmap]⟩)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      obtain ⟨r, hr, e⟩ := hφ m'
      exact ⟨r, hr, by rw [hm', e]; rfl⟩)
  rw [← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along, hmap] at key
  obtain ⟨r, hr, e⟩ := key
  refine ⟨r, hr, ?_⟩
  have e' : algebraMap R k r = _ := e
  rw [map_add, e']
  ring
end GlobalTheory
