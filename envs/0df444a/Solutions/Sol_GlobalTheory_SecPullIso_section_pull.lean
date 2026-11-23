-- Prove2me | solution 1 for GlobalTheory.SecPullIso.section_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:25.965153+00:00
-- url     : https://prove2.me/submissions/a9369f77-ea06-4bb7-9212-2793ad38cd08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionPull
import Theorems.Thm_GlobalTheory_SecPullIso_isUnit_gs_iff
import Theorems.Thm_GlobalTheory_SecPullIso_exists_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SecPullIso
namespace GlobalTheory.SecPullIso
theorem _root_.solution : ∀ (X X' : Scheme.{0}) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull φ)), H.IsLB → H'.IsLB → w.IsGen → ∀ s : LB.Sec H, (∃! s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k'))) ∧ ∀ s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) → nonzeroLocus s' = φ ⁻¹ᵁ nonzeroLocus s := by
  intro X X' φ H H' w hH hH' hw s
  constructor
  · obtain ⟨s', hs'⟩ := exists_pull φ H H' w hH hH' hw s
    refine ⟨s', hs', fun t ht => ?_⟩
    obtain ⟨f, hf⟩ := t
    obtain ⟨g, hg⟩ := s'
    obtain rfl : f = g := funext fun k' => fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hH (φ z)
      exact (Units.mul_right_inj _).1 ((ht z k k' hk hz).symm.trans (hs' z k k' hk hz))
    rfl
  · intro s' hs'
    have key : ∀ (z : X') (k : H.ι) (k' : H'.ι), φ z ∈ H.U k → z ∈ H'.U k' →
        (φ z ∈ X.basicOpen (s.f k) ↔ z ∈ X'.basicOpen (s'.f k')) := fun z k k' hk hk' => by
      rw [← isUnit_gs_iff φ z hk, hs' z k k' hk hk', Units.isUnit_units_mul]
      exact isUnit_gs_iff (𝟙 X') z hk' _
    ext z
    constructor
    · intro hz
      obtain ⟨k', hk'⟩ := Opens.mem_iSup.1 hz
      obtain ⟨k, hk⟩ := exists_chart hH (φ z)
      exact Opens.mem_iSup.2 ⟨k, (key z k k' hk (X'.basicOpen_le _ hk')).2 hk'⟩
    · intro hz
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show φ z ∈ nonzeroLocus s from hz)
      obtain ⟨k', hk'⟩ := exists_chart hH' z
      exact Opens.mem_iSup.2 ⟨k', (key z k k' (X.basicOpen_le _ hk) hk').1 hk⟩
end GlobalTheory.SecPullIso
