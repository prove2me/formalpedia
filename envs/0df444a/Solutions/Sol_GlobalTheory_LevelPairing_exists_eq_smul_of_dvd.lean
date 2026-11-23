-- Prove2me | solution 1 for GlobalTheory.LevelPairing.exists_eq_smul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:35.588646+00:00
-- url     : https://prove2.me/submissions/8d2f4355-b883-4cab-8b27-db0ec9d508a4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos

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
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.LevelPairing
theorem _root_.solution (x : Dw.La) (m : ℕ) (hm : m ≠ 0) (h : ∀ y, (m : ℤ) ∣ Dw.EF x y) :
    ∃ z, x = (m : ℤ) • z := by
  let f : Dw.La →ₗ[ℤ] ℤ :=
    { toFun := fun y => Dw.EF x y / m
      map_add' := fun a b => by rw [map_add, Int.add_ediv_of_dvd_left (h a)]
      map_smul' := fun k a => by
        rw [map_zsmul]; simp only [smul_eq_mul, RingHom.id_apply]; exact Int.mul_ediv_assoc _ (h a) }
  obtain ⟨z, hz⟩ := Dw.unimod.2 f
  refine ⟨z, Dw.unimod.1 ?_⟩
  ext y
  rw [map_zsmul, hz]
  simp only [LinearMap.smul_apply, smul_eq_mul, f, LinearMap.coe_mk, AddHom.coe_mk]
  exact (Int.mul_ediv_cancel' (h y)).symm
end GlobalTheory.LevelPairing
