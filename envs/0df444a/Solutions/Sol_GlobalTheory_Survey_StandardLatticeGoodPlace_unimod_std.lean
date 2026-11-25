-- Prove2me | solution 1 for GlobalTheory.Survey.StandardLatticeGoodPlace.unimod_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:16:33.963926+00:00
-- url     : https://prove2.me/submissions/9b715bde-2fa8-45e8-ae9b-72d0393cb57c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ThetaIntegralityAtPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_StandardLatticeGoodPlace
import Theorems.Thm_GlobalTheory_Survey_StandardLatticeGoodPlace_mem_std
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Survey.StandardLatticeGoodPlace
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.ThetaIntegralityAtPlaces
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
private theorem algebraMap_range_mem_iff_isIntegral (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y, fun h => ⟨⟨x, h⟩, rfl⟩⟩
end GlobalTheory.Survey.StandardLatticeGoodPlace
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.StandardLatticeGoodPlace
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.ThetaIntegralityAtPlaces
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.Survey.StandardLatticeGoodPlace
theorem _root_.solution (H : Host E) (n : ℕ) : GenLat.Unimod (⟨stdLat E n⟩ : GenLat E n) := by
  intro v
  show v ∈ stdLat E n ↔ ∀ w ∈ stdLat E n, _
  simp only [mem_std]
  constructor
  · intro hv w hw
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hw j)
    exact (algebraMap_range_mem_iff_isIntegral _).2 (((algebraMap_range_mem_iff_isIntegral _).1 (hv j)).map
      ((IsCMField.complexConj E).toRingEquiv : E →+* E).toIntAlgHom)
  · intro h j
    have hs : ∀ i, (Pi.single j (1 : E) : Fin n → E) i ∈ (algebraMap (𝓞 E) E).range := by
      intro i
      rw [Pi.single_apply]
      split_ifs
      exacts [Subring.one_mem _, Subring.zero_mem _]
    have h1 := h (Pi.single j 1) hs
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h1
    have h2 := ((algebraMap_range_mem_iff_isIntegral _).1 h1).map
      ((IsCMField.complexConj E).toRingEquiv : E →+* E).toIntAlgHom
    exact (algebraMap_range_mem_iff_isIntegral _).2 (by simpa using h2)
end GlobalTheory.Survey.StandardLatticeGoodPlace
