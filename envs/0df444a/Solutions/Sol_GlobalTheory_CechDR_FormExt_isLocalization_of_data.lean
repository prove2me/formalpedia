-- Prove2me | solution 1 for GlobalTheory.CechDR.FormExt.isLocalization_of_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:39:36.445801+00:00
-- url     : https://prove2.me/submissions/70a75765-32cc-479a-a043-5234b4eaf439

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocOAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData

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
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExt
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CechDR.FormExt
theorem _root_.solution {T T' : C} (l : T ⟶ T') (b : F.obj T) (h1 : IsUnit (mp F l b))
    (h2 : ∀ y : F.obj T', ∃ (n : ℕ) (x : F.obj T), y * mp F l b ^ n = mp F l x)
    (h3 : ∀ x : F.obj T, mp F l x = 0 → ∃ n : ℕ, b ^ n * x = 0) :
    letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
    IsLocalization.Away b (F.obj T') := by
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  refine ⟨?_, fun z ↦ ?_, fun {x y} e ↦ ?_⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit (mp F l (b ^ n))
    rw [map_pow]; exact h1.pow n
  · obtain ⟨n, x, e⟩ := h2 z
    refine ⟨(x, ⟨b ^ n, n, rfl⟩), ?_⟩
    change z * mp F l (b ^ n) = mp F l x
    rw [map_pow]; exact e
  · obtain ⟨n, hn⟩ := h3 (x - y) (by rw [map_sub]; exact sub_eq_zero.2 e)
    exact ⟨⟨b ^ n, n, rfl⟩, sub_eq_zero.1 (by rw [← mul_sub]; exact hn)⟩
end GlobalTheory.CechDR.FormExt
