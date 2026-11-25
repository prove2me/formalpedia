-- Prove2me | solution 1 for GlobalTheory.SectionBasis.exists_dvd_of_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:11.686729+00:00
-- url     : https://prove2.me/submissions/da27bb06-7d0f-40de-acf9-cfc826618942

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}
namespace GlobalTheory.SectionBasis
theorem _root_.solution {P F S L : Type} [CommRing P] [IsDomain P] [Field F] [Algebra P F]
    [IsFractionRing P F] [CommRing S] [IsDomain S] [Field L] [Algebra F L] [FiniteDimensional F L]
    (φ : P →+* S) (i : S →+* L) (hi : Function.Injective i)
    (h : ∀ q, algebraMap F L (algebraMap P F q) = i (φ q)) (f : S) (hf : f ≠ 0) :
    ∃ q : P, q ≠ 0 ∧ f ∣ φ q := by
  letI : Algebra P S := φ.toAlgebra
  letI : Algebra S L := i.toAlgebra
  letI : Algebra P L := (i.comp φ).toAlgebra
  haveI : IsScalarTower P F L := IsScalarTower.of_algebraMap_eq fun q => (h q).symm
  haveI : IsScalarTower P S L := IsScalarTower.of_algebraMap_eq fun q => rfl
  have h1 : IsAlgebraic F (algebraMap S L f) := Algebra.IsAlgebraic.isAlgebraic _
  have h2 := (IsFractionRing.isAlgebraic_iff P F L).2 h1
  have h3 := (isAlgebraic_algebraMap_iff hi).1 h2
  exact h3.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)
end GlobalTheory.SectionBasis
