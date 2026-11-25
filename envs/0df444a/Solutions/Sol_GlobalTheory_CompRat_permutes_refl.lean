-- Prove2me | solution 1 for GlobalTheory.CompRat.permutes_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:52.349057+00:00
-- url     : https://prove2.me/submissions/d1fb0539-4465-4fb0-acc4-8518ddbda668

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Statements_PrincipalLattices_FiniteDimensionalBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType
open GlobalTheory GlobalTheory.CompRat
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.CompRat
theorem _root_.solution (F : FamilyUnif Xo σ ty) : ConjugationPermutesPeriods F (RingEquiv.refl ℂ) id := fun i P hP =>
  ⟨P, hP, by
    have : spMap ((RingEquiv.refl ℂ : ℂ ≃+* ℂ) : ℂ →+* ℂ) = 𝟙 _ := Spec.map_id (CommRingCat.of ℂ)
    rw [this, Category.id_comp]; rfl⟩
end GlobalTheory.CompRat
