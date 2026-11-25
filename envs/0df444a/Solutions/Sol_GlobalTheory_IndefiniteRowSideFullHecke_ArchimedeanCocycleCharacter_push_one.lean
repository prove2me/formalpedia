-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter.push_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:49:32.286855+00:00
-- url     : https://prove2.me/submissions/4439f704-8cd8-466d-bd85-df1feae6be98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ArchimedeanCocycleCharacter

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter
theorem _root_.solution (c : Coeff l) (n : ℕ) :
    push (Dw := Dw) c (1 : Matrix (Fin n) (Fin n) E) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, i, j⟩
  simp only [push, letB, MvPolynomial.aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne hb]
  · simp
end GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter
