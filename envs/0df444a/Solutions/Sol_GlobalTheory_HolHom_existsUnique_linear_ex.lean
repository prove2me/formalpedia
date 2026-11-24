-- Prove2me | solution 1 for GlobalTheory.HolHom.existsUnique_linear_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:57:43.306871+00:00
-- url     : https://prove2.me/submissions/a3c7adc8-0f8c-45d8-9e53-79da182418b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_existsUnique_linear
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_ex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
namespace GlobalTheory.HolHom
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    {e : V → (Over.mk (Fu.u i P) ⟶ Xo.univ.t.G)} (he : ∀ z w, e (z + w) = e z * e w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) :
    ∃! h : V →ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = Fu.ex i P (h z) :=
  existsUnique_linear he (Fu.ex_add i P hP) hol (isHolTo_ex Fu i hP) (Fu.ex_diff i P hP).2
end GlobalTheory.HolHom
