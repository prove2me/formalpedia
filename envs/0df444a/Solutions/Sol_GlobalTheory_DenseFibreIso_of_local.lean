-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:59.245798+00:00
-- url     : https://prove2.me/submissions/1beced0c-3582-4f5c-878f-bab1fa30ad99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Γ' X : Scheme.{0}} (s : X ⟶ Sp R) (f : Γ' ⟶ X)
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] [IsProper s]
    (P : Set (Ideal R)) (hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p)
    (h : ∀ x : X, (s x).asIdeal ∈ P → ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Γ')
      (f' : T' ⟶ T), IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f') :
    Q f := by
  let W : Set X := {x | ∃ U : X.Opens, x ∈ U ∧ Q (f ∣_ U)}
  have hW : IsOpen W := isOpen_iff_forall_mem_open.2 fun x ⟨U, hx, hU⟩ =>
    ⟨U, fun y hy => ⟨U, hy, hU⟩, U.isOpen, hx⟩
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  by_contra hx
  have hc : IsClosed (s '' Wᶜ) := s.isClosedMap _ hW.isClosed_compl
  obtain ⟨p, hp, hp', hle⟩ := hP (s x).asIdeal (s x).isPrime
  have hsp : s x ⤳ (⟨p, hp'⟩ : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 hle
  obtain ⟨y, hy, hy'⟩ := hsp.mem_closed hc ⟨x, hx, rfl⟩
  obtain ⟨T, T', g, g', f', H, _, hg, hQ⟩ := h y (by rw [hy']; exact hp)
  refine hy ⟨g.opensRange, hg, ?_⟩
  have H' : IsPullback (f' ≫ g.isoOpensRange.hom) g' g.opensRange.ι f :=
    H.of_iso (Iso.refl _) g.isoOpensRange (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  have H'' := isPullback_morphismRestrict f g.opensRange
  rw [← H''.isoIsPullback_hom_fst _ _ H', Q.cancel_left_of_respectsIso,
    Q.cancel_right_of_respectsIso]
  exact hQ
end GlobalTheory.DenseFibreIso
