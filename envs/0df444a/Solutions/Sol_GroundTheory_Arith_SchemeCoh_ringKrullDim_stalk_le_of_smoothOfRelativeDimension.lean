-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ringKrullDim_stalk_le_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:43:12.825797+00:00
-- url     : https://prove2.me/submissions/da30d4ef-e632-4d41-821f-19bda3d0e6b6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ringKrullDim_localization_le_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing
universe u
open AlgebraicGeometry CategoryTheory
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (n : ℕ) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ n := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hUtop : U = ⊤ := eq_top_iff.mpr fun y _ ↦ Subsingleton.elim (f.base x) y ▸ e hx
  subst hUtop
  let eΓ := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have : IsRegularRing Γ(Spec (.of k), ⊤) := IsRegularRing.of_ringEquiv eΓ.symm
  have : IsNoetherianRing Γ(Spec (.of k), ⊤) := isNoetherianRing_of_ringEquiv k eΓ.symm
  have hdim0 : ringKrullDim Γ(Spec (.of k), ⊤) = 0 := by
    rw [ringKrullDim_eq_of_ringEquiv eΓ, ringKrullDim_eq_zero_of_field]
  algebraize [(f.appLE ⊤ V e).hom]
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n
    Γ(Spec (.of k), ⊤) Γ(X, V)
  algebraize [g.toRingHom]
  set P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P := hV.isLocalization_stalk ⟨x, hx⟩
  rw [← ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv (R := Γ(X, V)) P.primeCompl
    (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv]
  refine (ringKrullDim_localization_le_of_etale (P := MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))
    P).trans ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (P.under (MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))) (Localization.AtPrime _)]
  refine (Ideal.height_le_ringKrullDim_of_isPrime).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hdim0]
  simp
end GroundTheory.Arith.SchemeCoh
