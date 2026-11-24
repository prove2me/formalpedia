-- Prove2me | solution 1 for GlobalTheory.exists_fg_subalgebra_spec_factors_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:41:24.389187+00:00
-- url     : https://prove2.me/submissions/be2bdc70-5835-403a-8189-bb56a7bdb00c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFgSubalgebraSpecFactorThroughOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (R : Subalgebra o Ω) (hR : R.FG) (V : (Sp R).Opens) (hV : (V : Set (Sp R)).Nonempty) :
    ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧
      ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  classical
  obtain ⟨x, hx⟩ := hV
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := x) (u := (V : Set (Sp R))) hx V.isOpen
  have hf0 : (f : Ω) ≠ 0 := by
    intro h0
    have : f = 0 := Subtype.ext h0
    subst this
    exact hxf (Ideal.zero_mem _)
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (({(f : Ω)⁻¹} : Finset Ω) : Set Ω)
  have h : R ≤ R' := le_sup_left
  have hinv : (f : Ω)⁻¹ ∈ R' :=
    (le_sup_right : _ ≤ R') (Algebra.subset_adjoin (by simp))
  refine ⟨R', h, hR.sup (Subalgebra.fg_adjoin_finset _), ?_⟩
  have hu : IsUnit ((Subalgebra.inclusion h).toRingHom f) :=
    IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : R') (Subtype.ext (mul_inv_cancel₀ hf0))
  refine ⟨IsOpenImmersion.lift V.ι (spMap (Subalgebra.inclusion h).toRingHom) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  apply hfV
  intro hm
  exact y.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
end GlobalTheory
