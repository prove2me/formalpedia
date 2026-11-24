-- Prove2me | solution 1 for GlobalTheory.FlatThickenings.flat_of_flat_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:47:02.400086+00:00
-- url     : https://prove2.me/submissions/ef578c67-593a-4a0f-99f9-23490727cf96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemPowOfFlatQuotient
import Theorems.Thm_GlobalTheory_FlatThickenings_mem_pow_of_flat_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatThickenings
namespace GlobalTheory.FlatThickenings
theorem _root_.solution {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsNoetherianRing C] (σ : V →+* C)
    (h : ∀ e : ℕ, (Ideal.quotientMap ((IsLocalRing.maximalIdeal V ^ (e + 1)).map σ) σ
      (Ideal.le_comap_map (I := IsLocalRing.maximalIdeal V ^ (e + 1)))).Flat) : σ.Flat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ a : C, σ ϖ * a = 0 → a = 0 := by
    intro a ha
    have hm : a ∈ ⨅ i : ℕ, (Ideal.span {σ ϖ} ^ i • ⊤ : Submodule C C) := by
      rw [Submodule.mem_iInf]
      intro e
      rw [smul_eq_mul, Ideal.mul_top]
      exact mem_pow_of_flat_quotient σ hϖ.ne_zero _ hϖ.maximalIdeal_eq e (h e) ha
    obtain ⟨⟨r, hr⟩, hra⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff _ a).1 hm
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [← hra]
    change c * σ ϖ * a = 0
    rw [_root_.mul_assoc, ha, mul_zero]
  have keyn : ∀ (n : ℕ) (a : C), σ ϖ ^ n * a = 0 → a = 0 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; exact key a (ih _ (by rw [← ha]; ring))
  let _ := σ.toAlgebra
  change Module.Flat V C
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨v, hv⟩, hva⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hv) hϖ
  have h1 : σ (u * ϖ ^ n) * a = 0 := hva
  rw [map_mul, _root_.mul_assoc, map_pow] at h1
  exact keyn n a (((u.isUnit.map σ).mul_right_eq_zero).1 h1)
end GlobalTheory.FlatThickenings
