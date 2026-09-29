-- Prove2me | solution 1 for ModularCurve.exists_coeffEmb_basis_of_forall_coeffMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a1cfc2a2-1477-5d0d-85f0-b74ba35060b7

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ModPFormFn
import Theorems.Thm_Submodule_span_fixedPoints_semilinear_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeffEmb_basis_of_forall_coeffMap_mem

set_option autoImplicit false

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (V : Submodule L (LaurentSeries L)) [FiniteDimensional L V]
    (hV : ∀ (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries L), x ∈ V → ModularCurve.coeffMap (σ : L →+* L) x ∈ V) :
    ∃ (n : ℕ) (Y : Fin n → LaurentSeries ℚ),
      LinearIndependent L (fun i => ModularCurve.coeffEmb L (Y i)) ∧
      Submodule.span L (Set.range fun i => ModularCurve.coeffEmb L (Y i)) = V := by
  classical

  let ρ : (L ≃ₐ[ℚ] L) → V →+ V := fun σ =>
    { toFun := fun v => ⟨ModularCurve.coeffMap (σ : L →+* L) v, hV σ v v.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  have hρ : ∀ σ (v : V), ((ρ σ v : V) : LaurentSeries L) = ModularCurve.coeffMap (σ : L →+* L) v := fun _ _ => rfl
  have hρ_smul : ∀ (σ : L ≃ₐ[ℚ] L) (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v := by
    intro σ a v
    apply Subtype.ext
    rw [hρ, Submodule.coe_smul, Submodule.coe_smul, hρ]
    ext k
    simp only [ModularCurve.coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul]
    rfl
  have hρ_one : ∀ v : V, ρ 1 v = v := fun v => Subtype.ext (by
    rw [hρ]; ext k; simp [ModularCurve.coeffMap_coeff])
  have hρ_mul : ∀ (σ τ : L ≃ₐ[ℚ] L) (v : V), ρ (σ * τ) v = ρ σ (ρ τ v) := fun σ τ v => Subtype.ext (by
    rw [hρ, hρ, hρ]; ext k; simp [ModularCurve.coeffMap_coeff, AlgEquiv.mul_apply])
  have hspan := Submodule.span_fixedPoints_semilinear_eq_top ℚ L V ρ hρ_smul hρ_one hρ_mul

  have hfix : ∀ v : V, (∀ σ, ρ σ v = v) → ∃ y : LaurentSeries ℚ, ModularCurve.coeffEmb L y = v := by
    intro v hv
    have hcoef : ∀ k : ℤ, ∃ c : ℚ, algebraMap ℚ L c = (v : LaurentSeries L).coeff k := by
      intro k
      have hk : ∀ σ : L ≃ₐ[ℚ] L, σ ((v : LaurentSeries L).coeff k) = (v : LaurentSeries L).coeff k := fun σ => by
        have := congrArg (fun w : V => (w : LaurentSeries L).coeff k) (hv σ)
        simpa [hρ] using this
      have hmem : (v : LaurentSeries L).coeff k ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[ℚ] L)) := by
        rw [IntermediateField.mem_fixedField_iff]
        exact fun σ _ => hk σ
      rw [← IntermediateField.fixingSubgroup_bot, IsGalois.fixedField_fixingSubgroup, IntermediateField.mem_bot] at hmem
      exact hmem
    choose c hc using hcoef
    refine ⟨⟨c, (v : LaurentSeries L).isPWO_support.mono ?_⟩, ?_⟩
    · intro k hk
      rw [Function.mem_support] at hk
      rw [HahnSeries.mem_support]
      intro h0
      exact hk ((map_eq_zero_iff _ (algebraMap ℚ L).injective).mp ((hc k).trans h0))
    · ext k
      exact hc k

  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent L {v : V | ∀ σ : L ≃ₐ[ℚ] L, ρ σ v = v}
  rw [hspan] at hbspan
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  choose y hy using fun v : b => hfix v (hbS v.2)
  let e := Fintype.equivFin b
  have hfam : (fun i : Fin (Fintype.card b) => ModularCurve.coeffEmb L (y (e.symm i))) =
      (fun v : b => ((v : V) : LaurentSeries L)) ∘ e.symm := by
    funext i
    simp only [Function.comp_apply, hy]
  refine ⟨Fintype.card b, fun i => y (e.symm i), ?_, ?_⟩
  · rw [hfam]
    exact (hbli.map' V.subtype (Submodule.ker_subtype V)).comp _ e.symm.injective
  · rw [hfam, e.symm.surjective.range_comp]
    have hrange : Set.range (fun v : b => ((v : V) : LaurentSeries L)) = V.subtype '' b := by
      ext x
      constructor
      · rintro ⟨⟨v, hv⟩, rfl⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩
    rw [hrange, Submodule.span_image, hbspan, Submodule.map_top, Submodule.range_subtype]

end S_ModularCurve_exists_coeffEmb_basis_of_forall_coeffMap_mem
end P2MW
export P2MW.S_ModularCurve_exists_coeffEmb_basis_of_forall_coeffMap_mem (solution)
