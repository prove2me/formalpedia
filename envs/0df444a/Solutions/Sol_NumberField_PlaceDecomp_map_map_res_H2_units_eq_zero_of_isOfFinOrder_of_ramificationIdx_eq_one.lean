-- Prove2me | solution 1 for NumberField.PlaceDecomp.map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7adc3a6c-187e-5f56-945b-46c561acc05b

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceDecomp.coe_smul_integers PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_units coe_smul_integers subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one"
namespace CoordZeroUnram
p2m_open "NumberField.PlaceDecomp NumberField"

variable {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))

private theorem valued_eq_one_of_isOfFinOrder (c : (w.adicCompletion F)ˣ) (hc : IsOfFinOrder c) :
    Valued.v (c : w.adicCompletion F) = 1 := by
  obtain ⟨n, hn, hcn⟩ := hc.exists_pow_eq_one
  have hv : Valued.v (c : w.adicCompletion F) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hcn, Units.val_one, map_one]
  have hne : Valued.v (c : w.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr c.ne_zero
  obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hne
  rw [← hm] at hv ⊢
  rw [← WithZero.coe_pow, ← WithZero.coe_one, WithZero.coe_inj] at hv
  rw [← WithZero.coe_one, WithZero.coe_inj]
  have : n • Multiplicative.toAdd m = 0 := by
    rw [← toAdd_pow, hv]; rfl
  have hm0 : Multiplicative.toAdd m = 0 := by
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h hn.ne'
    · exact h
  exact Multiplicative.toAdd.injective hm0

private noncomputable def unitOfValuedEqOne (c : (w.adicCompletion F)ˣ) (hc : Valued.v (c : w.adicCompletion F) = 1) :
    (w.adicCompletionIntegers F)ˣ where
  val := ⟨(c : w.adicCompletion F), (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc.le⟩
  inv := ⟨((c⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F), (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hc, inv_one])⟩
  val_inv := Subtype.ext c.mul_inv
  inv_val := Subtype.ext c.inv_mul

private theorem coe_coe_unitOfValuedEqOne (c : (w.adicCompletion F)ˣ) (hc : Valued.v (c : w.adicCompletion F) = 1) :
    (((unitOfValuedEqOne w c hc : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F) : w.adicCompletion F) = c := rfl

private noncomputable abbrev unitsIncl : (w.adicCompletionIntegers F)ˣ →* (w.adicCompletion F)ˣ :=
  Units.map ((w.adicCompletionIntegers F).subtype : w.adicCompletionIntegers F →* w.adicCompletion F)

private theorem unitsIncl_injective : Function.Injective (unitsIncl (F := F) w) := by
  intro a b h
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun u : (w.adicCompletion F)ˣ => (u : w.adicCompletion F)) h

private theorem unitsIncl_smul (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (u : (w.adicCompletionIntegers F)ˣ) :
    unitsIncl w (g • u) = g • unitsIncl w u := by
  apply Units.ext
  show (((g • u : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F) : w.adicCompletion F) =
    ((g • unitsIncl w u : (w.adicCompletion F)ˣ) : w.adicCompletion F)
  rw [NumberField.PlaceDecomp.coe_smul_units]
  exact NumberField.PlaceDecomp.coe_smul_integers g _

end NumberField.PlaceDecomp.CoordZeroUnram

open NumberField.PlaceDecomp.CoordZeroUnram in
set_option maxHeartbeats 6400000 in

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F))
    (hunr : Ideal.ramificationIdx' (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) w.asIdeal = 1)
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hρ : ∀ u : Fˣ, ρ.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))
    (b : (F ≃ₐ[E] F) × (F ≃ₐ[E] F) → Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)
    (hb : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))
    (hfin : ∀ g : (F ≃ₐ[E] F) × (F ≃ₐ[E] F), IsOfFinOrder (Additive.toMul (b g) : Fˣ)) :
    (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) ρ 2).hom
      ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
        (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom
          ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom ⟨b, hb⟩)) = 0 := by
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _

  let ιw : Fˣ →* (w.adicCompletion F)ˣ := Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom
  have hιw : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (u : Fˣ), ιw ((g : F ≃ₐ[E] F) • u) = g • ιw u := by
    intro g u
    have h := Rep.hom_comm_apply ρ g (Additive.ofMul u)

    rw [hρ] at h
    have h' : ρ.hom (Additive.ofMul ((g : F ≃ₐ[E] F) • u)) = Additive.ofMul (g • ιw u) := h
    rw [hρ] at h'
    exact Additive.ofMul.injective h'

  let c : ↥(NumberField.PlaceDecomp.decomp E F w) × ↥(NumberField.PlaceDecomp.decomp E F w) → (w.adicCompletion F)ˣ :=
    fun gh => ιw (Additive.toMul (b ((gh.1 : F ≃ₐ[E] F), (gh.2 : F ≃ₐ[E] F))))
  have hc1 : ∀ gh, Valued.v ((c gh : (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1 :=
    fun gh => valued_eq_one_of_isOfFinOrder w (c gh) (MonoidHom.isOfFinOrder ιw (hfin _))
  let b'' : ↥(NumberField.PlaceDecomp.decomp E F w) × ↥(NumberField.PlaceDecomp.decomp E F w) → (w.adicCompletionIntegers F)ˣ :=
    fun gh => unitOfValuedEqOne w (c gh) (hc1 gh)
  have hb''c : ∀ gh, unitsIncl w (b'' gh) = c gh := fun gh => Units.ext rfl

  have hbmul := groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (M := Fˣ) (f := b) hb
  have hb''mul : groupCohomology.IsMulCocycle₂ b'' := by
    intro g h j
    apply unitsIncl_injective w
    rw [map_mul, map_mul, unitsIncl_smul, hb''c, hb''c, hb''c, hb''c]
    show ιw (Additive.toMul (b ((g * h : ↥(NumberField.PlaceDecomp.decomp E F w)), (j : F ≃ₐ[E] F)))) * ιw (Additive.toMul (b (g, h))) =
      g • ιw (Additive.toMul (b (h, j))) * ιw (Additive.toMul (b (g, (h * j : ↥(NumberField.PlaceDecomp.decomp E F w)))))
    rw [← hιw g, ← map_mul ιw, ← map_mul ιw]
    congr 1
    exact hbmul (g : F ≃ₐ[E] F) h j
  let A₀ := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletionIntegers F)ˣ
  let z₀ : cocycles₂ A₀ := groupCohomology.cocyclesOfIsMulCocycle₂ hb''mul

  let incl : A₀ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ :=
    M4aHerbrand.repHomOfMulEquivariant (unitsIncl w) (unitsIncl_smul (E := E) w)

  have hL : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) ρ 2).hom
      ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
        (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom
          ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom ⟨b, hb⟩)) =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) incl 2).hom ((H2π A₀).hom z₀) := by
    have e1 := congrArg (fun T => (ModuleCat.Hom.hom T) (⟨b, hb⟩ : cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)))
      (groupCohomology.H2π_comp_map (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) (NumberField.PlaceDecomp.decomp E F w).subtype
        (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))))
    have e2 := fun y => congrArg (fun T => (ModuleCat.Hom.hom T) y)
      (groupCohomology.H2π_comp_map (A := Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))
        (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) ρ)
    have e3 := congrArg (fun T => (ModuleCat.Hom.hom T) z₀)
      (groupCohomology.H2π_comp_map (A := A₀) (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) incl)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2 e3
    rw [e1, e2, e3]
    congr 1
    apply Subtype.ext
    funext gh
    show ρ.hom (b ((gh.1 : F ≃ₐ[E] F), (gh.2 : F ≃ₐ[E] F))) = Additive.ofMul (unitsIncl w (b'' gh))
    rw [hb''c, show b ((gh.1 : F ≃ₐ[E] F), (gh.2 : F ≃ₐ[E] F)) = Additive.ofMul (Additive.toMul (b ((gh.1 : F ≃ₐ[E] F), (gh.2 : F ≃ₐ[E] F)))) from rfl, hρ]
    rfl

  have hs : Subsingleton (groupCohomology A₀ 2) := by
    have := NumberField.PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one E F w
      (by rw [HeightOneSpectrum.under_asIdeal]; exact hunr) (((1 + 1 : ℕ) : ℤ))
    rwa [Rep.tateCohomology_ofNat_succ] at this
  rw [hL, Subsingleton.elim ((H2π A₀).hom z₀) 0, map_zero]

end S_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one (solution)
