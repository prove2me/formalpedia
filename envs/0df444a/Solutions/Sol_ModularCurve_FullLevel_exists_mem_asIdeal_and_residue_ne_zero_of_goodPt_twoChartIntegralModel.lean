-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_mem_asIdeal_and_residue_ne_zero_of_goodPt_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/58b51efc-106c-525b-8858-ceff833fbc85

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

import Theorems.Thm_ModularCurve_mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_mem_asIdeal_and_residue_ne_zero_of_goodPt_twoChartIntegralModel

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace GPNMAux

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem isAlgebraic_of_forall_mem_residue_eq_zero
    {A₁ : Type*} [CommRing A₁] {T : Type*} [Field T] [Algebra A₁ T]
    {F : Type*} [Field F] {E : Type*} [Field E] {κ : Type*} [Field κ] [Algebra κ E]
    (B : Subalgebra A₁ T) (t : T) (htB : t ∈ B)
    (hint : ∀ b : ↥B, IsIntegral ↥(Algebra.adjoin A₁ ({t} : Set T)) (b : T))
    (ι : T →+* F) (O : ValuationSubring F)
    (hAO : ∀ a : A₁, ι (algebraMap A₁ T a) ∈ O) (htO : ι t ∈ O) (htO' : (ι t)⁻¹ ∈ O) (ht0 : ι t ≠ 0)
    (res : ↥O →+* E) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥O)
    (c₀ : A₁ →+* κ) (hconst : ∀ a : A₁, res ⟨ι (algebraMap A₁ T a), hAO a⟩ = algebraMap κ E (c₀ a))
    (y : Ideal ↥B) [hy : y.IsMaximal]
    (hbr : ∀ b : ↥B, ι (b : T) ∈ O.nonunits → b ∈ y)
    (hBO : ∀ b : ↥B, ι (b : T) ∈ O)
    (H : ∀ b : ↥B, b ∈ y → res ⟨ι (b : T), hBO b⟩ = 0) :
    IsAlgebraic κ (res ⟨ι t, htO⟩) := by
  classical

  let ιB : ↥B →+* ↥O :=
    { toFun := fun b => ⟨ι (b : T), hBO b⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let ψ : ↥B →+* E := res.comp ιB
  have hψ : ∀ b : ↥B, ψ b = res ⟨ι (b : T), hBO b⟩ := fun _ => rfl

  have hkerψ : RingHom.ker ψ = y := by
    ext b
    rw [RingHom.mem_ker]
    constructor
    · intro h0
      apply hbr
      have : ιB b ∈ RingHom.ker res := h0
      rw [hker] at this
      exact (ValuationSubring.coe_mem_nonunits_iff).mpr this
    · exact H b

  have hRg : IsField ↥ψ.range := by
    haveI : (RingHom.ker ψ).IsMaximal := by rw [hkerψ]; exact hy
    letI : Field (↥B ⧸ RingHom.ker ψ) := Ideal.Quotient.field _
    exact MulEquiv.isField (Field.toIsField _) (RingHom.quotientKerEquivRange ψ).symm.toMulEquiv

  have hadjB : Algebra.adjoin A₁ ({t} : Set T) ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr htB)
  let θ : ↥(Algebra.adjoin A₁ ({t} : Set T)) →+* ↥B := (Subalgebra.inclusion hadjB).toRingHom
  have hθ : ∀ z, ((θ z : ↥B) : T) = (z : T) := fun _ => rfl
  let Sθ : Subring E := (ψ.comp θ).range
  have hSR : Sθ ≤ ψ.range := by
    rintro e ⟨z, rfl⟩; exact ⟨θ z, rfl⟩
  letI algSR : Algebra ↥Sθ ↥ψ.range := (Subring.inclusion hSR).toAlgebra
  have hinjSR : Function.Injective (algebraMap ↥Sθ ↥ψ.range) := Subring.inclusion_injective hSR

  haveI : Algebra.IsIntegral ↥Sθ ↥ψ.range := by
    refine ⟨fun r => ?_⟩
    obtain ⟨b, hb⟩ := r.2
    obtain ⟨p, hpm, hp0⟩ := hint b

    have hpB : p.eval₂ θ b = 0 := by
      apply Subtype.val_injective
      rw [show ((p.eval₂ θ b : ↥B) : T) = (algebraMap ↥B T) (p.eval₂ θ b) from rfl, Polynomial.hom_eval₂]
      first | simpa using hp0 | exact hp0
    have hpE : (p.map ((ψ.comp θ).rangeRestrict)).eval₂ (algebraMap ↥Sθ ↥ψ.range) r = 0 := by
      apply Subtype.val_injective
      rw [show ((Polynomial.eval₂ (algebraMap ↥Sθ ↥ψ.range) r (p.map (ψ.comp θ).rangeRestrict) : ↥ψ.range) : E) =
        (ψ.range.subtype) (Polynomial.eval₂ (algebraMap ↥Sθ ↥ψ.range) r (p.map (ψ.comp θ).rangeRestrict)) from rfl,
        Polynomial.hom_eval₂, Polynomial.eval₂_map]
      have h2 := congrArg ψ hpB
      rw [Polynomial.hom_eval₂, map_zero] at h2
      rw [show (ψ.range.subtype) r = ψ b from hb.symm]
      convert h2 using 2 <;> try rfl
    exact ⟨p.map _, hpm.map _, hpE⟩
  have hSθ : IsField ↥Sθ := isField_of_isIntegral_of_isField hinjSR hRg

  set ρ := res ⟨ι t, htO⟩ with hρ
  have hρψ : ψ ⟨t, htB⟩ = ρ := rfl
  have hρS : ρ ∈ Sθ := ⟨⟨t, Algebra.self_mem_adjoin_singleton A₁ t⟩, rfl⟩
  have hρ0 : ρ ≠ 0 := by
    intro h0
    have hm : (⟨ι t, htO⟩ : ↥O) ∈ RingHom.ker res := h0
    rw [hker] at hm
    apply (IsLocalRing.mem_maximalIdeal _).mp hm
    exact IsUnit.of_mul_eq_one ⟨(ι t)⁻¹, htO'⟩ (Subtype.ext (mul_inv_cancel₀ ht0))
  obtain ⟨s, hs⟩ := hSθ.mul_inv_cancel (a := ⟨ρ, hρS⟩) (fun h => hρ0 (congrArg Subtype.val h))
  obtain ⟨z, hz⟩ := s.2
  obtain ⟨P, hP⟩ : (z : T) ∈ (Polynomial.aeval (R := A₁) t).range :=
    (Algebra.adjoin_singleton_eq_range_aeval A₁ t).le z.2

  have hθz : θ z = Polynomial.eval₂ (algebraMap A₁ ↥B) ⟨t, htB⟩ P := by
    apply Subtype.val_injective
    rw [hθ, ← hP, show ((Polynomial.eval₂ (algebraMap A₁ ↥B) ⟨t, htB⟩ P : ↥B) : T) =
      (algebraMap ↥B T) (Polynomial.eval₂ (algebraMap A₁ ↥B) ⟨t, htB⟩ P) from rfl, Polynomial.hom_eval₂,
      ← IsScalarTower.algebraMap_eq]
    rfl
  have hψA : ψ.comp (algebraMap A₁ ↥B) = (algebraMap κ E).comp c₀ := RingHom.ext fun a => hconst a
  have hsE : (s : E) = P.eval₂ ((algebraMap κ E).comp c₀) ρ := by
    rw [← hz, RingHom.comp_apply, hθz, Polynomial.hom_eval₂, hψA]
    rfl
  have hρs : ρ * (s : E) = 1 := by
    have := congrArg Subtype.val hs
    simpa using this

  refine ⟨Polynomial.X * P.map c₀ - 1, ?_, ?_⟩
  · intro h0
    have := congrArg (fun Q : Polynomial κ => Q.coeff 0) h0
    simp at this
  · rw [map_sub, map_one, map_mul, Polynomial.aeval_X, Polynomial.aeval_def, Polynomial.eval₂_map, ← hsE, hρs, sub_self]

end GPNMAux

open GPNMAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 25600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    ∀ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))),
      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) →

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    let OffBranch : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      ∀ ℓ : CuspidalType.ProjLine q, ℓ ≠ lineInfty q →
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal) ∧
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal)

    ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x →
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ∃ h : ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers,
          b ∈ y.asIdeal ∧ R.residue ⟨((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')), h⟩ ≠ 0) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ∃ h : ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers,
          b ∈ y.asIdeal ∧ R.residue ⟨((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')), h⟩ ≠ 0) := by
  intro F₀ hK1 hStab hLD hRAT instA₁T hconst j₁ hj₁ instFact NIg hN
  intro InStalk InMax Centred GoodPt Reads OffBranch x hx
  have hspec := hx.1
  have hcl := hx.2.1
  have hbrF := hx.2.2.1
  have hbrI := hx.2.2.2.1
  classical

  let toA : ↥A₁ →+* ↥A :=
    { toFun := fun a => ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ a).mp a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let c₀ : ↥A₁ →+* ResidueField ↥A := (IsLocalRing.residue ↥A).comp toA
  let ι : (type_of% j₁) →+* ↥(fieldBar q M') := algebraMap (type_of% j₁) ↥(fieldBar q M')
  have hι : ∀ f : (type_of% j₁), ι f = (f : ↥(fieldBar q M')) := fun _ => rfl
  have hAO : ∀ a : ↥A₁, ι (algebraMap ↥A₁ (type_of% j₁) a) ∈ R.integers := by
    intro a; rw [hι, hconst, R.algebraMap_mem_iff]; exact (hA₁ a).mp a.2
  have hconstE : ∀ a : ↥A₁, R.residue ⟨ι (algebraMap ↥A₁ (type_of% j₁) a), hAO a⟩ = algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) (c₀ a) := by
    intro a
    rw [show c₀ a = IsLocalRing.residue ↥A (toA a) from rfl, ← R.residue_algebraMap (toA a)]
    congr 1
    exact Subtype.ext ((hι _).trans (hconst a))

  have hjqA : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [ModularCurve.coeffSemilinearAut.coeffMap_jqModC]
    exact (ModularCurve.coeffSemilinearAut.coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm
  have hjκ : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) :=
    ModularCurve.coeffSemilinearAut.coeffMap_jqModC _
  have hjZ : (jqModC ℤ).coeff (-1 : ℤ) = 1 := by
    have h : ((jqModC ℤ).coeff (-1 : ℤ) : ℚ) = (jqModC ℚ).coeff (-1 : ℤ) := by
      rw [jqModC_eq_map_intCast (K := ℚ), HahnSeries.map_coeff]; rfl
    rw [jqModC_rat, coeff_jq_neg_one] at h
    exact_mod_cast h
  have hcoeffκ : ∀ (K : Type) [CommRing K], (jqModC K).coeff (-1 : ℤ) = 1 := by
    intro K _
    rw [jqModC_eq_map_intCast (K := K), HahnSeries.map_coeff, hjZ]; simp
  have hjκ0 : jqModC (ResidueField ↥A) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun s => HahnSeries.coeff s (-1 : ℤ)) h0
    simp only [hcoeffκ, HahnSeries.coeff_zero] at h1
    exact one_ne_zero h1
  have hj₁L : ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by rw [hj₁]; rfl
  have hjL0 : coeffEmb (AlgebraicClosure ℚ) jq ≠ 0 := by
    intro h0
    have h1 := congrArg (fun s => HahnSeries.coeff s (-1 : ℤ)) h0
    simp only [HahnSeries.coeff_zero] at h1
    rw [← hjqA, ModularCurve.coeffSemilinearAut.coeffMap_jqModC, hcoeffκ] at h1
    exact one_ne_zero h1
  have hj₁0 : (j₁ : ↥(fieldBar q M')) ≠ 0 := fun h => hjL0 (by rw [← hj₁L, h]; rfl)
  have hj₁O : (j₁ : ↥(fieldBar q M')) ∈ R.integers := by
    rw [hR, hIg_inf]
    exact ⟨jqModC ↥A, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one, hjqA, hj₁L]⟩
  have hj₁O' : (j₁ : ↥(fieldBar q M'))⁻¹ ∈ R.integers := by
    rw [hR, hIg_inf]
    refine ⟨1, jqModC ↥A, by rw [hjκ]; exact hjκ0, ?_⟩
    rw [map_one, hjqA, ← hj₁L]
    have hne : ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by rw [hj₁L]; exact hjL0
    exact inv_mul_cancel₀ hne

  have chartSubO : ∀ t : (type_of% j₁), ι t ∈ R.integers → ∀ b : (type_of% j₁),
      b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg ↥A₁ (type_of% j₁) ({t} : Set (type_of% j₁)) → ι b ∈ R.integers := by
    intro t htO b hb
    have hadjO : ∀ z ∈ Algebra.adjoin ↥A₁ ({t} : Set (type_of% j₁)), ι z ∈ R.integers := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact htO
      | algebraMap a => exact hAO a
      | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
      | mul x z _ _ hx hz => rw [map_mul]; exact mul_mem hx hz
    let θO : ↥(Algebra.adjoin ↥A₁ ({t} : Set (type_of% j₁))) →+* ↥R.integers :=
      { toFun := fun z => ⟨ι z, hadjO z z.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp) }
    obtain ⟨p, hpm, hp0⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff ↥A₁ (type_of% j₁)).mp hb
    have hint : IsIntegral ↥R.integers (ι b) := by
      refine ⟨p.map θO, hpm.map θO, ?_⟩
      rw [Polynomial.eval₂_map]
      have h := congrArg ι hp0
      rw [Polynomial.hom_eval₂, map_zero] at h
      exact h
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥R.integers) (K := ↥(fieldBar q M'))).mp hint
    rw [← hz]; exact z.2

  obtain ⟨jN, hjN, -⟩ := hN
  have hjq₀mem : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hjqA]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨h₀, hres₀⟩ := hR₀ (jqModC ↥A) hjq₀mem
  obtain ⟨hC, hρ⟩ := hjN _ h₀
  have hρj : R.residue ⟨(j₁ : ↥(fieldBar q M')), hj₁O⟩ = jN (R₀.residue ⟨_, h₀⟩) := by
    rw [← hρ]
    congr 1
    apply Subtype.ext
    show (j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle ⟨coeffMap A.subtype (jqModC ↥A), hjq₀mem⟩
    rw [hj₁]
    congr 1
    exact Subtype.ext hjqA.symm
  have hjNκ : ∀ c : ResidueField ↥A, jN (algebraMap (ResidueField ↥A) _ c) = algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    have hmem : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ) ∈ R₀.integers :=
      (R₀.algebraMap_mem_iff _).mpr a.2
    obtain ⟨hC', h'⟩ := hjN _ hmem
    rw [← R₀.residue_algebraMap a, ← h', ← R.residue_algebraMap a]
    congr 1
  have noConst : ∀ c : ResidueField ↥A, jN (R₀.residue ⟨_, h₀⟩) ≠ algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) c := by
    intro c h
    rw [← hjNκ] at h
    have h2 := jN.injective h
    have h3 := congrArg (fun z : ↥(modularFunctionFieldC (ResidueField ↥A) M') => (z : LaurentSeries (ResidueField ↥A)).coeff (-1 : ℤ)) h2
    try simp only at h3
    rw [hres₀, hjκ, hcoeffκ, show ((algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') c :
        ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) =
        algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c from rfl,
      algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by norm_num)] at h3
    exact one_ne_zero h3

  have maxFin : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ (type_of% j₁) j₁),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ (type_of% j₁) j₁).base y = x → y.asIdeal.IsMaximal := by
    intro y hy
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
    let y₂ : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ (type_of% j₁) j₁) := ⟨M, hM.isPrime⟩
    have hsp : (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ (type_of% j₁) j₁).base y ⤳
        (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ (type_of% j₁) j₁).base y₂ :=
      ((PrimeSpectrum.le_iff_specializes y y₂).mp hle).map (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ (type_of% j₁) j₁).continuous
    rw [hy] at hsp
    have h2 := hcl _ hsp
    rw [← hy] at h2
    have hyy : y₂ = y := (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ (type_of% j₁) j₁).isOpenEmbedding.injective h2
    have hM' : M = y.asIdeal := congrArg PrimeSpectrum.asIdeal hyy
    rw [← hM']; exact hM
  have maxInf : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ (type_of% j₁) j₁),
      (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ (type_of% j₁) j₁).base y = x → y.asIdeal.IsMaximal := by
    intro y hy
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
    let y₂ : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ (type_of% j₁) j₁) := ⟨M, hM.isPrime⟩
    have hsp : (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ (type_of% j₁) j₁).base y ⤳
        (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ (type_of% j₁) j₁).base y₂ :=
      ((PrimeSpectrum.le_iff_specializes y y₂).mp hle).map (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ (type_of% j₁) j₁).continuous
    rw [hy] at hsp
    have h2 := hcl _ hsp
    rw [← hy] at h2
    have hyy : y₂ = y := (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ (type_of% j₁) j₁).isOpenEmbedding.injective h2
    have hM' : M = y.asIdeal := congrArg PrimeSpectrum.asIdeal hyy
    rw [← hM']; exact hM
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  ·
    by_contra Hc
    push_neg at Hc
    have hBO : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ (type_of% j₁) j₁), ι (b : (type_of% j₁)) ∈ R.integers :=
      fun b => chartSubO j₁ hj₁O b b.2
    haveI := maxFin y hy
    have halg := isAlgebraic_of_forall_mem_residue_eq_zero (κ := ResidueField ↥A)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ (type_of% j₁) j₁) j₁ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ (type_of% j₁) j₁).2
      (fun b => b.2) ι R.integers hAO hj₁O hj₁O' hj₁0 R.residue R.ker_residue c₀ hconstE y.asIdeal (hbrF y hy) hBO
      (fun b hb => Hc b (hBO b) hb)
    obtain ⟨c, hc⟩ := ModularCurve.mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC (ResidueField ↥A)
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) _ halg
    exact noConst c (hρj.symm.trans hc.symm)
  ·
    by_contra Hc
    push_neg at Hc
    have hιinv : ι j₁⁻¹ = (ι j₁)⁻¹ := map_inv₀ ι j₁
    have htO : ι j₁⁻¹ ∈ R.integers := by rw [hιinv]; exact hj₁O'
    have htO' : (ι j₁⁻¹)⁻¹ ∈ R.integers := by rw [hιinv, inv_inv]; exact hj₁O
    have ht0 : ι j₁⁻¹ ≠ 0 := by rw [hιinv]; exact inv_ne_zero hj₁0
    have hBO : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ (type_of% j₁) j₁), ι (b : (type_of% j₁)) ∈ R.integers :=
      fun b => chartSubO j₁⁻¹ htO b b.2
    haveI := maxInf y hy
    have halg' := isAlgebraic_of_forall_mem_residue_eq_zero (κ := ResidueField ↥A)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ (type_of% j₁) j₁) j₁⁻¹ (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf ↥A₁ (type_of% j₁) j₁).2
      (fun b => b.2) ι R.integers hAO htO htO' ht0 R.residue R.ker_residue c₀ hconstE y.asIdeal (hbrI y hy) hBO
      (fun b hb => Hc b (hBO b) hb)
    have hinvres : R.residue ⟨ι j₁⁻¹, htO⟩ = (R.residue ⟨(j₁ : ↥(fieldBar q M')), hj₁O⟩)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul]
      have : (⟨ι j₁⁻¹, htO⟩ * ⟨(j₁ : ↥(fieldBar q M')), hj₁O⟩ : ↥R.integers) = 1 :=
        Subtype.ext (by rw [MulMemClass.coe_mul, OneMemClass.coe_one]; show ι j₁⁻¹ * (j₁ : ↥(fieldBar q M')) = 1; rw [hιinv, hι]; exact inv_mul_cancel₀ hj₁0)
      rw [this, map_one]
    have halg : IsAlgebraic (ResidueField ↥A) (R.residue ⟨(j₁ : ↥(fieldBar q M')), hj₁O⟩) := by
      have h := halg'.inv
      rw [hinvres, inv_inv] at h
      exact h
    obtain ⟨c, hc⟩ := ModularCurve.mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC (ResidueField ↥A)
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) _ halg
    exact noConst c (hρj.symm.trans hc.symm)

end S_ModularCurve_FullLevel_exists_mem_asIdeal_and_residue_ne_zero_of_goodPt_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_mem_asIdeal_and_residue_ne_zero_of_goodPt_twoChartIntegralModel (solution)
