-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/020cda34-fa98-5df8-95a0-a64c86cd56ad

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_ModularCurve_FullLevel_exists_admissible_smallConstants_of_descentBase
import Theorems.Thm_ModularCurve_FullLevel_exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open IsLocalRing
namespace E150I

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem isUnit_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    IsUnit (e a) ↔ IsUnit a := MulEquiv.isUnit_map e.toMulEquiv

theorem mem_maximalIdeal_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (a : A) : e a ∈ maximalIdeal B ↔ a ∈ maximalIdeal A := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_of_ringEquiv]

theorem eval_map_symm {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (f : B[X]) (b : A) :
    e ((f.map e.symm.toRingHom).eval b) = f.eval (e b) := by
  rw [Polynomial.eval_map]
  change e.toRingHom (eval₂ e.symm.toRingHom b f) = _
  rw [Polynomial.hom_eval₂, RingEquiv.toRingHom_comp_symm_toRingHom, eval₂_eq_eval_map, Polynomial.map_id]
  rfl

theorem henselianLocalRing_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [HenselianLocalRing A] (e : A ≃+* B) : HenselianLocalRing B where
  is_henselian := by
    intro f hf a₀ h₁ h₂
    set g : A[X] := f.map e.symm.toRingHom with hg_def
    have hg : g.Monic := hf.map _
    have hb₀ : e (e.symm a₀) = a₀ := e.apply_symm_apply a₀
    have h₁' : g.eval (e.symm a₀) ∈ maximalIdeal A := by
      rw [← mem_maximalIdeal_iff_of_ringEquiv e, eval_map_symm, hb₀]; exact h₁
    have h₂' : IsUnit (g.derivative.eval (e.symm a₀)) := by
      rw [← isUnit_iff_of_ringEquiv e, hg_def, derivative_map, eval_map_symm, hb₀]; exact h₂
    obtain ⟨b, hb, hb'⟩ := HenselianLocalRing.is_henselian g hg (e.symm a₀) h₁' h₂'
    refine ⟨e b, ?_, ?_⟩
    · have := congrArg e hb.eq_zero
      rw [eval_map_symm, map_zero] at this
      exact this
    · have := (mem_maximalIdeal_iff_of_ringEquiv e _).mpr hb'
      rwa [map_sub, hb₀] at this

theorem isDiscreteValuationRing_of_ringEquiv {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing A] (e : A ≃+* B) : IsDiscreteValuationRing B := by
  haveI : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  haveI : IsLocalRing B := IsLocalRing.of_surjective' e.toRingHom e.surjective
  refine { not_a_field' := ?_ }
  intro h
  apply IsDiscreteValuationRing.not_a_field A
  rw [eq_bot_iff] at h ⊢
  intro a ha
  have := h ((mem_maximalIdeal_iff_of_ringEquiv e a).mpr ha)
  rw [Ideal.mem_bot] at this ⊢
  exact e.injective (this.trans (map_zero e).symm)

theorem maximalIdeal_eq_span_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (ϖ : A) (h : maximalIdeal A = Ideal.span {ϖ}) : maximalIdeal B = Ideal.span {e ϖ} := by
  apply le_antisymm
  · intro b hb
    have : e.symm b ∈ maximalIdeal A := by
      rw [← mem_maximalIdeal_iff_of_ringEquiv e, e.apply_symm_apply]; exact hb
    rw [h, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    rw [Ideal.mem_span_singleton]
    refine ⟨e c, ?_⟩
    rw [← map_mul, ← hc, e.apply_symm_apply]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (mem_maximalIdeal_iff_of_ringEquiv e ϖ).mpr (h ▸ Ideal.mem_span_singleton_self ϖ)

theorem exists_isPrimitiveRoot_of_isUnit_of_residueField
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    (n : ℕ) (hn : 0 < n) (hnA : IsUnit (n : A))
    (hk : ∃ ζ₀ : ResidueField A, IsPrimitiveRoot ζ₀ n) :
    ∃ ζ : A, IsPrimitiveRoot ζ n ∧ ∃ ζ₀ : ResidueField A, IsPrimitiveRoot ζ₀ n ∧ residue A ζ = ζ₀ := by
  obtain ⟨ζ₀, hζ₀⟩ := hk
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective ζ₀
  have ha₀' : residue A a₀ = ζ₀ := ha₀

  have hmonic : (X ^ n - 1 : A[X]).Monic := monic_X_pow_sub_C (1 : A) hn.ne'
  have heval : (X ^ n - 1 : A[X]).eval a₀ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff]
    simp only [eval_sub, eval_pow, eval_X, eval_one, map_sub, map_pow, map_one, ha₀', hζ₀.pow_eq_one, sub_self]
  have hderiv : IsUnit ((X ^ n - 1 : A[X]).derivative.eval a₀) := by
    have : (X ^ n - 1 : A[X]).derivative.eval a₀ = (n : A) * a₀ ^ (n - 1) := by
      simp [derivative_X_pow]
    rw [this]
    refine hnA.mul (IsUnit.pow _ ?_)
    rw [← residue_ne_zero_iff_isUnit, ha₀']
    exact hζ₀.ne_zero hn.ne'
  obtain ⟨ζ, hroot, hζa⟩ := HenselianLocalRing.is_henselian (X ^ n - 1) hmonic a₀ heval hderiv
  have hres : residue A ζ = ζ₀ := by
    rw [← ha₀', ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hζa
  have hpow : ζ ^ n = 1 := by
    have := hroot
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at this
    exact this
  refine ⟨ζ, IsPrimitiveRoot.mk_of_lt ζ hn hpow ?_, ζ₀, hζ₀, hres⟩
  intro l hl0 hln hl
  apply hζ₀.pow_ne_one_of_pos_of_lt hl0.ne' hln
  rw [← hres, ← map_pow, hl, map_one]

end E150I

namespace E150L

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

noncomputable def botComap (k₀ : IntermediateField F L) (A : ValuationSubring L) :
    ValuationSubring ↥(⊥ : IntermediateField ↥k₀ L) :=
  A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ L) L)

theorem mem_botComap (k₀ : IntermediateField F L) (A : ValuationSubring L) (x : ↥(⊥ : IntermediateField ↥k₀ L)) :
    x ∈ botComap k₀ A ↔ (x : L) ∈ A := ValuationSubring.mem_comap

def toBot (k₀ : IntermediateField F L) (c : ↥k₀) : ↥(⊥ : IntermediateField ↥k₀ L) :=
  ⟨(c : L), (IntermediateField.mem_bot).mpr ⟨c, rfl⟩⟩

@[scoped simp] theorem coe_toBot (k₀ : IntermediateField F L) (c : ↥k₀) : ((toBot k₀ c : ↥(⊥ : IntermediateField ↥k₀ L)) : L) = c := rfl

theorem toBot_surjective (k₀ : IntermediateField F L) : Function.Surjective (toBot k₀) := by
  intro x
  obtain ⟨c, hc⟩ := (IntermediateField.mem_bot).mp x.2
  exact ⟨c, Subtype.ext hc⟩

noncomputable def botComapEquiv (k₀ : IntermediateField F L) (A : ValuationSubring L) :
    ↥(A.comap (algebraMap ↥k₀ L)) ≃+* ↥(botComap k₀ A) :=
  RingEquiv.ofBijective
    ({ toFun := fun a => ⟨toBot k₀ (a : ↥k₀), (mem_botComap k₀ A _).mpr (by
          rw [coe_toBot]; exact (ValuationSubring.mem_comap.mp a.2))⟩
       map_one' := Subtype.ext (Subtype.ext (by simp))
       map_mul' := fun a b => Subtype.ext (Subtype.ext (by simp))
       map_zero' := Subtype.ext (Subtype.ext (by simp))
       map_add' := fun a b => Subtype.ext (Subtype.ext (by simp)) } : ↥(A.comap (algebraMap ↥k₀ L)) →+* ↥(botComap k₀ A))
    ⟨fun a b h => by
        have := congrArg (fun t : ↥(botComap k₀ A) => ((t : ↥(⊥ : IntermediateField ↥k₀ L)) : L)) h
        exact Subtype.ext (Subtype.ext (by simpa using this)),
      fun y => by
        obtain ⟨c, hc⟩ := toBot_surjective k₀ (y : ↥(⊥ : IntermediateField ↥k₀ L))
        refine ⟨⟨c, ValuationSubring.mem_comap.mpr ?_⟩, Subtype.ext hc⟩
        have := (mem_botComap k₀ A _).mp y.2
        rw [← hc, coe_toBot] at this
        exact this⟩

theorem coe_botComapEquiv (k₀ : IntermediateField F L) (A : ValuationSubring L) (a : ↥(A.comap (algebraMap ↥k₀ L))) :
    (((botComapEquiv k₀ A a : ↥(botComap k₀ A)) : ↥(⊥ : IntermediateField ↥k₀ L)) : L) = ((a : ↥k₀) : L) := rfl

end E150L
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase.E150L"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
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

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ)) :
    ∃ (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : AlgebraicClosure ℚ) ∈ A),
      (k₀ : Set (AlgebraicClosure ℚ)) = (K₀ : Set (AlgebraicClosure ℚ)) ∧ (π₀ : AlgebraicClosure ℚ) = π ∧

      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))} ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
      (∀ a : AlgebraicClosure ℚ, a ∈ A → ∃ c : ↥k₀, (c : AlgebraicClosure ℚ) ∈ A ∧
        ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧

      (∃ ℓ : ℕ, ℓ.Prime ∧ 3 ≤ ℓ ∧ ℓ ≠ q ∧ ¬ ℓ ∣ M' ∧
        ∃ ζ₀ : ↥k₀, IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ)) ∧
      (∃ u : ↥A, IsUnit u ∧ (π₀ : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ)) ∧

      (∃ e : A₀ ≃+* ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ∀ a : A₀,
        algebraMap ↥k₀ (AlgebraicClosure ℚ) ((e a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) = ((ι a : ↥A) : AlgebraicClosure ℚ)) ∧

      (∀ x : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), x ∈ (A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↔ (x : AlgebraicClosure ℚ) ∈ A) ∧
      FiniteDimensional ↥k₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ∧
      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ∧
      (∃ e₀ : A₀ ≃+* ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))),
        ∀ a : A₀, (((e₀ a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)))) : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))) : AlgebraicClosure ℚ) = ((ι a : ↥A) : AlgebraicClosure ℚ)) ∧

      (letI : Algebra ↥k₀ ↥(fieldBar q M') :=
        ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
       ∃ F₀' : IntermediateField ↥k₀ ↥(fieldBar q M'),
        (∀ f : ↥(fieldBar q M'), f ∈ F₀' ↔ ∀ n : ℤ, ∃ c : ↥k₀, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) ∧
        (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀' = ⊤) ∧
        (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀' → levelAutBar q M' ζ' γ f ∈ F₀') ∧
        (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
          ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀') →
            LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) ∧
        (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀') ∧
        (∀ f : ↥(fieldBar q M'), f ∈ F₀' ↔ f ∈ F₀) ∧
        ∃ Φ : ↥F₀ ≃+* ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'),
          ∀ f : ↥F₀, ((Φ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) = (f : ↥(fieldBar q M'))) := by
  classical
  obtain ⟨k₀, π₀, hπ₀, hk₀, hππ, hdvr, hunif, hhens, hres', hκ, ⟨ℓ, hℓ, hℓ3, hℓq, hℓM', ζ₀, hζ₀⟩, htame, ⟨e, he⟩⟩ :=
    ModularCurve.FullLevel.exists_admissible_smallConstants_of_descentBase q hq M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
  haveI := hdvr
  haveI := hhens
  have hqprime : q.Prime := Fact.out
  refine ⟨k₀, π₀, hπ₀, hk₀, hππ, hdvr, hunif, hhens, hres', hκ, ⟨ℓ, hℓ, hℓ3, hℓq, hℓM', ζ₀, hζ₀⟩, htame, ⟨e, he⟩,
    fun x => ValuationSubring.mem_comap, inferInstance,
    E150I.isDiscreteValuationRing_of_ringEquiv (E150L.botComapEquiv k₀ A),
    E150I.henselianLocalRing_of_ringEquiv (E150L.botComapEquiv k₀ A),
    ⟨e.trans (E150L.botComapEquiv k₀ A), fun a => (E150L.coe_botComapEquiv k₀ A (e a)).trans (he a)⟩, ?_⟩

  letI algk0 : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  have hζq : IsPrimitiveRoot (((ζ₀ ^ ℓ : ↥k₀)) : AlgebraicClosure ℚ) q := by
    rw [SubmonoidClass.coe_pow]
    exact hζ₀.pow (Nat.pos_of_ne_zero (Nat.mul_ne_zero hqprime.ne_zero hℓ.ne_zero)) (Nat.mul_comm q ℓ ▸ rfl)
  obtain ⟨F₀', hCHAR, hK1, hSTAB, hLD⟩ :=
    ModularCurve.FullLevel.exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint q hq M' hqM' k₀ (ζ₀ ^ ℓ) hζq
  have hcar : ∀ f : ↥(fieldBar q M'), f ∈ F₀' ↔ f ∈ F₀ := by
    intro f
    rw [hCHAR, hF₀]
    constructor
    · intro h n
      obtain ⟨c, hc⟩ := h n
      rw [hc]
      have : (c : AlgebraicClosure ℚ) ∈ (k₀ : Set (AlgebraicClosure ℚ)) := c.2
      rw [hk₀] at this
      exact this
    · intro h n
      have hn : ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ (k₀ : Set (AlgebraicClosure ℚ)) := by
        rw [hk₀]; exact h n
      exact ⟨⟨_, hn⟩, rfl⟩
  have hRAT : ∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀' := by
    rintro f ⟨x, hx⟩
    rw [hCHAR]
    intro n
    refine ⟨algebraMap ℚ ↥k₀ (x.coeff n), ?_⟩
    rw [← hx, coeffEmb_coeff]
    rfl
  have hle1 : IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ≤ F₀' := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (IntermediateField.mem_bot).mp hx
    rw [← hc]
    exact F₀'.algebraMap_mem c
  have hT1 : IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀' = F₀' := sup_eq_right.mpr hle1
  have hmem : ∀ f : ↥F₀, ((f : ↥F₀) : ↥(fieldBar q M')) ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀' := fun f => by
    rw [hT1]; exact (hcar _).mpr f.2
  let Φ₀ : ↥F₀ →+* ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') := (F₀.subtype).codRestrict (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') hmem
  have hΦbij : Function.Bijective Φ₀ := by
    constructor
    · intro a b h
      apply Subtype.ext
      have := congrArg Subtype.val h
      exact this
    · intro t
      have ht : (t : ↥(fieldBar q M')) ∈ F₀ := (hcar _).mp (hT1.le t.2)
      exact ⟨⟨t, ht⟩, Subtype.ext rfl⟩
  exact ⟨F₀', hCHAR, hK1, hSTAB, hLD, hRAT, hcar, RingEquiv.ofBijective Φ₀ hΦbij, fun f => rfl⟩

end S_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase (solution)
