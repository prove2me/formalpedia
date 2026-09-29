-- Prove2me | solution 1 for ModularCurve.finiteIndex_closure_range_sections_addSubgroupOf_fixedPoints_of_compMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2a292810-c0b3-524e-ada2-d02553b85b43

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_forall_algEquiv_comp_eq
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_and_comp_eq_of_valuationSubring_comap
import Theorems.Thm_NeronModelInfra_existsUnique_extension_of_exists_isLocalization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteIndex_closure_range_sections_addSubgroupOf_fixedPoints_of_compMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

namespace L3V

theorem hfix_rat (x : AlgebraicClosure ℚ)
    (h : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ x = x) :
    ∃ a : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) a = x := by
  have hx : x ∈ IntermediateField.fixedField
      (⊤ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := fun σ => h σ
  rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hx
  exact hx

theorem specMap_rat_ext {O : Type} [CommRing O] [Algebra ℤ O] (M : Submonoid ℤ) [IsLocalization M O]
    (f₁ f₂ : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of O)) : f₁ = f₂ := by
  obtain ⟨r₁, rfl⟩ := Spec.map_surjective f₁
  obtain ⟨r₂, rfl⟩ := Spec.map_surjective f₂
  congr 1
  ext1
  exact IsLocalization.ringHom_ext M (RingHom.ext_int _ _)

theorem specMap_rat_ext_away (p : ℤ)
    (f₁ f₂ : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of (Localization.Away p))) : f₁ = f₂ :=
  specMap_rat_ext (Submonoid.powers p) f₁ f₂

theorem specMap_int_eq {O : Type} [CommRing O] [Algebra ℤ O]
    (f : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of ℤ)) :
    f = Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) := by
  obtain ⟨r, rfl⟩ := Spec.map_surjective f
  congr 1
  ext1
  exact RingHom.ext_int _ _

theorem isLocalization_atPrime_comap (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    IsLocalization.AtPrime (↥(A.comap (algebraMap ℚ (AlgebraicClosure ℚ)))) (Ideal.span {(p : ℤ)}) := by
  classical
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpirr : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.mp Fact.out).irreducible

  have vp : A.valuation (p : AlgebraicClosure ℚ) < 1 := by
    have h := (ValuationSubring.mem_nonunits_iff A).mp hA
    simpa using h
  have vint : ∀ n : ℤ, A.valuation (n : AlgebraicClosure ℚ) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A n)

  have hcop : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → A.valuation (n : AlgebraicClosure ℚ) = 1 := by
    intro n hn
    rcases (vint n).lt_or_eq with hlt | heq
    · exfalso
      obtain ⟨a, b, hab⟩ := (hpirr.coprime_iff_not_dvd).mpr hn
      have h1 : (1 : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ) * p + (b : AlgebraicClosure ℚ) * n := by
        exact_mod_cast hab.symm
      have hlt1 : A.valuation (1 : AlgebraicClosure ℚ) < 1 := by
        rw [h1]
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [Valuation.map_mul]
          calc A.valuation (a : AlgebraicClosure ℚ) * A.valuation (p : AlgebraicClosure ℚ)
              ≤ 1 * A.valuation (p : AlgebraicClosure ℚ) := by gcongr; exact vint a
            _ = _ := one_mul _
            _ < 1 := vp
        · rw [Valuation.map_mul]
          calc A.valuation (b : AlgebraicClosure ℚ) * A.valuation (n : AlgebraicClosure ℚ)
              ≤ 1 * A.valuation (n : AlgebraicClosure ℚ) := by gcongr; exact vint b
            _ = _ := one_mul _
            _ < 1 := hlt
      simp at hlt1
    · exact heq

  have hdvd : ∀ n : ℤ, (p : ℤ) ∣ n → A.valuation (n : AlgebraicClosure ℚ) < 1 := by
    rintro n ⟨k, rfl⟩
    push_cast
    rw [Valuation.map_mul]
    calc A.valuation (p : AlgebraicClosure ℚ) * A.valuation (k : AlgebraicClosure ℚ)
        ≤ A.valuation (p : AlgebraicClosure ℚ) * 1 := by gcongr; exact vint k
      _ = _ := mul_one _
      _ < 1 := vp
  have hιz : ∀ n : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (n : ℚ) = (n : AlgebraicClosure ℚ) := fun n => by simp

  have hinv : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → ((n : ℚ)⁻¹) ∈ A.comap (algebraMap ℚ (AlgebraicClosure ℚ)) := by
    intro n hn
    rw [ValuationSubring.mem_comap, ← A.valuation_le_one_iff, map_inv₀, hιz, map_inv₀, hcop n hn, inv_one]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro y
    have hy : ¬ (p : ℤ) ∣ (y : ℤ) := fun h => y.2 (Ideal.mem_span_singleton.mpr h)
    have hy0 : ((y : ℤ) : ℚ) ≠ 0 := by
      intro h; apply hy; rw [show (y : ℤ) = 0 by exact_mod_cast h]; exact dvd_zero _
    refine IsUnit.of_mul_eq_one ⟨((y : ℤ) : ℚ)⁻¹, hinv y hy⟩ ?_
    apply Subtype.ext
    simp [hy0]
  ·
    intro z
    set q : ℚ := (z : ℚ) with hq
    have hden : ¬ (p : ℤ) ∣ (q.den : ℤ) := by
      intro hpd

      have hnum : ¬ (p : ℤ) ∣ q.num := by
        intro hpn
        have h1 : (p : ℕ) ∣ q.num.natAbs := by
          rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]; exact hpn
        have h2 : (p : ℕ) ∣ q.den := by exact_mod_cast hpd
        have := Nat.dvd_gcd h1 h2
        rw [q.reduced] at this
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
      have hzA : A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) q) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (ValuationSubring.mem_comap.mp z.2)
      have hmul : algebraMap ℚ (AlgebraicClosure ℚ) q * (q.den : ℤ) = (q.num : AlgebraicClosure ℚ) := by
        rw [← hιz, ← hιz, ← map_mul]; congr 1; push_cast; exact q.mul_den_eq_num
      have h := hcop q.num hnum
      rw [← hmul, Valuation.map_mul] at h
      have hlt : A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) q) * A.valuation ((q.den : ℤ) : AlgebraicClosure ℚ) < 1 :=
        calc A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) q) * A.valuation ((q.den : ℤ) : AlgebraicClosure ℚ)
            ≤ 1 * A.valuation ((q.den : ℤ) : AlgebraicClosure ℚ) := by gcongr
          _ = _ := one_mul _
          _ < 1 := hdvd _ hpd
      rw [h] at hlt
      exact lt_irrefl _ hlt
    refine ⟨⟨q.num, ⟨(q.den : ℤ), fun h => hden (Ideal.mem_span_singleton.mp h)⟩⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    push_cast
    rw [← hq]
    exact q.mul_den_eq_num
  ·
    intro x y hxy
    refine ⟨1, ?_⟩
    have h : ((x : ℚ)) = (y : ℚ) := by
      have := congrArg (fun w : ↥(A.comap (algebraMap ℚ (AlgebraicClosure ℚ))) => (w : ℚ)) hxy
      simpa using this
    have : x = y := by exact_mod_cast h
    rw [this]

theorem exists_localPoint_of_not_mem (p : ℕ) [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [IsSeparated g] [LocallyOfFiniteType g]
    (proper_away : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))))
    (y : Spec (CommRingCat.of ℚ) ⟶ G) (hy : y ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
    (𝔪 : Ideal ℤ) [𝔪.IsMaximal] (hp : (p : ℤ) ∉ 𝔪) :
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℤ O) (_ : IsLocalization.AtPrime O 𝔪)
      (_ : Algebra O ℚ) (_ : @IsScalarTower ℤ O ℚ Algebra.toSMul Algebra.toSMul Algebra.toSMul)
      (σ : Spec (CommRingCat.of O) ⟶ G),
      σ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap O ℚ)) ≫ σ = y := by
  classical

  let O := Localization.AtPrime 𝔪
  have hunit : ∀ z : 𝔪.primeCompl, IsUnit (algebraMap ℤ ℚ z) := by
    intro z
    apply IsUnit.mk0
    have hz : (z : ℤ) ≠ 0 := by
      intro h; apply z.2; show (z : ℤ) ∈ 𝔪; rw [h]; exact 𝔪.zero_mem
    rw [eq_intCast]
    exact_mod_cast hz
  letI algOQ : Algebra O ℚ := (IsLocalization.lift (M := 𝔪.primeCompl) (S := O) hunit).toAlgebra
  haveI hst : @IsScalarTower ℤ O ℚ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun n => (IsLocalization.lift_eq (M := 𝔪.primeCompl) (S := O) hunit n).symm
  haveI : IsFractionRing O ℚ :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔪.primeCompl O ℚ

  have hpO : IsUnit (algebraMap ℤ O (p : ℤ)) := IsLocalization.map_units (M := 𝔪.primeCompl) O ⟨(p : ℤ), hp⟩
  let jp : Localization.Away (p : ℤ) →+* O := IsLocalization.Away.lift (p : ℤ) hpO
  have hpQ : IsUnit (algebraMap ℤ ℚ (p : ℤ)) := by
    apply IsUnit.mk0; rw [eq_intCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  let jq : Localization.Away (p : ℤ) →+* ℚ := IsLocalization.Away.lift (p : ℤ) hpQ

  let f' := pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))
  haveI : IsProper f' := proper_away
  have hE : ValuativeCriterion.Existence f' := by
    have h : UniversallyClosed f' := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let i₁ : Spec (CommRingCat.of ℚ) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))) :=
    pullback.lift y (Spec.map (CommRingCat.ofHom jq)) (by
      rw [hy, ← Spec.map_comp]; congr 1; ext1; exact RingHom.ext_int _ _)
  let i₂ : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of (Localization.Away (p : ℤ))) :=
    Spec.map (CommRingCat.ofHom jp)
  have hsq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap O ℚ))) f' i₂ :=
    ⟨specMap_rat_ext_away (p : ℤ) _ _⟩
  let Sq : ValuativeCommSq f' := ValuativeCommSq.mk O ℚ i₁ i₂ hsq
  haveI : Sq.commSq.HasLift := hE Sq
  refine ⟨O, inferInstance, inferInstance, inferInstance, algOQ, hst,
    Sq.commSq.lift ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))),
    specMap_int_eq _, ?_⟩
  rw [← Category.assoc]
  erw [Sq.commSq.fac_left]
  exact pullback.lift_fst _ _ _

theorem localDatum (p : ℕ) {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ))
    (y : Spec (CommRingCat.of ℚ) ⟶ G) (hy : y ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
    (𝔪 : Ideal ℤ) [𝔪.IsMaximal]
    (O : Type) [CommRing O] [Algebra ℤ O] [IsLocalization.AtPrime O 𝔪] [Algebra O ℚ]
    (σ : Spec (CommRingCat.of O) ⟶ G)
    (hσg : σ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
    (hσy : Spec.map (CommRingCat.ofHom (algebraMap O ℚ)) ≫ σ = y)
    (v : NeronModelInfra.SchemeHomOver (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ))) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ))
      (pullback.snd g (NeronModelInfra.specGenericFibreInclusion ℤ ℚ)))
    (hv : v.1 ≫ pullback.fst g (NeronModelInfra.specGenericFibreInclusion ℤ ℚ)
      = pullback.snd (𝟙 (Spec (CommRingCat.of ℤ))) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) ≫ y) :
    ∃ (gA : pullback (𝟙 (Spec (CommRingCat.of ℤ))) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⟶ G),
      gA ≫ g = pullback.fst (𝟙 (Spec (CommRingCat.of ℤ))) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ≫ 𝟙 _ ∧
      ∀ j : pullback (𝟙 (Spec (CommRingCat.of ℤ))) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) ⟶
          pullback (𝟙 (Spec (CommRingCat.of ℤ))) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        j ≫ pullback.fst (𝟙 (Spec (CommRingCat.of ℤ))) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          pullback.fst (𝟙 (Spec (CommRingCat.of ℤ))) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) →
        j ≫ gA = v.1 ≫ pullback.fst g (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) := by
  refine ⟨pullback.snd (𝟙 (Spec (CommRingCat.of ℤ))) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ≫ σ, ?_, ?_⟩
  · rw [Category.assoc, hσg, Category.comp_id]
    exact pullback.condition.symm
  · intro j _

    have key : ∀ f₁ f₂ : pullback (𝟙 (Spec (CommRingCat.of ℤ))) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) ⟶
        Spec (CommRingCat.of O), f₁ = f₂ := by
      intro f₁ f₂
      rw [← cancel_epi (inv (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ)))
        (NeronModelInfra.specGenericFibreInclusion ℤ ℚ)))]
      exact specMap_rat_ext 𝔪.primeCompl _ _
    rw [← Category.assoc, key (j ≫ pullback.snd _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap O ℚ))),
      Category.assoc, hσy, hv]

end L3V

theorem solution
    (p : ℕ) [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) g)
    (pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
      (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    [IsSeparated g] [LocallyOfFiniteType g]
    (proper_away : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Φ : Type) [AddCommGroup Φ] [Finite Φ]
    (comp : ↥(inertiaInvariants A p) →+ Φ)
    (hR1 : ∀ x : ↥(inertiaInvariants A p),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • (x : JZero p) = x) → comp x = 0 →
        ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g,
          (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1) :
    ((AddSubgroup.closure (Set.range fun s : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) g =>
        pts.symm (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
          (Category.comp_id _) s))).addSubgroupOf
      (FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p))).FiniteIndex := by
  classical

  set ι : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ) with hι
  have hZQb : Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))
      = Spec.map (CommRingCat.ofHom ι) ≫ NeronModelInfra.specGenericFibreInclusion ℤ ℚ := by
    have h : CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))
        = CommRingCat.ofHom (algebraMap ℤ ℚ) ≫ CommRingCat.ofHom ι := by
      ext1; exact RingHom.ext_int _ _
    rw [NeronModelInfra.specGenericFibreInclusion_eq, h, Spec.map_comp]
  let JQ := FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p)

  have hle : JQ ≤ inertiaInvariants A p := by
    intro x hx
    rw [mem_inertiaInvariants]
    exact fun σ _ => hx σ

  let S : AddSubgroup (JZero p) := AddSubgroup.closure (Set.range fun s : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) g =>
        pts.symm (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
          (Category.comp_id _) s))
  show (S.addSubgroupOf JQ).FiniteIndex

  let ψ : ↥JQ →+ Φ := comp.comp (AddSubgroup.inclusion hle)

  have hker : ψ.ker ≤ S.addSubgroupOf JQ := by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf]
    have hxfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • (x : JZero p) = x := x.2
    have hcomp : comp (AddSubgroup.inclusion hle x) = 0 := hx

    have hinv : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1 = (pts x).1 := by
      intro σ
      rw [← pts_galois σ x, hxfix σ]
    obtain ⟨y, hy⟩ := AlgebraicGeometry.exists_comp_eq_of_forall_algEquiv_comp_eq L3V.hfix_rat (pts (x : JZero p)).1 hinv
    have hyg : y ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) := L3V.specMap_int_eq (y ≫ g)

    obtain ⟨sA, hsA⟩ := hR1 (AddSubgroup.inclusion hle x) hxfix hcomp
    obtain ⟨s₀, hs₀, -⟩ := AlgebraicGeometry.exists_comp_eq_and_comp_eq_of_valuationSubring_comap ι A y sA.1
      (by rw [← hsA, hy]; rfl)

    let v : NeronModelInfra.SchemeHomOver (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ))) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ)) (pullback.snd g (NeronModelInfra.specGenericFibreInclusion ℤ ℚ)) :=
      ⟨pullback.lift (pullback.snd (𝟙 _) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) ≫ y)
          (pullback.snd (𝟙 _) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ)) (by rw [Category.assoc, hyg]; rfl),
        pullback.lift_snd _ _ _⟩
    have hv : v.1 ≫ pullback.fst g (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) = pullback.snd (𝟙 _) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) ≫ y := pullback.lift_fst _ _ _

    have h31 := NeronModelInfra.existsUnique_extension_of_exists_isLocalization_atPrime ℚ g
      (𝟙 (Spec (CommRingCat.of ℤ))) v (by
        intro 𝔪 h𝔪
        by_cases hp : (p : ℤ) ∈ 𝔪
        ·
          have hprime : (Ideal.span {(p : ℤ)}).IsPrime :=
            (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
              (Nat.prime_iff_prime_int.mp Fact.out)
          have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hprime.isMaximal (by
            rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (Fact.out : p.Prime).ne_zero)
          have h𝔪p : Ideal.span {(p : ℤ)} = 𝔪 :=
            hmax.eq_of_le h𝔪.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hp)
          subst h𝔪p
          haveI := L3V.isLocalization_atPrime_comap p A hA
          obtain ⟨gA, hgA⟩ := L3V.localDatum p g y hyg (Ideal.span {(p : ℤ)})
            (↥(A.comap ι)) s₀ (L3V.specMap_int_eq _) hs₀ v hv
          exact ⟨↥(A.comap ι), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, gA, hgA⟩
        · obtain ⟨O, i1, i2, i3, i4, i5, σ, hσg, hσy⟩ :=
            L3V.exists_localPoint_of_not_mem p g proper_away y hyg 𝔪 hp
          obtain ⟨gA, hgA⟩ := L3V.localDatum p g y hyg 𝔪 O σ hσg hσy v hv
          exact ⟨O, i1, i2, i3, i4, i5, gA, hgA⟩)
    obtain ⟨φ, hφ, -⟩ := h31

    have h1 : pullback.fst (𝟙 _) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) ≫ φ.1 = pullback.snd (𝟙 _) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) ≫ y := by
      have h := congrArg (fun w : NeronModelInfra.SchemeHomOver (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ))) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ))
        (pullback.snd g (NeronModelInfra.specGenericFibreInclusion ℤ ℚ)) => w.1 ≫ pullback.fst g (NeronModelInfra.specGenericFibreInclusion ℤ ℚ)) hφ
      simp only [NeronModelInfra.genericFibreRestrict, pullback.lift_fst] at h
      rw [← hv, ← h]
    have h2 : (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) ≫ φ.1 = y := by
      have hc : pullback.fst (𝟙 (Spec (CommRingCat.of ℤ))) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) = pullback.snd (𝟙 _) (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) ≫ (NeronModelInfra.specGenericFibreInclusion ℤ ℚ) := by
        simpa using (pullback.condition (f := 𝟙 (Spec (CommRingCat.of ℤ))) (g := (NeronModelInfra.specGenericFibreInclusion ℤ ℚ)))
      rw [hc, Category.assoc] at h1
      exact (cancel_epi _).mp h1

    refine AddSubgroup.subset_closure ⟨φ, ?_⟩
    apply pts.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ φ.1 = (pts (x : JZero p)).1
    rw [← hy, ← h2, ← Category.assoc, ← hZQb]

  haveI : Finite (↥JQ ⧸ ψ.ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange ψ).symm.toEquiv
  haveI : ψ.ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact AddSubgroup.finiteIndex_of_le hker

end S_ModularCurve_finiteIndex_closure_range_sections_addSubgroupOf_fixedPoints_of_compMap
end P2MW
export P2MW.S_ModularCurve_finiteIndex_closure_range_sections_addSubgroupOf_fixedPoints_of_compMap (solution)
