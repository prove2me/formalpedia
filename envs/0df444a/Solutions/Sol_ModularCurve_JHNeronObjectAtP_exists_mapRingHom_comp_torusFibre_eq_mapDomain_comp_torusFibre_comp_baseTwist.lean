-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/596faf34-0c96-5451-b4bc-62a1b2190c28

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist.ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist.ModularCurve.JHNeronObjectAtP"

namespace ToricHeckeAlg

open AddMonoidAlgebra

variable {κ : Type*} [Field κ]

@[reducible] noncomputable def instCoeFunAddMonoidAlgebra {R M : Type*} [Semiring R] :
    CoeFun (AddMonoidAlgebra R M) (fun _ => M → R) := ⟨fun a => ⇑a.coeff⟩
attribute [local instance] instCoeFunAddMonoidAlgebra

def HasEnoughChars (κ : Type*) [Field κ] (G : Type*) [AddCommGroup G] : Prop :=
  ∀ u : G, u ≠ 0 → ∃ F : Multiplicative G →* κ, F (Multiplicative.ofAdd u) ≠ 1

section separation

variable {G : Type*} [AddCommGroup G]

def evHom (κ : Type*) [Field κ] (u : G) : (Multiplicative G →* κ) →* κ where
  toFun F := F (Multiplicative.ofAdd u)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem evHom_injective (h : HasEnoughChars κ G) : Function.Injective (evHom κ : G → _) := by
  intro u u' huu'
  by_contra hne
  obtain ⟨F, hF⟩ := h (u - u') (sub_ne_zero.mpr hne)
  apply hF
  have := congrArg (fun φ : (Multiplicative G →* κ) →* κ ↦ φ F) huu'
  simp only [evHom, MonoidHom.coe_mk, OneHom.coe_mk] at this
  rw [ofAdd_sub, div_eq_mul_inv, map_mul, map_inv, this, mul_inv_cancel₀]

  exact (F.toHomUnits (Multiplicative.ofAdd u')).ne_zero

theorem eq_zero_of_forall_lift_eq_zero (h : HasEnoughChars κ G) (d : AddMonoidAlgebra κ G)
    (hd : ∀ F : Multiplicative G →* κ, AddMonoidAlgebra.lift κ κ G F d = 0) : d = 0 := by
  classical
  have hli : LinearIndependent κ (fun u : G ↦ ((evHom κ u : (Multiplicative G →* κ) →* κ) :
      (Multiplicative G →* κ) → κ)) :=
    (linearIndependent_monoidHom (Multiplicative G →* κ) κ).comp (evHom κ) (evHom_injective h)
  suffices h0 : d.coeff = 0 from
    AddMonoidAlgebra.coeff_injective (h0.trans AddMonoidAlgebra.coeff_zero.symm)
  refine linearIndependent_iff.mp hli d.coeff ?_
  funext F
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.zero_apply]
  have := hd F
  rw [AddMonoidAlgebra.lift_apply, Finsupp.sum] at this
  simpa [evHom, smul_eq_mul, mul_comm] using this

end separation

section enough

theorem hasEnoughChars_prod {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (hG : HasEnoughChars κ G) (hH : HasEnoughChars κ H) : HasEnoughChars κ (G × H) := by
  rintro ⟨u, w⟩ huw
  by_cases hu : u = 0
  · subst hu
    have hw : w ≠ 0 := fun h ↦ huw (by rw [h]; rfl)
    obtain ⟨F, hF⟩ := hH w hw
    exact ⟨F.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd G H)), hF⟩
  · obtain ⟨F, hF⟩ := hG u hu
    exact ⟨F.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst G H)), hF⟩

noncomputable def coordChar {t : ℕ} (ζ : κ) (hζ : ζ ≠ 0) (i : Fin t) : Multiplicative (Fin t → ℤ) →* κ where
  toFun v := ζ ^ (Multiplicative.toAdd v i)
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, Pi.add_apply, zpow_add₀ hζ]

theorem hasEnoughChars_pi_int [Infinite κ] (t : ℕ) : HasEnoughChars κ (Fin t → ℤ) := by
  classical
  intro u hu
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)

  set n : ℕ := (u i).natAbs with hn
  have hn0 : 0 < n := Int.natAbs_pos.mpr hi
  obtain ⟨ζ, hζ⟩ := Infinite.exists_notMem_finset
    ((Polynomial.X ^ n - Polynomial.C (1 : κ)).roots.toFinset ∪ {0})
  simp only [Finset.mem_union, Multiset.mem_toFinset, Finset.mem_singleton, not_or] at hζ
  obtain ⟨hζroot, hζ0⟩ := hζ
  have hζn : ζ ^ n ≠ 1 := by
    intro h1
    apply hζroot
    rw [Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hn0 1)]
    simp [h1]
  refine ⟨coordChar ζ hζ0 i, ?_⟩
  simp only [coordChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rcases Int.natAbs_eq (u i) with h | h
  · rw [h, ← hn, zpow_natCast]; exact hζn
  · rw [h, ← hn, zpow_neg, zpow_natCast, Ne, inv_eq_one]; exact hζn

end enough

section main

variable {G : Type*} [AddCommGroup G]

theorem lift_single_one {H : Type*} [AddCommGroup H] (F : Multiplicative H →* κ) (g : H) :
    AddMonoidAlgebra.lift κ κ H F (single g 1) = F (Multiplicative.ofAdd g) := by
  rw [AddMonoidAlgebra.lift_single, one_smul]

open TensorProduct in

theorem lift_finsuppTensorFinsupp' (Ψ : Multiplicative (G × G) →* κ) (a b : AddMonoidAlgebra κ G) :
    AddMonoidAlgebra.lift κ κ (G × G) Ψ
        (AddMonoidAlgebra.ofCoeff (finsuppTensorFinsupp' κ G G (a.coeff ⊗ₜ b.coeff))) =
      AddMonoidAlgebra.lift κ κ G (Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl G G))) a *
        AddMonoidAlgebra.lift κ κ G (Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr G G))) b := by

  let L : (G →₀ κ) →ₗ[κ] (G →₀ κ) →ₗ[κ] κ :=
    (TensorProduct.mk κ _ _).compr₂
      ((AddMonoidAlgebra.lift κ κ (G × G) Ψ).toLinearMap ∘ₗ
        (AddMonoidAlgebra.coeffLinearEquiv κ).symm.toLinearMap ∘ₗ (finsuppTensorFinsupp' κ G G).toLinearMap)
  let R' : (G →₀ κ) →ₗ[κ] (G →₀ κ) →ₗ[κ] κ :=
    (LinearMap.mul κ κ).compl₁₂
      ((AddMonoidAlgebra.lift κ κ G (Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl G G)))).toLinearMap ∘ₗ
        (AddMonoidAlgebra.coeffLinearEquiv κ).symm.toLinearMap)
      ((AddMonoidAlgebra.lift κ κ G (Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr G G)))).toLinearMap ∘ₗ
        (AddMonoidAlgebra.coeffLinearEquiv κ).symm.toLinearMap)
  suffices L = R' from congrArg (fun T : _ →ₗ[κ] _ →ₗ[κ] κ ↦ T a.coeff b.coeff) this
  refine Finsupp.lhom_ext' fun v ↦ LinearMap.ext_ring (Finsupp.lhom_ext' fun w ↦ LinearMap.ext_ring ?_)
  change AddMonoidAlgebra.lift κ κ (G × G) Ψ
      (AddMonoidAlgebra.ofCoeff (finsuppTensorFinsupp' κ G G (Finsupp.single v 1 ⊗ₜ Finsupp.single w 1))) =
    AddMonoidAlgebra.lift κ κ G (Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl G G))) (single v 1) *
      AddMonoidAlgebra.lift κ κ G (Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr G G))) (single w 1)
  rw [finsuppTensorFinsupp'_single_tmul_single, mul_one]
  erw [lift_single_one, lift_single_one, lift_single_one]
  rw [MonoidHom.coe_comp, MonoidHom.coe_comp, Function.comp_apply, Function.comp_apply,
    AddMonoidHom.toMultiplicative_apply_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, toAdd_ofAdd,
    AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, ← map_mul, ← ofAdd_add, Prod.mk_add_mk, add_zero, zero_add]

theorem exists_addMonoidHom_single_eq (hsep : HasEnoughChars κ (G × G))
    (E : AddMonoidAlgebra κ G →ₐ[κ] AddMonoidAlgebra κ G)
    (hE : ∀ (F F' : Multiplicative G →* κ) (g : G),
      AddMonoidAlgebra.lift κ κ G (F * F') (E (single g 1)) =
        AddMonoidAlgebra.lift κ κ G F (E (single g 1)) * AddMonoidAlgebra.lift κ κ G F' (E (single g 1))) :
    ∃ M : G →+ G, ∀ g : G, E (single g 1) = single (M g) 1 := by
  classical
  have key : ∀ g : G, ∃ v : G, E (single g 1) = single v 1 := by
    intro g
    set a : AddMonoidAlgebra κ G := E (single g 1) with ha
    let P : AddMonoidAlgebra κ (G × G) := AddMonoidAlgebra.mapDomain (fun v ↦ (v, v)) a
    let Q : AddMonoidAlgebra κ (G × G) :=
      AddMonoidAlgebra.ofCoeff (finsuppTensorFinsupp' κ G G (a.coeff ⊗ₜ[κ] a.coeff))
    have hPQ : P = Q := by
      refine sub_eq_zero.mp (eq_zero_of_forall_lift_eq_zero hsep _ fun Ψ ↦ ?_)
      let F : Multiplicative G →* κ := Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl G G))
      let F' : Multiplicative G →* κ := Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr G G))
      have h1 : AddMonoidAlgebra.lift κ κ (G × G) Ψ P = AddMonoidAlgebra.lift κ κ G (F * F') a := by
        simp only [P, AddMonoidAlgebra.lift_apply, AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff]
        rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_mul])]
        refine Finsupp.sum_congr fun v _ ↦ ?_
        congr 1
        simp only [F, F', MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
          AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, AddMonoidHom.inl_apply,
          AddMonoidHom.inr_apply, ← map_mul, ← ofAdd_add, Prod.mk_add_mk, add_zero, zero_add]
      rw [map_sub, h1, hE]
      exact sub_eq_zero.mpr (lift_finsuppTensorFinsupp' Ψ a a).symm

    have hcoeff : ∀ v w : G, (if v = w then a v else 0) = a v * a w := by
      intro v w
      have := congrArg (fun x : AddMonoidAlgebra κ (G × G) ↦ x (v, w)) hPQ
      simp only [P, Q, AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff,
        finsuppTensorFinsupp'_apply_apply] at this
      rw [← this]
      split_ifs with hvw
      · subst hvw
        exact (Finsupp.mapDomain_apply (fun x y h ↦ (Prod.mk.inj h).1) a.coeff v).symm
      · rw [Finsupp.mapDomain_notin_range]
        rintro ⟨x, hx⟩
        exact hvw ((Prod.mk.inj hx).1.symm.trans (Prod.mk.inj hx).2)

    have ha0 : a ≠ 0 := by
      have hu : IsUnit (single g (1 : κ) : AddMonoidAlgebra κ G) :=
        IsUnit.of_mul_eq_one (single (-g) 1) (by
          rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]; rfl)
      exact (hu.map E).ne_zero
    obtain ⟨v₀, hv₀⟩ : ∃ v, a v ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (AddMonoidAlgebra.coeff_injective (Finsupp.ext h))
    have hv₀1 : a v₀ = 1 := by
      have h := hcoeff v₀ v₀
      rw [if_pos rfl] at h
      exact (mul_left_cancel₀ hv₀ (h.symm.trans (mul_one _).symm))
    have hoth : ∀ w, w ≠ v₀ → a w = 0 := fun w hw ↦ by
      have h := hcoeff v₀ w
      rw [if_neg (Ne.symm hw)] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hv₀
    refine ⟨v₀, AddMonoidAlgebra.coeff_injective (Finsupp.ext fun w ↦ ?_)⟩
    by_cases hw : w = v₀
    · subst hw; rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]; exact hv₀1
    · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hw)]; exact hoth w hw
  choose M hM using key
  have hM_add : ∀ g h : G, M (g + h) = M g + M h := by
    intro g h
    have e1 : (single (g + h) (1 : κ) : AddMonoidAlgebra κ G) = single g 1 * single h 1 := by
      rw [AddMonoidAlgebra.single_mul_single, mul_one]
    have := hM (g + h)
    rw [e1, map_mul, hM g, hM h, AddMonoidAlgebra.single_mul_single, mul_one] at this
    exact (AddMonoidAlgebra.single_left_injective (one_ne_zero (α := κ)) this).symm
  exact ⟨AddMonoidHom.mk' M hM_add, hM⟩

end main

end ToricHeckeAlg

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "LevelData torusFibre abqFibre mk abqFibre_mul g mk.inj torusFibre_mul G toricRank torusFibre_isClosedImmersion abqFibre_eq_one_iff L"
namespace ToricHecke
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

section plumbing

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem eq_one_of_mul_self (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t f) (h : L.mul t z z = z) : z = L.one t := by
  letI := L.pointGroup t
  have h' : z * z = z * 1 := by rw [mul_one]; exact h
  exact mul_left_cancel h'

theorem comp_one_eq_one {Y : Scheme.{0}} {g : Y ⟶ Spec (CommRingCat.of R)}
    (LY : RelativeGroupLaw R g) (LX : RelativeGroupLaw R f) (φ : SchemeHomOver g f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (hφ : ∀ x y : SchemeHomOver t g, NeronModelInfra.schemeHomOverComp (LY.mul t x y) φ =
      LX.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) :
    NeronModelInfra.schemeHomOverComp (LY.one t) φ = LX.one t := by
  apply eq_one_of_mul_self
  rw [← hφ, LY.one_mul]

variable {R' : Type} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

theorem fibreRestrictAlong_mul {Y : Scheme.{0}} {g : Y ⟶ Spec (CommRingCat.of R)}
    (LY : RelativeGroupLaw R g) (LX : RelativeGroupLaw R f) (φ : SchemeHomOver g f)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (LY.mul s x y) φ =
        LX.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R'))
    (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι g)) :
    NeronModelInfra.schemeHomOverComp ((LY.baseChange ι).mul s x y) (fibreRestrictAlong ι f g φ) =
      (LX.baseChange ι).mul s (NeronModelInfra.schemeHomOverComp x (fibreRestrictAlong ι f g φ))
        (NeronModelInfra.schemeHomOverComp y (fibreRestrictAlong ι f g φ)) := by
  apply (RelativeGroupLaw.baseChangePointEquiv ι s).injective
  change RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_mul,
    hφ, RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]

end plumbing

section torus

variable (S : Type) [Field S] (t : ℕ)

theorem exists_torusPt_eq (u : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) (torusStr S t)) :
    ∃ χ : torusCoord S t →ₐ[S] S, torusPt S t χ = u := by
  let r : CommRingCat.of (torusCoord S t) ⟶ CommRingCat.of S := Spec.preimage u.1
  have hr : Spec.map r = u.1 := Spec.map_preimage _
  have hcomp : r.hom.comp (algebraMap S (torusCoord S t)) = RingHom.id S := by
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t)) ≫ r) = Spec.map (𝟙 _) := by
      rw [Spec.map_comp, hr, Spec.map_id]; exact u.2
    have := Spec.map_injective h2
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨{ r.hom with commutes' := fun c ↦ ?_ }, ?_⟩
  · exact congrFun (congrArg DFunLike.coe hcomp) c
  · apply Subtype.ext
    change Spec.map _ = u.1
    rw [← hr]
    rfl

theorem torusPt_injective : Function.Injective (torusPt S t) := by
  intro χ χ' h
  have h1 := congrArg Subtype.val h
  change Spec.map (CommRingCat.ofHom χ.toRingHom) = Spec.map (CommRingCat.ofHom χ'.toRingHom) at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  simp only [CommRingCat.hom_ofHom] at h2
  exact AlgHom.ext fun x ↦ congrFun (congrArg DFunLike.coe h2) x

theorem torusPt_comp_specMap (χ : torusCoord S t →ₐ[S] S) (E : torusCoord S t →ₐ[S] torusCoord S t)
    (hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ torusStr S t = torusStr S t) :
    NeronModelInfra.schemeHomOverComp (torusPt S t χ) (⟨Spec.map (CommRingCat.ofHom E.toRingHom), hE⟩ :
      SchemeHomOver (torusStr S t) (torusStr S t)) = torusPt S t (χ.comp E) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Spec.map (CommRingCat.ofHom E.toRingHom) =
    Spec.map (CommRingCat.ofHom (χ.comp E).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end torus

section core

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

theorem exists_comp_torusFibre_eq'
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hAκ : AbelianSchemePropertyBundle (ResidueField ↥A)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
    (x : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
    (hx1 : NeronModelInfra.schemeHomOverComp
        (torusPt (ResidueField ↥A) O.toricRank (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv) x =
      (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)) :
    ∃ y : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (torusStr (ResidueField ↥A) O.toricRank),
      NeronModelInfra.schemeHomOverComp y O.torusFibre = x := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A

  apply (O.abqFibre_eq_one_iff (torusStr (ResidueField ↥A) O.toricRank) x).mp
  intro i
  set ψ := NeronModelInfra.schemeHomOverComp x (O.abqFibre i) with hψ

  obtain ⟨a, ha, hψa⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
      hAκ O.toricRank ψ.1 ψ.2

  let u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (torusStr (ResidueField ↥A) O.toricRank) :=
    torusPt (ResidueField ↥A) O.toricRank (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv

  have hψu : NeronModelInfra.schemeHomOverComp u ψ = (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    have e1 : NeronModelInfra.schemeHomOverComp u ψ =
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp u x) (O.abqFibre i) := by
      apply Subtype.ext
      simp only [hψ, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    rw [e1, hx1, comp_one_eq_one (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (O.abqFibre i) (𝟙 _) (O.abqFibre_mul i (𝟙 _))]

  have ha1 : a = ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 := by
    have := congrArg Subtype.val hψu
    rw [NeronModelInfra.schemeHomOverComp_coe, hψa, ← Category.assoc, u.2, Category.id_comp] at this
    exact this

  apply Subtype.ext
  rw [hψa, ha1]
  have := congrArg Subtype.val
    ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one_natural (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank) (torusStr (ResidueField ↥A) O.toricRank) (Category.comp_id _))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this

end core

section conv

variable {S : Type} [Field S] {G : Type} [AddCommGroup G]

theorem convMul_ofConv_single (χ χ' : WithConv (AddMonoidAlgebra S G →ₐ[S] S)) (v : G) :
    (χ * χ').ofConv (AddMonoidAlgebra.single v 1) =
      χ.ofConv (AddMonoidAlgebra.single v 1) * χ'.ofConv (AddMonoidAlgebra.single v 1) := by
  change (χ * χ') (AddMonoidAlgebra.single v 1) = _
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem convMul_lift (F F' : Multiplicative G →* S) :
    (WithConv.toConv (AddMonoidAlgebra.lift S S G F) * WithConv.toConv (AddMonoidAlgebra.lift S S G F')).ofConv =
      AddMonoidAlgebra.lift S S G (F * F') := by
  refine AddMonoidAlgebra.algHom_ext (fun v ↦ ?_) (Subsingleton.elim _ _)
  rw [convMul_ofConv_single]
  change AddMonoidAlgebra.lift S S G F _ * AddMonoidAlgebra.lift S S G F' _ = _
  rw [ToricHeckeAlg.lift_single_one, ToricHeckeAlg.lift_single_one, ToricHeckeAlg.lift_single_one,
    MonoidHom.mul_apply]

end conv

section matrix

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

theorem exists_algHom_specMap_eq (S : Type) [Field S] (t : ℕ)
    (y : SchemeHomOver (torusStr S t) (torusStr S t)) :
    ∃ E : torusCoord S t →ₐ[S] torusCoord S t, Spec.map (CommRingCat.ofHom E.toRingHom) = y.1 := by
  let r : CommRingCat.of (torusCoord S t) ⟶ CommRingCat.of (torusCoord S t) := Spec.preimage y.1
  have hr : Spec.map r = y.1 := Spec.map_preimage _
  have hcomp : r.hom.comp (algebraMap S (torusCoord S t)) = algebraMap S (torusCoord S t) := by
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t)) ≫ r) =
        Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t))) := by
      rw [Spec.map_comp, hr]; exact y.2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  refine ⟨{ r.hom with commutes' := fun c ↦ ?_ }, ?_⟩
  · exact congrFun (congrArg DFunLike.coe hcomp) c
  · rw [← hr]; rfl

theorem exists_addMonoidHom_specMap_mapDomain_eq'
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (x : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
    (hxmul : ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
      NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank (χ * χ').ofConv) x =
        (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank χ.ofConv) x)
          (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank χ'.ofConv) x))
    (y : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (torusStr (ResidueField ↥A) O.toricRank))
    (hy : NeronModelInfra.schemeHomOverComp y O.torusFibre = x) :
    ∃ M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      y.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A

  obtain ⟨E, hE⟩ := exists_algHom_specMap_eq (ResidueField ↥A) O.toricRank y
  have hyE : y = ⟨Spec.map (CommRingCat.ofHom E.toRingHom), hE ▸ y.2⟩ := Subtype.ext hE.symm

  have hinj : Function.Injective fun χ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A ↦
      NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank χ) O.torusFibre := by
    intro χ χ' h
    apply torusPt_injective (ResidueField ↥A) O.toricRank
    apply Subtype.ext
    haveI := O.torusFibre_isClosedImmersion
    have h1 := congrArg Subtype.val h
    simp only [NeronModelInfra.schemeHomOverComp_coe] at h1
    exact (cancel_mono O.torusFibre.1).mp h1

  have hpts : ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
      (χ * χ').ofConv.comp E =
        (WithConv.toConv (χ.ofConv.comp E) * WithConv.toConv (χ'.ofConv.comp E)).ofConv := by
    intro χ χ'
    apply hinj
    change NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ((χ * χ').ofConv.comp E)) O.torusFibre =
      NeronModelInfra.schemeHomOverComp
        (torusPt (ResidueField ↥A) O.toricRank (WithConv.toConv (χ.ofConv.comp E) * WithConv.toConv (χ'.ofConv.comp E)).ofConv) O.torusFibre

    have hcompE : ∀ ξ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
        NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ξ) y = torusPt (ResidueField ↥A) O.toricRank (ξ.comp E) := by
      intro ξ
      rw [hyE]
      exact torusPt_comp_specMap (ResidueField ↥A) O.toricRank ξ E _
    rw [← hcompE, NeronModelInfra.schemeHomOverComp_assoc, hy, hxmul, ← hy, ← NeronModelInfra.schemeHomOverComp_assoc,
      ← NeronModelInfra.schemeHomOverComp_assoc, hcompE, hcompE,
      O.torusFibre_mul (WithConv.toConv (χ.ofConv.comp E)) (WithConv.toConv (χ'.ofConv.comp E))]

  have hE' : ∀ (F F' : Multiplicative (Fin O.toricRank → ℤ) →* ResidueField ↥A) (g : Fin O.toricRank → ℤ),
      AddMonoidAlgebra.lift (ResidueField ↥A) (ResidueField ↥A) _ (F * F') (E (AddMonoidAlgebra.single g 1)) =
        AddMonoidAlgebra.lift (ResidueField ↥A) (ResidueField ↥A) _ F (E (AddMonoidAlgebra.single g 1)) *
          AddMonoidAlgebra.lift (ResidueField ↥A) (ResidueField ↥A) _ F' (E (AddMonoidAlgebra.single g 1)) := by
    intro F F' g
    have h := congrArg (fun f : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A ↦ f (AddMonoidAlgebra.single g 1))
      (hpts (WithConv.toConv (AddMonoidAlgebra.lift (ResidueField ↥A) (ResidueField ↥A) _ F)) (WithConv.toConv (AddMonoidAlgebra.lift (ResidueField ↥A) (ResidueField ↥A) _ F')))
    simp only [AlgHom.comp_apply] at h
    rw [convMul_ofConv_single] at h
    change _ = (AddMonoidAlgebra.lift (ResidueField ↥A) (ResidueField ↥A) _ F).comp E (AddMonoidAlgebra.single g 1) *
      (AddMonoidAlgebra.lift (ResidueField ↥A) (ResidueField ↥A) _ F').comp E (AddMonoidAlgebra.single g 1) at h
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at h
    rw [← h, ← convMul_lift]
  haveI : Infinite (ResidueField ↥A) := IsAlgClosed.instInfinite
  obtain ⟨M₀, hM₀⟩ := ToricHeckeAlg.exists_addMonoidHom_single_eq
    (ToricHeckeAlg.hasEnoughChars_prod (ToricHeckeAlg.hasEnoughChars_pi_int O.toricRank)
      (ToricHeckeAlg.hasEnoughChars_pi_int O.toricRank)) E hE'
  refine ⟨M₀, ?_⟩
  rw [← hE]
  congr 2
  have hEM : E = AddMonoidAlgebra.mapDomainAlgHom (ResidueField ↥A) (ResidueField ↥A) M₀ :=
    AddMonoidAlgebra.algHom_ext (fun g ↦ by
      rw [hM₀]
      first
        | (rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single])
        | simp [AddMonoidAlgebra.mapDomain_single]) (Subsingleton.elim _ _)
  rw [hEM]
  rfl

end matrix

end ModularCurve.JHNeronObjectAtP.ToricHecke

namespace LATwist

open ModularCurve.JHNeronObjectAtP.ToricHecke

section chars

variable {κ : Type} [Field κ] {G : Type} [AddCommGroup G]

noncomputable def twistChar (ψ : κ ≃+* κ) (χ : AddMonoidAlgebra κ G →ₐ[κ] κ) : AddMonoidAlgebra κ G →ₐ[κ] κ :=
  AddMonoidAlgebra.lift κ κ G
    ((ψ.symm : κ ≃+* κ).toRingHom.toMonoidHom.comp ((χ : AddMonoidAlgebra κ G →+* κ).toMonoidHom.comp (AddMonoidAlgebra.of κ G)))

theorem twistChar_single (ψ : κ ≃+* κ) (χ : AddMonoidAlgebra κ G →ₐ[κ] κ) (v : G) :
    twistChar ψ χ (AddMonoidAlgebra.single v 1) = ψ.symm (χ (AddMonoidAlgebra.single v 1)) := by
  rw [twistChar, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem comp_mapRingHom_eq (ψ : κ ≃+* κ) (χ : AddMonoidAlgebra κ G →ₐ[κ] κ) :
    (χ : AddMonoidAlgebra κ G →+* κ).comp (AddMonoidAlgebra.mapRingHom G ψ.toRingHom) =
      ψ.toRingHom.comp (twistChar ψ χ : AddMonoidAlgebra κ G →+* κ) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single]
    have h1 : (AddMonoidAlgebra.single (0 : G) (ψ.toRingHom r) : AddMonoidAlgebra κ G) = algebraMap κ _ (ψ r) := rfl
    have h2 : (AddMonoidAlgebra.single (0 : G) r : AddMonoidAlgebra κ G) = algebraMap κ _ r := rfl
    rw [h1, h2]
    show χ (algebraMap κ _ (ψ r)) = ψ (twistChar ψ χ (algebraMap κ _ r))
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  · intro v
    rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single, map_one]
    show χ (AddMonoidAlgebra.single v 1) = ψ (twistChar ψ χ (AddMonoidAlgebra.single v 1))
    rw [twistChar_single]
    exact (ψ.apply_symm_apply _).symm

theorem twistChar_convMul (ψ : κ ≃+* κ) (χ χ' : WithConv (AddMonoidAlgebra κ G →ₐ[κ] κ)) :
    twistChar ψ (χ * χ').ofConv =
      (WithConv.toConv (twistChar ψ χ.ofConv) * WithConv.toConv (twistChar ψ χ'.ofConv)).ofConv := by
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  rw [twistChar_single, convMul_ofConv_single, convMul_ofConv_single, map_mul]
  change _ = twistChar ψ χ.ofConv (AddMonoidAlgebra.single v 1) * twistChar ψ χ'.ofConv (AddMonoidAlgebra.single v 1)
  rw [twistChar_single, twistChar_single]

end chars

section rat

theorem ringHom_baseRing_comp_eq (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] (ψ : κ ≃+* κ) (f : baseRing p →+* κ) :
    ψ.toRingHom.comp f = f := by
  haveI : IsLocalization.AtPrime (baseRing p) (Ideal.span {(p : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (Subsingleton.elim _ _)

end rat

section twist

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

theorem specMap_comp_resPt_σA (ψ : ResidueField ↥A ≃+* ResidueField ↥A) :
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ resPt A ≫ Λ.σA = resPt A ≫ Λ.σA := by
  set φ₀ := Spec.preimage (resPt A ≫ Λ.σA) with hφ₀
  have hφ : Spec.map φ₀ = resPt A ≫ Λ.σA := Spec.map_preimage _
  rw [← hφ, ← Spec.map_comp]
  congr 1
  ext1
  exact ringHom_baseRing_comp_eq p ψ φ₀.hom

theorem specMap_mapRingHom_comp_torusStr (ψ : ResidueField ↥A ≃+* ResidueField ↥A) (t : ℕ) :
    Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) ψ.toRingHom)) ≫ torusStr (ResidueField ↥A) t =
      torusStr (ResidueField ↥A) t ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro a
  show AddMonoidAlgebra.mapRingHom (Fin t → ℤ) ψ.toRingHom (algebraMap _ _ a) = algebraMap _ _ (ψ.toRingHom a)
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

end twist

end LATwist

open ModularCurve.JHNeronObjectAtP.ToricHecke LATwist in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ψ : ResidueField ↥A ≃+* ResidueField ↥A)

    (ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA))
    (hΞ₁ : ΞG ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞ₂ : ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom))
    :
    ∃ P₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) ψ.toRingHom)) ≫ O.torusFibre.1 =
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) P₀)) ≫ O.torusFibre.1 ≫ ΞG := by

  set κ := ResidueField ↥A with hκ
  set ι : Spec (CommRingCat.of κ) ⟶ base p := resPt A ≫ Λ.σA with hι
  haveI : IsAlgClosed κ := ValuationSubring.isAlgClosed_residueField A
  set tF := O.torusFibre with htF
  set Sψ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom ψ.toRingHom) with hSψ
  set Tψ := Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) ψ.toRingHom)) with hTψ
  have hSι : Sψ ≫ ι = ι := specMap_comp_resPt_σA ψ
  have hTstr : Tψ ≫ torusStr κ O.toricRank = torusStr κ O.toricRank ≫ Sψ := specMap_mapRingHom_comp_torusStr ψ O.toricRank

  let e₀ : SchemeHomOver (torusStr κ O.toricRank ≫ ι) O.g :=
    ⟨Tψ ≫ tF.1 ≫ pullback.fst O.g ι, by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc tF.1,
        show tF.1 ≫ pullback.snd O.g ι = torusStr κ O.toricRank from tF.2, ← Category.assoc, hTstr, Category.assoc, hSι]⟩
  let x : SchemeHomOver (torusStr κ O.toricRank) (RelativeGroupLaw.baseChangeStr ι O.g) :=
    RelativeGroupLaw.baseChangePointOfBase ι e₀
  have hx1 : x.1 ≫ pullback.fst O.g ι = Tψ ≫ tF.1 ≫ pullback.fst O.g ι := by
    rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]

  have hτ : Sψ ≫ 𝟙 _ ≫ ι = 𝟙 _ ≫ ι := by rw [Category.id_comp, hSι]
  have hpt : ∀ χ : torusCoord κ O.toricRank →ₐ[κ] κ,
      RelativeGroupLaw.baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp (torusPt κ O.toricRank χ) x) =
        GoodReductionJacobian.schemeHomOverComp Sψ hτ
          (RelativeGroupLaw.baseChangePointToBase ι
            (NeronModelInfra.schemeHomOverComp (torusPt κ O.toricRank (twistChar ψ χ)) tF)) := by
    intro χ
    apply Subtype.ext
    rw [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hx1,
      GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe,
      NeronModelInfra.schemeHomOverComp_coe]
    show Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Tψ ≫ tF.1 ≫ pullback.fst O.g ι =
      Sψ ≫ (Spec.map (CommRingCat.ofHom (twistChar ψ χ).toRingHom) ≫ tF.1) ≫ pullback.fst O.g ι
    simp only [← Category.assoc]
    congr 2
    rw [hTψ, hSψ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact comp_mapRingHom_eq ψ χ

  have hxmul : ∀ χ χ' : WithConv (torusCoord κ O.toricRank →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt κ O.toricRank (χ * χ').ofConv) x =
        (O.L.baseChange ι).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (torusPt κ O.toricRank χ.ofConv) x)
          (NeronModelInfra.schemeHomOverComp (torusPt κ O.toricRank χ'.ofConv) x) := by
    intro χ χ'
    apply (RelativeGroupLaw.baseChangePointEquiv ι (𝟙 (Spec (CommRingCat.of κ)))).injective
    show RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
    rw [hpt, twistChar_convMul, O.torusFibre_mul, RelativeGroupLaw.baseChangePointToBase_mul, O.L.mul_natural,
      RelativeGroupLaw.baseChangePointToBase_mul, hpt, hpt]

  have hx_one : NeronModelInfra.schemeHomOverComp
      (torusPt κ O.toricRank (1 : WithConv (torusCoord κ O.toricRank →ₐ[κ] κ)).ofConv) x = (O.L.baseChange ι).one (𝟙 _) := by
    apply eq_one_of_mul_self
    have h := hxmul 1 1
    rw [mul_one] at h
    exact h.symm
  obtain ⟨y, hy⟩ := exists_comp_torusFibre_eq' O
    (GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_of_field hΛ ι) x hx_one
  obtain ⟨M₀, hM₀⟩ := exists_addMonoidHom_specMap_mapDomain_eq' O x hxmul y hy
  refine ⟨M₀, ?_⟩

  have hyx : y.1 ≫ tF.1 ≫ pullback.fst O.g ι = Tψ ≫ tF.1 ≫ pullback.fst O.g ι := by
    rw [← hx1, ← hy, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Category.assoc, hΞ₁, ← hM₀]
    exact hyx.symm
  · rw [Category.assoc, Category.assoc, Category.assoc, hΞ₂, ← Category.assoc tF.1,
      show tF.1 ≫ pullback.snd O.g ι = torusStr κ O.toricRank from tF.2, hTstr, ← hM₀, ← Category.assoc, y.2]

end S_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist (solution)
