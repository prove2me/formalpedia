-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3bd56248-86fa-5ce9-9639-2b0c384c66de

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong.ModularCurve IsLocalRing ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong.ModularCurve.JZeroNeronObjectAtP"

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
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "base resPt torusCoord torusStr torusPt LevelData abqFibre_eq_one_iff L torusFibre_isClosedImmersion G abqFibre_mul mk torusFibre abqFibre comp g mk.inj torusFibre_mul toricRank"
namespace ToricHecke
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

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

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}

theorem exists_comp_torusFibre_eq
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (hAκ : AbelianSchemePropertyBundle (ResidueField ↥A)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
    (φ : SchemeHomOver O.g O.g)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) :
    ∃ y : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (torusStr (ResidueField ↥A) O.toricRank),
      NeronModelInfra.schemeHomOverComp y O.torusFibre =
        NeronModelInfra.schemeHomOverComp O.torusFibre (fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g φ) := by

  set κ := ResidueField ↥A with hκ
  set ι : Spec (CommRingCat.of κ) ⟶ base p := resPt A ≫ Λ.σA with hι
  haveI : IsAlgClosed κ := ValuationSubring.isAlgClosed_residueField A
  set φκ := fibreRestrictAlong ι O.g O.g φ with hφκ
  set tF := O.torusFibre with htF

  have hφκ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of κ))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange ι).mul s x y) φκ =
        (O.L.baseChange ι).mul s (NeronModelInfra.schemeHomOverComp x φκ)
          (NeronModelInfra.schemeHomOverComp y φκ) :=
    fun s x y ↦ fibreRestrictAlong_mul ι O.L O.L φ hφ s x y

  apply (O.abqFibre_eq_one_iff (torusStr κ O.toricRank) (NeronModelInfra.schemeHomOverComp tF φκ)).mp
  intro i
  set ψ := NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp tF φκ) (O.abqFibre i) with hψ

  obtain ⟨a, ha, hψa⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
      hAκ O.toricRank ψ.1 ψ.2

  let u : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (torusStr κ O.toricRank) :=
    torusPt κ O.toricRank (1 : WithConv (torusCoord κ O.toricRank →ₐ[κ] κ)).ofConv
  have hu : NeronModelInfra.schemeHomOverComp u tF = (O.L.baseChange ι).one (𝟙 _) := by
    apply eq_one_of_mul_self
    have h := O.torusFibre_mul 1 1
    rw [mul_one] at h
    exact h.symm

  have hψu : NeronModelInfra.schemeHomOverComp u ψ = (Λ.L.baseChange ι).one (𝟙 _) := by
    have e1 : NeronModelInfra.schemeHomOverComp u ψ =
        NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp u tF) φκ) (O.abqFibre i) := by
      apply Subtype.ext
      simp only [hψ, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    rw [e1, hu, comp_one_eq_one (O.L.baseChange ι) (O.L.baseChange ι) φκ (𝟙 _) (hφκ (𝟙 _)),
      comp_one_eq_one (O.L.baseChange ι) (Λ.L.baseChange ι) (O.abqFibre i) (𝟙 _) (O.abqFibre_mul i (𝟙 _))]

  have ha1 : a = ((Λ.L.baseChange ι).one (𝟙 _)).1 := by
    have := congrArg Subtype.val hψu
    rw [NeronModelInfra.schemeHomOverComp_coe, hψa, ← Category.assoc, u.2, Category.id_comp] at this
    exact this

  apply Subtype.ext
  rw [hψa, ha1]
  have := congrArg Subtype.val
    ((Λ.L.baseChange ι).one_natural (𝟙 _) (torusStr κ O.toricRank) (torusStr κ O.toricRank) (Category.comp_id _))
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

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}

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

theorem exists_addMonoidHom_specMap_mapDomain_eq
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (φκ : SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
    (hφκ : ∀ (x y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _) x y) φκ =
        (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _) (NeronModelInfra.schemeHomOverComp x φκ)
          (NeronModelInfra.schemeHomOverComp y φκ))
    (y : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (torusStr (ResidueField ↥A) O.toricRank))
    (hy : NeronModelInfra.schemeHomOverComp y O.torusFibre = NeronModelInfra.schemeHomOverComp O.torusFibre φκ) :
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
    rw [← hcompE, NeronModelInfra.schemeHomOverComp_assoc, hy, ← NeronModelInfra.schemeHomOverComp_assoc,
      O.torusFibre_mul χ χ', hφκ, NeronModelInfra.schemeHomOverComp_assoc,
      NeronModelInfra.schemeHomOverComp_assoc, ← hy, ← NeronModelInfra.schemeHomOverComp_assoc,
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

end ModularCurve.JZeroNeronObjectAtP.ToricHecke

open ModularCurve.JZeroNeronObjectAtP.ToricHecke in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (φ : SchemeHomOver O.g O.g)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) :
    ∃ M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O.torusFibre.1 =
        O.torusFibre.1 ≫ (fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g φ).1 := by
  obtain ⟨y, hy⟩ := exists_comp_torusFibre_eq O
    (GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_of_field hΛ.1 (resPt A ≫ Λ.σA)) φ hφ
  obtain ⟨M₀, hM₀⟩ := exists_addMonoidHom_specMap_mapDomain_eq O (fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g φ)
    (fun x y ↦ fibreRestrictAlong_mul (resPt A ≫ Λ.σA) O.L O.L φ hφ (𝟙 _) x y) y hy
  refine ⟨M₀, ?_⟩
  rw [← hM₀]
  exact congrArg Subtype.val hy

end S_ModularCurve_JZeroNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong (solution)
