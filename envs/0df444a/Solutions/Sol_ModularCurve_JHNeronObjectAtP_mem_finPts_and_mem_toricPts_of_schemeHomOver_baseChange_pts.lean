-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.mem_finPts_and_mem_toricPts_of_schemeHomOver_baseChange_pts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d25ce528-f546-5811-b10e-ade205d4ca94

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_mem_finPts_and_mem_toricPts_of_schemeHomOver_baseChange_pts
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_mem_finPts_and_mem_toricPts_of_schemeHomOver_baseChange_pts.ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_mem_finPts_and_mem_toricPts_of_schemeHomOver_baseChange_pts.ModularCurve.JHNeronObjectAtP"

namespace KToricStable

abbrev red (t m : ℕ) : (Fin t → ℤ) →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

theorem red_apply (t m : ℕ) (z : Fin t → ℤ) (i : Fin t) : red t m z i = (z i : ZMod m) := rfl

private def _root_.KToricStable.lift (t m : ℕ) (g : Fin t → ZMod m) : Fin t → ℤ := fun i => ((g i).cast : ℤ)

p2m_export "KToricStable" "lift"
theorem red_lift (t m : ℕ) [NeZero m] (g : Fin t → ZMod m) : red t m (lift t m g) = g := by
  funext i
  simp [red_apply, lift, ZMod.intCast_zmod_cast]

theorem red_map_eq_of_red_eq (t m : ℕ) (M₀ : (Fin t → ℤ) →+ (Fin t → ℤ)) (z z' : Fin t → ℤ)
    (h : red t m z = red t m z') : red t m (M₀ z) = red t m (M₀ z') := by
  have hd : ∀ i, (m : ℤ) ∣ z i - z' i := by
    intro i
    have hi := congrFun h i
    rw [red_apply, red_apply] at hi
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (z' i) (z i) m).mp hi.symm
  choose w hw using hd
  have hz : z = z' + (m : ℤ) • (fun i => w i) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; have := hw i; omega
  funext i
  rw [red_apply, red_apply, hz, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]

def redEnd (t m : ℕ) [NeZero m] (M₀ : (Fin t → ℤ) →+ (Fin t → ℤ)) : (Fin t → ZMod m) →+ (Fin t → ZMod m) where
  toFun g := red t m (M₀ (lift t m g))
  map_zero' := by
    have h : red t m (lift t m 0) = red t m 0 := by rw [red_lift, map_zero]
    rw [red_map_eq_of_red_eq t m M₀ _ _ h, map_zero, map_zero]
  map_add' g g' := by
    have h : red t m (lift t m (g + g')) = red t m (lift t m g + lift t m g') := by
      rw [red_lift, map_add, red_lift, red_lift]
    rw [red_map_eq_of_red_eq t m M₀ _ _ h, map_add, map_add]

theorem redEnd_red (t m : ℕ) [NeZero m] (M₀ : (Fin t → ℤ) →+ (Fin t → ℤ)) (z : Fin t → ℤ) :
    redEnd t m M₀ (red t m z) = red t m (M₀ z) := by
  show red t m (M₀ (lift t m (red t m z))) = red t m (M₀ z)
  apply red_map_eq_of_red_eq
  rw [red_lift]

theorem conv_single {S T : Type} [CommRing S] [CommRing T] [Algebra S T] {M : Type} [AddCommMonoid M]
    (χ ψ : WithConv (AddMonoidAlgebra S M →ₐ[S] T)) (g : M) :
    (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) = χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
  rw [AlgHom.convMul_def]
  simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]

theorem conv_comp_mapDomain {S T : Type} [CommRing S] [CommRing T] [Algebra S T] {M N : Type} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) (χ ψ : WithConv (AddMonoidAlgebra S N →ₐ[S] T)) :
    (χ * ψ).ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f) =
      (WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f)) *
        WithConv.toConv (ψ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f))).ofConv := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro g
  rw [AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single, conv_single, conv_single]
  simp only [WithConv.ofConv_toConv, AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]

end KToricStable

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
p2m_export "ModularCurve" "JHNeronObjectAtP.LevelData JHNeronObjectAtP JHNeronObjectAtP.toricPoint JHNeronObjectAtP.toricPts JHNeronObjectAtP.finPts JZeroNeronObjectAtP xHFunctionFieldBar JH JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "LevelData toricPoint toricPts finPts torusFibre toricLift abqFibre toricLift_mul mk abqFibre_mul pts g mk.inj toricLift_special torusFibre_mul G toricRank torusFibre_isClosedImmersion abqFibre_eq_one_iff L eq_of_muBaseChange_residue_comp_eq"
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

theorem exists_comp_torusFibre_eq
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hAκ : AbelianSchemePropertyBundle (ResidueField ↥A)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
    (φκ : SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
    (hφκ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt A ≫ Λ.σA)).mul s x y) φκ =
        (O.L.baseChange (resPt A ≫ Λ.σA)).mul s (NeronModelInfra.schemeHomOverComp x φκ)
          (NeronModelInfra.schemeHomOverComp y φκ)) :
    ∃ y : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (torusStr (ResidueField ↥A) O.toricRank),
      NeronModelInfra.schemeHomOverComp y O.torusFibre =
        NeronModelInfra.schemeHomOverComp O.torusFibre φκ := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  set tF := O.torusFibre with htF

  apply (O.abqFibre_eq_one_iff (torusStr (ResidueField ↥A) O.toricRank) (NeronModelInfra.schemeHomOverComp tF φκ)).mp
  intro i
  set ψ := NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp tF φκ) (O.abqFibre i) with hψ

  obtain ⟨a, ha, hψa⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
      hAκ O.toricRank ψ.1 ψ.2

  let u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (torusStr (ResidueField ↥A) O.toricRank) :=
    torusPt (ResidueField ↥A) O.toricRank (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[(ResidueField ↥A)] (ResidueField ↥A))).ofConv
  have hu : NeronModelInfra.schemeHomOverComp u tF = (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    apply eq_one_of_mul_self
    have h := O.torusFibre_mul 1 1
    rw [mul_one] at h
    exact h.symm

  have hψu : NeronModelInfra.schemeHomOverComp u ψ = (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    have e1 : NeronModelInfra.schemeHomOverComp u ψ =
        NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp u tF) φκ) (O.abqFibre i) := by
      apply Subtype.ext
      simp only [hψ, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    rw [e1, hu, comp_one_eq_one (O.L.baseChange (resPt A ≫ Λ.σA)) (O.L.baseChange (resPt A ≫ Λ.σA)) φκ (𝟙 _) (hφκ (𝟙 _)),
      comp_one_eq_one (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (O.abqFibre i) (𝟙 _) (O.abqFibre_mul i (𝟙 _))]

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

theorem exists_addMonoidHom_specMap_mapDomain_eq
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
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

end ModularCurve.JHNeronObjectAtP.ToricHecke

namespace WFinStabAux

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

noncomputable abbrev tFA (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank ≫ resPt A) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
  RelativeGroupLaw.baseChangePointOfBase Λ.σA
    (castOver (Category.assoc (torusStr (ResidueField ↥A) O.toricRank) (resPt A) Λ.σA).symm
      (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) O.torusFibre))

theorem tFA_fst (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    (tFA O).1 ≫ pullback.fst O.g Λ.σA = O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) := by
  simp only [tFA, RelativeGroupLaw.baseChangePointOfBase_coe, castOver, RelativeGroupLaw.baseChangePointToBase_coe,
    pullback.lift_fst]

theorem tFA_snd (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    (tFA O).1 ≫ pullback.snd O.g Λ.σA = torusStr (ResidueField ↥A) O.toricRank ≫ resPt A := by
  simp only [tFA, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]

theorem muBaseChange_muStr (A : ValuationSubring (AlgebraicClosure ℚ)) (t m : ℕ) :
    muBaseChange (residue ↥A) t m ≫ muStr ↥A t m =
      muToTorus (ResidueField ↥A) t m ≫ torusStr (ResidueField ↥A) t ≫ resPt A := by
  simp only [muBaseChange, muStr, muToTorus, torusStr, resPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  simp [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single]

theorem muBaseChange_toricLift (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m) :
    muBaseChange (residue ↥A) O.toricRank m ≫ (O.toricLift m hm).1 =
      muToTorus (ResidueField ↥A) O.toricRank m ≫ (tFA O).1 := by
  apply pullback.hom_ext
  · simp only [Category.assoc, tFA_fst]
    exact O.toricLift_special m hm
  · simp only [Category.assoc, tFA_snd, (O.toricLift m hm).2]
    exact muBaseChange_muStr A O.toricRank m

end WFinStabAux

namespace WFinStabTorus

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

section generic
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem castOver_mul (L : RelativeGroupLaw R f) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s')
    (a b : SchemeHomOver s f) : castOver h (L.mul s a b) = L.mul s' (castOver h a) (castOver h b) := by
  subst h; rfl

variable {R' : Type} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

theorem ofBase_mul (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (a b : SchemeHomOver (t' ≫ ι) f) :
    RelativeGroupLaw.baseChangePointOfBase ι (L.mul _ a b) =
      (L.baseChange ι).mul t' (RelativeGroupLaw.baseChangePointOfBase ι a) (RelativeGroupLaw.baseChangePointOfBase ι b) := by
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase]

end generic

noncomputable def jκ (O : JHNeronObjectAtP p M H hpM A hA Λ) : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g Λ.σA :=
  pullback.lift (pullback.fst O.g (resPt A ≫ Λ.σA)) (pullback.snd O.g (resPt A ≫ Λ.σA) ≫ resPt A)
    (by rw [Category.assoc]; exact pullback.condition)

noncomputable def Wκ (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) :
    SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  ⟨pullback.lift (jκ O ≫ W.1 ≫ pullback.fst O.g Λ.σA) (pullback.snd O.g (resPt A ≫ Λ.σA)) (by
      have hW2 : W.1 ≫ pullback.snd O.g Λ.σA = pullback.snd O.g Λ.σA := W.2
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc W.1, hW2, jκ, pullback.lift_snd_assoc, Category.assoc]),
    pullback.lift_snd _ _ _⟩

theorem Wκ_fst (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) :
    (Wκ O W).1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) = jκ O ≫ W.1 ≫ pullback.fst O.g Λ.σA := by
  simp only [Wκ, pullback.lift_fst]

theorem Wκ_snd (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) :
    (Wκ O W).1 ≫ pullback.snd O.g (resPt A ≫ Λ.σA) = pullback.snd O.g (resPt A ≫ Λ.σA) := by
  simp only [Wκ, pullback.lift_snd]

theorem toBase_comp_Wκ (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
    (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)) :
    RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) (NeronModelInfra.schemeHomOverComp x (Wκ O W)) =
      castOver (Category.assoc s (resPt A) Λ.σA)
        (RelativeGroupLaw.baseChangePointToBase Λ.σA
          (NeronModelInfra.schemeHomOverComp
            (RelativeGroupLaw.baseChangePointOfBase Λ.σA
              (castOver (Category.assoc s (resPt A) Λ.σA).symm
                (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) x))) W)) := by
  have hx2 : x.1 ≫ pullback.snd O.g (resPt A ≫ Λ.σA) = s := x.2
  have hx : x.1 ≫ jκ O =
      (RelativeGroupLaw.baseChangePointOfBase Λ.σA
        (castOver (Category.assoc s (resPt A) Λ.σA).symm
          (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) x))).1 := by
    apply pullback.hom_ext
    · simp only [jκ, Category.assoc, pullback.lift_fst, RelativeGroupLaw.baseChangePointOfBase_coe, castOver,
        RelativeGroupLaw.baseChangePointToBase_coe]
    · simp only [jκ, Category.assoc, pullback.lift_snd, RelativeGroupLaw.baseChangePointOfBase_coe]
      rw [← Category.assoc, hx2]
  apply Subtype.ext
  simp only [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, castOver,
    Category.assoc, Wκ_fst]
  rw [← Category.assoc x.1 (jκ O), hx]
  simp only [RelativeGroupLaw.baseChangePointOfBase_coe, castOver, RelativeGroupLaw.baseChangePointToBase_coe,
    Category.assoc]

theorem Wκ_mul (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hWmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W =
        (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W) (NeronModelInfra.schemeHomOverComp y W))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
    (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)) :
    NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt A ≫ Λ.σA)).mul s x y) (Wκ O W) =
      (O.L.baseChange (resPt A ≫ Λ.σA)).mul s (NeronModelInfra.schemeHomOverComp x (Wκ O W))
        (NeronModelInfra.schemeHomOverComp y (Wκ O W)) := by
  apply (RelativeGroupLaw.baseChangePointEquiv (resPt A ≫ Λ.σA) s).injective
  change RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) _ =
    RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) _
  simp only [toBase_comp_Wκ, RelativeGroupLaw.baseChangePointToBase_mul, castOver_mul, ofBase_mul, hWmul]

theorem Wκ_jκ (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) :
    (Wκ O W).1 ≫ jκ O = jκ O ≫ W.1 := by
  have hW2 : W.1 ≫ pullback.snd O.g Λ.σA = pullback.snd O.g Λ.σA := W.2
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, jκ, pullback.lift_fst, ← jκ, Wκ_fst]
  · rw [Category.assoc, Category.assoc, hW2, jκ, pullback.lift_snd, ← Category.assoc, Wκ_snd]

theorem tFA_eq (O : JHNeronObjectAtP p M H hpM A hA Λ) : (WFinStabAux.tFA O).1 = O.torusFibre.1 ≫ jκ O := by
  have h2 : O.torusFibre.1 ≫ pullback.snd O.g (resPt A ≫ Λ.σA) = torusStr (ResidueField ↥A) O.toricRank := O.torusFibre.2
  apply pullback.hom_ext
  · rw [WFinStabAux.tFA_fst, Category.assoc, jκ, pullback.lift_fst]
  · rw [WFinStabAux.tFA_snd, Category.assoc, jκ, pullback.lift_snd, ← Category.assoc, h2]

end WFinStabTorus

open KToricStable

namespace ModularCurve p2m_export "ModularCurve" "JHNeronObjectAtP.LevelData JHNeronObjectAtP JHNeronObjectAtP.toricPoint JHNeronObjectAtP.toricPts JHNeronObjectAtP.finPts JZeroNeronObjectAtP xHFunctionFieldBar JH JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq" namespace JHNeronObjectAtP p2m_export "ModularCurve.JHNeronObjectAtP" "LevelData toricPoint toricPts finPts torusFibre toricLift abqFibre toricLift_mul mk abqFibre_mul pts g mk.inj toricLift_special torusFibre_mul G toricRank torusFibre_isClosedImmersion abqFibre_eq_one_iff L eq_of_muBaseChange_residue_comp_eq" end ModularCurve.JHNeronObjectAtP
p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in

theorem ModularCurve.JHNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_of_baseChange
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hWmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W =
        (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W) (NeronModelInfra.schemeHomOverComp y W)) :
    ∃ M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫
          (RelativeGroupLaw.baseChangePointOfBase Λ.σA
          (castOver (Category.assoc (torusStr (ResidueField ↥A) O.toricRank) (resPt A) Λ.σA).symm
            (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) O.torusFibre))).1 =
        (RelativeGroupLaw.baseChangePointOfBase Λ.σA
          (castOver (Category.assoc (torusStr (ResidueField ↥A) O.toricRank) (resPt A) Λ.σA).symm
            (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) O.torusFibre))).1 ≫ W.1 := by
  obtain ⟨y, hy⟩ := ModularCurve.JHNeronObjectAtP.ToricHecke.exists_comp_torusFibre_eq O
    (GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_of_field hΛ (resPt A ≫ Λ.σA))
    (WFinStabTorus.Wκ O W) (fun s x y ↦ WFinStabTorus.Wκ_mul O W hWmul s x y)
  obtain ⟨M₀, hM₀⟩ := ModularCurve.JHNeronObjectAtP.ToricHecke.exists_addMonoidHom_specMap_mapDomain_eq O
    (WFinStabTorus.Wκ O W) (fun x y ↦ WFinStabTorus.Wκ_mul O W hWmul (𝟙 _) x y) y hy
  refine ⟨M₀, ?_⟩
  have hy1 : y.1 ≫ O.torusFibre.1 = O.torusFibre.1 ≫ (WFinStabTorus.Wκ O W).1 := congrArg Subtype.val hy
  rw [← hM₀, WFinStabTorus.tFA_eq, ← Category.assoc, hy1, Category.assoc, WFinStabTorus.Wκ_jκ, Category.assoc]

p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in

theorem ModularCurve.JHNeronObjectAtP.exists_comp_toricLift_eq_toricLift_comp_mapDomainAlgHom_of_baseChange
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hWmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W =
        (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W) (NeronModelInfra.schemeHomOverComp y W))
    (M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫
          (RelativeGroupLaw.baseChangePointOfBase Λ.σA
          (castOver (Category.assoc (torusStr (ResidueField ↥A) O.toricRank) (resPt A) Λ.σA).symm
            (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) O.torusFibre))).1 =
        (RelativeGroupLaw.baseChangePointOfBase Λ.σA
          (castOver (Category.assoc (torusStr (ResidueField ↥A) O.toricRank) (resPt A) Λ.σA).symm
            (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) O.torusFibre))).1 ≫ W.1)
    (m : ℕ) (hm : 0 < m) :
    ∃ Mbar : (Fin O.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m),
      Mbar.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)) =
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)).comp M₀ ∧
      ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        NeronModelInfra.schemeHomOverComp
            (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ) (O.toricLift m hm)) W =
          NeronModelInfra.schemeHomOverComp
            (muPt A O.toricRank m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))) (O.toricLift m hm) := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  set LA := O.L.baseChange Λ.σA with hLA
  set κ := ResidueField ↥A with hκ

  let Mb : (Fin O.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m) := redEnd O.toricRank m M₀
  let ψ : muCoord ↥A O.toricRank m →ₐ[↥A] muCoord ↥A O.toricRank m := AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mb

  let u : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
    NeronModelInfra.schemeHomOverComp (O.toricLift m hm) W
  let v : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
    ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (O.toricLift m hm).1, by
      rw [Category.assoc, (O.toricLift m hm).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2; exact ψ.comp_algebraMap⟩
  have hu1 : u.1 = (O.toricLift m hm).1 ≫ W.1 := rfl
  have hv1 : v.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (O.toricLift m hm).1 := rfl

  have hpt_u : ∀ θ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m θ) u =
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m θ) (O.toricLift m hm)) W :=
    fun θ => Subtype.ext (Category.assoc _ _ _).symm
  have hpt_v : ∀ θ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m θ) v =
        NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (θ.comp ψ)) (O.toricLift m hm) := by
    intro θ
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (O.toricLift m hm).1 =
      Spec.map (CommRingCat.ofHom (θ.comp ψ).toRingHom) ≫ (O.toricLift m hm).1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  have hu : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) u =
        LA.mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) u)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) u) := by
    intro χ χ'
    rw [hpt_u, hpt_u, hpt_u, O.toricLift_mul m hm χ χ', hWmul]
  have hv : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) v =
        LA.mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) v)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) v) := by
    intro χ χ'
    rw [hpt_v, hpt_v, hpt_v, conv_comp_mapDomain]
    exact O.toricLift_mul m hm _ _

  have hI1 : muBaseChange (residue ↥A) O.toricRank m ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Mb)) ≫ muBaseChange (residue ↥A) O.toricRank m := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      simp [ψ, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
        AddMonoidAlgebra.mapDomain_single]
    · intro g
      simp [ψ, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
        AddMonoidAlgebra.mapDomain_single]
  have hI2 : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Mb)) ≫ muToTorus κ O.toricRank m =
      muToTorus κ O.toricRank m ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
    · intro g
      simp only [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
      congr 1
      exact redEnd_red O.toricRank m M₀ g

  have hsp' : ∀ {X : Scheme.{0}} (k : _ ⟶ X),
      muBaseChange (residue ↥A) O.toricRank m ≫ (O.toricLift m hm).1 ≫ k = muToTorus κ O.toricRank m ≫ (WFinStabAux.tFA O).1 ≫ k := by
    intro X k
    simpa only [Category.assoc] using congrArg (· ≫ k) (WFinStabAux.muBaseChange_toricLift O m hm)
  have hM₀' : ∀ {X : Scheme.{0}} (k : _ ⟶ X),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) ≫ (WFinStabAux.tFA O).1 ≫ k =
        (WFinStabAux.tFA O).1 ≫ W.1 ≫ k := by
    intro X k
    simpa only [Category.assoc] using congrArg (· ≫ k) hM₀
  have hI1' : ∀ {X : Scheme.{0}} (k : _ ⟶ X),
      muBaseChange (residue ↥A) O.toricRank m ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ k =
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Mb)) ≫ muBaseChange (residue ↥A) O.toricRank m ≫ k := by
    intro X k
    simpa only [Category.assoc] using congrArg (· ≫ k) hI1
  have hI2' : ∀ {X : Scheme.{0}} (k : _ ⟶ X),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Mb)) ≫ muToTorus κ O.toricRank m ≫ k =
        muToTorus κ O.toricRank m ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) ≫ k := by
    intro X k
    simpa only [Category.assoc] using congrArg (· ≫ k) hI2
  have huv : muBaseChange (residue ↥A) O.toricRank m ≫ u.1 = muBaseChange (residue ↥A) O.toricRank m ≫ v.1 := by
    rw [hu1, hv1, hsp', ← hM₀, hI1', WFinStabAux.muBaseChange_toricLift O m hm, hI2']

  have huv' := ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq p M H hpM A hA Λ O m hm u v hu hv huv
  refine ⟨Mb, ?_, fun χ => ?_⟩
  · exact AddMonoidHom.ext fun z => redEnd_red O.toricRank m M₀ z
  · rw [← hpt_u, huv', hpt_v]

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hWmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W =
        (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W) (NeronModelInfra.schemeHomOverComp y W))
    (w : JH M H →+ JH M H)
    (hWpts : ∀ x : JH M H, O.pts (w x) =
      genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts x))) W)) :
    (∀ (m : ℕ) (x : JH M H), x ∈ O.finPts m → w x ∈ O.finPts m) ∧
    (GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f →
      ∀ (m : ℕ), 0 < m → ∀ x : JH M H, x ∈ O.toricPts m → w x ∈ O.toricPts m) := by
  refine ⟨?_, ?_⟩
  ·
    intro m x hx
    rw [JHNeronObjectAtP.finPts] at hx ⊢
    have hle : AddSubgroup.closure {x | x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ∧
          ExtendsToPlace A Λ.σA (O.pts x)} ≤
        (AddSubgroup.closure {x | x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ∧
          ExtendsToPlace A Λ.σA (O.pts x)}).comap w := by
      rw [AddSubgroup.closure_le]
      rintro y ⟨hy1, ⟨s, hs⟩⟩
      rw [AddSubgroup.coe_comap, Set.mem_preimage]
      apply AddSubgroup.subset_closure
      refine ⟨?_, ?_⟩
      · rw [Pic0.mem_torsion] at hy1 ⊢
        rw [← map_zsmul, hy1, map_zero]
      · refine ⟨castOver (Category.id_comp Λ.σA) (RelativeGroupLaw.baseChangePointToBase Λ.σA
          (NeronModelInfra.schemeHomOverComp
            (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver (Category.id_comp Λ.σA).symm s)) W)), ?_⟩
        have hpt : (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts y))).1 =
            barPt A ≫ (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver (Category.id_comp Λ.σA).symm s)).1 := by
          apply pullback.hom_ext
          · simp only [RelativeGroupLaw.baseChangePointOfBase_coe, Category.assoc, pullback.lift_fst]
            exact hs
          · simp only [RelativeGroupLaw.baseChangePointOfBase_coe, Category.assoc, pullback.lift_snd, Category.comp_id]
        rw [hWpts]
        simp only [genOfBaseChangePt, castOver, RelativeGroupLaw.baseChangePointToBase_coe,
          NeronModelInfra.schemeHomOverComp_coe, Category.assoc] at hpt ⊢
        rw [hpt]
        simp only [Category.assoc]
    exact hle hx
  ·
    intro hΛ m hm
    obtain ⟨M₀, hM₀⟩ :=
      ModularCurve.JHNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_of_baseChange
        p M H hpM A hA Λ hΛ O W hWmul
    obtain ⟨Mbar, -, hfac⟩ :=
      ModularCurve.JHNeronObjectAtP.exists_comp_toricLift_eq_toricLift_comp_mapDomainAlgHom_of_baseChange
        p M H hpM A hA Λ O W hWmul M₀ hM₀ m hm

    have hinv : ∀ y : SchemeHomOver (barPt A) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
        RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (genOfBaseChangePt Λ.hσA y)) = y := by
      intro y
      rw [show castOver Λ.hσA.symm (genOfBaseChangePt Λ.hσA y) = RelativeGroupLaw.baseChangePointToBase Λ.σA y from
        Subtype.ext rfl, RelativeGroupLaw.baseChangePointOfBase_toBase]

    have key : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        w (O.toricPoint m hm χ) = O.toricPoint m hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := by
      intro χ
      apply O.pts.injective
      rw [hWpts]
      simp only [JHNeronObjectAtP.toricPoint, Equiv.apply_symm_apply, hinv, hfac χ]
    intro x hx
    rw [JHNeronObjectAtP.toricPts, dif_pos hm] at hx ⊢
    have hle : AddSubgroup.closure (Set.range (O.toricPoint m hm)) ≤
        (AddSubgroup.closure (Set.range (O.toricPoint m hm))).comap w := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨χ, rfl⟩
      rw [AddSubgroup.coe_comap, Set.mem_preimage, key χ]
      exact AddSubgroup.subset_closure ⟨_, rfl⟩
    exact hle hx

end S_ModularCurve_JHNeronObjectAtP_mem_finPts_and_mem_toricPts_of_schemeHomOver_baseChange_pts
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_mem_finPts_and_mem_toricPts_of_schemeHomOver_baseChange_pts (solution)
