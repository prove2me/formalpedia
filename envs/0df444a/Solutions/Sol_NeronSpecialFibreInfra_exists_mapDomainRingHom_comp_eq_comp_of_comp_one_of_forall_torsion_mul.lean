-- Prove2me | solution 1 for NeronSpecialFibreInfra.exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7be9372c-f022-5588-a160-5a3eaceadb51

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronSpecialFibreInfra_exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_NeronSpecialFibreInfra_exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul.ModularCurve ModularCurve.JZeroNeronObjectAtP"

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

theorem exists_addMonoidHom_single_eq {G' : Type*} [AddCommGroup G'] (hsep : HasEnoughChars κ (G' × G'))
    (E : AddMonoidAlgebra κ G →ₐ[κ] AddMonoidAlgebra κ G')
    (hE : ∀ (F F' : Multiplicative G' →* κ) (g : G),
      AddMonoidAlgebra.lift κ κ G' (F * F') (E (single g 1)) =
        AddMonoidAlgebra.lift κ κ G' F (E (single g 1)) * AddMonoidAlgebra.lift κ κ G' F' (E (single g 1))) :
    ∃ M : G →+ G', ∀ g : G, E (single g 1) = single (M g) 1 := by
  classical
  have key : ∀ g : G, ∃ v : G', E (single g 1) = single v 1 := by
    intro g
    set a : AddMonoidAlgebra κ G' := E (single g 1) with ha
    let P : AddMonoidAlgebra κ (G' × G') := AddMonoidAlgebra.mapDomain (fun v ↦ (v, v)) a
    let Q : AddMonoidAlgebra κ (G' × G') :=
      AddMonoidAlgebra.ofCoeff (finsuppTensorFinsupp' κ G' G' (a.coeff ⊗ₜ[κ] a.coeff))
    have hPQ : P = Q := by
      refine sub_eq_zero.mp (eq_zero_of_forall_lift_eq_zero hsep _ fun Ψ ↦ ?_)
      let F : Multiplicative G' →* κ := Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl G' G'))
      let F' : Multiplicative G' →* κ := Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr G' G'))
      have h1 : AddMonoidAlgebra.lift κ κ (G' × G') Ψ P = AddMonoidAlgebra.lift κ κ G' (F * F') a := by
        simp only [P, AddMonoidAlgebra.lift_apply, AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff]
        rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_mul])]
        refine Finsupp.sum_congr fun v _ ↦ ?_
        congr 1
        simp only [F, F', MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
          AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, AddMonoidHom.inl_apply,
          AddMonoidHom.inr_apply, ← map_mul, ← ofAdd_add, Prod.mk_add_mk, add_zero, zero_add]
      rw [map_sub, h1, hE]
      exact sub_eq_zero.mpr (lift_finsuppTensorFinsupp' Ψ a a).symm

    have hcoeff : ∀ v w : G', (if v = w then a v else 0) = a v * a w := by
      intro v w
      have := congrArg (fun x : AddMonoidAlgebra κ (G' × G') ↦ x (v, w)) hPQ
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

section tors

variable {G : Type*} [AddCommGroup G]

def IsTorsChar (κ : Type*) [Field κ] {G : Type*} [AddCommGroup G] (F : Multiplicative G →* κ) : Prop :=
  ∃ m : ℕ, (m : κ) ≠ 0 ∧ ∀ v : Multiplicative G, F v ^ m = 1

variable (κ G) in

def torsChars : Submonoid (Multiplicative G →* κ) where
  carrier := {F | IsTorsChar κ F}
  one_mem' := ⟨1, by simp, fun v ↦ by simp⟩
  mul_mem' := by
    rintro F F' ⟨m, hm, hF⟩ ⟨m', hm', hF'⟩
    refine ⟨m * m', by exact_mod_cast mul_ne_zero hm hm', fun v ↦ ?_⟩
    rw [MonoidHom.mul_apply, mul_pow, pow_mul, hF, one_pow, mul_comm m m', pow_mul, hF', one_pow, one_mul]

def HasEnoughTorsChars (κ : Type*) [Field κ] (G : Type*) [AddCommGroup G] : Prop :=
  ∀ u : G, u ≠ 0 → ∃ F : Multiplicative G →* κ, IsTorsChar κ F ∧ F (Multiplicative.ofAdd u) ≠ 1

def evHomTors (κ : Type*) [Field κ] (u : G) : ↥(torsChars κ G) →* κ :=
  (evHom κ u).comp (torsChars κ G).subtype

theorem evHomTors_injective (h : HasEnoughTorsChars κ G) : Function.Injective (evHomTors κ : G → _) := by
  intro u u' huu'
  by_contra hne
  obtain ⟨F, hFt, hF⟩ := h (u - u') (sub_ne_zero.mpr hne)
  apply hF
  have := congrArg (fun φ : ↥(torsChars κ G) →* κ ↦ φ ⟨F, hFt⟩) huu'
  simp only [evHomTors, evHom, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply,
    Submonoid.coe_subtype] at this
  rw [ofAdd_sub, div_eq_mul_inv, map_mul, map_inv, this, mul_inv_cancel₀]
  exact (F.toHomUnits (Multiplicative.ofAdd u')).ne_zero

theorem eq_zero_of_forall_torsLift_eq_zero (h : HasEnoughTorsChars κ G) (d : AddMonoidAlgebra κ G)
    (hd : ∀ F : Multiplicative G →* κ, IsTorsChar κ F → AddMonoidAlgebra.lift κ κ G F d = 0) : d = 0 := by
  classical
  have hli : LinearIndependent κ (fun u : G ↦ ((evHomTors κ u : ↥(torsChars κ G) →* κ) :
      ↥(torsChars κ G) → κ)) :=
    (linearIndependent_monoidHom ↥(torsChars κ G) κ).comp (evHomTors κ) (evHomTors_injective h)
  suffices h0 : d.coeff = 0 from
    AddMonoidAlgebra.coeff_injective (h0.trans AddMonoidAlgebra.coeff_zero.symm)
  refine linearIndependent_iff.mp hli d.coeff ?_
  funext F
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.zero_apply]
  have := hd F.1 F.2
  rw [AddMonoidAlgebra.lift_apply, Finsupp.sum] at this
  simpa [evHomTors, evHom, smul_eq_mul, mul_comm] using this

theorem hasEnoughTorsChars_prod {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (hG : HasEnoughTorsChars κ G) (hH : HasEnoughTorsChars κ H) : HasEnoughTorsChars κ (G × H) := by
  rintro ⟨u, w⟩ huw
  by_cases hu : u = 0
  · subst hu
    have hw : w ≠ 0 := fun h ↦ huw (by rw [h]; rfl)
    obtain ⟨F, ⟨m, hm, hFm⟩, hF⟩ := hH w hw
    exact ⟨F.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd G H)), ⟨m, hm, fun v ↦ hFm _⟩, hF⟩
  · obtain ⟨F, ⟨m, hm, hFm⟩, hF⟩ := hG u hu
    exact ⟨F.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst G H)), ⟨m, hm, fun v ↦ hFm _⟩, hF⟩

theorem hasEnoughTorsChars_pi_int [IsAlgClosed κ] (t : ℕ) : HasEnoughTorsChars κ (Fin t → ℤ) := by
  classical
  intro u hu
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)

  obtain ⟨ℓ, hℓge, hℓp⟩ := Nat.exists_infinite_primes ((u i).natAbs + ringChar κ + 1)
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓκ : (ℓ : κ) ≠ 0 := by
    intro h0
    have hdvd : ringChar κ ∣ ℓ := (ringChar.spec κ ℓ).mp h0
    rcases (Nat.dvd_prime hℓp).mp hdvd with h1 | h2
    ·
      haveI : Nontrivial κ := inferInstance
      exact (CharP.ringChar_ne_one (R := κ)) h1
    · omega
  haveI : NeZero (ℓ : κ) := ⟨hℓκ⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : κ, IsPrimitiveRoot ζ ℓ := by
    have hdeg : (Polynomial.cyclotomic ℓ κ).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic, Nat.totient_prime hℓp]
      exact_mod_cast (show ℓ - 1 ≠ 0 by have := hℓp.two_le; omega)
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic ℓ κ) hdeg
    exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hℓp.ne_zero
  refine ⟨coordChar ζ hζ0 i, ⟨ℓ, hℓκ, fun v ↦ ?_⟩, ?_⟩
  · simp only [coordChar, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
  · simp only [coordChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    have hlt : (u i).natAbs < ℓ := by omega
    have hpos : 0 < (u i).natAbs := Int.natAbs_pos.mpr hi
    rcases Int.natAbs_eq (u i) with h | h
    · rw [h, zpow_natCast, Ne, hζ.pow_eq_one_iff_dvd]
      intro hd; exact absurd (Nat.le_of_dvd hpos hd) (by omega)
    · rw [h, zpow_neg, zpow_natCast, Ne, inv_eq_one, hζ.pow_eq_one_iff_dvd]
      intro hd; exact absurd (Nat.le_of_dvd hpos hd) (by omega)

theorem exists_addMonoidHom_single_eq_tors {G' : Type*} [AddCommGroup G'] (hsep : HasEnoughTorsChars κ (G' × G'))
    (E : AddMonoidAlgebra κ G →ₐ[κ] AddMonoidAlgebra κ G')
    (hE : ∀ (F F' : Multiplicative G' →* κ), IsTorsChar κ F → IsTorsChar κ F' → ∀ (g : G),
      AddMonoidAlgebra.lift κ κ G' (F * F') (E (single g 1)) =
        AddMonoidAlgebra.lift κ κ G' F (E (single g 1)) * AddMonoidAlgebra.lift κ κ G' F' (E (single g 1))) :
    ∃ M : G →+ G', ∀ g : G, E (single g 1) = single (M g) 1 := by
  classical
  have key : ∀ g : G, ∃ v : G', E (single g 1) = single v 1 := by
    intro g
    set a : AddMonoidAlgebra κ G' := E (single g 1) with ha
    let P : AddMonoidAlgebra κ (G' × G') := AddMonoidAlgebra.mapDomain (fun v ↦ (v, v)) a
    let Q : AddMonoidAlgebra κ (G' × G') :=
      AddMonoidAlgebra.ofCoeff (finsuppTensorFinsupp' κ G' G' (a.coeff ⊗ₜ[κ] a.coeff))
    have hPQ : P = Q := by
      refine sub_eq_zero.mp (eq_zero_of_forall_torsLift_eq_zero hsep _ fun Ψ hΨ ↦ ?_)
      let F : Multiplicative G' →* κ := Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl G' G'))
      let F' : Multiplicative G' →* κ := Ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr G' G'))
      have h1 : AddMonoidAlgebra.lift κ κ (G' × G') Ψ P = AddMonoidAlgebra.lift κ κ G' (F * F') a := by
        simp only [P, AddMonoidAlgebra.lift_apply, AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff]
        rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_mul])]
        refine Finsupp.sum_congr fun v _ ↦ ?_
        congr 1
        simp only [F, F', MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
          AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, AddMonoidHom.inl_apply,
          AddMonoidHom.inr_apply, ← map_mul, ← ofAdd_add, Prod.mk_add_mk, add_zero, zero_add]
      have hFt : IsTorsChar κ F := by
        obtain ⟨m, hm, hΨm⟩ := hΨ; exact ⟨m, hm, fun v ↦ hΨm _⟩
      have hF't : IsTorsChar κ F' := by
        obtain ⟨m, hm, hΨm⟩ := hΨ; exact ⟨m, hm, fun v ↦ hΨm _⟩
      rw [map_sub, h1, hE F F' hFt hF't]
      exact sub_eq_zero.mpr (lift_finsuppTensorFinsupp' Ψ a a).symm

    have hcoeff : ∀ v w : G', (if v = w then a v else 0) = a v * a w := by
      intro v w
      have := congrArg (fun x : AddMonoidAlgebra κ (G' × G') ↦ x (v, w)) hPQ
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

end tors

end main

end ToricHeckeAlg

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP"
namespace NeronCompare
namespace Tor
p2m_open "ModularCurve"

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

theorem torusPt_comp_specMap (t₀ : ℕ) (χ : torusCoord S t →ₐ[S] S) (E : torusCoord S t₀ →ₐ[S] torusCoord S t)
    (hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ torusStr S t₀ = torusStr S t) :
    NeronModelInfra.schemeHomOverComp (torusPt S t χ) (⟨Spec.map (CommRingCat.ofHom E.toRingHom), hE⟩ :
      SchemeHomOver (torusStr S t) (torusStr S t₀)) = torusPt S t₀ (χ.comp E) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Spec.map (CommRingCat.ofHom E.toRingHom) =
    Spec.map (CommRingCat.ofHom (χ.comp E).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_algHom_specMap_eq (t₀ : ℕ) (y : SchemeHomOver (torusStr S t) (torusStr S t₀)) :
    ∃ E : torusCoord S t₀ →ₐ[S] torusCoord S t, Spec.map (CommRingCat.ofHom E.toRingHom) = y.1 := by
  let r : CommRingCat.of (torusCoord S t₀) ⟶ CommRingCat.of (torusCoord S t) := Spec.preimage y.1
  have hr : Spec.map r = y.1 := Spec.map_preimage _
  have hcomp : r.hom.comp (algebraMap S (torusCoord S t₀)) = algebraMap S (torusCoord S t) := by
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t₀)) ≫ r) =
        Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t))) := by
      rw [Spec.map_comp, hr]; exact y.2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  refine ⟨{ r.hom with commutes' := fun c ↦ ?_ }, ?_⟩
  · exact congrFun (congrArg DFunLike.coe hcomp) c
  · rw [← hr]; rfl

end torus

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

def IsTorsPt (χ : AddMonoidAlgebra S G →ₐ[S] S) : Prop :=
  ∃ m : ℕ, (m : S) ≠ 0 ∧ ∀ v : G, χ (AddMonoidAlgebra.single v 1) ^ m = 1

theorem isTorsPt_lift_iff (F : Multiplicative G →* S) :
    IsTorsPt (AddMonoidAlgebra.lift S S G F) ↔ ToricHeckeAlg.IsTorsChar S F := by
  simp only [IsTorsPt, ToricHeckeAlg.IsTorsChar, ToricHeckeAlg.lift_single_one]
  constructor
  · rintro ⟨m, hm, h⟩; exact ⟨m, hm, fun v ↦ by simpa using h (Multiplicative.toAdd v)⟩
  · rintro ⟨m, hm, h⟩; exact ⟨m, hm, fun v ↦ h _⟩

end conv

section core

variable {R : Type} [CommRing R] {κ : Type} [Field κ] [IsAlgClosed κ]
  (ι ι₀ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R))
  {G G₀ X₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}
  {f₀ : X₀ ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R g) (L₀ : RelativeGroupLaw R g₀) (Lf₀ : RelativeGroupLaw R f₀)
  {t t₀ : ℕ}

theorem exists_comp_torusFibre_eq
    (hAκ₀ : AbelianSchemePropertyBundle κ (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    (τ : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr ι g))
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ =
        (L.baseChange ι).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ))
    (τ₀ : SchemeHomOver (torusStr κ t₀) (RelativeGroupLaw.baseChangeStr ι₀ g₀))
    (abq₀ : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr ι₀ g₀) (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    (abq₀_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of κ))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      NeronModelInfra.schemeHomOverComp ((L₀.baseChange ι₀).mul s x y) (abq₀ i) =
        (Lf₀.baseChange ι₀).mul s (NeronModelInfra.schemeHomOverComp x (abq₀ i))
          (NeronModelInfra.schemeHomOverComp y (abq₀ i)))
    (abq₀_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of κ))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abq₀ i) = (Lf₀.baseChange ι₀).one s) ↔
        ∃ y : SchemeHomOver s (torusStr κ t₀), NeronModelInfra.schemeHomOverComp y τ₀ = x)
    (Ψκ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι₀ g₀))
    (hΨκ_one : NeronModelInfra.schemeHomOverComp ((L.baseChange ι).one (𝟙 _)) Ψκ = (L₀.baseChange ι₀).one (𝟙 _)) :
    ∃ y : SchemeHomOver (torusStr κ t) (torusStr κ t₀),
      NeronModelInfra.schemeHomOverComp y τ₀ = NeronModelInfra.schemeHomOverComp τ Ψκ := by

  apply (abq₀_eq_one_iff (torusStr κ t) (NeronModelInfra.schemeHomOverComp τ Ψκ)).mp
  intro i
  set ψ := NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp τ Ψκ) (abq₀ i) with hψ

  obtain ⟨a, ha, hψa⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int hAκ₀ t ψ.1 ψ.2

  let u : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (torusStr κ t) :=
    torusPt κ t (1 : WithConv (torusCoord κ t →ₐ[κ] κ)).ofConv
  have hu : NeronModelInfra.schemeHomOverComp u τ = (L.baseChange ι).one (𝟙 _) := by
    apply eq_one_of_mul_self
    have h := hτmul 1 1
    rw [mul_one] at h
    exact h.symm

  have hψu : NeronModelInfra.schemeHomOverComp u ψ = (Lf₀.baseChange ι₀).one (𝟙 _) := by
    have e1 : NeronModelInfra.schemeHomOverComp u ψ =
        NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp u τ) Ψκ) (abq₀ i) := by
      apply Subtype.ext
      simp only [hψ, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    rw [e1, hu, hΨκ_one, comp_one_eq_one (L₀.baseChange ι₀) (Lf₀.baseChange ι₀) (abq₀ i) (𝟙 _) (abq₀_mul i (𝟙 _))]

  have ha1 : a = ((Lf₀.baseChange ι₀).one (𝟙 _)).1 := by
    have := congrArg Subtype.val hψu
    rw [NeronModelInfra.schemeHomOverComp_coe, hψa, ← Category.assoc, u.2, Category.id_comp] at this
    exact this

  apply Subtype.ext
  rw [hψa, ha1]
  have := congrArg Subtype.val
    ((Lf₀.baseChange ι₀).one_natural (𝟙 _) (torusStr κ t) (torusStr κ t) (Category.comp_id _))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this

end core

section matrix

variable {R : Type} [CommRing R] {κ : Type} [Field κ] [IsAlgClosed κ]
  (ι ι₀ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R))
  {G G₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R g) (L₀ : RelativeGroupLaw R g₀)
  {t t₀ : ℕ}

theorem exists_addMonoidHom_specMap_mapDomain_eq
    (τ : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr ι g))
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ =
        (L.baseChange ι).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ))
    (τ₀ : SchemeHomOver (torusStr κ t₀) (RelativeGroupLaw.baseChangeStr ι₀ g₀)) (hτ₀ : IsClosedImmersion τ₀.1)
    (hτ₀mul : ∀ χ χ' : WithConv (torusCoord κ t₀ →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ₀ =
        (L₀.baseChange ι₀).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ₀)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ₀))
    (Ψκ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι₀ g₀))
    (hΨκ : ∀ χ χ' : torusCoord κ t →ₐ[κ] κ, IsTorsPt χ → IsTorsPt χ' →
      NeronModelInfra.schemeHomOverComp ((L.baseChange ι).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (torusPt κ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt κ t χ') τ)) Ψκ =
        (L₀.baseChange ι₀).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt κ t χ) τ) Ψκ)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt κ t χ') τ) Ψκ))
    (y : SchemeHomOver (torusStr κ t) (torusStr κ t₀))
    (hy : NeronModelInfra.schemeHomOverComp y τ₀ = NeronModelInfra.schemeHomOverComp τ Ψκ) :
    ∃ M₀ : (Fin t₀ → ℤ) →+ (Fin t → ℤ),
      y.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) := by

  obtain ⟨E, hE⟩ := exists_algHom_specMap_eq κ t t₀ y
  have hyE : y = ⟨Spec.map (CommRingCat.ofHom E.toRingHom), hE ▸ y.2⟩ := Subtype.ext hE.symm

  have hinj : Function.Injective fun χ₀ : torusCoord κ t₀ →ₐ[κ] κ ↦
      NeronModelInfra.schemeHomOverComp (torusPt κ t₀ χ₀) τ₀ := by
    intro χ χ' h
    apply torusPt_injective κ t₀
    apply Subtype.ext
    haveI := hτ₀
    have h1 := congrArg Subtype.val h
    simp only [NeronModelInfra.schemeHomOverComp_coe] at h1
    exact (cancel_mono τ₀.1).mp h1

  have hcompE : ∀ ξ : torusCoord κ t →ₐ[κ] κ,
      NeronModelInfra.schemeHomOverComp (torusPt κ t ξ) y = torusPt κ t₀ (ξ.comp E) := by
    intro ξ
    rw [hyE]
    exact torusPt_comp_specMap κ t t₀ ξ E _

  have hpts : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ), IsTorsPt χ.ofConv → IsTorsPt χ'.ofConv →
      (χ * χ').ofConv.comp E =
        (WithConv.toConv (χ.ofConv.comp E) * WithConv.toConv (χ'.ofConv.comp E)).ofConv := by
    intro χ χ' hχ hχ'
    apply hinj
    change NeronModelInfra.schemeHomOverComp (torusPt κ t₀ ((χ * χ').ofConv.comp E)) τ₀ =
      NeronModelInfra.schemeHomOverComp
        (torusPt κ t₀ (WithConv.toConv (χ.ofConv.comp E) * WithConv.toConv (χ'.ofConv.comp E)).ofConv) τ₀
    rw [← hcompE, NeronModelInfra.schemeHomOverComp_assoc, hy, ← NeronModelInfra.schemeHomOverComp_assoc,
      hτmul χ χ', hΨκ χ.ofConv χ'.ofConv hχ hχ', NeronModelInfra.schemeHomOverComp_assoc,
      NeronModelInfra.schemeHomOverComp_assoc, ← hy, ← NeronModelInfra.schemeHomOverComp_assoc,
      ← NeronModelInfra.schemeHomOverComp_assoc, hcompE, hcompE,
      hτ₀mul (WithConv.toConv (χ.ofConv.comp E)) (WithConv.toConv (χ'.ofConv.comp E))]

  have hE' : ∀ (F F' : Multiplicative (Fin t → ℤ) →* κ), ToricHeckeAlg.IsTorsChar κ F → ToricHeckeAlg.IsTorsChar κ F' →
      ∀ (g : Fin t₀ → ℤ),
      AddMonoidAlgebra.lift κ κ _ (F * F') (E (AddMonoidAlgebra.single g 1)) =
        AddMonoidAlgebra.lift κ κ _ F (E (AddMonoidAlgebra.single g 1)) *
          AddMonoidAlgebra.lift κ κ _ F' (E (AddMonoidAlgebra.single g 1)) := by
    intro F F' hF hF' g
    have h := congrArg (fun f : torusCoord κ t₀ →ₐ[κ] κ ↦ f (AddMonoidAlgebra.single g 1))
      (hpts (WithConv.toConv (AddMonoidAlgebra.lift κ κ _ F)) (WithConv.toConv (AddMonoidAlgebra.lift κ κ _ F'))
        ((isTorsPt_lift_iff F).mpr hF) ((isTorsPt_lift_iff F').mpr hF'))
    simp only [AlgHom.comp_apply] at h
    rw [convMul_ofConv_single] at h
    change _ = (AddMonoidAlgebra.lift κ κ _ F).comp E (AddMonoidAlgebra.single g 1) *
      (AddMonoidAlgebra.lift κ κ _ F').comp E (AddMonoidAlgebra.single g 1) at h
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at h
    rw [← h, ← convMul_lift]
  obtain ⟨M₀, hM₀⟩ := ToricHeckeAlg.exists_addMonoidHom_single_eq_tors
    (ToricHeckeAlg.hasEnoughTorsChars_prod (ToricHeckeAlg.hasEnoughTorsChars_pi_int t)
      (ToricHeckeAlg.hasEnoughTorsChars_pi_int t)) E hE'
  refine ⟨M₀, ?_⟩
  rw [← hE]
  congr 2
  have hEM : E = AddMonoidAlgebra.mapDomainAlgHom κ κ M₀ :=
    AddMonoidAlgebra.algHom_ext (fun g ↦ by
      rw [hM₀]
      first
        | (rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single])
        | simp [AddMonoidAlgebra.mapDomain_single]) (Subsingleton.elim _ _)
  rw [hEM]
  rfl

end matrix

end ModularCurve.NeronCompare.Tor

open ModularCurve.NeronCompare.Tor in
theorem solution
    {R : Type} [CommRing R] {κ : Type} [Field κ] [IsAlgClosed κ]
    (ι ι₀ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R))
    {G G₀ X₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}
    {f₀ : X₀ ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g) (L₀ : RelativeGroupLaw R g₀) (Lf₀ : RelativeGroupLaw R f₀)
    (hX₀ : AbelianSchemePropertyBundle κ (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    {t t₀ : ℕ}
    (τ : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr ι g))
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ =
        (L.baseChange ι).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ))
    (τ₀ : SchemeHomOver (torusStr κ t₀) (RelativeGroupLaw.baseChangeStr ι₀ g₀)) (hτ₀ : IsClosedImmersion τ₀.1)
    (hτ₀mul : ∀ χ χ' : WithConv (torusCoord κ t₀ →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ₀ =
        (L₀.baseChange ι₀).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ₀)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ₀))
    (abq₀ : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr ι₀ g₀) (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    (abq₀_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of κ))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      NeronModelInfra.schemeHomOverComp ((L₀.baseChange ι₀).mul s x y) (abq₀ i) =
        (Lf₀.baseChange ι₀).mul s (NeronModelInfra.schemeHomOverComp x (abq₀ i))
          (NeronModelInfra.schemeHomOverComp y (abq₀ i)))
    (abq₀_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of κ))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abq₀ i) = (Lf₀.baseChange ι₀).one s) ↔
        ∃ y : SchemeHomOver s (torusStr κ t₀), NeronModelInfra.schemeHomOverComp y τ₀ = x)
    (Ψκ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι₀ g₀))
    (hΨκ_mul : ∀ χ χ' : torusCoord κ t →ₐ[κ] κ,
      (∃ n : ℕ, (n : κ) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ (AddMonoidAlgebra.single v 1) ^ n = 1) →
      (∃ n : ℕ, (n : κ) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ' (AddMonoidAlgebra.single v 1) ^ n = 1) →
      NeronModelInfra.schemeHomOverComp ((L.baseChange ι).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (torusPt κ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt κ t χ') τ)) Ψκ =
        (L₀.baseChange ι₀).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt κ t χ) τ) Ψκ)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt κ t χ') τ) Ψκ)) :
    ∃ M₀ : (Fin t₀ → ℤ) →+ (Fin t → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) ≫ τ₀.1 = τ.1 ≫ Ψκ.1 := by

  have htors1 : ∃ n : ℕ, (n : κ) ≠ 0 ∧ ∀ v : Fin t → ℤ,
      (1 : WithConv (torusCoord κ t →ₐ[κ] κ)).ofConv (AddMonoidAlgebra.single v 1) ^ n = 1 := by
    refine ⟨1, by simp, fun v ↦ ?_⟩
    rw [pow_one]
    change (1 : WithConv (torusCoord κ t →ₐ[κ] κ)) (AddMonoidAlgebra.single v 1) = 1
    rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single]
    simp
  have hu : NeronModelInfra.schemeHomOverComp (torusPt κ t (1 : WithConv (torusCoord κ t →ₐ[κ] κ)).ofConv) τ =
      (L.baseChange ι).one (𝟙 _) := by
    apply eq_one_of_mul_self
    have h := hτmul 1 1
    rw [mul_one] at h
    exact h.symm
  have hΨκ_one : NeronModelInfra.schemeHomOverComp ((L.baseChange ι).one (𝟙 _)) Ψκ = (L₀.baseChange ι₀).one (𝟙 _) := by
    apply eq_one_of_mul_self
    have h := hΨκ_mul _ _ htors1 htors1
    rw [hu, RelativeGroupLaw.one_mul] at h
    exact h.symm
  obtain ⟨y, hy⟩ := exists_comp_torusFibre_eq ι ι₀ L L₀ Lf₀ hX₀ τ hτmul τ₀ abq₀ abq₀_mul abq₀_eq_one_iff Ψκ hΨκ_one
  obtain ⟨M₀, hM₀⟩ := exists_addMonoidHom_specMap_mapDomain_eq ι ι₀ L L₀ τ hτmul τ₀ hτ₀ hτ₀mul Ψκ
    (fun χ χ' h h' ↦ hΨκ_mul χ χ' h h') y hy
  exact ⟨M₀, by rw [← hM₀]; exact congrArg Subtype.val hy⟩

end S_NeronSpecialFibreInfra_exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul
end P2MW
export P2MW.S_NeronSpecialFibreInfra_exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul (solution)
