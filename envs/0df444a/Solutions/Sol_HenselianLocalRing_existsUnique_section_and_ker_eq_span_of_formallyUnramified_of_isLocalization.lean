-- Prove2me | solution 1 for HenselianLocalRing.existsUnique_section_and_ker_eq_span_of_formallyUnramified_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5d3df848-485d-503e-8c38-2f57de5ce5a7

import Mathlib
import Theorems.Thm_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallyUnramified_of_isLocalization

set_option autoImplicit false

open IsLocalRing Polynomial

universe u

namespace HenselSectionsFP

variable {A : Type u} [CommRing A]
variable {S : Type u} [CommRing S] [Algebra A[X] S]

theorem algebraMap_A [Algebra A S] [IsScalarTower A A[X] S] (a : A) :
    algebraMap A S a = algebraMap A[X] S (C a) := by
  rw [IsScalarTower.algebraMap_apply A A[X] S, ← Polynomial.C_eq_algebraMap]

theorem mk_algebraMap_eq [Algebra A S] [IsScalarTower A A[X] S] (J₀ : Ideal S) (c : A)
    (hJ₀ : algebraMap A[X] S X - algebraMap A[X] S (C c) ∈ J₀) (p : A[X]) :
    (Ideal.Quotient.mk J₀ (algebraMap A[X] S p))
      = algebraMap A (S ⧸ J₀) (p.eval c) := by
  rw [IsScalarTower.algebraMap_apply A S (S ⧸ _) (p.eval c), Ideal.Quotient.algebraMap_eq,
    algebraMap_A (A := A) (S := S) (p.eval c), Ideal.Quotient.eq, ← map_sub]
  obtain ⟨q, hq⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := p) (a := c)
  rw [hq, map_mul]
  exact Ideal.mul_mem_right _ _ (by rw [map_sub]; exact hJ₀)

section KerFG

variable [Algebra A S] [IsScalarTower A A[X] S]
variable {P : Type u} [CommRing P] [Algebra A P] [Algebra.FinitePresentation A P] (M : Submonoid P)
variable [Algebra P S] [IsLocalization M S] [IsScalarTower A P S]

include M in
omit [Algebra A[X] S] [IsScalarTower A A[X] S] in

theorem ker_fg (χ : S →+* A) (hC : ∀ a, χ (algebraMap A S a) = a) : (RingHom.ker χ).FG := by
  classical
  let χP : P →ₐ[A] A :=
    { χ.comp (algebraMap P S) with
      commutes' := fun a => by
        change χ (algebraMap P S (algebraMap A P a)) = a
        rw [← IsScalarTower.algebraMap_apply]; exact hC a }
  have hχP : ∀ p, χP p = χ (algebraMap P S p) := fun _ => rfl
  have hsurj : Function.Surjective χP := fun a => ⟨algebraMap A P a, χP.commutes a⟩
  have hfg : (RingHom.ker χP.toRingHom).FG := Algebra.FinitePresentation.ker_fG_of_surjective χP hsurj
  have heq : RingHom.ker χ = (RingHom.ker χP.toRingHom).map (algebraMap P S) := by
    apply le_antisymm
    · intro s hs
      obtain ⟨p, m, rfl⟩ := IsLocalization.exists_mk'_eq M s
      have hu : IsUnit (algebraMap P S m) := IsLocalization.map_units S m
      have hp : p ∈ RingHom.ker χP.toRingHom := by
        rw [RingHom.mem_ker]
        change χP p = 0
        rw [hχP, ← IsLocalization.mk'_spec S p m, map_mul]
        rw [RingHom.mem_ker] at hs
        rw [hs, zero_mul]
      have h1 : IsLocalization.mk' S p m = algebraMap P S p * ↑(hu.unit⁻¹) := by
        rw [← IsLocalization.mk'_spec S p m, mul_assoc]
        rw [IsUnit.mul_val_inv, mul_one]
      rw [h1]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp)
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hχP]
      exact hp
  rw [heq]
  obtain ⟨T, hT⟩ := hfg
  refine ⟨T.image (algebraMap P S), ?_⟩
  rw [Finset.coe_image, ← Ideal.map_span, hT]

end KerFG

theorem ker_eq_span [IsLocalRing A] [IsLocalRing S]
    [Algebra A S] [IsScalarTower A A[X] S] [Algebra.FormallyUnramified A[X] S]
    (χ : S →+* A) (hC : ∀ a, χ (algebraMap A[X] S (C a)) = a) (hfg : (RingHom.ker χ).FG) :
    RingHom.ker χ =
      Ideal.span {algebraMap A[X] S X - algebraMap A[X] S (C (χ (algebraMap A[X] S X)))} := by
  set c := χ (algebraMap A[X] S X) with hcdef
  set J₀ : Ideal S := Ideal.span {algebraMap A[X] S X - algebraMap A[X] S (C c)} with hJ₀def
  have hJ₀mem : algebraMap A[X] S X - algebraMap A[X] S (C c) ∈ J₀ := Ideal.subset_span rfl
  have hJ₀χ : ∀ s ∈ J₀, χ s = 0 := by
    intro s hs
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    rw [map_mul, map_sub, hC, ← hcdef, sub_self, mul_zero]
  refine le_antisymm ?_ (fun s hs => (RingHom.mem_ker).mpr (hJ₀χ s hs))
  intro s hs
  rw [RingHom.mem_ker] at hs

  let B := S ⧸ J₀
  let χb : B →+* A := Ideal.Quotient.lift J₀ χ hJ₀χ
  have hχbA : ∀ a : A, χb (algebraMap A B a) = a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A S B, Ideal.Quotient.algebraMap_eq,
      algebraMap_A (A := A) (S := S) a]
    change Ideal.Quotient.lift J₀ χ hJ₀χ (Ideal.Quotient.mk J₀ _) = a
    rw [Ideal.Quotient.lift_mk]
    exact hC a
  have hpoly : ∀ p : A[X], (Ideal.Quotient.mk J₀ (algebraMap A[X] S p) : B) = algebraMap A B (p.eval c) :=
    fun p => mk_algebraMap_eq J₀ c hJ₀mem p
  set J : Ideal B := RingHom.ker χb with hJdef

  have hJJ : J ≤ J ^ 2 := by
    intro b hb
    let I : Ideal (B ⧸ J ^ 2) := J.map (Ideal.Quotient.mk (J ^ 2))
    have hI : IsNilpotent I := by
      refine ⟨2, ?_⟩
      rw [Submodule.zero_eq_bot]
      change (J.map (Ideal.Quotient.mk (J ^ 2))) ^ 2 = ⊥
      rw [← Ideal.map_pow, Ideal.map_quotient_self]
    let g₁ : B →ₐ[A[X]] B ⧸ J ^ 2 := Ideal.Quotient.mkₐ A[X] (J ^ 2)
    let g₂' : B →+* B ⧸ J ^ 2 := (Ideal.Quotient.mk (J ^ 2)).comp ((algebraMap A B).comp χb)
    let g₂ : B →ₐ[A[X]] B ⧸ J ^ 2 :=
      { g₂' with
        commutes' := by
          intro p
          change Ideal.Quotient.mk (J ^ 2) (algebraMap A B (χb (algebraMap A[X] B p)))
            = Ideal.Quotient.mk (J ^ 2) (algebraMap A[X] B p)
          rw [IsScalarTower.algebraMap_apply A[X] S B p, Ideal.Quotient.algebraMap_eq J₀]
          change Ideal.Quotient.mk (J ^ 2) (algebraMap A B (χb (Ideal.Quotient.mk J₀ (algebraMap A[X] S p))))
            = Ideal.Quotient.mk (J ^ 2) (Ideal.Quotient.mk J₀ (algebraMap A[X] S p))
          rw [hpoly, hχbA] }
    have H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x) := by
      intro x
      rw [Ideal.Quotient.eq]
      change Ideal.Quotient.mk (J ^ 2) x - Ideal.Quotient.mk (J ^ 2) (algebraMap A B (χb x)) ∈ I
      rw [← map_sub]
      refine Ideal.mem_map_of_mem _ ?_
      rw [hJdef, RingHom.mem_ker, map_sub, hχbA, sub_self]
    have hg : g₁ = g₂ := Algebra.FormallyUnramified.ext I hI H
    have hgb : g₁ b = g₂ b := by rw [hg]
    have hb0 : χb b = 0 := hb
    have h0 : Ideal.Quotient.mk (J ^ 2) b = 0 := by
      change Ideal.Quotient.mk (J ^ 2) b = Ideal.Quotient.mk (J ^ 2) (algebraMap A B (χb b)) at hgb
      rw [hgb, hb0, map_zero, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0

  have hJfg : J.FG := by
    classical
    have hJeq : J = (RingHom.ker χ).map (Ideal.Quotient.mk J₀) := by
      apply le_antisymm
      · intro b hb
        obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective b
        have hs' : s' ∈ RingHom.ker χ := by
          rw [RingHom.mem_ker]
          have : χb (Ideal.Quotient.mk J₀ s') = 0 := hb
          rwa [Ideal.Quotient.lift_mk] at this
        exact Ideal.mem_map_of_mem _ hs'
      · rw [Ideal.map_le_iff_le_comap]
        intro s' hs'
        rw [Ideal.mem_comap, hJdef, RingHom.mem_ker]
        change Ideal.Quotient.lift J₀ χ hJ₀χ (Ideal.Quotient.mk J₀ s') = 0
        rw [Ideal.Quotient.lift_mk]
        exact hs'
    rw [hJeq]
    obtain ⟨T, hT⟩ := hfg
    refine ⟨T.image (Ideal.Quotient.mk J₀), ?_⟩
    rw [Finset.coe_image, ← Ideal.map_span, hT]

  have hJtop : J ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ J := h ▸ Submodule.mem_top
    rw [hJdef, RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial B := nontrivial_of_ne 1 0 fun h10 =>
    hJtop ((Ideal.eq_top_iff_one J).mpr (h10 ▸ J.zero_mem))
  haveI : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J₀) Ideal.Quotient.mk_surjective
  have hJjac : J ≤ (⊥ : Ideal B).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hJtop
  have hJbot : J = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J J hJfg
      (by rw [Ideal.smul_eq_mul, ← pow_two]; exact hJJ) hJjac

  have hsJ : (Ideal.Quotient.mk J₀ s : B) ∈ J := by
    rw [hJdef, RingHom.mem_ker]
    change Ideal.Quotient.lift J₀ χ hJ₀χ (Ideal.Quotient.mk J₀ s) = 0
    rw [Ideal.Quotient.lift_mk]
    exact hs
  rw [hJbot, Ideal.mem_bot] at hsJ
  exact Ideal.Quotient.eq_zero_iff_mem.mp hsJ

theorem section_unique [IsLocalRing A] [IsLocalRing S]
    [Algebra A S] [IsScalarTower A A[X] S] [Algebra.FormallyUnramified A[X] S]
    (χ₁ χ₂ : S →+* A) (hC₁ : ∀ a, χ₁ (algebraMap A[X] S (C a)) = a)
    (hfg₁ : (RingHom.ker χ₁).FG)
    (hC₂ : ∀ a, χ₂ (algebraMap A[X] S (C a)) = a)
    (h : χ₁ (algebraMap A[X] S X) = χ₂ (algebraMap A[X] S X)) : χ₁ = χ₂ := by
  have hker := ker_eq_span χ₁ hC₁ hfg₁
  refine RingHom.ext fun s => ?_
  have hs : s - algebraMap A[X] S (C (χ₁ s)) ∈ RingHom.ker χ₁ := by
    rw [RingHom.mem_ker, map_sub, hC₁, sub_self]
  rw [hker] at hs
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hs
  have h2 : χ₂ (s - algebraMap A[X] S (C (χ₁ s))) = 0 := by
    rw [← hr, map_mul, map_sub, ← h, hC₂, sub_self, mul_zero]
  rw [map_sub, hC₂, sub_eq_zero] at h2
  exact h2.symm

theorem exists_section [HenselianLocalRing A] [IsLocalRing S]
    [Algebra A S] [IsScalarTower A A[X] S] [Algebra.FormallySmooth A[X] S]
    {P : Type u} [CommRing P] [Algebra A P] [Algebra.FinitePresentation A P] (M : Submonoid P)
    [Algebra P S] [IsLocalization M S] [IsScalarTower A P S]
    (χ₀ : S →+* ResidueField A)
    (hχ₀C : ∀ a : A, χ₀ (algebraMap A[X] S (C a)) = IsLocalRing.residue A a)
    (hχ₀t : χ₀ (algebraMap A[X] S X) = 0)
    (c : A) (hc : IsLocalRing.residue A c = 0) :
    ∃ χ : S →+* A, (∀ a : A, χ (algebraMap A[X] S (C a)) = a) ∧
      (∀ f : S, IsLocalRing.residue A (χ f) = χ₀ f) ∧ χ (algebraMap A[X] S X) = c := by
  set t := algebraMap A[X] S X with htdef

  obtain ⟨⟨p₀, m₀⟩, hpm⟩ := IsLocalization.surj M (t - algebraMap A[X] S (C c))
  simp only at hpm
  set I : Ideal P := Ideal.span {p₀} with hIdef
  set J₀ : Ideal S := I.map (algebraMap P S) with hJ₀def
  have hum₀ : IsUnit (algebraMap P S m₀) := IsLocalization.map_units S m₀
  have hJ₀eq : J₀ = Ideal.span {t - algebraMap A[X] S (C c)} := by
    rw [hJ₀def, hIdef, Ideal.map_span, Set.image_singleton, ← hpm]
    exact Ideal.span_singleton_mul_right_unit hum₀ _
  have hJ₀mem : t - algebraMap A[X] S (C c) ∈ J₀ := by rw [hJ₀eq]; exact Ideal.subset_span rfl
  have hχ₀A : ∀ a, χ₀ (algebraMap A S a) = residue A a := fun a => by
    rw [algebraMap_A (A := A) (S := S) a]; exact hχ₀C a
  have hJ₀χ₀ : ∀ s ∈ J₀, χ₀ s = 0 := by
    intro s hs
    rw [hJ₀eq] at hs
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    rw [map_mul, map_sub, hχ₀t, hχ₀C, hc, sub_self, mul_zero]
  let B := S ⧸ J₀
  have hJ₀top : J₀ ≠ ⊤ := by
    intro h
    have h1 : (1 : S) ∈ J₀ := h ▸ Submodule.mem_top
    have := hJ₀χ₀ 1 h1
    rw [map_one] at this
    exact one_ne_zero this
  haveI : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hJ₀top
  haveI : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J₀) Ideal.Quotient.mk_surjective

  let χb₀ : B →+* ResidueField A := Ideal.Quotient.lift J₀ χ₀ hJ₀χ₀
  have hχb₀ : ∀ s, χb₀ (Ideal.Quotient.mk J₀ s) = χ₀ s := fun s => Ideal.Quotient.lift_mk _ _ _
  let φB : B →ₐ[A] ResidueField A :=
    { χb₀ with
      commutes' := fun a => by
        change χb₀ (algebraMap A B a) = algebraMap A (ResidueField A) a
        rw [IsScalarTower.algebraMap_apply A S B, Ideal.Quotient.algebraMap_eq]
        change χb₀ (Ideal.Quotient.mk J₀ (algebraMap A S a)) = _
        rw [hχb₀, hχ₀A]
        rfl }
  have hφB : ∀ s, φB (Ideal.Quotient.mk J₀ s) = χ₀ s := hχb₀
  have hφBsurj : Function.Surjective φB := fun x => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨algebraMap A B a, φB.commutes a⟩
  have hkerB : RingHom.ker φB = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φB hφBsurj)
  have hunitB : ∀ b : B, IsUnit b ↔ φB b ≠ 0 := by
    intro b
    rw [Ne, ← RingHom.mem_ker, hkerB, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hpoly : ∀ p : A[X], (Ideal.Quotient.mk J₀ (algebraMap A[X] S p) : B) = algebraMap A B (p.eval c) :=
    fun p => mk_algebraMap_eq J₀ c hJ₀mem p

  haveI : Algebra.FormallySmooth A B := by
    refine Algebra.FormallySmooth.of_comp_surjective ?_
    intro T _ _ I' hI g
    letI algXT : Algebra A[X] T := ((algebraMap A T).comp (evalRingHom c)).toAlgebra
    haveI : IsScalarTower A A[X] T := IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap A T a = algebraMap A T (eval c (algebraMap A A[X] a))
      rw [← C_eq_algebraMap, eval_C]
    let g' : S →ₐ[A[X]] T ⧸ I' :=
      { g.toRingHom.comp (Ideal.Quotient.mk J₀) with
        commutes' := fun p => by
          change g (Ideal.Quotient.mk J₀ (algebraMap A[X] S p))
            = Ideal.Quotient.mk I' (algebraMap A T (p.eval c))
          rw [hpoly, g.commutes]
          rfl }
    have hg' : ∀ s, g' s = g (Ideal.Quotient.mk J₀ s) := fun s => rfl
    obtain ⟨l, hl⟩ := Algebra.FormallySmooth.exists_lift I' ⟨2, by rw [hI, Submodule.zero_eq_bot]⟩ g'
    have hl0 : l (t - algebraMap A[X] S (C c)) = 0 := by
      rw [map_sub, htdef, l.commutes, l.commutes]
      change algebraMap A T (eval c X) - algebraMap A T (eval c (C c)) = 0
      rw [eval_X, eval_C, sub_self]
    have hlJ₀ : ∀ s ∈ J₀, l s = 0 := fun s hs => by
      rw [hJ₀eq] at hs
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      rw [map_mul, hl0, mul_zero]
    let f : B →ₐ[A] T := Ideal.Quotient.liftₐ J₀ (l.restrictScalars A) hlJ₀
    refine ⟨f, ?_⟩
    apply Ideal.Quotient.algHom_ext
    refine AlgHom.ext fun s => ?_
    change Ideal.Quotient.mk I' (f (Ideal.Quotient.mk J₀ s)) = g (Ideal.Quotient.mk J₀ s)
    have h1 : f (Ideal.Quotient.mk J₀ s) = l s := Ideal.Quotient.lift_mk J₀ _ _
    rw [h1, ← hg']
    exact AlgHom.congr_fun hl s

  let P' := P ⧸ I
  haveI : Algebra.FinitePresentation A P' :=
    Algebra.FinitePresentation.quotient ⟨{p₀}, by rw [hIdef, Finset.coe_singleton]⟩
  let M' : Submonoid P' := Algebra.algebraMapSubmonoid P' M
  haveI : IsLocalization M' B := inferInstance
  haveI : IsScalarTower A P' B := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A B a = algebraMap P' B (Ideal.Quotient.mk I (algebraMap A P a))
    rw [IsScalarTower.algebraMap_apply A S B, Ideal.Quotient.algebraMap_eq,
      IsScalarTower.algebraMap_apply A P S]
    rfl
  let φ' : P' →ₐ[A] ResidueField A := φB.comp (IsScalarTower.toAlgHom A P' B)
  have hφ' : ∀ x : P', φ' x = φB (algebraMap P' B x) := fun x => rfl
  haveI hprime : (RingHom.ker φ').IsPrime := RingHom.ker_isPrime _
  have hunit' : ∀ x : P', x ∈ (RingHom.ker φ').primeCompl ↔ IsUnit (algebraMap P' B x) := fun x => by
    rw [Ideal.mem_primeCompl_iff, RingHom.mem_ker, hunitB, hφ']
  have hM'le : M' ≤ (RingHom.ker φ').primeCompl := by
    intro x hx
    rw [hunit']
    exact IsLocalization.map_units B ⟨x, hx⟩
  haveI : IsLocalization (RingHom.ker φ').primeCompl B :=
    IsLocalization.of_le M' _ hM'le (fun x hx => (hunit' x).mp hx)
  haveI : Algebra.IsSmoothAt A (RingHom.ker φ') := by
    let e : Localization.AtPrime (RingHom.ker φ') ≃ₐ[P'] B :=
      IsLocalization.algEquiv (RingHom.ker φ').primeCompl _ _
    exact Algebra.FormallySmooth.of_equiv (e.restrictScalars A).symm

  obtain ⟨ψ', hψ'⟩ := HenselianLocalRing.exists_algHom_lift_of_isSmoothAt P' φ'
  have hψ'res : ∀ x : P', residue A (ψ' x) = φ' x := hψ'

  have hunit : ∀ y : (RingHom.ker φ').primeCompl, IsUnit (ψ'.toRingHom y) := by
    intro y
    have h1 : φ' y ≠ 0 := fun h0 => (Ideal.mem_primeCompl_iff.mp y.2) h0
    by_contra hnu
    have hmem : ψ' y ∈ maximalIdeal A := hnu
    rw [← IsLocalRing.residue_eq_zero_iff, hψ'res] at hmem
    exact h1 hmem
  let ψB : B →+* A := IsLocalization.lift (M := (RingHom.ker φ').primeCompl) hunit
  have hψB_P' : ∀ x : P', ψB (algebraMap P' B x) = ψ' x := fun x => IsLocalization.lift_eq hunit x
  have hψB_A : ∀ a : A, ψB (algebraMap A B a) = a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A P' B, hψB_P', ψ'.commutes]
    rfl
  have hψB_res : ∀ b : B, residue A (ψB b) = φB b := by
    intro b
    obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq (RingHom.ker φ').primeCompl b
    have hspec := IsLocalization.mk'_spec B x y
    have hy0 : φ' y ≠ 0 := fun h0 => (Ideal.mem_primeCompl_iff.mp y.2) h0
    have h1 : ψB (IsLocalization.mk' B x y) * ψ' y = ψ' x := by
      rw [← hψB_P', ← hψB_P', ← map_mul]
      exact congrArg ψB hspec
    have h2 : φB (IsLocalization.mk' B x y) * φ' y = φ' x := by
      rw [hφ', hφ', ← map_mul]
      exact congrArg φB hspec
    apply mul_right_cancel₀ hy0
    rw [h2, ← hψ'res, ← hψ'res, ← map_mul, h1]

  refine ⟨ψB.comp (Ideal.Quotient.mk J₀), fun a => ?_, fun f => ?_, ?_⟩
  · change ψB (Ideal.Quotient.mk J₀ (algebraMap A[X] S (C a))) = a
    rw [← algebraMap_A (A := A) (S := S) a, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply]
    exact hψB_A a
  · change residue A (ψB (Ideal.Quotient.mk J₀ f)) = χ₀ f
    rw [hψB_res, hφB]
  · change ψB (Ideal.Quotient.mk J₀ (algebraMap A[X] S X)) = c
    rw [hpoly X, hψB_A, eval_X]

end HenselSectionsFP

theorem solution
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {S : Type u} [CommRing S] [IsLocalRing S]
    (φ : Polynomial A →+* S) (hφs : φ.FormallySmooth) (hφu : φ.FormallyUnramified)
    (P : Type u) [CommRing P] [Algebra A P] [Algebra.FinitePresentation A P] (M : Submonoid P)
    [Algebra P S] [IsLocalization M S]
    (hPS : ∀ a : A, algebraMap P S (algebraMap A P a) = φ (Polynomial.C a))
    (χ₀ : S →+* ResidueField A) (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
    (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a) (hχ₀t : χ₀ (φ Polynomial.X) = 0) :
    (∀ c : A, IsLocalRing.residue A c = 0 →
      ∃! χ : S →+* A, (∀ a : A, χ (φ (Polynomial.C a)) = a) ∧
        (∀ f : S, IsLocalRing.residue A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
    (∀ χ : S →+* A, (∀ a : A, χ (φ (Polynomial.C a)) = a) → (∀ f : S, IsLocalRing.residue A (χ f) = χ₀ f) →
      RingHom.ker χ = Ideal.span {φ Polynomial.X - φ (Polynomial.C (χ (φ Polynomial.X)))}) := by
  letI : Algebra A[X] S := φ.toAlgebra
  letI : Algebra A S := (φ.comp (algebraMap A A[X])).toAlgebra
  haveI : IsScalarTower A A[X] S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A P S := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hPS]; change φ (C a) = φ (algebraMap A A[X] a); rw [C_eq_algebraMap]
  haveI : Algebra.FormallySmooth A[X] S := hφs
  haveI : Algebra.FormallyUnramified A[X] S := hφu
  have hCφ : ∀ (χ : S →+* A), (∀ a : A, χ (φ (Polynomial.C a)) = a) →
      ∀ a, χ (algebraMap A S a) = a := fun χ hC a => by
    change χ (φ (algebraMap A A[X] a)) = a
    rw [← C_eq_algebraMap]; exact hC a
  have hfg : ∀ (χ : S →+* A), (∀ a : A, χ (φ (Polynomial.C a)) = a) → (RingHom.ker χ).FG :=
    fun χ hC => HenselSectionsFP.ker_fg (A := A) (S := S) M χ (hCφ χ hC)
  refine ⟨fun c hc => ?_, fun χ hC _ => HenselSectionsFP.ker_eq_span χ hC (hfg χ hC)⟩
  obtain ⟨χ, hC, hres, hct⟩ :=
    HenselSectionsFP.exists_section (A := A) (S := S) M χ₀ hχ₀C hχ₀t c hc
  refine ⟨χ, ⟨hC, hres, hct⟩, fun χ' hχ' => ?_⟩
  exact HenselSectionsFP.section_unique χ' χ hχ'.1 (hfg χ' hχ'.1) hC (hχ'.2.2.trans hct.symm)

end S_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallyUnramified_of_isLocalization
end P2MW
export P2MW.S_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallyUnramified_of_isLocalization (solution)
