-- Prove2me | solution 1 for HenselianLocalRing.moduleFinite_localization_atPrime_of_quasiFiniteAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8467790c-c499-56b7-84e8-514a1b5e4da9

import Mathlib
import Theorems.Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt

set_option autoImplicit false

namespace HenselFiniteAt

open IsLocalRing

theorem exists_isIdempotentElem_notMem_iff {C : Type*} [CommRing C] [IsArtinianRing C]
    (T : Set (Ideal C)) :
    ∃ e : C, IsIdempotentElem e ∧ ∀ 𝔫 : Ideal C, 𝔫.IsMaximal → (e ∉ 𝔫 ↔ 𝔫 ∈ T) := by
  classical
  let χ : (∀ I : MaximalSpectrum C, C ⧸ I.asIdeal) := fun I => if I.asIdeal ∈ T then 1 else 0
  have hχ : IsIdempotentElem χ := by
    rw [IsIdempotentElem]
    funext I
    simp only [Pi.mul_apply, χ]
    split_ifs <;> simp
  let y : C ⧸ nilradical C := (IsArtinianRing.quotNilradicalEquivPi C).symm χ
  have hy : IsIdempotentElem y := hχ.map _
  obtain ⟨e, he, hey⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk (nilradical C))
    (fun x hx => by
      rw [Ideal.mk_ker] at hx
      exact mem_nilradical.mp hx)
    y (RingHom.mem_range.mpr (Ideal.Quotient.mk_surjective y)) hy
  refine ⟨e, he, fun 𝔫 h𝔫 => ?_⟩
  let I : MaximalSpectrum C := ⟨𝔫, h𝔫⟩
  have h1 : (IsArtinianRing.quotNilradicalEquivPi C (Ideal.Quotient.mk _ e)) I =
      Ideal.Quotient.mk 𝔫 e := rfl
  rw [hey] at h1
  have h2 : (IsArtinianRing.quotNilradicalEquivPi C) y = χ := by
    simp only [y, AlgEquiv.apply_symm_apply]
  rw [h2] at h1

  haveI : 𝔫.IsMaximal := h𝔫
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← h1]
  simp only [χ, I]
  constructor
  · intro h
    by_contra hT
    rw [if_neg hT] at h
    exact h rfl
  · intro h
    rw [if_pos h]
    exact one_ne_zero

section finiteAlg

theorem map_maximalIdeal_le_of_isMaximal {R : Type*} [CommRing R] [IsLocalRing R]
    {A : Type*} [CommRing A] [Algebra R A] [Module.Finite R A] (𝔑 : Ideal A) [𝔑.IsMaximal] :
    (maximalIdeal R).map (algebraMap R A) ≤ 𝔑 := by
  rw [Ideal.map_le_iff_le_comap]
  have : (𝔑.comap (algebraMap R A)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔑
  rw [IsLocalRing.eq_maximalIdeal this]

theorem exists_isIdempotentElem_notMem_iff_of_moduleFinite (R : Type*) [CommRing R] [HenselianLocalRing R]
    {A : Type*} [CommRing A] [Algebra R A] [Module.Finite R A] (T : Set (Ideal A)) :
    ∃ ε : A, IsIdempotentElem ε ∧ ∀ 𝔑 : Ideal A, 𝔑.IsMaximal → (ε ∉ 𝔑 ↔ 𝔑 ∈ T) := by
  set 𝔪A : Ideal A := (maximalIdeal R).map (algebraMap R A) with h𝔪A
  set κ := ResidueField R

  let j : κ →+* A ⧸ 𝔪A := Ideal.Quotient.lift (maximalIdeal R)
    ((Ideal.Quotient.mk 𝔪A).comp (algebraMap R A)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ha)
  letI : Algebra κ (A ⧸ 𝔪A) := j.toAlgebra
  haveI : IsScalarTower R κ (A ⧸ 𝔪A) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Module.Finite κ (A ⧸ 𝔪A) := Module.Finite.of_restrictScalars_finite R κ (A ⧸ 𝔪A)
  haveI : IsArtinianRing (A ⧸ 𝔪A) := IsArtinianRing.of_finite κ (A ⧸ 𝔪A)

  set Tbar : Set (Ideal (A ⧸ 𝔪A)) := {𝔫 | 𝔫.comap (Ideal.Quotient.mk 𝔪A) ∈ T} with hTbar
  obtain ⟨ē, hē, hēT⟩ := exists_isIdempotentElem_notMem_iff Tbar

  obtain ⟨ε, ⟨hε, hεē⟩, -⟩ :=
    HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite (R := R) ē hē
  refine ⟨ε, hε, fun 𝔑 h𝔑 => ?_⟩
  haveI : 𝔑.IsMaximal := h𝔑
  have hle : 𝔪A ≤ 𝔑 := map_maximalIdeal_le_of_isMaximal 𝔑
  have hsurj : Function.Surjective (Ideal.Quotient.mk 𝔪A) := Ideal.Quotient.mk_surjective

  have hcomap : (𝔑.map (Ideal.Quotient.mk 𝔪A)).comap (Ideal.Quotient.mk 𝔪A) = 𝔑 := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hle]
  have hmax : (𝔑.map (Ideal.Quotient.mk 𝔪A)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj h𝔑 with h | h
    · exfalso
      apply h𝔑.ne_top
      rw [← hcomap, h, Ideal.comap_top]
    · exact h
  have hmem : ε ∈ 𝔑 ↔ ē ∈ 𝔑.map (Ideal.Quotient.mk 𝔪A) := by
    rw [← hεē, ← Ideal.mem_comap, hcomap]
  rw [hmem, hēT _ hmax, hTbar, Set.mem_setOf_eq, hcomap]

end finiteAlg

section finiteAt

variable {R : Type*} [CommRing R] [HenselianLocalRing R]
variable {S : Type*} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

theorem exists_isIdempotentElem_moduleFinite_quotient_notMem
    (q : Ideal S) [q.IsPrime] (hq : q.comap (algebraMap R S) = maximalIdeal R) [Algebra.QuasiFiniteAt R q] :
    ∃ e : S, IsIdempotentElem e ∧ Module.Finite R (S ⧸ Ideal.span ({1 - e} : Set S)) ∧ e ∉ q := by
  classical
  obtain ⟨X, hX⟩ := Algebra.FiniteType.out (R := R) (A := S)

  obtain ⟨r, hrq, hrint, hrx⟩ :=
    Algebra.zariskisMainProperty_iff.mp (Algebra.ZariskisMainProperty.of_finiteType (R := R) q)
  choose m hm using hrx

  set G : Set S := {r} ∪ ((fun x : S => r ^ m x * x) '' (↑X : Set S)) with hG
  have hGfin : G.Finite := (Set.finite_singleton r).union (X.finite_toSet.image _)
  have hGint : ∀ g ∈ G, IsIntegral R g := by
    rintro g (rfl | ⟨x, -, rfl⟩)
    · exact hrint
    · exact hm x
  set A : Subalgebra R S := Algebra.adjoin R G with hA
  haveI hAfin : Module.Finite R A :=
    ⟨(Submodule.fg_top _).mpr (fg_adjoin_of_finite hGfin hGint)⟩
  have hrA : r ∈ A := Algebra.subset_adjoin (Or.inl rfl)
  have hrxA : ∀ x ∈ X, r ^ m x * x ∈ A := fun x hx => Algebra.subset_adjoin (Or.inr ⟨x, hx, rfl⟩)

  set TA : Set (Ideal A) := {q.comap (A.val : A →+* S)} with hTA
  obtain ⟨ε, hε, hεT⟩ := exists_isIdempotentElem_notMem_iff_of_moduleFinite R TA

  have hkey : ∀ x ∈ X, (ε : S) * x ∈ A := by
    intro x hx
    let J : Ideal A :=
      { carrier := {a : A | (a : S) * x ∈ A}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_mul]
          exact A.add_mem ha hb
        zero_mem' := by simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, zero_mul]; exact A.zero_mem
        smul_mem' := fun c {a} ha => by
          simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_assoc]
          exact A.mul_mem c.2 ha }
    have hJmem : ∀ a : A, a ∈ J ↔ (a : S) * x ∈ A := fun a => Iff.rfl
    have htop : J ⊔ Ideal.span {1 - ε} = ⊤ := by
      by_contra hne
      obtain ⟨𝔑, h𝔑, hle⟩ := Ideal.exists_le_maximal _ hne
      have h1ε : 1 - ε ∈ 𝔑 := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      have hε𝔑 : ε ∉ 𝔑 := by
        intro h
        apply h𝔑.ne_top
        rw [Ideal.eq_top_iff_one]
        have : (1 : A) = (1 - ε) + ε := by ring
        rw [this]
        exact 𝔑.add_mem h1ε h
      have h𝔑q : 𝔑 = q.comap (A.val : A →+* S) := (hεT 𝔑 h𝔑).mp hε𝔑
      have hrJ : (⟨r ^ m x, A.pow_mem hrA _⟩ : A) ∈ J := by
        rw [hJmem]
        exact hrxA x hx
      have hr𝔑 := hle (Ideal.mem_sup_left hrJ)
      rw [h𝔑q, Ideal.mem_comap] at hr𝔑
      exact hrq (Ideal.IsPrime.mem_of_pow_mem ‹q.IsPrime› _ hr𝔑)
    have h1 : (1 : A) ∈ J ⊔ Ideal.span {1 - ε} := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    have hεJ : ε ∈ J := by
      have : ε = ε * a := by
        calc ε = ε * (a + c * (1 - ε)) := by rw [hab, mul_one]
          _ = ε * a + c * (ε - ε * ε) := by ring
          _ = ε * a := by rw [hε.eq, sub_self, mul_zero, add_zero]
      rw [this]
      exact J.mul_mem_left ε ha
    exact (hJmem ε).mp hεJ

  set e : S := (ε : S) with he
  have heid : IsIdempotentElem e := by
    rw [IsIdempotentElem, he, ← Subalgebra.coe_mul, hε.eq]
  set φ : A →ₐ[R] S ⧸ Ideal.span ({1 - e} : Set S) :=
    (Ideal.Quotient.mkₐ R (Ideal.span ({1 - e} : Set S))).comp A.val with hφ
  have hφsurj : Function.Surjective φ := by
    have hrange : φ.range = ⊤ := by
      have hψ : Function.Surjective (Ideal.Quotient.mkₐ R (Ideal.span ({1 - e} : Set S))) :=
        Ideal.Quotient.mkₐ_surjective R _
      have htop' : Algebra.adjoin R
          ((Ideal.Quotient.mkₐ R (Ideal.span ({1 - e} : Set S))) '' (↑X : Set S)) = ⊤ := by
        rw [Algebra.adjoin_image, hX, Algebra.map_top, AlgHom.range_eq_top]
        exact hψ
      rw [eq_top_iff, ← htop', Algebra.adjoin_le_iff]
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨e * x, hkey x hx⟩, ?_⟩
      change φ ⟨e * x, hkey x hx⟩ = Ideal.Quotient.mkₐ R (Ideal.span ({1 - e} : Set S)) x
      rw [hφ, AlgHom.comp_apply, Subalgebra.coe_val, Ideal.Quotient.mkₐ_eq_mk]
      change Ideal.Quotient.mk (Ideal.span ({1 - e} : Set S)) (e * x) = _
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨-x, by ring⟩
    intro y
    have : y ∈ φ.range := hrange ▸ Algebra.mem_top
    exact this
  refine ⟨e, heid, Module.Finite.of_surjective φ.toLinearMap hφsurj, ?_⟩
  intro heq
  have hmax : (q.comap (A.val : A →+* S)).IsMaximal := by
    haveI : (q.comap (A.val : A →+* S)).IsPrime := Ideal.comap_isPrime _ q
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
    rw [Ideal.comap_comap]
    have : (A.val : A →+* S).comp (algebraMap R A) = algebraMap R S := A.val.comp_algebraMap
    rw [this, hq]
    exact IsLocalRing.maximalIdeal.isMaximal R
  have := (hεT _ hmax).mpr rfl
  exact this heq

theorem moduleFinite_localization
    (q : Ideal S) [q.IsPrime] (hq : q.comap (algebraMap R S) = maximalIdeal R) [Algebra.QuasiFiniteAt R q] :
    Module.Finite R (Localization.AtPrime q) := by
  classical
  obtain ⟨e, he, hfin, heq⟩ := exists_isIdempotentElem_moduleFinite_quotient_notMem (R := R) q hq
  set I : Ideal S := Ideal.span ({1 - e} : Set S) with hIdef
  set S₁ := S ⧸ I
  set π : S →+* S₁ := Ideal.Quotient.mk I with hπ
  have hπsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  have h1e : 1 - e ∈ q := by
    have h0 : e * (1 - e) ∈ q := by
      have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
      rw [this]; exact q.zero_mem
    exact (‹q.IsPrime›.mem_or_mem h0).resolve_left heq
  have hIq : I ≤ q := by
    rw [hIdef, Ideal.span_le, Set.singleton_subset_iff]; exact h1e
  have hkerπ : RingHom.ker π = I := Ideal.mk_ker

  set q₁ : Ideal S₁ := q.map π with hq₁
  haveI hq₁p : q₁.IsPrime := Ideal.map_isPrime_of_surjective hπsurj (by rw [hkerπ]; exact hIq)
  have hcomap₁ : q₁.comap π = q := by
    rw [hq₁, Ideal.comap_map_of_surjective _ hπsurj, ← RingHom.ker_eq_comap_bot, hkerπ, sup_eq_left.mpr hIq]
  haveI : Module.Finite R S₁ := hfin
  have hq₁R : q₁.comap (algebraMap R S₁) = maximalIdeal R := by
    have : algebraMap R S₁ = π.comp (algebraMap R S) := rfl
    rw [this, ← Ideal.comap_comap, hcomap₁, hq]
  haveI hq₁max : q₁.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
    rw [hq₁R]; exact IsLocalRing.maximalIdeal.isMaximal R

  obtain ⟨ε', hε', hε'T⟩ := exists_isIdempotentElem_notMem_iff_of_moduleFinite R ({q₁} : Set (Ideal S₁))
  have hε'q₁ : ε' ∉ q₁ := (hε'T q₁ hq₁max).mpr rfl
  set J : Ideal S₁ := Ideal.span ({1 - ε'} : Set S₁) with hJdef
  set S₂ := S₁ ⧸ J
  set π₂ : S₁ →+* S₂ := Ideal.Quotient.mk J with hπ₂
  have hπ₂surj : Function.Surjective π₂ := Ideal.Quotient.mk_surjective
  have h1ε' : 1 - ε' ∈ q₁ := by
    have h0 : ε' * (1 - ε') ∈ q₁ := by
      have : ε' * (1 - ε') = 0 := by rw [mul_sub, mul_one, hε'.eq, sub_self]
      rw [this]; exact q₁.zero_mem
    exact (hq₁p.mem_or_mem h0).resolve_left hε'q₁
  have hJq₁ : J ≤ q₁ := by
    rw [hJdef, Ideal.span_le, Set.singleton_subset_iff]; exact h1ε'
  have hkerπ₂ : RingHom.ker π₂ = J := Ideal.mk_ker
  haveI : Module.Finite R S₂ := inferInstance

  set q₂ : Ideal S₂ := q₁.map π₂ with hq₂
  haveI hq₂p : q₂.IsPrime := Ideal.map_isPrime_of_surjective hπ₂surj (by rw [hkerπ₂]; exact hJq₁)
  have hcomap₂ : q₂.comap π₂ = q₁ := by
    rw [hq₂, Ideal.comap_map_of_surjective _ hπ₂surj, ← RingHom.ker_eq_comap_bot, hkerπ₂, sup_eq_left.mpr hJq₁]
  have hq₂max : q₂.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
    have : algebraMap R S₂ = π₂.comp (algebraMap R S₁) := rfl
    rw [this, ← Ideal.comap_comap, hcomap₂, hq₁R]; exact IsLocalRing.maximalIdeal.isMaximal R
  have huniq : ∀ 𝔐 : Ideal S₂, 𝔐.IsMaximal → 𝔐 = q₂ := by
    intro 𝔐 h𝔐
    haveI := h𝔐
    have hmax : (𝔐.comap π₂).IsMaximal := Ideal.comap_isMaximal_of_surjective π₂ hπ₂surj
    have hε'𝔐 : ε' ∉ 𝔐.comap π₂ := by
      intro h
      have h1 : (1 : S₁) - ε' ∈ 𝔐.comap π₂ := by
        rw [Ideal.mem_comap]
        have h0 : π₂ (1 - ε') = 0 := by
          rw [← RingHom.mem_ker, hkerπ₂]; exact Ideal.subset_span rfl
        rw [h0]; exact 𝔐.zero_mem
      apply h𝔐.ne_top
      rw [Ideal.eq_top_iff_one]
      have h2 : π₂ ((1 - ε') + ε') ∈ 𝔐 := (𝔐.comap π₂).add_mem h1 h
      rwa [sub_add_cancel, map_one] at h2
    have h3 : 𝔐.comap π₂ = q₁ := (hε'T _ hmax).mp hε'𝔐
    rw [← Ideal.map_comap_of_surjective π₂ hπ₂surj 𝔐, h3]
  haveI : Nontrivial S₂ := Ideal.Quotient.nontrivial_iff.mpr (fun hJ => hq₁max.ne_top (top_le_iff.mp (hJ ▸ hJq₁)))
  haveI : IsLocalRing S₂ := IsLocalRing.of_unique_max_ideal ⟨q₂, hq₂max, huniq⟩
  have hmaxS₂ : maximalIdeal S₂ = q₂ := (huniq _ (IsLocalRing.maximalIdeal.isMaximal S₂))

  set Sq := Localization.AtPrime q
  have hunitq : ∀ s : S, s ∉ q → IsUnit (algebraMap S Sq s) := fun s hs =>
    IsLocalization.map_units Sq (⟨s, hs⟩ : q.primeCompl)
  have hI0 : ∀ s ∈ I, algebraMap S Sq s = 0 := by
    intro s hs
    rw [hIdef] at hs
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    have hu := hunitq e heq
    have h0 : algebraMap S Sq (e * (1 - e)) = 0 := by
      rw [mul_sub, mul_one, he.eq, sub_self, map_zero]
    rw [map_mul] at h0
    have h1 : algebraMap S Sq (1 - e) = 0 := (hu.mul_right_eq_zero).mp h0
    rw [map_mul, h1, mul_zero]
  let g₁ : S₁ →+* Sq := Ideal.Quotient.lift I (algebraMap S Sq) hI0
  have hg₁ : ∀ s, g₁ (π s) = algebraMap S Sq s := fun s => Ideal.Quotient.lift_mk I _ _
  have hJ0 : ∀ s ∈ J, g₁ s = 0 := by
    intro s hs
    rw [hJdef] at hs
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    obtain ⟨ε₀, hε₀⟩ := hπsurj ε'
    have hε₀q : ε₀ ∉ q := by
      intro h
      apply hε'q₁
      rw [← hε₀, hq₁]; exact Ideal.mem_map_of_mem _ h
    have hu : IsUnit (g₁ ε') := by rw [← hε₀, hg₁]; exact hunitq ε₀ hε₀q
    have h0 : g₁ (ε' * (1 - ε')) = 0 := by rw [mul_sub, mul_one, hε'.eq, sub_self, map_zero]
    rw [map_mul] at h0
    have h1 : g₁ (1 - ε') = 0 := (hu.mul_right_eq_zero).mp h0
    rw [map_mul, h1, mul_zero]
  let g₂ : S₂ →+* Sq := Ideal.Quotient.lift J g₁ hJ0
  have hg₂ : ∀ s, g₂ (π₂ (π s)) = algebraMap S Sq s := fun s => by
    change Ideal.Quotient.lift J g₁ hJ0 (Ideal.Quotient.mk J (π s)) = _
    rw [Ideal.Quotient.lift_mk, hg₁]

  have hunit₂ : ∀ s : S, s ∉ q → IsUnit (π₂ (π s)) := by
    intro s hs
    by_contra hns
    have hmem : π₂ (π s) ∈ maximalIdeal S₂ := (IsLocalRing.mem_maximalIdeal _).mpr hns
    rw [hmaxS₂, ← Ideal.mem_comap, hcomap₂, ← Ideal.mem_comap, hcomap₁] at hmem
    exact hs hmem
  have hg₂surj : Function.Surjective g₂ := by
    intro z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨u, hu⟩ := hunit₂ s s.2
    refine ⟨π₂ (π a) * ↑u⁻¹, ?_⟩
    have hus : g₂ (u : S₂) = algebraMap S Sq s := by rw [hu, hg₂]
    have hmul : g₂ (↑u⁻¹ : S₂) * algebraMap S Sq s = 1 := by
      rw [← hus, ← map_mul, Units.inv_mul, map_one]
    rw [map_mul, hg₂]
    apply (IsLocalization.map_units Sq s).mul_left_injective

    change algebraMap S Sq a * g₂ ↑u⁻¹ * algebraMap S Sq s = IsLocalization.mk' Sq a s * algebraMap S Sq s
    rw [mul_assoc, hmul, mul_one, IsLocalization.mk'_spec]

  let g₂ₗ : S₂ →ₗ[R] Sq :=
    { toFun := g₂
      map_add' := fun x y => map_add g₂ x y
      map_smul' := fun c y => by
        obtain ⟨y, rfl⟩ := hπ₂surj y
        obtain ⟨x, rfl⟩ := hπsurj y
        have h1 : c • π₂ (π x) = π₂ (π (c • x)) := rfl
        rw [RingHom.id_apply, h1, hg₂, hg₂, Algebra.smul_def c x, map_mul,
          Algebra.smul_def c (algebraMap S Sq x), IsScalarTower.algebraMap_apply R S Sq c] }
  exact Module.Finite.of_surjective g₂ₗ hg₂surj

end finiteAt

end HenselFiniteAt

universe u v

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] (hq : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    [Algebra.QuasiFiniteAt R q] :
    Module.Finite R (Localization.AtPrime q) :=
  HenselFiniteAt.moduleFinite_localization q hq

end S_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt
end P2MW
export P2MW.S_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt (solution)
