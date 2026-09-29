-- Prove2me | solution 1 for HenselianLocalRing.exists_isIdempotentElem_moduleFinite_quotient_of_quasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4896d284-4296-5805-ad87-a76797976c71

import Mathlib
import Theorems.Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_exists_isIdempotentElem_moduleFinite_quotient_of_quasiFinite

set_option autoImplicit false

namespace FinitePart

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

section finitePart

variable {R : Type*} [CommRing R] [HenselianLocalRing R]
variable {S : Type*} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]

theorem exists_finitePart :
    ∃ e : S, IsIdempotentElem e ∧
      Module.Finite R (S ⧸ Ideal.span ({1 - e} : Set S)) ∧
      ∀ 𝔮 : Ideal S, 𝔮.IsPrime → 𝔮.comap (algebraMap R S) = maximalIdeal R → e ∉ 𝔮 := by
  classical

  set T : Set (Ideal S) := (maximalIdeal R).primesOver S with hT
  have hTfin : T.Finite := Algebra.QuasiFinite.finite_primesOver (maximalIdeal R)
  have hTmem : ∀ 𝔮 : Ideal S, 𝔮 ∈ T ↔ 𝔮.IsPrime ∧ 𝔮.comap (algebraMap R S) = maximalIdeal R := by
    intro 𝔮
    rw [hT, Ideal.primesOver, Set.mem_setOf_eq, Ideal.liesOver_iff, Ideal.under_def, eq_comm]

  obtain ⟨X, hX⟩ := Algebra.FiniteType.out (R := R) (A := S)

  have hZMT : ∀ 𝔮 ∈ T, ∃ r ∉ 𝔮, IsIntegral R r ∧ ∀ x : S, ∃ m : ℕ, IsIntegral R (r ^ m * x) := by
    intro 𝔮 h𝔮
    haveI : 𝔮.IsPrime := ((hTmem 𝔮).mp h𝔮).1
    exact Algebra.zariskisMainProperty_iff.mp (Algebra.ZariskisMainProperty.of_finiteType 𝔮)
  choose! r hr𝔮 hrint hrx using hZMT
  choose! m hm using hrx

  set G : Set S := (r '' T) ∪ ((fun p : Ideal S × S => r p.1 ^ m p.1 p.2 * p.2) '' (T ×ˢ (↑X : Set S)))
    with hG
  have hGfin : G.Finite :=
    (hTfin.image r).union ((hTfin.prod X.finite_toSet).image _)
  have hGint : ∀ g ∈ G, IsIntegral R g := by
    rintro g (⟨𝔮, h𝔮, rfl⟩ | ⟨⟨𝔮, x⟩, ⟨h𝔮, -⟩, rfl⟩)
    · exact hrint 𝔮 h𝔮
    · exact hm 𝔮 h𝔮 x
  set A : Subalgebra R S := Algebra.adjoin R G with hA
  haveI hAfin : Module.Finite R A :=
    ⟨(Submodule.fg_top _).mpr (fg_adjoin_of_finite hGfin hGint)⟩
  have hrA : ∀ 𝔮 ∈ T, r 𝔮 ∈ A := fun 𝔮 h𝔮 =>
    Algebra.subset_adjoin (Or.inl ⟨𝔮, h𝔮, rfl⟩)
  have hrxA : ∀ 𝔮 ∈ T, ∀ x ∈ X, r 𝔮 ^ m 𝔮 x * x ∈ A := fun 𝔮 h𝔮 x hx =>
    Algebra.subset_adjoin (Or.inr ⟨⟨𝔮, x⟩, ⟨h𝔮, hx⟩, rfl⟩)

  set TA : Set (Ideal A) := (fun 𝔮 : Ideal S => 𝔮.comap (A.val : A →+* S)) '' T with hTA
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
      obtain ⟨𝔮, h𝔮T, rfl⟩ := (hεT 𝔑 h𝔑).mp hε𝔑

      have hrJ : (⟨r 𝔮 ^ m 𝔮 x, A.pow_mem (hrA 𝔮 h𝔮T) _⟩ : A) ∈ J := by
        rw [hJmem]
        exact hrxA 𝔮 h𝔮T x hx
      have hr𝔑 := hle (Ideal.mem_sup_left hrJ)
      rw [Ideal.mem_comap] at hr𝔑
      haveI : 𝔮.IsPrime := ((hTmem 𝔮).mp h𝔮T).1
      exact hr𝔮 𝔮 h𝔮T (Ideal.IsPrime.mem_of_pow_mem ‹𝔮.IsPrime› _ hr𝔑)
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
  intro 𝔮 h𝔮 h𝔮m he𝔮
  have h𝔮T : 𝔮 ∈ T := (hTmem 𝔮).mpr ⟨h𝔮, h𝔮m⟩
  have hmax : (𝔮.comap (A.val : A →+* S)).IsMaximal := by
    haveI : (𝔮.comap (A.val : A →+* S)).IsPrime := Ideal.comap_isPrime _ 𝔮
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
    rw [Ideal.comap_comap]
    have : (A.val : A →+* S).comp (algebraMap R A) = algebraMap R S := A.val.comp_algebraMap
    rw [this, h𝔮m]
    exact IsLocalRing.maximalIdeal.isMaximal R
  have := (hεT _ hmax).mpr ⟨𝔮, h𝔮T, rfl⟩
  exact this he𝔮

end finitePart

end FinitePart

universe u v

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] :
    ∃ e : S, IsIdempotentElem e ∧
      Module.Finite R (S ⧸ Ideal.span ({1 - e} : Set S)) ∧
      ∀ 𝔮 : Ideal S, 𝔮.IsPrime → 𝔮.comap (algebraMap R S) = IsLocalRing.maximalIdeal R → e ∉ 𝔮 :=
  FinitePart.exists_finitePart

end S_HenselianLocalRing_exists_isIdempotentElem_moduleFinite_quotient_of_quasiFinite
end P2MW
export P2MW.S_HenselianLocalRing_exists_isIdempotentElem_moduleFinite_quotient_of_quasiFinite (solution)
