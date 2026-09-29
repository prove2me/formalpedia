-- Prove2me | solution 1 for Ideal.exists_ne_zero_and_forall_isMaximal_radical_map_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/779204ae-1fed-57fa-b492-19646a694fbe

import Mathlib
import Theorems.Thm_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
import Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Theorems.Thm_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent
import Theorems.Thm_Algebra_exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime

set_option autoImplicit false

universe u v w

namespace P2mGenIrredAff

open Ideal

theorem nilradical_isPrime_of_radicial {A D : Type*} [CommRing A] [Nontrivial A] [CommRing D] [IsDomain D]
    (j : D →+* A) (hj : Function.Injective j) (g : A)
    (hg : ∀ Q ∈ minimalPrimes A, g ∉ Q)
    (hrad : ∀ a : A, ∃ m M : ℕ, 0 < M ∧ (g ^ m * a) ^ M ∈ j.range) :
    (nilradical A).IsPrime := by

  have hmem : ∀ a : A, (∀ Q ∈ minimalPrimes A, a ∈ Q) → a ∈ nilradical A := by
    intro a ha
    rw [nilradical, Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hP0, hP⟩
    haveI := hP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hP0
    exact hQP (ha Q hQ)

  have hnil : ∀ (a : A) (m M : ℕ), 0 < M → (g ^ m * a) ^ M = 0 → a ∈ nilradical A := by
    intro a m M hM h0
    apply hmem
    intro Q hQ
    haveI : Q.IsPrime := hQ.1.1
    have h1 : g ^ m * a ∈ Q := Ideal.IsPrime.mem_of_pow_mem inferInstance M (by rw [h0]; exact zero_mem Q)
    rcases Ideal.IsPrime.mem_or_mem inferInstance h1 with h | h
    · exact absurd (Ideal.IsPrime.mem_of_pow_mem inferInstance m h) (hg Q hQ)
    · exact h
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : A) ∈ nilradical A := htop ▸ Submodule.mem_top
    rw [mem_nilradical] at h1
    obtain ⟨N, hN⟩ := h1
    rw [one_pow] at hN
    exact one_ne_zero hN
  · intro a b hab
    rw [mem_nilradical] at hab
    obtain ⟨N, hN⟩ := hab
    obtain ⟨m, M, hM, α, hα⟩ := hrad a
    obtain ⟨m', M', hM', β, hβ⟩ := hrad b

    have h1 : j ((α ^ M' * β ^ M) ^ N) = 0 := by
      rw [map_pow, map_mul, map_pow, map_pow, hα, hβ, ← pow_mul, ← pow_mul, mul_comm M' M,
        ← mul_pow, show (g ^ m * a) * (g ^ m' * b) = g ^ (m + m') * (a * b) by ring, mul_pow,
        mul_pow, ← pow_mul (a * b), mul_comm (M * M') N, pow_mul (a * b), hN,
        zero_pow (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hM hM')), mul_zero]
    have h2 : (α ^ M' * β ^ M) ^ N = 0 := hj (by rw [h1, map_zero])
    have h3 : α ^ M' * β ^ M = 0 := pow_eq_zero_iff'.mp h2 |>.1
    rcases mul_eq_zero.mp h3 with h | h
    · left
      have hα0 : α = 0 := pow_eq_zero_iff'.mp h |>.1
      refine hnil a m M hM ?_
      rw [← hα, hα0, map_zero]
    · right
      have hβ0 : β = 0 := pow_eq_zero_iff'.mp h |>.1
      refine hnil b m' M' hM' ?_
      rw [← hβ, hβ0, map_zero]

section OptionEquiv

variable {R S : Type*} [CommRing R] [CommRing S] {σ : Type*}

lemma optionEquivLeft_symm_C (p : MvPolynomial σ R) :
    (MvPolynomial.optionEquivLeft R σ).symm (Polynomial.C p) = MvPolynomial.rename some p := by
  simp [MvPolynomial.optionEquivLeft]

lemma map_optionEquivLeft_symm (f : R →+* S) (F : Polynomial (MvPolynomial σ R)) :
    MvPolynomial.map f ((MvPolynomial.optionEquivLeft R σ).symm F) =
      (MvPolynomial.optionEquivLeft S σ).symm (F.map (MvPolynomial.map f)) := by
  have key : (MvPolynomial.map f).comp
      ((MvPolynomial.optionEquivLeft R σ).symm : Polynomial (MvPolynomial σ R) →+* MvPolynomial (Option σ) R) =
      ((MvPolynomial.optionEquivLeft S σ).symm : Polynomial (MvPolynomial σ S) →+* MvPolynomial (Option σ) S).comp
        (Polynomial.mapRingHom (MvPolynomial.map f)) := by
    apply Polynomial.ringHom_ext
    · intro p
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, Polynomial.coe_mapRingHom,
        Polynomial.map_C, optionEquivLeft_symm_C, MvPolynomial.map_rename]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, Polynomial.coe_mapRingHom,
        Polynomial.map_X, MvPolynomial.optionEquivLeft_symm_X, MvPolynomial.map_X]
  exact congrArg (fun φ => φ F) key

lemma aeval_optionEquivLeft_symm {C : Type*} [CommRing C] [Algebra R C] {d : ℕ}
    (z : Fin d → C) (w : C) (F : Polynomial (MvPolynomial (Fin d) R)) :
    MvPolynomial.aeval (fun o : Option (Fin d) => o.elim w z) ((MvPolynomial.optionEquivLeft R (Fin d)).symm F) =
      F.eval₂ (MvPolynomial.aeval z : MvPolynomial (Fin d) R →ₐ[R] C).toRingHom w := by
  rw [MvPolynomial.aeval_def, ← MvPolynomial.eval_map, map_optionEquivLeft_symm,
    MvPolynomial.optionEquivLeft_elim_eval, AlgEquiv.apply_symm_apply, Polynomial.map_map,
    Polynomial.eval_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

end OptionEquiv

section General

theorem ringKrullDim_le_of_isIntegral {B S : Type*} [CommRing B] [CommRing S] (f : B →+* S)
    (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim B := by
  letI : Algebra B S := f.toAlgebra
  haveI : Algebra.IsIntegral B S := ⟨hf⟩
  change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum B)
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B S)) ?_
  intro q1 q2 hlt
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
  obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff
    ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
    (Algebra.IsIntegral.isIntegral y)

theorem radical_eq_comap_nilradical {C : Type*} [CommRing C] (I : Ideal C) :
    I.radical = (nilradical (C ⧸ I)).comap (Ideal.Quotient.mk I) := by
  ext x
  rw [Ideal.mem_comap, mem_nilradical, Ideal.mem_radical_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hn]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_pow]; exact hn)⟩

theorem comap_mem_minimalPrimes {C : Type*} [CommRing C] (I : Ideal C) {Qb : Ideal (C ⧸ I)}
    (hQb : Qb ∈ minimalPrimes (C ⧸ I)) : Qb.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes := by
  haveI : Qb.IsPrime := hQb.1.1
  refine ⟨⟨Ideal.comap_isPrime _ Qb, ?_⟩, ?_⟩
  · intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact zero_mem _
  · rintro P ⟨hP, hIP⟩ hle
    haveI := hP
    have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ P := by rwa [Ideal.mk_ker]
    haveI hPm : (P.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have h1 : P.map (Ideal.Quotient.mk I) ≤ Qb := by
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Qb]
      exact Ideal.map_mono hle
    have h2 : Qb ≤ P.map (Ideal.Quotient.mk I) := hQb.2 ⟨hPm, bot_le⟩ h1
    intro x hx
    have h3 : x ∈ (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) := h2 hx
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker] at h3

end General

section Main

variable (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C] [FaithfulSMul R C]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main
    (hgi : ∀ θ : FractionRing C,
      IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) θ →
      θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) :
    ∃ r : R, r ≠ 0 ∧ ∀ n : Ideal R, n.IsMaximal → r ∉ n →
      n.map (algebraMap R C) = ⊤ ∨ (n.map (algebraMap R C)).radical.IsPrime := by
  classical

  obtain ⟨r₁, hr₁, d, z, w, F, g, hz, hFm, hFroot, hFirr, hg0, hrad, hint⟩ :=
    Algebra.exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable k hgi

  let G : MvPolynomial (Option (Fin d)) R := (MvPolynomial.optionEquivLeft R (Fin d)).symm F
  have hGirr : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))) G) := by
    change Irreducible (MvPolynomial.map _ ((MvPolynomial.optionEquivLeft R (Fin d)).symm F))
    rw [map_optionEquivLeft_symm]
    exact (MulEquiv.irreducible_iff
      (MvPolynomial.optionEquivLeft (AlgebraicClosure (FractionRing R)) (Fin d)).symm.toMulEquiv).mpr hFirr
  obtain ⟨c₂, hc₂, hBN⟩ :=
    MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure G hGirr

  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hg0
  refine ⟨r₁ * c₂ * g.coeff μ, mul_ne_zero (mul_ne_zero hr₁ hc₂) hμ, ?_⟩
  intro n hn hrn
  haveI := hn
  have hr₁n : r₁ ∉ n := fun h => hrn (n.mul_mem_right _ (n.mul_mem_right _ h))
  have hc₂n : c₂ ∉ n := fun h => hrn (n.mul_mem_right _ (n.mul_mem_left _ h))
  have hγn : g.coeff μ ∉ n := fun h => hrn (n.mul_mem_left _ h)
  by_cases htop : n.map (algebraMap R C) = ⊤
  · exact Or.inl htop
  right

  haveI hAnt : Nontrivial (C ⧸ n.map (algebraMap R C)) := Ideal.Quotient.nontrivial_iff.mpr htop
  let φ : R →+* n.ResidueField := algebraMap R n.ResidueField
  have hφ0 : ∀ x : R, φ x = 0 ↔ x ∈ n := fun x => Ideal.algebraMap_residueField_eq_zero
  let π : C →+* C ⧸ n.map (algebraMap R C) := Ideal.Quotient.mk (n.map (algebraMap R C))
  let πₐ : C →ₐ[R] C ⧸ n.map (algebraMap R C) := Ideal.Quotient.mkₐ R (n.map (algebraMap R C))
  have hππ : ∀ c, πₐ c = π c := fun _ => rfl
  have hπsurj : Function.Surjective π := Ideal.Quotient.mk_surjective

  have hi₁ : n ≤ RingHom.ker (π.comp (algebraMap R C)) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hx
  have hi₂ : n.primeCompl ≤ (IsUnit.submonoid (C ⧸ n.map (algebraMap R C))).comap (π.comp (algebraMap R C)) := by
    intro x hx
    obtain ⟨y, u, hu, hyx⟩ := hn.exists_inv hx
    change IsUnit (π (algebraMap R C x))
    refine isUnit_iff_exists_inv.mpr ⟨π (algebraMap R C y), ?_⟩
    rw [← map_mul, ← map_mul, mul_comm x y, show y * x = 1 - u by rw [← hyx]; ring, map_sub, map_one,
      map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hu), sub_zero]
  let i : n.ResidueField →+* C ⧸ n.map (algebraMap R C) := Ideal.ResidueField.lift n _ hi₁ hi₂
  have hiφ : ∀ x : R, i (φ x) = π (algebraMap R C x) := fun x => Ideal.ResidueField.lift_algebraMap n _ hi₁ hi₂ x
  have hiφ' : i.comp φ = π.comp (algebraMap R C) := RingHom.ext hiφ

  let zb : Fin d → C ⧸ n.map (algebraMap R C) := fun i => π (z i)
  let wb : C ⧸ n.map (algebraMap R C) := π w
  let ψ : MvPolynomial (Fin d) n.ResidueField →+* C ⧸ n.map (algebraMap R C) := MvPolynomial.eval₂Hom i zb
  have hψC : ∀ y, ψ (MvPolynomial.C y) = i y := fun y => MvPolynomial.eval₂Hom_C i zb y
  have hψX : ∀ t, ψ (MvPolynomial.X t) = zb t := fun t => MvPolynomial.eval₂Hom_X' i zb t
  have hψmap : ∀ q : MvPolynomial (Fin d) R, ψ (MvPolynomial.map φ q) = π (MvPolynomial.aeval z q) := by
    intro q
    change MvPolynomial.eval₂Hom i zb (MvPolynomial.map φ q) = π (MvPolynomial.eval₂ (algebraMap R C) z q)
    rw [MvPolynomial.eval₂Hom_map_hom, hiφ', MvPolynomial.eval₂_comp_left]
    rfl

  have hGbirr : Irreducible (MvPolynomial.map φ G) := hBN n.ResidueField φ ((hφ0 c₂).not.mpr hc₂n)
  have hGbprime : Prime (MvPolynomial.map φ G) :=
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hGbirr)
  haveI hDprime : (Ideal.span {MvPolynomial.map φ G}).IsPrime :=
    (Ideal.span_singleton_prime hGbprime.ne_zero).mpr hGbprime
  haveI : IsDomain (MvPolynomial (Option (Fin d)) n.ResidueField ⧸ Ideal.span {MvPolynomial.map φ G}) :=
    Ideal.Quotient.isDomain _

  let j₀ : MvPolynomial (Option (Fin d)) n.ResidueField →+* C ⧸ n.map (algebraMap R C) :=
    MvPolynomial.eval₂Hom i fun o => o.elim wb zb
  have hj₀G : j₀ (MvPolynomial.map φ G) = 0 := by
    have h1 : j₀ (MvPolynomial.map φ G) =
        π (MvPolynomial.aeval (fun o : Option (Fin d) => o.elim w z) G) := by
      change MvPolynomial.eval₂Hom i _ (MvPolynomial.map φ G) =
        π (MvPolynomial.eval₂ (algebraMap R C) (fun o : Option (Fin d) => o.elim w z) G)
      rw [MvPolynomial.eval₂Hom_map_hom, hiφ', MvPolynomial.eval₂_comp_left]
      change MvPolynomial.eval₂ _ _ G = MvPolynomial.eval₂ _ _ G
      congr 1
      funext o
      cases o <;> rfl
    rw [h1, aeval_optionEquivLeft_symm, hFroot, map_zero]
  let j : (MvPolynomial (Option (Fin d)) n.ResidueField ⧸ Ideal.span {MvPolynomial.map φ G}) →+*
      C ⧸ n.map (algebraMap R C) :=
    Ideal.Quotient.lift _ j₀ (by
      intro a ha
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hj₀G, mul_zero])
  have hjmk : ∀ q, j (Ideal.Quotient.mk _ q) = j₀ q := fun q => rfl

  have hrangeA : ∀ a ∈ Algebra.adjoin R (Set.range z), π a ∈ ψ.range := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact ⟨MvPolynomial.X t, hψX t⟩
    | algebraMap x =>
      exact ⟨MvPolynomial.C (φ x), by rw [hψC, hiφ]⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hintA : ψ.IsIntegral := by
    intro ab
    obtain ⟨c, rfl⟩ := hπsurj ab
    obtain ⟨n₀, P, hPm, hP⟩ := hint c
    let P₂ : Polynomial (C ⧸ n.map (algebraMap R C)) :=
      P.map (π.comp (algebraMap (Algebra.adjoin R (Set.range z)) C))
    have hP₂m : P₂.Monic := hPm.map _
    have hP₂ : P₂.eval (π (r₁ ^ n₀ • c)) = 0 := by
      rw [Polynomial.eval_map, ← Polynomial.hom_eval₂, hP, map_zero]
    have hlift : P₂ ∈ Polynomial.lifts ψ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro t
      rw [Polynomial.coeff_map, RingHom.comp_apply]
      obtain ⟨s, hs⟩ := hrangeA _ (P.coeff t).2
      exact ⟨s, hs⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP₂m
    have hint1 : ψ.IsIntegralElem (π (r₁ ^ n₀ • c)) := by
      refine ⟨Q, hQm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map, hQ]
      exact hP₂

    have hu : φ r₁ ≠ 0 := (hφ0 r₁).not.mpr hr₁n
    have heq : π c = ψ (MvPolynomial.C ((φ r₁)⁻¹ ^ n₀)) * π (r₁ ^ n₀ • c) := by
      rw [hψC, Algebra.smul_def, map_mul, ← hiφ, map_pow, map_pow, map_pow, ← mul_assoc, ← mul_pow,
        ← map_mul, inv_mul_cancel₀ hu, map_one, one_pow, one_mul]
    rw [heq]
    exact RingHom.IsIntegralElem.mul ψ (RingHom.isIntegralElem_map ψ) hint1

  let θ₀ : MvPolynomial (Fin d) n.ResidueField →+* MvPolynomial (Option (Fin d)) n.ResidueField :=
    MvPolynomial.eval₂Hom MvPolynomial.C fun t => MvPolynomial.X (some t)
  let θ : MvPolynomial (Fin d) n.ResidueField →+*
      (MvPolynomial (Option (Fin d)) n.ResidueField ⧸ Ideal.span {MvPolynomial.map φ G}) :=
    (Ideal.Quotient.mk _).comp θ₀
  have hθ₀ : θ₀ = (MvPolynomial.rename (R := n.ResidueField) (some : Fin d → Option (Fin d))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro y; simp [θ₀]
    · intro t; simp [θ₀, MvPolynomial.rename_X]
  have hjθ : j.comp θ = ψ := by
    apply MvPolynomial.ringHom_ext
    · intro y
      change j (Ideal.Quotient.mk _ (θ₀ (MvPolynomial.C y))) = ψ (MvPolynomial.C y)
      rw [hjmk, hψC]
      simp [θ₀, j₀]
    · intro t
      change j (Ideal.Quotient.mk _ (θ₀ (MvPolynomial.X t))) = ψ (MvPolynomial.X t)
      rw [hjmk, hψX]
      simp [θ₀, j₀]
  have hθint : θ.IsIntegral := by

    have ht : θ.IsIntegralElem (Ideal.Quotient.mk (Ideal.span {MvPolynomial.map φ G}) (MvPolynomial.X none)) := by
      refine ⟨F.map (MvPolynomial.map φ), hFm.map _, ?_⟩
      have h1 : (F.map (MvPolynomial.map φ)).eval₂ θ₀ (MvPolynomial.X none) = MvPolynomial.map φ G := by
        change _ = MvPolynomial.map φ ((MvPolynomial.optionEquivLeft R (Fin d)).symm F)
        rw [map_optionEquivLeft_symm, hθ₀]
        rfl
      have h2 := congrArg (Ideal.Quotient.mk (Ideal.span {MvPolynomial.map φ G})) h1
      rw [Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)] at h2
      exact h2
    intro x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction q using MvPolynomial.induction_on with
    | C a =>
      have : Ideal.Quotient.mk (Ideal.span {MvPolynomial.map φ G}) (MvPolynomial.C a) = θ (MvPolynomial.C a) := by
        change _ = Ideal.Quotient.mk _ (θ₀ (MvPolynomial.C a))
        simp [θ₀]
      rw [this]
      exact RingHom.isIntegralElem_map θ
    | add p q hp hq => rw [map_add]; exact RingHom.IsIntegralElem.add θ hp hq
    | mul_X p o hp =>
      rw [map_mul]
      refine RingHom.IsIntegralElem.mul θ hp ?_
      cases o with
      | none => exact ht
      | some t =>
        have : Ideal.Quotient.mk (Ideal.span {MvPolynomial.map φ G}) (MvPolynomial.X (some t)) =
            θ (MvPolynomial.X t) := by
          change _ = Ideal.Quotient.mk _ (θ₀ (MvPolynomial.X t))
          simp [θ₀]
        rw [this]
        exact RingHom.isIntegralElem_map θ

  have hinjQ : ∀ Qb ∈ minimalPrimes (C ⧸ n.map (algebraMap R C)),
      ∀ b : MvPolynomial (Fin d) n.ResidueField, Ideal.Quotient.mk Qb (ψ b) = 0 → b = 0 := by
    intro Qb hQb
    haveI hQbp : Qb.IsPrime := hQb.1.1

    have hQ : Qb.comap (Ideal.Quotient.mk (n.map (algebraMap R C))) ∈ (n.map (algebraMap R C)).minimalPrimes :=
      comap_mem_minimalPrimes _ hQb
    have hdimQ := Ideal.natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent
      k z hz r₁ hr₁ hint n hr₁n _ hQ
    have hQbeq : Qb = (Qb.comap (Ideal.Quotient.mk (n.map (algebraMap R C)))).map
        (Ideal.Quotient.mk (n.map (algebraMap R C))) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Qb).symm
    have hdimQb : (d : WithBot ℕ∞) ≤ ringKrullDim ((C ⧸ n.map (algebraMap R C)) ⧸ Qb) := by
      have e := (Ideal.quotEquivOfEq hQbeq).trans
        (DoubleQuot.quotQuotEquivQuotOfLE (comap_mem_minimalPrimes _ hQb).1.2)
      rw [ringKrullDim_eq_of_ringEquiv e]
      exact hdimQ

    let ψb : MvPolynomial (Fin d) n.ResidueField →+* (C ⧸ n.map (algebraMap R C)) ⧸ Qb :=
      (Ideal.Quotient.mk Qb).comp ψ
    have hψb : ∀ b, ψb b = Ideal.Quotient.mk Qb (ψ b) := fun _ => rfl
    haveI : IsDomain ((C ⧸ n.map (algebraMap R C)) ⧸ Qb) := Ideal.Quotient.isDomain Qb
    haveI hpprime : (RingHom.ker ψb).IsPrime := RingHom.ker_isPrime ψb

    have hψbint : ψb.IsIntegral :=
      RingHom.IsIntegral.trans ψ (Ideal.Quotient.mk Qb) hintA
        (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
    have hlift_int : (RingHom.kerLift ψb).IsIntegral := by
      refine RingHom.IsIntegral.tower_top (Ideal.Quotient.mk (RingHom.ker ψb)) (RingHom.kerLift ψb) ?_
      have hc : (RingHom.kerLift ψb).comp (Ideal.Quotient.mk (RingHom.ker ψb)) = ψb :=
        RingHom.ext fun b => RingHom.kerLift_mk ψb b
      rw [hc]
      exact hψbint
    have hdim1 : ringKrullDim ((C ⧸ n.map (algebraMap R C)) ⧸ Qb) ≤
        ringKrullDim (MvPolynomial (Fin d) n.ResidueField ⧸ RingHom.ker ψb) :=
      ringKrullDim_le_of_isIntegral (RingHom.kerLift ψb) hlift_int

    have hDF := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType n.ResidueField (RingHom.ker ψb)
    have hdimB : ringKrullDim (MvPolynomial (Fin d) n.ResidueField) = d := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hdimB] at hDF
    have hht0 : (RingHom.ker ψb).height = 0 := by
      obtain ⟨hq, hhq⟩ : ∃ hq : ℕ, (RingHom.ker ψb).height = hq :=
        ⟨_, (ENat.coe_toNat (Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance))).symm⟩
      have hle : (d : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin d) n.ResidueField ⧸ RingHom.ker ψb) :=
        hdimQb.trans hdim1
      have hlt : ringKrullDim (MvPolynomial (Fin d) n.ResidueField ⧸ RingHom.ker ψb) ≤ d := by
        rw [← hdimB]; exact ringKrullDim_quotient_le _
      have heq : ringKrullDim (MvPolynomial (Fin d) n.ResidueField ⧸ RingHom.ker ψb) = d := le_antisymm hlt hle
      rw [hhq, heq] at hDF
      have : hq + d = d := by exact_mod_cast hDF
      have : hq = 0 := by omega
      rw [hhq, this]; rfl
    have hker : RingHom.ker ψb = ⊥ := by
      have hmin := Ideal.height_eq_zero_iff.mp hht0
      rw [IsDomain.minimalPrimes_eq_singleton_bot] at hmin
      exact hmin
    intro b hb
    have : b ∈ RingHom.ker ψb := by rw [RingHom.mem_ker, hψb]; exact hb
    rwa [hker] at this

  obtain ⟨Q₀, hQ₀, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (C ⧸ n.map (algebraMap R C))))
    (J := (Classical.arbitrary (MaximalSpectrum (C ⧸ n.map (algebraMap R C)))).asIdeal) bot_le
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    exact hinjQ Q₀ hQ₀ b (by rw [hb, map_zero])
  let gb : C ⧸ n.map (algebraMap R C) := ψ (MvPolynomial.map φ g)
  have hgb : ∀ Qb ∈ minimalPrimes (C ⧸ n.map (algebraMap R C)), gb ∉ Qb := by
    intro Qb hQb hmem
    have h1 : MvPolynomial.map φ g = 0 := hinjQ Qb hQb _ (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
    have h2 : (MvPolynomial.map φ g).coeff μ = 0 := by rw [h1, MvPolynomial.coeff_zero]
    rw [MvPolynomial.coeff_map] at h2
    exact hγn ((hφ0 _).mp h2)

  have hjinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    letI : Algebra (MvPolynomial (Fin d) n.ResidueField)
        (MvPolynomial (Option (Fin d)) n.ResidueField ⧸ Ideal.span {MvPolynomial.map φ G}) := θ.toAlgebra
    have hxint : IsIntegral (MvPolynomial (Fin d) n.ResidueField) x := hθint x
    have hne := Ideal.comap_ne_bot_of_integral_mem (I := RingHom.ker j) hx0 ((RingHom.mem_ker).mpr hx) hxint
    apply hne
    rw [eq_bot_iff]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker] at hb
    change j (θ b) = 0 at hb
    rw [← RingHom.comp_apply, hjθ] at hb
    exact (Submodule.mem_bot _).mpr (hψinj (by rw [hb, map_zero]))

  have hrangeJ : ∀ a ∈ Algebra.adjoin R (insert w (Set.range z)), π a ∈ j.range := by
    have hj₀r : ∀ q, j₀ q ∈ j.range := fun q => ⟨Ideal.Quotient.mk _ q, hjmk q⟩
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | ⟨t, rfl⟩
      · refine ⟨Ideal.Quotient.mk _ (MvPolynomial.X none), ?_⟩
        rw [hjmk]; exact MvPolynomial.eval₂Hom_X' _ _ _
      · refine ⟨Ideal.Quotient.mk _ (MvPolynomial.X (some t)), ?_⟩
        rw [hjmk]; exact MvPolynomial.eval₂Hom_X' _ _ _
    | algebraMap x =>
      refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C (φ x)), ?_⟩
      rw [hjmk]
      change j₀ (MvPolynomial.C (φ x)) = π (algebraMap R C x)
      rw [MvPolynomial.eval₂Hom_C, hiφ]
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hradA : ∀ a : C ⧸ n.map (algebraMap R C), ∃ m M : ℕ, 0 < M ∧ (gb ^ m * a) ^ M ∈ j.range := by
    intro a
    obtain ⟨c, rfl⟩ := hπsurj a
    obtain ⟨m, M, hM, hmem⟩ := hrad c
    refine ⟨m, M, hM, ?_⟩
    have h1 : gb = π (MvPolynomial.aeval z g) := hψmap g
    rw [h1, ← map_pow, ← map_mul, ← map_pow]
    exact hrangeJ _ hmem

  have hprime : (nilradical (C ⧸ n.map (algebraMap R C))).IsPrime :=
    nilradical_isPrime_of_radicial j hjinj gb hgb hradA
  rw [radical_eq_comap_nilradical]
  exact Ideal.comap_isPrime _ _

end Main

end P2mGenIrredAff

theorem solution
    (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C] [FaithfulSMul R C]
    (hgi : ∀ θ : FractionRing C,
      IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) θ →
      θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) :
    ∃ r : R, r ≠ 0 ∧ ∀ n : Ideal R, n.IsMaximal → r ∉ n →
      n.map (algebraMap R C) = ⊤ ∨ (n.map (algebraMap R C)).radical.IsPrime :=
  P2mGenIrredAff.main k hgi

end S_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime
end P2MW
export P2MW.S_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime (solution)
