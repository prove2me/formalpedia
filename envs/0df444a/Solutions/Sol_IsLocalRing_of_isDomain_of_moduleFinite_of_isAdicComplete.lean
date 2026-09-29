-- Prove2me | solution 1 for IsLocalRing.of_isDomain_of_moduleFinite_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ff0776f6-2d3f-568b-8e84-ba70635cdb14

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_of_isDomain_of_moduleFinite_of_isAdicComplete

open Polynomial

namespace S10Card2
variable {R : Type*} [CommRing R] (I : Ideal R)

theorem isPrecomplete_of_surjective {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [IsPrecomplete I M] {f : M →ₗ[R] N}
    (hf : Function.Surjective f) : IsPrecomplete I N := by
  refine ⟨fun g hg => ?_⟩
  have hmap : ∀ k : ℕ, Submodule.map f (I ^ k • ⊤ : Submodule R M) =
      (I ^ k • ⊤ : Submodule R N) := by
    intro k
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  have hstep : ∀ k : ℕ, ∃ d : M, d ∈ (I ^ k • ⊤ : Submodule R M) ∧ f d = g (k + 1) - g k := by
    intro k
    have h1 : g k - g (k + 1) ∈ (I ^ k • ⊤ : Submodule R N) := by
      have h2 := hg (Nat.le_succ k)
      rwa [SModEq.sub_mem] at h2
    have h3 : g (k + 1) - g k ∈ (I ^ k • ⊤ : Submodule R N) := by
      have := neg_mem h1
      rwa [neg_sub] at this
    rw [← hmap k] at h3
    obtain ⟨d, hd, hfd⟩ := h3
    exact ⟨d, hd, hfd⟩
  choose d hd hfd using hstep
  obtain ⟨m₀, hm₀⟩ := hf (g 0)
  obtain ⟨h, hh0, hhsucc⟩ : ∃ h : ℕ → M, h 0 = m₀ ∧ ∀ k, h (k + 1) = h k + d k :=
    ⟨fun k => Nat.rec (motive := fun _ => M) m₀ (fun k acc => acc + d k) k, rfl, fun _ => rfl⟩
  have hfh : ∀ k, f (h k) = g k := by
    intro k
    induction k with
    | zero => rw [hh0, hm₀]
    | succ k ih =>
      rw [hhsucc, map_add, ih, hfd]
      abel
  have hcauchy : ∀ {a b : ℕ}, a ≤ b → h a ≡ h b [SMOD (I ^ a • ⊤ : Submodule R M)] := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact SModEq.refl _
    | succ b hab ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem]
      have he : h b - h (b + 1) = -(d b) := by rw [hhsucc b]; abel
      rw [he]
      exact neg_mem (Submodule.pow_smul_top_le I M hab (hd b))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I M) @hcauchy
  refine ⟨f L, fun k => ?_⟩
  rw [SModEq.sub_mem]
  have h1 : h k - L ∈ (I ^ k • ⊤ : Submodule R M) := by
    have h2 := hL k
    rwa [SModEq.sub_mem] at h2
  have h3 : g k - f L = f (h k - L) := by rw [map_sub, hfh k]
  rw [h3, ← hmap k]
  exact Submodule.mem_map_of_mem h1

variable {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem apply_mem_smul_top {K : Ideal R} {x : ∀ i, M i}
    (hx : x ∈ (K • ⊤ : Submodule R (∀ i, M i))) (i : ι) :
    x i ∈ (K • ⊤ : Submodule R (M i)) := by
  have h2 : (LinearMap.proj (R := R) (φ := M) i) x ∈
      Submodule.map (LinearMap.proj (R := R) (φ := M) i) (K • ⊤ : Submodule R (∀ i, M i)) :=
    Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h2
  have h3 : (LinearMap.proj (R := R) (φ := M) i) x ∈ (K • ⊤ : Submodule R (M i)) :=
    Submodule.smul_mono le_rfl le_top h2
  simpa using h3

theorem mem_smul_top_pi [Finite ι] {K : Ideal R} {x : ∀ i, M i}
    (hx : ∀ i, x i ∈ (K • ⊤ : Submodule R (M i))) :
    x ∈ (K • ⊤ : Submodule R (∀ i, M i)) := by
  classical
  have h1 : x ∈ Submodule.pi Set.univ (fun i => (K • ⊤ : Submodule R (M i))) :=
    Submodule.mem_pi.mpr fun i _ => hx i
  rw [← Submodule.iSup_map_single] at h1
  have hle : (⨆ i, Submodule.map (LinearMap.single R M i) (K • ⊤ : Submodule R (M i))) ≤
      (K • ⊤ : Submodule R (∀ i, M i)) := by
    refine iSup_le fun i => ?_
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle h1

theorem isPrecomplete_pi [Finite ι] [∀ i, IsPrecomplete I (M i)] :
    IsPrecomplete I (∀ i, M i) := by
  refine ⟨fun g hg => ?_⟩
  have hcoord : ∀ i : ι, ∃ L : M i,
      ∀ k, g k i ≡ L [SMOD (I ^ k • ⊤ : Submodule R (M i))] := by
    intro i
    refine IsPrecomplete.prec (inferInstance : IsPrecomplete I (M i)) ?_
    intro a b hab
    have h1 := hg hab
    rw [SModEq.sub_mem] at h1 ⊢
    have h2 := apply_mem_smul_top M h1 i
    simpa using h2
  choose L hL using hcoord
  refine ⟨L, fun k => ?_⟩
  rw [SModEq.sub_mem]
  refine mem_smul_top_pi M fun i => ?_
  have h3 := hL i k
  rw [SModEq.sub_mem] at h3
  simpa using h3

theorem isPrecomplete_of_module_finite (M : Type*) [AddCommGroup M] [Module R M]
    [IsPrecomplete I R] [Module.Finite R M] :
    IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (R := R) (M := M)
  haveI : ∀ i : Fin n, IsPrecomplete I ((fun _ : Fin n => R) i) := fun _ => ‹IsPrecomplete I R›
  haveI : IsPrecomplete I (Fin n → R) := isPrecomplete_pi I (fun _ : Fin n => R)
  exact isPrecomplete_of_surjective I hf
end S10Card2

theorem S10.adic_complete_of_finite {R : Type*} [CommRing R] (I : Ideal R)
    [IsNoetherianRing R] [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsAdicComplete I M :=
  { toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot (I := I))
    toIsPrecomplete := S10Card2.isPrecomplete_of_module_finite I M }

theorem S10.henselian_idem {D : Type*} [CommRing D]
    [IsDomain D] (J : Ideal D) [HenselianRing D J] (e : D ⧸ J) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  classical
  obtain ⟨d, rfd⟩ := Ideal.Quotient.mk_surjective e
  set f : D[X] := X ^ 2 - X with hf
  have hmon : f.Monic := by
    rw [hf]
    exact Polynomial.monic_X_pow_sub (by simp [Polynomial.degree_X])
  have heval : f.eval d ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk J (f.eval d) = e ^ 2 - e := by
      rw [hf]; simp [rfd]
    rw [this, sq, he.eq, sub_self]
  have hder : IsUnit (Ideal.Quotient.mk J (f.derivative.eval d)) := by
    have h1 : Ideal.Quotient.mk J (f.derivative.eval d) = 2 * e - 1 := by
      rw [hf]; simp [rfd]; ring
    rw [h1]
    refine (isUnit_iff_exists_inv).mpr ⟨2 * e - 1, ?_⟩
    have : (2 * e - 1) * (2 * e - 1) = 4 * (e * e) - 4 * e + 1 := by ring
    rw [this, he.eq]; ring
  obtain ⟨a, ha, had⟩ := HenselianRing.is_henselian (I := J) f hmon d heval hder
  have ha' : a * a = a := by
    have : f.eval a = 0 := ha
    rw [hf] at this
    simp only [eval_sub, eval_pow, eval_X] at this
    rw [sq] at this
    exact sub_eq_zero.mp this
  have ha01 : a = 0 ∨ a = 1 := by
    have : a * (a - 1) = 0 := by rw [mul_sub, mul_one, ha', sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hae : Ideal.Quotient.mk J a = e := by
    rw [← rfd, Ideal.Quotient.eq]; exact had
  rcases ha01 with rfl | rfl
  · left; rw [← hae, map_zero]
  · right; rw [← hae, map_one]

theorem S10Card4.subsingleton_maximalSpectrum_quotient {D : Type*} [CommRing D]
    [IsDomain D] (J : Ideal D) [HenselianRing D J] [IsArtinianRing (D ⧸ J)] :
    Subsingleton (MaximalSpectrum (D ⧸ J)) := by
  classical
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨m₁, m₂, hne⟩ := hns
  set A := D ⧸ J
  let δ : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal := fun I => if I = m₁ then 0 else 1
  have hδ : IsIdempotentElem δ := by
    show δ * δ = δ
    funext I
    simp only [δ, Pi.mul_apply]
    split_ifs <;> simp
  let ε : A ⧸ nilradical A := (IsArtinianRing.quotNilradicalEquivPi A).symm δ
  have hε : IsIdempotentElem ε := by
    show ε * ε = ε
    simp only [ε, ← map_mul, hδ.eq]
  obtain ⟨e, he, hee⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk (nilradical A))
    (fun x hx => by rwa [Ideal.mk_ker, mem_nilradical] at hx) ε
    (Ideal.Quotient.mk_surjective ε) hε
  have hproj : IsArtinianRing.quotNilradicalEquivPi A (Ideal.Quotient.mk _ e) = δ := by
    rw [hee]; exact (IsArtinianRing.quotNilradicalEquivPi A).apply_symm_apply δ
  rcases S10.henselian_idem J e he with rfl | rfl
  · have := congrFun hproj m₂
    simp only [map_zero, Pi.zero_apply, δ, if_neg hne.symm] at this
    exact zero_ne_one this
  · have := congrFun hproj m₁
    simp only [map_one, Pi.one_apply, δ, if_pos rfl] at this
    exact one_ne_zero this

theorem S10.local_of_henselian_artinian {D : Type*} [CommRing D]
    [IsDomain D] (J : Ideal D) [HenselianRing D J] [IsArtinianRing (D ⧸ J)] [Nontrivial (D ⧸ J)] :
    IsLocalRing D := by
  classical
  haveI := S10Card4.subsingleton_maximalSpectrum_quotient J
  haveI : IsLocalRing (D ⧸ J) := by
    refine IsLocalRing.of_unique_max_ideal ?_
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (D ⧸ J)
    refine ⟨m, hm, fun m' hm' => ?_⟩
    have := Subsingleton.elim (⟨m', hm'⟩ : MaximalSpectrum (D ⧸ J)) ⟨m, hm⟩
    exact congrArg MaximalSpectrum.asIdeal this
  haveI : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J HenselianRing.jac
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk J a) with h | h
  · exact Or.inl (isUnit_of_map_unit (Ideal.Quotient.mk J) a h)
  · refine Or.inr (isUnit_of_map_unit (Ideal.Quotient.mk J) (1 - a) ?_)
    rwa [map_sub, map_one]

theorem S10Card5.map_maximalIdeal_ne_top {R : Type*} [CommRing R] [IsLocalRing R]
    (D : Type*) [CommRing D] [Algebra R D] [Module.Finite R D] [Nontrivial D] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R D) ≠ ⊤ := by
  intro htop
  have hsmul : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R D) = ⊤ := by
    rw [Ideal.smul_top_eq_map, htop]
    rfl
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) (⊤ : Submodule R D)
    Module.Finite.fg_top (by rw [hsmul]) (IsLocalRing.maximalIdeal_le_jacobson _)
  exact top_ne_bot this

theorem solution (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (D : Type*) [CommRing D] [IsDomain D] [Algebra R D] [Module.Finite R D] : IsLocalRing D := by
  classical
  have hJ := S10Card5.map_maximalIdeal_ne_top (R := R) D
  set J : Ideal D := (IsLocalRing.maximalIdeal R).map (algebraMap R D) with hJdef
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal R) D :=
    S10.adic_complete_of_finite (IsLocalRing.maximalIdeal R) D
  haveI : IsAdicComplete J D :=
    (IsAdicComplete.map_algebraMap_iff (I := IsLocalRing.maximalIdeal R) (S := D) (M := D)).mpr this
  haveI : HenselianRing D J := inferInstance
  haveI : Nontrivial (D ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (D ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R _ _
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  haveI : IsArtinianRing (D ⧸ J) :=
    IsArtinianRing.of_finite (R ⧸ IsLocalRing.maximalIdeal R) (D ⧸ J)
  exact S10.local_of_henselian_artinian J

end S_IsLocalRing_of_isDomain_of_moduleFinite_of_isAdicComplete
end P2MW
export P2MW.S_IsLocalRing_of_isDomain_of_moduleFinite_of_isAdicComplete (solution)
