-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.isRegularRing_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4b848fbb-b2f5-596f-a5bd-8c80eb85bb3d

import Mathlib
import Definitions.Def_MvPolynomial_CrossingQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_isRegularRing_of_irreducible

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial IsLocalRing

namespace CrossingResolutionR1

noncomputable section

section General

variable {A : Type*} [CommRing A]

theorem isRegularRing_localization [IsRegularRing A] (M : Submonoid A) :
    IsRegularRing (Localization M) := by
  rw [isRegularRing_iff]
  intro q hq
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).toRingEquiv

theorem isRegularLocalRing_atPrime_of_disjoint (M : Submonoid A) [IsRegularRing (Localization M)]
    (P : Ideal A) [hP : P.IsPrime] (h : Disjoint (M : Set A) (P : Set A)) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  set Q : Ideal (Localization M) := P.map (algebraMap A (Localization M)) with hQdef
  haveI hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P hP h
  have hc : Q.comap (algebraMap A (Localization M)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP h
  have hM : (Q.comap (algebraMap A (Localization M))).primeCompl = P.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hc]
  haveI : IsLocalization P.primeCompl (Localization.AtPrime Q) := by
    rw [← hM]
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime Q) Q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime Q)
      (Localization.AtPrime P)).toRingEquiv

variable [IsNoetherianRing A]

theorem isRegularLocalRing_of_span_eq (P : Ideal A) [P.IsPrime] (S : Finset A)
    (hS : Ideal.span (S : Set A) = P) (h : (S.card : ℕ∞) ≤ P.height) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  subst hS
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (Ideal.span (S : Set A))
    (Localization.AtPrime (Ideal.span (S : Set A))),
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span]
  have hfin : ((algebraMap A (Localization.AtPrime (Ideal.span (S : Set A)))) ''
      (S : Set A)).Finite := S.finite_toSet.image _
  have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Localization.AtPrime
    (Ideal.span (S : Set A))) hfin
  have h2 : ((algebraMap A (Localization.AtPrime (Ideal.span (S : Set A)))) ''
      (S : Set A)).ncard ≤ S.card := by
    calc _ ≤ (S : Set A).ncard := Set.ncard_image_le S.finite_toSet
      _ = S.card := Set.ncard_coe_finset S
  have h3 : ((Ideal.span ((algebraMap A (Localization.AtPrime (Ideal.span (S : Set A)))) ''
      (S : Set A))).spanFinrank : ℕ∞) ≤ (Ideal.span (S : Set A)).height :=
    le_trans (by exact_mod_cast h1.trans h2) h
  exact_mod_cast (WithBot.coe_le_coe.mpr h3)

theorem one_le_height_of_bot_lt [IsDomain A] (P : Ideal A) [P.IsPrime] (hP : ⊥ < P) :
    (1 : ℕ∞) ≤ P.height := by
  have h := Ideal.height_strict_mono_of_isPrime_of_isPrime (I := (⊥ : Ideal A)) (J := P) hP
  rw [Ideal.height_bot] at h
  exact Order.one_le_iff_pos.mpr h

theorem two_le_height_of_lt_of_lt [IsDomain A] (Q P : Ideal A) [Q.IsPrime] [P.IsPrime]
    (hQ : ⊥ < Q) (hQP : Q < P) : (2 : ℕ∞) ≤ P.height := by
  have h1 := one_le_height_of_bot_lt Q hQ
  have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hQP
  have h12 : (1 : ℕ∞) < P.height := lt_of_le_of_lt h1 h2
  have := Order.add_one_le_of_lt h12
  simpa [one_add_one_eq_two] using this

theorem isRegularLocalRing_of_mem_of_ker_eq_span [IsDomain A] {D : Type*} [CommRing D]
    [IsDomain D] [IsPrincipalIdealRing D] (ρ : A →+* D) (hρ : Function.Surjective ρ)
    {z : A} (hz : z ≠ 0) (hker : RingHom.ker ρ = Ideal.span {z})
    (P : Ideal A) [hP : P.IsPrime] (hzP : z ∈ P) : IsRegularLocalRing (Localization.AtPrime P) := by
  classical
  have hkerP : RingHom.ker ρ ≤ P := by
    rw [hker, Ideal.span_singleton_le_iff_mem]; exact hzP

  haveI hzprime : (Ideal.span {z} : Ideal A).IsPrime := by
    rw [← hker]; exact RingHom.ker_isPrime ρ
  have hbot : (⊥ : Ideal A) < Ideal.span {z} := by
    rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]; exact hz

  haveI hmapP : (P.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hρ hkerP
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (P.map ρ)).principal
  obtain ⟨G, rfl⟩ := hρ g
  have hPeq : P = Ideal.span {z, G} := by
    have h1 : P = (P.map ρ).comap ρ := by
      rw [Ideal.comap_map_of_surjective _ hρ, ← RingHom.ker_eq_comap_bot,
        left_eq_sup]; exact hkerP
    have h2 : (P.map ρ) = (Ideal.span {G}).map ρ := by
      rw [hg, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]
    rw [h1, h2, Ideal.comap_map_of_surjective _ hρ, ← RingHom.ker_eq_comap_bot, hker,
      ← Ideal.span_union, Set.union_singleton]
  by_cases hPz : P = Ideal.span {z}
  ·
    have hreg := isRegularLocalRing_of_span_eq (Ideal.span {z}) {z} (by simp)
      (by simpa using one_le_height_of_bot_lt (Ideal.span {z}) hbot)
    subst hPz
    exact hreg
  ·
    have hlt : Ideal.span {z} < P :=
      lt_of_le_of_ne (by rw [Ideal.span_singleton_le_iff_mem]; exact hzP) (Ne.symm hPz)
    have h2 := two_le_height_of_lt_of_lt (Ideal.span {z}) P hbot hlt
    refine isRegularLocalRing_of_span_eq P {z, G} (by rw [hPeq]; simp) ?_
    exact le_trans (by exact_mod_cast Finset.card_le_two) h2

end General

section Chart

variable {R : Type*} [CommRing R] (t : R)

open MvPolynomial.CrossingQuotient

local notation "𝔵" => (MvPolynomial.CrossingQuotient.mk t (MvPolynomial.X 0))

local notation "𝔶" => (MvPolynomial.CrossingQuotient.mk t (MvPolynomial.X 1))

abbrev rel : MvPolynomial (Fin 2) R := MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C t

theorem xy_eq : 𝔵 * 𝔶 = algebraMap R (CrossingQuotient R t) t := mk_X_mul_mk_X t

theorem mk_C (a : R) : mk t (MvPolynomial.C a) = algebraMap R (CrossingQuotient R t) a := by
  change mk t (algebraMap R (MvPolynomial (Fin 2) R) a) = _
  exact AlgHom.commutes _ a

theorem exists_normalForm (f : CrossingQuotient R t) :
    ∃ p q : Polynomial R, f = Polynomial.aeval 𝔵 p + 𝔶 * Polynomial.aeval 𝔶 q := by
  obtain ⟨F, rfl⟩ := mk_surjective t f
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Polynomial.C a, 0, ?_⟩
    simp only [Polynomial.aeval_C, map_zero, mul_zero, add_zero]
    exact mk_C t a
  | add p q hp hq =>
    obtain ⟨p₁, q₁, h₁⟩ := hp
    obtain ⟨p₂, q₂, h₂⟩ := hq
    refine ⟨p₁ + p₂, q₁ + q₂, ?_⟩
    rw [map_add, h₁, h₂, map_add, map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨P, Q, hPQ⟩ := hp
    have hxy := xy_eq t
    fin_cases i
    ·
      refine ⟨Polynomial.X * P + Polynomial.C (t * Q.coeff 0), Polynomial.C t * Q.divX, ?_⟩
      have hQ : Polynomial.aeval 𝔶 Q = 𝔶 * Polynomial.aeval 𝔶 Q.divX +
          algebraMap R _ (Q.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.zero_eta, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hQ]
      linear_combination (Polynomial.aeval 𝔶 Q.divX * 𝔶 + (algebraMap R _ (Q.coeff 0))) * hxy
    ·
      refine ⟨Polynomial.C t * P.divX, Polynomial.C (P.coeff 0) + Polynomial.X * Q, ?_⟩
      have hP : Polynomial.aeval 𝔵 P = 𝔵 * Polynomial.aeval 𝔵 P.divX +
          algebraMap R _ (P.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add P]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.mk_one, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hP]
      linear_combination (Polynomial.aeval 𝔵 P.divX) * hxy

abbrev Resid : Type _ := R ⧸ Ideal.span ({t} : Set R)

theorem algebraMap_resid_t : algebraMap R (Polynomial (Resid t)) t = 0 := by
  rw [Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t), map_zero]

noncomputable def branchY : CrossingQuotient R t →ₐ[R] Polynomial (Resid t) :=
  Ideal.Quotient.liftₐ (Ideal.span {rel t})
    (MvPolynomial.aeval ![(0 : Polynomial (Resid t)), Polynomial.X]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [algebraMap_resid_t t])

noncomputable def branchX : CrossingQuotient R t →ₐ[R] Polynomial (Resid t) :=
  Ideal.Quotient.liftₐ (Ideal.span {rel t})
    (MvPolynomial.aeval ![Polynomial.X, (0 : Polynomial (Resid t))]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [algebraMap_resid_t t])

theorem branchY_mk (F : MvPolynomial (Fin 2) R) :
    branchY t (mk t F) = MvPolynomial.aeval ![(0 : Polynomial (Resid t)), Polynomial.X] F := rfl

theorem branchX_mk (F : MvPolynomial (Fin 2) R) :
    branchX t (mk t F) = MvPolynomial.aeval ![Polynomial.X, (0 : Polynomial (Resid t))] F := rfl

@[scoped simp] theorem branchY_x : branchY t 𝔵 = 0 := by
  rw [branchY_mk, MvPolynomial.aeval_X]; rfl

@[scoped simp] theorem branchY_y : branchY t 𝔶 = Polynomial.X := by
  rw [branchY_mk, MvPolynomial.aeval_X]; rfl

@[scoped simp] theorem branchX_x : branchX t 𝔵 = Polynomial.X := by
  rw [branchX_mk, MvPolynomial.aeval_X]; rfl

@[scoped simp] theorem branchX_y : branchX t 𝔶 = 0 := by
  rw [branchX_mk, MvPolynomial.aeval_X]; rfl

theorem branchY_aeval_x (p : Polynomial R) :
    branchY t (Polynomial.aeval 𝔵 p) = Polynomial.C (algebraMap R (Resid t) (p.coeff 0)) := by
  rw [← Polynomial.aeval_algHom_apply, branchY_x, ← Polynomial.coeff_zero_eq_aeval_zero',
    Polynomial.algebraMap_apply]

theorem branchY_aeval_y (q : Polynomial R) :
    branchY t (Polynomial.aeval 𝔶 q) = q.map (algebraMap R (Resid t)) := by
  rw [← Polynomial.aeval_algHom_apply, branchY_y, Polynomial.aeval_X_left_eq_map]

theorem branchX_aeval_x (p : Polynomial R) :
    branchX t (Polynomial.aeval 𝔵 p) = p.map (algebraMap R (Resid t)) := by
  rw [← Polynomial.aeval_algHom_apply, branchX_x, Polynomial.aeval_X_left_eq_map]

theorem branchX_aeval_y (q : Polynomial R) :
    branchX t (Polynomial.aeval 𝔶 q) = Polynomial.C (algebraMap R (Resid t) (q.coeff 0)) := by
  rw [← Polynomial.aeval_algHom_apply, branchX_y, ← Polynomial.coeff_zero_eq_aeval_zero',
    Polynomial.algebraMap_apply]

theorem branchY_surjective : Function.Surjective (branchY t) := fun g => by
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (algebraMap R (Resid t))
    Ideal.Quotient.mk_surjective g
  exact ⟨Polynomial.aeval 𝔶 G, by rw [branchY_aeval_y, hG]⟩

theorem branchX_surjective : Function.Surjective (branchX t) := fun g => by
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (algebraMap R (Resid t))
    Ideal.Quotient.mk_surjective g
  exact ⟨Polynomial.aeval 𝔵 G, by rw [branchX_aeval_x, hG]⟩

theorem exists_eq_C_mul_of_map_eq_zero {q : Polynomial R} (hq : q.map (algebraMap R (Resid t)) = 0) :
    ∃ q' : Polynomial R, q' * Polynomial.C t = q := by
  have : q ∈ RingHom.ker (Polynomial.mapRingHom (algebraMap R (Resid t))) := hq
  rw [Polynomial.ker_mapRingHom, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, Ideal.map_span,
    Set.image_singleton] at this
  exact Ideal.mem_span_singleton'.mp this

theorem ker_branchY : RingHom.ker (branchY t) = Ideal.span {𝔵} := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨p, q, rfl⟩ := exists_normalForm t f
    rw [map_add, map_mul, branchY_aeval_x, branchY_y, branchY_aeval_y] at hf
    have hq : q.map (algebraMap R (Resid t)) = 0 := by
      ext n
      have := congrArg (fun g => Polynomial.coeff g (n+1)) hf
      simpa [Polynomial.coeff_C, Polynomial.coeff_X_mul] using this
    have hp0 : algebraMap R (Resid t) (p.coeff 0) = 0 := by
      have := congrArg (fun g => Polynomial.coeff g 0) hf
      simpa [hq] using this
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hp0
    obtain ⟨a, ha⟩ := hp0
    obtain ⟨q', hq'⟩ := exists_eq_C_mul_of_map_eq_zero t hq
    have hP : Polynomial.aeval 𝔵 p = 𝔵 * Polynomial.aeval 𝔵 p.divX +
        algebraMap R _ (p.coeff 0) := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add p]
      simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [Ideal.mem_span_singleton']
    refine ⟨Polynomial.aeval 𝔵 p.divX + 𝔶 * algebraMap R _ a + 𝔶 * 𝔶 * Polynomial.aeval 𝔶 q',
      ?_⟩
    rw [hP, ← ha, ← hq', map_mul, map_mul, Polynomial.aeval_C]
    linear_combination (𝔶 * Polynomial.aeval 𝔶 q' + algebraMap R _ a) * xy_eq t
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, branchY_x]

theorem ker_branchX : RingHom.ker (branchX t) = Ideal.span {𝔶} := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨p, q, rfl⟩ := exists_normalForm t f
    rw [map_add, map_mul, branchX_aeval_x, branchX_y, zero_mul, add_zero] at hf
    obtain ⟨p', hp'⟩ := exists_eq_C_mul_of_map_eq_zero t hf
    rw [Ideal.mem_span_singleton']
    refine ⟨𝔵 * Polynomial.aeval 𝔵 p' + Polynomial.aeval 𝔶 q, ?_⟩
    rw [← hp', map_mul, Polynomial.aeval_C]
    linear_combination (Polynomial.aeval 𝔵 p') * xy_eq t
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, branchX_y]

theorem x_ne_zero [Nontrivial (Resid t)] : (𝔵 : CrossingQuotient R t) ≠ 0 := by
  intro h
  have := congrArg (branchX t) h
  rw [branchX_x, map_zero] at this
  exact Polynomial.X_ne_zero this

theorem y_ne_zero [Nontrivial (Resid t)] : (𝔶 : CrossingQuotient R t) ≠ 0 := by
  intro h
  have := congrArg (branchY t) h
  rw [branchY_y, map_zero] at this
  exact Polynomial.X_ne_zero this

theorem eq_zero_of_algebraMap_mul_eq_zero [IsDomain R] (ht : t ≠ 0)
    [hprime : (Ideal.span ({t} : Set R)).IsPrime]
    {f : CrossingQuotient R t} (h : algebraMap R (CrossingQuotient R t) t * f = 0) : f = 0 := by
  obtain ⟨F, rfl⟩ := mk_surjective t f
  rw [← mk_C, ← map_mul, mk_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton'] at h
  obtain ⟨G, hG⟩ := h

  let red : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) (Resid t) :=
    MvPolynomial.map (Ideal.Quotient.mk _)
  have hredt : red (C t) = 0 := by
    simp only [red, MvPolynomial.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton t)), C_0]
  have hred : red G * (X 0 * X 1) = 0 := by
    have := congrArg red hG
    rw [map_mul, map_mul, hredt, zero_mul, map_sub, hredt, sub_zero, map_mul,
      MvPolynomial.map_X, MvPolynomial.map_X] at this
    exact this
  have hX : (X 0 * X 1 : MvPolynomial (Fin 2) (Resid t)) ≠ 0 :=
    mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)
  have hG0 : red G = 0 := (mul_eq_zero.mp hred).resolve_right hX
  have hGmem : G ∈ Ideal.span {(C t : MvPolynomial (Fin 2) R)} := by
    have : G ∈ RingHom.ker red := hG0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at this
    exact this
  obtain ⟨G', rfl⟩ := Ideal.mem_span_singleton'.mp hGmem
  have hCt : (C t : MvPolynomial (Fin 2) R) ≠ 0 := by
    rwa [Ne, MvPolynomial.C_eq_zero]
  have hF : F = G' * rel t := by
    apply mul_left_cancel₀ hCt
    rw [← hG]; ring
  rw [mk_apply, Ideal.Quotient.eq_zero_iff_mem, hF]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

end Chart

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

open MvPolynomial.CrossingQuotient

local notation "𝔵" => (MvPolynomial.CrossingQuotient.mk ϖ (MvPolynomial.X 0))
local notation "𝔶" => (MvPolynomial.CrossingQuotient.mk ϖ (MvPolynomial.X 1))

local notation "𝔸" => (CrossingQuotient R ϖ)

local notation "ϖA" => (algebraMap R (CrossingQuotient R ϖ) ϖ)

local notation "𝔸ϖ" => (Localization.Away (algebraMap R (CrossingQuotient R ϖ) ϖ))

local notation "𝕂" => (FractionRing R)

local notation "𝕃" => (LaurentPolynomial (FractionRing R))

theorem span_eq_maximalIdeal (hϖ : Irreducible ϖ) : Ideal.span {ϖ} = maximalIdeal R :=
  ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ).symm

theorem isMaximal_span (hϖ : Irreducible ϖ) : (Ideal.span ({ϖ} : Set R)).IsMaximal := by
  rw [span_eq_maximalIdeal hϖ]; infer_instance

theorem ϖK_ne_zero (hϖ : Irreducible ϖ) : algebraMap R 𝕂 ϖ ≠ 0 := fun h =>
  hϖ.ne_zero ((IsFractionRing.injective R 𝕂) (by rw [h, map_zero]))

theorem isUnit_algebraMap_ϖ : IsUnit (algebraMap R 𝔸ϖ ϖ) := by
  rw [IsScalarTower.algebraMap_apply R 𝔸 𝔸ϖ]
  exact IsLocalization.Away.algebraMap_isUnit ϖA

theorem isUnit_algebraMap_of_mem_nonZeroDivisors (hϖ : Irreducible ϖ)
    (y : nonZeroDivisors R) : IsUnit (algebraMap R 𝔸ϖ y) := by
  have hy : (y : R) ≠ 0 := nonZeroDivisors.ne_zero y.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [hu, map_mul, map_pow]
  exact (u.isUnit.map _).mul (isUnit_algebraMap_ϖ.pow n)

noncomputable def ι (hϖ : Irreducible ϖ) : 𝕂 →+* 𝔸ϖ :=
  IsLocalization.lift (M := nonZeroDivisors R) (g := algebraMap R 𝔸ϖ)
    (isUnit_algebraMap_of_mem_nonZeroDivisors hϖ)

theorem ι_algebraMap (hϖ : Irreducible ϖ) (r : R) : ι hϖ (algebraMap R 𝕂 r) = algebraMap R 𝔸ϖ r :=
  IsLocalization.lift_eq _ r

noncomputable def φ₀ : 𝔸 →ₐ[R] 𝕃 :=
  Ideal.Quotient.liftₐ (Ideal.span {rel ϖ})
    (MvPolynomial.aeval ![(LaurentPolynomial.T 1 : 𝕃), LaurentPolynomial.C (algebraMap R 𝕂 ϖ) * LaurentPolynomial.T (-1)]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, LaurentPolynomial.algebraMap_apply]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [mul_left_comm, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, mul_one, sub_self, mul_zero])

theorem φ₀_mk (F : MvPolynomial (Fin 2) R) : φ₀ (mk ϖ F) =
    MvPolynomial.aeval ![(LaurentPolynomial.T 1 : 𝕃), LaurentPolynomial.C (algebraMap R 𝕂 ϖ) * LaurentPolynomial.T (-1)] F := rfl

theorem φ₀_x : φ₀ 𝔵 = (LaurentPolynomial.T 1 : 𝕃) := by rw [φ₀_mk, MvPolynomial.aeval_X]; rfl

theorem φ₀_y : φ₀ 𝔶 = LaurentPolynomial.C (algebraMap R 𝕂 ϖ) * (LaurentPolynomial.T (-1) : 𝕃) := by
  rw [φ₀_mk, MvPolynomial.aeval_X]; rfl

theorem φ₀_algebraMap (r : R) : φ₀ (algebraMap R 𝔸 r) = LaurentPolynomial.C (algebraMap R 𝕂 r) := by
  rw [AlgHom.commutes, LaurentPolynomial.algebraMap_apply]

theorem isUnit_φ₀_ϖA (hϖ : Irreducible ϖ) : IsUnit (φ₀.toRingHom ϖA) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, φ₀_algebraMap]
  exact ((ϖK_ne_zero hϖ).isUnit).map _

noncomputable def φ (hϖ : Irreducible ϖ) : 𝔸ϖ →+* 𝕃 :=
  IsLocalization.Away.lift (S := 𝔸ϖ) ϖA (g := φ₀.toRingHom) (isUnit_φ₀_ϖA hϖ)

theorem φ_algebraMap (hϖ : Irreducible ϖ) (a : 𝔸) : φ hϖ (algebraMap 𝔸 𝔸ϖ a) = φ₀ a :=
  IsLocalization.Away.lift_eq (S := 𝔸ϖ) ϖA (isUnit_φ₀_ϖA hϖ) a

theorem xϖ_mul_yϖ : algebraMap 𝔸 𝔸ϖ 𝔵 * algebraMap 𝔸 𝔸ϖ 𝔶 = algebraMap R 𝔸ϖ ϖ := by
  rw [← map_mul, xy_eq, ← IsScalarTower.algebraMap_apply]

theorem isUnit_xϖ : IsUnit (algebraMap 𝔸 𝔸ϖ 𝔵) :=
  isUnit_of_mul_isUnit_left (by rw [xϖ_mul_yϖ]; exact isUnit_algebraMap_ϖ)

noncomputable def ψ₁ (hϖ : Irreducible ϖ) : Polynomial (FractionRing R) →+* 𝔸ϖ :=
  Polynomial.eval₂RingHom (ι hϖ) (algebraMap 𝔸 𝔸ϖ 𝔵)

noncomputable def ψ (hϖ : Irreducible ϖ) : 𝕃 →+* 𝔸ϖ :=
  IsLocalization.Away.lift (Polynomial.X : Polynomial (FractionRing R)) (g := ψ₁ hϖ)
    (by rw [ψ₁, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]; exact isUnit_xϖ)

theorem ψ_toLaurent (hϖ : Irreducible ϖ) (p : Polynomial (FractionRing R)) :
    ψ hϖ (Polynomial.toLaurent p) = ψ₁ hϖ p := by
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.Away.lift_eq _ _ p

theorem ψ_T_one (hϖ : Irreducible ϖ) : ψ hϖ (LaurentPolynomial.T 1) = algebraMap 𝔸 𝔸ϖ 𝔵 := by
  rw [← Polynomial.toLaurent_X, ψ_toLaurent, ψ₁, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

theorem ψ_C (hϖ : Irreducible ϖ) (a : 𝕂) : ψ hϖ (LaurentPolynomial.C a) = ι hϖ a := by
  rw [← Polynomial.toLaurent_C, ψ_toLaurent, ψ₁, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

theorem ψ_comp_φ (hϖ : Irreducible ϖ) : (ψ hϖ).comp (φ hϖ) = RingHom.id 𝔸ϖ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers ϖA)
  rw [RingHom.comp_assoc, φ, IsLocalization.Away.lift_comp, RingHom.id_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    show ψ hϖ (φ₀ (mk ϖ (C a))) = algebraMap 𝔸 𝔸ϖ (mk ϖ (C a))
    rw [mk_C, φ₀_algebraMap, ψ_C, ι_algebraMap, ← IsScalarTower.algebraMap_apply]
  · intro i
    fin_cases i
    · show ψ hϖ (φ₀ 𝔵) = algebraMap 𝔸 𝔸ϖ 𝔵
      rw [φ₀_x, ψ_T_one]
    · show ψ hϖ (φ₀ 𝔶) = algebraMap 𝔸 𝔸ϖ 𝔶
      rw [φ₀_y, map_mul, ψ_C, ι_algebraMap]
      have h1 : ψ hϖ (LaurentPolynomial.T (-1)) * algebraMap 𝔸 𝔸ϖ 𝔵 = 1 := by
        rw [← ψ_T_one hϖ, ← map_mul, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, map_one]
      have h2 := xϖ_mul_yϖ (ϖ := ϖ)
      linear_combination (algebraMap 𝔸 𝔸ϖ 𝔶) * h1 - (ψ hϖ (LaurentPolynomial.T (-1))) * h2

theorem φ_comp_ι (hϖ : Irreducible ϖ) : (φ hϖ).comp (ι hϖ) = LaurentPolynomial.C := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [ι_algebraMap, IsScalarTower.algebraMap_apply R 𝔸 𝔸ϖ, φ_algebraMap, φ₀_algebraMap]

theorem φ_comp_ψ (hϖ : Irreducible ϖ) : (φ hϖ).comp (ψ hϖ) = RingHom.id 𝕃 := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial (FractionRing R)))
  rw [RingHom.comp_assoc, ψ, IsLocalization.Away.lift_comp, RingHom.id_comp]
  apply Polynomial.ringHom_ext
  · intro a
    show φ hϖ (ψ₁ hϖ (Polynomial.C a)) = algebraMap _ 𝕃 (Polynomial.C a)
    rw [ψ₁, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C]
    exact RingHom.congr_fun (φ_comp_ι hϖ) a
  · show φ hϖ (ψ₁ hϖ Polynomial.X) = algebraMap _ 𝕃 Polynomial.X
    rw [ψ₁, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, φ_algebraMap, φ₀_x,
      LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]

noncomputable def awayEquivLaurent (hϖ : Irreducible ϖ) : 𝔸ϖ ≃+* 𝕃 :=
  RingEquiv.ofRingHom (φ hϖ) (ψ hϖ) (φ_comp_ψ hϖ) (ψ_comp_φ hϖ)

theorem isRegularRing_laurent : IsRegularRing 𝕃 := by
  haveI := isRegularRing_localization (A := Polynomial (FractionRing R))
    (Submonoid.powers (Polynomial.X : Polynomial (FractionRing R)))
  exact IsRegularRing.of_ringEquiv (IsLocalization.algEquiv
    (Submonoid.powers (Polynomial.X : Polynomial (FractionRing R)))
    (Localization.Away (Polynomial.X : Polynomial (FractionRing R))) 𝕃).toRingEquiv

theorem isRegularRing_away (hϖ : Irreducible ϖ) : IsRegularRing 𝔸ϖ := by
  haveI := isRegularRing_laurent (R := R)
  exact IsRegularRing.of_ringEquiv (awayEquivLaurent hϖ).symm

theorem isDomain_away (hϖ : Irreducible ϖ) : IsDomain 𝔸ϖ :=
  MulEquiv.isDomain 𝕃 (awayEquivLaurent hϖ).toMulEquiv

theorem ϖA_mem_nonZeroDivisors (hϖ : Irreducible ϖ) : ϖA ∈ nonZeroDivisors 𝔸 := by
  haveI := (isMaximal_span hϖ).isPrime
  refine mem_nonZeroDivisors_iff.mpr ⟨fun f hf => ?_, fun f hf => ?_⟩
  · exact eq_zero_of_algebraMap_mul_eq_zero ϖ hϖ.ne_zero hf
  · exact eq_zero_of_algebraMap_mul_eq_zero ϖ hϖ.ne_zero (by rwa [mul_comm] at hf)

private theorem _root_.CrossingResolutionR1.isDomain (hϖ : Irreducible ϖ) : IsDomain 𝔸 := by
  haveI := isDomain_away hϖ
  refine Function.Injective.isDomain (algebraMap 𝔸 𝔸ϖ) ?_
  exact IsLocalization.injective 𝔸ϖ (M := Submonoid.powers ϖA)
    ((Submonoid.powers_le).mpr (ϖA_mem_nonZeroDivisors hϖ))

p2m_export "CrossingResolutionR1" "isDomain"

theorem isRegularRing_crossingQuotient (hϖ : Irreducible ϖ) : IsRegularRing 𝔸 := by
  classical
  haveI hmaxI : (Ideal.span ({ϖ} : Set R)).IsMaximal := isMaximal_span hϖ
  letI : Field (Resid ϖ) := Ideal.Quotient.field _
  haveI : IsDomain 𝔸 := isDomain hϖ
  haveI : IsRegularRing 𝔸ϖ := isRegularRing_away hϖ
  rw [isRegularRing_iff]
  intro P hP
  by_cases hx : 𝔵 ∈ P
  · exact isRegularLocalRing_of_mem_of_ker_eq_span (branchY ϖ : 𝔸 →+* Polynomial (Resid ϖ))
      (branchY_surjective ϖ) (x_ne_zero ϖ) (ker_branchY ϖ) P hx
  by_cases hy : 𝔶 ∈ P
  · exact isRegularLocalRing_of_mem_of_ker_eq_span (branchX ϖ : 𝔸 →+* Polynomial (Resid ϖ))
      (branchX_surjective ϖ) (y_ne_zero ϖ) (ker_branchX ϖ) P hy
  have hϖP : ϖA ∉ P := fun h => by
    rw [← xy_eq] at h
    exact (hP.mem_or_mem h).elim hx hy
  exact isRegularLocalRing_atPrime_of_disjoint (Submonoid.powers ϖA) P
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime (I := P) ϖA).mpr hϖP)

end DVR

end

end CrossingResolutionR1
p2m_reactivate "P2MW.S_MvPolynomial_CrossingQuotient_isRegularRing_of_irreducible.CrossingResolutionR1"

open MvPolynomial MvPolynomial.CrossingQuotient in

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsRegularRing (CrossingQuotient R ϖ) :=
  CrossingResolutionR1.isRegularRing_crossingQuotient hϖ

end S_MvPolynomial_CrossingQuotient_isRegularRing_of_irreducible
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_isRegularRing_of_irreducible (solution)
