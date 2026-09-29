-- Prove2me | solution 1 for IsLocalRing.exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f97ac812-6f52-55ef-a46c-20e6b0660d67

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq

set_option autoImplicit false
set_option maxHeartbeats 3200000

universe u v w

open IsLocalRing Polynomial

namespace P2M
namespace WittTwoLift

theorem map_eval₂_int {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (P : ℤ[X]) (t : A) :
    f (P.eval₂ (Int.castRingHom A) t) = P.eval₂ (Int.castRingHom B) (f t) := by
  rw [Polynomial.hom_eval₂, RingHom.ext_int (f.comp (Int.castRingHom A)) (Int.castRingHom B)]

theorem newton {A : Type*} [CommRing A] (P : ℤ[X]) (t u : A)
    (hu : u * P.derivative.eval₂ (Int.castRingHom A) t = 1)
    (hsq : P.eval₂ (Int.castRingHom A) t * P.eval₂ (Int.castRingHom A) t = 0) :
    P.eval₂ (Int.castRingHom A) (t + -(P.eval₂ (Int.castRingHom A) t * u)) = 0 := by
  set y := -(P.eval₂ (Int.castRingHom A) t * u) with hy
  have hy2 : y ^ 2 = 0 := by
    rw [hy]; linear_combination (u * u) * hsq
  have h := Polynomial.eval_add_of_sq_eq_zero (P.map (Int.castRingHom A)) t y hy2
  rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval_map, Polynomial.eval_map] at h
  rw [h, hy]
  have : P.eval₂ (Int.castRingHom A) t + (derivative P).eval₂ (Int.castRingHom A) t *
      -(P.eval₂ (Int.castRingHom A) t * u) =
      P.eval₂ (Int.castRingHom A) t * (1 - u * (derivative P).eval₂ (Int.castRingHom A) t) := by ring
  rw [this, hu, sub_self, mul_zero]

theorem exists_eq_C_mul_of_map_eq_zero {q : ℕ} (hq : q ≠ 0) (B : ℤ[X])
    (hB : B.map (Int.castRingHom (ZMod q)) = 0) : ∃ B' : ℤ[X], B = C (q : ℤ) * B' ∧ B'.degree = B.degree := by
  have hker : B ∈ RingHom.ker (Polynomial.mapRingHom (Int.castRingHom (ZMod q))) := hB
  rw [Polynomial.ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hker
  obtain ⟨B', hB'⟩ := hker
  refine ⟨B', hB', ?_⟩
  rw [hB', Polynomial.degree_C_mul]
  exact_mod_cast hq

theorem main
    {q : ℕ} [hqp : Fact q.Prime] {S : Type u} [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] [CharP (ResidueField S) q]
    (hq : ((q : ℕ) : S) ∉ maximalIdeal S ^ 2)
    {D : Type v} [CommRing D] [IsLocalRing D] (hD : maximalIdeal D ^ 2 = ⊥)
    {K : Type w} [Field K] (πD : D →+* K) (hπD : Function.Surjective πD)
    (x : S →+* K) (hx : RingHom.ker x = maximalIdeal S) :
    ∃ ψ : S →+* D, πD.comp ψ = x := by
  classical
  set 𝔪 : Ideal S := maximalIdeal S with h𝔪
  have hqm : ((q : ℕ) : S) ∈ 𝔪 := by
    rw [h𝔪, ← residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ _

  have hxker : ∀ a ∈ 𝔪, x a = 0 := fun a ha => by rwa [← RingHom.mem_ker, hx]
  set ι : ResidueField S →+* K := Ideal.Quotient.lift 𝔪 x hxker with hιdef
  have hι : ∀ s, ι (residue S s) = x s := fun s => Ideal.Quotient.lift_mk _ _ hxker

  have hqK : ((q : ℕ) : K) = 0 := by rw [← map_natCast ι, CharP.cast_eq_zero, map_zero]
  have hkerπ : RingHom.ker πD = maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective πD hπD)
  have hmemD : ∀ d : D, d ∈ maximalIdeal D ↔ πD d = 0 := fun d => by rw [← hkerπ, RingHom.mem_ker]
  have hqD : ((q : ℕ) : D) ∈ maximalIdeal D := by rw [hmemD, map_natCast, hqK]
  have hDmul : ∀ d ∈ maximalIdeal D, ∀ d' ∈ maximalIdeal D, d * d' = 0 := fun d hd d' hd' => by
    have : d * d' ∈ maximalIdeal D ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hd hd'
    rwa [hD, Ideal.mem_bot] at this
  have hqD2 : ((q : ℕ) : D) * (q : ℕ) = 0 := hDmul _ hqD _ hqD

  set qbar : CotangentSpace S := 𝔪.toCotangent ⟨(q : ℕ), hqm⟩ with hqbar
  have hqbar0 : qbar ≠ 0 := fun h => hq ((Ideal.toCotangent_eq_zero 𝔪 _).mp h)
  obtain ⟨lam0, hlam0⟩ : ∃ lam : Module.Dual (ResidueField S) (CotangentSpace S), lam qbar ≠ 0 := by
    by_contra h
    push Not at h
    exact hqbar0 ((Module.forall_dual_apply_eq_zero_iff (ResidueField S) qbar).mp h)
  set lam : Module.Dual (ResidueField S) (CotangentSpace S) := (lam0 qbar)⁻¹ • lam0 with hlam
  have hlamq : lam qbar = 1 := by
    rw [hlam, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hlam0]

  have hsmul : ∀ (a : S) (y : CotangentSpace S), a • y = residue S a • y := fun a y => by
    rw [← IsScalarTower.algebraMap_smul (ResidueField S) a y]; rfl
  set L : 𝔪 → ResidueField S := fun m => lam (𝔪.toCotangent m) with hL
  have hL_add : ∀ m m' : 𝔪, L (m + m') = L m + L m' := fun m m' => by simp only [hL, map_add]
  have hL_smul : ∀ (a : S) (m : 𝔪), L (a • m) = residue S a * L m := fun a m => by
    simp only [hL, map_smul, hsmul, smul_eq_mul]
  have hL_sq : ∀ (m : 𝔪), (m : S) ∈ 𝔪 ^ 2 → L m = 0 := fun m hm => by
    simp only [hL]; rw [(Ideal.toCotangent_eq_zero 𝔪 m).mpr hm, map_zero]
  have hL_q : L ⟨(q : ℕ), hqm⟩ = 1 := hlamq

  let J : Ideal S :=
    { carrier := {s | ∃ h : s ∈ 𝔪, L ⟨s, h⟩ = 0}
      add_mem' := by
        rintro a b ⟨ha, hLa⟩ ⟨hb, hLb⟩
        refine ⟨add_mem ha hb, ?_⟩
        have : (⟨a + b, add_mem ha hb⟩ : 𝔪) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [this, hL_add, hLa, hLb, add_zero]
      zero_mem' := ⟨zero_mem _, by
        have h0 : (⟨0, zero_mem 𝔪⟩ : 𝔪) = 0 := rfl
        simp only [hL, h0, map_zero]⟩
      smul_mem' := by
        rintro c a ⟨ha, hLa⟩
        refine ⟨Ideal.mul_mem_left _ c ha, ?_⟩
        have : (⟨c • a, Ideal.mul_mem_left _ c ha⟩ : 𝔪) = c • ⟨a, ha⟩ := rfl
        rw [this, hL_smul, hLa, mul_zero] }
  have hJmem : ∀ s, s ∈ J ↔ ∃ h : s ∈ 𝔪, L ⟨s, h⟩ = 0 := fun s => Iff.rfl
  have hJle : J ≤ 𝔪 := fun s hs => ((hJmem s).mp hs).1
  have hJsq : 𝔪 ^ 2 ≤ J := fun s hs => (hJmem s).mpr ⟨Ideal.pow_le_self two_ne_zero hs, hL_sq _ hs⟩
  have hqJ : ((q : ℕ) : S) ∉ J := fun h => by
    obtain ⟨h', hL0⟩ := (hJmem _).mp h
    rw [hL_q] at hL0; exact one_ne_zero hL0
  have hmJ : ∀ m ∈ 𝔪, ∃ c : S, m - c * (q : ℕ) ∈ J := by
    intro m hm
    obtain ⟨c, hc⟩ := residue_surjective (L ⟨m, hm⟩)
    refine ⟨c, (hJmem _).mpr ⟨sub_mem hm (Ideal.mul_mem_left _ c hqm), ?_⟩⟩
    have : (⟨m - c * (q : ℕ), sub_mem hm (Ideal.mul_mem_left _ c hqm)⟩ : 𝔪) =
        ⟨m, hm⟩ + (-c) • ⟨(q : ℕ), hqm⟩ := by
      apply Subtype.ext; change m - c * (q : ℕ) = m + (-c) • ((q : ℕ) : S); rw [smul_eq_mul]; ring
    rw [this, hL_add, hL_smul, hL_q, mul_one, map_neg, hc, add_neg_cancel]

  set S₁ := S ⧸ J
  set mk₁ : S →+* S₁ := Ideal.Quotient.mk J with hmk₁
  have hJker : ∀ a ∈ J, residue S a = 0 := fun a ha => (residue_eq_zero_iff a).mpr (hJle ha)
  set ρ : S₁ →+* ResidueField S := Ideal.Quotient.lift J (residue S) hJker with hρ
  have hρmk : ∀ s, ρ (mk₁ s) = residue S s := fun s => Ideal.Quotient.lift_mk J _ hJker

  have hM_iff : ∀ s : S, ρ (mk₁ s) = 0 ↔ s ∈ 𝔪 := fun s => by rw [hρmk, residue_eq_zero_iff]
  have hM_mul : ∀ z z' : S₁, ρ z = 0 → ρ z' = 0 → z * z' = 0 := by
    intro z z' hz hz'
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective z'
    change ρ (mk₁ s) = 0 at hz; change ρ (mk₁ s') = 0 at hz'
    rw [hM_iff] at hz hz'
    change mk₁ s * mk₁ s' = 0
    rw [← map_mul, hmk₁, Ideal.Quotient.eq_zero_iff_mem]
    exact hJsq (by rw [pow_two]; exact Ideal.mul_mem_mul hz hz')
  have hM_q : ∀ z : S₁, ρ z = 0 → ∃ c : S₁, z = (q : ℕ) * c := by
    intro z hz
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
    change ρ (mk₁ s) = 0 at hz
    rw [hM_iff] at hz
    obtain ⟨c, hc⟩ := hmJ s hz
    refine ⟨mk₁ c, ?_⟩
    change mk₁ s = (q : ℕ) * mk₁ c
    rw [← map_natCast mk₁, ← map_mul, ← sub_eq_zero, ← map_sub, hmk₁, Ideal.Quotient.eq_zero_iff_mem, mul_comm]
    exact hc
  have hq₁ : ρ ((q : ℕ) : S₁) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero _ _
  have hq₁ne : ((q : ℕ) : S₁) ≠ 0 := by
    rw [← map_natCast mk₁, hmk₁, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hqJ
  have hunit₁ : ∀ z : S₁, ρ z ≠ 0 → IsUnit z := by
    intro z hz
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
    change ρ (mk₁ s) ≠ 0 at hz
    rw [Ne, hM_iff] at hz
    exact (notMem_maximalIdeal.mp hz).map mk₁
  have hAnn : ∀ z : S₁, (q : ℕ) * z = 0 → ρ z = 0 := by
    intro z hz
    by_contra hne
    obtain ⟨w, hw⟩ := (hunit₁ z hne).exists_right_inv
    apply hq₁ne
    rw [← mul_one ((q : ℕ) : S₁), ← hw, ← mul_assoc, hz, zero_mul]

  letI : Fintype (ResidueField S) := Fintype.ofFinite _
  letI algZ : Algebra (ZMod q) (ResidueField S) := ZMod.algebra _ q
  obtain ⟨θbar, hθbar⟩ := Field.exists_primitive_element (ZMod q) (ResidueField S)
  have hθint : IsIntegral (ZMod q) θbar := .of_finite (ZMod q) θbar
  set gbar : (ZMod q)[X] := minpoly (ZMod q) θbar with hgbar
  have hgbar_monic : gbar.Monic := minpoly.monic hθint
  have hgbar_root : aeval θbar gbar = 0 := minpoly.aeval _ _
  have hgbar_sep : gbar.Separable := Algebra.IsSeparable.isSeparable (ZMod q) θbar

  have hgen : ∀ c : ResidueField S, ∃ P : (ZMod q)[X], aeval θbar P = c := by
    intro c
    have hc : c ∈ (IntermediateField.adjoin (ZMod q) {θbar}).toSubalgebra := by
      rw [hθbar]; exact IntermediateField.mem_top
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hc
    obtain ⟨P, hP⟩ := hc
    exact ⟨P, hP⟩

  set red : ℤ →+* ZMod q := Int.castRingHom (ZMod q) with hred
  have hred_surj : Function.Surjective red := ZMod.ringHom_surjective red
  have haeval_red : ∀ (P : ℤ[X]) (c : ResidueField S),
      aeval c (P.map red) = P.eval₂ (Int.castRingHom (ResidueField S)) c := by
    intro P c
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap (ZMod q) (ResidueField S)).comp red) (Int.castRingHom _)]

  obtain ⟨g, hg_map, hg_deg, hg_monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective red hred_surj gbar))
      hgbar_monic

  obtain ⟨θ, hθ⟩ := residue_surjective θbar

  have ev_res : ∀ (P : ℤ[X]) (s : S), residue S (P.eval₂ (Int.castRingHom S) s) =
      aeval (residue S s) (P.map red) := fun P s => by rw [haeval_red, map_eval₂_int]
  have ev_ρ : ∀ (P : ℤ[X]) (s : S), ρ (P.eval₂ (Int.castRingHom S₁) (mk₁ s)) = aeval (residue S s) (P.map red) :=
    fun P s => by rw [← map_eval₂_int mk₁, hρmk, ev_res]

  have hgθ : g.eval₂ (Int.castRingHom S) θ ∈ 𝔪 := by
    rw [h𝔪, ← residue_eq_zero_iff, ev_res, hθ, hg_map]; exact hgbar_root
  have hg'θ : IsUnit ((derivative g).eval₂ (Int.castRingHom S) θ) := by
    rw [← notMem_maximalIdeal, ← h𝔪, h𝔪, ← (residue_eq_zero_iff _).not, ev_res, hθ, ← Polynomial.derivative_map,
      hg_map]
    exact hgbar_sep.aeval_derivative_ne_zero hgbar_root
  obtain ⟨u, hu⟩ := hg'θ.exists_left_inv

  set θ₁ : S := θ + -(g.eval₂ (Int.castRingHom S) θ * u) with hθ₁
  have hθ₁res : residue S θ₁ = θbar := by
    rw [hθ₁, map_add, map_neg, map_mul, (residue_eq_zero_iff _).mpr hgθ, zero_mul, neg_zero, add_zero, hθ]
  have hgθ₁ : g.eval₂ (Int.castRingHom S₁) (mk₁ θ₁) = 0 := by
    have h1 : mk₁ θ₁ = mk₁ θ + -(g.eval₂ (Int.castRingHom S₁) (mk₁ θ) * mk₁ u) := by
      rw [hθ₁, map_add, map_neg, map_mul, map_eval₂_int]
    rw [h1]
    apply newton g (mk₁ θ) (mk₁ u)
    · rw [← map_eval₂_int mk₁, ← map_mul, hu, map_one]
    · apply hM_mul <;> rw [← map_eval₂_int mk₁, hM_iff] <;> exact hgθ

  obtain ⟨η₀, hη₀⟩ := hπD (x θ)
  have hgη₀ : g.eval₂ (Int.castRingHom D) η₀ ∈ maximalIdeal D := by
    rw [hmemD, map_eval₂_int, hη₀, ← hι, ← map_eval₂_int ι, ← map_eval₂_int (residue S), hι]
    exact hxker _ hgθ
  have hg'η₀ : IsUnit ((derivative g).eval₂ (Int.castRingHom D) η₀) := by
    rw [← notMem_maximalIdeal, hmemD, map_eval₂_int, hη₀, ← hι, ← map_eval₂_int ι, ← map_eval₂_int (residue S),
      hι, ← RingHom.mem_ker, hx]
    exact notMem_maximalIdeal.mpr hg'θ
  obtain ⟨uD, huD⟩ := hg'η₀.exists_left_inv
  set η : D := η₀ + -(g.eval₂ (Int.castRingHom D) η₀ * uD) with hη
  have hgη : g.eval₂ (Int.castRingHom D) η = 0 := newton g η₀ uD huD (hDmul _ hgη₀ _ hgη₀)
  have hπη : πD η = x θ := by
    rw [hη, map_add, map_neg, map_mul, (hmemD _).mp hgη₀, zero_mul, neg_zero, add_zero, hη₀]

  set ev₁ : ℤ[X] →+* S₁ := Polynomial.eval₂RingHom (Int.castRingHom S₁) (mk₁ θ₁) with hev₁
  set evD : ℤ[X] →+* D := Polynomial.eval₂RingHom (Int.castRingHom D) η with hevD
  have hev₁_apply : ∀ P, ev₁ P = P.eval₂ (Int.castRingHom S₁) (mk₁ θ₁) := fun P => rfl
  have hevD_apply : ∀ P, evD P = P.eval₂ (Int.castRingHom D) η := fun P => rfl

  have hρev₁ : ∀ P : ℤ[X], ρ (ev₁ P) = aeval θbar (P.map red) := fun P => by
    rw [hev₁_apply, ev_ρ, hθ₁res]

  have happrox : ∀ s : S, ∃ P : ℤ[X], s - P.eval₂ (Int.castRingHom S) θ₁ ∈ 𝔪 := by
    intro s
    obtain ⟨Pbar, hPbar⟩ := hgen (residue S s)
    obtain ⟨P, hP⟩ := Polynomial.map_surjective red hred_surj Pbar
    refine ⟨P, ?_⟩
    rw [h𝔪, ← residue_eq_zero_iff, map_sub, ev_res, hθ₁res, hP, hPbar, sub_self]
  have hev₁_surj : Function.Surjective ev₁ := by
    intro z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨P₀, hP₀⟩ := happrox s
    obtain ⟨c, hc⟩ := hmJ _ hP₀
    obtain ⟨P₁, hP₁⟩ := happrox c
    refine ⟨P₀ + C ((q : ℕ) : ℤ) * P₁, ?_⟩
    change ev₁ (P₀ + C ((q : ℕ) : ℤ) * P₁) = mk₁ s
    rw [map_add, map_mul, hev₁_apply P₀, hev₁_apply P₁, ← map_eval₂_int mk₁, ← map_eval₂_int mk₁, hev₁_apply,
      Polynomial.eval₂_C, map_natCast, ← map_natCast mk₁ q, ← map_mul, ← map_add, eq_comm, ← sub_eq_zero,
      ← map_sub, hmk₁, Ideal.Quotient.eq_zero_iff_mem]
    have : s - (P₀.eval₂ (Int.castRingHom S) θ₁ + (q : ℕ) * P₁.eval₂ (Int.castRingHom S) θ₁) =
        (s - P₀.eval₂ (Int.castRingHom S) θ₁ - c * (q : ℕ)) + (q : ℕ) * (c - P₁.eval₂ (Int.castRingHom S) θ₁) := by
      ring
    rw [this]
    exact add_mem hc (hJsq (by rw [pow_two]; exact Ideal.mul_mem_mul hqm hP₁))

  have hg_natdeg : g.degree = gbar.degree := hg_deg

  have hkey : ∀ B : ℤ[X], B.degree < g.degree → ρ (ev₁ B) = 0 → B.map red = 0 := by
    intro B hB hB0
    by_contra hne
    have h1 : gbar.degree ≤ (B.map red).degree :=
      minpoly.degree_le_of_ne_zero (ZMod q) θbar hne (by rw [← hρev₁]; exact hB0)
    have h2 : (B.map red).degree ≤ B.degree := Polynomial.degree_map_le
    exact absurd (h1.trans h2) (not_le.mpr (hg_natdeg ▸ hB))
  have hkerle : RingHom.ker ev₁ ≤ RingHom.ker evD := by
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢

    set A := P /ₘ g
    set B := P %ₘ g with hBdef
    have hPAB : B + g * A = P := Polynomial.modByMonic_add_div P g
    have hBdeg : B.degree < g.degree := Polynomial.degree_modByMonic_lt P hg_monic
    have hg₁ : ev₁ g = 0 := hgθ₁
    have hB₁ : ev₁ B = 0 := by
      have := congrArg ev₁ hPAB
      rw [map_add, map_mul, hg₁, zero_mul, add_zero, hP] at this
      exact this

    obtain ⟨B', hBB', hB'deg⟩ :=
      exists_eq_C_mul_of_map_eq_zero hqp.out.ne_zero B (hkey B hBdeg (by rw [hB₁, map_zero]))

    have hB'₁ : ρ (ev₁ B') = 0 := by
      apply hAnn
      have := hB₁
      rw [hBB', map_mul, hev₁_apply (C _), Polynomial.eval₂_C, map_natCast] at this
      exact this
    obtain ⟨B'', hB'B'', -⟩ :=
      exists_eq_C_mul_of_map_eq_zero hqp.out.ne_zero B' (hkey B' (hB'deg ▸ hBdeg) hB'₁)

    rw [← hPAB, map_add, map_mul, hevD_apply g, hgη, zero_mul, add_zero, hBB', hB'B'', map_mul, map_mul,
      hevD_apply (C _), Polynomial.eval₂_C, map_natCast, ← mul_assoc, hqD2, zero_mul]

  set ψ₁ : S₁ →+* D :=
    (ev₁.liftOfRightInverse (Function.surjInv hev₁_surj) (Function.rightInverse_surjInv hev₁_surj))
      ⟨evD, hkerle⟩ with hψ₁
  have hψ₁ev : ∀ P, ψ₁ (ev₁ P) = evD P := fun P =>
    RingHom.liftOfRightInverse_comp_apply ev₁ _ _ ⟨evD, hkerle⟩ P
  refine ⟨ψ₁.comp mk₁, ?_⟩

  set x₁ : S₁ →+* K := Ideal.Quotient.lift J x (fun a ha => hxker a (hJle ha)) with hx₁
  have hx₁mk : ∀ s, x₁ (mk₁ s) = x s := fun s => Ideal.Quotient.lift_mk J x _
  have hcomp : (πD.comp ψ₁).comp ev₁ = x₁.comp ev₁ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hψ₁ev, hevD_apply, Polynomial.eval₂_X, hπη,
        hev₁_apply, Polynomial.eval₂_X, hx₁mk, hθ₁, map_add, map_neg, map_mul, hxker _ hgθ, zero_mul, neg_zero,
        add_zero]
  have hcomp' : πD.comp ψ₁ = x₁ := by
    apply RingHom.ext; intro z
    obtain ⟨P, rfl⟩ := hev₁_surj z
    exact congrArg (fun f : ℤ[X] →+* K => f P) hcomp
  ext s
  rw [RingHom.comp_apply, RingHom.comp_apply, ← RingHom.comp_apply πD ψ₁, hcomp', hx₁mk]

end P2M.WittTwoLift

theorem solution
    {q : ℕ} [Fact q.Prime] {S : Type u} [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] [CharP (ResidueField S) q]
    (hq : ((q : ℕ) : S) ∉ maximalIdeal S ^ 2)
    {D : Type v} [CommRing D] [IsLocalRing D] (hD : maximalIdeal D ^ 2 = ⊥)
    {K : Type w} [Field K] (πD : D →+* K) (hπD : Function.Surjective πD)
    (x : S →+* K) (hx : RingHom.ker x = maximalIdeal S) :
    ∃ ψ : S →+* D, πD.comp ψ = x :=
  P2M.WittTwoLift.main hq hD πD hπD x hx

end S_IsLocalRing_exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq
end P2MW
export P2MW.S_IsLocalRing_exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq (solution)
