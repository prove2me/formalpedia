-- Prove2me | solution 1 for MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/247d7560-3dc2-527d-8f7a-2cfe1cb53dc1

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u v w z

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map mk coeff_single_inl toPowerSeries coeff_single_inr assoc constantCoeff_eq_zero adicEval adicEval_coe adicEval_X coe_adicEvalAlgHom adicEval_subst map_adicEval hasSubst_elim"
namespace NilAdicEval
p2m_open "MvFormalGroup"

variable {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Algebra R C] {σ : Type w}

theorem isAdicComplete_of_isNilpotent (J : Ideal C) (hJ : IsNilpotent J) : IsAdicComplete J C := by
  obtain ⟨n, hn⟩ := hJ
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx n
    rw [hn] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f n, fun m => by
    by_cases hm : m ≤ n
    · exact hf hm
    · push Not at hm
      have h1 : f n ≡ f m [SMOD (J ^ n • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = n + (m - n) by omega, pow_add, hn, zero_mul]; simp
      have h3 : (J ^ n • ⊤ : Submodule C C) = ⊥ := by rw [hn]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem prod_pow_eq_zero_of_le_degree (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) (d : σ →₀ ℕ) (hd : N ≤ d.degree) :
    (d.prod fun s e => x s ^ e) = 0 := by
  have hmem : (d.prod fun s e => x s ^ e) ∈ J ^ d.degree := by
    rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun s _ => Ideal.pow_mem_pow (hx s) _
  have hle : J ^ d.degree ≤ J ^ N := Ideal.pow_le_pow_right hd
  have := hle hmem
  rwa [hN, Submodule.mem_bot] at this

theorem adicEval_eq_sum [Finite σ] (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) (D : Finset (σ →₀ ℕ))
    (hD : ∀ d, d ∉ D → N ≤ d.degree) :
    adicEval J x f = ∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal C := ⟨J⟩
  haveI hc : IsAdicComplete J C := isAdicComplete_of_isNilpotent J ⟨N, hN⟩
  haveI : CompleteSpace C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).1
  haveI : T2Space C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).2
  have hφ : Continuous (algebraMap R C) := continuous_of_discreteTopology
  have ha : MvPowerSeries.HasEval x := by
    refine ⟨fun s => ?_, ?_⟩
    ·
      apply tendsto_atTop_of_eventually_const (i₀ := N)
      intro n hn
      have h0 : x s ^ n = 0 := by
        have hmem : x s ^ n ∈ J ^ n := Ideal.pow_mem_pow (hx s) n
        have := (Ideal.pow_le_pow_right hn) hmem
        rwa [hN, Submodule.mem_bot] at this
      exact h0
    · rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  have h1 := MvPowerSeries.hasSum_eval₂ hφ ha f
  have h2 : HasSum (fun d : σ →₀ ℕ => algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e)
      (∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e) := by
    apply hasSum_sum_of_ne_finset_zero
    intro d hd'
    rw [prod_pow_eq_zero_of_le_degree J hN hx d (hD d hd'), mul_zero]
  exact h1.unique h2

theorem le_degree_of_not_mem_Iic [Fintype σ] [DecidableEq σ] (N : ℕ) (d : σ →₀ ℕ)
    (hd : d ∉ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : σ => N)) : N ≤ d.degree := by
  classical
  rw [Finset.mem_Iic] at hd
  have : ∃ s, N < d s := by
    by_contra h
    push Not at h
    exact hd fun s => by simpa using h s
  obtain ⟨s, hs⟩ := this
  calc N ≤ d s := hs.le
    _ ≤ d.degree := by
        rw [Finsupp.degree_apply]
        by_cases hs0 : s ∈ d.support
        · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hs0
        · rw [Finsupp.notMem_support_iff.mp hs0]; exact Nat.zero_le _

theorem adicEval_eq_adicEval [Finite σ] (J J' : Ideal C) (hJ : IsNilpotent J) (hJ' : IsNilpotent J')
    {x : σ → C} (hx : ∀ s, x s ∈ J) (hx' : ∀ s, x s ∈ J') (f : MvPowerSeries σ R) :
    adicEval J x f = adicEval J' x f := by
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  obtain ⟨N', hN'⟩ := hJ'
  have hM : J ^ max N N' = ⊥ := by
    rw [show max N N' = N + (max N N' - N) by omega, pow_add, hN, zero_mul]; rfl
  have hM' : J' ^ max N N' = ⊥ := by
    rw [show max N N' = N' + (max N N' - N') by omega, pow_add, hN', zero_mul]; rfl
  rw [adicEval_eq_sum J hM hx f _ (le_degree_of_not_mem_Iic (max N N')),
    adicEval_eq_sum J' hM' hx' f _ (le_degree_of_not_mem_Iic (max N N'))]

theorem adicEval_mem [Finite σ] (J : Ideal C) (hJ : IsNilpotent J) {x : σ → C} (hx : ∀ s, x s ∈ J)
    {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) : adicEval J x f ∈ J := by
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  replace hN : J ^ N = ⊥ := hN
  rw [adicEval_eq_sum J hN hx f _ (le_degree_of_not_mem_Iic N)]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext fun s => by simpa using h s)
    refine Ideal.mul_mem_left _ _ ?_
    rw [Finsupp.prod]
    have hs' : s ∈ d.support := Finsupp.mem_support_iff.mpr hs
    rw [← Finset.mul_prod_erase _ _ hs']
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ]
    exact Ideal.mul_mem_left _ _ (hx s)

theorem adicEval_eq_zero_of_forall_coeff [Finite σ] (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) {f : MvPowerSeries σ R} (hf : ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = 0) :
    adicEval J x f = 0 := by
  classical
  haveI := Fintype.ofFinite σ
  rw [adicEval_eq_sum J hN hx f _ (le_degree_of_not_mem_Iic N)]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d.degree < N
  · rw [hf d hd, map_zero, zero_mul]
  · rw [prod_pow_eq_zero_of_le_degree J hN hx d (not_lt.mp hd), mul_zero]

theorem map_adicEval [Finite σ] {C' : Type z} [CommRing C'] [Algebra R C'] (J : Ideal C) (J' : Ideal C')
    (hJ : IsNilpotent J) (hJ' : IsNilpotent J') (φ : C →ₐ[R] C') {x : σ → C} (hx : ∀ s, x s ∈ J)
    (hx' : ∀ s, φ (x s) ∈ J') (f : MvPowerSeries σ R) :
    φ (adicEval J x f) = adicEval J' (fun s => φ (x s)) f := by
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  obtain ⟨N', hN'⟩ := hJ'
  have hM : J ^ max N N' = ⊥ := by
    rw [show max N N' = N + (max N N' - N) by omega, pow_add, hN, zero_mul]; rfl
  have hM' : J' ^ max N N' = ⊥ := by
    rw [show max N N' = N' + (max N N' - N') by omega, pow_add, hN', zero_mul]; rfl
  rw [adicEval_eq_sum J hM hx f _ (le_degree_of_not_mem_Iic (max N N')),
    adicEval_eq_sum J' hM' hx' f _ (le_degree_of_not_mem_Iic (max N N'))]
  simp only [map_sum, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]

theorem adicEval_eq_aeval_of_forall_coeff [Finite σ] (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) (p : MvPolynomial σ R)
    (hfp : ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = MvPolynomial.coeff d p) :
    adicEval J x f = MvPolynomial.aeval x p := by
  have h : adicEval J x (f - (p : MvPowerSeries σ R)) = 0 := by
    apply adicEval_eq_zero_of_forall_coeff J hN hx
    intro d hd
    rw [map_sub, hfp d hd, MvPolynomial.coeff_coe, sub_self]
  haveI := isAdicComplete_of_isNilpotent J ⟨N, hN⟩
  have hxr : ∀ s, x s ∈ J.radical := fun s => Ideal.le_radical (hx s)
  have hlin : adicEval J x (f - (p : MvPowerSeries σ R)) =
      adicEval J x f - adicEval J x (p : MvPowerSeries σ R) := by
    rw [← coe_adicEvalAlgHom J hxr, map_sub]
  rw [hlin, sub_eq_zero] at h
  rw [h, adicEval_coe]

end MvFormalGroup.NilAdicEval

namespace NilYoneda

section TestPairs

variable {R : Type u} [CommRing R] {σ : Type}

abbrev varIdeal (R : Type u) [CommRing R] (σ : Type) : Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range MvPolynomial.X)

abbrev TestRing (R : Type u) [CommRing R] (σ : Type) (N : ℕ) : Type u :=
  MvPolynomial σ R ⧸ varIdeal R σ ^ N

abbrev testIdeal (R : Type u) [CommRing R] (σ : Type) (N : ℕ) : Ideal (TestRing R σ N) :=
  (varIdeal R σ).map (Ideal.Quotient.mk (varIdeal R σ ^ N))

def xbar (R : Type u) [CommRing R] (σ : Type) (N : ℕ) : σ → TestRing R σ N :=
  fun s => Ideal.Quotient.mk (varIdeal R σ ^ N) (MvPolynomial.X s)

theorem testIdeal_pow_eq_bot (N : ℕ) : testIdeal R σ N ^ N = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem isNilpotent_testIdeal (N : ℕ) : IsNilpotent (testIdeal R σ N) :=
  ⟨N, testIdeal_pow_eq_bot N⟩

theorem X_mem_varIdeal (s : σ) : (MvPolynomial.X s : MvPolynomial σ R) ∈ varIdeal R σ :=
  Ideal.subset_span ⟨s, rfl⟩

theorem xbar_mem (N : ℕ) (s : σ) : xbar R σ N s ∈ testIdeal R σ N :=
  Ideal.mem_map_of_mem _ (X_mem_varIdeal s)

noncomputable def rep {N : ℕ} (q : TestRing R σ N) : MvPolynomial σ R :=
  (Ideal.Quotient.mk_surjective q).choose

theorem mk_rep {N : ℕ} (q : TestRing R σ N) : Ideal.Quotient.mk (varIdeal R σ ^ N) (rep q) = q :=
  (Ideal.Quotient.mk_surjective q).choose_spec

noncomputable def coeffQ {N : ℕ} (d : σ →₀ ℕ) (q : TestRing R σ N) : R :=
  MvPolynomial.coeff d (rep q)

theorem aeval_xbar (N : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.aeval (xbar R σ N) p = Ideal.Quotient.mk (varIdeal R σ ^ N) p := by
  have h : MvPolynomial.aeval (xbar R σ N) = Ideal.Quotient.mkₐ R (varIdeal R σ ^ N) := by
    apply MvPolynomial.algHom_ext
    intro s
    simp [xbar]
  rw [h]
  rfl

def transition {N M : ℕ} (h : N ≤ M) : TestRing R σ M →ₐ[R] TestRing R σ N :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)

theorem transition_mk {N M : ℕ} (h : N ≤ M) (p : MvPolynomial σ R) :
    transition h (Ideal.Quotient.mk (varIdeal R σ ^ M) p) = Ideal.Quotient.mk (varIdeal R σ ^ N) p := rfl

theorem transition_xbar {N M : ℕ} (h : N ≤ M) (s : σ) : transition h (xbar R σ M s) = xbar R σ N s := rfl

theorem transition_mem {N M : ℕ} (h : N ≤ M) {q : TestRing R σ M} (hq : q ∈ testIdeal R σ M) :
    transition h q ∈ testIdeal R σ N := by
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq
  rw [transition_mk]
  exact Ideal.mem_map_of_mem _ hp

noncomputable def evalAt {C : Type u} [CommRing C] [Algebra R C] (J : Ideal C) {M : ℕ} (hM : J ^ M = ⊥)
    (x : σ → C) (hx : ∀ s, x s ∈ J) : TestRing R σ M →ₐ[R] C :=
  Ideal.Quotient.liftₐ (varIdeal R σ ^ M) (MvPolynomial.aeval x) (by
    have hle : (varIdeal R σ).map (MvPolynomial.aeval x) ≤ J := by
      rw [Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      simpa using hx s
    intro a ha
    have hmem : MvPolynomial.aeval x a ∈ ((varIdeal R σ) ^ M).map (MvPolynomial.aeval x) :=
      Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at hmem
    have := (Ideal.pow_right_mono hle M) hmem
    rwa [hM, Submodule.mem_bot] at this)

theorem evalAt_mk {C : Type u} [CommRing C] [Algebra R C] (J : Ideal C) {M : ℕ} (hM : J ^ M = ⊥)
    (x : σ → C) (hx : ∀ s, x s ∈ J) (p : MvPolynomial σ R) :
    evalAt J hM x hx (Ideal.Quotient.mk (varIdeal R σ ^ M) p) = MvPolynomial.aeval x p := rfl

theorem evalAt_xbar {C : Type u} [CommRing C] [Algebra R C] (J : Ideal C) {M : ℕ} (hM : J ^ M = ⊥)
    (x : σ → C) (hx : ∀ s, x s ∈ J) (s : σ) : evalAt J hM x hx (xbar R σ M s) = x s := by
  rw [xbar, evalAt_mk]; simp

theorem evalAt_mem {C : Type u} [CommRing C] [Algebra R C] (J : Ideal C) {M : ℕ} (hM : J ^ M = ⊥)
    (x : σ → C) (hx : ∀ s, x s ∈ J) {q : TestRing R σ M} (hq : q ∈ testIdeal R σ M) :
    evalAt J hM x hx q ∈ J := by
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq
  rw [evalAt_mk]
  have hle : (varIdeal R σ).map (MvPolynomial.aeval x) ≤ J := by
    rw [Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    simpa using hx s
  exact hle (Ideal.mem_map_of_mem _ hp)

end TestPairs

section Coefficients

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [DecidableEq σ]

def lowVanish (R : Type u) [CommRing R] (σ : Type) [DecidableEq σ] (N : ℕ) : Ideal (MvPolynomial σ R) where
  carrier := {p | ∀ d : σ →₀ ℕ, d.degree < N → MvPolynomial.coeff d p = 0}
  zero_mem' := fun d _ => MvPolynomial.coeff_zero d
  add_mem' := fun {p q} hp hq d hd => by
    simp only [Set.mem_setOf_eq] at hp hq
    rw [MvPolynomial.coeff_add, hp d hd, hq d hd, add_zero]
  smul_mem' := fun q p hp d hd => by
    simp only [Set.mem_setOf_eq] at hp
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    have hab' : ab.1 + ab.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hdeg : ab.2.degree ≤ d.degree := by
      rw [← hab', map_add]; exact Nat.le_add_left _ _
    rw [hp ab.2 (lt_of_le_of_lt hdeg hd), mul_zero]

omit [Fintype σ] in
theorem mem_lowVanish {N : ℕ} {p : MvPolynomial σ R} :
    p ∈ lowVanish R σ N ↔ ∀ d : σ →₀ ℕ, d.degree < N → MvPolynomial.coeff d p = 0 := Iff.rfl

theorem varIdeal_pow_le_lowVanish (N : ℕ) : varIdeal R σ ^ N ≤ lowVanish R σ N := by
  induction N with
  | zero =>
    intro p _ d hd
    exact absurd hd (Nat.not_lt_zero _)
  | succ N ih =>
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun p hp q hq => ?_
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hq
    rw [Finset.mul_sum]
    refine Ideal.sum_mem _ fun s _ => ?_
    intro d hd
    rw [← mul_assoc, MvPolynomial.coeff_mul_X']
    split_ifs with hs
    · have hmem : p * c s ∈ varIdeal R σ ^ N := Ideal.mul_mem_right _ _ hp
      apply ih hmem
      have h1 : (d - Finsupp.single s 1).degree + 1 = d.degree := by
        have hds : 1 ≤ d s := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
        have hsub : d - Finsupp.single s 1 + Finsupp.single s 1 = d := by
          ext i
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply]
          split_ifs with his
          · subst his; omega
          · omega
        conv_rhs => rw [← hsub]
        rw [map_add, Finsupp.degree_single]
      omega
    · rfl

theorem coeff_eq_zero_of_mem_pow {N : ℕ} {p : MvPolynomial σ R} (hp : p ∈ varIdeal R σ ^ N)
    {d : σ →₀ ℕ} (hd : d.degree < N) : MvPolynomial.coeff d p = 0 :=
  varIdeal_pow_le_lowVanish N hp d hd

theorem coeffQ_mk {N : ℕ} {d : σ →₀ ℕ} (hd : d.degree < N) (p : MvPolynomial σ R) :
    coeffQ d (Ideal.Quotient.mk (varIdeal R σ ^ N) p) = MvPolynomial.coeff d p := by
  unfold coeffQ
  have h : rep (Ideal.Quotient.mk (varIdeal R σ ^ N) p) - p ∈ varIdeal R σ ^ N :=
    Ideal.Quotient.eq.mp (mk_rep _)
  have := coeff_eq_zero_of_mem_pow h hd
  rwa [MvPolynomial.coeff_sub, sub_eq_zero] at this

noncomputable def truncPoly (M : ℕ) (f : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ e ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : σ => M), MvPolynomial.monomial e (coeff e f)

theorem coeff_truncPoly (M : ℕ) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) (hd : d.degree < M) :
    MvPolynomial.coeff d (truncPoly M f) = coeff d f := by
  unfold truncPoly
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.Iic _) d (fun e => coeff e f)]
  rw [if_pos]
  by_contra h
  exact absurd (MvFormalGroup.NilAdicEval.le_degree_of_not_mem_Iic M d h) (not_le.mpr hd)

theorem adicEval_xbar (N : ℕ) (f : MvPowerSeries σ R) :
    MvFormalGroup.adicEval (testIdeal R σ N) (xbar R σ N) f =
      Ideal.Quotient.mk (varIdeal R σ ^ N) (truncPoly N f) := by
  rw [MvFormalGroup.NilAdicEval.adicEval_eq_aeval_of_forall_coeff (testIdeal R σ N)
    (testIdeal_pow_eq_bot N) (xbar_mem N) f (truncPoly N f)
    (fun d hd => (coeff_truncPoly N f d hd).symm), aeval_xbar]

theorem coeffQ_adicEval_xbar {N : ℕ} (f : MvPowerSeries σ R) {d : σ →₀ ℕ} (hd : d.degree < N) :
    coeffQ d (MvFormalGroup.adicEval (testIdeal R σ N) (xbar R σ N) f) = coeff d f := by
  rw [adicEval_xbar, coeffQ_mk hd, coeff_truncPoly N f d hd]

theorem eq_of_forall_adicEval_xbar_eq {f f' : MvPowerSeries σ R}
    (h : ∀ N, MvFormalGroup.adicEval (testIdeal R σ N) (xbar R σ N) f =
      MvFormalGroup.adicEval (testIdeal R σ N) (xbar R σ N) f') : f = f' := by
  ext d
  have := congrArg (coeffQ d) (h (d.degree + 1))
  rwa [coeffQ_adicEval_xbar f (Nat.lt_succ_self _), coeffQ_adicEval_xbar f' (Nat.lt_succ_self _)]
    at this

theorem coeffQ_transition {N M : ℕ} (h : N ≤ M) (q : TestRing R σ M) {d : σ →₀ ℕ} (hd : d.degree < N) :
    coeffQ d (transition h q) = coeffQ d q := by
  conv_rhs => rw [← mk_rep q]
  conv_lhs => rw [← mk_rep q, transition_mk]
  rw [coeffQ_mk hd, coeffQ_mk (lt_of_lt_of_le hd h)]

theorem evalAt_eq_aeval_of_forall_coeffQ {C : Type u} [CommRing C] [Algebra R C] (J : Ideal C) {M : ℕ}
    (hM : J ^ M = ⊥) (x : σ → C) (hx : ∀ s, x s ∈ J) (q : TestRing R σ M) (p : MvPolynomial σ R)
    (hqp : ∀ d : σ →₀ ℕ, d.degree < M → coeffQ d q = MvPolynomial.coeff d p) :
    evalAt J hM x hx q = MvPolynomial.aeval x p := by
  conv_lhs => rw [← mk_rep q, evalAt_mk]

  have hdiff : ∀ d : σ →₀ ℕ, d.degree < M → MvPolynomial.coeff d (rep q - p) = 0 := by
    intro d hd
    rw [MvPolynomial.coeff_sub, ← hqp d hd, sub_eq_zero]
    have := coeffQ_mk hd (rep q) (R := R)
    rw [mk_rep] at this
    exact this.symm
  have hval : MvPolynomial.aeval x (rep q - p) = 0 := by
    have h := MvFormalGroup.NilAdicEval.adicEval_eq_aeval_of_forall_coeff J hM hx
      (0 : MvPowerSeries σ R) (rep q - p) (fun d hd => by rw [map_zero, hdiff d hd])
    haveI := MvFormalGroup.NilAdicEval.isAdicComplete_of_isNilpotent J ⟨M, hM⟩
    have h0 : MvFormalGroup.adicEval J x (0 : MvPowerSeries σ R) = 0 := by
      rw [← MvFormalGroup.coe_adicEvalAlgHom J (fun s => Ideal.le_radical (hx s)), map_zero]
    rw [h0] at h
    exact h.symm
  rwa [map_sub, sub_eq_zero] at hval

end Coefficients

end NilYoneda

namespace NilYoneda

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [DecidableEq σ]

noncomputable def series
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C) : MvPowerSeries σ R :=
  fun d => coeffQ d (t (TestRing R σ (d.degree + 1)) (testIdeal R σ (d.degree + 1)) (xbar R σ (d.degree + 1)))

theorem coeff_series
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x))
    {M : ℕ} (d : σ →₀ ℕ) (hd : d.degree < M) :
    coeff d (series t) = coeffQ d (t (TestRing R σ M) (testIdeal R σ M) (xbar R σ M)) := by
  show coeffQ d (t (TestRing R σ (d.degree + 1)) (testIdeal R σ (d.degree + 1))
    (xbar R σ (d.degree + 1))) = _
  have hle : d.degree + 1 ≤ M := hd
  have hnat := ht_nat (TestRing R σ M) (TestRing R σ (d.degree + 1)) (testIdeal R σ M)
    (testIdeal R σ (d.degree + 1)) (isNilpotent_testIdeal M) (isNilpotent_testIdeal _)
    (transition hle) (fun s hs => transition_mem hle hs) (xbar R σ M) (xbar_mem M)
  have hx : (⇑(transition (R := R) (σ := σ) hle) ∘ xbar R σ M) = xbar R σ (d.degree + 1) := by
    funext s; exact transition_xbar hle s
  rw [hx] at hnat
  rw [hnat, coeffQ_transition hle _ (Nat.lt_succ_self _)]

theorem apply_eq_adicEval_series
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x))
    (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C) (hJ : IsNilpotent J)
    (x : σ → C) (hx : ∀ s, x s ∈ J) : t C J x = MvFormalGroup.adicEval J x (series t) := by
  obtain ⟨M, hM⟩ := hJ
  replace hM : J ^ M = ⊥ := hM

  have hnat := ht_nat (TestRing R σ M) C (testIdeal R σ M) J (isNilpotent_testIdeal M) ⟨M, hM⟩
    (evalAt J hM x hx) (fun s hs => evalAt_mem J hM x hx hs) (xbar R σ M) (xbar_mem M)
  have hx' : (⇑(evalAt (R := R) (σ := σ) J hM x hx) ∘ xbar R σ M) = x := by
    funext s; exact evalAt_xbar J hM x hx s
  rw [hx'] at hnat
  rw [hnat, evalAt_eq_aeval_of_forall_coeffQ J hM x hx _ (truncPoly M (series t)),
    MvFormalGroup.NilAdicEval.adicEval_eq_aeval_of_forall_coeff J hM hx (series t)
      (truncPoly M (series t))]
  · intro d hd
    exact (coeff_truncPoly M (series t) d hd).symm
  · intro d hd
    rw [coeff_truncPoly M (series t) d hd, coeff_series t ht_nat d hd]

theorem eq_series_of_forall_xbar
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x))
    (f : MvPowerSeries σ R)
    (hf : ∀ N, t (TestRing R σ N) (testIdeal R σ N) (xbar R σ N) =
      MvFormalGroup.adicEval (testIdeal R σ N) (xbar R σ N) f) : f = series t := by
  refine eq_of_forall_adicEval_xbar_eq fun N => ?_
  rw [← hf N]
  exact apply_eq_adicEval_series t ht_nat _ _ (isNilpotent_testIdeal N) _ (xbar_mem N)

end NilYoneda

namespace NilYonedaLaw

p2m_open "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent.NilYoneda MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent.MvFormalGroup"

variable {R : Type u} [CommRing R]

theorem two_le_degree {σ : Type} [Fintype σ] [DecidableEq σ] (e : σ →₀ ℕ) (h0 : e ≠ 0)
    (h1 : ∀ s, e ≠ Finsupp.single s 1) : 2 ≤ e.degree := by
  obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Finsupp.ext fun s => by simpa using h s)
  rw [Finsupp.degree_eq_sum]
  by_cases h2 : 2 ≤ e s
  · exact le_trans h2 (Finset.single_le_sum (fun i _ => Nat.zero_le (e i)) (Finset.mem_univ s))
  · have hes : e s = 1 := by omega
    obtain ⟨s', hs'⟩ : ∃ s', s' ≠ s ∧ e s' ≠ 0 := by
      by_contra h
      push Not at h
      apply h1 s
      ext i
      by_cases his : i = s
      · subst his; simp [hes]
      · rw [Finsupp.single_apply, if_neg (Ne.symm his)]
        exact h i his
    have hsub : ({s, s'} : Finset σ) ⊆ Finset.univ := Finset.subset_univ _
    have hle : ∑ i ∈ ({s, s'} : Finset σ), e i ≤ ∑ i, e i := Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair (Ne.symm hs'.1)] at hle
    have : 1 ≤ e s' := Nat.one_le_iff_ne_zero.mpr hs'.2
    omega

theorem adicEval_eq_sum_linear {σ : Type} [Fintype σ] [DecidableEq σ] {C : Type v} [CommRing C] [Algebra R C]
    (J : Ideal C) (hJ : J ^ 2 = ⊥) {w : σ → C} (hw : ∀ s, w s ∈ J) (f : MvPowerSeries σ R)
    (hf : constantCoeff f = 0) :
    MvFormalGroup.adicEval J w f = ∑ s, algebraMap R C (coeff (Finsupp.single s 1) f) * w s := by
  have h0 : (0 : σ →₀ ℕ) ∉ Finset.univ.image fun s : σ => Finsupp.single s 1 := by
    simp [Finsupp.single_eq_zero]
  rw [MvFormalGroup.NilAdicEval.adicEval_eq_sum J hJ hw f
    (insert 0 (Finset.univ.image fun s : σ => Finsupp.single s 1)) ?_]
  · rw [Finset.sum_insert h0, Finset.sum_image fun s _ s' _ h => Finsupp.single_left_injective one_ne_zero h]
    have hc0 : coeff (0 : σ →₀ ℕ) f = 0 := by rw [coeff_zero_eq_constantCoeff_apply, hf]
    rw [hc0, map_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.prod_single_index (by simp), pow_one]
  · intro e he
    rw [Finset.mem_insert, not_or, Finset.mem_image, not_exists] at he
    exact two_le_degree e he.1 fun s h => he.2 s ⟨Finset.mem_univ s, h.symm⟩

theorem adicEval_subst_pair {d : ℕ} {τ : Type} [Fintype τ] {C : Type v} [CommRing C] [Algebra R C]
    (J : Ideal C) [IsAdicComplete J C] {w : τ → C} (hw : ∀ t, w t ∈ J.radical)
    (Φ : MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ j, (u j).constantCoeff = 0) (hv : ∀ j, (v j).constantCoeff = 0) :
    MvFormalGroup.adicEval J w (subst (Sum.elim u v) Φ) =
      MvFormalGroup.adicEval J (Sum.elim (fun j => MvFormalGroup.adicEval J w (u j))
        fun j => MvFormalGroup.adicEval J w (v j)) Φ := by
  have hfam : (fun s => MvFormalGroup.adicEval J w (Sum.elim u v s)) =
      Sum.elim (fun j => MvFormalGroup.adicEval J w (u j)) fun j => MvFormalGroup.adicEval J w (v j) := by
    funext s; rcases s with j | j <;> rfl
  rw [MvFormalGroup.adicEval_subst J hw (MvFormalGroup.hasSubst_elim hu hv), hfam]

variable {d : ℕ}
  (μ : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (Fin d → C) → (Fin d → C) → (Fin d → C))
  (hμ_mem : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
    ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → ∀ j, μ C J x y j ∈ J)
  (hμ_zero : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
    ∀ x : Fin d → C, (∀ j, x j ∈ J) → μ C J x 0 = x ∧ μ C J 0 x = x)
  (hμ_assoc : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
    ∀ x y z : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → (∀ j, z j ∈ J) →
      μ C J (μ C J x y) z = μ C J x (μ C J y z))
  (hμ_comm : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
    ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → μ C J x y = μ C J y x)
  (hμ_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
    (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
    ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
      ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
        μ C' J' (φ ∘ x) (φ ∘ y) = φ ∘ μ C J x y)

def pairFun (i : Fin d) : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (Fin d ⊕ Fin d → C) → C :=
  fun C _ _ J z => μ C J (fun j => z (Sum.inl j)) (fun j => z (Sum.inr j)) i

include hμ_nat in
theorem pairFun_nat (i : Fin d) : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
    (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
    ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
      ∀ z : Fin d ⊕ Fin d → C, (∀ s, z s ∈ J) → pairFun μ i C' J' (φ ∘ z) = φ (pairFun μ i C J z) := by
  intro C C' _ _ _ _ J J' hJ hJ' φ hφ z hz
  exact congrFun (hμ_nat C C' J J' hJ hJ' φ hφ (fun j => z (Sum.inl j)) (fun j => z (Sum.inr j))
    (fun j => hz _) (fun j => hz _)) i

def lawSeries (i : Fin d) : MvPowerSeries (Fin d ⊕ Fin d) R := series (pairFun μ i)

include hμ_nat in

theorem mu_eq_adicEval (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C) (hJ : IsNilpotent J)
    (x y : Fin d → C) (hx : ∀ j, x j ∈ J) (hy : ∀ j, y j ∈ J) (i : Fin d) :
    μ C J x y i = MvFormalGroup.adicEval J (Sum.elim x y) (lawSeries μ i) := by
  have hz : ∀ s, Sum.elim x y s ∈ J := by rintro (j | j); exacts [hx j, hy j]
  exact apply_eq_adicEval_series (pairFun μ i) (pairFun_nat μ hμ_nat i) C J hJ (Sum.elim x y) hz

theorem adicEval_bot_zero {σ : Type} [Fintype σ] (f : MvPowerSeries σ R) :
    MvFormalGroup.adicEval (⊥ : Ideal R) (0 : σ → R) f = constantCoeff f := by
  classical
  rw [MvFormalGroup.NilAdicEval.adicEval_eq_sum (⊥ : Ideal R) (N := 1) (pow_one _) (x := 0)
    (fun _ => Submodule.zero_mem _) f {0} ?_]
  · simp
  · intro e he
    rw [Finset.mem_singleton] at he
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    apply he
    ext s
    have : e s ≤ e.degree := by
      rw [Finsupp.degree_apply]
      by_cases hs : s ∈ e.support
      · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hs
      · rw [Finsupp.notMem_support_iff.mp hs]; exact Nat.zero_le _
    rw [h0] at this
    simpa using this

include hμ_zero hμ_nat in
theorem constantCoeff_lawSeries (i : Fin d) : constantCoeff (lawSeries μ i) = 0 := by
  have hbot : IsNilpotent (⊥ : Ideal R) := ⟨1, by rw [pow_one]; rfl⟩
  have h1 := mu_eq_adicEval μ hμ_nat R (⊥ : Ideal R) hbot 0 0 (fun _ => Submodule.zero_mem _)
    (fun _ => Submodule.zero_mem _) i
  have h00 : (Sum.elim (0 : Fin d → R) (0 : Fin d → R)) = 0 := by
    funext s; rcases s with j | j <;> rfl
  rw [h00, adicEval_bot_zero, (hμ_zero R ⊥ hbot 0 fun _ => Submodule.zero_mem _).1] at h1
  exact h1.symm

include hμ_zero hμ_nat in

theorem coeff_single_inl (i j : Fin d) :
    coeff (Finsupp.single (Sum.inl j) 1) (lawSeries μ i) = if i = j then 1 else 0 := by
  classical

  set C := TestRing R (Fin d) 2
  set J := testIdeal R (Fin d) 2
  have hJ2 : J ^ 2 = ⊥ := testIdeal_pow_eq_bot 2
  have hJ : IsNilpotent J := ⟨2, hJ2⟩
  have hX : ∀ l, xbar R (Fin d) 2 l ∈ J := xbar_mem 2
  have hunit := congrFun (hμ_zero C J hJ (xbar R (Fin d) 2) hX).1 i
  rw [mu_eq_adicEval μ hμ_nat C J hJ _ 0 hX (fun _ => Submodule.zero_mem _) i,
    adicEval_eq_sum_linear J hJ2 (by rintro (l | l); exacts [hX l, Submodule.zero_mem _]) _
      (constantCoeff_lawSeries μ hμ_zero hμ_nat i),
    Fintype.sum_sum_type] at hunit
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    at hunit

  have hl : (∑ l : Fin d, algebraMap R C (coeff (Finsupp.single (Sum.inl l) 1) (lawSeries μ i)) *
      xbar R (Fin d) 2 l) = Ideal.Quotient.mk (varIdeal R (Fin d) ^ 2)
        (∑ l : Fin d, MvPolynomial.C (coeff (Finsupp.single (Sum.inl l) 1) (lawSeries μ i)) *
          MvPolynomial.X l) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  rw [hl] at hunit
  have hd1 : (Finsupp.single j 1 : Fin d →₀ ℕ).degree < 2 := by
    rw [Finsupp.degree_single]; exact Nat.lt_succ_self 1
  have h := congrArg (coeffQ (Finsupp.single j 1)) hunit
  rw [coeffQ_mk hd1, xbar, coeffQ_mk hd1, MvPolynomial.coeff_sum, MvPolynomial.coeff_X'] at h
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
    Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [← h]

include hμ_zero hμ_nat in

theorem coeff_single_inr (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1) (lawSeries μ i) = if i = j then 1 else 0 := by
  classical
  set C := TestRing R (Fin d) 2
  set J := testIdeal R (Fin d) 2
  have hJ2 : J ^ 2 = ⊥ := testIdeal_pow_eq_bot 2
  have hJ : IsNilpotent J := ⟨2, hJ2⟩
  have hX : ∀ l, xbar R (Fin d) 2 l ∈ J := xbar_mem 2
  have hunit := congrFun (hμ_zero C J hJ (xbar R (Fin d) 2) hX).2 i
  rw [mu_eq_adicEval μ hμ_nat C J hJ 0 _ (fun _ => Submodule.zero_mem _) hX i,
    adicEval_eq_sum_linear J hJ2 (by rintro (l | l); exacts [Submodule.zero_mem _, hX l]) _
      (constantCoeff_lawSeries μ hμ_zero hμ_nat i),
    Fintype.sum_sum_type] at hunit
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    at hunit
  have hl : (∑ l : Fin d, algebraMap R C (coeff (Finsupp.single (Sum.inr l) 1) (lawSeries μ i)) *
      xbar R (Fin d) 2 l) = Ideal.Quotient.mk (varIdeal R (Fin d) ^ 2)
        (∑ l : Fin d, MvPolynomial.C (coeff (Finsupp.single (Sum.inr l) 1) (lawSeries μ i)) *
          MvPolynomial.X l) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  rw [hl] at hunit
  have hd1 : (Finsupp.single j 1 : Fin d →₀ ℕ).degree < 2 := by
    rw [Finsupp.degree_single]; exact Nat.lt_succ_self 1
  have h := congrArg (coeffQ (Finsupp.single j 1)) hunit
  rw [coeffQ_mk hd1, xbar, coeffQ_mk hd1, MvPolynomial.coeff_sum, MvPolynomial.coeff_X'] at h
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
    Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [← h]

include hμ_mem hμ_zero hμ_assoc hμ_nat in

theorem assoc_lawSeries (i : Fin d) :
    subst
      (Sum.elim
        (fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
            fun l => X (Sum.inr (Sum.inl l)))
          (lawSeries μ j))
        fun j => X (Sum.inr (Sum.inr j)))
      (lawSeries μ i)
      =
    subst
      (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
        fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
            fun l => X (Sum.inr (Sum.inr l)))
          (lawSeries μ j))
      (lawSeries μ i) := by
  classical
  apply eq_of_forall_adicEval_xbar_eq
  intro N
  set C := TestRing R (Fin d ⊕ (Fin d ⊕ Fin d)) N
  set J := testIdeal R (Fin d ⊕ (Fin d ⊕ Fin d)) N
  set z := xbar R (Fin d ⊕ (Fin d ⊕ Fin d)) N
  have hJ : IsNilpotent J := isNilpotent_testIdeal N
  haveI : IsAdicComplete J C := MvFormalGroup.NilAdicEval.isAdicComplete_of_isNilpotent J hJ
  have hz : ∀ s, z s ∈ J := xbar_mem N
  have hzr : ∀ s, z s ∈ J.radical := fun s => Ideal.le_radical (hz s)
  let a : Fin d → C := fun j => z (Sum.inl j)
  let b : Fin d → C := fun j => z (Sum.inr (Sum.inl j))
  let c : Fin d → C := fun j => z (Sum.inr (Sum.inr j))
  have ha : ∀ j, a j ∈ J := fun j => hz _
  have hb : ∀ j, b j ∈ J := fun j => hz _
  have hc : ∀ j, c j ∈ J := fun j => hz _
  have hΦ0 : ∀ j, constantCoeff (lawSeries μ j) = 0 := constantCoeff_lawSeries μ hμ_zero hμ_nat
  have hXa : ∀ l, (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hXb : ∀ l, (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R).constantCoeff
      = 0 := fun l => constantCoeff_X _
  have hXc : ∀ l, (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R).constantCoeff
      = 0 := fun l => constantCoeff_X _
  have hab : ∀ j, μ C J a b j ∈ J := hμ_mem C J hJ a b ha hb
  have hbc : ∀ j, μ C J b c j ∈ J := hμ_mem C J hJ b c hb hc

  have hin_ab : (fun j => MvFormalGroup.adicEval J z (subst
      (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
        fun l => X (Sum.inr (Sum.inl l))) (lawSeries μ j))) = μ C J a b := by
    funext j
    rw [adicEval_subst_pair J hzr _ hXa hXb]
    simp only [MvFormalGroup.adicEval_X]
    exact (mu_eq_adicEval μ hμ_nat C J hJ a b ha hb j).symm
  have hin_bc : (fun j => MvFormalGroup.adicEval J z (subst
      (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
        fun l => X (Sum.inr (Sum.inr l))) (lawSeries μ j))) = μ C J b c := by
    funext j
    rw [adicEval_subst_pair J hzr _ hXb hXc]
    simp only [MvFormalGroup.adicEval_X]
    exact (mu_eq_adicEval μ hμ_nat C J hJ b c hb hc j).symm
  have hva : (fun j => MvFormalGroup.adicEval J z
      (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = a :=
    funext fun j => MvFormalGroup.adicEval_X _ _ _
  have hvc : (fun j => MvFormalGroup.adicEval J z
      (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = c :=
    funext fun j => MvFormalGroup.adicEval_X _ _ _
  rw [adicEval_subst_pair J hzr _ (fun j => constantCoeff_subst_eq_zero
      (MvFormalGroup.hasSubst_elim hXa hXb) (by rintro (l | l); exacts [hXa l, hXb l]) (hΦ0 j)) hXc,
    adicEval_subst_pair J hzr _ hXa (fun j => constantCoeff_subst_eq_zero
      (MvFormalGroup.hasSubst_elim hXb hXc) (by rintro (l | l); exacts [hXb l, hXc l]) (hΦ0 j)),
    hin_ab, hin_bc, hva, hvc,
    ← mu_eq_adicEval μ hμ_nat C J hJ _ c hab hc i,
    ← mu_eq_adicEval μ hμ_nat C J hJ a _ ha hbc i,
    hμ_assoc C J hJ a b c ha hb hc]

include hμ_comm hμ_nat in

theorem comm_lawSeries (i : Fin d) :
    subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
        fun j => X (Sum.inl j))
      (lawSeries μ i) = lawSeries μ i := by
  classical
  apply eq_of_forall_adicEval_xbar_eq
  intro N
  set C := TestRing R (Fin d ⊕ Fin d) N
  set J := testIdeal R (Fin d ⊕ Fin d) N
  set z := xbar R (Fin d ⊕ Fin d) N
  have hJ : IsNilpotent J := isNilpotent_testIdeal N
  haveI : IsAdicComplete J C := MvFormalGroup.NilAdicEval.isAdicComplete_of_isNilpotent J hJ
  have hz : ∀ s, z s ∈ J := xbar_mem N
  have hzr : ∀ s, z s ∈ J.radical := fun s => Ideal.le_radical (hz s)
  let a : Fin d → C := fun j => z (Sum.inl j)
  let b : Fin d → C := fun j => z (Sum.inr j)
  have ha : ∀ j, a j ∈ J := fun j => hz _
  have hb : ∀ j, b j ∈ J := fun j => hz _
  have hXa : ∀ l, (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hXb : ∀ l, (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hzab : z = Sum.elim a b := by
    funext s; rcases s with j | j <;> rfl
  rw [adicEval_subst_pair J hzr _ hXb hXa]
  simp only [MvFormalGroup.adicEval_X]
  rw [← mu_eq_adicEval μ hμ_nat C J hJ b a hb ha i]
  conv_rhs => rw [hzab]
  rw [← mu_eq_adicEval μ hμ_nat C J hJ a b ha hb i, hμ_comm C J hJ a b ha hb]

def law : MvFormalGroup d R where
  toPowerSeries := lawSeries μ
  constantCoeff_eq_zero := constantCoeff_lawSeries μ hμ_zero hμ_nat
  coeff_single_inl := coeff_single_inl μ hμ_zero hμ_nat
  coeff_single_inr := coeff_single_inr μ hμ_zero hμ_nat
  assoc := assoc_lawSeries μ hμ_mem hμ_zero hμ_assoc hμ_nat

include hμ_comm in
theorem isComm_law : (law μ hμ_mem hμ_zero hμ_assoc hμ_nat).IsComm :=
  ⟨comm_lawSeries μ hμ_comm hμ_nat⟩

end NilYonedaLaw

open NilYoneda NilYonedaLaw in
theorem solution
    {R : Type u} [CommRing R] (d : ℕ)
    (μ : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (Fin d → C) → (Fin d → C) → (Fin d → C))
    (hμ_mem : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → ∀ j, μ C J x y j ∈ J)
    (hμ_zero : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin d → C, (∀ j, x j ∈ J) → μ C J x 0 = x ∧ μ C J 0 x = x)
    (hμ_assoc : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x y z : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → (∀ j, z j ∈ J) →
        μ C J (μ C J x y) z = μ C J x (μ C J y z))
    (hμ_comm : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → μ C J x y = μ C J y x)
    (hμ_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
          μ C' J' (φ ∘ x) (φ ∘ y) = φ ∘ μ C J x y) :
    ∃! Φ : MvFormalGroup d R, Φ.IsComm ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
        ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
          ∀ i, μ C J x y i = MvFormalGroup.adicEval J (Sum.elim x y) (Φ.toPowerSeries i) := by
  classical
  refine ⟨law μ hμ_mem hμ_zero hμ_assoc hμ_nat, ⟨isComm_law μ hμ_mem hμ_zero hμ_assoc hμ_comm hμ_nat,
    fun C _ _ J hJ x y hx hy i => mu_eq_adicEval μ hμ_nat C J hJ x y hx hy i⟩, ?_⟩
  rintro Φ' ⟨_, hΦ'⟩
  apply MvFormalGroup.ext
  funext i
  show Φ'.toPowerSeries i = lawSeries μ i
  refine eq_series_of_forall_xbar (pairFun μ i) (pairFun_nat μ hμ_nat i) _ fun N => ?_
  have h := hΦ' (TestRing R (Fin d ⊕ Fin d) N) (testIdeal R (Fin d ⊕ Fin d) N) (isNilpotent_testIdeal N)
    (fun j => xbar R (Fin d ⊕ Fin d) N (Sum.inl j)) (fun j => xbar R (Fin d ⊕ Fin d) N (Sum.inr j))
    (fun j => xbar_mem N _) (fun j => xbar_mem N _) i
  have hz : Sum.elim (fun j => xbar R (Fin d ⊕ Fin d) N (Sum.inl j))
      (fun j => xbar R (Fin d ⊕ Fin d) N (Sum.inr j)) = xbar R (Fin d ⊕ Fin d) N := by
    funext s; rcases s with j | j <;> rfl
  rw [hz] at h
  exact h

end

end S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent
end P2MW
export P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent (solution)
