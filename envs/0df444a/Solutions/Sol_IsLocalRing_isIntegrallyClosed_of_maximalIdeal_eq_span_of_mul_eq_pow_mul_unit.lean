-- Prove2me | solution 1 for IsLocalRing.isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7dd18c40-8c02-5002-8a88-0279de75f523

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot_of_isPrecomplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit

set_option autoImplicit false

namespace PowerSeries
p2m_export "PowerSeries" "coe_mul algebraMap_apply coeff_mk mk trunc eq_X_mul_shift_add_const map_surjective eval₂_X coeff_coe eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc map_X constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X X_ne_zero coe_C quotient_span_X_sub_C_pow_of_irreducible"
p2m_open "PowerSeries"

variable {A : Type*} [CommRing A]

def coeffwiseIdeal (I : Ideal A) (n : ℕ) : Ideal (PowerSeries A) where
  carrier := {G | ∀ k, coeff k G ∈ I ^ (n - k)}
  zero_mem' := fun k => by simp
  add_mem' := fun {G H} hG hH k => by
    rw [map_add]
    exact Ideal.add_mem _ (hG k) (hH k)
  smul_mem' := fun H G hG k => by
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    have hp' : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) (hG p.2))

theorem mem_coeffwiseIdeal {I : Ideal A} {n : ℕ} {G : PowerSeries A} :
    G ∈ coeffwiseIdeal I n ↔ ∀ k, coeff k G ∈ I ^ (n - k) := Iff.rfl

theorem coeffwiseIdeal_zero (I : Ideal A) : coeffwiseIdeal I 0 = ⊤ :=
  eq_top_iff.mpr fun G _ k => by simp

theorem coeffwiseIdeal_mul_le (I : Ideal A) (m n : ℕ) :
    coeffwiseIdeal I m * coeffwiseIdeal I n ≤ coeffwiseIdeal I (m + n) :=
  Ideal.mul_le.mpr fun G hG H hH k => by
    rw [coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    have hp' : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hGH := Ideal.mul_mem_mul (hG p.1) (hH p.2)
    rw [← pow_add] at hGH
    exact Ideal.pow_le_pow_right (by omega) hGH

theorem map_C_sup_span_X_le_coeffwiseIdeal (I : Ideal A) :
    I.map (C : A →+* PowerSeries A) ⊔ Ideal.span {X} ≤ coeffwiseIdeal I 1 := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_) (Ideal.span_le.mpr ?_)
  · rw [Ideal.mem_comap, mem_coeffwiseIdeal]
    rintro (_ | k)
    · simpa using ha
    · simp
  · rintro _ ⟨⟩
    rw [SetLike.mem_coe, mem_coeffwiseIdeal]
    rintro (_ | k)
    · simp
    · simp

theorem map_C_sup_span_X_pow_le_coeffwiseIdeal (I : Ideal A) (n : ℕ) :
    (I.map (C : A →+* PowerSeries A) ⊔ Ideal.span {X}) ^ n ≤ coeffwiseIdeal I n := by
  induction n with
  | zero => simp [coeffwiseIdeal_zero]
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (map_C_sup_span_X_le_coeffwiseIdeal I)).trans
      (coeffwiseIdeal_mul_le I n 1)

theorem coeffwiseIdeal_le_map_C_sup_span_X_pow (I : Ideal A) (n : ℕ) :
    coeffwiseIdeal I n ≤ (I.map (C : A →+* PowerSeries A) ⊔ Ideal.span {X}) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro G hG
    rw [eq_X_mul_shift_add_const G]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ']
      refine Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mem_span_singleton_self X)) (ih fun k => ?_)
      rw [coeff_mk]
      simpa using hG (k + 1)
    · have h0 : constantCoeff G ∈ I ^ (n + 1) := by simpa using hG 0
      have := Ideal.mem_map_of_mem (C : A →+* PowerSeries A) h0
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono le_sup_left (n + 1) this

theorem map_C_sup_span_X_pow_eq (I : Ideal A) (n : ℕ) :
    (I.map (C : A →+* PowerSeries A) ⊔ Ideal.span {X}) ^ n = coeffwiseIdeal I n :=
  le_antisymm (map_C_sup_span_X_pow_le_coeffwiseIdeal I n) (coeffwiseIdeal_le_map_C_sup_span_X_pow I n)

end PowerSeries

namespace PowerSeries p2m_export "PowerSeries" "coe_mul algebraMap_apply coeff_mk mk trunc eq_X_mul_shift_add_const map_surjective eval₂_X coeff_coe eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc map_X constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X X_ne_zero coe_C quotient_span_X_sub_C_pow_of_irreducible" end PowerSeries
p2m_open_scoped "PowerSeries" in
theorem PowerSeries.isAdicComplete_map_C_sup_span_X {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A] :
    IsAdicComplete (I.map (PowerSeries.C : A →+* PowerSeries A) ⊔ Ideal.span {PowerSeries.X}) (PowerSeries A) := by
  have htop : ∀ n, ((I.map (PowerSeries.C : A →+* PowerSeries A) ⊔ Ideal.span {PowerSeries.X}) ^ n • ⊤ :
      Ideal (PowerSeries A)) = PowerSeries.coeffwiseIdeal I n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top, PowerSeries.map_C_sup_span_X_pow_eq]
  exact
  { haus' := fun F hF => by
      ext k
      rw [map_zero]
      refine IsHausdorff.haus (inferInstance : IsHausdorff I A) _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      have := hF (n + k)
      rw [SModEq.zero, htop, PowerSeries.mem_coeffwiseIdeal] at this
      simpa using this k
    prec' := fun f hf => by
      have hf' : ∀ k m n, m ≤ n →
          PowerSeries.coeff k (f (m + k)) - PowerSeries.coeff k (f (n + k)) ∈ I ^ m := by
        intro k m n hmn
        have := hf (Nat.add_le_add_right hmn k)
        rw [SModEq.sub_mem, htop, PowerSeries.mem_coeffwiseIdeal] at this
        simpa using this k
      have hL : ∀ k, ∃ L : A, ∀ m, PowerSeries.coeff k (f (m + k)) - L ∈ I ^ m := fun k => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I A)
          (f := fun m => PowerSeries.coeff k (f (m + k))) (fun {m n} hmn => by
            rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
            exact hf' k m n hmn)
        exact ⟨L, fun m => by simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL m⟩
      choose L hL using hL
      refine ⟨PowerSeries.mk L, fun n => ?_⟩
      rw [SModEq.sub_mem, htop, PowerSeries.mem_coeffwiseIdeal]
      intro k
      rw [map_sub, PowerSeries.coeff_mk]
      rcases Nat.lt_or_ge n k with hkn | hkn
      · rw [Nat.sub_eq_zero_of_le hkn.le, pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
        rw [Nat.add_sub_cancel_left, add_comm k m]
        exact hL k m }

namespace Submodule p2m_export "Submodule" "Quotient.eq mem_sup_right smul_mem' mk smul_mem mem_bot mem_span_singleton_self Quotient.mk span smul_induction_on mem_map_of_mem add_mem_sup span_le mem_comap mem_span_insert mem_span_range_iff_exists_fun pow_mem_pow mul_le mem_top mem_span_singleton fg_iff_exists_fin_generating_family mul_mem_mul smul_mem_smul mem_iInf generators nontrivial_iff map_mono map_smul' zero one map_span Quotient.mk_surjective map rec Quotient.nontrivial_iff mem_sup smul_mono_left subset_span module smul_def FG ext factor_mk factorPow map_sup fg_span mem_span_pair mem_sup_left map_le_iff_le_comap restrictScalars_mem" end Submodule
p2m_open_scoped "Submodule" in
theorem Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) [IsAdicComplete I A] [IsHausdorff I M]
    (N : Submodule A M) (hN : N.FG) (h : N ⊔ I • ⊤ = ⊤) : N = ⊤ := by
  classical
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hN

  let φ : (Fin k → A) →ₗ[A] M :=
    { toFun := fun c => ∑ i, c i • s i
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.smul_sum, mul_smul] }
  have hφ : ∀ c, φ c = ∑ i, c i • s i := fun c => rfl
  have hφN : ∀ c, φ c ∈ N := fun c => by
    rw [hφ, ← hs]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have h0 : ∀ m : M, ∃ c : Fin k → A, m - φ c ∈ (I • ⊤ : Submodule A M) := fun m => by
    have hm : m ∈ N ⊔ I • ⊤ := by rw [h]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hm
    rw [← hs, Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, rfl⟩ := hy
    exact ⟨c, by rw [hφ]; simpa using hz⟩

  have hstep : ∀ (n : ℕ) (y : M), y ∈ (I ^ n • ⊤ : Submodule A M) →
      ∃ c : Fin k → A, (∀ i, c i ∈ I ^ n) ∧ y - φ c ∈ (I ^ (n + 1) • ⊤ : Submodule A M) := by
    intro n y hy
    refine Submodule.smul_induction_on
      (p := fun y => ∃ c : Fin k → A, (∀ i, c i ∈ I ^ n) ∧ y - φ c ∈ (I ^ (n + 1) • ⊤ : Submodule A M))
      hy ?_ ?_
    · intro r hr m _
      obtain ⟨c, hc⟩ := h0 m
      refine ⟨r • c, fun i => Ideal.mul_mem_right _ _ hr, ?_⟩
      rw [map_smul, ← smul_sub, pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hr hc
    · rintro y₁ y₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
      refine ⟨c₁ + c₂, fun i => Ideal.add_mem _ (hc₁ i) (hc₂ i), ?_⟩
      rw [map_add]
      convert Submodule.add_mem _ h₁ h₂ using 1
      abel
  choose c hcI hcy using hstep
  refine eq_top_iff.mpr fun x _ => ?_

  let r : (n : ℕ) → {y : M // y ∈ (I ^ n • ⊤ : Submodule A M)} :=
    fun n => Nat.rec (motive := fun n => {y : M // y ∈ (I ^ n • ⊤ : Submodule A M)})
      ⟨x, by simp⟩ (fun n y => ⟨y.1 - φ (c n y.1 y.2), hcy n y.1 y.2⟩) n

  let a : ℕ → Fin k → A := fun n => c n (r n).1 (r n).2
  have haI : ∀ n i, a n i ∈ I ^ n := fun n i => hcI n (r n).1 (r n).2 i
  let S : ℕ → Fin k → A := fun n i => ∑ t ∈ Finset.range n, a t i
  have hS0 : S 0 = 0 := funext fun i => by simp [S]
  have hSsucc : ∀ n, S (n + 1) = S n + a n := fun n => funext fun i => by
    simp [S, Finset.sum_range_succ]
  have hr0 : (r 0).1 = x := rfl
  have hrsucc : ∀ n, (r (n + 1)).1 = (r n).1 - φ (a n) := fun n => rfl
  have hr : ∀ n, (r n).1 = x - φ (S n) := by
    intro n
    induction n with
    | zero => rw [hr0, hS0, map_zero, sub_zero]
    | succ n ih => rw [hrsucc, ih, hSsucc, map_add]; abel

  have hS : ∀ i m n, m ≤ n → S n i - S m i ∈ I ^ m := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hSsucc, Pi.add_apply, add_sub_right_comm]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmn (haI n i))
  have hL : ∀ i, ∃ L : A, ∀ n, S n i - L ∈ I ^ n := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I A) (f := fun n => S n i)
      (fun {m n} hmn => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, Ideal.neg_mem_iff]
        exact hS i m n hmn)
    exact ⟨L, fun n => by simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL n⟩
  choose L hL using hL

  suffices hx : x - φ L = 0 by rw [sub_eq_zero.mp hx]; exact hφN L
  refine IsHausdorff.haus (inferInstance : IsHausdorff I M) _ fun n => ?_
  rw [SModEq.zero]
  have : x - φ L = (r n).1 + φ (S n - L) := by rw [hr n, map_sub]; abel
  rw [this]
  refine Submodule.add_mem _ (r n).2 ?_
  rw [hφ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hL i n) Submodule.mem_top

namespace PowerSeries
p2m_export "PowerSeries" "coe_mul algebraMap_apply coeff_mk mk trunc eq_X_mul_shift_add_const map_surjective eval₂_X coeff_coe eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc map_X constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X X_ne_zero coe_C quotient_span_X_sub_C_pow_of_irreducible"
p2m_open "PowerSeries"

variable {A S : Type*} [CommRing A] [CommRing S]

theorem liftOfIsAdicComplete_sum_range_sub_sum_range_mem (J : Ideal S) (θ : A →+* S) (x : S)
    (hx : x ∈ J) (F : PowerSeries A) {m N : ℕ} (h : m ≤ N) :
    (Finset.range N).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) -
      (Finset.range m).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) ∈ J ^ m := by
  rw [← Finset.sum_range_add_sum_Ico _ h, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hi.1 (Ideal.pow_mem_pow hx i))

theorem liftOfIsAdicComplete_eval₂_sub_eval₂_trunc_mem (J : Ideal S) (θ : A →+* S) (x : S)
    (hx : x ∈ J) (P : Polynomial A) (n : ℕ) :
    Polynomial.eval₂ θ x P - Polynomial.eval₂ θ x (PowerSeries.trunc n (P : PowerSeries A)) ∈ J ^ n := by
  have hN : P.natDegree < max n (P.natDegree + 1) := by omega
  rw [Polynomial.eval₂_eq_sum_range' θ hN, PowerSeries.eval₂_trunc_eq_sum_range]
  simpa only [Polynomial.coeff_coe] using
    liftOfIsAdicComplete_sum_range_sub_sum_range_mem J θ x hx (P : PowerSeries A)
      (le_max_left n (P.natDegree + 1))

noncomputable def liftOfIsAdicCompleteAux (J : Ideal S) (θ : A →+* S) (x : S) (hx : x ∈ J) (n : ℕ) :
    PowerSeries A →+* S ⧸ J ^ n where
  toFun F := Ideal.Quotient.mk (J ^ n) (Polynomial.eval₂ θ x (PowerSeries.trunc n F))
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk (J ^ n)), Ideal.Quotient.eq, ← Polynomial.eval₂_one θ x,
      ← Polynomial.coe_one]
    rw [← neg_mem_iff, neg_sub]
    exact liftOfIsAdicComplete_eval₂_sub_eval₂_trunc_mem J θ x hx 1 n
  map_mul' F G := by
    rw [← map_mul, Ideal.Quotient.eq, ← Polynomial.eval₂_mul, ← PowerSeries.trunc_trunc_mul_trunc,
      ← Polynomial.coe_mul, ← neg_mem_iff, neg_sub]
    exact liftOfIsAdicComplete_eval₂_sub_eval₂_trunc_mem J θ x hx _ n
  map_zero' := by simp
  map_add' F G := by simp [Polynomial.eval₂_add]

theorem liftOfIsAdicCompleteAux_apply (J : Ideal S) (θ : A →+* S) (x : S) (hx : x ∈ J) (n : ℕ)
    (F : PowerSeries A) :
    liftOfIsAdicCompleteAux J θ x hx n F =
      Ideal.Quotient.mk (J ^ n) ((Finset.range n).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i)) := by
  simp [liftOfIsAdicCompleteAux, PowerSeries.eval₂_trunc_eq_sum_range]

theorem liftOfIsAdicCompleteAux_compat (J : Ideal S) (θ : A →+* S) (x : S) (hx : x ∈ J) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (liftOfIsAdicCompleteAux J θ x hx n) =
      liftOfIsAdicCompleteAux J θ x hx m := by
  ext F
  simp only [RingHom.comp_apply, liftOfIsAdicCompleteAux_apply, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  exact liftOfIsAdicComplete_sum_range_sub_sum_range_mem J θ x hx F hle

end PowerSeries

p2m_open_scoped "PowerSeries" in
noncomputable def PowerSeries.liftOfIsAdicComplete {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) : PowerSeries A →+* S :=
  IsAdicComplete.liftRingHom J (PowerSeries.liftOfIsAdicCompleteAux J θ x hx)
    (fun hle => PowerSeries.liftOfIsAdicCompleteAux_compat J θ x hx hle)

p2m_open_scoped "PowerSeries" in

theorem PowerSeries.liftOfIsAdicComplete_sub_sum_mem {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) (F : PowerSeries A) (n : ℕ) :
    PowerSeries.liftOfIsAdicComplete J θ x hx F -
      (Finset.range n).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) ∈ J ^ n := by
  rw [← Ideal.Quotient.eq, ← PowerSeries.liftOfIsAdicCompleteAux_apply J θ x hx]
  exact IsAdicComplete.mk_liftRingHom J _ _ n F

namespace PowerSeries
p2m_export "PowerSeries" "coe_mul algebraMap_apply coeff_mk mk trunc eq_X_mul_shift_add_const map_surjective eval₂_X coeff_coe eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc map_X constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X X_ne_zero coe_C quotient_span_X_sub_C_pow_of_irreducible"
p2m_open "PowerSeries"

variable {A S : Type*} [CommRing A] [CommRing S]

theorem liftOfIsAdicComplete_eq_of_forall_sub_mem (J : Ideal S) [IsHausdorff J S] {a b : S}
    (h : ∀ n, a - b ∈ J ^ n) : a = b := by
  refine sub_eq_zero.mp (IsHausdorff.haus ‹_› _ fun n => ?_)
  rw [SModEq.zero]
  simpa [smul_eq_mul, Ideal.mul_top] using h n

theorem liftOfIsAdicComplete_coe (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J)
    (P : Polynomial A) :
    PowerSeries.liftOfIsAdicComplete J θ x hx (P : PowerSeries A) = Polynomial.eval₂ θ x P := by
  refine liftOfIsAdicComplete_eq_of_forall_sub_mem J fun n => ?_
  have h1 := PowerSeries.liftOfIsAdicComplete_sub_sum_mem J θ x hx (P : PowerSeries A) n
  have h2 := liftOfIsAdicComplete_eval₂_sub_eval₂_trunc_mem J θ x hx P n
  rw [PowerSeries.eval₂_trunc_eq_sum_range] at h2
  simpa using sub_mem h1 h2

end PowerSeries

p2m_open_scoped "PowerSeries" in
theorem PowerSeries.liftOfIsAdicComplete_C {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) (a : A) :
    PowerSeries.liftOfIsAdicComplete J θ x hx (PowerSeries.C a) = θ a := by
  rw [← Polynomial.coe_C, PowerSeries.liftOfIsAdicComplete_coe, Polynomial.eval₂_C]

p2m_open_scoped "PowerSeries" in
theorem PowerSeries.liftOfIsAdicComplete_X {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) :
    PowerSeries.liftOfIsAdicComplete J θ x hx PowerSeries.X = x := by
  rw [← Polynomial.coe_X, PowerSeries.liftOfIsAdicComplete_coe, Polynomial.eval₂_X]

p2m_open_scoped "PowerSeries" in

theorem PowerSeries.eq_liftOfIsAdicComplete {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) (φ : PowerSeries A →+* S)
    (hC : ∀ a, φ (PowerSeries.C a) = θ a) (hX : φ PowerSeries.X = x)
    (hcont : ∀ F n, φ F - (Finset.range n).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) ∈ J ^ n) :
    φ = PowerSeries.liftOfIsAdicComplete J θ x hx := by
  have := And.intro hC hX; clear this
  refine RingHom.ext fun F => PowerSeries.liftOfIsAdicComplete_eq_of_forall_sub_mem J fun n => ?_
  simpa using sub_mem (hcont F n) (PowerSeries.liftOfIsAdicComplete_sub_sum_mem J θ x hx F n)

namespace IsIntegrallyClosed p2m_export "IsIntegrallyClosed" "isIntegral_iff of_equiv" end IsIntegrallyClosed
p2m_open_scoped "IsIntegrallyClosed" in
theorem IsIntegrallyClosed.of_faithfullyFlat (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] : IsIntegrallyClosed A := by
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  let K := FractionRing A
  let L := FractionRing B
  have hg : Function.Injective ((algebraMap B L).comp (algebraMap A B)) :=
    (IsFractionRing.injective B L).comp hinj
  let φ : K →+* L := IsFractionRing.lift hg
  have hφA : ∀ a : A, φ (algebraMap A K a) = algebraMap A L a := by
    intro a
    rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  let φₐ : K →ₐ[A] L := { φ with commutes' := hφA }
  refine (isIntegrallyClosed_iff K).mpr ?_
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hy : IsIntegral A (φₐ (algebraMap A K a / algebraMap A K b)) := hx.map φₐ
  have hyB : IsIntegral B (φₐ (algebraMap A K a / algebraMap A K b)) := hy.tower_top
  obtain ⟨β, hβ⟩ := IsIntegrallyClosed.isIntegral_iff.mp hyB
  have hφx : φₐ (algebraMap A K a / algebraMap A K b) = algebraMap A L a / algebraMap A L b := by
    change φ _ = _
    rw [map_div₀, hφA, hφA]
  rw [hφx] at hβ
  have hbL : algebraMap A L b ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B L]
    exact (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr ((map_ne_zero_iff _ hinj).mpr hb0)
  have hβ' : algebraMap B L (β * algebraMap A B b) = algebraMap B L (algebraMap A B a) := by
    rw [map_mul, hβ, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      div_mul_cancel₀ _ hbL]
  have hmem : algebraMap A B a ∈ (Ideal.span {b}).map (algebraMap A B) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨β, by rw [← IsFractionRing.injective B L hβ']; ring⟩
  have ha : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span {b}), Ideal.mem_comap]
    exact hmem
  rw [Ideal.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  refine ⟨c, ?_⟩
  have hbK : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0
  rw [map_mul, eq_div_iff hbK, mul_comm]

namespace COMP

theorem isPrecomplete_map_mk {A : Type*} [CommRing A] (I J : Ideal A) [hI : IsPrecomplete I A] :
    IsPrecomplete (I.map (Ideal.Quotient.mk J)) (A ⧸ J) := by
  constructor
  intro f hf

  have hstep : ∀ n, f (n + 1) - f n ∈ (I ^ n).map (Ideal.Quotient.mk J) := by
    intro n
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, ← Ideal.map_pow, smul_eq_mul, Ideal.mul_top] at h
    exact h

  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  choose d hd hdq using fun n => (Ideal.mem_map_iff_of_surjective _ hsurj).mp (hstep n)
  obtain ⟨g0, hg0⟩ := hsurj (f 0)
  let g : ℕ → A := fun n => Nat.rec g0 (fun k acc => acc + d k) n
  have hg_succ : ∀ n, g (n + 1) = g n + d n := fun n => rfl
  have hgf : ∀ n, Ideal.Quotient.mk J (g n) = f n := by
    intro n
    induction n with
    | zero => exact hg0
    | succ n ih => rw [hg_succ, map_add, ih, hdq]; ring

  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem, hg_succ, smul_eq_mul, Ideal.mul_top]
      have : g n - (g n + d n) = -d n := by ring
      rw [this]
      exact Submodule.neg_mem _ (Ideal.pow_le_pow_right hmn (hd n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI hgc
  refine ⟨Ideal.Quotient.mk J L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  rw [SModEq.sub_mem, ← hgf, ← map_sub, ← Ideal.map_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_map_of_mem _ h

theorem ker_powerSeries_map_of_ker_eq_span {A B : Type*} [CommRing A] [CommRing B] (π : A →+* B)
    {p : A} (hker : RingHom.ker π = Ideal.span {p}) :
    RingHom.ker (PowerSeries.map π) = Ideal.span {PowerSeries.C p} := by
  apply le_antisymm
  · intro F hF
    rw [RingHom.mem_ker] at hF
    have hc : ∀ n, p ∣ PowerSeries.coeff n F := by
      intro n
      have := congrArg (PowerSeries.coeff n) hF
      rw [PowerSeries.coeff_map, map_zero] at this
      have hmem : PowerSeries.coeff n F ∈ RingHom.ker π := this
      rw [hker, Ideal.mem_span_singleton] at hmem
      exact hmem
    choose q hq using hc
    rw [Ideal.mem_span_singleton]
    refine ⟨PowerSeries.mk q, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hq n]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, PowerSeries.map_C]
    have : π p = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self p
    rw [this, map_zero]

theorem injective_of_forall_pow_ne_zero {κ E : Type*} [Field κ] [CommRing E] (ψ : PowerSeries κ →+* E)
    (hψ : ∀ n : ℕ, (ψ PowerSeries.X) ^ n ≠ 0) : Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hF0
  have hU : IsUnit (PowerSeries.divXPowOrder F) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hF0)
  have h := congrArg ψ (PowerSeries.X_pow_order_mul_divXPowOrder (f := F))
  rw [hF, map_mul, map_pow] at h
  apply hψ F.order.toNat
  have hu := hU.map ψ
  exact (hu.mul_left_eq_zero).mp h

end COMP

namespace COMP

theorem smul_injective_of_flat {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    {r : R} (hr : r ≠ 0) : Function.Injective (fun m : M => r • m) :=
  (Module.Flat.isTorsionFree (R := R) (M := M)).isSMulRegular (isRegular_of_ne_zero hr)
end COMP

namespace COMP
open IsLocalRing Polynomial
noncomputable section
set_option synthInstance.maxHeartbeats 800000

section W
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) [hϖ : Fact (Irreducible ϖ)]

abbrev IW : Ideal (PowerSeries O) := Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C (ϖ ^ 1)}
abbrev W : Type _ := PowerSeries O ⧸ IW ϖ

abbrev ϖW : W ϖ := Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)

theorem W_facts : (IW ϖ).IsPrime ∧ IsPrincipalIdealRing (W ϖ) ∧ IsLocalRing (W ϖ) ∧ Irreducible (ϖW ϖ) :=
  PowerSeries.quotient_span_X_sub_C_pow_of_irreducible ϖ hϖ.out 1 le_rfl

scoped instance : (IW ϖ).IsPrime := (W_facts ϖ).1
scoped instance : IsDomain (W ϖ) := Ideal.Quotient.isDomain _
scoped instance : IsPrincipalIdealRing (W ϖ) := (W_facts ϖ).2.1
scoped instance : IsLocalRing (W ϖ) := (W_facts ϖ).2.2.1
theorem ϖW_irreducible : Irreducible (ϖW ϖ) := (W_facts ϖ).2.2.2
scoped instance : IsDiscreteValuationRing (W ϖ) :=
  ⟨fun h0 => (ϖW_irreducible ϖ).ne_zero (by
    have hmem : ϖW ϖ ∈ maximalIdeal (W ϖ) := (ϖW_irreducible ϖ).not_isUnit
    rw [h0] at hmem; exact hmem)⟩

theorem maximalIdeal_W : maximalIdeal (W ϖ) = Ideal.span {ϖW ϖ} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (ϖW_irreducible ϖ)

theorem mk_X_eq_ϖW : Ideal.Quotient.mk (IW ϖ) PowerSeries.X = ϖW ϖ := by
  rw [Ideal.Quotient.eq]
  simpa using Ideal.subset_span (by rfl : (PowerSeries.X : PowerSeries O) - PowerSeries.C (ϖ ^ 1) ∈ _)

theorem maximalIdeal_W_eq_map : maximalIdeal (W ϖ) = (Ideal.span {PowerSeries.X}).map (Ideal.Quotient.mk (IW ϖ)) := by
  rw [maximalIdeal_W, Ideal.map_span, Set.image_singleton, mk_X_eq_ϖW]

scoped instance : IsPrecomplete (maximalIdeal (W ϖ)) (W ϖ) := by
  rw [maximalIdeal_W_eq_map]; exact isPrecomplete_map_mk _ _

scoped instance instIsAdicCompleteW : IsAdicComplete (maximalIdeal (W ϖ)) (W ϖ) where

end W

section Rh
variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

abbrev Rh (R : Type*) [CommRing R] [IsLocalRing R] : Type _ := AdicCompletion (maximalIdeal R) R

abbrev mh (R : Type*) [CommRing R] [IsLocalRing R] : Ideal (Rh R) := (maximalIdeal R).map (algebraMap R (Rh R))

scoped instance : IsAdicComplete (maximalIdeal R) (Rh R) := AdicCompletion.isAdicComplete (IsNoetherian.noetherian _)
scoped instance : IsAdicComplete (mh R) (Rh R) := (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance
scoped instance : Module.Flat R (Rh R) := AdicCompletion.flat_of_isNoetherian _

theorem algebraMap_Rh_apply (r : R) : algebraMap R (Rh R) r = AdicCompletion.of (maximalIdeal R) R r := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem algebraMap_Rh_injective : Function.Injective (algebraMap R (Rh R)) := by
  intro a b hab
  rw [algebraMap_Rh_apply, algebraMap_Rh_apply] at hab
  exact AdicCompletion.of_injective (maximalIdeal R) R hab

theorem exists_sub_algebraMap_mem (n : ℕ) (x : Rh R) :
    ∃ r : R, x - algebraMap R (Rh R) r ∈ ((maximalIdeal R) ^ n • ⊤ : Submodule R (Rh R)) := by
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal R) R n x)
  refine ⟨r, ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian _), LinearMap.mem_ker, map_sub,
    algebraMap_Rh_apply, AdicCompletion.eval_of, ← hr, sub_eq_zero]
  rfl

scoped instance : Module.FaithfullyFlat R (Rh R) := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun I hI htop => ?_⟩
  have hle : (I • ⊤ : Submodule R (Rh R)) ≤ (maximalIdeal R) ^ 1 • ⊤ := by
    rw [pow_one]; exact Submodule.smul_mono_left (IsLocalRing.le_maximalIdeal hI)
  rw [htop, top_le_iff, AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian _)] at hle
  have hsurj := AdicCompletion.eval_surjective (maximalIdeal R) R 1
  have hne : ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R) ≠ ⊤ := by
    rw [pow_one, smul_eq_mul, Ideal.mul_top]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R)) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨q, hq⟩ := exists_ne (0 : R ⧸ ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R))
  obtain ⟨x, rfl⟩ := hsurj q
  have hx : x ∈ LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R 1) := hle ▸ Submodule.mem_top
  exact hq (LinearMap.mem_ker.mp hx)

end Rh

section Maps
variable {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Algebra O R]
  (ϖ : O) [Fact (Irreducible ϖ)]
  (hϖm : algebraMap O R ϖ ∈ maximalIdeal R)

abbrev ϖR : Rh R := algebraMap R (Rh R) (algebraMap O R ϖ)

include hϖm in
theorem ϖR_mem : ϖR (R := R) ϖ ∈ mh R := Ideal.mem_map_of_mem _ hϖm

def θ₀ : PowerSeries O →+* Rh R :=
  PowerSeries.liftOfIsAdicComplete (mh R) ((algebraMap R (Rh R)).comp (algebraMap O R)) (ϖR ϖ) (ϖR_mem ϖ hϖm)

theorem θ₀_C (a : O) : θ₀ ϖ hϖm (PowerSeries.C a) = algebraMap R (Rh R) (algebraMap O R a) :=
  PowerSeries.liftOfIsAdicComplete_C _ _ _ _ a

theorem θ₀_X : θ₀ ϖ hϖm PowerSeries.X = ϖR (R := R) ϖ :=
  PowerSeries.liftOfIsAdicComplete_X _ _ _ _

def θW : W ϖ →+* Rh R :=
  Ideal.Quotient.lift (IW ϖ) (θ₀ ϖ hϖm) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_sub, θ₀_X, pow_one, θ₀_C, sub_self, zero_mul])

theorem θW_mk (F : PowerSeries O) : θW ϖ hϖm (Ideal.Quotient.mk (IW ϖ) F) = θ₀ ϖ hϖm F :=
  Ideal.Quotient.lift_mk _ _ _

theorem θW_ϖW : θW ϖ hϖm (ϖW ϖ) = ϖR (R := R) ϖ := by
  rw [θW_mk, θ₀_C]

theorem θW_const (a : O) :
    θW ϖ hϖm (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C a)) = algebraMap R (Rh R) (algebraMap O R a) := by
  rw [θW_mk, θ₀_C]

variable (g h w : R) (hw : IsUnit w) (hgm : g ∈ maximalIdeal R) (hhm : h ∈ maximalIdeal R)

abbrev gR : Rh R := algebraMap R (Rh R) g

abbrev sR : Rh R := algebraMap R (Rh R) (g + h * ↑(hw.unit⁻¹))

include hgm hhm in
theorem sR_mem : sR g h w hw ∈ mh R :=
  Ideal.mem_map_of_mem _ (Ideal.add_mem _ hgm (Ideal.mul_mem_right _ _ hhm))

def ρ : PowerSeries (W ϖ) →+* Rh R :=
  PowerSeries.liftOfIsAdicComplete (mh R) (θW ϖ hϖm) (sR g h w hw) (sR_mem g h w hw hgm hhm)

theorem ρ_C (a : W ϖ) : ρ ϖ hϖm g h w hw hgm hhm (PowerSeries.C a) = θW ϖ hϖm a :=
  PowerSeries.liftOfIsAdicComplete_C _ _ _ _ a

theorem ρ_X : ρ ϖ hϖm g h w hw hgm hhm PowerSeries.X = sR g h w hw :=
  PowerSeries.liftOfIsAdicComplete_X _ _ _ _

variable (e : ℕ)

abbrev cqW : (PowerSeries (W ϖ))[X] :=
  Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries (W ϖ)) * Polynomial.X +
    Polynomial.C (PowerSeries.C (ϖW ϖ ^ e))

variable (hgh : g * h = algebraMap O R ϖ ^ e * w)

include hgh in
theorem eval₂_cqW : Polynomial.eval₂ (ρ ϖ hϖm g h w hw hgm hhm) (gR g) (cqW ϖ e) = 0 := by
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, ρ_X, ρ_C, map_pow, θW_ϖW]

  have hu : (w : R) * ↑(hw.unit⁻¹) = 1 := hw.mul_val_inv
  have key : g ^ 2 - (g + h * ↑(hw.unit⁻¹)) * g + algebraMap O R ϖ ^ e = 0 := by
    have : h * g = algebraMap O R ϖ ^ e * w := by rw [mul_comm, hgh]
    linear_combination (-(↑(hw.unit⁻¹) : R)) * this - (algebraMap O R ϖ ^ e) * hu
  have := congrArg (algebraMap R (Rh R)) key
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at this
  simp only [gR, sR, map_add, map_mul]
  linear_combination this

def Φ : AdjoinRoot (cqW ϖ e) →+* Rh R :=
  AdjoinRoot.lift (ρ ϖ hϖm g h w hw hgm hhm) (gR g) (eval₂_cqW ϖ hϖm g h w hw hgm hhm e hgh)

theorem Φ_of (F : PowerSeries (W ϖ)) :
    Φ ϖ hϖm g h w hw hgm hhm e hgh (AdjoinRoot.of _ F) = ρ ϖ hϖm g h w hw hgm hhm F :=
  AdjoinRoot.lift_of _

theorem Φ_root : Φ ϖ hϖm g h w hw hgm hhm e hgh (AdjoinRoot.root _) = gR g :=
  AdjoinRoot.lift_root _

end Maps

section Inj
variable {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Algebra O R]
  (ϖ : O) [Fact (Irreducible ϖ)]
  (hϖm : algebraMap O R ϖ ∈ maximalIdeal R)
  (g h w : R) (hw : IsUnit w) (hgm : g ∈ maximalIdeal R) (hhm : h ∈ maximalIdeal R)
  (e : ℕ) (hgh : g * h = algebraMap O R ϖ ^ e * w)

abbrev ϖA : PowerSeries (W ϖ) := PowerSeries.C (ϖW ϖ)

abbrev κ := ResidueField (W ϖ)
abbrev mapπ : PowerSeries (W ϖ) →+* PowerSeries (κ ϖ) := PowerSeries.map (residue (W ϖ))

theorem ker_residue_W : RingHom.ker (residue (W ϖ)) = Ideal.span {ϖW ϖ} := by
  rw [IsLocalRing.ker_residue, maximalIdeal_W]

theorem ker_mapπ : RingHom.ker (mapπ ϖ) = Ideal.span {ϖA ϖ} :=
  ker_powerSeries_map_of_ker_eq_span _ (ker_residue_W ϖ)

theorem mapπ_surjective : Function.Surjective (mapπ ϖ) :=
  PowerSeries.map_surjective _ (IsLocalRing.residue_surjective)

theorem isPrime_span_ϖA : (Ideal.span {ϖA ϖ}).IsPrime := by
  rw [← ker_mapπ]
  exact RingHom.ker_isPrime _

theorem exists_factor (P : Ideal R) (hP : algebraMap O R ϖ ∈ P) :
    ∃ ψ : PowerSeries (κ ϖ) →+* Rh R ⧸ P.map (algebraMap R (Rh R)),
      ψ.comp (mapπ ϖ) = (Ideal.Quotient.mk _).comp (ρ ϖ hϖm g h w hw hgm hhm) := by
  have hker : RingHom.ker (mapπ ϖ) ≤ RingHom.ker ((Ideal.Quotient.mk (P.map (algebraMap R (Rh R)))).comp
      (ρ ϖ hϖm g h w hw hgm hhm)) := by
    rw [ker_mapπ, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      RingHom.comp_apply, ρ_C, θW_ϖW, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hP
  refine ⟨RingHom.liftOfRightInverse (mapπ ϖ) (Function.surjInv (mapπ_surjective ϖ))
    (Function.rightInverse_surjInv (mapπ_surjective ϖ)) ⟨_, hker⟩, ?_⟩
  ext1 F
  exact RingHom.liftOfRightInverse_comp_apply (mapπ ϖ) (Function.surjInv (mapπ_surjective ϖ))
    (Function.rightInverse_surjInv (mapπ_surjective ϖ)) ⟨_, hker⟩ F

theorem ker_comp_ρ_eq (P : Ideal R) [P.IsPrime] (hP : algebraMap O R ϖ ∈ P)
    (hs : ∀ n : ℕ, (Ideal.Quotient.mk (P.map (algebraMap R (Rh R)))) (sR g h w hw ^ n) ≠ 0) :
    RingHom.ker ((Ideal.Quotient.mk (P.map (algebraMap R (Rh R)))).comp (ρ ϖ hϖm g h w hw hgm hhm)) =
      Ideal.span {ϖA ϖ} := by
  obtain ⟨ψ, hψ⟩ := exists_factor ϖ hϖm g h w hw hgm hhm P hP
  have hinjψ : Function.Injective ψ := by
    apply injective_of_forall_pow_ne_zero
    intro n
    have hX : ψ PowerSeries.X = Ideal.Quotient.mk _ (sR g h w hw) := by
      have := congrArg (fun φ => φ PowerSeries.X) hψ
      simp only [RingHom.comp_apply, PowerSeries.map_X] at this
      rw [this, ρ_X]
    rw [hX, ← map_pow]
    exact hs n
  rw [← hψ, ← ker_mapπ ϖ]
  ext F
  simp only [RingHom.mem_ker, RingHom.comp_apply]
  constructor
  · intro hF; exact hinjψ (by rw [hF, map_zero])
  · intro hF; rw [hF, map_zero]

variable (hm : maximalIdeal R = Ideal.span {algebraMap O R ϖ, g, h})
  (hg : (Ideal.span {algebraMap O R ϖ, g}).IsPrime) (hh : (Ideal.span {algebraMap O R ϖ, h}).IsPrime)
  (hhg : h ∉ Ideal.span {algebraMap O R ϖ, g}) (hgh' : g ∉ Ideal.span {algebraMap O R ϖ, h})

include hh hgh' in

theorem sR_pow_ne_zero_mod_h (n : ℕ) :
    (Ideal.Quotient.mk ((Ideal.span {algebraMap O R ϖ, h}).map (algebraMap R (Rh R)))) (sR g h w hw ^ n) ≠ 0 := by
  haveI := hh
  set P := Ideal.span {algebraMap O R ϖ, h} with hPdef
  have hsg : (Ideal.Quotient.mk (P.map (algebraMap R (Rh R)))) (sR g h w hw) =
      (Ideal.Quotient.mk (P.map (algebraMap R (Rh R)))) (gR g) := by
    rw [Ideal.Quotient.eq, sR, gR, ← map_sub, add_sub_cancel_left]
    exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  rw [map_pow, hsg, ← map_pow, gR, ← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem,
    ← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat]
  exact fun hmem => hgh' (hh.mem_of_pow_mem n hmem)

include hg hhg in

theorem sR_pow_ne_zero_mod_g (n : ℕ) :
    (Ideal.Quotient.mk ((Ideal.span {algebraMap O R ϖ, g}).map (algebraMap R (Rh R)))) (sR g h w hw ^ n) ≠ 0 := by
  haveI := hg
  set P := Ideal.span {algebraMap O R ϖ, g} with hPdef
  have hsg : (Ideal.Quotient.mk (P.map (algebraMap R (Rh R)))) (sR g h w hw) =
      (Ideal.Quotient.mk (P.map (algebraMap R (Rh R)))) (algebraMap R (Rh R) (h * ↑(hw.unit⁻¹))) := by
    rw [Ideal.Quotient.eq, sR, ← map_sub, add_sub_cancel_right]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  rw [map_pow, hsg, ← map_pow, ← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem,
    ← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat, mul_pow]
  intro hmem
  have h1 : h ^ n ∈ P := by
    rcases hg.mem_or_mem hmem with h1 | h1
    · exact h1
    · exfalso
      have hu : IsUnit ((↑(hw.unit⁻¹) : R) ^ n) := (Units.isUnit _).pow n
      exact hg.ne_top (P.eq_top_of_isUnit_mem h1 hu)
  exact hhg (hg.mem_of_pow_mem n h1)

theorem exists_eq_of_add_of_mul_root (x : AdjoinRoot (cqW ϖ e)) :
    ∃ a b : PowerSeries (W ϖ), x = AdjoinRoot.of _ a + AdjoinRoot.of _ b * AdjoinRoot.root _ := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hq : cqW ϖ e = Polynomial.X ^ 2 + Polynomial.C (-(PowerSeries.X : PowerSeries (W ϖ))) * Polynomial.X +
      Polynomial.C (PowerSeries.C (ϖW ϖ ^ e)) := by
    simp only [cqW, Polynomial.C_neg]; ring
  have hmonic : (cqW ϖ e).Monic := by rw [hq]; monicity!
  have hdeg : (cqW ϖ e).natDegree = 2 := by rw [hq]; compute_degree!
  have hf1 : cqW ϖ e ≠ 1 := by
    intro h1; rw [h1, Polynomial.natDegree_one] at hdeg; exact absurd hdeg (by norm_num)
  have hpmod : AdjoinRoot.mk (cqW ϖ e) p = AdjoinRoot.mk (cqW ϖ e) (p %ₘ cqW ϖ e) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ cqW ϖ e, by linear_combination -(Polynomial.modByMonic_add_div p (cqW ϖ e))⟩
  have hle : (p %ₘ cqW ϖ e).natDegree ≤ 1 := by
    have := Polynomial.natDegree_modByMonic_lt p hmonic hf1
    rw [hdeg] at this; omega
  refine ⟨(p %ₘ cqW ϖ e).coeff 0, (p %ₘ cqW ϖ e).coeff 1, ?_⟩
  rw [hpmod]
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hle]
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  ring

include hg hh hhg hgh' in

theorem exists_eq_mul_of_Φ_eq_zero (hϖ0 : algebraMap O R ϖ ≠ 0) (x : AdjoinRoot (cqW ϖ e))
    (hx : Φ ϖ hϖm g h w hw hgm hhm e hgh x = 0) :
    ∃ x' : AdjoinRoot (cqW ϖ e), x = AdjoinRoot.of _ (ϖA ϖ) * x' ∧ Φ ϖ hϖm g h w hw hgm hhm e hgh x' = 0 := by
  haveI := hg; haveI := hh
  obtain ⟨a, b, rfl⟩ := exists_eq_of_add_of_mul_root ϖ e x
  rw [map_add, map_mul, Φ_of, Φ_of, Φ_root] at hx
  have hϖO : algebraMap O R ϖ ∈ Ideal.span {algebraMap O R ϖ, h} := Ideal.subset_span (by simp)
  have hϖO' : algebraMap O R ϖ ∈ Ideal.span {algebraMap O R ϖ, g} := Ideal.subset_span (by simp)

  have h2 := ker_comp_ρ_eq ϖ hϖm g h w hw hgm hhm (Ideal.span {algebraMap O R ϖ, h}) hϖO
    (sR_pow_ne_zero_mod_h ϖ g h w hw hh hgh')
  have hab : a + PowerSeries.X * b ∈ Ideal.span {ϖA ϖ} := by
    rw [← h2, RingHom.mem_ker, RingHom.comp_apply, map_add, map_mul, ρ_X]
    have hsg : (Ideal.Quotient.mk ((Ideal.span {algebraMap O R ϖ, h}).map (algebraMap R (Rh R)))) (sR g h w hw) =
        (Ideal.Quotient.mk ((Ideal.span {algebraMap O R ϖ, h}).map (algebraMap R (Rh R)))) (gR g) := by
      rw [Ideal.Quotient.eq, sR, gR, ← map_sub, add_sub_cancel_left]
      exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    rw [map_add, map_mul, hsg, ← map_mul, ← map_add, mul_comm, hx, map_zero]

  have h1 := ker_comp_ρ_eq ϖ hϖm g h w hw hgm hhm (Ideal.span {algebraMap O R ϖ, g}) hϖO'
    (sR_pow_ne_zero_mod_g ϖ g h w hw hg hhg)
  have ha : a ∈ Ideal.span {ϖA ϖ} := by
    rw [← h1, RingHom.mem_ker, RingHom.comp_apply]
    have hg0 : (Ideal.Quotient.mk ((Ideal.span {algebraMap O R ϖ, g}).map (algebraMap R (Rh R)))) (gR g) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
    have := congrArg (Ideal.Quotient.mk ((Ideal.span {algebraMap O R ϖ, g}).map (algebraMap R (Rh R)))) hx
    rw [map_add, map_mul, hg0, mul_zero, add_zero, map_zero] at this
    exact this
  have hb : b ∈ Ideal.span {ϖA ϖ} := by
    have hXb : PowerSeries.X * b ∈ Ideal.span {ϖA ϖ} := by
      have := Ideal.sub_mem _ hab ha
      rwa [add_sub_cancel_left] at this
    rcases (isPrime_span_ϖA ϖ).mem_or_mem hXb with hX | hb
    · exfalso
      rw [← ker_mapπ, RingHom.mem_ker, PowerSeries.map_X] at hX
      exact PowerSeries.X_ne_zero hX
    · exact hb
  rw [Ideal.mem_span_singleton] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  refine ⟨AdjoinRoot.of _ a' + AdjoinRoot.of _ b' * AdjoinRoot.root _, by rw [map_mul, map_mul]; ring, ?_⟩

  have hzero : ϖR ϖ * (ρ ϖ hϖm g h w hw hgm hhm a' + ρ ϖ hϖm g h w hw hgm hhm b' * gR g) = 0 := by
    rw [map_mul, map_mul, ρ_C, θW_ϖW] at hx
    linear_combination hx
  rw [map_add, map_mul, Φ_of, Φ_of, Φ_root]
  rw [ϖR, ← Algebra.smul_def] at hzero
  exact smul_injective_of_flat (M := Rh R) hϖ0 (hzero.trans (smul_zero _).symm)

end Inj

section Surj
variable {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Algebra O R]
  (ϖ : O) [Fact (Irreducible ϖ)]
  (hϖm : algebraMap O R ϖ ∈ maximalIdeal R)
  (g h w : R) (hw : IsUnit w) (hgm : g ∈ maximalIdeal R) (hhm : h ∈ maximalIdeal R)
  (e : ℕ) (he : 1 ≤ e) (hgh : g * h = algebraMap O R ϖ ^ e * w)
  (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
  (hm : maximalIdeal R = Ideal.span {algebraMap O R ϖ, g, h})

abbrev JR : Ideal R := Ideal.span {algebraMap O R ϖ, g + h * ↑(hw.unit⁻¹)}

include he hgh hm in
theorem maximalIdeal_sq_le_JR : (maximalIdeal R) ^ 2 ≤ JR ϖ g h w hw := by
  have hu : (w : R) * ↑(hw.unit⁻¹) = 1 := hw.mul_val_inv
  have hpe : algebraMap O R ϖ ^ e = algebraMap O R ϖ * algebraMap O R ϖ ^ (e - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hm, pow_two, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  dsimp only
  rw [SetLike.mem_coe, Ideal.mem_span_pair]
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb]
  · exact ⟨algebraMap O R ϖ, 0, by ring⟩
  · exact ⟨g, 0, by ring⟩
  · exact ⟨h, 0, by ring⟩
  · exact ⟨g, 0, by ring⟩
  · refine ⟨-(algebraMap O R ϖ ^ (e - 1)), g, ?_⟩
    linear_combination (↑(hw.unit⁻¹) : R) * hgh + (algebraMap O R ϖ ^ e) * hu + hpe
  · exact ⟨algebraMap O R ϖ ^ (e - 1) * w, 0, by rw [hgh, hpe]; ring⟩
  · exact ⟨h, 0, by ring⟩
  · exact ⟨algebraMap O R ϖ ^ (e - 1) * w, 0, by rw [mul_comm h g, hgh, hpe]; ring⟩
  · refine ⟨-(algebraMap O R ϖ ^ (e - 1) * w * w), h * w, ?_⟩
    linear_combination (w * w) * hpe + w * hgh + (h * h) * hu

include hres in

theorem exists_sub_algebraMap_mem_maximalIdeal (r : R) : ∃ o : O, r - algebraMap O R o ∈ maximalIdeal R := by
  obtain ⟨o, ho⟩ := hres (IsLocalRing.residue R r)
  refine ⟨o, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ho.symm

include he hgh hres hm hgm in

theorem exists_sub_mem_JR (r : R) :
    ∃ o₀ o₁ : O, r - (algebraMap O R o₀ + algebraMap O R o₁ * g) ∈ JR ϖ g h w hw := by
  have hu : (w : R) * ↑(hw.unit⁻¹) = 1 := hw.mul_val_inv
  obtain ⟨o₀, h₀⟩ := exists_sub_algebraMap_mem_maximalIdeal hres r
  rw [hm] at h₀
  obtain ⟨c₁, z, hz, hcz⟩ := Ideal.mem_span_insert.mp h₀
  obtain ⟨c₂, c₃, rfl⟩ := Ideal.mem_span_pair.mp hz

  obtain ⟨o₁, h₁⟩ := exists_sub_algebraMap_mem_maximalIdeal hres (c₂ - c₃ * w)
  refine ⟨o₀, o₁, ?_⟩
  have hsq := maximalIdeal_sq_le_JR ϖ g h w hw e he hgh hm

  have hdecomp : r - (algebraMap O R o₀ + algebraMap O R o₁ * g) =
      c₁ * algebraMap O R ϖ + (c₃ * w) * (g + h * ↑(hw.unit⁻¹)) + (c₂ - c₃ * w - algebraMap O R o₁) * g := by
    linear_combination hcz - (c₃ * h) * hu
  rw [hdecomp]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · apply hsq
    rw [pow_two]
    exact Ideal.mul_mem_mul h₁ hgm

include he hgh hres hm in
theorem Φ_surjective : Function.Surjective (Φ ϖ hϖm g h w hw hgm hhm e hgh) := by
  let ρ' : PowerSeries (W ϖ) →+* Rh R := ρ ϖ hϖm g h w hw hgm hhm
  letI : Algebra (PowerSeries (W ϖ)) (Rh R) := ρ'.toAlgebra
  have halg : algebraMap (PowerSeries (W ϖ)) (Rh R) = ρ' := rfl
  let J : Ideal (PowerSeries (W ϖ)) :=
    (maximalIdeal (W ϖ)).map (PowerSeries.C : W ϖ →+* PowerSeries (W ϖ)) ⊔ Ideal.span {PowerSeries.X}
  haveI : IsAdicComplete J (PowerSeries (W ϖ)) := PowerSeries.isAdicComplete_map_C_sup_span_X _
  have hJ : J.map ρ' ≤ mh R := by
    rw [Ideal.map_sup, Ideal.map_map, maximalIdeal_W, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton, sup_le_iff]
    constructor <;> rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    · rw [RingHom.comp_apply, ρ_C, θW_ϖW]; exact ϖR_mem ϖ hϖm
    · rw [ρ_X]; exact sR_mem g h w hw hgm hhm
  have hJR : (JR ϖ g h w hw).map (algebraMap R (Rh R)) ≤ J.map ρ' := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have : algebraMap R (Rh R) (algebraMap O R ϖ) = ρ' (PowerSeries.C (ϖW ϖ)) := by rw [ρ_C, θW_ϖW]
      rw [SetLike.mem_coe, this]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left
        (Ideal.mem_map_of_mem _ ((ϖW_irreducible ϖ).not_isUnit)))
    · have : algebraMap R (Rh R) (g + h * ↑(hw.unit⁻¹)) = ρ' PowerSeries.X := by rw [ρ_X]
      rw [SetLike.mem_coe, this]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

  haveI : IsHausdorff J (Rh R) := by
    refine ⟨fun x hx => ?_⟩
    apply IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal R) (Rh R))
    intro n
    have hn := hx n
    rw [SModEq.zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, halg] at hn
    rw [SModEq.zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    have : (J ^ n).map ρ' ≤ ((maximalIdeal R) ^ n).map (algebraMap R (Rh R)) := by
      rw [Ideal.map_pow, Ideal.map_pow]
      exact Ideal.pow_right_mono hJ n
    exact this hn

  let N : Submodule (PowerSeries (W ϖ)) (Rh R) := Submodule.span (PowerSeries (W ϖ)) {1, gR g}
  have hN : N.FG := Submodule.fg_span (Set.toFinite _)
  have key : N ⊔ J • ⊤ = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem 2 y
    obtain ⟨o₀, o₁, hoo⟩ := exists_sub_mem_JR ϖ g h w hw hgm e he hgh hres hm r

    have hJtop : ∀ z : Rh R, z ∈ J.map ρ' → z ∈ (J • ⊤ : Submodule (PowerSeries (W ϖ)) (Rh R)) := by
      intro z hz
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, halg]
      exact hz
    have h1 : y - algebraMap R (Rh R) r ∈ (J • ⊤ : Submodule (PowerSeries (W ϖ)) (Rh R)) := by
      apply hJtop
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at hr
      exact hJR (Ideal.map_mono (maximalIdeal_sq_le_JR ϖ g h w hw e he hgh hm) hr)
    have h2 : algebraMap R (Rh R) r - (algebraMap R (Rh R) (algebraMap O R o₀) +
        algebraMap R (Rh R) (algebraMap O R o₁) * gR g) ∈ (J • ⊤ : Submodule (PowerSeries (W ϖ)) (Rh R)) := by
      apply hJtop
      have := Ideal.mem_map_of_mem (algebraMap R (Rh R)) hoo
      rw [map_sub, map_add, map_mul] at this
      exact hJR this
    have h3 : algebraMap R (Rh R) (algebraMap O R o₀) + algebraMap R (Rh R) (algebraMap O R o₁) * gR g ∈ N := by
      rw [Submodule.mem_span_pair]
      refine ⟨PowerSeries.C (Ideal.Quotient.mk _ (PowerSeries.C o₀)), PowerSeries.C (Ideal.Quotient.mk _ (PowerSeries.C o₁)), ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, halg, ρ_C, ρ_C, θW_const, θW_const, mul_one]
    have : y = (algebraMap R (Rh R) (algebraMap O R o₀) + algebraMap R (Rh R) (algebraMap O R o₁) * gR g) +
        ((algebraMap R (Rh R) r - (algebraMap R (Rh R) (algebraMap O R o₀) +
          algebraMap R (Rh R) (algebraMap O R o₁) * gR g)) + (y - algebraMap R (Rh R) r)) := by ring
    rw [this]
    exact Submodule.add_mem_sup h3 (Submodule.add_mem _ h2 h1)
  have hNtop := Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top J N hN key
  intro y
  have hy : y ∈ N := hNtop ▸ Submodule.mem_top
  rw [Submodule.mem_span_pair] at hy
  obtain ⟨a, b, rfl⟩ := hy
  refine ⟨AdjoinRoot.of _ a + AdjoinRoot.of _ b * AdjoinRoot.root _, ?_⟩
  rw [map_add, map_mul, Φ_of, Φ_of, Φ_root, Algebra.smul_def, Algebra.smul_def, halg, mul_one]

end Surj

section Assembly

theorem isPrecomplete_pow {R : Type*} [CommRing R] (I : Ideal R) [h : IsPrecomplete I R]
    (e : ℕ) (he : 1 ≤ e) : IsPrecomplete (I ^ e) R := by
  refine ⟨fun {f} hf => ?_⟩
  have hf' : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n hmn
    have := hf hmn
    refine SModEq.mono ?_ this
    apply Submodule.smul_mono_left
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by nlinarith)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' f hf'
  refine ⟨L, fun n => ?_⟩
  have h1 : f n ≡ f (e * n) [SMOD (I ^ e) ^ n • (⊤ : Submodule R R)] := hf (by nlinarith)
  have h2 : f (e * n) ≡ L [SMOD I ^ (e * n) • (⊤ : Submodule R R)] := hL (e * n)
  rw [← pow_mul] at h1 ⊢
  exact h1.trans h2

variable {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Algebra O R]
  (ϖ : O) [Fact (Irreducible ϖ)]

theorem main
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
    (g h w : R) (hw : IsUnit w) (e : ℕ) (he : 1 ≤ e)
    (hgh : g * h = algebraMap O R ϖ ^ e * w)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap O R ϖ, g, h})
    (hg : (Ideal.span {algebraMap O R ϖ, g}).IsPrime) (hh : (Ideal.span {algebraMap O R ϖ, h}).IsPrime)
    (hhg : h ∉ Ideal.span {algebraMap O R ϖ, g}) (hgh' : g ∉ Ideal.span {algebraMap O R ϖ, h}) :
    IsIntegrallyClosed R := by
  have hϖm : algebraMap O R ϖ ∈ maximalIdeal R := by rw [hm]; exact Ideal.subset_span (by simp)
  have hgm : g ∈ maximalIdeal R := by rw [hm]; exact Ideal.subset_span (by simp)
  have hhm : h ∈ maximalIdeal R := by rw [hm]; exact Ideal.subset_span (by simp)
  have hϖ0 : algebraMap O R ϖ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega), zero_mul] at hgh
    rcases mul_eq_zero.mp hgh with h1 | h1
    · exact hgh' (h1 ▸ Ideal.zero_mem _)
    · exact hhg (h1 ▸ Ideal.zero_mem _)
  have hc0 : ϖW ϖ ^ e ≠ 0 := pow_ne_zero _ (ϖW_irreducible ϖ).ne_zero
  have hcu : ¬IsUnit (ϖW ϖ ^ e) := fun hu =>
    (ϖW_irreducible ϖ).not_isUnit ((isUnit_pow_iff (by omega)).mp hu)
  haveI : IsPrecomplete (Ideal.span {ϖW ϖ ^ e}) (W ϖ) := by
    rw [← Ideal.span_singleton_pow, ← maximalIdeal_W]
    exact isPrecomplete_pow _ e he

  obtain ⟨eqv, -, -⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_adjoinRoot_of_isPrecomplete (ϖW ϖ ^ e) hc0 hcu
  obtain ⟨hdom, hloc, hic⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete (ϖW ϖ) (ϖW_irreducible ϖ) e he
  haveI := hdom; haveI := hloc; haveI := hic
  haveI hnoethSrc : IsNoetherianRing (ModularCurve.UVCrossingModel (W ϖ) (ϖW ϖ ^ e)) :=
    ModularCurve.UVCrossingModel.isNoetherianRing _

  haveI : IsNoetherianRing (AdjoinRoot (cqW ϖ e)) :=
    isNoetherianRing_of_ringEquiv (ModularCurve.UVCrossingModel (W ϖ) (ϖW ϖ ^ e)) eqv
  haveI : IsDomain (AdjoinRoot (cqW ϖ e)) :=
    MulEquiv.isDomain (ModularCurve.UVCrossingModel (W ϖ) (ϖW ϖ ^ e)) eqv.symm.toMulEquiv

  let Φ' := Φ ϖ hϖm g h w hw hgm hhm e hgh
  have hstep := exists_eq_mul_of_Φ_eq_zero ϖ hϖm g h w hw hgm hhm e hgh hg hh hhg hgh' hϖ0
  have hne : Ideal.span {AdjoinRoot.of (cqW ϖ e) (ϖA ϖ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := (hu.map Φ').map (AdicCompletion.evalₐ (maximalIdeal R) 1)
    rw [show Φ' (AdjoinRoot.of (cqW ϖ e) (ϖA ϖ)) = ϖR ϖ by rw [Φ_of, ρ_C, θW_ϖW], ϖR,
      algebraMap_Rh_apply, AdicCompletion.evalₐ_of] at h1
    have h0 : (Ideal.Quotient.mk ((maximalIdeal R) ^ 1) (algebraMap O R ϖ)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [pow_one]; exact hϖm)
    rw [h0] at h1
    haveI : Nontrivial (R ⧸ (maximalIdeal R) ^ 1) :=
      Ideal.Quotient.nontrivial_iff.mpr (by rw [pow_one]; exact (maximalIdeal.isMaximal R).ne_top)
    exact not_isUnit_zero h1
  have hkrull := Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {AdjoinRoot.of (cqW ϖ e) (ϖA ϖ)}) hne
  have hinj : Function.Injective Φ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hmem : ∀ n, ∀ y, Φ' y = 0 → y ∈ (Ideal.span {AdjoinRoot.of (cqW ϖ e) (ϖA ϖ)}) ^ n := by
      intro n
      induction n with
      | zero => intro y _; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
      | succ n ih =>
        intro y hy
        obtain ⟨y', rfl, hy'⟩ := hstep y hy
        rw [pow_succ']
        exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (ih y' hy')
    have : x ∈ (⨅ n, (Ideal.span {AdjoinRoot.of (cqW ϖ e) (ϖA ϖ)}) ^ n : Ideal _) :=
      Ideal.mem_iInf.mpr (fun n => hmem n x hx)
    rwa [hkrull, Ideal.mem_bot] at this
  have hsurj := Φ_surjective ϖ hϖm g h w hw hgm hhm e he hgh hres hm
  let ΦE := RingEquiv.ofBijective Φ' ⟨hinj, hsurj⟩
  let E := eqv.trans ΦE
  haveI : IsDomain (Rh R) := MulEquiv.isDomain (ModularCurve.UVCrossingModel (W ϖ) (ϖW ϖ ^ e)) E.symm.toMulEquiv
  haveI : IsIntegrallyClosed (Rh R) :=
    @IsIntegrallyClosed.of_equiv (ModularCurve.UVCrossingModel (W ϖ) (ϖW ϖ ^ e)) (Rh R) _ _ E hic
  exact IsIntegrallyClosed.of_faithfullyFlat R (Rh R)

end Assembly

end

end COMP
p2m_reactivate "P2MW.S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit.COMP"

theorem solution
    {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Algebra O R]
    (ϖ : O) (hϖ : Irreducible ϖ)
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
    (g h w : R) (hw : IsUnit w) (e : ℕ) (he : 1 ≤ e)
    (hgh : g * h = algebraMap O R ϖ ^ e * w)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap O R ϖ, g, h})
    (hg : (Ideal.span {algebraMap O R ϖ, g}).IsPrime) (hh : (Ideal.span {algebraMap O R ϖ, h}).IsPrime)
    (hhg : h ∉ Ideal.span {algebraMap O R ϖ, g}) (hgh' : g ∉ Ideal.span {algebraMap O R ϖ, h})
    (h2 : IsUnit (2 : R)) :
    IsIntegrallyClosed R := by
  haveI : Fact (Irreducible ϖ) := ⟨hϖ⟩
  exact COMP.main ϖ hres g h w hw e he hgh hm hg hh hhg hgh'

end S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit
end P2MW
export P2MW.S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit (solution)
