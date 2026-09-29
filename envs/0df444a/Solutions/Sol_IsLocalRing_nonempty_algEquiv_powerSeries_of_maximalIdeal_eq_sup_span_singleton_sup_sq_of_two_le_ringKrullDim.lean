-- Prove2me | solution 1 for IsLocalRing.nonempty_algEquiv_powerSeries_of_maximalIdeal_eq_sup_span_singleton_sup_sq_of_two_le_ringKrullDim
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6d8616ca-3648-5b0d-8aa1-36f7599938ef

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_nonempty_algEquiv_powerSeries_of_maximalIdeal_eq_sup_span_singleton_sup_sq_of_two_le_ringKrullDim

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace PowerSeries
p2m_export "PowerSeries" "coe_mul constantCoeff_C coeff_mk mk trunc eq_X_mul_shift_add_const C_eq_algebraMap eval₂_X coeff_coe eq_shift_mul_X_add_const eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc constantCoeff coe_one eval₂_C coeff_mul coe_X isUnit_iff_constantCoeff ext map C coeff X coe_C"
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

namespace PowerSeries p2m_export "PowerSeries" "coe_mul constantCoeff_C coeff_mk mk trunc eq_X_mul_shift_add_const C_eq_algebraMap eval₂_X coeff_coe eq_shift_mul_X_add_const eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc constantCoeff coe_one eval₂_C coeff_mul coe_X isUnit_iff_constantCoeff ext map C coeff X coe_C" end PowerSeries
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

namespace Submodule p2m_export "Submodule" "le_of_le_smul_of_le_jacobson_bot Quotient.eq span_singleton_le_iff_mem mem_sup_right smul_mem' mk smul_mem mem_span_singleton_self Quotient.mk span smul_induction_on mem_map_of_mem add_mem_sup span_le mem_comap mem_span_range_iff_exists_fun pow_mem_pow mul_le spanFinrank_span_le_ncard_of_finite mem_top mem_span_singleton fg_iff_exists_fin_generating_family spanFinrank mul_mem_mul smul_mem_smul generators map_smul' zero one map_span map rec mem_sup exists_mem_ne_zero_of_ne_bot subset_span module smul_def FG ext factor_mk factorPow map_sup fg_span mem_sup_left map_le_iff_le_comap restrictScalars_mem" end Submodule
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
p2m_export "PowerSeries" "coe_mul constantCoeff_C coeff_mk mk trunc eq_X_mul_shift_add_const C_eq_algebraMap eval₂_X coeff_coe eq_shift_mul_X_add_const eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc constantCoeff coe_one eval₂_C coeff_mul coe_X isUnit_iff_constantCoeff ext map C coeff X coe_C"
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
p2m_export "PowerSeries" "coe_mul constantCoeff_C coeff_mk mk trunc eq_X_mul_shift_add_const C_eq_algebraMap eval₂_X coeff_coe eq_shift_mul_X_add_const eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc constantCoeff coe_one eval₂_C coeff_mul coe_X isUnit_iff_constantCoeff ext map C coeff X coe_C"
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

namespace F6A

open IsLocalRing

variable {W R : Type} [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra W R] [IsAdicComplete (maximalIdeal R) R]
  (hloc : ∀ a ∈ maximalIdeal W, algebraMap W R a ∈ maximalIdeal R)
  (t : R) (ht : maximalIdeal R = (maximalIdeal W).map (algebraMap W R) ⊔ Ideal.span {t})
  (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap W R)))

include ht in
theorem t_mem : t ∈ maximalIdeal R := by
  rw [ht]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)

def θ : PowerSeries W →+* R :=
  PowerSeries.liftOfIsAdicComplete (maximalIdeal R) (algebraMap W R) t (t_mem t ht)

theorem θ_C (a : W) : θ t ht (PowerSeries.C a) = algebraMap W R a :=
  PowerSeries.liftOfIsAdicComplete_C _ _ _ _ a

theorem θ_X : θ t ht PowerSeries.X = t :=
  PowerSeries.liftOfIsAdicComplete_X _ _ _ _

include hres in
theorem exists_sub_algebraMap_mem_maximalIdeal (r : R) : ∃ o : W, r - algebraMap W R o ∈ maximalIdeal R := by
  obtain ⟨o, ho⟩ := hres (IsLocalRing.residue R r)
  refine ⟨o, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ho.symm

include hloc hres in
theorem θ_surjective : Function.Surjective (θ t ht) := by
  let B := PowerSeries W
  let ρ' : B →+* R := θ t ht
  letI : Algebra B R := ρ'.toAlgebra
  have halg : algebraMap B R = ρ' := rfl
  let J : Ideal B := (maximalIdeal W).map (PowerSeries.C : W →+* B) ⊔ Ideal.span {PowerSeries.X}
  haveI : IsAdicComplete J B := PowerSeries.isAdicComplete_map_C_sup_span_X _

  have hJ : J.map ρ' ≤ maximalIdeal R := by
    rw [Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton, sup_le_iff]
    refine ⟨?_, ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.comp_apply]
      show ρ' (PowerSeries.C a) ∈ maximalIdeal R
      rw [show ρ' (PowerSeries.C a) = algebraMap W R a from θ_C t ht a]
      exact hloc a ha
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, show ρ' PowerSeries.X = t from θ_X t ht]
      exact t_mem t ht

  have hmJ : maximalIdeal R ≤ J.map ρ' := by
    intro x hx
    rw [ht] at hx
    refine Submodule.mem_sup.mp hx |> fun ⟨y, hy, z, hz, hyz⟩ => ?_
    rw [← hyz]
    refine Ideal.add_mem _ ?_ ?_
    · have hle : (maximalIdeal W).map (algebraMap W R) ≤ J.map ρ' := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, show algebraMap W R a = ρ' (PowerSeries.C a) from (θ_C t ht a).symm]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
      exact hle hy
    · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      rw [show t = ρ' PowerSeries.X from (θ_X t ht).symm]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

  haveI : IsHausdorff J R := by
    refine ⟨fun x hx => ?_⟩
    apply IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal R) R)
    intro n
    have hn := hx n
    rw [SModEq.zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, halg] at hn
    rw [SModEq.zero, Ideal.smul_top_eq_map]
    have : (J ^ n).map ρ' ≤ (maximalIdeal R) ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hJ n
    simpa using this hn

  let N : Submodule B R := Submodule.span B {1}
  have hN : N.FG := Submodule.fg_span (Set.toFinite _)
  have key : N ⊔ J • ⊤ = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨o, ho⟩ := exists_sub_algebraMap_mem_maximalIdeal hres y
    have hJtop : ∀ z : R, z ∈ J.map ρ' → z ∈ (J • ⊤ : Submodule B R) := by
      intro z hz
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, halg]
      exact hz
    have h2 : y - algebraMap W R o ∈ (J • ⊤ : Submodule B R) := hJtop _ (hmJ ho)
    have h3 : algebraMap W R o ∈ N := by
      rw [Submodule.mem_span_singleton]
      refine ⟨PowerSeries.C o, ?_⟩
      rw [Algebra.smul_def, halg, show ρ' (PowerSeries.C o) = _ from θ_C t ht o, mul_one]
    have : y = algebraMap W R o + (y - algebraMap W R o) := by ring
    rw [this]
    exact Submodule.add_mem_sup h3 h2
  have hNtop := Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top J N hN key
  intro y
  have hy : y ∈ N := hNtop ▸ Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hy
  obtain ⟨b, rfl⟩ := hy
  exact ⟨b, by rw [Algebra.smul_def, halg, mul_one]⟩

end F6A

open IsLocalRing in
theorem solution
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
    (t : R)
    (ht : IsLocalRing.maximalIdeal R =
      (IsLocalRing.maximalIdeal O).map (algebraMap O R) ⊔ Ideal.span {t} ⊔ (IsLocalRing.maximalIdeal R) ^ 2)
    (hdim : 2 ≤ ringKrullDim R) :
    Nonempty (R ≃ₐ[O] PowerSeries O) := by
  classical

  have hloc : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ maximalIdeal R := by
    intro a ha
    have hker : RingHom.ker ((IsLocalRing.residue R).comp (algebraMap O R)) = maximalIdeal O := by
      have hmax : (RingHom.ker ((IsLocalRing.residue R).comp (algebraMap O R))).IsMaximal :=
        RingHom.ker_isMaximal_of_surjective _ hres
      exact IsLocalRing.eq_maximalIdeal hmax
    have : a ∈ RingHom.ker ((IsLocalRing.residue R).comp (algebraMap O R)) := hker ▸ ha
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff] at this
    exact this

  have ht' : maximalIdeal R = (maximalIdeal O).map (algebraMap O R) ⊔ Ideal.span {t} := by
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R)
        (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _)
      rw [Ideal.smul_eq_mul, ← pow_two]
      exact ht.le
    · rw [ht]; exact le_sup_left

  let θ := F6A.θ t ht'
  have hθs : Function.Surjective θ := F6A.θ_surjective hloc t ht' hres

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmO : maximalIdeal O = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hmB : maximalIdeal (PowerSeries O) = Ideal.span {PowerSeries.C ϖ, PowerSeries.X} := by
    apply le_antisymm
    · intro f hf
      have hc : PowerSeries.constantCoeff f ∈ maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf ⊢
        exact fun hu => hf (PowerSeries.isUnit_iff_constantCoeff.mpr hu)
      rw [hmO, Ideal.mem_span_singleton'] at hc
      obtain ⟨a, ha⟩ := hc
      have : f = PowerSeries.C a * PowerSeries.C ϖ + (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f) * PowerSeries.X := by
        rw [← map_mul, ha]
        exact (PowerSeries.eq_shift_mul_X_add_const f).trans (add_comm _ _)
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · rw [Ideal.span_le]
      intro f hf
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl
      · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
          PowerSeries.constantCoeff_C]
        exact hϖ.not_isUnit
      · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
        simp
  have hdimB : ringKrullDim (PowerSeries O) ≤ 2 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h1 := Ideal.height_le_spanFinrank (maximalIdeal (PowerSeries O)) (Ideal.IsMaximal.ne_top inferInstance)
    have h2 : Submodule.spanFinrank (maximalIdeal (PowerSeries O)) ≤ 2 := by
      rw [hmB]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have h3 : (maximalIdeal (PowerSeries O)).height ≤ 2 := h1.trans (by exact_mod_cast h2)
    have h4 : ((maximalIdeal (PowerSeries O)).height : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr h3
    exact h4.trans (le_of_eq (by norm_cast))

  have hθi : Function.Injective θ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hP
    obtain ⟨f, hfP, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hfnz : f ∈ nonZeroDivisors (PowerSeries O) := mem_nonZeroDivisors_of_ne_zero hf0
    have hq := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hfnz

    have hle : Ideal.span {f} ≤ RingHom.ker θ := (Ideal.span_singleton_le_iff_mem _).mpr hfP
    have hsurj : Function.Surjective ((Ideal.Quotient.lift (Ideal.span {f}) θ
        (fun a ha => (RingHom.mem_ker).mp (hle ha))) ) := by
      intro r; obtain ⟨x, rfl⟩ := hθs r; exact ⟨Ideal.Quotient.mk _ x, rfl⟩
    have hR : ringKrullDim R ≤ ringKrullDim (PowerSeries O ⧸ Ideal.span {f}) := ringKrullDim_le_of_surjective _ hsurj
    have key : (2 : WithBot ℕ∞) + 1 ≤ 2 :=
      ((add_le_add (hdim.trans hR) (le_refl (1 : WithBot ℕ∞))).trans hq).trans hdimB
    have hne : ¬ ((2 : WithBot ℕ∞) + 1 ≤ 2) := by
      first
        | decide
        | norm_num
        | simp
        | (intro h; exact absurd h (by decide))
    exact hne key

  let θₐ : PowerSeries O →ₐ[O] R :=
    { toRingHom := θ
      commutes' := fun a => by
        show θ (algebraMap O (PowerSeries O) a) = algebraMap O R a
        rw [show algebraMap O (PowerSeries O) a = PowerSeries.C a from PowerSeries.C_eq_algebraMap.symm]
        exact F6A.θ_C t ht' a }
  exact ⟨(AlgEquiv.ofBijective θₐ ⟨hθi, hθs⟩).symm⟩

end
end S_IsLocalRing_nonempty_algEquiv_powerSeries_of_maximalIdeal_eq_sup_span_singleton_sup_sq_of_two_le_ringKrullDim
end P2MW
export P2MW.S_IsLocalRing_nonempty_algEquiv_powerSeries_of_maximalIdeal_eq_sup_span_singleton_sup_sq_of_two_le_ringKrullDim (solution)
