-- Prove2me | solution 1 for IsLocalRing.exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/afc385ea-b043-571d-af52-9736ec4247ca

import Mathlib
import Theorems.Thm_IsLocalRing_comap_map_adicCompletion_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace PowerSeries
p2m_export "PowerSeries" "coe_mul constantCoeff_C algebraMap_apply coeff_mk mk trunc eq_X_mul_shift_add_const map_surjective eval₂_X coeff_coe eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc map_X coeff_smul constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X coe_C algebraMap_eq"
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

namespace PowerSeries p2m_export "PowerSeries" "coe_mul constantCoeff_C algebraMap_apply coeff_mk mk trunc eq_X_mul_shift_add_const map_surjective eval₂_X coeff_coe eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc map_X coeff_smul constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X coe_C algebraMap_eq" end PowerSeries
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

namespace Submodule p2m_export "Submodule" "Quotient.eq span_singleton_le_iff_mem mem_sup_right smul_mem' mk smul_mem mem_span_singleton_self Quotient.mk span restrictScalars smul_induction_on mem_sInf mem_map_of_mem add_mem_sup span_le mem_comap mem_span_range_iff_exists_fun pow_mem_pow mul_le mem_top mem_span_singleton fg_iff_exists_fin_generating_family mul_mem_mul smul_mem_smul generators nontrivial_iff map_smul' zero one map_span Quotient.mk_surjective map rec Quotient.nontrivial_iff mem_sup smul_mono_left subset_span eq_bot_of_le_smul_of_le_jacobson_bot module smul_def FG ext mem_span_finset factor_mk add comap factorPow map_sup fg_span mem_sup_left map_le_iff_le_comap restrictScalars_mem" end Submodule
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
p2m_export "PowerSeries" "coe_mul constantCoeff_C algebraMap_apply coeff_mk mk trunc eq_X_mul_shift_add_const map_surjective eval₂_X coeff_coe eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc map_X coeff_smul constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X coe_C algebraMap_eq"
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
p2m_export "PowerSeries" "coe_mul constantCoeff_C algebraMap_apply coeff_mk mk trunc eq_X_mul_shift_add_const map_surjective eval₂_X coeff_coe eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc map_X coeff_smul constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X coe_C algebraMap_eq"
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

open TensorProduct in
section
open TensorProduct

namespace KEYFSMB

noncomputable def smulMap {W : Type*} [CommRing W] (I : Ideal W) (M : Type*) [AddCommGroup M] [Module W M] :
    I ⊗[W] M →ₗ[W] M :=
  TensorProduct.lift ((LinearMap.lsmul W M).comp I.subtype)

theorem smulMap_tmul {W : Type*} [CommRing W] (I : Ideal W) {M : Type*} [AddCommGroup M] [Module W M]
    (i : I) (m : M) : smulMap I M (i ⊗ₜ m) = (i : W) • m := by
  simp [smulMap]

theorem smulMap_injective_of_flat {W : Type*} [CommRing W] (I : Ideal W) (N : Type*) [AddCommGroup N] [Module W N]
    [Module.Flat W N] : Function.Injective (smulMap I N) := by
  have h1 : Function.Injective (LinearMap.rTensor N I.subtype) := Module.Flat.iff_rTensor_injective'.mp inferInstance I
  have : smulMap I N = (TensorProduct.lid W N).toLinearMap ∘ₗ LinearMap.rTensor N I.subtype := by
    apply TensorProduct.ext'
    intro i n
    simp [smulMap, LinearMap.rTensor_tmul]
  rw [this]
  exact (TensorProduct.lid W N).injective.comp h1

theorem exists_smulMap_eq_of_mem_smul_top {W : Type*} [CommRing W] (I : Ideal W) {M : Type*} [AddCommGroup M] [Module W M]
    (y : M) (hy : y ∈ I • (⊤ : Submodule W M)) : ∃ ξ : I ⊗[W] M, smulMap I M ξ = y := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr f _
    exact ⟨⟨r, hr⟩ ⊗ₜ f, smulMap_tmul I ⟨r, hr⟩ f⟩
  · rintro a b ⟨ξ, rfl⟩ ⟨η, rfl⟩
    exact ⟨ξ + η, map_add _ _ _⟩

theorem smulMap_lTensor {W : Type*} [CommRing W] (I : Ideal W) {M M' : Type*} [AddCommGroup M] [Module W M]
    [AddCommGroup M'] [Module W M'] (g : M →ₗ[W] M') (ζ : I ⊗[W] M) :
    smulMap I M' (LinearMap.lTensor I g ζ) = g (smulMap I M ζ) := by
  induction ζ using TensorProduct.induction_on with
  | zero => simp
  | tmul i f => rw [LinearMap.lTensor_tmul, smulMap_tmul, smulMap_tmul, map_smul]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]

theorem smulMap_mem_smul {W : Type*} [CommRing W] (I : Ideal W) {M : Type*} [AddCommGroup M] [Module W M]
    (K : Submodule W M) (η : I ⊗[W] K) : smulMap I M (LinearMap.lTensor I K.subtype η) ∈ I • K := by
  induction η using TensorProduct.induction_on with
  | zero => simp
  | tmul i k =>
    rw [LinearMap.lTensor_tmul, smulMap_tmul]
    exact Submodule.smul_mem_smul i.2 k.2
  | add a b ha hb =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

theorem mem_smul_ker_of_flat {W F N : Type*} [CommRing W] [AddCommGroup F] [Module W F]
    [AddCommGroup N] [Module W N] [Module.Flat W N]
    (θ : F →ₗ[W] N) (hθ : Function.Surjective θ) (I : Ideal W) (x : F) (hxK : θ x = 0)
    (hxI : x ∈ I • (⊤ : Submodule W F)) : x ∈ I • (LinearMap.ker θ) := by
  classical
  obtain ⟨ξ, rfl⟩ := exists_smulMap_eq_of_mem_smul_top I x hxI
  have h0 : LinearMap.lTensor I θ ξ = 0 :=
    smulMap_injective_of_flat I N (by rw [smulMap_lTensor, hxK, map_zero])
  have hex : Function.Exact (LinearMap.lTensor I (LinearMap.ker θ).subtype) (LinearMap.lTensor I θ) :=
    lTensor_exact I (LinearMap.exact_subtype_ker_map θ) hθ
  obtain ⟨η, hη⟩ := (hex ξ).mp h0
  rw [← hη]
  exact smulMap_mem_smul I (LinearMap.ker θ) η

end KEYFSMB

end

namespace KEYFSMB
open IsLocalRing

section Rh
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

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

section Theta
variable {W R : Type*} [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra W R] [IsLocalHom (algebraMap W R)]
  (t : R) (ht : maximalIdeal R = (maximalIdeal W).map (algebraMap W R) ⊔ Ideal.span {t})
  (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap W R)))

abbrev tR : Rh R := algebraMap R (Rh R) t

include ht in
theorem t_mem : t ∈ maximalIdeal R := by
  rw [ht]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)

include ht in
theorem tR_mem : tR t ∈ mh R := Ideal.mem_map_of_mem _ (t_mem t ht)

def θ : PowerSeries W →+* Rh R :=
  PowerSeries.liftOfIsAdicComplete (mh R) ((algebraMap R (Rh R)).comp (algebraMap W R)) (tR t) (tR_mem t ht)

theorem θ_C (a : W) : θ t ht (PowerSeries.C a) = algebraMap R (Rh R) (algebraMap W R a) :=
  PowerSeries.liftOfIsAdicComplete_C _ _ _ _ a

theorem θ_X : θ t ht PowerSeries.X = tR t :=
  PowerSeries.liftOfIsAdicComplete_X _ _ _ _

include hres in
theorem exists_sub_algebraMap_mem_maximalIdeal (r : R) : ∃ o : W, r - algebraMap W R o ∈ maximalIdeal R := by
  obtain ⟨o, ho⟩ := hres (IsLocalRing.residue R r)
  refine ⟨o, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ho.symm

include hres in
theorem θ_surjective : Function.Surjective (θ t ht) := by
  let B := PowerSeries W
  let ρ' : B →+* Rh R := θ t ht
  letI : Algebra B (Rh R) := ρ'.toAlgebra
  have halg : algebraMap B (Rh R) = ρ' := rfl
  let J : Ideal B := (maximalIdeal W).map (PowerSeries.C : W →+* B) ⊔ Ideal.span {PowerSeries.X}
  haveI : IsAdicComplete J B := PowerSeries.isAdicComplete_map_C_sup_span_X _

  have hJ : J.map ρ' ≤ mh R := by
    rw [Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton, sup_le_iff]
    refine ⟨?_, ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.comp_apply]
      show ρ' (PowerSeries.C a) ∈ mh R
      rw [show ρ' (PowerSeries.C a) = algebraMap R (Rh R) (algebraMap W R a) from θ_C t ht a]
      refine Ideal.mem_map_of_mem _ ?_
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      exact fun hu => ha (IsLocalHom.map_nonunit a hu)
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, show ρ' PowerSeries.X = tR t from θ_X t ht]
      exact tR_mem t ht

  have hmJ : mh R ≤ J.map ρ' := by
    rw [mh, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [ht] at hx
    rw [Ideal.mem_comap]
    refine Submodule.mem_sup.mp hx |> fun ⟨y, hy, z, hz, hyz⟩ => ?_
    rw [← hyz, map_add]
    refine Ideal.add_mem _ ?_ ?_
    ·
      have hle : (maximalIdeal W).map (algebraMap W R) ≤ ((J.map ρ').comap (algebraMap R (Rh R))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, Ideal.mem_comap,
          show algebraMap R (Rh R) (algebraMap W R a) = ρ' (PowerSeries.C a) from (θ_C t ht a).symm]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
      exact hle hy
    · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      rw [map_mul, show algebraMap R (Rh R) t = ρ' PowerSeries.X from (θ_X t ht).symm]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

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

  let N : Submodule B (Rh R) := Submodule.span B {1}
  have hN : N.FG := Submodule.fg_span (Set.toFinite _)
  have key : N ⊔ J • ⊤ = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem 1 y
    obtain ⟨o, ho⟩ := exists_sub_algebraMap_mem_maximalIdeal hres r
    have hJtop : ∀ z : Rh R, z ∈ J.map ρ' → z ∈ (J • ⊤ : Submodule B (Rh R)) := by
      intro z hz
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, halg]
      exact hz
    have h1 : y - algebraMap R (Rh R) r ∈ (J • ⊤ : Submodule B (Rh R)) := by
      apply hJtop
      rw [pow_one, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at hr
      exact hmJ hr
    have h2 : algebraMap R (Rh R) r - algebraMap R (Rh R) (algebraMap W R o) ∈ (J • ⊤ : Submodule B (Rh R)) := by
      apply hJtop
      have := Ideal.mem_map_of_mem (algebraMap R (Rh R)) ho
      rw [map_sub] at this
      exact hmJ this
    have h3 : algebraMap R (Rh R) (algebraMap W R o) ∈ N := by
      rw [Submodule.mem_span_singleton]
      refine ⟨PowerSeries.C o, ?_⟩
      rw [Algebra.smul_def, halg, show ρ' (PowerSeries.C o) = _ from θ_C t ht o, mul_one]
    have : y = algebraMap R (Rh R) (algebraMap W R o) +
        ((algebraMap R (Rh R) r - algebraMap R (Rh R) (algebraMap W R o)) + (y - algebraMap R (Rh R) r)) := by ring
    rw [this]
    exact Submodule.add_mem_sup h3 (Submodule.add_mem _ h2 h1)
  have hNtop := Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top J N hN key
  intro y
  have hy : y ∈ N := hNtop ▸ Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hy
  obtain ⟨b, rfl⟩ := hy
  exact ⟨b, by rw [Algebra.smul_def, halg, mul_one]⟩

end Theta

section CoeffLemmas
variable {A : Type*} [CommRing A]

theorem PowerSeries_mem_smul_top_of_forall_coeff_mem (I : Ideal A) (hI : I.FG) (x : PowerSeries A)
    (hx : ∀ n, PowerSeries.coeff n x ∈ I) : x ∈ I • (⊤ : Submodule A (PowerSeries A)) := by
  classical
  obtain ⟨s, hs⟩ := hI

  have hc : ∀ n, ∃ c : s → A, ∑ i, c i * (i : A) = PowerSeries.coeff n x := by
    intro n
    have := hx n
    rw [← hs, Ideal.span, Submodule.mem_span_finset] at this
    obtain ⟨c, -, hc⟩ := this
    refine ⟨fun i => c i, ?_⟩
    rw [← hc]
    simp only [smul_eq_mul]
    exact (Finset.sum_coe_sort s (fun i => c i * i))
  choose c hc using hc
  have : x = ∑ i : s, (i : A) • PowerSeries.mk (fun n => c n i) := by
    ext n
    simp only [map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_mk, smul_eq_mul]
    rw [← hc n]
    simp only [mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hs ▸ Ideal.subset_span i.2) Submodule.mem_top

end CoeffLemmas

section Inj
variable {W R : Type*} [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra W R] [IsLocalHom (algebraMap W R)] [Module.Flat W R]
  (t : R) (ht : maximalIdeal R = (maximalIdeal W).map (algebraMap W R) ⊔ Ideal.span {t})
  (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap W R)))
  (hdim : ringKrullDim (R ⧸ (maximalIdeal W).map (algebraMap W R)) = 1)

include ht hdim in

theorem pow_not_mem (m : ℕ) : t ^ m ∉ (maximalIdeal W).map (algebraMap W R) := by
  intro hm
  set J : Ideal R := (maximalIdeal W).map (algebraMap W R) with hJ
  have hJle : J ≤ maximalIdeal R := by rw [ht]; exact le_sup_left
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hJle))
  haveI : Nontrivial (R ⧸ J) := ⟨⟨0, 1, fun h => hJne (Ideal.Quotient.zero_eq_one_iff.mp h)⟩⟩

  have h0 : Ring.KrullDimLE 0 (R ⧸ J) := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_

    have htP : Ideal.Quotient.mk J t ∈ P := by
      have : (Ideal.Quotient.mk J t) ^ m = 0 := by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hm
      exact hP.mem_of_pow_mem m (this.symm ▸ P.zero_mem)
    have hmP : (maximalIdeal R).map (Ideal.Quotient.mk J) ≤ P := by
      rw [ht, Ideal.map_sup, Ideal.map_span, Set.image_singleton, sup_le_iff]
      refine ⟨?_, (Ideal.span_singleton_le_iff_mem _).mpr htP⟩
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
      exact P.zero_mem
    have hmax : ((maximalIdeal R).map (Ideal.Quotient.mk J)).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
        (maximalIdeal.isMaximal R) with h | h
      · exact absurd (top_le_iff.mp (h ▸ hmP)) hP.ne_top
      · exact h
    rw [hmax.eq_of_le hP.ne_top hmP] at hmax
    exact hmax
  have h1 := (Ring.krullDimLE_iff (n := 0) (R := R ⧸ J)).mp h0
  rw [hdim] at h1
  exact absurd h1 (by norm_num)

include ht hres hdim in
theorem θ_injective : Function.Injective (θ t ht) := by
  classical
  haveI : Module.Flat W (Rh R) := Module.Flat.trans W R (Rh R)
  let F := PowerSeries W
  let k := ResidueField W

  have hθC : ∀ a : W, θ t ht (PowerSeries.C a) = algebraMap R (Rh R) (algebraMap W R a) := fun a => θ_C t ht a
  let θₗ : F →ₗ[W] Rh R :=
    { toFun := θ t ht
      map_add' := map_add _
      map_smul' := fun a g => by
        rw [Algebra.smul_def, PowerSeries.algebraMap_eq, map_mul, hθC, RingHom.id_apply,
          ← IsScalarTower.algebraMap_smul R a (θ t ht g), Algebra.smul_def] }
  have hθₗ : ∀ g, θₗ g = θ t ht g := fun g => rfl

  let 𝔐 : Ideal (Rh R) := ((maximalIdeal W).map (algebraMap W R)).map (algebraMap R (Rh R))
  let π : F →+* PowerSeries k := PowerSeries.map (IsLocalRing.residue W)
  have hπ : Function.Surjective π := PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective
  have hkerπ : ∀ y : F, π y = 0 ↔ ∀ n, PowerSeries.coeff n y ∈ maximalIdeal W := by
    intro y
    rw [PowerSeries.ext_iff]
    refine forall_congr' fun n => ?_
    rw [PowerSeries.coeff_map, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem
  let θbar : F →+* Rh R ⧸ 𝔐 := (Ideal.Quotient.mk 𝔐).comp (θ t ht)
  have hθbar_ker : ∀ y ∈ RingHom.ker π, θbar y = 0 := by
    intro y hy
    rw [RingHom.mem_ker, hkerπ] at hy
    have hyI : y ∈ (maximalIdeal W) • (⊤ : Submodule W F) :=
      PowerSeries_mem_smul_top_of_forall_coeff_mem _ (IsNoetherian.noetherian _) y hy
    show Ideal.Quotient.mk 𝔐 (θₗ y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Submodule.smul_induction_on hyI ?_ ?_
    · intro a ha g _
      rw [map_smul, ← IsScalarTower.algebraMap_smul R a, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha))
    · intro u v hu hv; rw [map_add]; exact Ideal.add_mem _ hu hv
  let ψ : PowerSeries k →+* Rh R ⧸ 𝔐 :=
    (Ideal.Quotient.lift (RingHom.ker π) θbar hθbar_ker).comp
      (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψπ : ∀ y : F, ψ (π y) = θbar y := by
    intro y
    show Ideal.Quotient.lift (RingHom.ker π) θbar hθbar_ker ((RingHom.quotientKerEquivOfSurjective hπ).symm (π y)) = θbar y
    have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π y) = Ideal.Quotient.mk (RingHom.ker π) y := by
      apply (RingHom.quotientKerEquivOfSurjective hπ).injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [this, Ideal.Quotient.lift_mk]
  have hψX : ψ PowerSeries.X = Ideal.Quotient.mk 𝔐 (tR t) := by
    have : (PowerSeries.X : PowerSeries k) = π PowerSeries.X := (PowerSeries.map_X _).symm
    rw [this, hψπ]
    show Ideal.Quotient.mk 𝔐 (θ t ht PowerSeries.X) = _
    rw [θ_X]
  have hψinj : Function.Injective ψ := by
    apply COMP.injective_of_forall_pow_ne_zero
    intro m hm
    rw [hψX, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← map_pow] at hm

    have := Ideal.mem_comap.mpr hm
    rw [IsLocalRing.comap_map_adicCompletion_eq] at this
    exact pow_not_mem t ht hdim m this

  have hK : ∀ x : F, θ t ht x = 0 → x ∈ (maximalIdeal W) • (⊤ : Submodule W F) := by
    intro x hx
    have h1 : ψ (π x) = 0 := by
      rw [hψπ]; show Ideal.Quotient.mk 𝔐 (θ t ht x) = 0; rw [hx, map_zero]
    have h2 : π x = 0 := hψinj (h1.trans (map_zero ψ).symm)
    exact PowerSeries_mem_smul_top_of_forall_coeff_mem _ (IsNoetherian.noetherian _) x ((hkerπ x).mp h2)

  let K : Ideal F := RingHom.ker (θ t ht)
  have hKeq : (K.restrictScalars W : Submodule W F) = LinearMap.ker θₗ := by
    ext x; rfl
  have hKle : K ≤ ((maximalIdeal W).map (PowerSeries.C : W →+* F)) * K := by
    intro x hx
    have hx0 : θ t ht x = 0 := hx
    have hpur : x ∈ (maximalIdeal W) • (LinearMap.ker θₗ) :=
      mem_smul_ker_of_flat θₗ (θ_surjective t ht hres) (maximalIdeal W) x hx0 (hK x hx0)

    refine Submodule.smul_induction_on hpur ?_ ?_
    · intro a ha g hg
      rw [Algebra.smul_def, PowerSeries.algebraMap_eq]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha) hg
    · intro u v hu hv; exact Ideal.add_mem _ hu hv
  have hjac : (maximalIdeal W).map (PowerSeries.C : W →+* F) ≤ (⊥ : Ideal F).jacobson := by
    intro g hg
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    haveI : M.IsMaximal := hM
    rw [IsLocalRing.eq_maximalIdeal hM]
    refine (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_) hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      PowerSeries.constantCoeff_C]
    exact ha
  have hKfg : K.FG := (IsNoetherian.noetherian K)
  have hK0 : K = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot ((maximalIdeal W).map (PowerSeries.C : W →+* F)) K hKfg
      (by rw [smul_eq_mul]; exact hKle) hjac
  intro x y hxy
  have : x - y ∈ K := by rw [RingHom.mem_ker, map_sub, hxy, sub_self]
  rw [hK0] at this
  exact sub_eq_zero.mp this

end Inj

end KEYFSMB
p2m_reactivate "P2MW.S_IsLocalRing_exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span.KEYFSMB"

open KEYFSMB IsLocalRing in
theorem solution
    (W : Type*) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra W R]
    [IsLocalHom (algebraMap W R)] [Module.Flat W R]
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap W R)))
    (t : R) (ht : maximalIdeal R = (maximalIdeal W).map (algebraMap W R) ⊔ Ideal.span {t})
    (hdim : ringKrullDim (R ⧸ (maximalIdeal W).map (algebraMap W R)) = 1) :
    ∃ e : AdicCompletion (maximalIdeal R) R ≃+* PowerSeries W,
      (∀ a : W, e (algebraMap R (AdicCompletion (maximalIdeal R) R) (algebraMap W R a)) = PowerSeries.C a) ∧
        e (algebraMap R (AdicCompletion (maximalIdeal R) R) t) = PowerSeries.X := by
  classical
  let e₀ := RingEquiv.ofBijective (θ t ht) ⟨θ_injective t ht hres hdim, θ_surjective t ht hres⟩
  refine ⟨e₀.symm, fun a => ?_, ?_⟩
  · apply e₀.injective
    rw [RingEquiv.apply_symm_apply]
    exact (θ_C t ht a).symm
  · apply e₀.injective
    rw [RingEquiv.apply_symm_apply]
    exact (θ_X t ht).symm

end
end S_IsLocalRing_exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span
end P2MW
export P2MW.S_IsLocalRing_exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span (solution)
