-- Prove2me | solution 1 for MvFormalGroup.exists_map_padicInt_eq_of_log
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/40ce87d4-4f4b-543a-b95b-1b9ef794c3b3

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_map_padicInt_eq_of_log

set_option autoImplicit false

universe u

noncomputable section

open MvPowerSeries

namespace MvFormalGroupU2

section LogType

variable {R : Type*} [CommRing R] {d : ℕ} {τ : Type*} (p : ℕ) [hp : Fact p.Prime]

theorem single_pow_injective :
    Function.Injective (fun kj : ℕ × Fin d => Finsupp.single kj.2 (p ^ kj.1)) := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  have hne : (p ^ k : ℕ) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h with ⟨hj, hk⟩ | ⟨h0, _⟩
  · have hkk : k = k' := Nat.pow_right_injective hp.out.two_le hk
    have hjj : j = j' := hj
    rw [hkk, hjj]
  · exact absurd h0 hne

theorem coeff_subst_logType
    (F : MvPowerSeries (Fin d) R) (b : ℕ → Fin d → R)
    (hF3 : ∀ j k, coeff (Finsupp.single j (p ^ k)) F = b k j)
    (hF4 : ∀ e, (∀ j k, e ≠ Finsupp.single j (p ^ k)) → coeff e F = 0)
    (g : Fin d → MvPowerSeries τ R) (hg : ∀ j, (g j).constantCoeff = 0)
    (e : τ →₀ ℕ) (M : ℕ) (hM : ∀ j k, M ≤ k → coeff e (g j ^ p ^ k) = 0) :
    coeff e (subst g F) = ∑ k ∈ Finset.range M, ∑ j : Fin d, b k j * coeff e (g j ^ p ^ k) := by
  classical
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hg)]
  set φ : (Fin d →₀ ℕ) → R := fun m => coeff m F • coeff e (m.prod fun s n => g s ^ n) with hφ
  have hprod : ∀ (j : Fin d) (n : ℕ), (Finsupp.single j n).prod (fun s n => g s ^ n) = g j ^ n :=
    fun j n => Finsupp.prod_single_index (pow_zero _)
  set ι : ℕ × Fin d → (Fin d →₀ ℕ) := fun kj => Finsupp.single kj.2 (p ^ kj.1) with hι
  have hsupp : Function.support φ ⊆ (((Finset.range M ×ˢ Finset.univ).image ι : Finset _) : Set _) := by
    intro m hm
    rw [Function.mem_support] at hm
    by_contra hnot
    apply hm
    by_cases hex : ∃ j k, m = Finsupp.single j (p ^ k)
    · obtain ⟨j, k, rfl⟩ := hex
      have hk : M ≤ k := by
        by_contra hlt
        apply hnot
        rw [Finset.mem_coe, Finset.mem_image]
        refine ⟨(k, j), ?_, rfl⟩
        simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
        omega
      simp only [φ, hprod, hM j k hk, smul_zero]
    · push Not at hex
      simp only [φ, hF4 m (fun j k => hex j k), zero_smul]
  rw [finsum_eq_sum_of_support_subset φ hsupp,
    Finset.sum_image (fun x _ y _ h => single_pow_injective p h), Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [φ, ι, hF3, hprod, smul_eq_mul]

end LogType

section Vanish

variable {R : Type*} [CommRing R] {τ : Type*}

theorem coeff_pow_eq_zero_of_lt {g : MvPowerSeries τ R} {N : ℕ}
    (hg : ∀ e : τ →₀ ℕ, e.degree < N → coeff e g = 0) {L : ℕ} {e : τ →₀ ℕ}
    (he : e.degree < N * L) : coeff e (g ^ L) = 0 := by
  classical
  induction L generalizing e with
  | zero => simp at he
  | succ L IH =>
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdd : q.1.degree + q.2.degree = e.degree := by rw [← hq, map_add]
    by_cases h1 : q.1.degree < N * L
    · rw [IH h1, zero_mul]
    · have h2 : q.2.degree < N := by
        rw [Nat.mul_succ] at he
        omega
      rw [hg q.2 h2, mul_zero]

theorem coeff_eq_zero_of_degree_lt_one {g : MvPowerSeries τ R} (hg : g.constantCoeff = 0)
    (e : τ →₀ ℕ) (he : e.degree < 1) : coeff e g = 0 := by
  have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
  subst he0
  rw [coeff_zero_eq_constantCoeff_apply, hg]

theorem coeff_expand_eq_zero_of_lt {g : MvPowerSeries τ R} {n : ℕ} (N : ℕ) (hN : N ≠ 0)
    (hg : ∀ e : τ →₀ ℕ, e.degree < n → coeff e g = 0) {e : τ →₀ ℕ}
    (he : e.degree < N * n) : coeff e (expand N hN g) = 0 := by
  classical
  by_cases h : ∀ i, N ∣ e i
  · obtain ⟨m, hm⟩ : ∃ m : τ →₀ ℕ, N • m = e :=
      ⟨e.mapRange (fun a => a / N) (by simp), by ext i; simp [Nat.mul_div_cancel' (h i)]⟩
    rw [← hm, coeff_expand_smul]
    apply hg
    have : (N • m).degree = N * m.degree := by rw [map_nsmul, smul_eq_mul]
    rw [← hm, this] at he
    exact Nat.lt_of_mul_lt_mul_left he
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact coeff_expand_of_not_dvd N hN g hi

end Vanish

section Lift

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] {τ : Type*}

theorem exists_map_eq_of_coeff_mem_range (h : R →+* S) (ψ : MvPowerSeries τ S)
    (hψ : ∀ e, coeff e ψ ∈ Set.range h) : ∃ ψ₀ : MvPowerSeries τ R, map h ψ₀ = ψ := by
  choose c hc using hψ
  refine ⟨fun e => c e, ?_⟩
  ext e
  rw [coeff_map]
  exact hc e

theorem map_injective_of_injective (h : R →+* S) (hh : Function.Injective h) :
    Function.Injective (map (σ := τ) h) := by
  intro x y hxy
  ext e
  apply hh
  rw [← coeff_map, ← coeff_map, hxy]

theorem exists_C_mul_of_dvd_coeff (r : R) (ψ : MvPowerSeries τ R) (hψ : ∀ e, r ∣ coeff e ψ) :
    ∃ w : MvPowerSeries τ R, ψ = C r * w := by
  choose c hc using hψ
  refine ⟨fun e => c e, ?_⟩
  ext e
  rw [coeff_C_mul]
  exact hc e

end Lift

section Descent

variable {g : ℕ} {R : Type*} [CommRing R] {S : Type*} [CommRing S]

theorem exists_mvFormalGroup_map_eq (h : R →+* S) (hh : Function.Injective h)
    (F : MvFormalGroup g S) (hF : ∀ i e, coeff e (F.toPowerSeries i) ∈ Set.range h) :
    ∃ F₀ : MvFormalGroup g R, MvFormalGroup.map h F₀ = F := by
  choose Φ₀ hΦ₀ using fun i => exists_map_eq_of_coeff_mem_range h (F.toPowerSeries i) (hF i)
  have hinj3 := map_injective_of_injective (τ := Fin g ⊕ (Fin g ⊕ Fin g)) h hh
  have hz0 : ∀ i, (Φ₀ i).constantCoeff = 0 := by
    intro i; apply hh; rw [← constantCoeff_map, hΦ₀, F.constantCoeff_eq_zero, map_zero]
  refine ⟨{ toPowerSeries := Φ₀
            constantCoeff_eq_zero := hz0
            coeff_single_inl := ?_
            coeff_single_inr := ?_
            assoc := ?_ }, ?_⟩
  · intro i j; apply hh; rw [← coeff_map, hΦ₀, F.coeff_single_inl]; split <;> simp
  · intro i j; apply hh; rw [← coeff_map, hΦ₀, F.coeff_single_inr]; split <;> simp
  · intro i
    apply hinj3
    have hzB : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    have hzC : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    have hB := hasSubst_of_constantCoeff_zero hzB
    have hC := hasSubst_of_constantCoeff_zero hzC
    have hA : HasSubst (Sum.elim
        (fun j => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (Φ₀ j))
        fun j => X (Sum.inr (Sum.inr j))) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero hB hzB (hz0 j)
      · exact constantCoeff_X _
    have hA' : HasSubst (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (Φ₀ j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_eq_zero hC hzC (hz0 j)
    rw [map_subst hA, map_subst hA', hΦ₀]
    have hBmap : (fun s => MvPowerSeries.map h ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) s))
        = Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
          fun l => X (Sum.inr (Sum.inl l)) := by
      funext s
      rcases s with l | l <;> simp [map_X]
    have hCmap : (fun s => MvPowerSeries.map h ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) s))
        = Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
          fun l => X (Sum.inr (Sum.inr l)) := by
      funext s
      rcases s with l | l <;> simp [map_X]
    have hAmap : (fun s => MvPowerSeries.map h ((Sum.elim
        (fun j => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (Φ₀ j))
        fun j => X (Sum.inr (Sum.inr j))) s))
        = Sum.elim
          (fun j => subst (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
            fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
          fun j => X (Sum.inr (Sum.inr j)) := by
      funext s
      rcases s with j | j
      · show MvPowerSeries.map h (subst (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inl l))) (Φ₀ j))
            = subst (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
              fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j)
        rw [map_subst hB, hBmap, hΦ₀]
      · simp [map_X]
    have hA'map : (fun s => MvPowerSeries.map h ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (Φ₀ j)) s))
        = Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
          fun j => subst (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
            fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j) := by
      funext s
      rcases s with j | j
      · simp [map_X]
      · show MvPowerSeries.map h (subst (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inr l))) (Φ₀ j))
            = subst (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
              fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)
        rw [map_subst hC, hCmap, hΦ₀]
    rw [hAmap, hA'map]
    exact F.assoc i
  · apply MvFormalGroup.ext
    funext i
    exact hΦ₀ i

end Descent

variable (p : ℕ) [hp : Fact p.Prime] (d : ℕ)

def iota : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p) →+* MvPolynomial (ℕ × Fin d × Fin d) (Padic p) :=
  MvPolynomial.map (PadicInt.Coe.ringHom (p := p))

theorem iota_injective : Function.Injective (iota p d) :=
  MvPolynomial.map_injective _ Subtype.coe_injective

def A : Subring (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) := (iota p d).range

def sigK : MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →+* MvPolynomial (ℕ × Fin d × Fin d) (Padic p) :=
  (MvPolynomial.aeval fun v => MvPolynomial.X v ^ p).toRingHom

def sig0 : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p) →+* MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p) :=
  (MvPolynomial.aeval fun v => MvPolynomial.X v ^ p).toRingHom

theorem sigK_comp_iota : (sigK p d).comp (iota p d) = (iota p d).comp (sig0 p d) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [sigK, sig0, iota]
  · intro v
    simp [sigK, sig0, iota]

theorem sigK_mem_A {x : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)} (hx : x ∈ A p d) :
    sigK p d x ∈ A p d := by
  obtain ⟨q, rfl⟩ := hx
  refine ⟨sig0 p d q, ?_⟩
  have := congrArg (fun φ => φ q) (sigK_comp_iota p d)
  exact this.symm

theorem padicInt_exists_pow_eq (a : PadicInt p) : ∃ r : PadicInt p, a = a ^ p + p * r := by
  have h0 : PadicInt.toZMod (a - a ^ p) = 0 := by
    rw [map_sub, map_pow, ZMod.pow_card]
    ring
  have hmem : a - a ^ p ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h0
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  obtain ⟨r, hr⟩ := hmem
  exact ⟨r, by linear_combination hr⟩

theorem sig0_sub_pow_mem (q : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) :
    ∃ r, sig0 p d q = q ^ p + (p : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) * r := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      obtain ⟨r, hr⟩ := padicInt_exists_pow_eq p a
      refine ⟨MvPolynomial.C r, ?_⟩
      have hs : sig0 p d (MvPolynomial.C a) = MvPolynomial.C a := by simp [sig0]
      rw [hs]
      conv_lhs => rw [hr]
      simp only [map_add, map_mul, map_pow, map_natCast]
  | add q₁ q₂ h₁ h₂ =>
      obtain ⟨r₁, hr₁⟩ := h₁
      obtain ⟨r₂, hr₂⟩ := h₂
      obtain ⟨r₃, hr₃⟩ := (Commute.all q₁ q₂).exists_add_pow_prime_eq hp.out
      refine ⟨r₁ + r₂ - q₁ * q₂ * r₃, ?_⟩
      rw [map_add, hr₁, hr₂, hr₃]
      ring
  | mul_X q v h =>
      obtain ⟨r, hr⟩ := h
      refine ⟨r * MvPolynomial.X v ^ p, ?_⟩
      rw [map_mul, hr]
      have : sig0 p d (MvPolynomial.X v) = MvPolynomial.X v ^ p := by simp [sig0]
      rw [this, mul_pow]
      ring

theorem gain {R : Type*} [CommRing R] {x y : R} (h : (p : R) ∣ x - y) (k : ℕ) :
    (p : R) ^ (k + 1) ∣ x ^ p ^ k - y ^ p ^ k :=
  dvd_sub_pow_of_dvd_sub h k

def CongP (s : ℕ) (x y : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) : Prop :=
  ∃ z ∈ A p d, x - y = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ s * z

theorem CongP.refl (s : ℕ) (x : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) : CongP p d s x x :=
  ⟨0, (A p d).zero_mem, by ring⟩

theorem CongP.add {s : ℕ} {x y x' y' : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)}
    (h : CongP p d s x y) (h' : CongP p d s x' y') : CongP p d s (x + x') (y + y') := by
  obtain ⟨z, hz, hxy⟩ := h
  obtain ⟨z', hz', hxy'⟩ := h'
  exact ⟨z + z', (A p d).add_mem hz hz', by rw [add_sub_add_comm, hxy, hxy']; ring⟩

theorem CongP.mul_left {s : ℕ} {c x y : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)}
    (hc : c ∈ A p d) (h : CongP p d s x y) : CongP p d s (c * x) (c * y) := by
  obtain ⟨z, hz, hxy⟩ := h
  exact ⟨c * z, (A p d).mul_mem hc hz, by rw [← mul_sub, hxy]; ring⟩

theorem CongP.pow_pow {x y : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)}
    (hx : x ∈ A p d) (hy : y ∈ A p d) (h : CongP p d 1 x y) (k : ℕ) :
    CongP p d (k + 1) (x ^ p ^ k) (y ^ p ^ k) := by
  obtain ⟨zx, hzx⟩ := hx
  obtain ⟨zy, hzy⟩ := hy
  obtain ⟨z, hz, hxy⟩ := h
  obtain ⟨w, hw⟩ := hz

  have hsub : zx - zy = (p : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) * w := by
    apply iota_injective p d
    rw [map_sub, map_mul, map_natCast, hzx, hzy, hw, hxy, pow_one]
  have hdvd : (p : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) ∣ zx - zy := ⟨w, hsub⟩
  obtain ⟨w', hw'⟩ := dvd_sub_pow_of_dvd_sub hdvd k
  refine ⟨iota p d w', ⟨w', rfl⟩, ?_⟩
  have := congrArg (iota p d) hw'
  rw [map_sub, map_pow, map_pow, map_mul, map_pow, map_natCast, hzx, hzy] at this
  exact this

theorem X_mem_A (v : ℕ × Fin d × Fin d) :
    (MvPolynomial.X v : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ∈ A p d :=
  ⟨MvPolynomial.X v, by simp [iota]⟩

theorem natCast_mem_A (n : ℕ) :
    ((n : MvPolynomial (ℕ × Fin d × Fin d) (Padic p))) ∈ A p d := natCast_mem (A p d) n

theorem sigK_iterate_mem_A {x : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)}
    (hx : x ∈ A p d) (m : ℕ) : (⇑(sigK p d))^[m] x ∈ A p d := by
  induction m with
  | zero => exact hx
  | succ m ih => rw [Function.iterate_succ_apply']; exact sigK_mem_A p d ih

section LogCoeff

variable (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (h1 : a 0 = 1)
variable (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])

include h1 h2 in

theorem pow_mul_logCoeff_mem (k : ℕ) (i j : Fin d) :
    (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * a k i j ∈ A p d := by
  induction k using Nat.strong_induction_on generalizing i j with
  | _ k ih =>
    match k with
    | 0 =>
        rw [pow_zero, one_mul, h1]
        by_cases hij : i = j
        · subst hij; rw [Matrix.one_apply_eq]; exact (A p d).one_mem
        · rw [Matrix.one_apply_ne hij]; exact (A p d).zero_mem
    | (k + 1) =>
        have hcoe : (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
            MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p] MvPolynomial (ℕ × Fin d × Fin d) (Padic p))) = ⇑(sigK p d) := rfl
        have hentry : (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * a (k + 1) i j
            = ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
                MvPolynomial.X (m, i, l) *
                  (⇑(sigK p d))^[m + 1] (a (k - m) l j) := by
          have h := congrArg (fun M => M i j) (h2 k)
          simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
            Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, hcoe] at h
          exact h
        have hpush : ∀ (n : ℕ) (y : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)),
            (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * (⇑(sigK p d))^[n] y = (⇑(sigK p d))^[n] ((p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * y) := by
          intro n y
          rw [← RingHom.coe_pow, map_mul, map_pow, map_natCast]
        have hmain : (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ (k + 1) * a (k + 1) i j
            = ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
                MvPolynomial.X (m, i, l) *
                  (⇑(sigK p d))^[m + 1] ((p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * a (k - m) l j) := by
          have hstep : (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ (k + 1) * a (k + 1) i j
              = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * ((p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * a (k + 1) i j) := by ring
          rw [hstep, hentry, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [mul_left_comm, hpush]
        rw [hmain]
        refine Subring.sum_mem _ fun m hm => Subring.sum_mem _ fun l _ => ?_
        refine (A p d).mul_mem (X_mem_A p d _) ?_
        have hk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have hsplit : (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * a (k - m) l j
            = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ m * ((p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ (k - m) * a (k - m) l j) := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          omega
        rw [hsplit]
        exact sigK_iterate_mem_A p d
          ((A p d).mul_mem ((A p d).pow_mem (natCast_mem_A p d p) m)
            (ih (k - m) (by omega) l j)) (m + 1)

end LogCoeff

abbrev Rint := MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)

abbrev Krat := MvPolynomial (ℕ × Fin d × Fin d) (Padic p)

abbrev Kbar := MvPolynomial (ℕ × Fin d × Fin d) (ZMod p)

def piBar : Rint p d →+* Kbar p d := MvPolynomial.map (PadicInt.toZMod (p := p))

section Frob

theorem piBar_sig0 (x : Rint p d) : piBar p d (sig0 p d x) = (piBar p d x) ^ p := by
  have h : (piBar p d).comp (sig0 p d) = (frobenius (Kbar p d) p).comp (piBar p d) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hs : sig0 p d (MvPolynomial.C a) = MvPolynomial.C a := by simp [sig0]
      rw [RingHom.comp_apply, RingHom.comp_apply, hs, piBar, MvPolynomial.map_C, frobenius_def,
        ← MvPolynomial.C_pow, ZMod.pow_card]
    · intro v
      have hs : sig0 p d (MvPolynomial.X v) = MvPolynomial.X v ^ p := by simp [sig0]
      rw [RingHom.comp_apply, RingHom.comp_apply, hs, map_pow, piBar, MvPolynomial.map_X,
        frobenius_def]
  have := congrArg (fun φ => φ x) h
  simpa [frobenius_def] using this

theorem piBar_sig0_pow (m : ℕ) (x : Rint p d) :
    piBar p d (((sig0 p d) ^ m) x) = (piBar p d x) ^ p ^ m := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [RingHom.coe_pow, Function.iterate_succ_apply', ← RingHom.coe_pow, piBar_sig0, ih,
      ← pow_mul, pow_succ]

theorem piBar_comp_sig0_pow (m : ℕ) :
    (piBar p d).comp ((sig0 p d) ^ m) = (iterateFrobenius (Kbar p d) p m).comp (piBar p d) := by
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply, piBar_sig0_pow, iterateFrobenius_def]

variable {τ : Type*}

theorem map_piBar_expand_map_sig0_pow (m : ℕ) (ψ : MvPowerSeries τ (Rint p d)) :
    map (piBar p d) (expand (p ^ m) (pow_ne_zero m hp.out.ne_zero) (map ((sig0 p d) ^ m) ψ))
      = map (piBar p d) (ψ ^ p ^ m) := by
  rw [map_expand, map_map, piBar_comp_sig0_pow, ← map_map, ← map_expand,
    map_iterateFrobenius_expand p hp.out.ne_zero, map_pow]

theorem exists_expand_map_sig0_pow_eq (m : ℕ) (ψ : MvPowerSeries τ (Rint p d)) :
    ∃ w : MvPowerSeries τ (Rint p d),
      expand (p ^ m) (pow_ne_zero m hp.out.ne_zero) (map ((sig0 p d) ^ m) ψ)
        = ψ ^ p ^ m + (p : MvPowerSeries τ (Rint p d)) * w := by
  set E := expand (p ^ m) (pow_ne_zero m hp.out.ne_zero) (map ((sig0 p d) ^ m) ψ) with hE
  have hker : ∀ e, (p : Rint p d) ∣ coeff e (E - ψ ^ p ^ m) := by
    intro e
    have h0 : piBar p d (coeff e (E - ψ ^ p ^ m)) = 0 := by
      rw [← coeff_map, map_sub, hE, map_piBar_expand_map_sig0_pow, sub_self]
      rfl
    have hmem : coeff e (E - ψ ^ p ^ m) ∈ RingHom.ker (piBar p d) := h0
    rw [piBar, MvPolynomial.ker_map, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, map_natCast] at hmem
    exact hmem
  obtain ⟨w, hw⟩ := exists_C_mul_of_dvd_coeff (p : Rint p d) (E - ψ ^ p ^ m) hker
  refine ⟨w, ?_⟩
  rw [map_natCast] at hw
  linear_combination hw

end Frob

section Push

theorem sigK_pow_comp_iota (m : ℕ) :
    ((sigK p d) ^ m).comp (iota p d) = (iota p d).comp ((sig0 p d) ^ m) := by
  induction m with
  | zero =>
    refine RingHom.ext fun x => ?_
    simp [RingHom.one_def]
  | succ m ih =>
    refine RingHom.ext fun x => ?_
    have h1 := congrArg (fun φ => φ x) ih
    have h2 := congrArg (fun φ => φ (((sig0 p d) ^ m) x)) (sigK_comp_iota p d)
    simp only [RingHom.comp_apply, RingHom.coe_pow, Function.iterate_succ_apply'] at h1 h2 ⊢
    rw [h1]
    exact h2

theorem sigK_pow_iota (m : ℕ) (x : Rint p d) :
    ((sigK p d) ^ m) (iota p d x) = iota p d (((sig0 p d) ^ m) x) := by
  have := congrArg (fun φ => φ x) (sigK_pow_comp_iota p d m)
  simpa using this

theorem sigK_pow_mem_A (m : ℕ) {x : Krat p d} (hx : x ∈ A p d) : ((sigK p d) ^ m) x ∈ A p d := by
  rw [RingHom.coe_pow]
  exact sigK_iterate_mem_A p d hx m

variable {τ : Type*}

theorem map_sigK_pow_map_iota (m : ℕ) (ψ : MvPowerSeries τ (Rint p d)) :
    map ((sigK p d) ^ m) (map (iota p d) ψ) = map (iota p d) (map ((sig0 p d) ^ m) ψ) := by
  rw [map_map, map_map, sigK_pow_comp_iota]

theorem exists_expand_map_sigK_pow_eq (m : ℕ) (ψ₀ : MvPowerSeries τ (Rint p d)) :
    ∃ w : MvPowerSeries τ (Rint p d),
      expand (p ^ m) (pow_ne_zero m hp.out.ne_zero) (map ((sigK p d) ^ m) (map (iota p d) ψ₀))
        = map (iota p d) (ψ₀ ^ p ^ m + (p : MvPowerSeries τ (Rint p d)) * w) := by
  obtain ⟨w, hw⟩ := exists_expand_map_sig0_pow_eq p d m ψ₀
  refine ⟨w, ?_⟩
  rw [map_sigK_pow_map_iota, ← map_expand, hw]

theorem exists_coeff_pow_sub_eq (G₀ Q₀ w : MvPowerSeries τ (Rint p d))
    (hG : G₀ = Q₀ + (p : MvPowerSeries τ (Rint p d)) * w) (k : ℕ) (e : τ →₀ ℕ) :
    ∃ u ∈ A p d, coeff e ((map (iota p d) G₀) ^ p ^ k) - coeff e ((map (iota p d) Q₀) ^ p ^ k)
      = (p : Krat p d) ^ (k + 1) * u := by
  have hdvd : (p : MvPowerSeries τ (Rint p d)) ∣ G₀ - Q₀ := ⟨w, by rw [hG]; ring⟩
  obtain ⟨U, hU⟩ := dvd_sub_pow_of_dvd_sub hdvd k
  refine ⟨iota p d (coeff e U), ⟨coeff e U, rfl⟩, ?_⟩
  have hcoeff : coeff e (G₀ ^ p ^ k) - coeff e (Q₀ ^ p ^ k) = (p : Rint p d) ^ (k + 1) * coeff e U := by
    rw [← map_sub, hU, ← map_natCast (C : Rint p d →+* MvPowerSeries τ (Rint p d)) p, ← map_pow,
      coeff_C_mul]
  rw [← map_pow, ← map_pow, coeff_map, coeff_map, ← map_sub, hcoeff, map_mul, map_pow, map_natCast]

theorem exists_sum_sub_sum_eq {M : ℕ} (b x y : ℕ → Fin d → Krat p d)
    (hb : ∀ k j, (p : Krat p d) ^ k * b k j ∈ A p d)
    (hxy : ∀ k j, ∃ u ∈ A p d, x k j - y k j = (p : Krat p d) ^ (k + 1) * u) :
    ∃ z ∈ A p d, (∑ k ∈ Finset.range M, ∑ j : Fin d, b k j * x k j)
      - (∑ k ∈ Finset.range M, ∑ j : Fin d, b k j * y k j) = (p : Krat p d) * z := by
  choose u hu using hxy
  refine ⟨∑ k ∈ Finset.range M, ∑ j : Fin d, ((p : Krat p d) ^ k * b k j) * u k j, ?_, ?_⟩
  · exact Subring.sum_mem _ fun k _ => Subring.sum_mem _ fun j _ =>
      (A p d).mul_mem (hb k j) (hu k j).1
  · rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_sub, (hu k j).2]
    ring

end Push

section StepD

variable (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])

include h2 in
theorem p_mul_logCoeff_entry (k : ℕ) (i j : Fin d) :
    (p : Krat p d) * a (k + 1) i j
      = ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
          MvPolynomial.X (m, i, l) * ((sigK p d) ^ (m + 1)) (a (k - m) l j) := by
  have hcoe : (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
      MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p] MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
        = ⇑(sigK p d) := rfl
  have h := congrArg (fun M => M i j) (h2 k)
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, hcoe, ← RingHom.coe_pow] at h
  exact h

include h2 in

theorem p_mul_sum_logCoeff_eq (φ : ℕ → Fin d → Krat p d) (i : Fin d) (M : ℕ) :
    (p : Krat p d) * ∑ k ∈ Finset.range M, ∑ j : Fin d, a (k + 1) i j * φ (k + 1) j
      = ∑ m ∈ Finset.range M, ∑ l : Fin d, MvPolynomial.X (m, i, l) *
          ∑ k ∈ Finset.range (M - m), ∑ j : Fin d,
            ((sigK p d) ^ (m + 1)) (a k l j) * φ (k + (m + 1)) j := by

  set f : ℕ → ℕ → Krat p d := fun m k => ∑ l : Fin d, ∑ j : Fin d,
    MvPolynomial.X (m, i, l) * (((sigK p d) ^ (m + 1)) (a k l j) * φ (k + (m + 1)) j) with hf
  have lhs : (p : Krat p d) * ∑ k ∈ Finset.range M, ∑ j : Fin d, a (k + 1) i j * φ (k + 1) j
      = ∑ k ∈ Finset.range M, ∑ m ∈ Finset.range (k + 1), f m (k - m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum]
    have step : ∀ j : Fin d, (p : Krat p d) * (a (k + 1) i j * φ (k + 1) j)
        = ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
            MvPolynomial.X (m, i, l) * (((sigK p d) ^ (m + 1)) (a (k - m) l j) * φ (k - m + (m + 1)) j) := by
      intro j
      rw [← mul_assoc, p_mul_logCoeff_entry p d a h2 k i j, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hkm : k - m + (m + 1) = k + 1 := by
        have := Finset.mem_range.mp hm
        omega
      rw [hkm, mul_assoc]
    rw [Finset.sum_congr rfl fun j _ => step j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
  rw [lhs, Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [hf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]

end StepD

section Crux

variable {τ : Type*}

theorem coeff_pow_pow_eq_zero {g : MvPowerSeries τ (Krat p d)} {N M k : ℕ} {e : τ →₀ ℕ}
    (hg : ∀ e' : τ →₀ ℕ, e'.degree < N → coeff e' g = 0) (he : e.degree < N * p ^ M)
    (hk : M ≤ k) (hp1 : 1 ≤ p) : coeff e (g ^ p ^ k) = 0 := by
  apply coeff_pow_eq_zero_of_lt hg
  calc e.degree < N * p ^ M := he
    _ ≤ N * p ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp1 hk)

variable (Φ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (h5 : ∀ i : Fin d,
      MvPowerSeries.subst Φ.toPowerSeries (f i)
        = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
          + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i))

include h5 in

theorem subst_expand_map_eq (m : ℕ) (l : Fin d) :
    subst (fun j => expand (p ^ m) (pow_ne_zero m hp.out.ne_zero)
        (map ((sigK p d) ^ m) (Φ.toPowerSeries j))) (map ((sigK p d) ^ m) (f l))
      = subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ m)
          (map ((sigK p d) ^ m) (f l))
        + subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ m)
          (map ((sigK p d) ^ m) (f l)) := by
  have hN := pow_ne_zero m hp.out.ne_zero
  have key := congrArg (fun s => expand (p ^ m) hN (map ((sigK p d) ^ m) s)) (h5 l)
  have hΦ : HasSubst Φ.toPowerSeries := Φ.hasSubst_toPowerSeries
  have hΦσ : HasSubst (fun j => map ((sigK p d) ^ m) (Φ.toPowerSeries j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_map, Φ.constantCoeff_eq_zero, map_zero]
  have hL : HasSubst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d))) :=
    hasSubst_of_constantCoeff_zero fun j => constantCoeff_X _
  have hR : HasSubst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d))) :=
    hasSubst_of_constantCoeff_zero fun j => constantCoeff_X _
  simp only [map_add, map_subst hΦ, map_subst hL, map_subst hR, map_X] at key
  rw [expand_subst _ _ hΦσ, expand_subst _ _ hL, expand_subst _ _ hR] at key
  simp only [expand_X] at key
  exact key

end Crux

section Ssum

variable {τ : Type*}

def Ssum (b : ℕ → Fin d → Krat p d) (M : ℕ) (e : τ →₀ ℕ)
    (g : Fin d → MvPowerSeries τ (Krat p d)) : Krat p d :=
  ∑ k ∈ Finset.range M, ∑ j : Fin d, b k j * coeff e (g j ^ p ^ k)

theorem Ssum_congr {b : ℕ → Fin d → Krat p d} {M : ℕ} {e : τ →₀ ℕ}
    {g g' : Fin d → MvPowerSeries τ (Krat p d)}
    (h : ∀ j k, coeff e (g j ^ p ^ k) = coeff e (g' j ^ p ^ k)) :
    Ssum p d b M e g = Ssum p d b M e g' := by
  unfold Ssum
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [h j k]

theorem Ssum_eq_coeff_subst {b : ℕ → Fin d → Krat p d} {M : ℕ} {e : τ →₀ ℕ}
    (F : MvPowerSeries (Fin d) (Krat p d))
    (hF3 : ∀ j k, coeff (Finsupp.single j (p ^ k)) F = b k j)
    (hF4 : ∀ e', (∀ j k, e' ≠ Finsupp.single j (p ^ k)) → coeff e' F = 0)
    {N : ℕ} (hN : N ≠ 0) (g : Fin d → MvPowerSeries τ (Krat p d))
    (hg : ∀ j (e' : τ →₀ ℕ), e'.degree < N → coeff e' (g j) = 0)
    (he : e.degree < N * p ^ M) :
    Ssum p d b M e g = coeff e (subst g F) := by
  have hg0 : ∀ j, (g j).constantCoeff = 0 := fun j => by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hg j 0 (by rw [map_zero]; omega)
  unfold Ssum
  rw [coeff_subst_logType p F b hF3 hF4 g hg0 e M]
  intro j k hk
  exact coeff_pow_pow_eq_zero p d (hg j) he hk hp.out.one_lt.le

theorem coeff_pow_eq_zero_of_constantCoeff {u : MvPowerSeries τ (Krat p d)} (hu : u.constantCoeff = 0)
    {N : ℕ} (e' : τ →₀ ℕ) (he' : e'.degree < N) : coeff e' (u ^ N) = 0 :=
  coeff_pow_eq_zero_of_lt (N := 1) (coeff_eq_zero_of_degree_lt_one hu) (by omega)

theorem coeff_expand_eq_zero_of_constantCoeff {u : MvPowerSeries τ (Krat p d)}
    (hu : u.constantCoeff = 0) {N : ℕ} (hN : N ≠ 0) (e' : τ →₀ ℕ) (he' : e'.degree < N) :
    coeff e' (expand N hN u) = 0 :=
  coeff_expand_eq_zero_of_lt (n := 1) N hN (coeff_eq_zero_of_degree_lt_one hu) (by omega)

end Ssum

section CruxMain

variable (Φ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (h1 : a 0 = 1)
variable (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
variable (h3 : ∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j)
variable (h4 : ∀ (i : Fin d) (e : Fin d →₀ ℕ),
      (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0)
variable (h5 : ∀ i : Fin d,
      MvPowerSeries.subst Φ.toPowerSeries (f i)
        = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
          + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i))

include h1 h2 h3 h4 h5 in

theorem crux (n : ℕ) (hn : 1 ≤ n)
    (Ψ₀ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (Rint p d))
    (hΨ0 : ∀ j, (Ψ₀ j).constantCoeff = 0)
    (hΨΦ : ∀ j (e' : Fin d ⊕ Fin d →₀ ℕ), e'.degree < n →
      coeff e' (map (iota p d) (Ψ₀ j)) = coeff e' (Φ.toPowerSeries j))
    (m : ℕ) (hm : 1 ≤ m) (l : Fin d) (e : Fin d ⊕ Fin d →₀ ℕ) (he : e.degree = n)
    (M : ℕ) (hM : n < p ^ (m + M)) :
    ∃ z ∈ A p d,
      ∑ k ∈ Finset.range M, ∑ j : Fin d, ((sigK p d) ^ m) (a k l j) *
        (coeff e ((X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + m))
          + coeff e ((X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + m))
          - coeff e ((map (iota p d) (Ψ₀ j)) ^ p ^ (k + m)))
      = (p : Krat p d) * z := by
  classical
  have hN : p ^ m ≠ 0 := pow_ne_zero m hp.out.ne_zero
  have hN2 : 2 ≤ p ^ m := le_trans hp.out.two_le (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right hp.out.one_lt.le hm)
  have heM : e.degree < p ^ m * p ^ M := by rw [← pow_add, he]; exact hM

  have hF3 : ∀ j k, coeff (Finsupp.single j (p ^ k)) (map ((sigK p d) ^ m) (f l))
      = ((sigK p d) ^ m) (a k l j) := by
    intro j k
    rw [coeff_map]
    exact congrArg _ (h3 l j k)
  have hF4 : ∀ e', (∀ j k, e' ≠ Finsupp.single j (p ^ k)) →
      coeff e' (map ((sigK p d) ^ m) (f l)) = 0 := by
    intro e' he'
    rw [coeff_map]
    have h := h4 l e' he'
    change ((sigK p d) ^ m) ((f l).coeff e') = 0
    rw [h, map_zero]

  have hb : ∀ k j, (p : Krat p d) ^ k * ((sigK p d) ^ m) (a k l j) ∈ A p d := by
    intro k j
    have : (p : Krat p d) ^ k * ((sigK p d) ^ m) (a k l j)
        = ((sigK p d) ^ m) ((p : Krat p d) ^ k * a k l j) := by
      rw [map_mul, map_pow, map_natCast]
    rw [this]
    exact sigK_pow_mem_A p d m (pow_mul_logCoeff_mem p d a h1 h2 k l j)

  choose w hw using fun j => exists_expand_map_sigK_pow_eq p d (τ := Fin d ⊕ Fin d) m (Ψ₀ j)

  have vXL : ∀ j (e' : Fin d ⊕ Fin d →₀ ℕ), e'.degree < p ^ m →
      coeff e' ((fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ m) j) = 0 :=
    fun j e' he' => coeff_pow_eq_zero_of_constantCoeff p d (constantCoeff_X _) e' he'
  have vXR : ∀ j (e' : Fin d ⊕ Fin d →₀ ℕ), e'.degree < p ^ m →
      coeff e' ((fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ m) j) = 0 :=
    fun j e' he' => coeff_pow_eq_zero_of_constantCoeff p d (constantCoeff_X _) e' he'
  have hΨc : ∀ j, (map (iota p d) (Ψ₀ j)).constantCoeff = 0 := fun j => by
    rw [constantCoeff_map, hΨ0, map_zero]
  have vQ : ∀ j (e' : Fin d ⊕ Fin d →₀ ℕ), e'.degree < p ^ m →
      coeff e' ((fun j => (map (iota p d) (Ψ₀ j)) ^ p ^ m) j) = 0 :=
    fun j e' he' => coeff_pow_eq_zero_of_constantCoeff p d (hΨc j) e' he'
  have vG : ∀ j (e' : Fin d ⊕ Fin d →₀ ℕ), e'.degree < p ^ m →
      coeff e' ((fun j => expand (p ^ m) hN (map ((sigK p d) ^ m) (map (iota p d) (Ψ₀ j)))) j) = 0 :=
    fun j e' he' => coeff_expand_eq_zero_of_constantCoeff p d
      (by rw [constantCoeff_map, hΨc, map_zero]) hN e' he'
  have vG' : ∀ j (e' : Fin d ⊕ Fin d →₀ ℕ), e'.degree < p ^ m →
      coeff e' ((fun j => expand (p ^ m) hN (map ((sigK p d) ^ m) (Φ.toPowerSeries j))) j) = 0 :=
    fun j e' he' => coeff_expand_eq_zero_of_constantCoeff p d
      (by rw [constantCoeff_map, Φ.constantCoeff_eq_zero, map_zero]) hN e' he'

  have step1 : Ssum p d (fun k j => ((sigK p d) ^ m) (a k l j)) M e
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ m)
      + Ssum p d (fun k j => ((sigK p d) ^ m) (a k l j)) M e
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ m)
      = Ssum p d (fun k j => ((sigK p d) ^ m) (a k l j)) M e
        (fun j => expand (p ^ m) hN (map ((sigK p d) ^ m) (Φ.toPowerSeries j))) := by
    rw [Ssum_eq_coeff_subst p d _ hF3 hF4 hN _ vXL heM, Ssum_eq_coeff_subst p d _ hF3 hF4 hN _ vXR heM,
      Ssum_eq_coeff_subst p d _ hF3 hF4 hN _ vG' heM]
    have key := congrArg (coeff e) (subst_expand_map_eq p d Φ f h5 m l)
    rw [map_add] at key
    exact key.symm

  have step2 : Ssum p d (fun k j => ((sigK p d) ^ m) (a k l j)) M e
        (fun j => expand (p ^ m) hN (map ((sigK p d) ^ m) (Φ.toPowerSeries j)))
      = Ssum p d (fun k j => ((sigK p d) ^ m) (a k l j)) M e
        (fun j => expand (p ^ m) hN (map ((sigK p d) ^ m) (map (iota p d) (Ψ₀ j)))) := by
    apply Ssum_congr
    intro j k
    apply MvFormalGroup.coeff_pow_congr (n := n) _ (le_of_eq he)
    intro e' he'
    rw [← sub_eq_zero, ← map_sub, ← map_sub, ← map_sub]
    apply coeff_expand_eq_zero_of_lt (n := n) (p ^ m) hN
    · intro e'' he''
      rw [coeff_map, map_sub, ← hΨΦ j e'' he'', sub_self, map_zero]
    · calc e'.degree ≤ n := he'
        _ < 2 * n := by omega
        _ ≤ p ^ m * n := Nat.mul_le_mul_right _ hN2

  obtain ⟨z, hz, step3⟩ := exists_sum_sub_sum_eq p d (M := M) (fun k j => ((sigK p d) ^ m) (a k l j))
    (fun k j => coeff e ((fun j => expand (p ^ m) hN (map ((sigK p d) ^ m) (map (iota p d) (Ψ₀ j)))) j ^ p ^ k))
    (fun k j => coeff e ((fun j => (map (iota p d) (Ψ₀ j)) ^ p ^ m) j ^ p ^ k)) hb (by
      intro k j
      have h := exists_coeff_pow_sub_eq p d
        (Ψ₀ j ^ p ^ m + (p : MvPowerSeries (Fin d ⊕ Fin d) (Rint p d)) * w j) (Ψ₀ j ^ p ^ m) (w j) rfl k e
      rw [map_pow (map (iota p d)) (Ψ₀ j) (p ^ m)] at h
      beta_reduce
      rw [hw j]
      exact h)
  refine ⟨z, hz, ?_⟩

  have hT : ∑ k ∈ Finset.range M, ∑ j : Fin d, ((sigK p d) ^ m) (a k l j) *
        (coeff e ((X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + m))
          + coeff e ((X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + m))
          - coeff e ((map (iota p d) (Ψ₀ j)) ^ p ^ (k + m)))
      = Ssum p d (fun k j => ((sigK p d) ^ m) (a k l j)) M e
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ m)
        + Ssum p d (fun k j => ((sigK p d) ^ m) (a k l j)) M e
          (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ m)
        - Ssum p d (fun k j => ((sigK p d) ^ m) (a k l j)) M e
          (fun j => (map (iota p d) (Ψ₀ j)) ^ p ^ m) := by
    unfold Ssum
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpk : p ^ (k + m) = p ^ m * p ^ k := by rw [add_comm, pow_add]
    rw [hpk, pow_mul, pow_mul, pow_mul]
    ring
  rw [hT, step1, step2]
  unfold Ssum
  beta_reduce at step3
  exact step3

end CruxMain

section Main

variable (Φ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (h1 : a 0 = 1)
variable (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
variable (h3 : ∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j)
variable (h4 : ∀ (i : Fin d) (e : Fin d →₀ ℕ),
      (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0)
variable (h5 : ∀ i : Fin d,
      MvPowerSeries.subst Φ.toPowerSeries (f i)
        = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
          + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i))

include h1 h3 h4 h5 in

theorem coeff_toPowerSeries_eq (i : Fin d) (e : Fin d ⊕ Fin d →₀ ℕ) (M₁ : ℕ)
    (hM : e.degree < p ^ (M₁ + 1)) :
    coeff e (Φ.toPowerSeries i)
      = (∑ j : Fin d, a 0 i j *
          (coeff e ((X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ 0)
            + coeff e ((X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ 0)))
        + ∑ k ∈ Finset.range M₁, ∑ j : Fin d, a (k + 1) i j *
            (coeff e ((X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + 1))
              + coeff e ((X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + 1))
              - coeff e ((Φ.toPowerSeries j) ^ p ^ (k + 1))) := by
  classical
  have hf3 : ∀ j k, coeff (Finsupp.single j (p ^ k)) (f i) = a k i j := fun j k => h3 i j k
  have hf4 : ∀ e', (∀ j k, e' ≠ Finsupp.single j (p ^ k)) → coeff e' (f i) = 0 :=
    fun e' h => h4 i e' h
  have vanM : ∀ (g : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)),
      (∀ j, (g j).constantCoeff = 0) → ∀ j k, M₁ + 1 ≤ k → coeff e (g j ^ p ^ k) = 0 :=
    fun g hg j k hk => coeff_pow_pow_eq_zero p d (N := 1) (M := M₁ + 1)
      (coeff_eq_zero_of_degree_lt_one (hg j)) (by simpa using hM) hk hp.out.one_lt.le
  have hL0 : ∀ j, ((X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d))).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hR0 : ∀ j, ((X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d))).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have EΦ := coeff_subst_logType p (f i) (fun k j => a k i j) hf3 hf4 Φ.toPowerSeries
    Φ.constantCoeff_eq_zero e (M₁ + 1) (vanM _ Φ.constantCoeff_eq_zero)
  have EL := coeff_subst_logType p (f i) (fun k j => a k i j) hf3 hf4
    (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d))) hL0 e (M₁ + 1) (vanM _ hL0)
  have ER := coeff_subst_logType p (f i) (fun k j => a k i j) hf3 hf4
    (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d))) hR0 e (M₁ + 1) (vanM _ hR0)
  have key := congrArg (coeff e) (h5 i)
  rw [map_add, EΦ, EL, ER, Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_range_succ'] at key
  have h0 : ∑ j : Fin d, a 0 i j * coeff e (Φ.toPowerSeries j ^ p ^ 0)
      = coeff e (Φ.toPowerSeries i) := by
    rw [h1]
    simp [Matrix.one_apply]
  rw [h0] at key
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination key

include h1 h2 h3 h4 h5 in

theorem coeff_toPowerSeries_mem_A_of_lt (n : ℕ) :
    ∀ (i : Fin d) (e : Fin d ⊕ Fin d →₀ ℕ), e.degree < n → coeff e (Φ.toPowerSeries i) ∈ A p d := by
  classical
  induction n with
  | zero => intro i e he; omega
  | succ n IH =>
    intro i e he
    by_cases hlt : e.degree < n
    · exact IH i e hlt
    have hen : e.degree = n := by omega
    by_cases hn0 : n = 0
    · subst hn0
      have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp hen
      subst he0
      rw [coeff_zero_eq_constantCoeff_apply, Φ.constantCoeff_eq_zero]
      exact (A p d).zero_mem
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0

    let Ψ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (Krat p d) :=
      fun j e' => if e'.degree < n then coeff e' (Φ.toPowerSeries j) else 0
    have hΨcoeff : ∀ j e', coeff e' (Ψ j) = if e'.degree < n then coeff e' (Φ.toPowerSeries j) else 0 :=
      fun j e' => rfl
    have hΨA : ∀ j e', coeff e' (Ψ j) ∈ Set.range (iota p d) := by
      intro j e'
      rw [hΨcoeff]
      split_ifs with h
      · exact IH j e' h
      · exact ⟨0, map_zero _⟩
    choose Ψ₀ hΨ₀ using fun j => exists_map_eq_of_coeff_mem_range (iota p d) (Ψ j) (hΨA j)
    have hΨΦ : ∀ j (e' : Fin d ⊕ Fin d →₀ ℕ), e'.degree < n →
        coeff e' (map (iota p d) (Ψ₀ j)) = coeff e' (Φ.toPowerSeries j) := by
      intro j e' he'
      rw [hΨ₀, hΨcoeff, if_pos he']
    have hΨ0 : ∀ j, (Ψ₀ j).constantCoeff = 0 := by
      intro j
      apply iota_injective p d
      rw [← constantCoeff_map, ← coeff_zero_eq_constantCoeff_apply, hΨΦ j 0 (by rw [map_zero]; omega),
        coeff_zero_eq_constantCoeff_apply, Φ.constantCoeff_eq_zero, map_zero]
    have hΨc : ∀ j, (map (iota p d) (Ψ₀ j)).constantCoeff = 0 := fun j => by
      rw [constantCoeff_map, hΨ0, map_zero]

    have hnp : n < p ^ (n + 1) :=
      calc n < p ^ n := Nat.lt_pow_self hp.out.one_lt
        _ ≤ p ^ (n + 1) := Nat.pow_le_pow_right hp.out.one_lt.le (Nat.le_succ n)
    have hM : e.degree < p ^ (n + 1) := by rw [hen]; exact hnp
    rw [coeff_toPowerSeries_eq p d Φ a f h1 h3 h4 h5 i e n hM]

    have htail : ∀ j k, coeff e ((Φ.toPowerSeries j) ^ p ^ (k + 1))
        = coeff e ((map (iota p d) (Ψ₀ j)) ^ p ^ (k + 1)) := by
      intro j k
      have h2le : 2 ≤ p ^ (k + 1) := le_trans hp.out.two_le (Nat.le_self_pow (Nat.succ_ne_zero k) p)
      exact MvFormalGroup.coeff_pow_sub_congr hn (Φ.constantCoeff_eq_zero j) (hΨc j)
        (fun e' he' => (hΨΦ j e' he').symm) (by rw [hen]; omega)
    simp only [htail]

    set D := ∑ k ∈ Finset.range n, ∑ j : Fin d, a (k + 1) i j *
        (coeff e ((X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + 1))
          + coeff e ((X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + 1))
          - coeff e ((map (iota p d) (Ψ₀ j)) ^ p ^ (k + 1))) with hD
    have hcrux : ∀ (m : ℕ) (l : Fin d), ∃ z ∈ A p d, m < n →
        ∑ k ∈ Finset.range (n - m), ∑ j : Fin d, ((sigK p d) ^ (m + 1)) (a k l j) *
          (coeff e ((X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + (m + 1)))
            + coeff e ((X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ (k + (m + 1)))
            - coeff e ((map (iota p d) (Ψ₀ j)) ^ p ^ (k + (m + 1))))
        = (p : Krat p d) * z := by
      intro m l
      by_cases hmn : m < n
      · obtain ⟨z, hz, h⟩ := crux p d Φ a f h1 h2 h3 h4 h5 n hn Ψ₀ hΨ0 hΨΦ (m + 1)
          (Nat.succ_pos m) l e hen (n - m) (by
            have : m + 1 + (n - m) = n + 1 := by omega
            rw [this]; exact hnp)
        exact ⟨z, hz, fun _ => h⟩
      · exact ⟨0, (A p d).zero_mem, fun h => absurd h hmn⟩
    choose z hzA hz using hcrux
    have hpD : (p : Krat p d) * D
        = (p : Krat p d) * ∑ m ∈ Finset.range n, ∑ l : Fin d, MvPolynomial.X (m, i, l) * z m l := by
      have hSD := p_mul_sum_logCoeff_eq p d a h2
        (fun k j => coeff e ((X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ k)
          + coeff e ((X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (Krat p d)) ^ p ^ k)
          - coeff e ((map (iota p d) (Ψ₀ j)) ^ p ^ k)) i n
      beta_reduce at hSD
      rw [hD, hSD, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hz m l (Finset.mem_range.mp hm)]
      ring
    have hp0 : (p : Krat p d) ≠ 0 := by
      rw [← map_natCast (MvPolynomial.C : Padic p →+* Krat p d), Ne, MvPolynomial.C_eq_zero]
      exact_mod_cast hp.out.ne_zero
    have hDeq : D = ∑ m ∈ Finset.range n, ∑ l : Fin d, MvPolynomial.X (m, i, l) * z m l :=
      mul_left_cancel₀ hp0 hpD
    rw [hDeq]
    refine (A p d).add_mem ?_ ?_
    · refine Subring.sum_mem _ fun j _ => (A p d).mul_mem ?_ ((A p d).add_mem ?_ ?_)
      · have := pow_mul_logCoeff_mem p d a h1 h2 0 i j
        rwa [pow_zero, one_mul] at this
      · rw [coeff_X_pow]
        split_ifs
        · exact (A p d).one_mem
        · exact (A p d).zero_mem
      · rw [coeff_X_pow]
        split_ifs
        · exact (A p d).one_mem
        · exact (A p d).zero_mem
    · exact Subring.sum_mem _ fun m _ => Subring.sum_mem _ fun l _ =>
        (A p d).mul_mem (X_mem_A p d _) (hzA m l)

include h1 h2 h3 h4 h5 in
theorem coeff_toPowerSeries_mem_A (i : Fin d) (e : Fin d ⊕ Fin d →₀ ℕ) :
    coeff e (Φ.toPowerSeries i) ∈ A p d :=
  coeff_toPowerSeries_mem_A_of_lt p d Φ a f h1 h2 h3 h4 h5 (e.degree + 1) i e (Nat.lt_succ_self _)

end Main

end MvFormalGroupU2

end

theorem solution
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (Φ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (h3 : ∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j)
    (h4 : ∀ (i : Fin d) (e : Fin d →₀ ℕ),
      (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0)
    (h5 : ∀ i : Fin d,
      MvPowerSeries.subst Φ.toPowerSeries (f i)
        = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
          + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i)) :
    ∃ Φ₀ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)),
      MvFormalGroup.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀ = Φ := by
  obtain ⟨Φ₀, hΦ₀⟩ := MvFormalGroupU2.exists_mvFormalGroup_map_eq (MvFormalGroupU2.iota p d)
    (MvFormalGroupU2.iota_injective p d) Φ (fun i e =>
      RingHom.mem_range.mp (MvFormalGroupU2.coeff_toPowerSeries_mem_A p d Φ a f h1 h2 h3 h4 h5 i e))
  exact ⟨Φ₀, hΦ₀⟩

end S_MvFormalGroup_exists_map_padicInt_eq_of_log
end P2MW
export P2MW.S_MvFormalGroup_exists_map_padicInt_eq_of_log (solution)
