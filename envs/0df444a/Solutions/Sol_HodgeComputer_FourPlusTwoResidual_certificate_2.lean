-- Prove2me | solution 2 for HodgeComputer.FourPlusTwoResidual.certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-10T05:26:13.912+00:00
-- url     : https://prove2.me/submissions/a963c410-7abf-4947-a8a6-6f0243b839cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Definitions.Def_HodgeComputerFourPlusTwoResidual
import Definitions.Def_HodgeComputerFourPlusTwoCore
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate

/-! Reduction of the four-plus-two-residual certificate to a strict four-variable equation.
The lemmas `relPrime_of_specialization`, `relPrime_of_retract` and `hom_of_isHomogeneous` are taken from
github.com/hodge-computer/sextics (formal/lean/HodgeComputer/Verify.lean, Apache 2.0). -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MvPolynomial
open scoped BigOperators

namespace FP2
open HodgeComputer HodgeComputer.FourPlusTwoResidual

theorem pderiv_rename_inj {σ τ : Type*} [DecidableEq σ] [DecidableEq τ] {f : σ → τ}
    (hf : Function.Injective f) (i : σ) (p : MvPolynomial σ ℂ) :
    pderiv (f i) (rename f p) = rename f (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, rename_X, Derivation.leibniz, hp, pderiv_X, smul_eq_mul, Pi.single_apply,
      hf.eq_iff]
    split_ifs <;> simp

theorem pderiv_rename_notin {σ τ : Type*} [DecidableEq τ] {f : σ → τ} {j : τ}
    (hj : ∀ i, f i ≠ j) (p : MvPolynomial σ ℂ) :
    pderiv j (rename f p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, rename_X, Derivation.leibniz, hp, pderiv_X, smul_eq_mul, Pi.single_apply,
      hj i]
    simp

abbrev P6 := MvPolynomial (Fin 6) ℂ

def ι : Fin 4 → Fin 6 := ![0, 1, 3, 4]

theorem ι_inj : Function.Injective ι := by decide

def Bp : P6 :=
  X 2 ^ 6 + C (15 / 7 : ℂ) * X 2 ^ 4 * X 5 ^ 2 + C (10 / 7 : ℂ) * X 2 ^ 2 * X 5 ^ 4 + X 5 ^ 6

theorem F_eq : (F : P6) = rename ι core + Bp := by
  have h : ∀ x : Fin 6 → ℂ, eval x (F : P6) = eval x (rename ι core + Bp) := by
    intro x
    simp [F, core, Bp, ι, eval_rename]
    ring
  exact MvPolynomial.funext h

theorem A_eq : (A : P6) = rename ι coreSource := by
  have h : ∀ x : Fin 6 → ℂ, eval x (A : P6) = eval x (rename ι coreSource) := by
    intro x
    simp [A, coreSource, ι, eval_rename]
  exact MvPolynomial.funext h

theorem defect_zero (d a H' M : P6) (n h dd dn : Fin 4 → P6)
    (hd : ∀ i, pderiv (ι i) d = dd i) (hd2 : pderiv 2 d = 0) (hd5 : pderiv 5 d = 0)
    (hn : ∀ i, pderiv (ι i) (n i) = dn i)
    (hH : ∀ i, pderiv (ι i) H' = h i) (hH2 : pderiv 2 H' = 0) (hH5 : pderiv 5 H' = 0)
    (hn2 : ∀ i, pderiv 2 (n i) = 0) (hn5 : ∀ i, pderiv 5 (n i) = 0)
    (hM2 : pderiv 2 M = 0) (hM5 : pderiv 5 M = 0)
    (hM : M = d * (∑ i, dn i) - ∑ i, dd i * n i)
    (hc : 2 * a * d ^ 2 - 2 * d * (∑ i, h i * n i) + 3 * H' * M = 0) :
    defect (H' + Bp) a (C 4 * d ^ 2) 1
      ![C 4 * d * n 0, C 4 * d * n 1, X 2 * M, C 4 * d * n 2, C 4 * d * n 3, X 5 * M] = 0 := by
  have hd0 : pderiv 0 d = dd 0 := hd 0
  have hd1 : pderiv 1 d = dd 1 := hd 1
  have hd3 : pderiv 3 d = dd 2 := hd 2
  have hd4 : pderiv 4 d = dd 3 := hd 3
  have hn0 : pderiv 0 (n 0) = dn 0 := hn 0
  have hn1 : pderiv 1 (n 1) = dn 1 := hn 1
  have hn3 : pderiv 3 (n 2) = dn 2 := hn 2
  have hn4 : pderiv 4 (n 3) = dn 3 := hn 3
  have hH0 : pderiv 0 H' = h 0 := hH 0
  have hH1 : pderiv 1 H' = h 1 := hH 1
  have hH3 : pderiv 3 H' = h 2 := hH 2
  have hH4 : pderiv 4 H' = h 3 := hH 3
  simp only [Fin.sum_univ_four] at hM hc
  have e4 : (C (4:ℂ) : P6) = 4 := map_ofNat C 4
  have hp4 : ∀ i : Fin 6, pderiv i (4 : P6) = 0 := fun i => by rw [← e4]; exact pderiv_C
  unfold defect divergenceNumerator divergence directional
  have key : ∀ (g : Fin (5 + 1) → P6), (∑ i : Fin (5 + 1), g i) = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 :=
    fun g => Fin.sum_univ_six g
  simp only [key]
  simp only [Bp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul,
    Derivation.leibniz, Derivation.leibniz_pow, pderiv_C, pderiv_X, smul_eq_mul,
    hd0, hd1, hd3, hd4, hd2, hd5, hn0, hn1, hn3, hn4, hH0, hH1, hH3, hH4, hH2, hH5, hM2, hM5, hn2, hn5, hp4,
    Pi.single_apply, smul_zero, mul_zero, zero_mul, add_zero, zero_add, Nat.cast_one,
    nsmul_eq_mul, Nat.cast_ofNat, e4]
  simp
  subst hM
  linear_combination (8 * d ^ 2) * hc

theorem hom_of_isHomogeneous {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℕ}
    (h : P.IsHomogeneous k) : Homogeneous P (k : ℤ) := by
  intro m hm
  exact_mod_cast (show m.degree = k by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h hm)

theorem relPrime_of_specialization {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (φ : R →+* S) (f g : Polynomial R)
    (hf : IsUnit f.leadingCoeff) (h : IsRelPrime (f.map φ) (g.map φ)) : IsRelPrime f g := by
  intro a ha hb
  have hu : IsUnit a.leadingCoeff := by
    obtain ⟨b, rfl⟩ := ha
    rw [Polynomial.leadingCoeff_mul] at hf
    exact isUnit_of_mul_isUnit_left hf
  exact Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map φ hu
    (h (map_dvd (Polynomial.mapRingHom φ) ha) (map_dvd (Polynomial.mapRingHom φ) hb))

theorem relPrime_of_retract {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : S →+* R) (hg : g.comp f = RingHom.id R) {a b : R}
    (h : IsRelPrime (f a) (f b)) : IsRelPrime a b := by
  intro p hp hq
  have hu := (h (map_dvd f hp) (map_dvd f hq)).map g
  simpa only [← RingHom.comp_apply, hg, RingHom.id_apply] using hu

/-- The chart making `X 2` the polynomial variable. -/
def chart : P6 →+* Polynomial P6 :=
  eval₂Hom (Polynomial.C.comp C) (fun j : Fin 6 => if j = 2 then Polynomial.X else Polynomial.C (X j))

def unchart : Polynomial P6 →+* P6 := Polynomial.eval₂RingHom (RingHom.id P6) (X 2)

theorem unchart_chart : unchart.comp chart = RingHom.id P6 := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [chart, unchart]
  · intro j
    by_cases hj : j = 2
    · subst hj; simp [chart, unchart]
    · simp [chart, unchart, hj]

theorem chart_rename (p : MvPolynomial (Fin 4) ℂ) : chart (rename ι p) = Polynomial.C (rename ι p) := by
  have : chart.comp (rename ι : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] P6).toRingHom
      = Polynomial.C.comp (rename ι : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] P6).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [chart]
    · intro i
      have : ι i ≠ 2 := by revert i; decide
      simp [chart, this]
  exact congrArg (fun f => f p) this

theorem chart_Bp : chart Bp = Polynomial.X ^ 6 + Polynomial.C (C (15/7) * X 5 ^ 2) * Polynomial.X ^ 4
    + Polynomial.C (C (10/7) * X 5 ^ 4) * Polynomial.X ^ 2 + Polynomial.C (X 5 ^ 6) := by
  have h5 : (5 : Fin 6) ≠ 2 := by decide
  simp [chart, Bp, h5]
  ring

theorem relPrime_F (e : MvPolynomial (Fin 4) ℂ) (he : e ≠ 0) : IsRelPrime (F : P6) (rename ι e) := by
  have hne : rename ι e ≠ (0 : P6) := by
    intro h; exact he (rename_injective ι ι_inj (by simpa using h))
  obtain ⟨x, hx⟩ : ∃ x : Fin 6 → ℂ, eval x (rename ι e) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hne (MvPolynomial.funext (fun x => by simpa using hcon x))
  apply relPrime_of_retract chart unchart unchart_chart
  rw [F_eq, map_add, chart_rename, chart_rename, chart_Bp]
  apply relPrime_of_specialization (eval x)
  · have hm : (Polynomial.C (rename ι core) + (Polynomial.X ^ 6 + Polynomial.C (C (15/7) * X 5 ^ 2) * Polynomial.X ^ 4
        + Polynomial.C (C (10/7) * X 5 ^ 4) * Polynomial.X ^ 2 + Polynomial.C (X 5 ^ 6)) : Polynomial P6).Monic := by
      monicity!
    rw [hm.leadingCoeff]; exact isUnit_one
  · rw [Polynomial.map_C]
    exact (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hx)).isRelPrime_right

theorem core_hom : core.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 4) ℂ
  have hC := isHomogeneous_C (Fin 4) (R := ℂ)
  have t1 : (X 0 ^ 6 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 := (hX 0).pow 6
  have t2 : (C (5 / 7 : ℂ) * X 0 ^ 5 * X 1 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((hC _).mul ((hX 0).pow 5)).mul (hX 1)
  have t3 : (C (5 / 7 : ℂ) * X 0 ^ 3 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((((hC _).mul ((hX 0).pow 3)).mul (hX 1)).mul (hX 2)).mul (hX 3)
  have t4 : (C (10 / 7 : ℂ) * X 0 * X 1 ^ 5 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((hC _).mul (hX 0)).mul ((hX 1).pow 5)
  have t5 : (C (10 / 7 : ℂ) * X 0 * X 1 * X 2 ^ 3 * X 3 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((((hC _).mul (hX 0)).mul (hX 1)).mul ((hX 2).pow 3)).mul (hX 3)
  have t6 : (X 1 ^ 6 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 := (hX 1).pow 6
  have t7 : (X 2 ^ 6 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 := (hX 2).pow 6
  have t8 : (C (5 / 7 : ℂ) * X 2 ^ 5 * X 3 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((hC _).mul ((hX 2).pow 5)).mul (hX 3)
  have t9 : (C (15 / 7 : ℂ) * X 2 * X 3 ^ 5 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((hC _).mul (hX 2)).mul ((hX 3).pow 5)
  have t10 : (X 3 ^ 6 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 := (hX 3).pow 6
  unfold core
  exact ((((((((t1.add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add t10

theorem Bp_hom : Bp.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 6) ℂ
  have hC := isHomogeneous_C (Fin 6) (R := ℂ)
  have t1 : (X 2 ^ 6 : P6).IsHomogeneous 6 := (hX 2).pow 6
  have t2 : (C (15 / 7 : ℂ) * X 2 ^ 4 * X 5 ^ 2 : P6).IsHomogeneous 6 :=
    ((hC _).mul ((hX 2).pow 4)).mul ((hX 5).pow 2)
  have t3 : (C (10 / 7 : ℂ) * X 2 ^ 2 * X 5 ^ 4 : P6).IsHomogeneous 6 :=
    ((hC _).mul ((hX 2).pow 2)).mul ((hX 5).pow 4)
  have t4 : (X 5 ^ 6 : P6).IsHomogeneous 6 := (hX 5).pow 6
  unfold Bp
  exact ((t1.add t2).add t3).add t4

theorem coreSource_hom : coreSource.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 4) ℂ
  unfold coreSource
  exact ((hX 0).pow 3).mul ((hX 2).pow 3)

theorem F_hom : (F : P6).IsHomogeneous 6 := by
  rw [F_eq]; exact core_hom.rename_isHomogeneous.add Bp_hom

theorem F_ne : (F : P6) ≠ 0 := by
  intro h
  have h' : (rename ι core + Bp : P6) = (0 : P6) := F_eq ▸ h
  have := congrArg (eval (fun j : Fin 6 => if j = 2 then (1:ℂ) else 0)) h'
  simp [core, Bp, ι, eval_rename] at this

theorem cert_of_core (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ)
    (hcore : CoreCertificate D N) : HasCertificate (n := 5) (F : P6) A 6 1 := by
  obtain ⟨hD0, ⟨k, hDh, hNh⟩, hc⟩ := hcore
  let M4 : MvPolynomial (Fin 4) ℂ := D * (∑ i, pderiv i (N i)) - ∑ i, pderiv i D * N i
  have hM4 : M4.IsHomogeneous (2 * k + 2) := by
    have h1 : (D * (∑ i, pderiv i (N i))).IsHomogeneous (2 * k + 2) := by
      have := hDh.mul (IsHomogeneous.sum Finset.univ (fun i => pderiv i (N i)) (k + 2 - 1)
        (fun i _ => (hNh i).pderiv))
      convert this using 1; omega
    have h2 : (∑ i, pderiv i D * N i).IsHomogeneous (2 * k + 2) := by
      apply IsHomogeneous.sum
      intro i _
      have := (hDh.pderiv (i := i)).mul (hNh i)
      convert this using 1; omega
    exact h1.sub h2
  set d : P6 := rename ι D with hd
  set M : P6 := rename ι M4 with hM
  have hd0 : d ≠ 0 := by
    intro h; exact hD0 (rename_injective ι ι_inj (by simpa [hd] using h))
  have hdh : d.IsHomogeneous (k + 1) := hDh.rename_isHomogeneous
  have hMh : M.IsHomogeneous (2 * k + 2) := hM4.rename_isHomogeneous
  have hnh : ∀ i, (rename ι (N i) : P6).IsHomogeneous (k + 2) := fun i => (hNh i).rename_isHomogeneous
  have hC4 : (C (4:ℂ) : P6) ≠ 0 := by
    rw [Ne, C_eq_zero]; norm_num
  have hD6 : (C 4 * d ^ 2 : P6) ≠ 0 := mul_ne_zero hC4 (pow_ne_zero 2 hd0)
  have hD6h : (C 4 * d ^ 2 : P6).IsHomogeneous (2 * k + 2) := by
    have := (isHomogeneous_C (Fin 6) (4:ℂ)).mul (hdh.pow 2)
    convert this using 1; omega
  have htd : (C 4 * d ^ 2 : P6).totalDegree = 2 * k + 2 := hD6h.totalDegree hD6
  have hX := isHomogeneous_X (σ := Fin 6) ℂ
  refine ⟨C 4 * d ^ 2, ![C 4 * d * rename ι (N 0), C 4 * d * rename ι (N 1), X 2 * M,
    C 4 * d * rename ι (N 2), C 4 * d * rename ι (N 3), X 5 * M], 0, ?_⟩
  refine ⟨F_ne, F_hom, ?_, hD6, by rw [htd]; exact hD6h, ?_, ?_, ?_⟩
  · have := hom_of_isHomogeneous (A_eq ▸ coreSource_hom.rename_isHomogeneous : (A : P6).IsHomogeneous 6)
    intro m hm
    exact (this hm).trans (by norm_num)
  · have e : ((C 4 * d ^ 2 : P6).totalDegree : ℤ) + ((6:ℕ):ℤ) * ((1:ℕ):ℤ) - ((5:ℕ):ℤ) = ((2 * k + 3 : ℕ) : ℤ) := by
      rw [htd]; push_cast; ring
    rw [e]
    have hn4 : ∀ i, (C 4 * d * rename ι (N i) : P6).IsHomogeneous (2 * k + 3) := by
      intro i
      have := ((isHomogeneous_C (Fin 6) (4:ℂ)).mul hdh).mul (hnh i)
      convert this using 1; omega
    have hxm : ∀ j, (X j * M : P6).IsHomogeneous (2 * k + 3) := by
      intro j
      have := (hX j).mul hMh
      convert this using 1; omega
    intro i
    fin_cases i
    · exact hom_of_isHomogeneous (hn4 0)
    · exact hom_of_isHomogeneous (hn4 1)
    · exact hom_of_isHomogeneous (hxm 2)
    · exact hom_of_isHomogeneous (hn4 2)
    · exact hom_of_isHomogeneous (hn4 3)
    · exact hom_of_isHomogeneous (hxm 5)
  · have := relPrime_F (C 4 * D ^ 2) (mul_ne_zero (by rw [Ne, C_eq_zero]; norm_num) (pow_ne_zero 2 hD0))
    have e : rename ι (C 4 * D ^ 2) = (C 4 * d ^ 2 : P6) := by rw [map_mul, map_pow, rename_C]
    rw [← e]; exact this
  · have h2 : ∀ i, ι i ≠ 2 := by decide
    have h5 : ∀ i, ι i ≠ 5 := by decide
    have key := defect_zero d (rename ι coreSource) (rename ι core) M (fun i => rename ι (N i))
      (fun i => rename ι (pderiv i core)) (fun i => rename ι (pderiv i D))
      (fun i => rename ι (pderiv i (N i)))
      (fun i => pderiv_rename_inj ι_inj i D) (pderiv_rename_notin h2 D) (pderiv_rename_notin h5 D)
      (fun i => pderiv_rename_inj ι_inj i (N i))
      (fun i => pderiv_rename_inj ι_inj i core) (pderiv_rename_notin h2 core) (pderiv_rename_notin h5 core)
      (fun i => pderiv_rename_notin h2 (N i)) (fun i => pderiv_rename_notin h5 (N i))
      (pderiv_rename_notin h2 M4) (pderiv_rename_notin h5 M4)
      (by simp [hM, hd, M4, map_sub, map_mul, map_sum])
      (by
        have hc' : 2 * coreSource * D ^ 2 - 2 * D * (∑ i, pderiv i core * N i) + 3 * core * M4 = 0 := hc
        have := congrArg (rename ι) hc'
        simp only [map_add, map_sub, map_mul, map_sum, map_pow, map_zero, map_ofNat] at this
        exact this)
    rw [F_eq, A_eq, mul_zero]
    exact key

end FP2

theorem solution : HodgeComputer.HasCertificate (n := HodgeComputer.FourPlusTwoResidual.n)
    HodgeComputer.FourPlusTwoResidual.F HodgeComputer.FourPlusTwoResidual.A
    HodgeComputer.FourPlusTwoResidual.d HodgeComputer.FourPlusTwoResidual.q := by
  obtain ⟨D, N, h⟩ := HodgeComputer.FourPlusTwoResidual.coreCertificate
  exact FP2.cert_of_core D N h
