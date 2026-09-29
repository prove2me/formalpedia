-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/07042c73-05e5-5277-9f8d-9a6d3c2fe9b7

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Theorems.Thm_MvPowerSeries_exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation

set_option autoImplicit false

universe u

noncomputable section

open MvPowerSeries

namespace MvFormalGroupINT

variable (p : ℕ) [hp : Fact p.Prime] (d : ℕ)

abbrev Krat := MvPolynomial (ℕ × Fin d × Fin d) (Padic p)

abbrev Rint := MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)

def iota : Rint p d →+* Krat p d := MvPolynomial.map (PadicInt.Coe.ringHom (p := p))

theorem iota_injective : Function.Injective (iota p d) :=
  MvPolynomial.map_injective _ Subtype.coe_injective

def sigK : Krat p d →+* Krat p d := (MvPolynomial.aeval fun v => MvPolynomial.X v ^ p).toRingHom
def sig0 : Rint p d →+* Rint p d := (MvPolynomial.aeval fun v => MvPolynomial.X v ^ p).toRingHom

theorem sigK_comp_iota : (sigK p d).comp (iota p d) = (iota p d).comp (sig0 p d) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [sigK, sig0, iota]
  · intro v; simp [sigK, sig0, iota]

theorem sigK_pow_iota (m : ℕ) (x : Rint p d) :
    ((sigK p d) ^ m) (iota p d x) = iota p d (((sig0 p d) ^ m) x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [RingHom.coe_pow, RingHom.coe_pow, Function.iterate_succ_apply', Function.iterate_succ_apply',
      ← RingHom.coe_pow, ← RingHom.coe_pow, ih]
    have := congrArg (fun φ => φ (((sig0 p d) ^ m) x)) (sigK_comp_iota p d)
    simpa only [RingHom.comp_apply] using this

theorem map_injective_iota {τ : Type*} : Function.Injective (map (σ := τ) (iota p d)) := by
  intro x y hxy
  refine MvPowerSeries.ext fun e => ?_
  apply iota_injective p d
  rw [← coeff_map, ← coeff_map, hxy]

section GhostFE

variable (c : ℕ → Fin d → MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
variable (g : Fin d → MvPowerSeries ℕ (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (hm : ∀ (j : Fin d) (k n : ℕ),
      coeff (Finsupp.single k (p ^ n)) (g j) = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * c (k + n) j)
variable (hm' : ∀ (j : Fin d) (e : ℕ →₀ ℕ), (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → coeff e (g j) = 0)

include hm in

theorem coeff_single_expand_map (M k n : ℕ) (l : Fin d) (hN : p ^ (M + 1) ≠ 0) :
    coeff (Finsupp.single k (p ^ n)) (expand (p ^ (M + 1)) hN (map ((sigK p d) ^ (M + 1)) (g l)))
      = if M + 1 ≤ n then (p : Krat p d) ^ k * ((sigK p d) ^ (M + 1)) (c (k + (n - (M + 1))) l) else 0 := by
  classical
  split_ifs with h
  · have he : Finsupp.single k (p ^ n) = p ^ (M + 1) • Finsupp.single k (p ^ (n - (M + 1))) := by
      rw [Finsupp.smul_single, smul_eq_mul, ← pow_add]
      congr 2
      omega
    rw [he, coeff_expand_smul, coeff_map, hm, map_mul, map_pow, map_natCast]
  · apply coeff_expand_of_not_dvd (i := k)
    rw [Finsupp.single_eq_same, Nat.pow_dvd_pow_iff_le_right hp.out.one_lt]
    omega

include hm' in

theorem coeff_expand_map_eq_zero (M : ℕ) (l : Fin d) (hN : p ^ (M + 1) ≠ 0) (e : ℕ →₀ ℕ)
    (he : ∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) :
    coeff e (expand (p ^ (M + 1)) hN (map ((sigK p d) ^ (M + 1)) (g l))) = 0 := by
  classical
  by_cases hdiv : ∀ i, p ^ (M + 1) ∣ e i
  · obtain ⟨e', he'⟩ : ∃ e' : ℕ →₀ ℕ, p ^ (M + 1) • e' = e :=
      ⟨e.mapRange (fun a => a / p ^ (M + 1)) (by simp), by
        ext i; simp [Nat.mul_div_cancel' (hdiv i)]⟩
    rw [← he', coeff_expand_smul, coeff_map, hm' l e', map_zero]
    intro k n hk
    apply he k (n + (M + 1))
    rw [← he', hk, Finsupp.smul_single, smul_eq_mul, ← pow_add, add_comm]
  · push Not at hdiv
    obtain ⟨i, hi⟩ := hdiv
    exact coeff_expand_of_not_dvd _ hN _ hi

end GhostFE

section GhostFE2

variable (c : ℕ → Fin d → MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
variable (g : Fin d → MvPowerSeries ℕ (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (hm : ∀ (j : Fin d) (k n : ℕ),
      coeff (Finsupp.single k (p ^ n)) (g j) = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * c (k + n) j)
variable (hm' : ∀ (j : Fin d) (e : ℕ →₀ ℕ), (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → coeff e (g j) = 0)
variable (hcA : ∀ (N : ℕ) (j : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ N * c N j = MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r)
variable (hcFE : ∀ (k : ℕ) (j : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * c (k + 1) j
        - ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
            MvPolynomial.X (m, j, l) *
              ((⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
                  MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p] MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))^[m + 1]) (c (k - m) l)
        = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r)

include hcA in

theorem exists_tail_term (M k idx : ℕ) (hidx : idx < k) (i l : Fin d) :
    ∃ s : Rint p d, (p : Krat p d) ^ k * (MvPolynomial.X (M, i, l) * ((sigK p d) ^ (M + 1)) (c idx l))
      = (p : Krat p d) * iota p d s := by
  obtain ⟨r, hr⟩ := hcA idx l
  have hr' : (p : Krat p d) ^ idx * c idx l = iota p d r := hr
  refine ⟨MvPolynomial.X (M, i, l) * ((sig0 p d) ^ (M + 1)) ((p : Rint p d) ^ (k - idx - 1) * r), ?_⟩
  have hX : iota p d (MvPolynomial.X (M, i, l)) = MvPolynomial.X (M, i, l) := by simp [iota]
  rw [map_mul, ← sigK_pow_iota, map_mul, map_pow, map_natCast, hX, ← hr', map_mul, map_mul, map_pow,
    map_pow]
  simp only [map_natCast]
  have hpk : (p : Krat p d) ^ k = (p : Krat p d) ^ (k - idx - 1) * p * (p : Krat p d) ^ idx := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  rw [hpk]
  ring

include hm hm' hcA hcFE in

theorem hFE_ghost (i : Fin d) (e : ℕ →₀ ℕ) :
    ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * (g i).coeff e
        - ∑ m ∈ Finset.range (Finsupp.degree e), ∑ l : Fin d,
            MvPolynomial.X (m, i, l) *
              (MvPowerSeries.expand (p ^ (m + 1)) (pow_ne_zero (m + 1) (Fact.out : p.Prime).ne_zero)
                (MvPowerSeries.map
                  ((MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
                      MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p]
                        MvPolynomial (ℕ × Fin d × Fin d) (Padic p)).toRingHom ^ (m + 1)) (g l))).coeff e
        = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
            * MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r := by
  classical

  change ∃ r : Rint p d, (p : Krat p d) * coeff e (g i)
      - ∑ M ∈ Finset.range (Finsupp.degree e), ∑ l : Fin d, MvPolynomial.X (M, i, l) *
          coeff e (expand (p ^ (M + 1)) (pow_ne_zero (M + 1) hp.out.ne_zero) (map ((sigK p d) ^ (M + 1)) (g l)))
      = (p : Krat p d) * iota p d r
  by_cases hex : ∃ k n, e = Finsupp.single k (p ^ n)
  · obtain ⟨k, n, rfl⟩ := hex
    rw [Finsupp.degree_single, hm]
    have hnle : n ≤ p ^ n := (Nat.lt_pow_self hp.out.one_lt).le
    rw [← Finset.sum_range_add_sum_Ico _ hnle]
    have hIco : ∑ M ∈ Finset.Ico n (p ^ n), ∑ l : Fin d, MvPolynomial.X (M, i, l) *
        coeff (Finsupp.single k (p ^ n)) (expand (p ^ (M + 1)) (pow_ne_zero (M + 1) hp.out.ne_zero)
          (map ((sigK p d) ^ (M + 1)) (g l))) = 0 := by
      refine Finset.sum_eq_zero fun M hM => Finset.sum_eq_zero fun l _ => ?_
      have hM1 : n ≤ M := (Finset.mem_Ico.mp hM).1
      rw [coeff_single_expand_map p d c g hm, if_neg (by omega), mul_zero]
    rw [hIco, add_zero]
    have hlow : ∑ M ∈ Finset.range n, ∑ l : Fin d, MvPolynomial.X (M, i, l) *
        coeff (Finsupp.single k (p ^ n)) (expand (p ^ (M + 1)) (pow_ne_zero (M + 1) hp.out.ne_zero)
          (map ((sigK p d) ^ (M + 1)) (g l)))
        = ∑ M ∈ Finset.range n, ∑ l : Fin d, (p : Krat p d) ^ k * (MvPolynomial.X (M, i, l) *
            ((sigK p d) ^ (M + 1)) (c (k + n - 1 - M) l)) := by
      refine Finset.sum_congr rfl fun M hM => Finset.sum_congr rfl fun l _ => ?_
      have hM' := Finset.mem_range.mp hM
      rw [coeff_single_expand_map p d c g hm, if_pos (by omega)]
      have hidx0 : k + (n - (M + 1)) = k + n - 1 - M := by omega
      rw [hidx0]
      ring
    rw [hlow]
    cases n with
    | zero =>
      obtain ⟨r, hr⟩ := hcA k i
      refine ⟨r, ?_⟩
      rw [Finset.range_zero, Finset.sum_empty, sub_zero, add_zero, hr]
      rfl
    | succ n' =>
      obtain ⟨r₀, hr₀⟩ := hcFE (k + n') i
      have hcoe : (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
          MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p] MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
            = ⇑(sigK p d) := rfl
      simp only [hcoe, ← RingHom.coe_pow] at hr₀

      rw [← Finset.sum_range_add_sum_Ico _ (show n' + 1 ≤ k + n' + 1 by omega)] at hr₀
      have hr₀' : (p : Krat p d) * c (k + n' + 1) i
          - (∑ M ∈ Finset.range (n' + 1), ∑ l : Fin d, MvPolynomial.X (M, i, l) * ((sigK p d) ^ (M + 1)) (c (k + n' - M) l)
            + ∑ M ∈ Finset.Ico (n' + 1) (k + n' + 1), ∑ l : Fin d,
                MvPolynomial.X (M, i, l) * ((sigK p d) ^ (M + 1)) (c (k + n' - M) l))
          = (p : Krat p d) * iota p d r₀ := hr₀

      have htail : ∀ (M : ℕ) (l : Fin d), ∃ s : Rint p d, M ∈ Finset.Ico (n' + 1) (k + n' + 1) →
          (p : Krat p d) ^ k * (MvPolynomial.X (M, i, l) * ((sigK p d) ^ (M + 1)) (c (k + n' - M) l))
            = (p : Krat p d) * iota p d s := by
        intro M l
        by_cases hM : M ∈ Finset.Ico (n' + 1) (k + n' + 1)
        · have hM' := Finset.mem_Ico.mp hM
          obtain ⟨s, hs⟩ := exists_tail_term p d c hcA M k (k + n' - M) (by omega) i l
          exact ⟨s, fun _ => hs⟩
        · exact ⟨0, fun h => absurd h hM⟩
      choose s hs using htail
      refine ⟨(p : Rint p d) ^ k * r₀ + ∑ M ∈ Finset.Ico (n' + 1) (k + n' + 1), ∑ l : Fin d, s M l, ?_⟩
      have hsumtail : (p : Krat p d) ^ k * ∑ M ∈ Finset.Ico (n' + 1) (k + n' + 1), ∑ l : Fin d,
          (MvPolynomial.X (M, i, l) * ((sigK p d) ^ (M + 1)) (c (k + n' - M) l))
          = (p : Krat p d) * iota p d (∑ M ∈ Finset.Ico (n' + 1) (k + n' + 1), ∑ l : Fin d, s M l) := by
        rw [map_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun M hM => ?_
        rw [map_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => hs M l hM
      have hidx : ∀ M ∈ Finset.range (n' + 1), k + (n' + 1) - 1 - M = k + n' - M := fun M _ => by omega
      rw [Finset.sum_congr rfl fun M hM => Finset.sum_congr rfl fun l _ => by rw [hidx M hM]]
      simp_rw [← Finset.mul_sum]

      rw [map_add, map_mul, map_pow, map_natCast, mul_add, ← hsumtail]
      have : k + (n' + 1) = k + n' + 1 := by omega
      rw [this]
      linear_combination (p : Krat p d) ^ k * hr₀'
  · push Not at hex
    refine ⟨0, ?_⟩
    rw [hm' i e (fun k n => hex k n), mul_zero, map_zero, mul_zero, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun M _ => Finset.sum_eq_zero fun l _ => ?_
    rw [coeff_expand_map_eq_zero p d g hm' M l _ e (fun k n => hex k n), mul_zero]

end GhostFE2

end MvFormalGroupINT

end

open MvPowerSeries in

theorem solution
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (Φ₀ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p))) [Φ₀.IsComm]
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
    (c : ℕ → Fin d → MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
    (hcA : ∀ (N : ℕ) (j : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ N * c N j = MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r)
    (hcFE : ∀ (k : ℕ) (j : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * c (k + 1) j
        - ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
            MvPolynomial.X (m, j, l) *
              ((⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
                  MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p] MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))^[m + 1]) (c (k - m) l)
        = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r)
    (m : MvFormalGroup.CartierModule p
      (MvFormalGroup.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀))
    (hm : ∀ (j : Fin d) (k n : ℕ),
      (coeff (Finsupp.single k (p ^ n)) (subst m.toPowerSeries (f j)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * c (k + n) j)
    (hm' : ∀ (j : Fin d) (e : ℕ →₀ ℕ), (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
      (coeff e (subst m.toPowerSeries (f j)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0) :
    ∃ m₀ : MvFormalGroup.CartierModule p Φ₀,
      MvFormalGroup.CartierModule.baseChange (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) m₀ = m := by
  classical

  have hΘ : ∀ i, (m.toPowerSeries i).constantCoeff = 0 := m.constantCoeff_eq_zero
  obtain ⟨Θ₀, hΘ₀⟩ := MvPowerSeries.exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation p d
    a f h1 h2 h3 h4 m.toPowerSeries hΘ (fun j => subst m.toPowerSeries (f j)) (fun j => rfl)
    (fun i e => MvFormalGroupINT.hFE_ghost p d c (fun j => subst m.toPowerSeries (f j)) hm hm' hcA hcFE i e)

  have hι := MvFormalGroupINT.map_injective_iota p d (τ := Fin 2 × ℕ)
  have hz0 : ∀ j, (Θ₀ j).constantCoeff = 0 := by
    intro j
    apply MvFormalGroupINT.iota_injective p d
    change (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) ((Θ₀ j).constantCoeff) = _
    rw [← constantCoeff_map, hΘ₀, m.constantCoeff_eq_zero, map_zero]
  let m₀ : MvFormalGroup.CartierModule p Φ₀ :=
    { toPowerSeries := Θ₀
      constantCoeff_eq_zero := hz0
      subst_eq := by
        intro j
        apply hι
        change MvPowerSeries.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) _
          = MvPowerSeries.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) _
        have hL : HasSubst (fun n : ℕ => (X (0, n) : MvPowerSeries (Fin 2 × ℕ) (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)))) :=
          MvPowerSeries.HasSubst.X_comp (Prod.mk (0 : Fin 2))
        have hR : HasSubst (fun n : ℕ => (X (1, n) : MvPowerSeries (Fin 2 × ℕ) (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)))) :=
          MvPowerSeries.HasSubst.X_comp (Prod.mk (1 : Fin 2))
        have hE : HasSubst (Sum.elim
            (fun l => subst (fun n : ℕ => (X (0, n) : MvPowerSeries (Fin 2 × ℕ) (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)))) (Θ₀ l))
            fun l => subst (fun n : ℕ => (X (1, n) : MvPowerSeries (Fin 2 × ℕ) (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)))) (Θ₀ l)) := by
          apply hasSubst_of_constantCoeff_zero
          rintro (l | l)
          · exact constantCoeff_subst_eq_zero hL (fun n => constantCoeff_X _) (hz0 l)
          · exact constantCoeff_subst_eq_zero hR (fun n => constantCoeff_X _) (hz0 l)
        rw [map_subst (MvFormalGroup.WittLaw.hasSubst_addFam p _), map_subst hE, hΘ₀]
        have hA : (fun n => MvPowerSeries.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p)))
            (MvFormalGroup.WittLaw.addFam p (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) n))
            = MvFormalGroup.WittLaw.addFam p (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) :=
          funext (MvFormalGroup.WittLaw.map_addFam _)
        have hfam : (fun s => MvPowerSeries.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) (Sum.elim
            (fun l => subst (fun n : ℕ => (X (0, n) : MvPowerSeries (Fin 2 × ℕ) (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)))) (Θ₀ l))
            (fun l => subst (fun n : ℕ => (X (1, n) : MvPowerSeries (Fin 2 × ℕ) (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)))) (Θ₀ l)) s))
            = Sum.elim
              (fun l => subst (fun n : ℕ => (X (0, n) : MvPowerSeries (Fin 2 × ℕ) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (m.toPowerSeries l))
              fun l => subst (fun n : ℕ => (X (1, n) : MvPowerSeries (Fin 2 × ℕ) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (m.toPowerSeries l) := by
          funext s
          rcases s with l | l
          · show MvPowerSeries.map _ (subst _ (Θ₀ l)) = _
            rw [map_subst hL, hΘ₀]
            congr 1
            funext n
            exact map_X _ (0, n)
          · show MvPowerSeries.map _ (subst _ (Θ₀ l)) = _
            rw [map_subst hR, hΘ₀]
            congr 1
            funext n
            exact map_X _ (1, n)
        rw [hA, hfam]
        exact m.subst_eq j }
  refine ⟨m₀, ?_⟩
  apply MvFormalGroup.CartierModule.ext
  funext j
  exact hΘ₀ j

end S_MvFormalGroup_CartierModule_exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation (solution)
