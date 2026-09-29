-- Prove2me | solution 1 for MvFormalGroup.coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/27de9a6a-f85f-5c45-be73-f47ea43b81bf

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Theorems.Thm_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
import Theorems.Thm_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem
import Theorems.Thm_MvPowerSeries_le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq
import Theorems.Thm_MvFormalGroup_lt_degree_and_natCast_mul_coeff_subst_sub_sub_mem_of_scaledLogTrunc
import Theorems.Thm_WittVector_coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector
p2m_attr_erase "instance" "MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid"
p2m_attr_erase "simp" "MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast"

set_option autoImplicit false
open MvPowerSeries

universe u v

namespace S17C2

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]

section PS
variable {σ : Type v}

theorem mem_span_C_iff (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (f : MvPowerSeries σ 𝓞) :
    f ∈ Ideal.span {(p : MvPowerSeries σ 𝓞)} ↔ ∀ μ, coeff μ f ∈ Ideal.span {(p : 𝓞)} := by
  constructor
  · intro hf μ
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hf
    rw [show (p : MvPowerSeries σ 𝓞) = C (p : 𝓞) from (map_natCast (C (σ := σ) (R := 𝓞)) p).symm,
      coeff_mul_C]
    exact Ideal.mem_span_singleton'.2 ⟨coeff μ g, rfl⟩
  · intro hf
    choose g hg using fun μ => Ideal.mem_span_singleton'.1 (hf μ)
    refine Ideal.mem_span_singleton'.2 ⟨(fun μ => g μ : MvPowerSeries σ 𝓞), ?_⟩
    ext μ
    rw [show (p : MvPowerSeries σ 𝓞) = C (p : 𝓞) from (map_natCast (C (σ := σ) (R := 𝓞)) p).symm,
      coeff_mul_C]
    exact hg μ

theorem natCast_mem_nonZeroDivisors (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) :
    (p : MvPowerSeries σ 𝓞) ∈ nonZeroDivisors (MvPowerSeries σ 𝓞) := by
  rw [show (p : MvPowerSeries σ 𝓞) = C (p : 𝓞) from (map_natCast (C (σ := σ) (R := 𝓞)) p).symm]
  refine mem_nonZeroDivisors_iff_right.2 fun f hf => ?_
  ext μ
  have := congrArg (coeff μ) hf
  rw [coeff_mul_C, coeff_zero] at this
  simpa using (mem_nonZeroDivisors_iff_right.1 hp) _ this

theorem isReduced_quotient (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) :
    IsReduced (MvPowerSeries σ 𝓞 ⧸ Ideal.span {(p : MvPowerSeries σ 𝓞)}) := by
  refine ⟨fun x ⟨k, hk⟩ => ?_⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_C_iff p hp]
  intro μ

  have hmap : MvPowerSeries.map (algebraMap 𝓞 (ZMod p)) (f ^ k) = 0 := by
    ext ν
    rw [coeff_map, coeff_zero]
    have := (mem_span_C_iff p hp _).1 hk ν
    rw [← hker] at this
    exact this
  rw [map_pow] at hmap
  have h0 : MvPowerSeries.map (algebraMap 𝓞 (ZMod p)) f = 0 := IsReduced.eq_zero _ ⟨k, hmap⟩
  have := congrArg (coeff μ) h0
  rw [coeff_map, coeff_zero] at this
  rw [← hker]
  exact this

theorem exists_le_degree_eq [DecidableEq σ] : ∀ (E : ℕ) (μ : σ →₀ ℕ), E ≤ μ.degree → ∃ ν : σ →₀ ℕ, ν ≤ μ ∧ ν.degree = E
  | 0, μ, _ => ⟨0, by simp, by simp⟩
  | E + 1, μ, h => by
    obtain ⟨ν, hν, hνE⟩ := exists_le_degree_eq E μ (Nat.le_of_succ_le h)

    have hne : μ - ν ≠ 0 := by
      intro h0
      have : μ = ν := le_antisymm (tsub_eq_zero_iff_le.1 h0) hν
      rw [this, hνE] at h
      omega
    obtain ⟨t, ht⟩ : ∃ t, (μ - ν) t ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (Finsupp.ext hall)
    refine ⟨ν + Finsupp.single t 1, ?_, ?_⟩
    · intro s
      simp only [Finsupp.coe_add, Pi.add_apply]
      have h1 := hν s
      have h2 : (μ - ν) t = μ t - ν t := Finsupp.tsub_apply _ _ _
      by_cases hst : t = s
      · subst hst
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_apply, if_neg hst, add_zero]
        exact h1
    · rw [map_add, hνE, Finsupp.degree_single]

theorem monomial_mem_pow (ν : σ →₀ ℕ) :
    (monomial ν (1 : 𝓞) : MvPowerSeries σ 𝓞) ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ ν.degree := by
  classical
  induction ν using Finsupp.induction with
  | zero => simp
  | single_add t n ν ht hn ih =>
    rw [show (monomial (Finsupp.single t n + ν) (1 : 𝓞) : MvPowerSeries σ 𝓞) =
        monomial (Finsupp.single t n) 1 * monomial ν 1 by rw [monomial_mul_monomial, one_mul],
      map_add, Finsupp.degree_single, pow_add]
    refine Ideal.mul_mem_mul ?_ ih
    rw [show (monomial (Finsupp.single t n) (1 : 𝓞) : MvPowerSeries σ 𝓞) = X t ^ n by
      rw [X_pow_eq]]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self t)) n

theorem mem_pow_of_forall_le_degree [Fintype σ] [DecidableEq σ] (E : ℕ) (f : MvPowerSeries σ 𝓞)
    (hf : ∀ μ : σ →₀ ℕ, coeff μ f ≠ 0 → E ≤ μ.degree) :
    f ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ E := by
  classical

  let fl : (σ →₀ ℕ) → (σ →₀ ℕ) := fun μ =>
    if h : E ≤ μ.degree then Classical.choose (exists_le_degree_eq (σ := σ) E μ h) else 0
  have hfl : ∀ μ, E ≤ μ.degree → fl μ ≤ μ ∧ (fl μ).degree = E := fun μ h => by
    simp only [fl, dif_pos h]; exact Classical.choose_spec (exists_le_degree_eq (σ := σ) E μ h)

  let g : (σ →₀ ℕ) → MvPowerSeries σ 𝓞 := fun ν κ => if fl (κ + ν) = ν then coeff (κ + ν) f else 0
  let S : Finset (σ →₀ ℕ) := (Finset.univ : Finset σ).finsuppAntidiag E
  have hS : ∀ ν : σ →₀ ℕ, ν ∈ S ↔ ν.degree = E := fun ν => by
    show ν ∈ (Finset.univ : Finset σ).finsuppAntidiag E ↔ _
    have hsum : ∑ i ∈ ν.support, ν i = ∑ i, ν i :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
    rw [Finset.mem_finsuppAntidiag, Finsupp.degree_apply, hsum]
    simp
  have hdec : f = ∑ ν ∈ S, monomial ν (1 : 𝓞) * g ν := by
    ext κ
    rw [map_sum]
    simp only [coeff_monomial_mul, one_mul]
    by_cases hκ : E ≤ κ.degree
    · obtain ⟨hle, hdeg⟩ := hfl κ hκ
      rw [Finset.sum_eq_single (fl κ)]
      · rw [if_pos hle]
        show coeff κ f = (if fl (κ - fl κ + fl κ) = fl κ then coeff (κ - fl κ + fl κ) f else 0)
        rw [tsub_add_cancel_of_le hle, if_pos rfl]
      · intro ν hν hne
        split_ifs with hνκ
        · show (if fl (κ - ν + ν) = ν then coeff (κ - ν + ν) f else 0) = 0
          rw [tsub_add_cancel_of_le hνκ, if_neg (Ne.symm hne)]
        · rfl
      · intro hnot
        exact absurd ((hS _).2 hdeg) hnot
    · have h0 : coeff κ f = 0 := by
        by_contra hne; exact hκ (hf κ hne)
      rw [h0, eq_comm]
      refine Finset.sum_eq_zero fun ν hν => ?_
      split_ifs with hνκ
      · show (if fl (κ - ν + ν) = ν then coeff (κ - ν + ν) f else 0) = 0
        rw [tsub_add_cancel_of_le hνκ]
        split_ifs
        · exact h0
        · rfl
      · rfl
  rw [hdec]
  refine Ideal.sum_mem _ fun ν hν => ?_
  have := monomial_mem_pow (𝓞 := 𝓞) ν
  rw [(hS ν).1 hν] at this
  exact Ideal.mul_mem_right _ _ this

end PS

theorem pow_sub_self_mem [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (c : 𝓞) :
    c ^ p - c ∈ Ideal.span {(p : 𝓞)} := by
  rw [← hker, RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card, sub_self]

theorem ghostComponent_map {R : Type v} {S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (x : WittVector p R) (n : ℕ) :
    WittVector.ghostComponent n (WittVector.map f x) = f (WittVector.ghostComponent n x) := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, MvPolynomial.aeval_def,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

end S17C2

namespace S17C2

theorem main
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i : Fin d) (N E : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (c : (Fin d →₀ ℕ) → 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ M → c m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
        (M < m.degree → c m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
          (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) →
      ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (M - 1 - n) • m')) →
        ∀ j : ℕ, M - N ≤ j → j < M →
          (WittVector.map (MvPowerSeries.substAlgHom
                (MvPowerSeries.hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero)).toRingHom ℓ -
            WittVector.map (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
                (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inl j) (R := 𝓞)))).toRingHom ℓ -
            WittVector.map (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
                (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inr j) (R := 𝓞)))).toRingHom ℓ).coeff j ∈
            Ideal.span {(p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)} ⊔
              (Ideal.span (Set.range (X : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) ^ E := by
  classical

  have hφint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree} :=
    fun i j m => MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
      p hp F Fp hFp hFp0 φ hφ0 hφ1 hφF i j m
  have hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)} := pow_sub_self_mem p hker
  refine ⟨N + E + 1, fun M hM c hc ℓ hℓ j hjlo hjhi => ?_⟩
  have hM1 : 1 ≤ M := by omega

  set sF : MvPowerSeries (Fin d) 𝓞 →+* MvPowerSeries (Fin d ⊕ Fin d) 𝓞 := (MvPowerSeries.substAlgHom (R := 𝓞)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero)).toRingHom with hsF
  set s1 : MvPowerSeries (Fin d) 𝓞 →+* MvPowerSeries (Fin d ⊕ Fin d) 𝓞 := (MvPowerSeries.substAlgHom (R := 𝓞) (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inl j) (R := 𝓞)))).toRingHom with hs1
  set s2 : MvPowerSeries (Fin d) 𝓞 →+* MvPowerSeries (Fin d ⊕ Fin d) 𝓞 := (MvPowerSeries.substAlgHom (R := 𝓞) (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inr j) (R := 𝓞)))).toRingHom with hs2

  let G : MvPowerSeries (Fin d) 𝓞 := fun m => c m
  have hGc : ∀ m, G.coeff m = c m := fun m => rfl
  have hGpin : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ M → G.coeff m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
      (M < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m)) := fun m => by
    rw [hGc]; exact hc m
  let P : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 := sF G - s1 G - s2 G
  have hPdef : P = subst F.toPowerSeries G
      - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
      - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G := by
    simp only [P, hsF, hs1, hs2, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.coe_substAlgHom]
  obtain ⟨hPdeg, hPdiff⟩ :=
    MvFormalGroup.lt_degree_and_natCast_mul_coeff_subst_sub_sub_mem_of_scaledLogTrunc p hp F Fp hFp hFp0 φ
      hφ0 hφ1 hφF hφint M hM1 i G hGpin
  rw [← hPdef] at hPdeg hPdiff

  obtain ⟨ℓP, hℓP⟩ :=
    MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem p hp hfrob M P
      hPdiff

  set Δ := WittVector.map sF ℓ - WittVector.map s1 ℓ - WittVector.map s2 ℓ with hΔ
  have htopℓ : WittVector.ghostComponent (M - 1) ℓ = G := by
    ext μ
    rw [hℓ (M - 1) (by omega) μ, show M - 1 - (M - 1) = 0 from Nat.sub_self _, pow_zero, one_smul, hGc]
  have htopP : WittVector.ghostComponent (M - 1) ℓP = P := by
    ext μ
    rw [hℓP (M - 1) (by omega) μ, show M - 1 - (M - 1) = 0 from Nat.sub_self _, pow_zero, one_smul]
  have htopΔ : WittVector.ghostComponent (M - 1) Δ = P := by
    simp only [hΔ, map_sub, ghostComponent_map, htopℓ]
    rfl

  have hp𝓑 := natCast_mem_nonZeroDivisors (σ := Fin d ⊕ Fin d) p hp
  have hred := isReduced_quotient (σ := Fin d ⊕ Fin d) p hp hker
  have hcong : ∀ k, k < M → (Δ - ℓP).coeff k ∈ Ideal.span {(p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)} :=
    WittVector.coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced p hp𝓑 hred (Δ - ℓP) M
      (by rw [map_sub, htopΔ, htopP, sub_self]; exact Ideal.zero_mem _)

  have hdiffj : Δ.coeff j - ℓP.coeff j ∈ Ideal.span {(p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)} := by
    let π := Ideal.Quotient.mk (Ideal.span {(p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)})
    have hker' : ∀ a, π a = 0 ↔ a ∈ Ideal.span {(p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)} := fun a =>
      Ideal.Quotient.eq_zero_iff_mem
    have hW : WittVector.truncate M (WittVector.map π (Δ - ℓP)) = 0 := by
      rw [← RingHom.mem_ker, WittVector.mem_ker_truncate]
      intro k hk
      rw [WittVector.map_coeff, hker']
      exact hcong k hk
    rw [map_sub, map_sub, sub_eq_zero] at hW
    have := congrArg (fun t => TruncatedWittVector.coeff ⟨j, hjhi⟩ t) hW
    simp only [WittVector.coeff_truncate, WittVector.map_coeff] at this
    rw [← hker', map_sub, sub_eq_zero]
    exact this

  have hordj : ℓP.coeff j ∈ (Ideal.span (Set.range (X : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) ^ E := by
    refine mem_pow_of_forall_le_degree E _ fun μ' hμ' => ?_
    have hle := MvPowerSeries.le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq p hp M
      (p ^ (M - 1) + 1) P (fun μ hμ => hPdeg μ hμ) ℓP hℓP j hjhi μ' hμ'

    by_contra hlt
    rw [not_le] at hlt
    have hppos : 0 < p ^ (M - 1 - j) := pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) _
    have h1 : p ^ (M - 1 - j) * μ'.degree < p ^ (M - 1 - j) * E := (Nat.mul_lt_mul_left hppos).2 hlt
    have h2 : p ^ (M - 1 - j) * E ≤ p ^ (M - 1) := by
      have hE : E ≤ p ^ E := (Nat.lt_pow_self (Nat.Prime.one_lt (Fact.out : p.Prime))).le
      calc p ^ (M - 1 - j) * E ≤ p ^ (M - 1 - j) * p ^ E := Nat.mul_le_mul_left _ hE
        _ = p ^ (M - 1 - j + E) := (pow_add _ _ _).symm
        _ ≤ p ^ (M - 1) := Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : p.Prime)) (by omega)
    omega

  have : Δ.coeff j = (Δ.coeff j - ℓP.coeff j) + ℓP.coeff j := by ring
  rw [this]
  exact Submodule.add_mem_sup hdiffj hordj

end S17C2

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i : Fin d) (N E : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (c : (Fin d →₀ ℕ) → 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ M → c m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
        (M < m.degree → c m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
          (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) →
      ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (M - 1 - n) • m')) →
        ∀ j : ℕ, M - N ≤ j → j < M →
          (WittVector.map (MvPowerSeries.substAlgHom
                (MvPowerSeries.hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero)).toRingHom ℓ -
            WittVector.map (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
                (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inl j) (R := 𝓞)))).toRingHom ℓ -
            WittVector.map (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
                (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inr j) (R := 𝓞)))).toRingHom ℓ).coeff j ∈
            Ideal.span {(p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)} ⊔
              (Ideal.span (Set.range (X : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) ^ E :=
  S17C2.main p hp hker F Fp hFp hFp0 φ hφ0 hφ1 hφT hφF i N E

end S_MvFormalGroup_coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector
end P2MW
export P2MW.S_MvFormalGroup_coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector (solution)
