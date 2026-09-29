-- Prove2me | solution 1 for MvFormalGroup.exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d058b800-c581-5f5e-a5ca-41353b78825f

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_coeff_rescaledLog_mem_span_of_three_le_degree
import Theorems.Thm_MvFormalGroup_coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero
import Theorems.Thm_MvFormalGroup_exists_coeff_mem_span_pow_sub_log_of_isNilpotent_hasseWitt
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Theorems.Thm_MvFormalGroup_isNilpotent_hasseWittMatrix_nthSeries_of_isLocalRing_cartierDual
import Theorems.Thm_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span
import Definitions.Def_MvFormalGroup_NegV2
import Theorems.Thm_MvPowerSeries_eventually_coeff_mem_span_pow_of_subst_eq_X_of_exists_polynomial_inverse_mod
import Theorems.Thm_MvPolynomial_exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual_of_eq_two

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries linearPart mk mk.injEq toPowerSeries rec adicEval subst_elim_zero_left coeff_rescaledLog_mem_span_of_three_le_degree coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero exists_coeff_mem_span_pow_sub_log_of_isNilpotent_hasseWitt exists_subst_eq_X_of_linearPart_eq_one isNilpotent_hasseWittMatrix_nthSeries_of_isLocalRing_cartierDual coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span"
namespace RescaledExpTwo
p2m_open "MvFormalGroup"

private theorem two_mul_le_two_pow_add_one (L : ℕ) : 2 * L ≤ 2 ^ L + 1 := by
  induction L with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have : 2 ≤ 2 ^ n := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      calc 2 * (n + 1) = 2 * n + 2 := by ring
        _ ≤ 2 ^ n + 1 + 2 := by omega
        _ ≤ 2 ^ n + 2 ^ n + 1 := by omega
        _ = 2 ^ (n + 1) + 1 := by ring

private theorem log_le_half (p n : ℕ) (hp : 2 ≤ p) : Nat.log p n ≤ (n + 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have h1 : Nat.log p n ≤ Nat.log 2 n := Nat.log_anti_left (by norm_num) hp
  have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have h3 := two_mul_le_two_pow_add_one (Nat.log 2 n)
  omega

private theorem degree_two_cases {d : ℕ} (m : Fin d →₀ ℕ) (hm : m.degree = 2)
    (h : ∀ j, m ≠ Finsupp.single j 2) :
    ∃ j k : Fin d, j ≠ k ∧ m = Finsupp.single j 1 + Finsupp.single k 1 := by
  classical
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, map_zero] at hm; exact absurd hm (by norm_num)
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hm0
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hj
  have hsplit : m = Finsupp.single j (m j) + m.erase j := (Finsupp.single_add_erase j m).symm
  have hdeg : m.degree = m j + (m.erase j).degree := by
    conv_lhs => rw [hsplit]
    rw [map_add, Finsupp.degree_single]
  have hmj : m j ≤ 2 := by omega

  have hmj1 : m j = 1 := by
    rcases Nat.lt_or_ge (m j) 2 with hlt | hge
    · omega
    · have hmj2 : m j = 2 := le_antisymm hmj hge
      have h0 : (m.erase j).degree = 0 := by omega
      have : m.erase j = 0 := (Finsupp.degree_eq_zero_iff _).1 h0
      exact absurd (by rw [hsplit, this, hmj2, add_zero]) (h j)
  have h1 : (m.erase j).degree = 1 := by omega
  have hne : m.erase j ≠ 0 := by
    intro h0; rw [h0, map_zero] at h1; exact absurd h1 (by norm_num)
  obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 hne
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hk
  have hkj : k ≠ j := by
    rintro rfl; exact hk (Finsupp.erase_same)
  have hsplit' : m.erase j = Finsupp.single k ((m.erase j) k) + (m.erase j).erase k :=
    (Finsupp.single_add_erase k (m.erase j)).symm
  have hdeg' : (m.erase j).degree = (m.erase j) k + ((m.erase j).erase k).degree := by
    conv_lhs => rw [hsplit']
    rw [map_add, Finsupp.degree_single]
  have hk1 : (m.erase j) k = 1 := by omega
  have h0' : ((m.erase j).erase k).degree = 0 := by omega
  have hz : (m.erase j).erase k = 0 := (Finsupp.degree_eq_zero_iff _).1 h0'
  refine ⟨j, k, hkj.symm, ?_⟩
  rw [hsplit, hmj1, hsplit', hk1, hz, add_zero]

private theorem coeff_subst_mem {𝓞 : Type u} [CommRing 𝓞] {d : ℕ} {τ : Type*}
    (a : Fin d → MvPowerSeries τ 𝓞) (ha : HasSubst a) (I : Ideal 𝓞)
    (G : MvPowerSeries (Fin d) 𝓞) (hG : ∀ m, G.coeff m ∈ I) (n : τ →₀ ℕ) :
    (subst a G).coeff n ∈ I := by
  rw [coeff_subst ha G n, finsum_eq_sum _ (coeff_subst_finite ha G n)]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [smul_eq_mul]
  exact I.mul_mem_right _ (hG m)

end MvFormalGroup.RescaledExpTwo

open MvFormalGroup.RescaledExpTwo in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hp2 : p = 2)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]

    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))

    (v : ℕ) (hv : 0 < v)
    (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))

    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R))) :
    ∃ ψ : Fin d → MvPowerSeries (Fin d) 𝓞,

      (∀ i, (ψ i).constantCoeff = 0) ∧

      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧

      (∀ i, subst φ (ψ i) = X i) ∧

      (∀ i, subst ψ (φ i) = X i) := by
  classical
  subst hp2

  obtain ⟨ψ, hψ0, hψφ, hφψ⟩ := MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one φ hφ0 hφ1
  refine ⟨ψ, hψ0, ?_, hψφ, hφψ⟩

  have hHW := MvFormalGroup.isNilpotent_hasseWittMatrix_nthSeries_of_isLocalRing_cartierDual 2 hp hker F v hv
    R π hπ hπX hπeval hkerπ hπΔ hunip

  let G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞 := fun n =>
    Nat.rec (motive := fun n => Fin d → MvPowerSeries (Fin n × Fin d) 𝓞) (fun _ => 0)
      (fun n Gn => fun k => subst (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (Gn j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
        (F.toPowerSeries k)) n
  have hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
      subst (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
        (F.toPowerSeries k) := fun n k => rfl
  have hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k) := by
    intro k
    show G (0 + 1) k = _
    rw [hGsucc]
    have hX0 : HasSubst (fun sj : Fin 0 × Fin d => (X (Fin.castSucc sj.1, sj.2) :
        MvPowerSeries (Fin (0 + 1) × Fin d) 𝓞)) :=
      hasSubst_of_constantCoeff_zero fun sj => constantCoeff_X _
    have hfam : (Sum.elim
        (fun j => subst (fun sj : Fin 0 × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (0 + 1) × Fin d) 𝓞)) (G 0 j))
        (fun j => (X (Fin.last 0, j) : MvPowerSeries (Fin (0 + 1) × Fin d) 𝓞))) =
        Sum.elim (fun _ => (0 : MvPowerSeries (Fin 1 × Fin d) 𝓞))
          (fun j => (X ((0 : Fin 1), j) : MvPowerSeries (Fin 1 × Fin d) 𝓞)) := by
      funext s
      rcases s with j | j
      · show subst _ (0 : MvPowerSeries (Fin 0 × Fin d) 𝓞) = 0
        rw [← coe_substAlgHom hX0, map_zero]
      · rfl
    rw [hfam]
    exact MvFormalGroup.subst_elim_zero_left F (fun j => constantCoeff_X _) k

  let e : Fin d ⊕ Fin d ↪ Fin 2 × Fin d :=
    ⟨Sum.elim (fun j => ((0 : Fin 2), j)) (fun j => ((1 : Fin 2), j)), by
      intro a b h
      rcases a with a | a <;> rcases b with b | b <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h
      · exact congrArg Sum.inl h.2
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
      · exact congrArg Sum.inr h.2⟩
  have hG2 : ∀ k, G 2 k = MvPowerSeries.rename e (F.toPowerSeries k) := by
    intro k
    show G (1 + 1) k = _
    rw [hGsucc, MvPowerSeries.rename_eq_subst]
    congr 1
    funext s
    rcases s with j | j
    · show subst _ (G 1 j) = X (e (Sum.inl j))
      rw [hG1, subst_X (hasSubst_of_constantCoeff_zero fun sj => constantCoeff_X _)]
      rfl
    · rfl
  have hγB : ∀ k i,
      (F.toPowerSeries k).coeff (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1) -
        (F.nthSeries 2 k).coeff (Finsupp.single i 2) ∈ Ideal.span {((2 : ℕ) : 𝓞)} := by
    intro k i
    have h := MvFormalGroup.coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span 2 F G hG1 hGsucc k i
    have hsum : (∑ s : Fin 2, Finsupp.single (s, i) 1 : Fin 2 × Fin d →₀ ℕ) =
        Finsupp.embDomain e (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1) := by
      rw [Fin.sum_univ_two, Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]
      rfl
    have h' : (G 2 k).coeff (Finsupp.embDomain e (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1)) -
        (F.nthSeries 2 k).coeff (Finsupp.single i 2) ∈ Ideal.span {((2 : ℕ) : 𝓞)} := by
      rw [← hsum]; exact h
    rwa [hG2, MvPowerSeries.coeff_embDomain_rename] at h'

  let C : Matrix (Fin d) (Fin d) 𝓞 := Matrix.of fun i j => (φ i).coeff (Finsupp.single j 2)
  have hC : C.map (algebraMap 𝓞 (ZMod 2)) =
      -(Matrix.of fun i j : Fin d => algebraMap 𝓞 (ZMod 2) ((F.nthSeries 2 i).coeff (Finsupp.single j 2))) := by
    ext i j
    have hq := MvFormalGroup.coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero 2 hp F Fp hFp hFp0 φ hφ0
      hφ1 hφF i j

    have hγC : (F.toPowerSeries i).coeff (Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr j) 1) +
        (φ i).coeff (Finsupp.single j 2) = 0 := by
      refine (mem_nonZeroDivisors_iff.1 hp).2 _ ?_
      rw [add_mul]
      convert hq using 2
      push_cast
      ring
    have hCij : (φ i).coeff (Finsupp.single j 2) =
        -((F.toPowerSeries i).coeff (Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr j) 1)) :=
      eq_neg_of_add_eq_zero_right hγC
    have hγ : algebraMap 𝓞 (ZMod 2)
        ((F.toPowerSeries i).coeff (Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr j) 1)) =
        algebraMap 𝓞 (ZMod 2) ((F.nthSeries 2 i).coeff (Finsupp.single j 2)) := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker]
      exact hγB i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.neg_apply, C, hCij, map_neg, hγ]
  have hCnil : IsNilpotent (C.map (algebraMap 𝓞 (ZMod 2))) := by
    rw [hC]; exact hHW.neg

  obtain ⟨χ, hχ0, hχ1, -⟩ :=
    MvPolynomial.exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent 2 hker C hCnil

  obtain ⟨h3, hmixed⟩ := MvFormalGroup.coeff_rescaledLog_mem_span_of_three_le_degree 2 hp F Fp hFp hFp0 φ hφ0
    hφ1 hφF
  have hlin : ∀ i k, (φ i).coeff (Finsupp.single k 1) = if i = k then 1 else 0 := fun i k => by
    have := congrFun (congrFun hφ1 i) k
    simpa [MvFormalGroup.linearPart, Matrix.one_apply] using this

  have hΔ : ∀ (i : Fin d) (m : Fin d →₀ ℕ),
      (φ i - ((MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞) +
        ∑ j, MvPowerSeries.C (C i j) * (MvPowerSeries.X j : MvPowerSeries (Fin d) 𝓞) ^ 2)).coeff m ∈
        Ideal.span {((2 : ℕ) : 𝓞)} := by
    intro i m
    have hsq : ∀ j, ((MvPowerSeries.C (C i j) * (MvPowerSeries.X j : MvPowerSeries (Fin d) 𝓞) ^ 2)).coeff m
        = if m = Finsupp.single j 2 then C i j else 0 := fun j => by
      rw [coeff_C_mul, coeff_X_pow]; split_ifs <;> simp only [mul_one, mul_zero]
    simp only [map_sub, map_add, map_sum, hsq, coeff_X]
    rcases Nat.lt_or_ge m.degree 3 with hlt | hge
    ·
      rcases Nat.lt_or_ge m.degree 2 with hlt2 | hge2
      · rcases Nat.lt_or_ge m.degree 1 with hlt1 | hge1
        ·
          have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
          subst hm0
          have hx : ¬ ((0 : Fin d →₀ ℕ) = Finsupp.single i 1) := fun h => by
            have := congrArg (fun f => f i) h; simp at this
          have hs : ∀ j, ¬ ((0 : Fin d →₀ ℕ) = Finsupp.single j 2) := fun j h => by
            have := congrArg (fun f => f j) h; simp at this
          simp only [hx, if_false, hs, Finset.sum_const_zero, add_zero, sub_zero,
            MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0]
          exact zero_mem _
        ·
          have hdeg1 : m.degree = 1 := by omega
          obtain ⟨k, hk⟩ : ∃ k, m = Finsupp.single k 1 := by
            have hm0 : m ≠ 0 := by intro h0; rw [h0, map_zero] at hdeg1; exact absurd hdeg1 (by norm_num)
            obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 hm0
            simp only [Finsupp.coe_zero, Pi.zero_apply] at hk
            refine ⟨k, ?_⟩
            have hsplit : m = Finsupp.single k (m k) + m.erase k := (Finsupp.single_add_erase k m).symm
            have hdeg : m.degree = m k + (m.erase k).degree := by
              conv_lhs => rw [hsplit]
              rw [map_add, Finsupp.degree_single]
            have hmk : m k = 1 := by omega
            have hz : m.erase k = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
            rw [hsplit, hmk, hz, add_zero]
          subst hk
          have hs : ∀ j, ¬ (Finsupp.single k 1 = Finsupp.single j 2) := fun j h => by
            have := congrArg Finsupp.degree h
            rw [Finsupp.degree_single, Finsupp.degree_single] at this
            exact absurd this (by norm_num)
          simp only [hs, if_false, Finset.sum_const_zero, add_zero, hlin]
          by_cases hik : i = k
          · subst hik; simp
          · have : ¬ (Finsupp.single k 1 = Finsupp.single i 1) := fun h => hik
              ((Finsupp.single_left_injective (by norm_num)) h).symm
            simp [hik, this]
      ·
        have hdeg2 : m.degree = 2 := by omega
        have hx : ¬ (m = Finsupp.single i 1) := fun h => by
          rw [h, Finsupp.degree_single] at hdeg2; exact absurd hdeg2 (by norm_num)
        by_cases hsq' : ∃ j, m = Finsupp.single j 2
        · obtain ⟨j, rfl⟩ := hsq'
          have hsum : (∑ x : Fin d, if Finsupp.single j 2 = Finsupp.single x 2 then C i x else 0) = C i j := by
            rw [Finset.sum_eq_single j]
            · simp
            · intro b _ hb
              have : ¬ (Finsupp.single j 2 = Finsupp.single b 2) := fun h =>
                hb ((Finsupp.single_left_injective (by norm_num)) h).symm
              simp [this]
            · intro h; exact absurd (Finset.mem_univ j) h
          rw [hsum]
          simp only [hx, if_false, zero_add, C, Matrix.of_apply, sub_self]
          exact zero_mem _
        · push Not at hsq'
          obtain ⟨j, k, hjk, rfl⟩ := degree_two_cases m hdeg2 hsq'
          have hs : ∀ l, ¬ (Finsupp.single j 1 + Finsupp.single k 1 = Finsupp.single l 2) := fun l h =>
            hsq' l h
          simp only [hx, if_false, hs, Finset.sum_const_zero, add_zero, sub_zero]
          exact hmixed i j k hjk
    ·
      have hx : ¬ (m = Finsupp.single i 1) := fun h => by
        rw [h, Finsupp.degree_single] at hge; exact absurd hge (by norm_num)
      have hs : ∀ j, ¬ (m = Finsupp.single j 2) := fun j h => by
        rw [h, Finsupp.degree_single] at hge; exact absurd hge (by norm_num)
      simp only [hx, if_false, hs, Finset.sum_const_zero, add_zero, sub_zero]
      exact h3 i m hge

  have hχφ : ∀ (i : Fin d) (m : Fin d →₀ ℕ),
      (subst (fun j => (χ j : MvPowerSeries (Fin d) 𝓞)) (φ i)).coeff m -
        (MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞).coeff m ∈ Ideal.span {((2 : ℕ) : 𝓞)} := by
    intro i m
    have ha : HasSubst (fun j => (χ j : MvPowerSeries (Fin d) 𝓞)) :=
      hasSubst_of_constantCoeff_zero fun j => by
        show MvPowerSeries.constantCoeff (χ j : MvPowerSeries (Fin d) 𝓞) = 0
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
        exact hχ0 j
    have key := hχ1 i m
    have hdiff := coeff_subst_mem (fun j => (χ j : MvPowerSeries (Fin d) 𝓞)) ha (Ideal.span {((2 : ℕ) : 𝓞)})
      _ (hΔ i) m
    rw [subst_sub ha, map_sub] at hdiff
    have := Ideal.add_mem _ hdiff key
    convert this using 1
    ring

  have hJ : ∀ (i j : Fin d) (m : Fin d →₀ ℕ), 2 ≤ m.degree →
      ((m j : ℕ) : 𝓞) * (φ i).coeff m ∈ Ideal.span {((2 : ℕ) : 𝓞)} := by
    intro i j m hm
    rcases Nat.lt_or_ge m.degree 3 with hlt | hge
    · have hdeg2 : m.degree = 2 := by omega
      by_cases hsq : ∃ k, m = Finsupp.single k 2
      · obtain ⟨k, rfl⟩ := hsq
        by_cases hjk : k = j
        · subst hjk
          simp only [Finsupp.single_eq_same]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
        · simp [hjk]
      · push Not at hsq
        obtain ⟨k, l, hkl, rfl⟩ := degree_two_cases m hdeg2 hsq
        exact Ideal.mul_mem_left _ _ (hmixed i k l hkl)
    · exact Ideal.mul_mem_left _ _ (h3 i m hge)

  obtain ⟨A, B, C0, hAB, hslope⟩ :=
    MvFormalGroup.exists_coeff_mem_span_pow_sub_log_of_isNilpotent_hasseWitt 2 hp hker F Fp hFp hFp0 φ hφ0 hφ1
      hφF hHW
  have hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite,
      (φ i).coeff m ∈ Ideal.span {((2 : ℕ) : 𝓞) ^ N} := by
    intro N i
    rw [Filter.eventually_cofinite]
    let K : ℕ := 2 * N + 2 * C0 + 4
    let nb : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => K
    refine (Finset.Iic nb).finite_toSet.subset ?_
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    rw [Finset.coe_Iic, Set.mem_Iic]

    by_contra hle
    have hbig : K < m.degree := by
      by_contra hK
      push Not at hK
      apply hle
      intro j
      show m j ≤ nb j
      have : nb j = K := rfl
      rw [this]
      exact (Finsupp.le_degree j m).trans hK
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0, map_zero] at hbig; omega
    have hmem := hslope i m hm0
    have hq : A * Nat.log 2 m.degree / B ≤ (m.degree + 1) / 2 := by
      have hB : 0 < B := by omega
      have h1 : A * Nat.log 2 m.degree / B ≤ Nat.log 2 m.degree :=
        calc A * Nat.log 2 m.degree / B ≤ B * Nat.log 2 m.degree / B :=
              Nat.div_le_div_right (Nat.mul_le_mul_right _ hAB.le)
          _ = Nat.log 2 m.degree := Nat.mul_div_cancel_left _ hB
      exact h1.trans (log_le_half 2 _ le_rfl)
    have hN : N ≤ m.degree - 1 - A * Nat.log 2 m.degree / B - C0 := by
      simp only [K] at hbig
      omega
    exact hm (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hN) hmem)

  exact MvPowerSeries.eventually_coeff_mem_span_pow_of_subst_eq_X_of_exists_polynomial_inverse_mod 2 φ ψ
    hφ0 hφ1 hφT hJ hψ0 hψφ hφψ χ hχ0 hχφ

end S_MvFormalGroup_exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual_of_eq_two
end P2MW
export P2MW.S_MvFormalGroup_exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual_of_eq_two (solution)
