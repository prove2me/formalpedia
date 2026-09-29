-- Prove2me | solution 1 for ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ea78e70c-aafa-58d1-a9dd-8d2c753abb40

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL
import Theorems.Thm_ModularForm_exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem

set_option autoImplicit false

section FaithHelpers

open scoped MatrixGroups ModularForm
open UpperHalfPlane

private def faithCoeff (M : ℕ) (c : (ZMod M)ˣ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    ∑ d ∈ n.divisors,
      if ((n / d : ℕ) : ZMod M) = (c : ZMod M) ∨ ((n / d : ℕ) : ZMod M) = -(c : ZMod M)
      then (d : ℤ) ^ 3 else 0

private theorem faithCoeff_neg (M : ℕ) (c : (ZMod M)ˣ) (n : ℕ) :
    faithCoeff M (-c) n = faithCoeff M c n := by
  by_cases hn : n = 0
  · simp [faithCoeff, hn]
  · simp only [faithCoeff, hn, if_false, Units.val_neg, neg_neg]
    exact Finset.sum_congr rfl fun d _ => if_congr or_comm rfl rfl

private theorem faithCoeff_one (M : ℕ) (c : (ZMod M)ˣ) :
    faithCoeff M c 1 = if (1 : ZMod M) = (c : ZMod M) ∨ (1 : ZMod M) = -(c : ZMod M) then 1 else 0 := by
  simp [faithCoeff, Nat.divisors_one]

private theorem faith_ne_neg {M : ℕ} [NeZero M] (hM : 3 ≤ M) (c : (ZMod M)ˣ) : c ≠ -c := by
  intro h
  have hc : (c : ZMod M) = -(c : ZMod M) := by
    rw [← Units.val_neg]
    exact congrArg Units.val h
  have h3 : (2 : ZMod M) * (c : ZMod M) = 0 := by
    rw [two_mul]
    nth_rw 2 [hc]
    exact add_neg_cancel _
  have h2 : ((2 : ℤ) : ZMod M) = 0 := by
    rw [Int.cast_ofNat]
    exact (Units.mul_left_eq_zero c).mp h3
  have hdvd : M ∣ 2 := Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd 2 M).mp h2)
  have := Nat.le_of_dvd two_pos hdvd
  omega

private theorem faith_sum_even {M : ℕ} [NeZero M] (hM : 3 ≤ M) (A : Finset (ZMod M)ˣ)
    (hA : ∀ c ∈ A, -c ∈ A) (t : (ZMod M)ˣ → ℤ) (ht : ∀ c, t (-c) = t c) :
    ∑ c ∈ A, t c =
      2 * ∑ c ∈ A.filter (fun c : (ZMod M)ˣ => (c : ZMod M).val < ((-c : (ZMod M)ˣ) : ZMod M).val),
        t c := by
  classical
  have hval : ∀ c : (ZMod M)ˣ, (c : ZMod M).val ≠ ((-c : (ZMod M)ˣ) : ZMod M).val := by
    intro c h
    apply faith_ne_neg hM c
    exact Units.ext (ZMod.val_injective M h)
  rw [← Finset.sum_filter_add_sum_filter_not A
    (fun c : (ZMod M)ˣ => (c : ZMod M).val < ((-c : (ZMod M)ˣ) : ZMod M).val) t, two_mul]
  congr 1
  refine Finset.sum_nbij' (fun c => -c) (fun c => -c) ?_ ?_ (fun c _ => neg_neg c)
    (fun c _ => neg_neg c) (fun c _ => (ht c).symm)
  · intro c hc
    simp only [Finset.mem_filter, not_lt] at hc ⊢
    refine ⟨hA c hc.1, ?_⟩
    rw [neg_neg]
    exact lt_of_le_of_ne hc.2 (Ne.symm (hval c))
  · intro c hc
    simp only [Finset.mem_filter, not_lt] at hc ⊢
    refine ⟨hA c hc.1, ?_⟩
    rw [neg_neg]
    exact hc.2.le

end FaithHelpers

namespace CohCarrier
p2m_export "CohCarrier" "gamma0Units val_gamma0Units GammaH mem_GammaH_iff"
p2m_open "CohCarrier"

theorem mem_or_neg_mem_of_mem_sup_zpowers_neg_one {M : ℕ} (H : Subgroup (ZMod M)ˣ)
    {d : (ZMod M)ˣ} (hd : d ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) : d ∈ H ∨ -d ∈ H := by
  let S : Subgroup (ZMod M)ˣ :=
    { carrier := {x | x = 1 ∨ x = -1}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp
      inv_mem' := by
        rintro a (rfl | rfl) <;> simp }
  have hS : Subgroup.zpowers (-1 : (ZMod M)ˣ) ≤ S := by
    rw [Subgroup.zpowers_le]
    exact Or.inr rfl
  obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp hd
  rcases hS hz with hz1 | hz1
  · left; rw [hz1, mul_one]; exact hh
  · right; rw [hz1]; simpa using hh

end CohCarrier

open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH IsIntegralQExp intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset div_mem_qExpFunctionFieldC IsDiamondPullbackModL"
namespace KerDiamond
p2m_open "ModularCurve"

open scoped MatrixGroups ModularForm in

theorem faith_exact
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hd : CohCarrier.gamma0Units M ⟨γ, hγ⟩ ∉ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) :
    ∃ (k : ℤ) (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (pf pg pf₁ pg₁ : PowerSeries ℤ),
      ModularCurve.IsIntegralQExp f pf ∧ ModularCurve.IsIntegralQExp g pg ∧
      ModularCurve.IsIntegralQExp f₁ pf₁ ∧ ModularCurve.IsIntegralQExp g₁ pg₁ ∧
      (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∧
      (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∧
      ModularCurve.intSeriesC K pg ≠ 0 ∧ ModularCurve.intSeriesC K pg₁ ≠ 0 ∧
      ModularCurve.intSeriesC K pf * ModularCurve.intSeriesC K pg₁ ≠
        ModularCurve.intSeriesC K pg * ModularCurve.intSeriesC K pf₁ := by
  classical

  have hM3 : 3 ≤ M := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have hcard : Fintype.card (ZMod M)ˣ ≤ 1 := by
      rw [ZMod.card_units_eq_totient]
      interval_cases M <;> decide
    haveI : Subsingleton (ZMod M)ˣ := Fintype.card_le_one_iff_subsingleton.mp hcard
    exact hd (by rw [Subsingleton.elim (CohCarrier.gamma0Units M ⟨γ, hγ⟩) 1]; exact Subgroup.one_mem _)

  obtain ⟨R, hRq, hRs⟩ :=
    ModularForm.exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq M hM3
  have hRq' : ∀ c : (ZMod M)ˣ,
      qExpansion 1 (⇑(R c)) = (PowerSeries.mk (faithCoeff M c)).map (Int.castRingHom ℂ) :=
    fun c => (hRq c).symm
  obtain ⟨u, hu⟩ : ∃ u : (ZMod M)ˣ, u = CohCarrier.gamma0Units M ⟨γ, hγ⟩ := ⟨_, rfl⟩

  obtain ⟨H', hH'⟩ : ∃ H' : Subgroup (ZMod M)ˣ, H' = H ⊔ Subgroup.zpowers (-1) := ⟨_, rfl⟩
  have hnegH' : ∀ c ∈ H', -c ∈ H' := fun c hc => by
    rw [show -c = c * (-1) from (mul_neg_one c).symm]
    exact H'.mul_mem hc (hH' ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hHle : H ≤ H' := hH' ▸ le_sup_left
  have huH' : u ∉ H' := hu ▸ hH' ▸ hd
  have hnuH' : -u ∉ H' := fun h => huH' (by simpa using hnegH' _ h)
  let A : Finset (ZMod M)ˣ := Finset.univ.filter (· ∈ H')
  have hmemA : ∀ c, c ∈ A ↔ c ∈ H' := fun c => by simp [A]
  have hnegA : ∀ c ∈ A, -c ∈ A := fun c hc => (hmemA _).mpr (hnegH' c ((hmemA c).mp hc))
  have hnegU : ∀ c ∈ (Finset.univ : Finset (ZMod M)ˣ), -c ∈ (Finset.univ : Finset (ZMod M)ˣ) :=
    fun c _ => Finset.mem_univ _

  have h1per : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  have hsum_slash : ∀ (s : Finset (ZMod M)ˣ) (φ : (ZMod M)ˣ → ℍ → ℂ) (B : GL (Fin 2) ℝ),
      ((∑ c ∈ s, φ c) ∣[(4 : ℤ)] B) = ∑ c ∈ s, (φ c ∣[(4 : ℤ)] B) := by
    intro s φ B
    induction s using Finset.induction_on with
    | empty => simp [SlashAction.zero_slash]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  have hcoe_sum : ∀ (s : Finset (ZMod M)ˣ)
      (Φ : (ZMod M)ˣ → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4),
      (⇑(∑ c ∈ s, Φ c) : ℍ → ℂ) = ∑ c ∈ s, ⇑(Φ c) := fun s Φ => map_sum (FunLike.coeAddMonoidHom (ModularForm _ 4) ℍ ℂ) Φ s
  have hqsum : ∀ (s : Finset (ZMod M)ˣ)
      (Φ : (ZMod M)ˣ → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4),
      qExpansion 1 (⇑(∑ c ∈ s, Φ c)) = ∑ c ∈ s, qExpansion 1 (⇑(Φ c)) := by
    intro s Φ
    induction s using Finset.induction_on with
    | empty => simp [UpperHalfPlane.qExpansion_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
        ModularForm.qExpansion_add one_pos h1per (Φ a) (∑ c ∈ s, Φ c), ih]

  have hslash_sum : ∀ (s : Finset (ZMod M)ˣ) (v : (ZMod M)ˣ) (β : SL(2, ℤ))
      (hβ : β ∈ CongruenceSubgroup.Gamma0 M),
      ((⇑(∑ c ∈ s, R (c * v))) ∣[(4 : ℤ)] (β : GL (Fin 2) ℝ)) =
        ∑ c ∈ s, ⇑(R (c * v * (CohCarrier.gamma0Units M ⟨β, hβ⟩)⁻¹)) := by
    intro s v β hβ
    rw [hcoe_sum, hsum_slash]
    exact Finset.sum_congr rfl fun c _ => hRs (c * v) β hβ
  have hreindexA : ∀ (v w : (ZMod M)ˣ), w ∈ H' →
      ∑ c ∈ A, (⇑(R (c * v * w⁻¹)) : ℍ → ℂ) = ∑ c ∈ A, ⇑(R (c * v)) := by
    intro v w hw
    refine Finset.sum_nbij' (fun c => c * w⁻¹) (fun c => c * w) ?_ ?_ (fun c _ => by simp)
      (fun c _ => by simp) (fun c _ => by rw [mul_right_comm])
    · intro c hc
      rw [hmemA] at hc ⊢
      exact H'.mul_mem hc (H'.inv_mem hw)
    · intro c hc
      rw [hmemA] at hc ⊢
      exact H'.mul_mem hc hw
  have hreindexU : ∀ (w : (ZMod M)ˣ),
      ∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), (⇑(R (c * 1 * w⁻¹)) : ℍ → ℂ) =
        ∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), ⇑(R (c * 1)) := by
    intro w
    exact Fintype.sum_equiv (Equiv.mulRight w⁻¹) _ _ fun c => by simp

  have hinvA : ∀ (v : (ZMod M)ˣ) (β : SL(2, ℤ)), β ∈ CohCarrier.GammaH M H →
      ((⇑(∑ c ∈ A, R (c * v))) ∣[(4 : ℤ)] (β : GL (Fin 2) ℝ)) = ⇑(∑ c ∈ A, R (c * v)) := by
    intro v β hβ
    obtain ⟨hβ0, hβH⟩ := CohCarrier.mem_GammaH_iff.mp hβ
    rw [hslash_sum A v β hβ0, hreindexA v _ (hHle hβH), hcoe_sum]
  have hinvU : ∀ (β : SL(2, ℤ)), β ∈ CohCarrier.GammaH M H →
      ((⇑(∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), R (c * 1))) ∣[(4 : ℤ)] (β : GL (Fin 2) ℝ)) =
        ⇑(∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), R (c * 1)) := by
    intro β hβ
    obtain ⟨hβ0, _⟩ := CohCarrier.mem_GammaH_iff.mp hβ
    rw [hslash_sum _ 1 β hβ0, hreindexU, hcoe_sum]

  have hle1 : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
    intro β hβ
    rw [CohCarrier.mem_GammaH_iff]
    have hβ' := (CongruenceSubgroup.Gamma1_mem M β).mp hβ
    refine ⟨CongruenceSubgroup.Gamma1_in_Gamma0 M hβ, ?_⟩
    have h1 : CohCarrier.gamma0Units M ⟨β, CongruenceSubgroup.Gamma1_in_Gamma0 M hβ⟩ = 1 := by
      refine Units.ext ?_
      rw [CohCarrier.val_gamma0Units]
      simpa [CongruenceSubgroup.Gamma0Map] using hβ'.2.1
    rw [h1]
    exact H.one_mem
  haveI hfinH : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le hle1
  have hcusp : ∀ {c : OnePoint ℝ}, IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
      IsCusp c (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) := fun hc =>
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)
  let lift : ∀ (Φ : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4),
      (∀ β : SL(2, ℤ), β ∈ CohCarrier.GammaH M H → ((⇑Φ) ∣[(4 : ℤ)] (β : GL (Fin 2) ℝ)) = ⇑Φ) →
      ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 4 := fun Φ hΦ =>
    { toFun := Φ
      slash_action_eq' := fun A hA => by
        obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.mp hA
        exact hΦ β hβ
      holo' := Φ.holo'
      bdd_at_cusps' := fun hc => Φ.bdd_at_cusps' (hcusp hc) }
  have hlift : ∀ Φ hΦ, (⇑(lift Φ hΦ) : ℍ → ℂ) = ⇑Φ := fun _ _ => rfl
  let fH := lift (∑ c ∈ A, R (c * 1)) (hinvA 1)
  let f₁H := lift (∑ c ∈ A, R (c * u⁻¹)) (hinvA u⁻¹)
  let gH := lift (∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), R (c * 1)) hinvU

  have hint : ∀ (s : Finset (ZMod M)ˣ) (hs : ∀ c ∈ s, -c ∈ s) (v : (ZMod M)ˣ)
      (Φ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 4),
      (⇑Φ : ℍ → ℂ) = ⇑(∑ c ∈ s, R (c * v)) →
      ModularCurve.IsIntegralQExp (⇑((2⁻¹ : ℂ) • Φ))
        (PowerSeries.mk fun n => (∑ c ∈ s, faithCoeff M (c * v) n) / 2) := by
    intro s hs v Φ hΦ
    unfold ModularCurve.IsIntegralQExp
    rw [ModularForm.IsGLPos.coe_smul, hΦ, ModularForm.qExpansion_smul one_pos h1per, hqsum]
    ext n
    have hterm : ∀ c : (ZMod M)ˣ,
        (PowerSeries.coeff n) (qExpansion 1 (⇑(R (c * v)))) = ((faithCoeff M (c * v) n : ℤ) : ℂ) :=
      fun c => by rw [hRq' (c * v), PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_smul, map_sum, smul_eq_mul,
      eq_intCast, hterm]
    rw [← Int.cast_sum,
      faith_sum_even hM3 s hs (fun c => faithCoeff M (c * v) n)
        (fun c => by simp only [neg_mul, faithCoeff_neg]),
      Int.mul_ediv_cancel_left _ two_ne_zero]
    push_cast
    ring

  have hone_ne : (1 : (ZMod M)ˣ) ≠ -1 := faith_ne_neg hM3 1
  have hPQ : ∀ w : (ZMod M)ˣ,
      ((1 : ZMod M) = (w : ZMod M) ∨ (1 : ZMod M) = -(w : ZMod M)) ↔ (w = 1 ∨ w = -1) := by
    intro w
    rw [← Units.val_neg]
    constructor
    · rintro (h | h)
      · exact Or.inl (Units.val_eq_one.mp h.symm)
      · exact Or.inr (neg_eq_iff_eq_neg.mp (Units.val_eq_one.mp h.symm))
    · rintro (rfl | rfl) <;> simp
  have hcount : ∀ (s : Finset (ZMod M)ˣ) (v : (ZMod M)ˣ),
      ∑ c ∈ s, faithCoeff M (c * v) 1 = ((s.filter fun c => c * v = 1 ∨ c * v = -1).card : ℤ) := by
    intro s v
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [faithCoeff_one, hPQ]
  have hpair : ∀ (s : Finset (ZMod M)ˣ), (1 : (ZMod M)ˣ) ∈ s → (-1 : (ZMod M)ˣ) ∈ s →
      (s.filter fun c => c * 1 = 1 ∨ c * 1 = -1).card = 2 := by
    intro s h1 hm1
    rw [show (s.filter fun c => c * 1 = 1 ∨ c * 1 = -1) = {1, -1} from ?_, Finset.card_pair hone_ne]
    ext c
    simp only [Finset.mem_filter, mul_one, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨h1, Or.inl rfl⟩
      · exact ⟨hm1, Or.inr rfl⟩
  have hempty : (A.filter fun c => c * u⁻¹ = 1 ∨ c * u⁻¹ = -1).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc h
    rw [hmemA] at hc
    rcases h with h | h
    · exact huH' (by rw [mul_inv_eq_one] at h; exact h ▸ hc)
    · exact hnuH' (by rw [mul_inv_eq_iff_eq_mul, neg_one_mul] at h; exact h ▸ hc)
  have h1A : (1 : (ZMod M)ˣ) ∈ A := (hmemA 1).mpr H'.one_mem
  have hm1A : (-1 : (ZMod M)ˣ) ∈ A :=
    (hmemA _).mpr (hH' ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hpf1 : PowerSeries.coeff 1 (PowerSeries.mk fun n => (∑ c ∈ A, faithCoeff M (c * 1) n) / 2) = 1 := by
    rw [PowerSeries.coeff_mk, hcount A 1, hpair A h1A hm1A]
    norm_num
  have hpg1 : PowerSeries.coeff 1 (PowerSeries.mk fun n =>
      (∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), faithCoeff M (c * 1) n) / 2) = 1 := by
    rw [PowerSeries.coeff_mk, hcount _ 1, hpair _ (Finset.mem_univ _) (Finset.mem_univ _)]
    norm_num
  have hpf₁1 : PowerSeries.coeff 1 (PowerSeries.mk fun n =>
      (∑ c ∈ A, faithCoeff M (c * u⁻¹) n) / 2) = 0 := by
    rw [PowerSeries.coeff_mk, hcount A u⁻¹, hempty]
    norm_num
  have hcoe1 : ∀ p : PowerSeries ℤ,
      (ModularCurve.intSeriesC K p).coeff 1 = ((PowerSeries.coeff 1 p : ℤ) : K) := fun p => by
    rw [ModularCurve.intSeriesC, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]

  have hg0 : ModularCurve.intSeriesC K (PowerSeries.mk fun n =>
      (∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), faithCoeff M (c * 1) n) / 2) ≠ 0 := by
    intro h
    have h1 := hcoe1 (PowerSeries.mk fun n =>
      (∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), faithCoeff M (c * 1) n) / 2)
    rw [h, hpg1, HahnSeries.coeff_zero] at h1
    exact one_ne_zero (by exact_mod_cast h1.symm)
  have key : ∀ (Ψ : ℍ → ℂ), ((2⁻¹ : ℂ) • Ψ) ∣[(4 : ℤ)] (γ : GL (Fin 2) ℝ) =
      (2⁻¹ : ℂ) • (Ψ ∣[(4 : ℤ)] (γ : GL (Fin 2) ℝ)) := fun Ψ =>
    ModularForm.SL_smul_slash (4 : ℤ) γ Ψ (2⁻¹ : ℂ)
  refine ⟨4, (2⁻¹ : ℂ) • fH, (2⁻¹ : ℂ) • gH, (2⁻¹ : ℂ) • f₁H, (2⁻¹ : ℂ) • gH,
    PowerSeries.mk fun n => (∑ c ∈ A, faithCoeff M (c * 1) n) / 2,
    PowerSeries.mk fun n => (∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), faithCoeff M (c * 1) n) / 2,
    PowerSeries.mk fun n => (∑ c ∈ A, faithCoeff M (c * u⁻¹) n) / 2,
    PowerSeries.mk fun n => (∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), faithCoeff M (c * 1) n) / 2,
    hint A hnegA 1 fH (hlift _ (hinvA 1)), hint _ hnegU 1 gH (hlift _ hinvU),
    hint A hnegA u⁻¹ f₁H (hlift _ (hinvA u⁻¹)), hint _ hnegU 1 gH (hlift _ hinvU), ?_, ?_, hg0, hg0, ?_⟩
  ·
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, hlift _ (hinvA u⁻¹),
      hlift _ (hinvA 1), key, hslash_sum A 1 γ hγ, ← hu, hcoe_sum]
    congr 1
    exact Finset.sum_congr rfl fun c _ => by rw [mul_one]
  ·
    rw [ModularForm.IsGLPos.coe_smul, hlift _ hinvU, key, hslash_sum _ 1 γ hγ, ← hu,
      hreindexU u, hcoe_sum]
  ·
    intro h
    rw [mul_comm (ModularCurve.intSeriesC K (PowerSeries.mk fun n =>
      (∑ c ∈ (Finset.univ : Finset (ZMod M)ˣ), faithCoeff M (c * 1) n) / 2))] at h
    have h' := mul_right_cancel₀ hg0 h
    have h1 := congrArg (fun x : LaurentSeries K => x.coeff 1) h'
    simp only [hcoe1, hpf1, hpf₁1, Int.cast_one, Int.cast_zero] at h1
    exact one_ne_zero h1

open scoped MatrixGroups ModularForm in

theorem SL_slash_neg (k : ℤ) (A : SL(2, ℤ)) (f : ℍ → ℂ) :
    (f ∣[k] (-A)) = ((-1 : ℂ) ^ k) • (f ∣[k] A) := by
  ext τ
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, ModularForm.SL_slash_apply, smul_eq_mul,
    ModularGroup.SL_neg_smul]
  have hden : denom (↑(-A) : GL (Fin 2) ℝ) τ = -denom (A : GL (Fin 2) ℝ) τ := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    ring
  rw [hden, neg_eq_neg_one_mul, mul_zpow, zpow_neg (-1 : ℂ), ← inv_zpow, inv_neg, inv_one]
  ring

theorem neg_one_zpow_eq_pow_natAbs (k : ℤ) : (-1 : ℂ) ^ k = (-1 : ℂ) ^ k.natAbs := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp
  · rw [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_add, ← two_mul, pow_mul]; simp)

end ModularCurve.KerDiamond

open scoped MatrixGroups ModularForm in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem.ModularCurve in
set_option maxHeartbeats 3200000 in
theorem solution
    {K : Type*} [Field K] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    {ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))}
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ) (γ : CongruenceSubgroup.Gamma0 M) :
    ρ γ = 1 ↔ CohCarrier.gamma0Units M γ ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ) := by
  classical
  constructor
  ·
    intro h1
    by_contra hd
    have hd' : CohCarrier.gamma0Units M ⟨(γ : SL(2, ℤ)), γ.2⟩ ∉ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ) := by
      simpa using hd
    obtain ⟨k, f, g, f₁, g₁, pf, pg, pf₁, pg₁, hf, hg, hf₁, hg₁, ef, eg, hg0, hg₁0, hne⟩ :=
      ModularCurve.KerDiamond.faith_exact K M H (γ : SL(2, ℤ)) γ.2 hd'
    have key := hρ γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ ef eg hg0
      ⟨intSeriesC K pf₁ / intSeriesC K pg₁, div_mem_qExpFunctionFieldC f₁ g₁ hf₁ hg₁ hg₁0⟩ rfl
    rw [h1, AlgEquiv.one_apply] at key
    change intSeriesC K pf₁ / intSeriesC K pg₁ = intSeriesC K pf / intSeriesC K pg at key
    rw [div_eq_div_iff hg₁0 hg0] at key
    exact hne (key.symm.trans (mul_comm _ _))
  ·
    intro hd

    have hper : (1 : ℝ) ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
      rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH M H)]
      exact AddSubgroup.mem_zmultiples 1

    obtain ⟨sg, hsg⟩ : ∃ sg : ℤˣ, ∀ (k : ℤ) (φ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
        ((⇑φ : ℍ → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ((((sg ^ k : ℤˣ) : ℤ)) : ℂ) • (⇑φ : ℍ → ℂ) := by
      rcases CohCarrier.mem_or_neg_mem_of_mem_sup_zpowers_neg_one H hd with h | h
      · refine ⟨1, fun k φ => ?_⟩
        have hγH : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H := CohCarrier.mem_GammaH_iff.mpr ⟨γ.2, h⟩
        have e : ((⇑φ : ℍ → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑φ :=
          SlashInvariantForm.slash_action_eqn φ _ (Subgroup.mem_map_of_mem _ hγH)
        rw [e]
        simp
      · refine ⟨-1, fun k φ => ?_⟩
        have hneg0 : (-(γ : SL(2, ℤ))) ∈ CongruenceSubgroup.Gamma0 M := by
          have := CongruenceSubgroup.Gamma0_mem.mp γ.2
          rw [CongruenceSubgroup.Gamma0_mem]
          simp [Matrix.SpecialLinearGroup.coe_neg, this]
        have hunits : CohCarrier.gamma0Units M ⟨-(γ : SL(2, ℤ)), hneg0⟩ = -CohCarrier.gamma0Units M γ := by
          ext
          simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]
        have hnegH : (-(γ : SL(2, ℤ))) ∈ CohCarrier.GammaH M H :=
          CohCarrier.mem_GammaH_iff.mpr ⟨hneg0, by rw [hunits]; exact h⟩
        have e1 : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (((-(-(γ : SL(2, ℤ)))) : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
          rw [neg_neg]
        have e : ((⇑φ : ℍ → ℂ) ∣[k] ((-(γ : SL(2, ℤ)) : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑φ :=
          SlashInvariantForm.slash_action_eqn φ _ (Subgroup.mem_map_of_mem _ hnegH)
        rw [e1, ← ModularForm.SL_slash, ModularCurve.KerDiamond.SL_slash_neg, ModularForm.SL_slash, e]
        congr 1
        rw [ModularCurve.KerDiamond.neg_one_zpow_eq_pow_natAbs, ← Int.coe_negOnePow ℂ k]
        rfl

    have hgen : ∀ s ∈ intFormRatiosC K (CohCarrier.GammaH M H),
        ∀ hs : s ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H),
        ρ γ ⟨s, hs⟩ = ⟨s, hs⟩ := by
      intro s hsS hs
      obtain ⟨k, a, b, pa, pb, ha, hb, hb0, rfl⟩ := hsS
      set c : ℤ := ((sg ^ k : ℤˣ) : ℤ) with hcdef
      have hcK : ((c : ℤ) : K) ≠ 0 := by
        rw [hcdef]; exact (Units.map (Int.castRingHom K).toMonoidHom (sg ^ k)).ne_zero

      have hint : ∀ (φ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
          (p : PowerSeries ℤ), IsIntegralQExp φ p →
          IsIntegralQExp (⇑(((c : ℤ) : ℂ) • φ)) (c • p) := by
        intro φ p hp
        unfold IsIntegralQExp at hp ⊢
        rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos hper, map_zsmul, hp,
          Int.cast_smul_eq_zsmul]
      have hred : ∀ (p : PowerSeries ℤ),
          intSeriesC K (c • p) = ((c : ℤ) : LaurentSeries K) * intSeriesC K p := by
        intro p
        simp only [intSeriesC, zsmul_eq_mul, map_mul, map_intCast]
      have hCne : ((c : ℤ) : LaurentSeries K) ≠ 0 := by
        rw [← map_intCast (algebraMap K (LaurentSeries K)) c]
        exact (map_ne_zero_iff _ (algebraMap K (LaurentSeries K)).injective).mpr hcK
      have hslash_a : (⇑(((c : ℤ) : ℂ) • a) : ℍ → ℂ) = ((⇑a : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
        rw [ModularForm.IsGLPos.coe_smul, ModularForm.SL_slash, hsg k a]
      have hslash_b : (⇑(((c : ℤ) : ℂ) • b) : ℍ → ℂ) = ((⇑b : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
        rw [ModularForm.IsGLPos.coe_smul, ModularForm.SL_slash, hsg k b]
      have hx : ((⟨intSeriesC K pa / intSeriesC K pb, hs⟩ : qExpFunctionFieldC K (CohCarrier.GammaH M H)) :
            LaurentSeries K) =
          intSeriesC K (c • pa) / intSeriesC K (c • pb) := by
        rw [hred, hred, mul_div_mul_left _ _ hCne]
      have key := hρ γ k a b (((c : ℤ) : ℂ) • a) (((c : ℤ) : ℂ) • b) pa pb
        (c • pa) (c • pb) ha hb (hint a pa ha) (hint b pb hb)
        hslash_a hslash_b hb0 ⟨intSeriesC K pa / intSeriesC K pb, hs⟩ hx
      exact Subtype.ext key

    apply AlgEquiv.ext
    intro x
    have hle : qExpFunctionFieldC K (CohCarrier.GammaH M H) ≤
        IntermediateField.lift (IntermediateField.fixedField (Subgroup.zpowers (ρ γ))) := by
      change IntermediateField.adjoin K (intFormRatiosC K (CohCarrier.GammaH M H)) ≤ _
      rw [IntermediateField.adjoin_le_iff]
      intro s hsS
      have hs : s ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) := intFormRatiosC_subset K _ hsS
      apply (IntermediateField.mem_lift ⟨s, hs⟩).mpr
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      have hstab : Subgroup.zpowers (ρ γ) ≤ MulAction.stabilizer _ (⟨s, hs⟩ : qExpFunctionFieldC K (CohCarrier.GammaH M H)) := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact hgen s hsS hs
      exact MulAction.mem_stabilizer_iff.mp (hstab hg)
    have hx : x ∈ IntermediateField.fixedField (Subgroup.zpowers (ρ γ)) :=
      (IntermediateField.mem_lift x).mp (hle x.2)
    rw [IntermediateField.mem_fixedField_iff] at hx
    simpa using hx (ρ γ) (Subgroup.mem_zpowers _)

end S_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem
end P2MW
export P2MW.S_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem (solution)
