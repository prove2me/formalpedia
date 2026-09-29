-- Prove2me | solution 1 for NumberField.exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/881ebf7c-cf5c-58f4-b244-9d109ea35187

import Mathlib
import Definitions.Def_LanglandsTunnell_NormClass
import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_NumberField_RayCharacterData
import Definitions.Def_FrobeniusDensity_PrimeSums
import Definitions.Def_NumberField_PrimeNormSums
import Definitions.Def_NumberField_NormResidueCharacter
import Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries
import Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one
import Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
import Theorems.Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal
import Theorems.Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
import Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO
import Theorems.Thm_FrobeniusDensity_tailSum_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension

set_option autoImplicit false

noncomputable section

namespace P2mHeckeDensity

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply Filter Topology
open LanglandsTunnell.P2.Artin NumberField.PrimeNormSum NumberField.NormResidueChar
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable (K : Type) [Field K] [NumberField K] (m : ℕ) [NeZero m]

variable {K m}

theorem sign_norm_int_ne_zero {α : 𝓞 K} (hα : α ≠ 0) : SignType.sign (Algebra.norm ℤ α) ≠ 0 := by
  rw [Ne, sign_eq_zero_iff]
  exact Algebra.norm_ne_zero_iff.mpr hα

theorem isParity_chi (ψ : DirichletCharacter ℂ m) :
    M4aP2.IsParity K (fm K m) (chi K m ψ) (paritySet ψ) := by
  intro α hα h1
  rw [chiIdeal_chi_span ψ hα h1, paritySet]
  have hsn := sign_norm_int_ne_zero hα

  have hαK : (α : K) ≠ 0 := by
    rw [Ne, RingOfIntegers.coe_eq_zero_iff]; exact hα
  have hsignQ : SignType.sign (Algebra.norm ℤ α) = SignType.sign (Algebra.norm ℚ (α : K)) := by
    rw [← Algebra.coe_norm_int]
    rcases lt_trichotomy (Algebra.norm ℤ α) 0 with h | h | h
    · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
    · rw [h, sign_zero, Int.cast_zero, sign_zero]
    · rw [sign_pos h, sign_pos (by exact_mod_cast h)]
  have hprod := NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal K hαK
  by_cases heven : ψ (-1) = 1
  · rw [if_pos heven, M4aP2.signAt, Finset.prod_empty]
    rcases (show SignType.sign (Algebra.norm ℤ α) = 1 ∨ SignType.sign (Algebra.norm ℤ α) = -1 by
      rcases h3 : SignType.sign (Algebra.norm ℤ α) with _ | _ | _
      · exact absurd h3 hsn
      · right; rfl
      · left; rfl) with h | h
    · rw [h]; simp
    · rw [h]; simp [heven]
  · have hodd : ψ (-1) = -1 := (psi_neg_one_eq ψ).resolve_left heven
    rw [if_neg heven, M4aP2.signAt]

    have hR : ∏ v ∈ (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}),
        ((SignType.sign (embedding_of_isReal v.2 (α : K)) : ℤ) : ℂ) =
        ((SignType.sign (Algebra.norm ℤ α) : ℤ) : ℂ) := by
      rw [hsignQ, hprod]
      have : ∀ x : SignType, ((x : ℤ) : ℂ) = SignType.castHom x := fun x => by
        rcases x <;> simp
      simp_rw [this]
      rw [map_prod]
    rw [hR]
    rcases (show SignType.sign (Algebra.norm ℤ α) = 1 ∨ SignType.sign (Algebra.norm ℤ α) = -1 by
      rcases h3 : SignType.sign (Algebra.norm ℤ α) with _ | _ | _
      · exact absurd h3 hsn
      · right; rfl
      · left; rfl) with h | h
    · rw [h]; simp
    · rw [h]; simp [hodd]

section PrimeSums

variable {F : Type} [Field F] [NumberField F]

theorem tail_le {s : ℝ} (hs : 1 ≤ s) :
    (∑' v : HeightOneSpectrum (𝓞 F), if (Ideal.absNorm v.asIdeal).Prime then 0 else pw F s v) ≤ Ctail F := by
  rw [← tailSum_toReal, Ctail]
  refine ENNReal.toReal_mono ?_ (FrobeniusDensity.tailSum_le F hs)
  exact (ENNReal.mul_lt_top (ENNReal.natCast_ne_top _).lt_top tailConst_lt_top).ne

theorem exists_logpole (F : Type) [Field F] [NumberField F] :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 < s → s < 1 + δ →
      |(∑' v, pw F s v) + Real.log (s - 1)| ≤ C := by
  have h := FrobeniusDensity.primeSum_toReal_add_log_isBigO F
  rw [Asymptotics.isBigO_iff] at h
  obtain ⟨c, hc⟩ := h
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset] at hc
  obtain ⟨u, hu, hsub⟩ := hc
  refine ⟨c, u - 1, by linarith [Set.mem_Ioi.mp hu], fun s hs hsu => ?_⟩
  have hmem := hsub ⟨hs, by linarith⟩
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, norm_one, mul_one] at hmem
  rwa [primeSum_toReal] at hmem

end PrimeSums

section Bounds

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]

def good (w : HeightOneSpectrum (𝓞 L)) : Prop := (Ideal.absNorm w.asIdeal).Prime ∧ (m : 𝓞 L) ∉ w.asIdeal

variable (K m) in

def XL (L : Type) [Field L] [NumberField L] (s : ℝ) : ℝ :=
  ∑' w : HeightOneSpectrum (𝓞 L), if good (m := m) w then pw L s w else 0

theorem XL_term_nonneg (s : ℝ) (w : HeightOneSpectrum (𝓞 L)) :
    0 ≤ (if good (m := m) w then pw L s w else 0) := by
  split_ifs
  · exact pw_nonneg s w
  · exact le_rfl

theorem XL_term_le (s : ℝ) (w : HeightOneSpectrum (𝓞 L)) :
    (if good (m := m) w then pw L s w else 0) ≤ pw L s w := by
  split_ifs
  · exact le_rfl
  · exact pw_nonneg s w

theorem good_under {ζ : L} (hζ : IsPrimitiveRoot ζ m) {w : HeightOneSpectrum (𝓞 L)} (hw : good (m := m) w) :
    Ideal.absNorm (w.under (𝓞 K)).asIdeal = Ideal.absNorm w.asIdeal ∧
      (Ideal.absNorm (w.under (𝓞 K)).asIdeal : ZMod m) = 1 := by
  refine ⟨absNorm_under_eq_of_prime w hw.1, ?_⟩
  rw [absNorm_under_eq_of_prime w hw.1]
  exact absNorm_cast_eq_one hζ w hw.2

theorem XL_le {ζ : L} (hζ : IsPrimitiveRoot ζ m) {s : ℝ} (hs : 1 < s) :
    XL m L s ≤ Module.finrank K L * T K m 1 s := by
  set n := Module.finrank K L with hn
  set t : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => if (Ideal.absNorm v.asIdeal : ZMod m) = 1 then pw K s v else 0 with ht
  have htsum : Summable t := summable_T 1 hs
  have htnn : ∀ v, 0 ≤ t v := T_term_nonneg 1 s
  refine Real.tsum_le_of_sum_le (XL_term_nonneg s) fun TT => ?_
  set u : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 K) := fun w => w.under (𝓞 K) with hu
  have hmaps : ∀ w ∈ TT, u w ∈ TT.image u := fun w hw => Finset.mem_image_of_mem _ hw
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]

  have hfib : ∀ v : HeightOneSpectrum (𝓞 K), ∀ S : Finset (HeightOneSpectrum (𝓞 L)),
      (∀ w ∈ S, u w = v) → ∑ w ∈ S, (if good (m := m) w then pw L s w else 0) ≤ n * t v := by
    intro v S hS
    have hterm : ∀ w ∈ S, (if good (m := m) w then pw L s w else 0) ≤ t v := by
      intro w hw
      split_ifs with hg
      · obtain ⟨hN, h1⟩ := good_under (K := K) hζ hg
        rw [← hS w hw] at *
        rw [ht]
        simp only
        rw [if_pos h1, pw, pw, hN]
      · exact htnn v
    have hcard : S.card ≤ n := by
      have h1 : (S : Set (HeightOneSpectrum (𝓞 L))) ⊆ {w | w.under (𝓞 K) = v} := fun w hw => hS w hw
      have h2 := Set.ncard_le_ncard h1 (finite_fibre v)
      rw [Set.ncard_coe_finset] at h2
      exact h2.trans (ncard_fibre_le (m := m) v)
    calc ∑ w ∈ S, (if good (m := m) w then pw L s w else 0)
        ≤ ∑ w ∈ S, t v := Finset.sum_le_sum hterm
      _ = S.card * t v := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * t v := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (htnn v)
  calc ∑ v ∈ TT.image u, ∑ w ∈ TT with u w = v, (if good (m := m) w then pw L s w else 0)
      ≤ ∑ v ∈ TT.image u, n * t v :=
        Finset.sum_le_sum fun v _ => hfib v _ (fun w hw => (Finset.mem_filter.mp hw).2)
    _ = n * ∑ v ∈ TT.image u, t v := by rw [Finset.mul_sum]
    _ ≤ n * ∑' v, t v := by
        refine mul_le_mul_of_nonneg_left (htsum.sum_le_tsum _ (fun v _ => htnn v)) (Nat.cast_nonneg _)
    _ = n * T K m 1 s := by rw [T]

theorem tsum_pw_le_XL_add {s : ℝ} (hs : 1 < s) :
    (∑' w : HeightOneSpectrum (𝓞 L), pw L s w) ≤ XL m L s + Ctail L + nbad L m := by
  set g : HeightOneSpectrum (𝓞 L) → ℝ := fun w => if good (m := m) w then pw L s w else 0
  set tl : HeightOneSpectrum (𝓞 L) → ℝ := fun w => if (Ideal.absNorm w.asIdeal).Prime then 0 else pw L s w
  set bd : HeightOneSpectrum (𝓞 L) → ℝ := fun w => if (m : 𝓞 L) ∈ w.asIdeal then pw L s w else 0
  have hle : ∀ w, pw L s w ≤ g w + tl w + bd w := by
    intro w
    simp only [g, tl, bd, good]
    by_cases hp : (Ideal.absNorm w.asIdeal).Prime <;> by_cases hm : (m : 𝓞 L) ∈ w.asIdeal <;>
      simp [hp, hm, (pw_nonneg s w)]
  have hg : Summable g := (summable_pw hs).of_nonneg_of_le (XL_term_nonneg s) (XL_term_le s)
  have htl : Summable tl := summable_tail hs
  have hbd : Summable bd := by
    refine (summable_pw hs).of_nonneg_of_le (fun w => ?_) (fun w => ?_)
    · simp only [bd]; split_ifs; exacts [pw_nonneg s w, le_rfl]
    · simp only [bd]; split_ifs; exacts [le_rfl, pw_nonneg s w]
  have h1 : (∑' w, pw L s w) ≤ ∑' w, (g w + tl w + bd w) :=
    (summable_pw hs).tsum_le_tsum hle ((hg.add htl).add hbd)
  rw [(hg.add htl).tsum_add hbd, hg.tsum_add htl] at h1
  have h2 : (∑' w, tl w) ≤ Ctail L := tail_le hs.le
  have h3 : (∑' w, bd w) ≤ nbad L m := tsum_bad_le bd
    (fun w => by simp only [bd]; split_ifs; exacts [pw_le_one (by linarith) w, zero_le_one])
    (fun w hw => by simp only [bd]; rw [if_neg hw])
  have h4 : (∑' w, g w) = XL m L s := rfl
  linarith

theorem exists_fibre_finset (v : HeightOneSpectrum (𝓞 K)) (hcop : (Ideal.absNorm v.asIdeal).Coprime m)
    (h1 : (Ideal.absNorm v.asIdeal : ZMod m) = 1) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S.card = Module.finrank K L ∧
      (∀ w ∈ S, w.under (𝓞 K) = v ∧ Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal) := by
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  obtain ⟨hcnt, hnorm⟩ :=
    NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one K L m
      v.asIdeal hcop h1
  refine ⟨(finite_fibre v).toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ (finite_fibre v), ncard_fibre_eq, hcnt]
  · intro w hw
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw
    exact ⟨hw, hnorm w.asIdeal (mem_primesOver_of_under_eq hw)⟩

theorem finrank_mul_T_le {s : ℝ} (hs : 1 < s) :
    Module.finrank K L * T K m 1 s ≤ ∑' w : HeightOneSpectrum (𝓞 L), pw L s w := by
  set n := Module.finrank K L with hn
  set t : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => if (Ideal.absNorm v.asIdeal : ZMod m) = 1 then pw K s v else 0 with ht
  have htsum : Summable t := summable_T 1 hs
  rw [T, ← htsum.tsum_mul_left]
  refine Real.tsum_le_of_sum_le (fun v => mul_nonneg (Nat.cast_nonneg _) (T_term_nonneg 1 s v)) fun TT => ?_

  have hchoice : ∀ v : HeightOneSpectrum (𝓞 K), ∃ S : Finset (HeightOneSpectrum (𝓞 L)),
      ((Ideal.absNorm v.asIdeal : ZMod m) = 1 → S.card = n ∧
        (∀ w ∈ S, w.under (𝓞 K) = v ∧ Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal)) ∧
      ((Ideal.absNorm v.asIdeal : ZMod m) ≠ 1 → S = ∅) := by
    intro v
    by_cases h1 : (Ideal.absNorm v.asIdeal : ZMod m) = 1
    · have hcop : (Ideal.absNorm v.asIdeal).Coprime m := by
        have hu : IsUnit ((Ideal.absNorm v.asIdeal : ℕ) : ZMod m) := by rw [h1]; exact isUnit_one
        exact (ZMod.isUnit_iff_coprime _ _).mp hu
      obtain ⟨S, hS, hS'⟩ := exists_fibre_finset (L := L) v hcop h1
      exact ⟨S, fun _ => ⟨hS, hS'⟩, fun h => absurd h1 h⟩
    · exact ⟨∅, fun h => absurd h h1, fun _ => rfl⟩
  choose Fb hFb1 hFb2 using hchoice
  have hterm : ∀ v ∈ TT, (n : ℝ) * t v = ∑ w ∈ Fb v, pw L s w := by
    intro v _
    by_cases h1 : (Ideal.absNorm v.asIdeal : ZMod m) = 1
    · obtain ⟨hc, hw⟩ := hFb1 v h1
      have : ∀ w ∈ Fb v, pw L s w = pw K s v := fun w hw' => by rw [pw, pw, (hw w hw').2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hc, ht]
      simp only
      rw [if_pos h1]
    · rw [hFb2 v h1, Finset.sum_empty, ht]
      simp only
      rw [if_neg h1, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have hdisj : (TT : Set (HeightOneSpectrum (𝓞 K))).PairwiseDisjoint Fb := by
    intro v _ v' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    apply hne
    by_cases h1 : (Ideal.absNorm v.asIdeal : ZMod m) = 1
    · by_cases h1' : (Ideal.absNorm v'.asIdeal : ZMod m) = 1
      · rw [← ((hFb1 v h1).2 w hw).1, ← ((hFb1 v' h1').2 w hw').1]
      · rw [hFb2 v' h1'] at hw'; simp at hw'
    · rw [hFb2 v h1] at hw; simp at hw
  rw [← Finset.sum_biUnion hdisj]
  exact (summable_pw hs).sum_le_tsum _ (fun w _ => pw_nonneg s w)

end Bounds

section Characters

variable (K m)

def Pc (ψ : DirichletCharacter ℂ m) (s : ℝ) : ℂ :=
  ∑' v : HeightOneSpectrum (𝓞 K), ψ (Ideal.absNorm v.asIdeal : ZMod m) * (pw K s v : ℂ)

def Aset : Finset (DirichletCharacter ℂ m) := Finset.univ.filter fun ψ => chi K m ψ = 1

variable {K m}

theorem norm_Pc_term_le (ψ : DirichletCharacter ℂ m) (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖ψ (Ideal.absNorm v.asIdeal : ZMod m) * (pw K s v : ℂ)‖ ≤ pw K s v := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pw_nonneg s v)]
  calc ‖ψ (Ideal.absNorm v.asIdeal : ZMod m)‖ * pw K s v ≤ 1 * pw K s v :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one ψ _) (pw_nonneg s v)
    _ = pw K s v := one_mul _

theorem summable_Pc (ψ : DirichletCharacter ℂ m) {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => ψ (Ideal.absNorm v.asIdeal : ZMod m) * (pw K s v : ℂ) :=
  Summable.of_norm_bounded (summable_pw hs) (norm_Pc_term_le ψ s)

theorem norm_Pc_le (ψ : DirichletCharacter ℂ m) {s : ℝ} (hs : 1 < s) : ‖Pc K m ψ s‖ ≤ ∑' v, pw K s v :=
  tsum_of_norm_bounded (summable_pw hs).hasSum (norm_Pc_term_le ψ s)

theorem cpow_eq_pw (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) = (pw K s v : ℂ) := by
  rw [pw, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, Complex.ofReal_neg]

theorem tsum_chiIdeal_eq_Pc (ψ : DirichletCharacter ℂ m) (s : ℝ) :
    (∑' v : HeightOneSpectrum (𝓞 K),
      M4aP2.chiIdeal K (fm K m) (chi K m ψ) (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) = Pc K m ψ s := by
  refine tsum_congr fun v => ?_
  rw [chiIdeal_chi, cpow_eq_pw]

theorem sum_Pc_eq (a : (ZMod m)ˣ) {s : ℝ} (hs : 1 < s) :
    ∑ ψ : DirichletCharacter ℂ m, ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s =
      (m.totient : ℂ) * (T K m (a : ZMod m) s : ℂ) := by
  have hswap : ∑ ψ : DirichletCharacter ℂ m, ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s =
      ∑' v : HeightOneSpectrum (𝓞 K), ∑ ψ : DirichletCharacter ℂ m,
        ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * (ψ (Ideal.absNorm v.asIdeal : ZMod m) * (pw K s v : ℂ)) := by
    rw [Summable.tsum_finsetSum (fun ψ _ => (summable_Pc ψ hs).mul_left _)]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [Pc, tsum_mul_left]
  rw [hswap, T, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (a := (a : ZMod m)) (Units.isUnit a)
    (Ideal.absNorm v.asIdeal : ZMod m)
  rw [ZMod.inv_coe_unit] at horth
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, horth]
  by_cases h : (a : ZMod m) = (Ideal.absNorm v.asIdeal : ZMod m)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), Complex.ofReal_zero, mul_zero, zero_mul]

theorem mem_Aset {ψ : DirichletCharacter ℂ m} : ψ ∈ Aset K m ↔ chi K m ψ = 1 := by
  simp [Aset]

theorem one_mem_Aset : (1 : DirichletCharacter ℂ m) ∈ Aset K m := mem_Aset.mpr (chi_one K m)

theorem Aset_card_pos : 0 < (Aset K m).card := Finset.card_pos.mpr ⟨1, one_mem_Aset⟩

theorem psi_absNorm_of_mem_Aset {ψ : DirichletCharacter ℂ m} (hψ : ψ ∈ Aset K m)
    (v : HeightOneSpectrum (𝓞 K)) :
    ψ (Ideal.absNorm v.asIdeal : ZMod m) = if (m : 𝓞 K) ∈ v.asIdeal then 0 else 1 := by
  rw [← chiIdeal_chi, mem_Aset.mp hψ, chiIdeal_prime]
  by_cases hv : v.asIdeal ∣ fm K m
  · rw [dif_pos hv, if_pos ((dvd_fm_iff v).mp hv)]
  · rw [dif_neg hv, if_neg (by rwa [dvd_fm_iff] at hv), MonoidHom.one_apply]

theorem Pc_of_mem_Aset {ψ : DirichletCharacter ℂ m} (hψ : ψ ∈ Aset K m) (s : ℝ) :
    Pc K m ψ s = (P0 K m s : ℂ) := by
  rw [Pc, P0, Complex.ofReal_tsum]
  refine tsum_congr fun v => ?_
  rw [psi_absNorm_of_mem_Aset hψ]
  split_ifs <;> simp

theorem apply_eq_one_of_mem_Aset {ψ : DirichletCharacter ℂ m} (hψ : ψ ∈ Aset K m) {a : (ZMod m)ˣ}
    (ha : a ∈ (nu K m).range) : ψ (a : ZMod m) = 1 := by
  obtain ⟨g, rfl⟩ := ha
  rw [← chi_apply, mem_Aset.mp hψ, MonoidHom.one_apply]

theorem Aset_card_mul : (Aset K m).card * Nat.card (nu K m).range = m.totient := by
  set U₁ : Subgroup (ZMod m)ˣ := (nu K m).range
  have hker : (Aset K m).card = Nat.card (MonoidHom.domRestrictHom U₁ ℂˣ).ker := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr ?_
    refine (MulChar.equivToUnitHom.subtypeEquiv fun ψ => ?_)
    show ψ ∈ Aset K m ↔ MulChar.equivToUnitHom ψ ∈ (MonoidHom.domRestrictHom U₁ ℂˣ).ker
    rw [mem_Aset, MonoidHom.mem_ker, MonoidHom.domRestrictHom_apply]
    constructor
    · intro h
      ext u
      obtain ⟨g, hg⟩ := u.2
      rw [MonoidHom.restrict_apply, MonoidHom.one_apply, Units.val_one, ← MulChar.toUnitHom_eq,
        MulChar.coe_toUnitHom, ← hg, ← chi_apply, h, MonoidHom.one_apply]
    · intro h
      refine MonoidHom.ext fun g => ?_
      have hu := DFunLike.congr_fun h ⟨nu K m g, ⟨g, rfl⟩⟩
      rw [MonoidHom.restrict_apply, MonoidHom.one_apply] at hu
      have hu' := congrArg (fun x : ℂˣ => (x : ℂ)) hu
      simp only at hu'
      rw [← MulChar.toUnitHom_eq, MulChar.coe_toUnitHom, Units.val_one] at hu'
      rw [chi_apply, MonoidHom.one_apply]
      exact hu'
  rw [hker, CommGroup.card_restrictHom_ker ℂ U₁, ← Subgroup.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

theorem Aset_card_le_card_class (ψ₀ : DirichletCharacter ℂ m) :
    (Aset K m).card ≤ (Finset.univ.filter fun ψ : DirichletCharacter ℂ m => chi K m ψ = chi K m ψ₀).card := by
  refine Finset.card_le_card_of_injOn (fun θ => ψ₀ * θ) (fun θ hθ => ?_) (fun θ _ θ' _ h => mul_left_cancel h)
  rw [Finset.mem_coe, mem_Aset] at hθ
  rw [Finset.mem_coe, Finset.mem_filter, chi_mul, hθ, mul_one]
  exact ⟨Finset.mem_univ _, rfl⟩

end Characters

section Analytic

theorem exists_lipschitz_of_differentiable {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 ≤ s → s ≤ 2 → ‖g s - g 1‖ ≤ C * (s - 1) := by
  have hcd : Continuous (deriv g) := (hg.contDiff (n := 1)).continuous_deriv le_rfl
  have hcont : ContinuousOn (fun t : ℝ => deriv g t) (Set.Icc 1 2) :=
    (hcd.comp Complex.continuous_ofReal).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn hcont
  set h : ℝ → ℂ := fun t => g t with hh
  have hderiv : ∀ t : ℝ, HasDerivAt h (deriv g t) t := fun t =>
    (hg (t : ℂ)).hasDerivAt.comp_ofReal
  refine ⟨max M 0, le_max_right _ _, fun s hs1 hs2 => ?_⟩
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := h) (s := Set.Icc (1 : ℝ) 2)
    (C := max M 0) (fun t _ => (hderiv t).differentiableAt)
    (fun t ht => by rw [(hderiv t).deriv]; exact (hM t ht).trans (le_max_left _ _))
    (convex_Icc 1 2) (Set.left_mem_Icc.mpr (by norm_num)) ⟨hs1, hs2⟩
  rw [hh] at key
  simp only at key
  rw [Complex.ofReal_one] at key
  rwa [Real.norm_of_nonneg (by linarith)] at key

theorem exists_close {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ s : ℝ, 1 < s ∧ s < 1 + δ ∧ M ≤ -Real.log (s - 1) := by
  set e : ℝ := min (δ / 2) (Real.exp (-M)) with he
  have hepos : 0 < e := lt_min (half_pos hδ) (Real.exp_pos _)
  refine ⟨1 + e, by linarith, by linarith [min_le_left (δ / 2) (Real.exp (-M))], ?_⟩
  rw [add_sub_cancel_left]
  have h1 : Real.log e ≤ Real.log (Real.exp (-M)) :=
    Real.log_le_log hepos (min_le_right _ _)
  rw [Real.log_exp] at h1
  linarith

theorem false_of_forall_log_le {c M δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (h : ∀ s : ℝ, 1 < s → s < 1 + δ → c * (-Real.log (s - 1)) ≤ M) : False := by
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_close hδ (M / c + 1)
  have := h s hs1 hs2
  have h2 : c * (M / c + 1) ≤ c * (-Real.log (s - 1)) := mul_le_mul_of_nonneg_left hs3 hc.le
  rw [mul_add, mul_div_cancel₀ _ hc.ne', mul_one] at h2
  linarith

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]

def Lr (ψ : DirichletCharacter ℂ m) (s : ℝ) : ℂ := M4aTorus.rayClassLSeries K (fm K m) (chi K m ψ) s

omit [IsCyclotomicExtension {m} K L] in

theorem analytic_pkg (ψ : DirichletCharacter ℂ m) (hψ : ψ ∉ Aset K m) :
    ∃ (Λ : ℝ → ℂ) (g₁ : ℂ) (C₀ C₁ : ℝ), 0 ≤ C₁ ∧ ContinuousOn Λ (Set.Ioi 1) ∧
      (∀ s : ℝ, 1 < s → Complex.exp (Λ s) = Lr (K := K) ψ s) ∧
      (∀ s : ℝ, 1 < s → ‖Λ s - Pc K m ψ s‖ ≤ C₀) ∧
      (∀ s : ℝ, 1 < s → s ≤ 2 → ‖Lr (K := K) ψ s - g₁‖ ≤ C₁ * (s - 1)) := by
  obtain ⟨Λ, hcont, hexp, -, C₀, hC₀⟩ :=
    NumberField.exists_continuousOn_exp_eq_rayClassLSeries K (fm K m) (fm_ne_bot K m) (chi K m ψ)
  have hne : chi K m ψ ≠ 1 := fun h => hψ (mem_Aset.mpr h)
  obtain ⟨g, hg, hgL⟩ := NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one K (fm K m)
    (fm_ne_bot K m) (chi K m ψ) hne (paritySet ψ) (isParity_chi ψ)
  obtain ⟨C₁, hC₁, hlip⟩ := exists_lipschitz_of_differentiable hg
  refine ⟨Λ, g 1, C₀, C₁, hC₁, hcont, hexp, fun s hs => ?_, fun s hs hs2 => ?_⟩
  · have := hC₀ s hs
    rwa [tsum_chiIdeal_eq_Pc] at this
  · have h1 := hlip s hs.le hs2
    rwa [hgL s (by simp; linarith)] at h1

theorem re_eq_log_norm_exp (z : ℂ) : z.re = Real.log ‖Complex.exp z‖ := by
  rw [Complex.norm_exp, Real.log_exp]

end Analytic

section Squeeze

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]

omit [IsCyclotomicExtension {m} K L] in

theorem totient_mul_T_one {s : ℝ} (hs : 1 < s) :
    (m.totient : ℝ) * T K m 1 s = (Aset K m).card * P0 K m s + ∑ ψ ∈ (Aset K m)ᶜ, (Pc K m ψ s).re := by
  have h := sum_Pc_eq (K := K) (m := m) 1 hs
  simp only [inv_one, Units.val_one, map_one, one_mul] at h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum] at hre
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hre
  rw [← hre, ← Finset.sum_add_sum_compl (Aset K m)]
  congr 1
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [Pc_of_mem_Aset hψ, Complex.ofReal_re]), Finset.sum_const,
    nsmul_eq_mul]

omit [IsCyclotomicExtension {m} K L] in

theorem totient_mul_T_ge {a : (ZMod m)ˣ} (ha : a ∈ (nu K m).range) {s : ℝ} (hs : 1 < s) :
    (Aset K m).card * P0 K m s - ∑ ψ ∈ (Aset K m)ᶜ, ‖Pc K m ψ s‖ ≤ (m.totient : ℝ) * T K m (a : ZMod m) s := by
  have h := sum_Pc_eq (K := K) (m := m) a hs
  have hR : ((m.totient : ℂ) * (T K m (a : ZMod m) s : ℂ)).re = (m.totient : ℝ) * T K m (a : ZMod m) s := by
    simp [Complex.mul_re]
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, hR] at hre
  rw [← hre, ← Finset.sum_add_sum_compl (Aset K m)]
  have hA : ∑ ψ ∈ Aset K m, (ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s).re = (Aset K m).card * P0 K m s := by
    rw [Finset.sum_congr rfl (fun ψ hψ => by
      rw [apply_eq_one_of_mem_Aset hψ (inv_mem ha), one_mul, Pc_of_mem_Aset hψ, Complex.ofReal_re]),
      Finset.sum_const, nsmul_eq_mul]
  rw [hA]
  have hB : -∑ ψ ∈ (Aset K m)ᶜ, ‖Pc K m ψ s‖ ≤ ∑ ψ ∈ (Aset K m)ᶜ, (ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s).re := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun ψ _ => ?_
    have h1 : |(ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s).re| ≤ ‖ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s‖ ≤ ‖Pc K m ψ s‖ := by
      rw [norm_mul]
      calc ‖ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m)‖ * ‖Pc K m ψ s‖ ≤ 1 * ‖Pc K m ψ s‖ :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one ψ _) (norm_nonneg _)
        _ = ‖Pc K m ψ s‖ := one_mul _
    have := neg_abs_le (ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s).re
    linarith
  linarith

omit [IsCyclotomicExtension {m} K L] in

theorem totient_mul_T_le {a : (ZMod m)ˣ} (ha : a ∈ (nu K m).range) {s : ℝ} (hs : 1 < s) :
    (m.totient : ℝ) * T K m (a : ZMod m) s ≤ (Aset K m).card * P0 K m s + ∑ ψ ∈ (Aset K m)ᶜ, ‖Pc K m ψ s‖ := by
  have h := sum_Pc_eq (K := K) (m := m) a hs
  have hR : ((m.totient : ℂ) * (T K m (a : ZMod m) s : ℂ)).re = (m.totient : ℝ) * T K m (a : ZMod m) s := by
    simp [Complex.mul_re]
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, hR] at hre
  rw [← hre, ← Finset.sum_add_sum_compl (Aset K m)]
  have hA : ∑ ψ ∈ Aset K m, (ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s).re = (Aset K m).card * P0 K m s := by
    rw [Finset.sum_congr rfl (fun ψ hψ => by
      rw [apply_eq_one_of_mem_Aset hψ (inv_mem ha), one_mul, Pc_of_mem_Aset hψ, Complex.ofReal_re]),
      Finset.sum_const, nsmul_eq_mul]
  rw [hA]
  have hB : ∑ ψ ∈ (Aset K m)ᶜ, (ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s).re ≤ ∑ ψ ∈ (Aset K m)ᶜ, ‖Pc K m ψ s‖ := by
    refine Finset.sum_le_sum fun ψ _ => ?_
    have h1 : |(ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s).re| ≤ ‖ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s‖ ≤ ‖Pc K m ψ s‖ := by
      rw [norm_mul]
      calc ‖ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m)‖ * ‖Pc K m ψ s‖ ≤ 1 * ‖Pc K m ψ s‖ :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one ψ _) (norm_nonneg _)
        _ = ‖Pc K m ψ s‖ := one_mul _
    have := le_abs_self (ψ ((a⁻¹ : (ZMod m)ˣ) : ZMod m) * Pc K m ψ s).re
    linarith
  linarith

theorem alg_lower (A φ Lg CK nb R : ℝ) (hφ : φ ≠ 0) :
    (A / φ * Lg - (A * (CK + nb) + R) / φ) * φ = A * (Lg - CK - nb) - R := by
  field_simp
  ring

theorem alg_upper (A φ Lg CK nb R : ℝ) (hφ : φ ≠ 0) :
    (A / φ * Lg + (A * (CK + nb) + R) / φ) * φ = A * (Lg + CK) + R + A * nb := by
  field_simp
  ring

theorem alg_inv (A n φ : ℝ) (hn : n ≠ 0) (hφ : φ ≠ 0) (h : A * n = φ) : n⁻¹ = A / φ := by
  have hA : A ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact hφ h.symm
  rw [← h]
  field_simp

set_option maxHeartbeats 1600000 in

theorem main {ζ : L} (hζ : IsPrimitiveRoot ζ m) (τ : L ≃ₐ[K] L) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 < s → s < 1 + δ →
      |T K m ((hζ.autToPow K τ : (ZMod m)ˣ) : ZMod m) s -
        (Module.finrank K L : ℝ)⁻¹ * Real.log (1 / (s - 1))| ≤ C := by

  set n : ℕ := Module.finrank K L with hndef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank K L)
  set φ : ℝ := (m.totient : ℝ) with hφdef
  have hφpos : (0 : ℝ) < φ := by rw [hφdef]; exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)
  set A := Aset K m with hAdef
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast Aset_card_pos (K := K) (m := m)
  obtain ⟨CK, δK, hδK, hK⟩ := exists_logpole K
  obtain ⟨CL, δL, hδL, hL⟩ := exists_logpole L

  have hpk : ∀ ψ : DirichletCharacter ℂ m, ∃ (Λ : ℝ → ℂ) (g₁ : ℂ) (C₀ C₁ : ℝ), ψ ∉ Aset K m →
      (0 ≤ C₁ ∧ ContinuousOn Λ (Set.Ioi 1) ∧
      (∀ s : ℝ, 1 < s → Complex.exp (Λ s) = Lr (K := K) ψ s) ∧
      (∀ s : ℝ, 1 < s → ‖Λ s - Pc K m ψ s‖ ≤ C₀) ∧
      (∀ s : ℝ, 1 < s → s ≤ 2 → ‖Lr (K := K) ψ s - g₁‖ ≤ C₁ * (s - 1))) := by
    intro ψ
    by_cases hψ : ψ ∉ Aset K m
    · obtain ⟨Λ, g₁, C₀, C₁, h⟩ := analytic_pkg (K := K) ψ hψ
      exact ⟨Λ, g₁, C₀, C₁, fun _ => h⟩
    · exact ⟨0, 0, 0, 0, fun h => absurd h hψ⟩
  choose Λ g₁ C₀ C₁ hpkg using hpk
  have hC₁ : ∀ ψ, ψ ∉ A → 0 ≤ C₁ ψ := fun ψ h => (hpkg ψ h).1
  have hcont : ∀ ψ, ψ ∉ A → ContinuousOn (Λ ψ) (Set.Ioi 1) := fun ψ h => (hpkg ψ h).2.1
  have hexp : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → Complex.exp (Λ ψ s) = Lr (K := K) ψ s :=
    fun ψ h => (hpkg ψ h).2.2.1
  have hC₀ : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → ‖Λ ψ s - Pc K m ψ s‖ ≤ C₀ ψ := fun ψ h => (hpkg ψ h).2.2.2.1
  have hlip : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → s ≤ 2 → ‖Lr (K := K) ψ s - g₁ ψ‖ ≤ C₁ ψ * (s - 1) :=
    fun ψ h => (hpkg ψ h).2.2.2.2

  have hLpos : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → 0 < ‖Lr (K := K) ψ s‖ := by
    intro ψ hψ s hs
    rw [← hexp ψ hψ s hs]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hre : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → (Λ ψ s).re = Real.log ‖Lr (K := K) ψ s‖ := by
    intro ψ hψ s hs
    rw [re_eq_log_norm_exp, hexp ψ hψ s hs]
  have hPre_le : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → (Pc K m ψ s).re ≤ Real.log ‖Lr (K := K) ψ s‖ + C₀ ψ := by
    intro ψ hψ s hs
    have h1 : (Pc K m ψ s).re = (Λ ψ s).re - (Λ ψ s - Pc K m ψ s).re := by simp
    have h2 := Complex.abs_re_le_norm (Λ ψ s - Pc K m ψ s)
    have h3 := hC₀ ψ hψ s hs
    rw [h1, hre ψ hψ s hs]
    linarith [neg_abs_le (Λ ψ s - Pc K m ψ s).re]
  have hPre_ge : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → Real.log ‖Lr (K := K) ψ s‖ - C₀ ψ ≤ (Pc K m ψ s).re := by
    intro ψ hψ s hs
    have h1 : (Pc K m ψ s).re = (Λ ψ s).re - (Λ ψ s - Pc K m ψ s).re := by simp
    have h2 := Complex.abs_re_le_norm (Λ ψ s - Pc K m ψ s)
    have h3 := hC₀ ψ hψ s hs
    rw [h1, hre ψ hψ s hs]
    linarith [le_abs_self (Λ ψ s - Pc K m ψ s).re]
  have hPnorm_le : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → ‖Pc K m ψ s‖ ≤ ‖Λ ψ s‖ + C₀ ψ := by
    intro ψ hψ s hs
    have := norm_sub_norm_le (Pc K m ψ s) (Λ ψ s)
    rw [norm_sub_rev] at this
    linarith [hC₀ ψ hψ s hs]

  have hT1_ge : ∀ s : ℝ, 1 < s → s < 1 + δL →
      (φ / n) * (-Real.log (s - 1) - CL - Ctail L - nbad L m) ≤ φ * T K m 1 s := by
    intro s hs hsL
    have h1 := XL_le (K := K) (m := m) hζ hs
    have h2 := tsum_pw_le_XL_add (m := m) (L := L) hs
    have h3 := hL s hs hsL
    have h4 : -CL ≤ (∑' w, pw L s w) + Real.log (s - 1) := by
      have := neg_abs_le ((∑' w, pw L s w) + Real.log (s - 1)); linarith
    have h5 : (-Real.log (s - 1) - CL - Ctail L - nbad L m) ≤ n * T K m 1 s := by linarith
    have h6 : (φ / n) * (-Real.log (s - 1) - CL - Ctail L - nbad L m) ≤ (φ / n) * (n * T K m 1 s) :=
      mul_le_mul_of_nonneg_left h5 (div_nonneg hφpos.le hnpos.le)
    calc (φ / n) * (-Real.log (s - 1) - CL - Ctail L - nbad L m) ≤ (φ / n) * (n * T K m 1 s) := h6
      _ = φ * T K m 1 s := by field_simp
  have hT1_le : ∀ s : ℝ, 1 < s → s < 1 + δL → φ * T K m 1 s ≤ (φ / n) * (-Real.log (s - 1) + CL) := by
    intro s hs hsL
    have h1 := finrank_mul_T_le (K := K) (m := m) (L := L) hs
    have h3 := hL s hs hsL
    have h4 : (∑' w, pw L s w) + Real.log (s - 1) ≤ CL := by
      have := le_abs_self ((∑' w, pw L s w) + Real.log (s - 1)); linarith
    have h5 : n * T K m 1 s ≤ -Real.log (s - 1) + CL := by linarith
    calc φ * T K m 1 s = (φ / n) * (n * T K m 1 s) := by field_simp
      _ ≤ (φ / n) * (-Real.log (s - 1) + CL) := mul_le_mul_of_nonneg_left h5 (div_nonneg hφpos.le hnpos.le)
  have hP0_le : ∀ s : ℝ, 1 < s → s < 1 + δK → P0 K m s ≤ -Real.log (s - 1) + CK := by
    intro s hs hsK
    have h1 := P0_le_tsum_pw (F := K) (m := m) hs
    have h3 := hK s hs hsK
    have := le_abs_self ((∑' v, pw K s v) + Real.log (s - 1)); linarith
  have hP0_ge : ∀ s : ℝ, 1 < s → s < 1 + δK → -Real.log (s - 1) - CK - nbad K m ≤ P0 K m s := by
    intro s hs hsK
    have h1 := tsum_pw_le_P0_add (F := K) (m := m) hs
    have h3 := hK s hs hsK
    have := neg_abs_le ((∑' v, pw K s v) + Real.log (s - 1)); linarith

  have hg₁ : ∀ ψ₀, ψ₀ ∉ A → g₁ ψ₀ ≠ 0 := by
    intro ψ₀ hψ₀ h0
    set B : Finset (DirichletCharacter ℂ m) := Finset.univ.filter fun ψ => chi K m ψ = chi K m ψ₀ with hB
    have hBA : A.card ≤ B.card := Aset_card_le_card_class ψ₀
    have hBsub : B ⊆ Aᶜ := by
      intro ψ hψ
      rw [Finset.mem_compl, hAdef, mem_Aset]
      rw [hB, Finset.mem_filter] at hψ
      rw [hψ.2]
      exact fun h => hψ₀ (mem_Aset.mpr h)

    have hC₁pos : 0 < C₁ ψ₀ := by
      have h1 := hlip ψ₀ hψ₀ (3/2) (by norm_num) (by norm_num)
      rw [h0, sub_zero] at h1
      have h2 := hLpos ψ₀ hψ₀ (3/2) (by norm_num)
      nlinarith

    set mψ : DirichletCharacter ℂ m → ℝ := fun ψ => ‖g₁ ψ‖ + C₁ ψ + |C₀ ψ| + |Real.log (C₁ ψ₀)| with hmψ
    have hbad : ∀ ψ ∈ B, ∀ s : ℝ, 1 < s → s ≤ 2 → (Pc K m ψ s).re ≤ Real.log (s - 1) + mψ ψ := by
      intro ψ hψB s hs hs2
      have hψ : ψ ∉ A := Finset.mem_compl.mp (hBsub hψB)
      have hLeq : Lr (K := K) ψ s = Lr (K := K) ψ₀ s := by
        rw [Lr, Lr, (Finset.mem_filter.mp hψB).2]
      have h1 := hPre_le ψ hψ s hs
      have h2 : ‖Lr (K := K) ψ₀ s‖ ≤ C₁ ψ₀ * (s - 1) := by
        have := hlip ψ₀ hψ₀ s hs hs2
        rwa [h0, sub_zero] at this
      have h3 : Real.log ‖Lr (K := K) ψ s‖ ≤ Real.log (C₁ ψ₀) + Real.log (s - 1) := by
        rw [hLeq, ← Real.log_mul hC₁pos.ne' (by linarith)]
        exact Real.log_le_log (hLpos ψ₀ hψ₀ s hs) h2
      have h4 : Real.log (C₁ ψ₀) ≤ |Real.log (C₁ ψ₀)| := le_abs_self _
      have h5 : C₀ ψ ≤ |C₀ ψ| := le_abs_self _
      have h6 : 0 ≤ ‖g₁ ψ‖ + C₁ ψ := add_nonneg (norm_nonneg _) (hC₁ ψ hψ)
      rw [hmψ]
      simp only
      linarith
    have hgood : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → s ≤ 2 → (Pc K m ψ s).re ≤ mψ ψ := by
      intro ψ hψ s hs hs2
      have h1 := hPre_le ψ hψ s hs
      have h2 : Real.log ‖Lr (K := K) ψ s‖ ≤ ‖Lr (K := K) ψ s‖ - 1 := Real.log_le_sub_one_of_pos (hLpos ψ hψ s hs)
      have h3 : ‖Lr (K := K) ψ s‖ ≤ ‖g₁ ψ‖ + C₁ ψ * (s - 1) := by
        have := norm_sub_norm_le (Lr (K := K) ψ s) (g₁ ψ)
        linarith [hlip ψ hψ s hs hs2]
      have h4 : C₁ ψ * (s - 1) ≤ C₁ ψ := by nlinarith [hC₁ ψ hψ]
      have h5 : C₀ ψ ≤ |C₀ ψ| := le_abs_self _
      have h6 : 0 ≤ |Real.log (C₁ ψ₀)| := abs_nonneg _
      rw [hmψ]
      simp only
      linarith

    set Mall : ℝ := ∑ ψ ∈ Aᶜ, mψ ψ with hMall
    have hsum_le : ∀ s : ℝ, 1 < s → s ≤ 2 →
        ∑ ψ ∈ Aᶜ, (Pc K m ψ s).re ≤ A.card * Real.log (s - 1) + Mall := by
      intro s hs hs2
      have hlogneg : Real.log (s - 1) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      have h1 : ∑ ψ ∈ Aᶜ, (Pc K m ψ s).re ≤ ∑ ψ ∈ Aᶜ, (mψ ψ + if ψ ∈ B then Real.log (s - 1) else 0) := by
        refine Finset.sum_le_sum fun ψ hψc => ?_
        have hψ : ψ ∉ A := Finset.mem_compl.mp hψc
        by_cases hb : ψ ∈ B
        · rw [if_pos hb]; linarith [hbad ψ hb s hs hs2]
        · rw [if_neg hb, add_zero]; exact hgood ψ hψ s hs hs2
      rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul] at h1
      have h2 : (Aᶜ ∩ B) = B := Finset.inter_eq_right.mpr hBsub
      rw [h2] at h1
      have h3 : (B.card : ℝ) * Real.log (s - 1) ≤ (A.card : ℝ) * Real.log (s - 1) :=
        mul_le_mul_of_nonpos_right (by exact_mod_cast hBA) hlogneg
      linarith

    set δ₁ : ℝ := min 1 (min δK δL) with hδ₁
    have hδ₁pos : 0 < δ₁ := lt_min one_pos (lt_min hδK hδL)
    refine false_of_forall_log_le (c := φ / n) (M := A.card * CK + Mall + (φ / n) * (CL + Ctail L + nbad L m))
      (div_pos hφpos hnpos) hδ₁pos fun s hs hsδ => ?_
    have hs2 : s ≤ 2 := by linarith [min_le_left 1 (min δK δL)]
    have hsK : s < 1 + δK := by linarith [min_le_right 1 (min δK δL), min_le_left δK δL]
    have hsL : s < 1 + δL := by linarith [min_le_right 1 (min δK δL), min_le_right δK δL]
    have h1 := totient_mul_T_one (K := K) (m := m) hs
    have h2 := hsum_le s hs hs2
    have h3 := hP0_le s hs hsK
    have h4 := hT1_ge s hs hsL
    have h5 : (A.card : ℝ) * P0 K m s ≤ A.card * (-Real.log (s - 1) + CK) :=
      mul_le_mul_of_nonneg_left h3 hApos.le
    have h6 : φ * T K m 1 s ≤ A.card * CK + Mall := by
      rw [← hAdef, ← hφdef] at h1
      nlinarith
    nlinarith

  set δψ : DirichletCharacter ℂ m → ℝ :=
    fun ψ => if ψ ∈ A then 1 else min 1 (‖g₁ ψ‖ / (2 * (C₁ ψ + 1))) with hδψ
  have hδψpos : ∀ ψ, 0 < δψ ψ := by
    intro ψ
    rw [hδψ]
    simp only
    split_ifs with h
    · exact one_pos
    · exact lt_min one_pos (div_pos (norm_pos_iff.mpr (hg₁ ψ h)) (by linarith [hC₁ ψ h]))
  have hδψle : ∀ ψ, δψ ψ ≤ 1 := by
    intro ψ
    rw [hδψ]
    simp only
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  set δ₂ : ℝ := Finset.univ.inf' ⟨1, Finset.mem_univ _⟩ δψ with hδ₂
  have hδ₂pos : 0 < δ₂ := (Finset.lt_inf'_iff _).mpr fun ψ _ => hδψpos ψ
  have hδ₂le : ∀ ψ, δ₂ ≤ δψ ψ := fun ψ => Finset.inf'_le _ (Finset.mem_univ ψ)
  have hLge : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → s ≤ 1 + δ₂ → ‖g₁ ψ‖ / 2 ≤ ‖Lr (K := K) ψ s‖ := by
    intro ψ hψ s hs hsδ
    have hδ : s - 1 ≤ ‖g₁ ψ‖ / (2 * (C₁ ψ + 1)) := by
      have := hδ₂le ψ
      rw [hδψ] at this
      simp only [if_neg hψ] at this
      linarith [min_le_right 1 (‖g₁ ψ‖ / (2 * (C₁ ψ + 1)))]
    have hs2 : s ≤ 2 := by linarith [hδ₂le ψ, hδψle ψ]
    have h1 := hlip ψ hψ s hs hs2
    have hne : C₁ ψ + 1 ≠ 0 := by linarith [hC₁ ψ hψ]
    have h2 : C₁ ψ * (s - 1) ≤ ‖g₁ ψ‖ / 2 := by
      calc C₁ ψ * (s - 1) ≤ (C₁ ψ + 1) * (s - 1) := by nlinarith
        _ ≤ (C₁ ψ + 1) * (‖g₁ ψ‖ / (2 * (C₁ ψ + 1))) :=
            mul_le_mul_of_nonneg_left hδ (by linarith [hC₁ ψ hψ])
        _ = ‖g₁ ψ‖ / 2 := by field_simp
    have := norm_sub_norm_le (g₁ ψ) (Lr (K := K) ψ s)
    rw [norm_sub_rev] at this
    linarith
  set kψ : DirichletCharacter ℂ m → ℝ := fun ψ => |Real.log (‖g₁ ψ‖ / 2)| + |C₀ ψ| with hkψ
  have hPre_lb : ∀ ψ, ψ ∉ A → ∀ s : ℝ, 1 < s → s ≤ 1 + δ₂ → -kψ ψ ≤ (Pc K m ψ s).re := by
    intro ψ hψ s hs hsδ
    have h1 := hPre_ge ψ hψ s hs
    have h2 : Real.log (‖g₁ ψ‖ / 2) ≤ Real.log ‖Lr (K := K) ψ s‖ :=
      Real.log_le_log (by positivity [norm_pos_iff.mpr (hg₁ ψ hψ)]) (hLge ψ hψ s hs hsδ)
    rw [hkψ]
    simp only
    linarith [neg_abs_le (Real.log (‖g₁ ψ‖ / 2)), le_abs_self (C₀ ψ)]
  set Kall : ℝ := ∑ ψ ∈ Aᶜ, kψ ψ with hKall
  have hsum_ge : ∀ s : ℝ, 1 < s → s ≤ 1 + δ₂ → -Kall ≤ ∑ ψ ∈ Aᶜ, (Pc K m ψ s).re := by
    intro s hs hsδ
    rw [hKall, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun ψ hψc => hPre_lb ψ (Finset.mem_compl.mp hψc) s hs hsδ

  have hAle : (A.card : ℝ) ≤ φ / n := by
    by_contra hlt
    push Not at hlt
    set δ₃ : ℝ := min δ₂ (min δK δL) with hδ₃
    have hδ₃pos : 0 < δ₃ := lt_min hδ₂pos (lt_min hδK hδL)
    refine false_of_forall_log_le (c := A.card - φ / n)
      (M := A.card * (CK + nbad K m) + Kall + (φ / n) * CL) (by linarith) hδ₃pos fun s hs hsδ => ?_
    have hs2 : s ≤ 1 + δ₂ := by linarith [min_le_left δ₂ (min δK δL)]
    have hsK : s < 1 + δK := by linarith [min_le_right δ₂ (min δK δL), min_le_left δK δL]
    have hsL : s < 1 + δL := by linarith [min_le_right δ₂ (min δK δL), min_le_right δK δL]
    have h1 := totient_mul_T_one (K := K) (m := m) hs
    have h2 := hsum_ge s hs hs2
    have h3 := hP0_ge s hs hsK
    have h4 := hT1_le s hs hsL
    have h5 : (A.card : ℝ) * (-Real.log (s - 1) - CK - nbad K m) ≤ A.card * P0 K m s :=
      mul_le_mul_of_nonneg_left h3 hApos.le
    rw [← hAdef, ← hφdef] at h1
    nlinarith
  have hU : (nu K m).range = U0 K m hζ := by
    apply Subgroup.eq_of_le_of_card_ge (range_nu_le_U0 K m hζ)
    rw [card_U0]
    have h1 := Aset_card_mul (K := K) (m := m)
    have h2 : (n : ℝ) * A.card ≤ A.card * Nat.card (nu K m).range := by
      have h3 : (A.card : ℝ) * n ≤ φ := by
        rw [le_div_iff₀ hnpos] at hAle; exact hAle
      have h4 : (φ : ℝ) = A.card * Nat.card (nu K m).range := by
        rw [hφdef, ← h1, hAdef]; push_cast; ring
      linarith
    have h5 : (n : ℝ) ≤ Nat.card (nu K m).range := le_of_mul_le_mul_left (by linarith) hApos
    exact_mod_cast h5

  have hAn : (A.card : ℝ) * n = φ := by
    have h1 := Aset_card_mul (K := K) (m := m)
    rw [hU, card_U0] at h1
    rw [hAdef, hndef, hφdef]
    exact_mod_cast h1
  set a : (ZMod m)ˣ := hζ.autToPow K τ with hadef
  have ha : a ∈ (nu K m).range := by rw [hU]; exact ⟨τ, rfl⟩

  have hbr : ∀ ψ : DirichletCharacter ℂ m, ∃ Cb δb : ℝ, 0 < δb ∧
      (ψ ∉ A → ∀ s : ℝ, 1 < s → s < 1 + δb → ‖Λ ψ s‖ ≤ Cb) := by
    intro ψ
    by_cases hψ : ψ ∉ A
    · have hlim : Tendsto (Lr (K := K) ψ) (𝓝[>] 1) (𝓝 (g₁ ψ)) := by
        rw [Metric.tendsto_nhdsWithin_nhds]
        intro ε hε
        refine ⟨min 1 (ε / (C₁ ψ + 1)), lt_min one_pos (div_pos hε (by linarith [hC₁ ψ hψ])), ?_⟩
        intro s hs hsd
        rw [Set.mem_Ioi] at hs
        rw [Real.dist_eq, abs_of_pos (by linarith)] at hsd
        have hs2 : s ≤ 2 := by linarith [min_le_left 1 (ε / (C₁ ψ + 1))]
        have hsd' : s - 1 < ε / (C₁ ψ + 1) := lt_of_lt_of_le hsd (min_le_right _ _)
        rw [dist_eq_norm]
        have hne : C₁ ψ + 1 ≠ 0 := by linarith [hC₁ ψ hψ]
        calc ‖Lr (K := K) ψ s - g₁ ψ‖ ≤ C₁ ψ * (s - 1) := hlip ψ hψ s hs hs2
          _ ≤ (C₁ ψ + 1) * (s - 1) := by nlinarith
          _ < (C₁ ψ + 1) * (ε / (C₁ ψ + 1)) := mul_lt_mul_of_pos_left hsd' (by linarith [hC₁ ψ hψ])
          _ = ε := by field_simp
      obtain ⟨Cb, δb, hδb, hb⟩ := Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
        (hcont ψ hψ) (hexp ψ hψ) hlim (hg₁ ψ hψ)
      exact ⟨Cb, δb, hδb, fun _ => hb⟩
    · exact ⟨0, 1, one_pos, fun h => absurd h hψ⟩
  choose Cb δb hδb hbr' using hbr
  set δ₄ : ℝ := min δK (Finset.univ.inf' ⟨1, Finset.mem_univ _⟩ δb) with hδ₄
  have hδ₄pos : 0 < δ₄ := lt_min hδK ((Finset.lt_inf'_iff _).mpr fun ψ _ => hδb ψ)
  set R : ℝ := ∑ ψ ∈ Aᶜ, (Cb ψ + C₀ ψ) with hR
  have hTa : ∀ s : ℝ, 1 < s → s < 1 + δ₄ →
      A.card * (-Real.log (s - 1) - CK - nbad K m) - R ≤ φ * T K m (a : ZMod m) s := by
    intro s hs hsδ
    have hsK : s < 1 + δK := by linarith [min_le_left δK (Finset.univ.inf' ⟨1, Finset.mem_univ _⟩ δb)]
    have h1 := totient_mul_T_ge (K := K) (m := m) ha hs
    have h2 : ∑ ψ ∈ Aᶜ, ‖Pc K m ψ s‖ ≤ R := by
      rw [hR]
      refine Finset.sum_le_sum fun ψ hψc => ?_
      have hψ : ψ ∉ A := Finset.mem_compl.mp hψc
      have hsb : s < 1 + δb ψ := by
        have := Finset.inf'_le δb (Finset.mem_univ ψ)
        linarith [min_le_right δK (Finset.univ.inf' ⟨1, Finset.mem_univ _⟩ δb)]
      linarith [hPnorm_le ψ hψ s hs, hbr' ψ hψ s hs hsb]
    have h3 := hP0_ge s hs hsK
    have h5 : (A.card : ℝ) * (-Real.log (s - 1) - CK - nbad K m) ≤ A.card * P0 K m s :=
      mul_le_mul_of_nonneg_left h3 hApos.le
    rw [← hAdef, ← hφdef] at h1
    linarith
  have hTa' : ∀ s : ℝ, 1 < s → s < 1 + δ₄ →
      φ * T K m (a : ZMod m) s ≤ A.card * (-Real.log (s - 1) + CK) + R := by
    intro s hs hsδ
    have hsK : s < 1 + δK := by linarith [min_le_left δK (Finset.univ.inf' ⟨1, Finset.mem_univ _⟩ δb)]
    have h1 := totient_mul_T_le (K := K) (m := m) ha hs
    have h2 : ∑ ψ ∈ Aᶜ, ‖Pc K m ψ s‖ ≤ R := by
      rw [hR]
      refine Finset.sum_le_sum fun ψ hψc => ?_
      have hψ : ψ ∉ A := Finset.mem_compl.mp hψc
      have hsb : s < 1 + δb ψ := by
        have := Finset.inf'_le δb (Finset.mem_univ ψ)
        linarith [min_le_right δK (Finset.univ.inf' ⟨1, Finset.mem_univ _⟩ δb)]
      linarith [hPnorm_le ψ hψ s hs, hbr' ψ hψ s hs hsb]
    have h3 := hP0_le s hs hsK
    have h5 : (A.card : ℝ) * P0 K m s ≤ A.card * (-Real.log (s - 1) + CK) :=
      mul_le_mul_of_nonneg_left h3 hApos.le
    rw [← hAdef, ← hφdef] at h1
    linarith

  set X : ℝ := (A.card * (CK + nbad K m) + R) / φ with hX
  refine ⟨X, δ₄, hδ₄pos, fun s hs hsδ => ?_⟩
  have hlog : Real.log (1 / (s - 1)) = -Real.log (s - 1) := by rw [one_div, Real.log_inv]
  have hinv : (n : ℝ)⁻¹ = A.card / φ := alg_inv _ _ _ hnpos.ne' hφpos.ne' hAn
  rw [hlog, hinv, abs_le]
  have h1 := hTa s hs hsδ
  have h2 := hTa' s hs hsδ
  have hnb : (0 : ℝ) ≤ A.card * nbad K m := mul_nonneg hApos.le (Nat.cast_nonneg _)
  have hφne : (φ : ℝ) ≠ 0 := hφpos.ne'
  constructor
  ·
    have h3 : (A.card : ℝ) / φ * -Real.log (s - 1) - X ≤ T K m (a : ZMod m) s := by
      refine le_of_mul_le_mul_right ?_ hφpos
      rw [hX, alg_lower _ _ _ _ _ _ hφne, mul_comm (T K m (a : ZMod m) s) φ]
      exact h1
    linarith only [h3]
  ·
    have h3 : T K m (a : ZMod m) s ≤ (A.card : ℝ) / φ * -Real.log (s - 1) + X := by
      refine le_of_mul_le_mul_right ?_ hφpos
      rw [hX, alg_upper _ _ _ _ _ _ hφne, mul_comm (T K m (a : ZMod m) s) φ]
      linarith only [h2, hnb]
    linarith only [h3]

end Squeeze

end P2mHeckeDensity

end

open NumberField in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (τ : L ≃ₐ[K] L) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 < s → s < 1 + δ →
      |(∑' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          (if (Ideal.absNorm v.asIdeal : ZMod m) = ((hζ.autToPow K τ : (ZMod m)ˣ) : ZMod m)
            then (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) else 0)) -
        (Module.finrank K L : ℝ)⁻¹ * Real.log (1 / (s - 1))| ≤ C :=
  P2mHeckeDensity.main hζ τ

end S_NumberField_exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension
end P2MW
export P2MW.S_NumberField_exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension (solution)
