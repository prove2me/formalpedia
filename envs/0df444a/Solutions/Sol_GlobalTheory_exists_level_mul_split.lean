-- Prove2me | solution 1 for GlobalTheory.exists_level_mul_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:52.096102+00:00
-- url     : https://prove2.me/submissions/45ccb220-d7b9-4146-a6d0-7f6519258df5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLevelMulSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
namespace SplitLevel
end SplitLevel
open NumberField Pointwise in
private theorem isCoprime_of_le_of_le {R : Type*} [CommRing R] {a b c d : Ideal R}
    (h : IsCoprime a b) (hac : a ≤ c) (hbd : b ≤ d) : IsCoprime c d := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact top_le_iff.1 (by rw [← h]; exact sup_le_sup hac hbd)
open NumberField Pointwise in
private theorem span_eq_span_inter_subalgebra {R : Type*} [CommRing R] (A : Subalgebra ℤ R)
    (S : Set R) (hS : S ⊆ A) :
    Ideal.span S = Ideal.span {a | a ∈ Ideal.span S ∧ a ∈ A} :=
  le_antisymm (Ideal.span_mono fun a ha => ⟨Ideal.subset_span ha, hS ha⟩)
    (Ideal.span_le.2 fun _ ha => ha.1)
open NumberField Pointwise in
private theorem mul_eq_span_inter_subalgebra {R : Type*} [CommRing R] (A : Subalgebra ℤ R)
    (I J : Ideal R) (hI : I = Ideal.span {a | a ∈ I ∧ a ∈ A})
    (hJ : J = Ideal.span {a | a ∈ J ∧ a ∈ A}) :
    I * J = Ideal.span {a | a ∈ I * J ∧ a ∈ A} := by
  have hsub : ({a | a ∈ I ∧ a ∈ A} * {a | a ∈ J ∧ a ∈ A} : Set R) ⊆ A := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact A.mul_mem hx.2 hy.2
  have hIJ : I * J = Ideal.span ({a | a ∈ I ∧ a ∈ A} * {a | a ∈ J ∧ a ∈ A}) := by
    rw [← Ideal.span_mul_span']
    exact congrArg₂ (· * ·) hI hJ
  rw [hIJ]
  exact span_eq_span_inter_subalgebra A _ hsub
open NumberField Pointwise in
private theorem w0_sq_sub_w0_add_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (c : ℕ) (hc : H.d + 1 = 4 * c) : H.w0 ^ 2 - H.w0 + (c : 𝓞 E) = 0 := by
  have hc' : (H.d : 𝓞 E) + 1 = 4 * c := by exact_mod_cast hc
  have h4 : (4 : 𝓞 E) * (H.w0 ^ 2 - H.w0 + c) = 0 := by
    linear_combination (2 * H.w0 + H.rt - 1) * H.two_weight_eq_one_add_root + H.rt_sq - hc'
  exact (mul_eq_zero.1 h4).resolve_left (by norm_num)
open NumberField Pointwise in
private theorem host_bar_rt_of_isCMField {E : Type} [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.bar H.rt = -H.rt := by
  have hsq : (H.bar H.rt - H.rt) * (H.bar H.rt + H.rt) = 0 := by
    have h1 : H.bar H.rt ^ 2 = -(H.d : 𝓞 E) := by
      rw [← map_pow, H.rt_sq, map_neg, map_natCast]
    linear_combination h1 - H.rt_sq
  rcases mul_eq_zero.1 hsq with h | h
  · exfalso
    have hfix : H.bar H.rt = H.rt := sub_eq_zero.1 h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hreal : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, hfix]
    obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.1 hreal
    have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have hC : (t : ℂ) ^ 2 = -(H.d : ℂ) := by
      rw [← ht, ← map_pow, hE, map_neg, map_natCast]
    have hR : t ^ 2 = -(H.d : ℝ) := by exact_mod_cast hC
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg t]
  · exact eq_neg_of_add_eq_zero_left h
open NumberField Pointwise in
private theorem host_bar_w0_of_isCMField {E : Type} [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  simp only [map_mul, map_add, map_one, map_ofNat, host_bar_rt_of_isCMField] at h
  have h2 : (2 : 𝓞 E) * H.bar H.w0 = 2 * (1 - H.w0) := by
    linear_combination h + H.two_weight_eq_one_add_root
  exact mul_left_cancel₀ two_ne_zero h2
end GlobalTheory
end

set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open NumberField Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H), (∀ (pd : ℕ) (I : Ideal (𝓞 E)), Odd pd → pd.Coprime l.M → I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {H.w0}} → I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} → I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∃ l₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.Dvd l₂ ∧ l₂.M = l.M * pd ∧ l₂.Mb = l.Mb * I ∧ l₂.A = l.A) ∧ ∀ pd : ℕ, pd.Prime → pd ≠ 2 → jacobiSym (-(H.d : ℤ)) pd = 1 → ∃ I : Ideal (𝓞 E), I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {H.w0}} ∧ I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} ∧ I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
  intro E _ _ _ H l
  refine ⟨fun pd I hodd hcop hI hprod hsup => ?_, fun pd hp hp2 hJ => ?_⟩
  · have hMp : IsCoprime (Ideal.span {((l.M : ℕ) : 𝓞 E)}) (Ideal.span {((pd : ℕ) : 𝓞 E)}) := by
      rw [Ideal.isCoprime_span_singleton_iff]
      have h := (Nat.isCoprime_iff_coprime.2 hcop.symm).map (Int.castRingHom (𝓞 E))
      simpa using h
    have hM1 : Ideal.span {((l.M : ℕ) : 𝓞 E)} ≤ l.Mb := by
      rw [← l.prod]; exact Ideal.mul_le_left
    have hM2 : Ideal.span {((l.M : ℕ) : 𝓞 E)} ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [← l.prod]; exact Ideal.mul_le_right
    have hp1 : Ideal.span {((pd : ℕ) : 𝓞 E)} ≤ I := by
      rw [← hprod]; exact Ideal.mul_le_left
    have hp2 : Ideal.span {((pd : ℕ) : 𝓞 E)} ≤ I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [← hprod]; exact Ideal.mul_le_right
    have hA : IsCoprime l.Mb (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) :=
      Ideal.isCoprime_iff_sup_eq.2 l.coprime
    have hB : IsCoprime I (I.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.isCoprime_iff_sup_eq.2 hsup
    have hC : IsCoprime l.Mb (I.map (H.bar : 𝓞 E →+* 𝓞 E)) := isCoprime_of_le_of_le hMp hM1 hp2
    have hD : IsCoprime I (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := (isCoprime_of_le_of_le hMp hM2 hp1).symm
    have hE : IsCoprime (l.Mb * I) ((l.Mb * I).map (H.bar : 𝓞 E →+* 𝓞 E)) := by
      rw [Ideal.map_mul]
      exact IsCoprime.mul_left (hA.mul_right hC) (hD.mul_right hB)
    refine ⟨⟨l.M * pd, le_trans l.three_le (Nat.le_mul_of_pos_right _ hodd.pos), l.odd.mul hodd,
      l.Mb * I, mul_eq_span_inter_subalgebra _ _ _ l.fromK hI, ?_,
      Ideal.isCoprime_iff_sup_eq.1 hE, l.A, l.A_pos⟩, ?_, rfl, rfl, rfl⟩
    · rw [Ideal.map_mul, mul_mul_mul_comm, l.prod, hprod, Ideal.span_singleton_mul_span_singleton,
        Nat.cast_mul]
    · unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.Dvd
      exact ⟨dvd_mul_right _ _, Ideal.mul_le_left, dvd_rfl⟩
  · haveI := Fact.mk hp
    obtain ⟨y, hy⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
    push_cast at hy
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * m = pd + 1 := by
      obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
      exact ⟨t + 1, by omega⟩
    have hm' : (2 : ZMod pd) * (m : ZMod pd) = 1 := by
      have := congrArg (Nat.cast : ℕ → ZMod pd) hm
      push_cast at this
      rw [this, ZMod.natCast_self, zero_add]
    set z : ZMod pd := (1 + y) * m with hz_def
    have hz : 2 * z = 1 + y := by
      rw [hz_def]; linear_combination (1 + y) * hm'
    set r : ℤ := ((z.val : ℕ) : ℤ) with hr_def
    have hrz : ((r : ℤ) : ZMod pd) = z := by simp [hr_def]
    have hdvd : (pd : ℤ) ∣ (2 * r - 1) ^ 2 + H.d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hrz]
      linear_combination (2 * z - 1 + y) * hz - hy
    obtain ⟨c, hc⟩ : ∃ c : ℕ, H.d + 1 = 4 * c := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
    have hcZ : (H.d : ℤ) + 1 = 4 * c := by exact_mod_cast hc
    have hpZ : Prime (pd : ℤ) := Nat.prime_iff_prime_int.1 hp
    have hkd : (pd : ℤ) ∣ r ^ 2 - r + c := by
      have h4 : (pd : ℤ) ∣ 4 * (r ^ 2 - r + c) := by
        have : 4 * (r ^ 2 - r + c) = (2 * r - 1) ^ 2 + H.d := by linear_combination (-1 : ℤ) * hcZ
        rw [this]; exact hdvd
      rcases hpZ.dvd_or_dvd h4 with h | h
      · exfalso
        have h' : pd ∣ 4 := by exact_mod_cast h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow (n := 2) (show pd ∣ 2 ^ 2 by simpa using h')))
      · exact h
    obtain ⟨k, hk⟩ := hkd
    have hndvd : ¬ (pd : ℤ) ∣ 2 * r - 1 := by
      intro h
      have hd : (pd : ℤ) ∣ (H.d : ℤ) := by
        have := dvd_sub hdvd (dvd_pow h two_ne_zero)
        simpa using this
      have h0 : (((-(H.d : ℤ)) : ℤ) : ZMod pd) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact (dvd_neg).2 hd
      have := (legendreSym.eq_zero_iff pd (-(H.d : ℤ))).2 h0
      rw [jacobiSym.legendreSym.to_jacobiSym, hJ] at this
      exact one_ne_zero this
    obtain ⟨u, v, huv⟩ := (hpZ.coprime_iff_not_dvd).2 hndvd
    have huv' : (u : 𝓞 E) * pd + v * (2 * r - 1) = 1 := by
      have := congrArg (fun t : ℤ => (t : 𝓞 E)) huv
      push_cast at this
      exact this
    have hk' : (r : 𝓞 E) ^ 2 - r + c = pd * k := by
      have := congrArg (fun t : ℤ => (t : 𝓞 E)) hk
      push_cast at this
      exact this
    have hw := w0_sq_sub_w0_add_eq_zero H c hc
    have hprodk : (H.w0 - r) * (1 - H.w0 - r) = (pd : 𝓞 E) * k := by
      linear_combination (-1 : 𝓞 E) * hw + hk'
    have hmap : (Ideal.span {(pd : 𝓞 E), H.w0 - (r : 𝓞 E)}).map (H.bar : 𝓞 E →+* 𝓞 E) =
        Ideal.span {(pd : 𝓞 E), 1 - H.w0 - (r : 𝓞 E)} := by
      rw [Ideal.map_span, Set.image_pair]
      simp [host_bar_w0_of_isCMField]
    refine ⟨Ideal.span {(pd : 𝓞 E), H.w0 - (r : 𝓞 E)}, ?_, ?_, ?_⟩
    · refine span_eq_span_inter_subalgebra _ _ (Set.insert_subset_iff.2
        ⟨Subalgebra.natCast_mem _ _, Set.singleton_subset_iff.2 (Subalgebra.sub_mem _
          (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _))⟩)
    · rw [hmap]
      apply le_antisymm
      · rw [Ideal.span_mul_span', Ideal.span_le]
        rintro _ ⟨x, hx, w, hw', rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hw'
        rw [SetLike.mem_coe, Ideal.mem_span_singleton]
        rcases hx with rfl | rfl <;> rcases hw' with rfl | rfl
        · exact dvd_mul_right _ _
        · exact dvd_mul_right _ _
        · exact dvd_mul_left _ _
        · exact ⟨k, hprodk⟩
      · rw [Ideal.span_singleton_le_iff_mem]
        have hp_mem : (pd : 𝓞 E) ∈ Ideal.span {(pd : 𝓞 E), H.w0 - (r : 𝓞 E)} :=
          Ideal.subset_span (Set.mem_insert _ _)
        have hq_mem : H.w0 - (r : 𝓞 E) ∈ Ideal.span {(pd : 𝓞 E), H.w0 - (r : 𝓞 E)} :=
          Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
        have hp_mem' : (pd : 𝓞 E) ∈ Ideal.span {(pd : 𝓞 E), 1 - H.w0 - (r : 𝓞 E)} :=
          Ideal.subset_span (Set.mem_insert _ _)
        have hq_mem' : 1 - H.w0 - (r : 𝓞 E) ∈ Ideal.span {(pd : 𝓞 E), 1 - H.w0 - (r : 𝓞 E)} :=
          Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
        have heq : (pd : 𝓞 E) = u * (pd * pd) - v * (pd * (1 - H.w0 - r)) - v * ((H.w0 - r) * pd) := by
          linear_combination (-(pd : 𝓞 E)) * huv'
        have key := Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_left _ (u : 𝓞 E)
          (Ideal.mul_mem_mul hp_mem hp_mem'))
          (Ideal.mul_mem_left _ (v : 𝓞 E) (Ideal.mul_mem_mul hp_mem hq_mem')))
          (Ideal.mul_mem_left _ (v : 𝓞 E) (Ideal.mul_mem_mul hq_mem hp_mem'))
        rw [← heq] at key
        exact key
    · rw [hmap, Ideal.eq_top_iff_one]
      have heq : (1 : 𝓞 E) = u * pd - v * (H.w0 - r) - v * (1 - H.w0 - r) := by
        linear_combination (-1 : 𝓞 E) * huv'
      have key : (u : 𝓞 E) * pd - v * (H.w0 - r) - v * (1 - H.w0 - r) ∈
          Ideal.span {(pd : 𝓞 E), H.w0 - (r : 𝓞 E)} ⊔
            Ideal.span {(pd : 𝓞 E), 1 - H.w0 - (r : 𝓞 E)} :=
        Ideal.sub_mem _ (Ideal.sub_mem _
          (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))))
          (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left
            (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))))
          (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right
            (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))))
      rw [← heq] at key
      exact key
end _root_.GlobalTheory
end GlobalTheory
