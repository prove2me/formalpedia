-- Prove2me | solution 1 for IsFractionRing.exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d0da6f76-67c3-5811-8848-c03ed758d33d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsFractionRing_exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData

set_option autoImplicit false

universe u v

namespace H3fColon

def cond {B : Type u} [CommRing B] {F : Type v} [CommRing F] [Algebra B F] (y : F) : Ideal B where
  carrier := {b | ∃ c : B, algebraMap B F b * y = algebraMap B F c}
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [map_add, add_mul, hc, hd, map_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro r a ⟨c, hc⟩
    exact ⟨r * c, by rw [smul_eq_mul, map_mul, mul_assoc, hc, map_mul]⟩

theorem exists_eq_algebraMap_of_forall_maximal {B : Type u} [CommRing B] {F : Type v} [CommRing F] [Algebra B F]
    (y : F) (h : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ b : B, b ∉ 𝔪 ∧ ∃ c : B, algebraMap B F b * y = algebraMap B F c) :
    ∃ c : B, y = algebraMap B F c := by
  have htop : (cond y : Ideal B) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨b, hb, c, hc⟩ := h 𝔪 h𝔪
    exact hb (hle ⟨c, hc⟩)
  have h1 : (1 : B) ∈ (cond y : Ideal B) := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, by rw [map_one, one_mul] at hc; exact hc⟩

end H3fColon

open H3fColon in
set_option maxHeartbeats 6400000 in
theorem solution
    {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    {F : Type v} [Field F] [Algebra B F] [IsFractionRing B F]
    {ι : Type u} [Fintype ι]
    (𝔪 : ι → Ideal B) (h𝔪 : ∀ i, (𝔪 i).IsMaximal) (hinj : Function.Injective 𝔪)
    (t : ι → B) (ht : ∀ i, t i ∈ 𝔪 i) (ht0 : ∀ i, t i ≠ 0)
    (I : ι → Ideal B)
    (hI : ∀ i (a : B), a ∈ I i ↔ ∃ s : B, s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {t i})
    (hle : ∀ i (P : Ideal B), P.IsPrime → I i ≤ P → P ≤ 𝔪 i)
    (n : ℕ) :

    (∀ (x : B) (g : F),
      (∀ 𝔭 : Ideal B, 𝔭.IsPrime → x ∉ 𝔭 → ∃ s : B, s ∉ 𝔭 ∧
        ∀ a ∈ (∏ i, I i) ^ n, ∃ b : B, g * algebraMap B F a * algebraMap B F s = algebraMap B F b) →
      ∃ k : ℕ, ∀ a ∈ (∏ i, I i) ^ n, ∃ b : B, algebraMap B F x ^ k * g * algebraMap B F a = algebraMap B F b) ∧

    (∀ e : ι → B, ∃ g : F, (∀ a ∈ (∏ i, I i) ^ (n + 1), ∃ b : B, g * algebraMap B F a = algebraMap B F b) ∧
      ∀ i, ∃ (s c : B), s ∉ 𝔪 i ∧ c ∈ I i ∧
        (g * algebraMap B F (t i) ^ (n + 1) - algebraMap B F (e i)) * algebraMap B F s = algebraMap B F c) ∧
    (∀ g : F, (∀ a ∈ (∏ i, I i) ^ (n + 1), ∃ b : B, g * algebraMap B F a = algebraMap B F b) →
      ((∀ i, ∃ (s c : B), s ∉ 𝔪 i ∧ c ∈ I i ∧ g * algebraMap B F (t i) ^ (n + 1) * algebraMap B F s = algebraMap B F c) ↔
        ∀ a ∈ (∏ i, I i) ^ n, ∃ b : B, g * algebraMap B F a = algebraMap B F b)) := by
  classical
  set φ := algebraMap B F with hφdef
  have hφinj : Function.Injective φ := IsFractionRing.injective B F
  have hφ0 : ∀ {b : B}, φ b ≠ 0 ↔ b ≠ 0 := fun {b} => map_ne_zero_iff φ hφinj
  set J : Ideal B := ∏ i, I i with hJdef

  haveI hmprime : ∀ i, (𝔪 i).IsPrime := fun i => (h𝔪 i).isPrime
  have hIne : ∀ i j, i ≠ j → ¬ I j ≤ 𝔪 i := by
    intro i j hij hle'
    exact hij (hinj ((h𝔪 i).eq_of_le (h𝔪 j).ne_top (hle j (𝔪 i) (hmprime i) hle')))
  have htI : ∀ i, t i ∈ I i := fun i => (hI i (t i)).mpr
    ⟨1, fun h => (h𝔪 i).ne_top ((Ideal.eq_top_iff_one _).mpr h), by rw [one_mul]; exact Ideal.mem_span_singleton_self _⟩
  have hJleI : ∀ i, J ≤ I i := fun i => Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))

  have hIfg : ∀ i, ∃ s : B, s ∉ 𝔪 i ∧ ∀ a ∈ I i, s * a ∈ Ideal.span {t i} := by
    intro i
    obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (I i))
    have : ∀ a ∈ G, ∃ s, s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {t i} :=
      fun a ha => (hI i a).mp (hG ▸ Ideal.subset_span ha)
    choose! sf hsf using this
    refine ⟨∏ a ∈ G, sf a, ?_, ?_⟩
    · intro hm
      obtain ⟨a, ha, hsa⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hmprime i)).mp hm
      exact (hsf a ha).1 hsa
    · intro a ha
      rw [← hG] at ha
      induction ha using Submodule.span_induction with
      | mem a ha =>
        rw [← Finset.mul_prod_erase G sf ha, mul_comm (sf a), mul_assoc]
        exact Ideal.mul_mem_left _ _ (hsf a ha).2
      | zero => rw [mul_zero]; exact Ideal.zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact Ideal.add_mem _ ha hb
      | smul r a _ ha => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ ha

  have hσ' : ∀ i, ∃ σ : B, σ ∉ 𝔪 i ∧ σ * t i ∈ J := by
    intro i
    have hy : ∀ j, j ≠ i → ∃ y, y ∈ I j ∧ y ∉ 𝔪 i := fun j hj => by
      obtain ⟨y, hy1, hy2⟩ := SetLike.not_le_iff_exists.mp (hIne i j (Ne.symm hj))
      exact ⟨y, hy1, hy2⟩
    choose! y hy using hy
    let z : ι → B := fun j => if j = i then t i else y j
    have hz : ∀ j, z j ∈ I j := fun j => by
      by_cases hj : j = i
      · subst hj; simp only [z, if_pos rfl]; exact htI _
      · simp only [z, if_neg hj]; exact (hy j hj).1
    refine ⟨∏ j ∈ Finset.univ.erase i, z j, ?_, ?_⟩
    · intro hm
      obtain ⟨j, hj, hzj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hmprime i)).mp hm
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp only [z, if_neg hji] at hzj
      exact (hy j hji).2 hzj
    · have : (∏ j ∈ Finset.univ.erase i, z j) * t i = ∏ j, z j := by
        rw [mul_comm, ← Finset.mul_prod_erase Finset.univ z (Finset.mem_univ i)]
        simp only [z, if_pos rfl]
      rw [this, hJdef]
      exact Ideal.prod_mem_prod (fun j _ => hz j)
  refine ⟨?_, ?_, ?_⟩

  · intro x g hx
    obtain ⟨G, hG⟩ := IsNoetherian.noetherian (J ^ n)
    have hgen : ∀ a ∈ G, ∃ k : ℕ, ∃ c : B, φ x ^ k * g * φ a = φ c := by
      intro a ha
      have haJ : a ∈ J ^ n := hG ▸ Ideal.subset_span ha
      have hrad : x ∈ (cond (g * φ a) : Ideal B).radical := by
        rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
        rintro P ⟨hP, hPprime⟩
        by_contra hxP
        obtain ⟨s, hs, hsa⟩ := hx P hPprime hxP
        obtain ⟨b, hb⟩ := hsa a haJ
        exact hs (hP ⟨b, by rw [← hb]; ring⟩)
      obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hrad
      obtain ⟨c, hc⟩ := hk
      exact ⟨k, c, by rw [← hc, map_pow]; ring⟩
    choose! kf cf hkc using hgen
    refine ⟨G.sup kf, ?_⟩
    intro a ha
    rw [← hG] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨d, hd⟩ : ∃ d, G.sup kf = kf a + d :=
        ⟨G.sup kf - kf a, by have := Finset.le_sup (f := kf) ha; omega⟩
      refine ⟨x ^ d * cf a, ?_⟩
      rw [hd, map_mul, map_pow, ← hkc a ha, pow_add]; ring
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by rw [map_add, mul_add, hc, hd, map_add]⟩
    | smul r a _ ha =>
      obtain ⟨c, hc⟩ := ha
      exact ⟨r * c, by rw [smul_eq_mul, map_mul, map_mul, ← hc]; ring⟩

  · intro e
    have hdat : ∀ i, ∃ s σ : B, s ∉ 𝔪 i ∧ σ ∉ 𝔪 i ∧ (∀ a ∈ I i, s * a ∈ Ideal.span {t i}) ∧ σ * t i ∈ J :=
      fun i => by
        obtain ⟨s, hs, hsI⟩ := hIfg i
        obtain ⟨σ, hσ, hσJ⟩ := hσ' i
        exact ⟨s, σ, hs, hσ, hsI, hσJ⟩
    choose s σ hs hσ hsI hσJ using hdat

    have hu : ∀ i, ∀ a ∈ J ^ (n + 1), ∃ b : B,
        (φ (s i) ^ (n + 1) * (φ (t i) ^ (n + 1))⁻¹) * φ a = φ b := by
      intro i a ha
      have h1 : Ideal.span {s i} * I i ≤ Ideal.span {t i} := Ideal.span_singleton_mul_le_iff.mpr (hsI i)
      have h2 := Ideal.pow_right_mono h1 (n + 1)
      rw [mul_pow, Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp
        (h2 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.pow_right_mono (hJleI i) _ ha)))
      refine ⟨b, ?_⟩
      have ht0' : φ (t i) ^ (n + 1) ≠ 0 := pow_ne_zero _ (hφ0.mpr (ht0 i))
      calc φ (s i) ^ (n + 1) * (φ (t i) ^ (n + 1))⁻¹ * φ a
          = (φ (s i) ^ (n + 1) * φ a) * (φ (t i) ^ (n + 1))⁻¹ := by ring
        _ = φ b := by rw [mul_inv_eq_iff_eq_mul₀ ht0', ← map_pow, ← map_mul, ← hb, map_mul, map_pow]

    have hcop : ∀ i (z : B), z ∉ 𝔪 i → ∃ w, w * z - 1 ∈ I i := by
      intro i z hz
      have htop : Ideal.span {z} ⊔ I i = ⊤ := by
        by_contra hne
        obtain ⟨M, hM, hle'⟩ := Ideal.exists_le_maximal _ hne
        have hM𝔪 : M = 𝔪 i := hM.eq_of_le (h𝔪 i).ne_top (hle i M hM.isPrime (le_sup_right.trans hle'))
        exact hz (hM𝔪 ▸ hle' (Ideal.mem_sup_left (Ideal.mem_span_singleton_self z)))
      have h1 : (1 : B) ∈ Ideal.span {z} ⊔ I i := htop ▸ Submodule.mem_top
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp h1
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      exact ⟨w, by rw [← hpq, sub_add_cancel_left]; exact (I i).neg_mem hq⟩
    have hw : ∀ i, ∃ w, w * (s i * σ i) ^ (n + 1) - 1 ∈ I i := fun i =>
      hcop i _ (fun hm => ((hmprime i).mem_or_mem ((hmprime i).mem_of_pow_mem _ hm)).elim (hs i) (hσ i))
    choose w hw using hw

    have hcoprime : Pairwise (fun i j => IsCoprime (I i) (I j)) := by
      intro i j hij
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      obtain ⟨M, hM, hle'⟩ := Ideal.exists_le_maximal _ hne
      have h1 := hM.eq_of_le (h𝔪 i).ne_top (hle i M hM.isPrime (le_sup_left.trans hle'))
      have h2 := hM.eq_of_le (h𝔪 j).ne_top (hle j M hM.isPrime (le_sup_right.trans hle'))
      exact hij (hinj (h1.symm.trans h2))
    let target : ι → B := fun j => e j * σ j ^ (n + 1) * w j
    have hc : ∀ j, ∃ c : B, c - target j ∈ I j ∧ ∀ k, k ≠ j → c ∈ I k := by
      intro j
      obtain ⟨c, hc⟩ := Ideal.exists_forall_sub_mem_ideal hcoprime (fun k => if k = j then target j else 0)
      refine ⟨c, by simpa using hc j, fun k hk => by simpa [hk] using hc k⟩
    choose c hc1 hc2 using hc
    have hβ : ∀ j i, ∃ b : B,
        (φ (s j) ^ (n + 1) * (φ (t j) ^ (n + 1))⁻¹) * φ ((σ i * t i) ^ (n + 1)) = φ b :=
      fun j i => hu j _ (Ideal.pow_mem_pow (hσJ i) _)
    choose β hβ using hβ
    refine ⟨∑ j, φ (c j) * (φ (s j) ^ (n + 1) * (φ (t j) ^ (n + 1))⁻¹), ?_, ?_⟩
    · intro a ha
      have : ∀ j, ∃ b, (φ (s j) ^ (n + 1) * (φ (t j) ^ (n + 1))⁻¹) * φ a = φ b := fun j => hu j a ha
      choose bf hbf using this
      refine ⟨∑ j, c j * bf j, ?_⟩
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_assoc, hbf, ← map_mul]
    · intro i
      refine ⟨σ i ^ (n + 1), (∑ j, c j * β j i) - e i * σ i ^ (n + 1), ?_, ?_, ?_⟩
      · exact fun hm => hσ i ((hmprime i).mem_of_pow_mem _ hm)
      · have hβii : β i i = (s i * σ i) ^ (n + 1) := by
          apply hφinj
          rw [← hβ i i]
          have ht0' : φ (t i) ^ (n + 1) ≠ 0 := pow_ne_zero _ (hφ0.mpr (ht0 i))
          rw [map_pow φ (σ i * t i), map_mul, map_pow φ (s i * σ i), map_mul]
          field_simp
          ring
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        have hrest : ∑ j ∈ Finset.univ.erase i, c j * β j i ∈ I i :=
          Ideal.sum_mem _ (fun j hj => Ideal.mul_mem_right _ _ (hc2 j i (Finset.ne_of_mem_erase hj).symm))
        have hmain : c i * β i i - e i * σ i ^ (n + 1) ∈ I i := by
          rw [hβii]
          have := (I i).add_mem (Ideal.mul_mem_right ((s i * σ i) ^ (n + 1)) _ (hc1 i))
            (Ideal.mul_mem_left _ (e i * σ i ^ (n + 1)) (hw i))
          convert this using 1
          simp only [target]; ring
        have : ∑ j ∈ Finset.univ.erase i, c j * β j i + c i * β i i - e i * σ i ^ (n + 1) =
            (∑ j ∈ Finset.univ.erase i, c j * β j i) + (c i * β i i - e i * σ i ^ (n + 1)) := by ring
        rw [this]
        exact (I i).add_mem hrest hmain
      · have key : ∀ j, φ (c j * β j i) =
            φ (c j) * (φ (s j) ^ (n + 1) * (φ (t j) ^ (n + 1))⁻¹) * (φ (σ i) * φ (t i)) ^ (n + 1) := by
          intro j
          rw [map_mul, ← hβ j i, map_pow φ (σ i * t i), map_mul]; ring
        have hsum : ∑ j, φ (c j * β j i) =
            (∑ j, φ (c j) * (φ (s j) ^ (n + 1) * (φ (t j) ^ (n + 1))⁻¹)) * (φ (σ i) * φ (t i)) ^ (n + 1) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => key j)
        rw [map_sub, map_sum, hsum, map_mul, map_pow]
        ring

  · intro g hg
    constructor
    · intro h a ha
      apply exists_eq_algebraMap_of_forall_maximal (g * φ a)
      intro 𝔪' h𝔪'
      by_cases hi : ∃ i, 𝔪' = 𝔪 i
      · obtain ⟨i, rfl⟩ := hi
        obtain ⟨s, hs, hsI⟩ := hIfg i
        obtain ⟨si, ci, hsi, hci, hgi⟩ := h i
        have ha' : s ^ n * a ∈ Ideal.span {t i ^ n} := by
          have h1 : Ideal.span {s} * I i ≤ Ideal.span {t i} := Ideal.span_singleton_mul_le_iff.mpr hsI
          have h2 := Ideal.pow_right_mono h1 n
          rw [mul_pow, Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
          exact h2 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.pow_right_mono (hJleI i) n ha))
        obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.mp ha'
        obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp (hsI ci hci)
        refine ⟨s ^ n * s * si, ?_, β * γ, ?_⟩
        · intro hm
          rcases (hmprime i).mem_or_mem hm with h' | h'
          · rcases (hmprime i).mem_or_mem h' with h'' | h''
            · exact hs ((hmprime i).mem_of_pow_mem n h'')
            · exact hs h''
          · exact hsi h'
        · have ht0' : φ (t i) ≠ 0 := hφ0.mpr (ht0 i)
          apply mul_left_cancel₀ (pow_ne_zero (n + 1) ht0')
          calc φ (t i) ^ (n + 1) * (φ (s ^ n * s * si) * (g * φ a))
              = φ s * φ (s ^ n * a) * (g * φ (t i) ^ (n + 1) * φ si) := by simp only [map_mul, map_pow]; ring
            _ = φ s * φ (β * t i ^ n) * φ ci := by rw [← hβ, hgi]
            _ = φ (β * t i ^ n) * φ (s * ci) := by rw [map_mul φ s ci]; ring
            _ = φ (β * t i ^ n) * φ (γ * t i) := by rw [← hγ]
            _ = φ (t i) ^ (n + 1) * φ (β * γ) := by simp only [map_mul, map_pow]; ring
      · push Not at hi
        have hJ𝔪 : ¬ J ≤ 𝔪' := fun hJle => by
          rw [hJdef] at hJle
          obtain ⟨j, -, hj⟩ := (h𝔪'.isPrime.prod_le).mp hJle
          exact hi j (h𝔪'.eq_of_le (h𝔪 j).ne_top (hle j 𝔪' h𝔪'.isPrime hj))
        obtain ⟨yJ, hyJ, hy𝔪⟩ := SetLike.not_le_iff_exists.mp hJ𝔪
        obtain ⟨b, hb⟩ := hg (yJ ^ (n + 1)) (Ideal.pow_mem_pow hyJ (n + 1))
        refine ⟨yJ ^ (n + 1), fun hm => hy𝔪 (h𝔪'.isPrime.mem_of_pow_mem _ hm), b * a, ?_⟩
        rw [map_mul, ← hb, map_pow]; ring
    · intro hgn i
      obtain ⟨σ, hσ, hσJ⟩ := hσ' i
      obtain ⟨b, hb⟩ := hgn ((σ * t i) ^ n) (Ideal.pow_mem_pow hσJ n)
      refine ⟨σ ^ n, b * t i, fun hm => hσ ((hmprime i).mem_of_pow_mem n hm), Ideal.mul_mem_left _ _ (htI i), ?_⟩
      rw [map_mul, ← hb, map_pow, map_pow, map_mul]; ring

end S_IsFractionRing_exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData
end P2MW
export P2MW.S_IsFractionRing_exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData (solution)
