-- Prove2me | solution 1 for KellyStochasticNetworks.RandomAccessCapacity.nonvertical_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:03:26.210911+00:00
-- url     : https://prove2.me/submissions/8f988cfd-021f-4616-927e-63bd17c96ffd

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Optimization

open Filter Topology Set

/-- points `b + s • v` lie in any neighbourhood of `b` for small `s ∈ (0,1)`. -/
theorem g80k_small {m : ℕ} (b v : Fin m → ℝ) {U : Set (Fin m → ℝ)} (hU : U ∈ 𝓝 b) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ b + s • v ∈ U := by
  have ht : Tendsto (fun s : ℝ => b + s • v) (𝓝[>] (0:ℝ)) (𝓝 b) := by
    have : Tendsto (fun s : ℝ => b + s • v) (𝓝 (0:ℝ)) (𝓝 (b + (0:ℝ) • v)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto _
    simpa using this.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ s in 𝓝[>] (0:ℝ), b + s • v ∈ U := ht hU
  have h2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s := self_mem_nhdsWithin
  have h3 : ∀ᶠ s in 𝓝[>] (0:ℝ), s < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
  obtain ⟨s, hs1, hs2, hs3⟩ := (h1.and (h2.and h3)).exists
  exact ⟨s, hs2, hs3, hs1⟩

theorem g80k_epi {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hconv : Convex ℝ {p : (Fin m → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)})
    {p q : Fin m → ℝ} {t u : ℝ} (hp : φ p ≤ (t : EReal)) (hq : φ q ≤ (u : EReal))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    φ (α • p + β • q) ≤ ((α * t + β * u : ℝ) : EReal) := by
  have := hconv (show (p, t) ∈ {p : (Fin m → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} from hp)
    (show (q, u) ∈ {p : (Fin m → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} from hq) hα hβ hαβ
  simpa [Prod.smul_mk] using this

theorem g80k_nobot {m : ℕ} (φ : (Fin m → ℝ) → EReal)
    (hconv : Convex ℝ {p : (Fin m → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)})
    (b : Fin m → ℝ)
    (hb : b ∈ interior {c | ∃ a : ℝ, φ c = (a : EReal)}) (c : Fin m → ℝ) : φ c ≠ ⊥ := by
  intro hc
  obtain ⟨δ, hδ, -, hδU⟩ := g80k_small b (b - c) (mem_interior_iff_mem_nhds.mp hb)
  obtain ⟨a', ha'⟩ := interior_subset hb
  obtain ⟨a, ha⟩ := (show b + δ • (b - c) ∈ {c | ∃ a : ℝ, φ c = (a : EReal)} from hδU)
  set t : ℝ := ((a' - 1) * (1 + δ) - a) / δ with ht
  have h1 : φ (b + δ • (b - c)) ≤ (a : EReal) := ha.le
  have h2 : φ c ≤ (t : EReal) := by rw [hc]; exact bot_le
  have hpos : 0 < 1 + δ := by linarith
  have h3 := g80k_epi hconv h1 h2 (α := 1 / (1 + δ)) (β := δ / (1 + δ)) (by positivity)
    (by positivity) (by field_simp)
  have heq : (1 / (1 + δ)) • (b + δ • (b - c)) + (δ / (1 + δ)) • c = b := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp; ring
  rw [heq, ha'] at h3
  have h4 := EReal.coe_le_coe_iff.mp h3
  have h5 : 1 / (1 + δ) * a + δ / (1 + δ) * t = a' - 1 := by
    rw [ht]; field_simp; ring
  linarith

theorem solution {m : ℕ} (φ : (Fin m → ℝ) → EReal)
    (hconv : Convex ℝ {p : (Fin m → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)})
    (b : Fin m → ℝ)
    (hb : b ∈ interior {c | ∃ a : ℝ, φ c = (a : EReal)}) :
    ∃ a : ℝ, ∃ y : Fin m → ℝ, φ b = (a : EReal) ∧
      ∀ c, ((a + ∑ i, y i * (c i - b i) : ℝ) : EReal) ≤ φ c := by
  have hnb := g80k_nobot φ hconv b hb
  set f : (Fin m → ℝ) → ℝ := fun c => (φ c).toReal with hf
  set D : Set (Fin m → ℝ) := {c | ∃ a : ℝ, φ c = (a : EReal)} with hD
  have hDf : ∀ c ∈ D, φ c = (f c : EReal) := by
    rintro c ⟨a, ha⟩; simp [hf, ha]
  have hDconv : Convex ℝ D := by
    intro p hp q hq α β hα hβ hαβ
    have h := g80k_epi hconv (hDf p hp).le (hDf q hq).le hα hβ hαβ
    refine ⟨(φ (α • p + β • q)).toReal, (EReal.coe_toReal ?_ (hnb _)).symm⟩
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h
  have hfconv : ConvexOn ℝ D f := by
    refine ⟨hDconv, fun p hp q hq α β hα hβ hαβ => ?_⟩
    have h := g80k_epi hconv (hDf p hp).le (hDf q hq).le hα hβ hαβ
    rw [hDf _ (hDconv hp hq hα hβ hαβ)] at h
    simpa [smul_eq_mul] using EReal.coe_le_coe_iff.mp h
  set U := interior D with hU
  have hUo : IsOpen U := isOpen_interior
  have hUconv : Convex ℝ U := hDconv.interior
  have hfc : ContinuousOn f U := hfconv.continuousOn_interior
  have hUD : U ⊆ D := interior_subset
  -- the open strict epigraph over U
  set S : Set ((Fin m → ℝ) × ℝ) := {z | z.1 ∈ U ∧ f z.1 < z.2} with hS
  have hSo : IsOpen S := by
    have h1 : IsOpen (U ×ˢ (univ : Set ℝ)) := hUo.prod isOpen_univ
    have h2 : ContinuousOn (fun z : (Fin m → ℝ) × ℝ => z.2 - f z.1) (U ×ˢ (univ : Set ℝ)) := by
      refine continuousOn_snd.sub (hfc.comp continuousOn_fst ?_)
      intro z hz; exact hz.1
    have h3 := h2.isOpen_inter_preimage h1 (isOpen_Ioi (a := (0:ℝ)))
    convert h3 using 1
    ext z; simp [hS, sub_pos]
  have hSconv : Convex ℝ S := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩ ⟨q, u⟩ ⟨hq, hu⟩ α β hα hβ hαβ
    refine ⟨hUconv hp hq hα hβ hαβ, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    have := hfconv.2 (hUD hp) (hUD hq) hα hβ hαβ
    simp only [smul_eq_mul] at this
    rcases hα.lt_or_eq with hα' | hα'
    · nlinarith [mul_lt_mul_of_pos_left ht hα', mul_le_mul_of_nonneg_left hu.le hβ]
    · subst hα'
      have hβ1 : β = 1 := by linarith
      subst hβ1
      simp only [zero_smul, zero_add, one_smul, zero_mul, one_mul] at this ⊢
      linarith
  have hbU : b ∈ U := hb
  have hxS : (b, f b) ∉ S := fun h => lt_irrefl _ h.2
  obtain ⟨F, hF⟩ := geometric_hahn_banach_open_point hSconv hSo hxS
  set lam : ℝ := F (0, 1) with hlam
  have hsplit : ∀ p : Fin m → ℝ, ∀ t : ℝ, F (p, t) = F (p, 0) + t * lam := by
    intro p t
    have : ((p, t) : (Fin m → ℝ) × ℝ) = (p, 0) + t • ((0 : Fin m → ℝ), (1 : ℝ)) := by
      simp [Prod.smul_mk]
    rw [this, map_add, map_smul, smul_eq_mul]
  have hlneg : lam < 0 := by
    have h := hF (b, f b + 1) ⟨hbU, by linarith⟩
    rw [hsplit, hsplit b (f b)] at h
    nlinarith
  set y : Fin m → ℝ := fun i => F (Pi.single i 1, 0) / (-lam) with hy
  have hlin : ∀ v : Fin m → ℝ, F (v, 0) = ∑ i, v i * F (Pi.single i 1, 0) := by
    intro v
    have hv : ((v, 0) : (Fin m → ℝ) × ℝ) = ∑ i, v i • ((Pi.single i 1 : Fin m → ℝ), (0:ℝ)) := by
      ext j
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [hv, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
  -- subgradient inequality on U
  have hsubU : ∀ p ∈ U, f b + ∑ i, y i * (p i - b i) ≤ f p := by
    intro p hp
    have hsum : ∑ i, y i * (p i - b i) = (F (p, 0) - F (b, 0)) / (-lam) := by
      have h1 : F (p, 0) - F (b, 0) = F (p - b, 0) := by
        rw [← map_sub]; simp
      rw [h1, hlin, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hy]; simp only [Pi.sub_apply]; ring
    rw [hsum]
    by_contra hc
    push_neg at hc
    set A := f b + (F (p, 0) - F (b, 0)) / -lam
    have h := hF (p, (A + f p) / 2) ⟨hp, by linarith⟩
    rw [hsplit, hsplit b (f b)] at h
    have hA : A * (-lam) = f b * (-lam) + (F (p, 0) - F (b, 0)) := by
      simp only [A]; field_simp [hlneg.ne]; ring
    nlinarith
  refine ⟨f b, y, hDf b (interior_subset hb), fun c => ?_⟩
  -- key: for every real t with φ c ≤ t, f b + y·(c - b) ≤ t
  have key : ∀ t : ℝ, φ c ≤ (t : EReal) → f b + ∑ i, y i * (c i - b i) ≤ t := by
    intro t ht
    obtain ⟨s, hs0, hs1, hsU⟩ := g80k_small b (c - b) (hUo.mem_nhds hbU)
    have hcomb : (1 - s) • b + s • c = b + s • (c - b) := by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have h1 := g80k_epi hconv (hDf b (interior_subset hb)).le ht (α := 1 - s) (β := s)
      (by linarith) hs0.le (by ring)
    rw [hcomb, hDf _ (hUD hsU)] at h1
    have h2 := EReal.coe_le_coe_iff.mp h1
    have h3 := hsubU _ hsU
    have h4 : ∑ i, y i * ((b + s • (c - b)) i - b i) = s * ∑ i, y i * (c i - b i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [h4] at h3
    have h5 : s * (f b + ∑ i, y i * (c i - b i)) ≤ s * t := by nlinarith
    exact le_of_mul_le_mul_left h5 hs0
  induction hφ : φ c with
  | bot => exact absurd hφ (hnb c)
  | top => exact le_top
  | coe r =>
    exact EReal.coe_le_coe_iff.mpr (key r hφ.le)
