-- Prove2me | solution 1 for NumInvQH.Oblique.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:30:39.211903+00:00
-- url     : https://prove2.me/submissions/d7e39e82-58cc-42b1-87cb-304e7dc14ba1

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace Sol43

variable {d : ℕ}

lemma ext_mv {A B : Matrix (Fin d) (Fin d) ℝ} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
  have : Matrix.toLin' A = Matrix.toLin' B := LinearMap.ext fun x => by simpa using h x
  exact Matrix.toLin'.injective this

lemma sym_psd {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) : Cᵀ = C := by
  have h := hC.isHermitian.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at h

lemma psd_nonneg {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) (w : Fin d → ℝ) :
    0 ≤ w ⬝ᵥ (C *ᵥ w) := by simpa using hC.dotProduct_mulVec_nonneg w

lemma psd_zero {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) (w : Fin d → ℝ)
    (h : w ⬝ᵥ (C *ᵥ w) = 0) : C *ᵥ w = 0 :=
  (hC.dotProduct_mulVec_zero_iff w).1 (by simpa using h)

lemma dot_sym {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (x y : Fin d → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA]

lemma mp_unique {M P Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : LocalDistanceNetwork.IsMoorePenroseInverse M P)
    (hQ : LocalDistanceNetwork.IsMoorePenroseInverse M Q) : P = Q := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  obtain ⟨k1, k2, k3, k4⟩ := hQ
  have e1 : P = P * M * Q := by
    calc P = P * M * P := h2.symm
     _ = P * (M * P)ᵀ := by rw [h3, Matrix.mul_assoc]
     _ = P * Pᵀ * Mᵀ := by rw [transpose_mul, Matrix.mul_assoc]
     _ = P * Pᵀ * (M * Q * M)ᵀ := by rw [k1]
     _ = P * (M * P)ᵀ * (M * Q)ᵀ := by simp only [transpose_mul, Matrix.mul_assoc]
     _ = P * (M * P) * (M * Q) := by rw [h3, k3]
     _ = (P * M * P) * M * Q := by simp only [Matrix.mul_assoc]
     _ = P * M * Q := by rw [h2]
  have e2 : Q = P * M * Q := by
    calc Q = Q * M * Q := k2.symm
     _ = (Q * M)ᵀ * Q := by rw [k4]
     _ = Mᵀ * Qᵀ * Q := by rw [transpose_mul]
     _ = (M * P * M)ᵀ * Qᵀ * Q := by rw [h1]
     _ = (P * M)ᵀ * (Q * M)ᵀ * Q := by simp only [transpose_mul, Matrix.mul_assoc]
     _ = (P * M) * (Q * M) * Q := by rw [h4, k4]
     _ = P * M * (Q * M * Q) := by simp only [Matrix.mul_assoc]
     _ = P * M * Q := by rw [k2]
  exact e1.trans e2.symm

lemma mp_sym {M P : Matrix (Fin d) (Fin d) ℝ} (hM : Mᵀ = M)
    (hP : LocalDistanceNetwork.IsMoorePenroseInverse M P) : Pᵀ = P := by
  refine mp_unique ?_ hP
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg transpose h1
    simpa [transpose_mul, hM, Matrix.mul_assoc] using this
  · have := congrArg transpose h2
    simpa [transpose_mul, hM, Matrix.mul_assoc] using this
  · rw [transpose_mul, transpose_transpose, hM, ← h4, transpose_mul, hM]
  · rw [transpose_mul, transpose_transpose, hM, ← h3, transpose_mul, hM]

lemma m_mulVec (s x : Fin d → ℝ) :
    (1 - (s ⬝ᵥ s)⁻¹ • vecMulVec s s) *ᵥ x = x - ((s ⬝ᵥ s)⁻¹ * (s ⬝ᵥ x)) • s := by
  rw [sub_mulVec, one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec]
  simp [smul_smul]

open NumInvQH.Oblique

lemma q_add {C : Matrix (Fin d) (Fin d) ℝ} (hCs : Cᵀ = C) (F x z : Fin d → ℝ) :
    quadraticForm C F (x + z) =
      quadraticForm C F x + 2 * (z ⬝ᵥ (C *ᵥ x - F)) + z ⬝ᵥ (C *ᵥ z) := by
  unfold quadraticForm
  have h := dot_sym hCs x z
  simp only [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_sub]
  rw [h, dotProduct_comm (C *ᵥ x) z]
  ring

lemma mem_hyper_iff {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) {s : Fin d → ℝ}
    (hs : s ≠ 0) (F x : Fin d → ℝ) (c : ℝ) :
    x ∈ hyperArgmin C F s c ↔ x ⬝ᵥ s = c ∧ ∃ l : ℝ, C *ᵥ x - F = l • s := by
  have hCs := sym_psd hC
  have hσ : s ⬝ᵥ s ≠ 0 := fun h => hs (dotProduct_self_eq_zero.1 h)
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    set g := C *ᵥ x - F with hg
    set l := (s ⬝ᵥ s)⁻¹ * (s ⬝ᵥ g) with hl
    set z := g - l • s with hz
    have hzs : z ⬝ᵥ s = 0 := by
      rw [hz, sub_dotProduct, smul_dotProduct, smul_eq_mul, hl, dotProduct_comm g s]
      field_simp
      ring
    have hzg : z ⬝ᵥ g = z ⬝ᵥ z := by
      have : g = z + l • s := by rw [hz]; abel
      conv_lhs => rw [this]
      rw [dotProduct_add, dotProduct_smul, hzs, smul_zero, add_zero]
    have key : ∀ t : ℝ, 0 ≤ 2 * t * (z ⬝ᵥ z) + t ^ 2 * (z ⬝ᵥ (C *ᵥ z)) := by
      intro t
      have h1 := hmin (x + t • z) (by rw [add_dotProduct, smul_dotProduct, hzs, hx]; simp)
      rw [q_add hCs] at h1
      rw [← hg] at h1
      simp only [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, hzg] at h1
      nlinarith
    set A := z ⬝ᵥ z
    set k := z ⬝ᵥ (C *ᵥ z)
    have hk : 0 ≤ k := psd_nonneg hC z
    have hA : 0 ≤ A := dotProduct_self_star_nonneg z |>.trans_eq (by simp [A])
    have hk1 : 0 < k + 1 := by linarith
    set u := A / (k + 1) with hu
    have hAu : A = u * (k + 1) := by rw [hu]; field_simp
    have ht := key (-u)
    rw [hAu] at ht
    have hu2 : u ^ 2 * (k + 2) ≤ 0 := by nlinarith
    have hu0 : u = 0 := by
      have : u ^ 2 ≤ 0 := by
        by_contra hcon
        have hcon := lt_of_not_ge hcon
        have : 0 < u ^ 2 * (k + 2) := mul_pos hcon (by linarith)
        linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg u))
    have hA0 : A = 0 := by rw [hAu, hu0, zero_mul]
    have hz0 : z = 0 := dotProduct_self_eq_zero.1 hA0
    refine ⟨l, ?_⟩
    rw [hz, sub_eq_zero] at hz0
    exact hz0
  · rintro ⟨hx, l, hl⟩
    refine ⟨hx, fun y hy => ?_⟩
    have h1 := q_add hCs F x (y - x)
    rw [add_sub_cancel] at h1
    rw [h1]
    have h2 : (y - x) ⬝ᵥ (C *ᵥ x - F) = 0 := by
      rw [hl, dotProduct_smul, sub_dotProduct, hy, hx, sub_self, smul_zero]
    have h3 := psd_nonneg hC (y - x)
    linarith

/-- the kernel set `N(C) ∩ N(sᵀ)` -/
def Kset (C : Matrix (Fin d) (Fin d) ℝ) (s : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {z | C *ᵥ z = 0 ∧ s ⬝ᵥ z = 0}

lemma hyper_eq {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) {s : Fin d → ℝ}
    (hs : s ≠ 0) {F x : Fin d → ℝ} {c : ℝ} (hx : x ∈ hyperArgmin C F s c) :
    hyperArgmin C F s c = {y | ∃ z : Fin d → ℝ, C *ᵥ z = 0 ∧ s ⬝ᵥ z = 0 ∧ y = x + z} := by
  rw [mem_hyper_iff hC hs] at hx
  obtain ⟨hxs, l, hl⟩ := hx
  ext y
  rw [mem_hyper_iff hC hs]
  constructor
  · rintro ⟨hys, l', hl'⟩
    have hCz : C *ᵥ (y - x) = (l' - l) • s := by
      rw [mulVec_sub, sub_smul, ← hl, ← hl']; abel
    have hsz : s ⬝ᵥ (y - x) = 0 := by
      rw [dotProduct_comm, sub_dotProduct, hys, hxs, sub_self]
    refine ⟨y - x, ?_, hsz, by abel⟩
    apply psd_zero hC
    rw [hCz, dotProduct_smul, dotProduct_comm, hsz, smul_zero]
  · rintro ⟨z, hz, hsz, rfl⟩
    refine ⟨?_, l, ?_⟩
    · rw [add_dotProduct, hxs, dotProduct_comm, hsz, add_zero]
    · rw [mulVec_add, hz, add_zero, hl]

lemma minnorm_of {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) {s : Fin d → ℝ}
    (hs : s ≠ 0) {F x : Fin d → ℝ} {c : ℝ} (hx : x ∈ hyperArgmin C F s c)
    (hperp : ∀ z, C *ᵥ z = 0 → s ⬝ᵥ z = 0 → x ⬝ᵥ z = 0) :
    IsMinNorm (hyperArgmin C F s c) x := by
  refine ⟨hx, fun y hy => ?_⟩
  rw [hyper_eq hC hs hx] at hy
  obtain ⟨z, hz, hsz, rfl⟩ := hy
  have := hperp z hz hsz
  have h2 : 0 ≤ z ⬝ᵥ z := dotProduct_self_star_nonneg z |>.trans_eq (by simp)
  rw [add_dotProduct, dotProduct_add, dotProduct_add, this, dotProduct_comm z x, this]
  linarith

lemma uniq_of {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) {s : Fin d → ℝ}
    (hs : s ≠ 0) {F x y : Fin d → ℝ} {c : ℝ} (hx : x ∈ hyperArgmin C F s c)
    (hy : y ∈ hyperArgmin C F s c)
    (hxp : ∀ z, C *ᵥ z = 0 → s ⬝ᵥ z = 0 → x ⬝ᵥ z = 0)
    (hyp : ∀ z, C *ᵥ z = 0 → s ⬝ᵥ z = 0 → y ⬝ᵥ z = 0) : x = y := by
  rw [hyper_eq hC hs hx] at hy
  obtain ⟨z, hz, hsz, rfl⟩ := hy
  have h1 := hxp z hz hsz
  have h2 := hyp z hz hsz
  rw [add_dotProduct, h1, zero_add] at h2
  rw [dotProduct_self_eq_zero.1 h2, add_zero]

lemma m_facts {s : Fin d → ℝ} (hs : s ≠ 0) :
    (1 - (s ⬝ᵥ s)⁻¹ • vecMulVec s s)ᵀ = 1 - (s ⬝ᵥ s)⁻¹ • vecMulVec s s ∧
    (1 - (s ⬝ᵥ s)⁻¹ • vecMulVec s s) * (1 - (s ⬝ᵥ s)⁻¹ • vecMulVec s s) =
      1 - (s ⬝ᵥ s)⁻¹ • vecMulVec s s ∧
    (1 - (s ⬝ᵥ s)⁻¹ • vecMulVec s s) *ᵥ s = 0 ∧
    (∀ z, s ⬝ᵥ z = 0 → (1 - (s ⬝ᵥ s)⁻¹ • vecMulVec s s) *ᵥ z = z) ∧
    (∀ v, (1 - (s ⬝ᵥ s)⁻¹ • vecMulVec s s) *ᵥ v = 0 → v = ((s ⬝ᵥ s)⁻¹ * (s ⬝ᵥ v)) • s) := by
  have hσ : s ⬝ᵥ s ≠ 0 := fun h => hs (dotProduct_self_eq_zero.1 h)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [transpose_sub, transpose_smul, transpose_vecMulVec]
  · apply ext_mv
    intro x
    rw [← mulVec_mulVec, m_mulVec, m_mulVec]
    have : s ⬝ᵥ (x - ((s ⬝ᵥ s)⁻¹ * (s ⬝ᵥ x)) • s) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      field_simp
      ring
    rw [this, mul_zero, zero_smul, sub_zero]
  · rw [m_mulVec, inv_mul_cancel₀ hσ, one_smul, sub_self]
  · intro z hz
    rw [m_mulVec, hz, mul_zero, zero_smul, sub_zero]
  · intro v hv
    rw [m_mulVec, sub_eq_zero] at hv
    exact hv

section PFacts

variable {C m p : Matrix (Fin d) (Fin d) ℝ} {s : Fin d → ℝ}

lemma p_facts (hCs : Cᵀ = C) (hmT : mᵀ = m) (hmm : m * m = m)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p) :
    pᵀ = p ∧ m * C * m * p = p * (m * C * m) ∧ p * m = p ∧ m * p = p := by
  have hMT : (m * C * m)ᵀ = m * C * m := by
    simp only [transpose_mul, hmT, hCs, Matrix.mul_assoc]
  have hpT := mp_sym hMT hp
  have hMp : m * C * m * p = p * (m * C * m) := by
    have := hp.2.2.1
    rw [transpose_mul, hMT, hpT] at this
    exact this.symm
  have hpp : p = p * p * (m * C * m) := by
    calc p = p * (m * C * m) * p := hp.2.1.symm
      _ = p * (m * C * m * p) := by rw [Matrix.mul_assoc]
      _ = p * p * (m * C * m) := by rw [hMp]; simp only [Matrix.mul_assoc]
  have hpm : p * m = p := by
    calc p * m = p * p * (m * C * m) * m := by rw [← hpp]
      _ = p * p * (m * C * (m * m)) := by simp only [Matrix.mul_assoc]
      _ = p := by rw [hmm, ← hpp]
  have hmp : m * p = p := by
    have := congrArg transpose hpm
    rwa [transpose_mul, hmT, hpT] at this
  exact ⟨hpT, hMp, hpm, hmp⟩

lemma p_key (hC : C.PosSemidef) (hmT : mᵀ = m) (hmm : m * m = m)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p) :
    m * C * m * p * C = m * C := by
  have hCs := sym_psd hC
  obtain ⟨hpT, hMp, hpm, hmp⟩ := p_facts hCs hmT hmm hp
  set M := m * C * m with hMdef
  set Q : Matrix (Fin d) (Fin d) ℝ := 1 - M * p with hQ
  have hQT : Qᵀ = Q := by
    rw [hQ, transpose_sub, transpose_one, hp.2.2.1]
  have hQM : Q * M = 0 := by rw [hQ, sub_mul, one_mul, hp.1, sub_self]
  have hCmQ : C * m * Q = 0 := by
    apply ext_mv
    intro x
    rw [zero_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    apply psd_zero hC
    calc (m *ᵥ (Q *ᵥ x)) ⬝ᵥ (C *ᵥ (m *ᵥ (Q *ᵥ x)))
        = (Q *ᵥ x) ⬝ᵥ (m *ᵥ (C *ᵥ (m *ᵥ (Q *ᵥ x)))) := (dot_sym hmT _ _).symm
      _ = x ⬝ᵥ (Q *ᵥ (m *ᵥ (C *ᵥ (m *ᵥ (Q *ᵥ x))))) := (dot_sym hQT _ _).symm
      _ = x ⬝ᵥ ((Q * M * Q) *ᵥ x) := by simp only [mulVec_mulVec, hMdef, Matrix.mul_assoc]
      _ = 0 := by rw [hQM, zero_mul, zero_mulVec, dotProduct_zero]
  have h1 : Q * (m * C) = 0 := by
    have := congrArg transpose hCmQ
    rwa [transpose_mul, transpose_mul, hQT, hmT, hCs, transpose_zero] at this
  rw [hQ, sub_mul, one_mul, sub_eq_zero] at h1
  calc M * p * C = M * (p * m) * C := by rw [hpm]
    _ = M * p * (m * C) := by simp only [Matrix.mul_assoc]
    _ = m * C := h1.symm

end PFacts

/-- the candidate `x̂ = pF + (c/sᵀs)(I - pC)s` -/
noncomputable def xhat (C p : Matrix (Fin d) (Fin d) ℝ) (s F : Fin d → ℝ) (c : ℝ) : Fin d → ℝ :=
  p *ᵥ F + (c * (s ⬝ᵥ s)⁻¹) • ((1 - p * C) *ᵥ s)

section XFacts

variable {C m p : Matrix (Fin d) (Fin d) ℝ} {s : Fin d → ℝ}

lemma pz_zero (hCs : Cᵀ = C) (hmT : mᵀ = m) (hmm : m * m = m)
    (hmz : ∀ z, s ⬝ᵥ z = 0 → m *ᵥ z = z)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p)
    (z : Fin d → ℝ) (hz : C *ᵥ z = 0) (hsz : s ⬝ᵥ z = 0) : p *ᵥ z = 0 := by
  obtain ⟨hpT, hMp, hpm, hmp⟩ := p_facts hCs hmT hmm hp
  have hpp : p = p * p * (m * C * m) := by
    calc p = p * (m * C * m) * p := hp.2.1.symm
      _ = p * (m * C * m * p) := by rw [Matrix.mul_assoc]
      _ = p * p * (m * C * m) := by rw [hMp]; simp only [Matrix.mul_assoc]
  have hMz : (m * C * m) *ᵥ z = 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hmz z hsz, hz, mulVec_zero]
  rw [hpp, ← mulVec_mulVec, hMz, mulVec_zero]

lemma ps_zero (hCs : Cᵀ = C) (hmT : mᵀ = m) (hmm : m * m = m) (hms : m *ᵥ s = 0)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p) : p *ᵥ s = 0 := by
  obtain ⟨hpT, hMp, hpm, hmp⟩ := p_facts hCs hmT hmm hp
  rw [← hpm, ← mulVec_mulVec, hms, mulVec_zero]

lemma xhat_s (hCs : Cᵀ = C) (hmT : mᵀ = m) (hmm : m * m = m) (hms : m *ᵥ s = 0)
    (hσ : s ⬝ᵥ s ≠ 0)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p) (F : Fin d → ℝ) (c : ℝ) :
    xhat C p s F c ⬝ᵥ s = c := by
  obtain ⟨hpT, hMp, hpm, hmp⟩ := p_facts hCs hmT hmm hp
  have hps := ps_zero hCs hmT hmm hms hp
  unfold xhat
  rw [add_dotProduct, smul_dotProduct, ← dot_sym hpT F s, hps, dotProduct_zero,
    sub_mulVec, one_mulVec, sub_dotProduct, ← mulVec_mulVec, ← dot_sym hpT (C *ᵥ s) s, hps,
    dotProduct_zero, sub_zero, smul_eq_mul]
  field_simp
  ring

lemma xhat_perp (hCs : Cᵀ = C) (hmT : mᵀ = m) (hmm : m * m = m)
    (hmz : ∀ z, s ⬝ᵥ z = 0 → m *ᵥ z = z)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p) (F : Fin d → ℝ) (c : ℝ)
    (z : Fin d → ℝ) (hz : C *ᵥ z = 0) (hsz : s ⬝ᵥ z = 0) : xhat C p s F c ⬝ᵥ z = 0 := by
  obtain ⟨hpT, hMp, hpm, hmp⟩ := p_facts hCs hmT hmm hp
  have hpz := pz_zero hCs hmT hmm hmz hp z hz hsz
  unfold xhat
  rw [add_dotProduct, smul_dotProduct, ← dot_sym hpT F z, hpz, dotProduct_zero,
    sub_mulVec, one_mulVec, sub_dotProduct, ← mulVec_mulVec, ← dot_sym hpT (C *ᵥ s) z, hpz,
    dotProduct_zero, sub_zero, hsz, smul_zero, add_zero]

lemma xhat_shift (hCs : Cᵀ = C) (hmT : mᵀ = m) (hmm : m * m = m)
    (hmz : ∀ z, s ⬝ᵥ z = 0 → m *ᵥ z = z)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p) (F : Fin d → ℝ) (c : ℝ)
    (z : Fin d → ℝ) (hz : C *ᵥ z = 0) (hsz : s ⬝ᵥ z = 0) :
    xhat C p s (F + z) c = xhat C p s F c := by
  have hpz := pz_zero hCs hmT hmm hmz hp z hz hsz
  unfold xhat
  rw [mulVec_add, hpz, add_zero]

lemma xhat_mem (hC : C.PosSemidef) (hs : s ≠ 0) (hmT : mᵀ = m) (hmm : m * m = m)
    (hms : m *ᵥ s = 0)
    (hmv : ∀ v, m *ᵥ v = 0 → v = ((s ⬝ᵥ s)⁻¹ * (s ⬝ᵥ v)) • s)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p) (w : Fin d → ℝ) (μ c : ℝ) :
    xhat C p s (C *ᵥ w + μ • s) c ∈ hyperArgmin C (C *ᵥ w + μ • s) s c := by
  have hCs := sym_psd hC
  have hσ : s ⬝ᵥ s ≠ 0 := fun h => hs (dotProduct_self_eq_zero.1 h)
  obtain ⟨hpT, hMp, hpm, hmp⟩ := p_facts hCs hmT hmm hp
  have hps := ps_zero hCs hmT hmm hms hp
  have key := p_key hC hmT hmm hp
  have e1 : m * (C * (p * C)) = m * C := by
    have h : m * C * m * p * C = m * (C * (p * C)) := by
      rw [show m * C * m * p * C = m * C * (m * p) * C by simp only [Matrix.mul_assoc], hmp]
      simp only [Matrix.mul_assoc]
    exact h.symm.trans key
  have e2 : (m * (C * p)) *ᵥ s = 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hps, mulVec_zero, mulVec_zero]
  have h0 : m *ᵥ (C *ᵥ xhat C p s (C *ᵥ w + μ • s) c - (C *ᵥ w + μ • s)) = 0 := by
    unfold xhat
    simp only [mulVec_add, mulVec_sub, mulVec_smul, sub_mulVec, one_mulVec, mulVec_mulVec]
    rw [e1, e2, hms]
    simp
  rw [mem_hyper_iff hC hs]
  exact ⟨xhat_s hCs hmT hmm hms hσ hp _ c, _, hmv _ h0⟩

lemma eq_xhat (hC : C.PosSemidef) (hs : s ≠ 0) (hmT : mᵀ = m) (hmm : m * m = m)
    (hms : m *ᵥ s = 0) (hmz : ∀ z, s ⬝ᵥ z = 0 → m *ᵥ z = z)
    (hmv : ∀ v, m *ᵥ v = 0 → v = ((s ⬝ᵥ s)⁻¹ * (s ⬝ᵥ v)) • s)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p)
    {F F1 F2 y w : Fin d → ℝ} {μ c : ℝ} (hF : F = F1 + F2) (hF1 : F1 = C *ᵥ w + μ • s)
    (hF2C : C *ᵥ F2 = 0) (hF2s : s ⬝ᵥ F2 = 0) (hy : y ⬝ᵥ s = c)
    (hy2 : ∃ l : ℝ, C *ᵥ y - F1 = l • s)
    (hyp : ∀ z, C *ᵥ z = 0 → s ⬝ᵥ z = 0 → y ⬝ᵥ z = 0) : xhat C p s F c = y := by
  have hCs := sym_psd hC
  rw [hF, xhat_shift hCs hmT hmm hmz hp F1 c F2 hF2C hF2s]
  subst hF1
  refine uniq_of hC hs (xhat_mem hC hs hmT hmm hms hmv hp w μ c) ?_
    (xhat_perp hCs hmT hmm hmz hp _ c) hyp
  rw [mem_hyper_iff hC hs]
  exact ⟨hy, hy2⟩

end XFacts

section CpFacts

variable {C Cp : Matrix (Fin d) (Fin d) ℝ}

lemma cp_facts (hCs : Cᵀ = C) (hCp : LocalDistanceNetwork.IsMoorePenroseInverse C Cp) :
    Cpᵀ = Cp ∧ C * Cp = Cp * C ∧ (∀ v, C *ᵥ (Cp *ᵥ (C *ᵥ v)) = C *ᵥ v) ∧
    (∀ v, Cp *ᵥ (C *ᵥ (Cp *ᵥ v)) = Cp *ᵥ v) ∧ (∀ z, C *ᵥ z = 0 → Cp *ᵥ z = 0) ∧
    (∀ v, C *ᵥ (C *ᵥ (Cp *ᵥ v)) = C *ᵥ v) := by
  have hCpT := mp_sym hCs hCp
  obtain ⟨h1, h2, h3, h4⟩ := hCp
  have hcomm : C * Cp = Cp * C := by
    have := h3
    rw [transpose_mul, hCs, hCpT] at this
    exact this.symm
  refine ⟨hCpT, hcomm, ?_, ?_, ?_, ?_⟩
  · intro v; rw [mulVec_mulVec, mulVec_mulVec, h1]
  · intro v; rw [mulVec_mulVec, mulVec_mulVec, h2]
  · intro z hz
    rw [← h2, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, ← mulVec_mulVec, hz, mulVec_zero]
  · intro v
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc C C Cp, hcomm,
      ← Matrix.mul_assoc, h1]

end CpFacts

section Part3

variable {C m p Cp : Matrix (Fin d) (Fin d) ℝ} {s : Fin d → ℝ}

lemma eq3 (hC : C.PosSemidef) (hs : s ≠ 0) (hmT : mᵀ = m) (hmm : m * m = m)
    (hms : m *ᵥ s = 0) (hmz : ∀ z, s ⬝ᵥ z = 0 → m *ᵥ z = z)
    (hmv : ∀ v, m *ᵥ v = 0 → v = ((s ⬝ᵥ s)⁻¹ * (s ⬝ᵥ v)) • s)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p)
    (hCp : LocalDistanceNetwork.IsMoorePenroseInverse C Cp)
    (ws : Fin d → ℝ) (hsw : s = C *ᵥ ws) (F : Fin d → ℝ) (c : ℝ) :
    xhat C p s F c =
      Cp *ᵥ F + ((c - F ⬝ᵥ (Cp *ᵥ s)) / (s ⬝ᵥ (Cp *ᵥ s))) • (Cp *ᵥ s) := by
  have hCs := sym_psd hC
  obtain ⟨hCpT, hcomm, v1, v2, vz, v3⟩ := cp_facts hCs hCp
  have hD : s ⬝ᵥ (Cp *ᵥ s) ≠ 0 := by
    intro h0
    have : ws ⬝ᵥ (C *ᵥ ws) = 0 := by
      calc ws ⬝ᵥ (C *ᵥ ws) = ws ⬝ᵥ (C *ᵥ (Cp *ᵥ (C *ᵥ ws))) := by rw [v1]
        _ = (C *ᵥ ws) ⬝ᵥ (Cp *ᵥ (C *ᵥ ws)) := dot_sym hCs _ _
        _ = 0 := by rw [← hsw]; exact h0
    exact hs (by rw [hsw]; exact psd_zero hC ws this)
  have hCCps : C *ᵥ (Cp *ᵥ s) = s := by rw [hsw, v1]
  have hF2C : C *ᵥ (F - C *ᵥ (Cp *ᵥ F)) = 0 := by rw [mulVec_sub, v3, sub_self]
  refine eq_xhat hC hs hmT hmm hms hmz hmv hp (F1 := C *ᵥ (Cp *ᵥ F))
    (F2 := F - C *ᵥ (Cp *ᵥ F)) (w := Cp *ᵥ F) (μ := 0) (by abel) (by simp) hF2C ?_ ?_ ?_ ?_
  · rw [hsw, ← dot_sym hCs, hF2C, dotProduct_zero]
  · rw [add_dotProduct, smul_dotProduct, ← dot_sym hCpT F s, dotProduct_comm (Cp *ᵥ s) s,
      smul_eq_mul]
    field_simp
    ring
  · exact ⟨_, by rw [mulVec_add, mulVec_smul, hCCps]; abel⟩
  · intro z hz _
    rw [add_dotProduct, smul_dotProduct, ← dot_sym hCpT F z, ← dot_sym hCpT s z, vz z hz,
      dotProduct_zero, dotProduct_zero, smul_zero, add_zero]

lemma alpha_facts (hC : C.PosSemidef) (hCp : LocalDistanceNetwork.IsMoorePenroseInverse C Cp)
    (hsn : ∀ w, C *ᵥ w ≠ s) (α : Fin d → ℝ)
    (hα : α = (s ⬝ᵥ ((1 - C * Cp) *ᵥ s))⁻¹ • ((1 - C * Cp) *ᵥ s)) :
    s ⬝ᵥ ((1 - C * Cp) *ᵥ s) ≠ 0 ∧ ((1 - C * Cp)ᵀ = 1 - C * Cp) ∧ α ⬝ᵥ s = 1 ∧
      C *ᵥ α = 0 ∧ (∀ z, C *ᵥ z = 0 → s ⬝ᵥ z = 0 → α ⬝ᵥ z = 0) ∧
      (∀ w, α ⬝ᵥ (C *ᵥ w) = 0) := by
  have hCs := sym_psd hC
  obtain ⟨hCpT, hcomm, v1, v2, vz, v3⟩ := cp_facts hCs hCp
  have hET : (C * Cp)ᵀ = C * Cp := hCp.2.2.1
  have hEE : C * Cp * (C * Cp) = C * Cp := by rw [← Matrix.mul_assoc, hCp.1]
  have hNT : (1 - C * Cp)ᵀ = 1 - C * Cp := by rw [transpose_sub, transpose_one, hET]
  have hNN : (1 - C * Cp) * (1 - C * Cp) = 1 - C * Cp := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hEE]; abel
  have hCN : C * (1 - C * Cp) = 0 := by
    rw [mul_sub, mul_one, ← Matrix.mul_assoc, Matrix.mul_assoc C C Cp, hcomm,
      ← Matrix.mul_assoc, hCp.1, sub_self]
  set N := 1 - C * Cp with hN
  set D := s ⬝ᵥ (N *ᵥ s) with hD
  have hDsq : D = (N *ᵥ s) ⬝ᵥ (N *ᵥ s) := by
    rw [hD, ← dot_sym hNT, mulVec_mulVec, hNN]
  have hD0 : D ≠ 0 := by
    intro h0
    rw [hDsq] at h0
    have h1 := dotProduct_self_eq_zero.1 h0
    rw [hN, sub_mulVec, one_mulVec, sub_eq_zero, ← mulVec_mulVec] at h1
    exact hsn _ h1.symm
  have hCα : C *ᵥ α = 0 := by
    rw [hα, mulVec_smul, mulVec_mulVec, hCN, zero_mulVec, smul_zero]
  refine ⟨hD0, hNT, ?_, hCα, ?_, ?_⟩
  · rw [hα, smul_dotProduct, dotProduct_comm, ← hD, smul_eq_mul, inv_mul_cancel₀ hD0]
  · intro z hz hsz
    rw [hα, smul_dotProduct, ← dot_sym hNT, hN, sub_mulVec, one_mulVec, dotProduct_sub, hsz,
      ← mulVec_mulVec, vz z hz, mulVec_zero, dotProduct_zero, sub_zero, smul_zero]
  · intro w
    rw [dot_sym hCs, hCα, zero_dotProduct]

lemma eq4 (hC : C.PosSemidef) (hs : s ≠ 0) (hmT : mᵀ = m) (hmm : m * m = m)
    (hms : m *ᵥ s = 0) (hmz : ∀ z, s ⬝ᵥ z = 0 → m *ᵥ z = z)
    (hmv : ∀ v, m *ᵥ v = 0 → v = ((s ⬝ᵥ s)⁻¹ * (s ⬝ᵥ v)) • s)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse (m * C * m) p)
    (hCp : LocalDistanceNetwork.IsMoorePenroseInverse C Cp)
    (hsn : ∀ w, C *ᵥ w ≠ s) (α : Fin d → ℝ)
    (hα : α = (s ⬝ᵥ ((1 - C * Cp) *ᵥ s))⁻¹ • ((1 - C * Cp) *ᵥ s)) (F : Fin d → ℝ) (c : ℝ) :
    xhat C p s F c =
      Cp *ᵥ (F - (α ⬝ᵥ F) • s) + (c - (F - (α ⬝ᵥ F) • s) ⬝ᵥ (Cp *ᵥ s)) • α := by
  have hCs := sym_psd hC
  obtain ⟨hCpT, hcomm, v1, v2, vz, v3⟩ := cp_facts hCs hCp
  obtain ⟨hD0, hNT, hαs, hCα, hαz, hαC⟩ := alpha_facts hC hCp hsn α hα
  set r := α ⬝ᵥ F with hr
  set v := F - r • s with hv
  have hF2C : C *ᵥ (F - (C *ᵥ (Cp *ᵥ v) + r • s)) = 0 := by
    rw [mulVec_sub, mulVec_add, v3, hv, mulVec_smul, mulVec_sub, mulVec_smul]; abel
  have hF2eq : F - (C *ᵥ (Cp *ᵥ v) + r • s) = (1 - C * Cp) *ᵥ v := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hv]; abel
  refine eq_xhat hC hs hmT hmm hms hmz hmv hp (F1 := C *ᵥ (Cp *ᵥ v) + r • s)
    (F2 := F - (C *ᵥ (Cp *ᵥ v) + r • s)) (w := Cp *ᵥ v) (μ := r) (by abel) rfl hF2C ?_ ?_ ?_ ?_
  · rw [hF2eq, dot_sym hNT, hv, dotProduct_sub, dotProduct_smul, smul_eq_mul, hr, hα,
      smul_dotProduct, smul_eq_mul, dotProduct_comm ((1 - C * Cp) *ᵥ s) s]
    field_simp
    ring
  · rw [add_dotProduct, smul_dotProduct, ← dot_sym hCpT v s, hαs, smul_eq_mul]
    ring
  · refine ⟨-r, ?_⟩
    rw [mulVec_add, mulVec_smul, hCα, smul_zero, add_zero, neg_smul]
    abel
  · intro z hz hsz
    rw [add_dotProduct, smul_dotProduct, ← dot_sym hCpT v z, vz z hz, dotProduct_zero,
      hαz z hz hsz, smul_zero, add_zero]

end Part3

lemma decomp {C : Matrix (Fin d) (Fin d) ℝ} {s F : Fin d → ℝ}
    (h : F ∈ LinearMap.range (Matrix.toLin' C) ⊔ Submodule.span ℝ {s}) :
    ∃ w : Fin d → ℝ, ∃ μ : ℝ, F = C *ᵥ w + μ • s := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
  obtain ⟨w, rfl⟩ := hy
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨w, μ, by rw [← hyz, toLin'_apply]⟩

lemma mem_sup_of {C : Matrix (Fin d) (Fin d) ℝ} {s F x : Fin d → ℝ} {l : ℝ}
    (h : C *ᵥ x - F = l • s) :
    F ∈ LinearMap.range (Matrix.toLin' C) ⊔ Submodule.span ℝ {s} := by
  refine Submodule.mem_sup.2 ⟨C *ᵥ x, ⟨x, by rw [toLin'_apply]⟩, (-l) • s,
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s), ?_⟩
  rw [neg_smul, ← sub_eq_add_neg, ← h]
  abel

end Sol43

open NumInvQH.Oblique Sol43 in
theorem solution {d : ℕ}
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (b s u : Fin d → ℝ) (v : ℝ) (hs : s ≠ 0)
    (hu : u ∈ LinearMap.range (Matrix.toLin' C))
    (p Cp : Matrix (Fin d) (Fin d) ℝ)
    (hp : LocalDistanceNetwork.IsMoorePenroseInverse
      ((1 - (s ⬝ᵥ s)⁻¹ • Matrix.vecMulVec s s) * C *
        (1 - (s ⬝ᵥ s)⁻¹ • Matrix.vecMulVec s s)) p)
    (hCp : LocalDistanceNetwork.IsMoorePenroseInverse C Cp) :
    let a := b ᵥ* p - (s ⬝ᵥ s)⁻¹ • (s ᵥ* (1 - C * p))
    let ξ := u ᵥ* p + (v * (s ⬝ᵥ s)⁻¹) • (s ᵥ* (1 - C * p))
    let Ξa := hyperArgmin C b s (-1)
    let Ξξ := hyperArgmin C u s v
    (Ξa.Nonempty ↔ b ∈ LinearMap.range (Matrix.toLin' C) ⊔ Submodule.span ℝ {s}) ∧
    (b ∈ LinearMap.range (Matrix.toLin' C) ⊔ Submodule.span ℝ {s} →
      Ξa = {x | ∃ z : Fin d → ℝ, C *ᵥ z = 0 ∧ s ⬝ᵥ z = 0 ∧ x = a + z} ∧
      IsMinNorm Ξa a) ∧
    (Ξξ = {x | ∃ z : Fin d → ℝ, C *ᵥ z = 0 ∧ s ⬝ᵥ z = 0 ∧ x = ξ + z} ∧
      IsMinNorm Ξξ ξ) ∧
    (s ∈ LinearMap.range (Matrix.toLin' C) →
      a = b ᵥ* Cp - ((1 + b ⬝ᵥ (Cp *ᵥ s)) / (s ⬝ᵥ (Cp *ᵥ s))) • (s ᵥ* Cp) ∧
      ξ = u ᵥ* Cp + ((v - u ⬝ᵥ (Cp *ᵥ s)) / (s ⬝ᵥ (Cp *ᵥ s))) • (s ᵥ* Cp)) ∧
    (s ∉ LinearMap.range (Matrix.toLin' C) →
      let mbar := 1 - C * Cp
      let α := (s ⬝ᵥ (mbar *ᵥ s))⁻¹ • (s ᵥ* mbar)
      let r := α ⬝ᵥ b
      a = (b - r • s) ᵥ* Cp - (1 + (b - r • s) ⬝ᵥ (Cp *ᵥ s)) • α ∧
      ξ = u ᵥ* Cp + (v - u ⬝ᵥ (Cp *ᵥ s)) • α ∧
      α ⬝ᵥ s = 1 ∧ α ᵥ* C = 0) := by
  intro a ξ Ξa Ξξ
  have hCs := sym_psd hC
  obtain ⟨hmT, hmm, hms, hmz, hmv⟩ := m_facts hs
  obtain ⟨hpT, -, -, -⟩ := p_facts hCs hmT hmm hp
  obtain ⟨hCpT, -, -, -, -, -⟩ := cp_facts hCs hCp
  have hvp : ∀ x, x ᵥ* p = p *ᵥ x := fun x => by rw [← vecMul_transpose, hpT]
  have hvCp : ∀ x, x ᵥ* Cp = Cp *ᵥ x := fun x => by rw [← vecMul_transpose, hCpT]
  have h1Cp : s ᵥ* (1 - C * p) = (1 - p * C) *ᵥ s := by
    rw [← vecMul_transpose, transpose_sub, transpose_one, transpose_mul, hCs, hpT]
  have ha : a = xhat C p s b (-1) := by
    show b ᵥ* p - (s ⬝ᵥ s)⁻¹ • (s ᵥ* (1 - C * p)) = _
    rw [hvp, h1Cp]
    unfold xhat
    rw [neg_one_mul, neg_smul, sub_eq_add_neg]
  have hξ : ξ = xhat C p s u v := by
    show u ᵥ* p + (v * (s ⬝ᵥ s)⁻¹) • (s ᵥ* (1 - C * p)) = _
    rw [hvp, h1Cp]
    rfl
  have hΞa : Ξa = hyperArgmin C b s (-1) := rfl
  have hΞξ : Ξξ = hyperArgmin C u s v := rfl
  obtain ⟨wu, hwu⟩ := hu
  rw [toLin'_apply] at hwu
  have huF : u = C *ᵥ wu + (0 : ℝ) • s := by rw [zero_smul, add_zero, hwu]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hΞa]
    constructor
    · rintro ⟨x, hx⟩
      rw [mem_hyper_iff hC hs] at hx
      obtain ⟨-, l, hl⟩ := hx
      exact mem_sup_of hl
    · intro hb
      obtain ⟨w, μ, hF⟩ := decomp hb
      refine ⟨xhat C p s b (-1), ?_⟩
      rw [hF]
      exact xhat_mem hC hs hmT hmm hms hmv hp w μ (-1)
  · intro hb
    obtain ⟨w, μ, hF⟩ := decomp hb
    have hx : xhat C p s b (-1) ∈ hyperArgmin C b s (-1) := by
      rw [hF]
      exact xhat_mem hC hs hmT hmm hms hmv hp w μ (-1)
    rw [ha, hΞa]
    exact ⟨hyper_eq hC hs hx, minnorm_of hC hs hx (xhat_perp hCs hmT hmm hmz hp b (-1))⟩
  · have hx : xhat C p s u v ∈ hyperArgmin C u s v := by
      rw [huF]
      exact xhat_mem hC hs hmT hmm hms hmv hp wu 0 v
    rw [hξ, hΞξ]
    exact ⟨hyper_eq hC hs hx, minnorm_of hC hs hx (xhat_perp hCs hmT hmm hmz hp u v)⟩
  · intro hsR
    obtain ⟨ws, hws⟩ := hsR
    rw [toLin'_apply] at hws
    rw [ha, hξ, eq3 hC hs hmT hmm hms hmz hmv hp hCp ws hws.symm b (-1),
      eq3 hC hs hmT hmm hms hmz hmv hp hCp ws hws.symm u v]
    simp only [hvCp]
    refine ⟨?_, trivial⟩
    rw [sub_eq_add_neg _ (((1 + _) / _) • _), ← neg_smul]
    congr 2
    ring
  · intro hsR mbar α r
    have hsn : ∀ w, C *ᵥ w ≠ s := by
      intro w hw
      exact hsR ⟨w, by rw [toLin'_apply, hw]⟩
    have hNT : (1 - C * Cp)ᵀ = 1 - C * Cp := by
      rw [transpose_sub, transpose_one, hCp.2.2.1]
    have hα : α = (s ⬝ᵥ ((1 - C * Cp) *ᵥ s))⁻¹ • ((1 - C * Cp) *ᵥ s) := by
      show (s ⬝ᵥ ((1 - C * Cp) *ᵥ s))⁻¹ • (s ᵥ* (1 - C * Cp)) = _
      rw [← mulVec_transpose, hNT]
    obtain ⟨-, -, hαs, hCα, -, hαC⟩ := alpha_facts hC hCp hsn α hα
    have hr : r = α ⬝ᵥ b := rfl
    refine ⟨?_, ?_, hαs, ?_⟩
    · rw [ha, eq4 hC hs hmT hmm hms hmz hmv hp hCp hsn α hα b (-1), hvCp, hr,
        sub_eq_add_neg _ ((1 + _) • α), ← neg_smul]
      congr 2
      ring
    · have hαu : α ⬝ᵥ u = 0 := by rw [← hwu]; exact hαC wu
      rw [hξ, eq4 hC hs hmT hmm hms hmz hmv hp hCp hsn α hα u v, hvCp, hαu, zero_smul, sub_zero]
    · rw [← mulVec_transpose, hCs, hCα]
